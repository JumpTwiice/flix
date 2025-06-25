/*
 * Copyright 2025 Casper Dalgaard Nielsen
 *                Adam Yasser Tallouzi
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

mod Fixpoint.Phase.Hoisting {
    use Fixpoint.Ast.Ram.{RamStmt, RelOp, RelSym, RamTerm, BoolExp, RowVar, RamProgram, RamId, arityOfNonLat}
    use Fixpoint.Boxed
    use Fixpoint.Util.{getOrCrash, unifyEqualitiesStmt}
    use MutDisjointSets.MutDisjointSets

    ///
    /// Hoists `If` ops in `program` as much as possible and merges them with `Search`
    /// into `Query` when possible/relevant. Additionally, guards are added at the top of
    /// `Insert` statements that only perform the operations if none of the relations are
    /// empty. For example, the following
    /// ```
    /// search a ∈ A do
    ///     search b ∈ B do
    ///         search c ∈ C do
    ///             if(b[0] = a[0] ∧ c[0] = a[0]) then
    ///                 project (a[0]) into R
    ///             end
    ///         end
    ///     end
    /// end
    /// ```
    /// is hoisted to 
    /// ```
    /// if(not (A = ∅) ∧ not (B = ∅) not (C = ∅)) then
    ///     search a ∈ A do
    ///         query {b ∈ B | b[0] = a[0]} do
    ///             query {c ∈ C | c[0] = a[0]} do
    ///                 project (a[0]) into R
    ///             end
    ///         end
    ///     end
    /// end
    /// ```
    ///
    @Internal
    pub def hoistProgram(program: RamProgram): RamProgram = match program { 
        case RamProgram.Program(stmt, facts, meta, index) => region rc {
            let equalitySets = MutDisjointSets.empty(rc);
            let constEqualities = MutMap.empty(rc);
            unifyEqualitiesStmt(equalitySets, constEqualities, stmt);
            let termMap = MutMap.empty(rc);
            let impossible = MutSet.empty(rc);
            MutMap.forEach(load -> listOfPairs -> List.forEach(match (val, id) -> {
                let rep = getOrCrash(MutDisjointSets.find(load, equalitySets));
                match MutMap.get(rep, termMap) {
                    case Some(RamTerm.Lit(v, _)) => 
                        if(v != val) MutSet.add(fst(rep), impossible)
                        else ()
                    case Some(_) => bug!("In Fixpoint.Phase.Hoisting.hoistStmt: termMap contains non-literals!")
                    case None => MutMap.put(rep, RamTerm.Lit(val, id), termMap)
                }
            }, listOfPairs), constEqualities);
            match hoistStmt(rc, termMap, equalitySets, impossible, stmt) {
                case None => RamProgram.Program(RamStmt.Comment("No rules are satisfiable"), facts, meta, index)
                case Some(hoistedStmt) => RamProgram.Program(hoistedStmt, facts, meta, index)
            }
        }
    }

    ///
    /// Hoist `If` ops in `stmt` and merge them with `Search` ops when relevant.
    ///
    /// `termMap` is used to look up which term a given `(RowVar, Int32)` is represented by and
    /// whether they are currently considered ground.
    ///
    /// `equalitySets` is used to find representative terms given the seen equalities.
    ///
    /// `impossible` contains the set of `RowVar`'s/rules which have been determined impossible to satisfy.
    ///
    def hoistStmt(
        rc: Region[r],
        termMap: MutMap[(RowVar, Int32), RamTerm, r],
        equalitySets: MutDisjointSets[(RowVar, Int32), r], 
        impossible: MutSet[RowVar, r], 
        stmt: RamStmt
    ): Option[RamStmt] \ r = match stmt {
        case RamStmt.Insert(op) =>
            let independent = MutList.empty(rc);
            let optNewOp = hoistOp(rc, termMap, equalitySets, impossible, MutMap.empty(rc), independent, op);
            match optNewOp {
                case None => None 
                case Some(newOp) => 
                    let isEmptyBools = 
                        collectRelSymsStmt(stmt) |> 
                        List.map(relSym -> BoolExp.Not(BoolExp.IsEmpty(relSym))) |>
                        List.toVector;
                    let newStmt = 
                        if (MutList.size(independent) == 0) {
                            RamStmt.Insert(RelOp.If(isEmptyBools, newOp))
                        } else {
                            let bools = MutList.toVector(independent) `Vector.append` isEmptyBools;
                            RamStmt.Insert(RelOp.If(bools, newOp))
                        };
                    Some(newStmt)
            }
        case RamStmt.MergeInto(_, _) => Some(stmt)
        case RamStmt.Swap(_, _) => Some(stmt)
        case RamStmt.Purge(_) => Some(stmt)
        case RamStmt.Seq(xs) =>
            let children =
                Vector.filterMap(hoistStmt(rc, termMap, equalitySets, impossible), xs);
            if (Vector.isEmpty(children)) None
            else if (Vector.length(children) == 1)
                Vector.head(children)
            else Some(RamStmt.Seq(children))
        case RamStmt.Par(xs) => 
            let children =
                Vector.filterMap(hoistStmt(rc, termMap, equalitySets, impossible), xs);
            if (Vector.isEmpty(children)) None
            else if (Vector.length(children) == 1)
                Vector.head(children)
            else Some(RamStmt.Par(children))
        case RamStmt.Until(test, body) =>
            match hoistStmt(rc, termMap, equalitySets, impossible, body) {
                case None => None
                case Some(v) => Some(RamStmt.Until(test, v))
            }
        case RamStmt.EstimateJoinSize(_, _, _, _) => Some(stmt)
        case RamStmt.Comment(_) => Some(stmt)
    }

    ///
    /// Returns a list of the `RelSym`'s appearing in `stmt`.
    ///
    def collectRelSymsStmt(stmt: RamStmt): List[RelSym] \ r = match stmt {
        case RamStmt.Insert(op) => collectRelSymsOp(op)
        case _ => unreachable!()
    }

    ///
    /// Returns a list of the `RelSym`'s appearing in `op`.
    ///
    def collectRelSymsOp(op: RelOp): List[RelSym] \ r = match op {
        case RelOp.Search(_, relSym, body) => relSym :: collectRelSymsOp(body)
        case RelOp.Query(_, relSym, _, _, body) => relSym :: collectRelSymsOp(body)
        case RelOp.Functional(_, _, _, body, _) => collectRelSymsOp(body)
        case RelOp.Project(_, _, _) => Nil
        case RelOp.If(_, body) => collectRelSymsOp(body)
    }

    ///
    /// Hoists statements in `op` as far as possible. See `hoistStmt`.
    ///
    /// `idToBool` maps `RowVar`s to a list of `BoolExp`s which `RowVar` occur in.
    /// 
    /// `independentBool` is a list of `BoolExp`s which do not depend on any `RowVar`s.
    ///
    def hoistOp(
        rc: Region[r],
        termMap: MutMap[(RowVar, Int32), RamTerm, r],
        equalitySets: MutDisjointSets[(RowVar, Int32), r], 
        impossible: MutSet[RowVar, r], 
        idToBool: MutMap[RowVar, MutList[BoolExp, r], r],
        independentBool: MutList[BoolExp, r],
        op: RelOp
    ): Option[RelOp] \ r =
        let hoistOpRec = hoistOp(rc, termMap, equalitySets, impossible, idToBool, independentBool);
        match op {
            // We could here keep the BoolExps that we do not want to handle as if, but then we limit
            // later iterations of the query algorithms, or require that this file is changed later
            case RelOp.Search(rowVar, relSym, body) =>
                let RelSym.Symbol(_, arity, _) = relSym;
                Vector.forEach(i -> {
                    match MutDisjointSets.find((rowVar, i), equalitySets) {
                        case Some(rep) => MutMap.putWith(_ -> v -> v, rep, RamTerm.RowLoad(rowVar, i, relSym), termMap)
                        case None => bug!("In Fixpoint.Phase.Hoisting: Everything should be in the equalitySet")
                    }
                }, Vector.range(0, arity));
                let optHoistedBody = hoistOpRec(body);
                match optHoistedBody {
                    case None => None
                    case Some(hoistedBody) =>
                        let termMapCopy = MutMap.copy(rc, termMap);
                        let relevant = List.filter(isBoolGround(termMap, equalitySets), MutList.toList(MutMap.getWithDefault(rowVar, MutList.empty(rc), idToBool)));
                        let range = Vector.range(0, arity);
                        // Remove all terms that were bound here.
                        // If there are equalities between 2 variables from the same tuple save them for later
                        let intraEqualities = MutList.empty(rc);
                        let knownEqualities = MutList.empty(rc);
                        range |> Vector.forEach(i -> {match MutDisjointSets.find((rowVar, i), equalitySets) {
                            case None => ()
                            case Some(rep) => match getOrCrash(MutMap.get(rep, termMapCopy)) {
                                case RamTerm.RowLoad(rv, i1, rel) =>
                                    if (rv == rowVar) {
                                        MutMap.remove(rep, termMap);
                                        if(i == i1) {
                                            ()
                                        } else {
                                            // This is for atoms of the form AtomName(x, x).
                                            MutList.push(BoolExp.Eq(RamTerm.RowLoad(rv, i, rel), RamTerm.RowLoad(rv, i1, rel)), intraEqualities)
                                        }
                                    } else
                                        MutList.push(BoolExp.Eq(RamTerm.RowLoad(rowVar, i, relSym), RamTerm.RowLoad(rv, i1, rel)), knownEqualities)
                                case value => MutList.push(BoolExp.Eq(RamTerm.RowLoad(rowVar, i, relSym), value), knownEqualities)
                        }}});
                        let hoistedToHere = List.filter(x -> not isBoolGround(termMap, equalitySets, x), relevant) |> List.map(replaceByRepBoolExp(termMapCopy, equalitySets));
                        let combined = List.toVector(MutList.toList(knownEqualities) ::: MutList.toList(intraEqualities) ::: hoistedToHere);
                        let newOp = 
                            if (Vector.length(combined) != 0)
                                RelOp.Query(rowVar, relSym, combined, -1, hoistedBody)
                            else RelOp.Search(rowVar, relSym, hoistedBody);
                        Some(newOp)
                }
            case RelOp.Query(_, _, _, _, _) => 
                bug!("In Fixpoint.Phase.Hoisting.hoistOp: Query should not exists when introducing Query")
            case RelOp.Functional(rowVar, func, terms, body, arity) =>
                Vector.forEach(i -> {
                    match MutDisjointSets.find((rowVar, i), equalitySets) {
                        case Some(rep) => MutMap.putWith(_ -> v -> v, rep, RamTerm.RowLoad(rowVar, i, Fixpoint.Phase.Compiler.functionalRelSym(arity)), termMap)
                        case None => bug!("In Fixpoint.Phase.Hoisting: Everything should be in the equalitySet")
                    }
                }, Vector.range(0, arity));
                match hoistOpRec(body) {
                    case None => None
                    case Some(v) => {
                        let termMapCopy = MutMap.copy(rc, termMap);
                        let relevant = List.filter(isBoolGround(termMap, equalitySets), MutList.toList(MutMap.getWithDefault(rowVar, MutList.empty(rc), idToBool)));
                        Vector.forEach(i -> {
                            match MutDisjointSets.find((rowVar, i), equalitySets) {
                                case Some(rep) => MutMap.remove(rep, termMap)
                                case None => bug!("In Fixpoint.Phase.Hoisting: Everything should be in the equalitySet")
                            }
                        }, Vector.range(0, arity));
                        let hoistedToHere = List.filter(x -> not isBoolGround(termMap, equalitySets, x), relevant);

                        if (List.nonEmpty(hoistedToHere)) {
                            Some(RelOp.Functional(rowVar, func, terms, RelOp.If(List.toVector(hoistedToHere) |> Vector.map(replaceByRepBoolExp(termMapCopy, equalitySets)), v), arity))
                        } else {
                            Some(RelOp.Functional(rowVar, func, terms, v, arity))
                        }
                    }
                }
            case RelOp.Project(_, _, _) => Some(op)
            case RelOp.If(boolExps, body) => 
                Vector.forEach(b -> {
                    let vars = collectBoolVariables(termMap, b);
                    if (Set.size(vars) == 0)
                        MutList.push(b, independentBool) 
                    else
                        // Don't collect Eq's. They are handled separately to ensure we refer to the earliest evaluated expression.
                        match b {
                            case BoolExp.Eq(_, _) => ()
                            case _ => vars |> Set.forEach(v ->{
                                let boolList = MutMap.getOrElsePut(v, MutList.empty(rc), idToBool);
                                MutList.push(b, boolList)
                        })
                        }
                }, boolExps);
                hoistOpRec(body)
        }

    ///
    /// Returns the set of `RowVar` in `bool`.
    ///
    def collectBoolVariables(termMap: MutMap[(RowVar, Int32), RamTerm, r], bool: BoolExp): Set[RowVar] \ r =
        let collectTerm = collectTermVariables(termMap);
        match bool {
            case BoolExp.Not(boolExp) => collectBoolVariables(termMap, boolExp)
            case BoolExp.IsEmpty(_) => Set#{}
            case BoolExp.NotMemberOf(terms, _) => Vector.foldLeft(y -> x -> Set.union(collectTerm(x), y), Set#{}, terms)
            case BoolExp.NotBot(t1, _, _) => collectTerm(t1)
            case BoolExp.Leq(_, rv, RelSym.Symbol(_, i, _)) => insertRepRowVar(termMap, rv, i)
            case BoolExp.Eq(t1, t2) => Set.union(collectTerm(t1), collectTerm(t2))
            case BoolExp.Guard1(_, t1) => collectTerm(t1)
            case BoolExp.Guard2(_, t1, t2) => Set.union(collectTerm(t1), collectTerm(t2))
            case BoolExp.Guard3(_, t1, t2, t3) => 
                Set.union(Set.union(collectTerm(t1), collectTerm(t2)), collectTerm(t3))
            case BoolExp.Guard4(_, t1, t2, t3, t4) => 
                Set.union(Set.union(Set.union(collectTerm(t1), collectTerm(t2)), collectTerm(t3)), collectTerm(t4))
            case BoolExp.Guard5(_, t1, t2, t3, t4, t5) => 
                Set.union(Set.union(Set.union(Set.union(collectTerm(t1), collectTerm(t2)), collectTerm(t3)), collectTerm(t4)), collectTerm(t5))
    }

    ///
    /// Returns the set of `RowVar` in `term`.
    ///
    def collectTermVariables(termMap: MutMap[(RowVar, Int32), RamTerm, r], term: RamTerm): Set[RowVar] \ r = match term {
        case RamTerm.Lit(_, _)               => Set#{}
        case RamTerm.ProvMax(vec)            => Vector.foldLeft(acc -> match (rv, _) -> Set.insert(rv, acc), Set#{}, vec)
        case RamTerm.RowLoad(rv, i, _)       => insertRepRowVar(termMap, rv, i)
        case RamTerm.Meet(_, t1, (rv, RelSym.Symbol(_, arity, _)), _) => Set.union(collectTermVariables(termMap, t1), insertRepRowVar(termMap, rv, arity))
        case RamTerm.App1(_, t1, _)          => collectTermVariables(termMap, t1)
        case RamTerm.App2(_, t1, t2, _) =>
            Vector#{t1, t2} |>
            Vector.foldRight(t -> acc -> collectTermVariables(termMap, t) `Set.union` acc, Set#{})
        case RamTerm.App3(_, t1, t2, t3, _) =>
            Vector#{t1, t2, t3} |>
            Vector.foldRight(t -> acc -> collectTermVariables(termMap, t) `Set.union` acc, Set#{})
        case RamTerm.App4(_, t1, t2, t3, t4, _) =>
            Vector#{t1, t2, t3, t4} |>
            Vector.foldRight(t -> acc -> collectTermVariables(termMap, t) `Set.union` acc, Set#{})
        case RamTerm.App5(_, t1, t2, t3, t4, t5, _) => 
            Vector#{t1, t2, t3, t4, t5} |>
            Vector.foldRight(t -> acc -> collectTermVariables(termMap, t) `Set.union` acc, Set#{})
    }

    def insertRepRowVar(termMap: MutMap[(RowVar, Int32), RamTerm, r], rv: RowVar, index: Int32): Set[RowVar] \ r = match MutMap.get((rv, index), termMap) {
        case None => Set#{rv}
        case Some(rep) => match rep {
            case RamTerm.RowLoad(rv1, _, _) => Set#{rv1}
            case _ => Set#{rv}
        }
    }

    ///
    /// Replace terms in `bool` by their representative.
    ///
    def replaceByRepBoolExp(
        termMap: MutMap[(RowVar, Int32), RamTerm, r],
        equalitySets: MutDisjointSets[(RowVar, Int32), r], 
        bool: BoolExp
    ): BoolExp \ r =
        let replaceRec = replaceByRepBoolExp(termMap, equalitySets);
        let replaceTerm = replaceByRepRamTerm(termMap, equalitySets);
        match bool {
            case BoolExp.Not(boolExp) => BoolExp.Not(replaceRec(boolExp))
            case BoolExp.IsEmpty(_) => bool
            case BoolExp.NotMemberOf(terms, rel) => BoolExp.NotMemberOf(Vector.map(replaceTerm, terms), rel)
            case BoolExp.NotBot(t1, f, bot) => BoolExp.NotBot(replaceTerm(t1), f, bot)
            case BoolExp.Leq(_, _, _) => bool
            case BoolExp.Eq(t1, t2) => BoolExp.Eq(replaceTerm(t1), replaceTerm(t2))
            case BoolExp.Guard1(f, t1) => BoolExp.Guard1(f, replaceTerm(t1))
            case BoolExp.Guard2(f, t1, t2) => BoolExp.Guard2(f, replaceTerm(t1), replaceTerm(t2))
            case BoolExp.Guard3(f, t1, t2, t3) => BoolExp.Guard3(f, replaceTerm(t1), replaceTerm(t2), replaceTerm(t3))
            case BoolExp.Guard4(f, t1, t2, t3, t4) => BoolExp.Guard4(f, replaceTerm(t1), replaceTerm(t2), replaceTerm(t3), replaceTerm(t4))
            case BoolExp.Guard5(f, t1, t2, t3, t4, t5) => BoolExp.Guard5(f, replaceTerm(t1), replaceTerm(t2), replaceTerm(t3), replaceTerm(t4), replaceTerm(t5))
    }

    ///
    /// Replace terms in `ramTerm` by their representative.
    ///
    def replaceByRepRamTerm(
        termMap: MutMap[(RowVar, Int32), RamTerm, r],
        equalitySets: MutDisjointSets[(RowVar, Int32), r], 
        ramTerm: RamTerm
    ): RamTerm \ r =
        let getRep = term -> match term {
            case RamTerm.RowLoad(rv, i, _) =>
            let load = MutDisjointSets.find((rv, i), equalitySets) |> getOrCrash;
            match MutMap.get(load, termMap) {
                case None => term
                case Some(rep) => rep
            }                
            case _ => term
        };
        let replaceRec = replaceByRepRamTerm(termMap, equalitySets);
        match ramTerm {
            case RamTerm.Lit(_, _)                      => ramTerm
            case RamTerm.ProvMax(_)                     => ramTerm
            case RamTerm.RowLoad(_, _, _)               => getRep(ramTerm)
            case RamTerm.Meet(_, _, _, _)               => ramTerm
            case RamTerm.App1(f, t1, id)                => RamTerm.App1(f, replaceRec(t1), id)
            case RamTerm.App2(f, t1, t2, id)            => RamTerm.App2(f, replaceRec(t1), replaceRec(t2), id)
            case RamTerm.App3(f, t1, t2, t3, id)        => RamTerm.App3(f, replaceRec(t1), replaceRec(t2), replaceRec(t3), id)
            case RamTerm.App4(f, t1, t2, t3, t4, id)    => RamTerm.App4(f, replaceRec(t1), replaceRec(t2), replaceRec(t3), replaceRec(t4), id)
            case RamTerm.App5(f, t1, t2, t3, t4, t5, id)=> RamTerm.App5(f, replaceRec(t1), replaceRec(t2), replaceRec(t3), replaceRec(t4), replaceRec(t5), id)
    }


    ///
    /// Returns `true` if `bool` is ground with respect to `termMap` and `equalitySets`.
    ///
    /// See `isTermGround`.
    ///
    def isBoolGround(
        termMap: MutMap[(RowVar, Int32), RamTerm, r],
        equalitySets: MutDisjointSets[(RowVar, Int32), r], 
        bool: BoolExp
    ): Bool \ r =
        let termGround = isTermGround(termMap, equalitySets);
        match bool {
            case BoolExp.Not(boolExp) => isBoolGround(termMap, equalitySets, boolExp)
            case BoolExp.IsEmpty(_) => unreachable!()
            case BoolExp.NotMemberOf(terms, _) => Vector.forAll(termGround, terms)
            case BoolExp.NotBot(t1, _, _) => termGround(t1)
            case BoolExp.Leq(_, rv, relSym) => 
                MutMap.memberOf(MutDisjointSets.find((rv, arityOfNonLat(relSym)), equalitySets) |> getOrCrash, termMap)
            case BoolExp.Eq(t1, t2) => termGround(t1) and termGround(t2)
            case BoolExp.Guard1(_, t1) => termGround(t1)
            case BoolExp.Guard2(_, t1, t2) => termGround(t1) and termGround(t2)
            case BoolExp.Guard3(_, t1, t2, t3) => termGround(t1) and termGround(t2) and termGround(t3)
            case BoolExp.Guard4(_, t1, t2, t3, t4) => termGround(t1) and termGround(t2) and termGround(t3) and termGround(t4)
            case BoolExp.Guard5(_, t1, t2, t3, t4, t5) => termGround(t1) and termGround(t2) and termGround(t3) and termGround(t4) and termGround(t5)
    }

    ///
    /// Returns `true` if `term` is ground with respect to `termMap` and `equalitySets`.
    ///
    /// A `RowLoad` is true if its representing `(rv, index)` with respect to `equalitySets`
    /// is in `termMap`.
    ///
    def isTermGround(
        termMap: MutMap[(RowVar, Int32), RamTerm, r],
        equalitySets: MutDisjointSets[(RowVar, Int32), r],
        term: RamTerm
    ): Bool \ r =
        let termGround = isTermGround(termMap, equalitySets);
        match term {
            case RamTerm.Lit(_, _) => true
            case RamTerm.ProvMax(loads) => 
                loads |> Vector.forAll(load -> {
                    MutMap.memberOf(MutDisjointSets.find(load, equalitySets) |> getOrCrash, termMap)
                })
            case RamTerm.RowLoad(rv, i, _) =>
                MutMap.memberOf(getOrCrash(MutDisjointSets.find((rv, i), equalitySets)), termMap)
            case RamTerm.Meet(_, t1, (rv, relSym), _) => termGround(t1) and MutMap.memberOf(getOrCrash(MutDisjointSets.find((rv, arityOfNonLat(relSym)), equalitySets)), termMap)
            case RamTerm.App1(_, t1, _) => termGround(t1)
            case RamTerm.App2(_, t1, t2, _) => termGround(t1) and termGround(t2)
            case RamTerm.App3(_, t1, t2, t3, _) => termGround(t1) and termGround(t2) and termGround(t3)
            case RamTerm.App4(_, t1, t2, t3, t4, _) => termGround(t1) and termGround(t2) and termGround(t3) and termGround(t4)
            case RamTerm.App5(_, t1, t2, t3, t4, t5, _) => termGround(t1) and termGround(t2) and termGround(t3) and termGround(t4) and termGround(t5)
        }
}
