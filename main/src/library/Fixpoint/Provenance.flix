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

///
/// The current implementation does not output the negative atoms. They can be derived from the positive.
///
mod Fixpoint.Provenance {
    use Fixpoint.Ast.Datalog.{Datalog, Constraint, VarSym, BodyPredicate, HeadPredicate, HeadTerm, BodyTerm, Polarity}
    use Fixpoint.Ast.Datalog.Datalog.{Datalog, Model, Join, Provenance}
    use Fixpoint.Ast.Shared.{PredSym}
    use Fixpoint.Boxed
    use Fixpoint.Counter
    use Fixpoint.Util.getOrCrash

    type alias ProvIDB = Map[PredSym, Map[Vector[Boxed], (Int64, Int32)]]

    type alias BPLookup[r: Region] = BPlusTree[Vector[Boxed], List[(Vector[Boxed], Int64, Int32)], r]

    type alias ProvLookupStruct[r: Region] = MutMap[PredSym, MutMap[Vector[Int32], BPLookup[r], r], r]

    enum ProofTree {
        case EDB(PredSym, Vector[Boxed])
        case Negative(PredSym, Vector[Boxed])
        case IDB(PredSym, Vector[Boxed], Vector[ProofTree])
    }

    def extractSearch(search: Vector[(Int32, Boxed)]): (Vector[Int32], Vector[Boxed]) =  {
        let searchBits = Vector.map(match (x, _) -> x, search);
        let searchValues = Vector.map(match (_, x) -> x, search);
        (searchBits, searchValues)
    }

    def lookup(idb: ProvIDB, rc: Region[r], searchAndVals: Vector[(Int32, Boxed)], arrSize: Int32, lookupStruct: ProvLookupStruct[r], pred: PredSym): Option[List[(Vector[Boxed], Int64, Int32)]] \ r =
        match Map.get(pred, idb) {
            case None => None
            case Some(fullTree) => 
                let (search, vals) = extractSearch(searchAndVals);
                let innerMap = MutMap.getOrElsePut(pred, MutMap.empty(rc), lookupStruct);
                match MutMap.get(search, innerMap) {
                    case Some(tree) => BPlusTree.get(vals, tree)
                    case None =>
                        let tree = BPlusTree.emptyWithSearch(rc, search);
                        let extractSearchPart = k -> Vector.init(i -> Vector.get(Vector.get(i, search), k), Vector.length(search));
                        let nonSearch = Vector.range(0, arrSize) |> Vector.filter(v -> not Vector.memberOf(v, search));
                        let extractNonSearchPart = k -> Vector.init(i -> Vector.get(Vector.get(i, nonSearch), k), Vector.length(nonSearch));
                        fullTree |>
                        Map.forEach(k -> match (depth, rule) -> {
                            let searchPart = extractSearchPart(k);
                            let nonSearchPart = extractNonSearchPart(k);
                            let newVal = ((nonSearchPart), depth, rule);
                            BPlusTree.putWith(_ -> old -> newVal :: old, searchPart, newVal :: Nil, tree)
                        });
                        MutMap.put(search, tree, innerMap);
                        BPlusTree.get(vals, tree)
                }
        }

    mod ProofTree {
        pub def toString(p: ProofTree, indentChild: Int32): String = match p {
            case EDB(pred, fact) => 
                let indentCur = String.repeat(indentChild, " ");
                let factString = Vector.join(", ", fact);
                "${indentCur}${pred}(${factString}). Fact"
            case Negative(pred, fact) => 
                let indentCur = String.repeat(indentChild, " ");
                let factString = Vector.join(", ", fact);
                "${indentCur}No ${pred}(${factString})"
            case IDB(pred, fact, subs) => 
                let factString = Vector.join(", ", fact);
                let indentCur = String.repeat(indentChild, " ");
                let subProofs = Vector.joinWith(sub -> toString(sub, indentChild + 4), "${String.lineSeparator()}", subs);
                "${indentCur}${pred}(${factString}). Proof:${String.lineSeparator()}${subProofs}"
        }
    }

    instance ToString[ProofTree] {
        pub def toString(p: ProofTree): String = ProofTree.toString(p, 0)
    }

    def flatMap(p: ProofTree): List[(PredSym, Vector[Boxed])] = region rc {
        let res = MutList.empty(rc);
        def recurse(t) = match t {
            case ProofTree.EDB(pred, fact) => MutList.push((pred, fact), res)
            case ProofTree.Negative(_, _) => ()
            case ProofTree.IDB(pred, fact, subTrees) => {
                MutList.push((pred, fact), res);
                subTrees |> Vector.forEach(recurse)
        }};
        recurse(p);
        res |> MutList.toList
    }

    pub def provQuery(predSym: PredSym, fact: Vector[Boxed], d: Datalog): Option[List[(PredSym, Vector[Boxed])]] = match d {
        case Provenance(rules, provIdb) => region rc {
            Array.empty(rc, 10);
            let reorderedRules = Vector.map(identity, rules);
            let annotation = match Map.get(predSym, provIdb) {
                case None => None
                case Some(v) => match Map.get(fact, v) {
                    case None => None
                    case Some(annotations) => Some(annotations)
                }
            };
            match annotation {
                case None => None
                case Some((depth, ruleUsed)) => 
                    let lookupStruct = MutMap.empty(rc);
                    let tree = buildProof(predSym, fact, depth, ruleUsed, reorderedRules, provIdb, lookupStruct, rc);
                    Some(flatMap(tree))                    
            }
        }
        case _ => 
            bug!("In Fixpoint.Provenance.provQuery: Can only build a proof from a provenance model")
    }

    def buildProof(predSym: PredSym, fact: Vector[Boxed], depth: Int64, ruleUsed: Int32, rules: Vector[Constraint], provIdb: ProvIDB, lookupStruct: ProvLookupStruct[r], rc: Region[r]): ProofTree \ r = {
        if(ruleUsed == -1) {
            ProofTree.EDB(predSym, fact)
        } else if(ruleUsed == -2) {
            ProofTree.Negative(predSym, fact)
        } else {
            let rule = Vector.get(ruleUsed, rules);
            let bodyAtoms = getMatchingBody(fact, depth, rc, provIdb, lookupStruct, rule);
            let Constraint.Constraint(_, bodyPreds) = rule;
            let relevantPreds = bodyPreds |> Vector.filter(bodyAtom -> match bodyAtom {
                case BodyPredicate.BodyAtom(_, _, _, _, _) => true
                case _ => false
            });
            let childProofs = Vector.zip(relevantPreds, bodyAtoms) |> Vector.map(match (bodyP, (bodyFact, bodyDepth, bodyRule)) -> match bodyP {
                case BodyPredicate.BodyAtom(p, _, _, _, _) =>
                    buildProof(p, bodyFact, bodyDepth, bodyRule, rules, provIdb, lookupStruct, rc)
                case _      => unreachable!()
            });
            ProofTree.IDB(predSym, fact, childProofs)
        }
    }

    def getMatchingBody(
        fact: Vector[Boxed],
        depth: Int64,
        rc: Region[r],
        provIdb: ProvIDB,
        lookupStruct: ProvLookupStruct[r],
        rule: Constraint
    ): Vector[(Vector[Boxed], Int64, Int32)] \ r = {
        let Constraint.Constraint(HeadPredicate.HeadAtom(_, _, headTerms), bodyPreds) = rule;
        let bodyValues = Array.init(rc, _ -> None, Vector.length(bodyPreds));
        let getValOfVar = MutMap.empty(rc);
        let headApps = Vector.zip(headTerms, fact) |>
        Vector.filter(match (h, _) -> match h {
            case (HeadTerm.App0(_)) => false // Must be true.
            case (HeadTerm.App1(_, _)) => true
            case (HeadTerm.App2(_, _, _)) => true
            case (HeadTerm.App3(_, _, _, _)) => true
            case (HeadTerm.App4(_, _, _, _, _)) => true
            case (HeadTerm.App5(_, _, _, _, _, _)) => true
            case _ => false
        });

        def getVal(varName) = getOrCrash(MutMap.get(varName, getValOfVar));
        def putVals(bodyTerms, matchedVFact) = bodyTerms |> Vector.forEachWithIndex(i -> v ->
            MutMap.put(v, Vector.get(i, matchedVFact), getValOfVar)
        );
        let guardFromApp = () -> headApps |>
            Vector.forAll(match (app, val) -> match app {
                case (HeadTerm.App1(f, v1))                 => val == f(getVal(v1))
                case (HeadTerm.App2(f, v1, v2))             => val == f(getVal(v1), getVal(v2))
                case (HeadTerm.App3(f, v1, v2, v3))         => val == f(getVal(v1), getVal(v2), getVal(v3))
                case (HeadTerm.App4(f, v1, v2, v3, v4))     => val == f(getVal(v1), getVal(v2), getVal(v3), getVal(v4))
                case (HeadTerm.App5(f, v1, v2, v3, v4, v5)) => val == f(getVal(v1), getVal(v2), getVal(v3), getVal(v4), getVal(v5))
                case _ => unreachable!()
            });
        
        def loop(index) = {
            if (index == Vector.length(bodyPreds)) {
                guardFromApp()
            } else {
                // This could, for performance something that was done once and only once. Would
                // require new representation.
                match Vector.get(index, bodyPreds) {
                    case BodyPredicate.BodyAtom(pred, _, Polarity.Positive, _, expected) =>
                        let filterAsList = expected |> Vector.foldLeft(match (acc, i) -> t -> match t {
                            case BodyTerm.Wild => (acc, i + 1)
                            case BodyTerm.Var(v) => match MutMap.get(v, getValOfVar) {
                                case None => (acc, i + 1)
                                case Some(val) => ((i, val) :: acc, i + 1)
                            }
                            case BodyTerm.Lit(val) => ((i, val) :: acc, i + 1)
                        }, (Nil, 0)) |> fst |> List.toVector |> Vector.reverse;
                        let nowBoundVars = expected |> Vector.filterMap(t -> match t {
                            case BodyTerm.Var(v) => match MutMap.get(v, getValOfVar) {
                                case None => Some(v)
                                case Some(_) => None
                            }
                            case _ => None
                        });
                        let matches = lookup(provIdb, rc, filterAsList, Vector.length(expected), lookupStruct, pred);
                        match matches {
                            case None => false
                            case Some(facts) => {
                                facts |> List.exists(match (bodyFact, bodyDepth, bodyRule) -> {
                                    if(bodyDepth >= depth) {
                                        false
                                    } else {
                                        let c1 = Counter.fresh(rc);
                                        let c2 = Counter.fresh(rc);
                                        let completeFact = Vector.range(0, Vector.length(expected)) |>
                                        Vector.map(i -> {
                                            if(Counter.get(c1) < Vector.length(filterAsList) and i == fst(Vector.get(Counter.get(c1), filterAsList))) {
                                                snd(Vector.get(Counter.getAndIncrement(c1), filterAsList))
                                            } else {
                                                Vector.get(Counter.getAndIncrement(c2), bodyFact)
                                            }
                                        });
                                        Array.put(Some((completeFact, bodyDepth, bodyRule)), index, bodyValues);
                                        putVals(nowBoundVars, bodyFact);
                                        loop(index + 1)
                                    }
                                })
                            }
                        }
                    case BodyPredicate.BodyAtom(pred, _, Polarity.Negative, _, expected) =>
                        let vals = expected |> Vector.map(t -> match t {
                            case BodyTerm.Var(v) => getVal(v)
                            case BodyTerm.Lit(val) => val
                            case BodyTerm.Wild => unreachable!()
                        });
                        let isNonMatch = match Map.get(pred, provIdb) {
                            case None => true
                            case Some(facts) => not Map.memberOf(vals, facts)
                        };
                        if(not isNonMatch)
                            false
                        else {
                            // No need to save the match. Negative atoms cannot bind variables.
                            Array.put(Some((vals, -2i64, -2)), index, bodyValues);
                            loop(index + 1)
                        }
                    case BodyPredicate.Guard0(f) =>
                        if(f())
                            loop(index + 1)
                        else false
                    case BodyPredicate.Guard1(f, v1) =>
                        if(f(getVal(v1)))
                            loop(index + 1)
                        else false
                    case BodyPredicate.Guard2(f, v1, v2) =>
                        if(f(getVal(v1), getVal(v2)))
                            loop(index + 1)
                        else false
                    case BodyPredicate.Guard3(f, v1, v2, v3) =>
                        if(f(getVal(v1), getVal(v2), getVal(v3)))
                            loop(index + 1)
                        else false
                    case BodyPredicate.Guard4(f, v1, v2, v3, v4) =>
                        if(f(getVal(v1), getVal(v2), getVal(v3), getVal(v4)))
                            loop(index + 1)
                        else false
                    case BodyPredicate.Guard5(f, v1, v2, v3, v4, v5) =>
                        if(f(getVal(v1), getVal(v2), getVal(v3), getVal(v4), getVal(v5)))
                            loop(index + 1)
                        else false
                    // Functional in provenance is not supported.
                    case BodyPredicate.Functional(_, _, _) => unreachable!()
                }
            }};
        headTerms |> Vector.mapWithIndex(i -> h -> match h {
            case HeadTerm.Var(v) => MutMap.put(v, Vector.get(i, fact), getValOfVar)
            case _ => ()
        });
        loop(0);
        bodyValues |> Array.filterMap(rc, identity) |> Array.toVector
    }
}
