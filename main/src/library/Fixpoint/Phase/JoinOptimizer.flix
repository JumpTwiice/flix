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

mod Fixpoint.Phase.JoinOptimizer {
    use Fixpoint.Ast.Ram.{RamProgram, RamStmt, RowVar, RelOp, RelSym}
    use Fixpoint.Util.{getOrCrash, collectRowVarRelSym}
    use Fixpoint.Options.{profilerMinimumFacts, profilerDiscrimination, profilerSeed, profilerFactLowerBound, disableJoinOptimizer}
    use Fixpoint.JoinProfiler
    use Fixpoint.JoinProfiler.JoinProfile

    ///
    /// Optimizes the join order of the rules in `program`. This is done by first running
    /// the program using the join profiler with a smaller representative input. This
    /// produces statistics on relation sizes which are used to derive a cost function.
    /// Selinger's algorithm is then run with the cost function to compute the optimal
    /// join order.
    ///
    /// If the number of facts in the program is smaller than `profilerMinimumFacts`, this
    /// phase is skipped.
    ///
    @Internal
    pub def scheduleProgram(program: RamProgram): RamProgram = 
        if (disableJoinOptimizer()) program
        else {
            let RamProgram.Program(_, facts, _, _) = program;
            let numOfFacts = Map.foldLeft(acc -> l -> acc + Vector.length(l) |> Int32.toInt64, 0i64, facts);
            if (numOfFacts < profilerMinimumFacts()) {
                program 
            } else scheduleProgramInternal(program)
        }
        
    ///
    /// Performs join reordering of the statements in `program` by running the join
    /// profiler on a representative input. The representative input is generated for each
    /// relation by flipping a biased coin with `p = profilerDiscrimination` for every
    /// input fact in that relation. If the number of chosen facts for a relation is less
    /// than `profilerFactLowerBound`, the facts in that relation are shuffled and the
    /// first `profilerFactLowerBound` facts are chosen.
    ///
    def scheduleProgramInternal(program: RamProgram): RamProgram = match program {
        case RamProgram.Program(stmt, facts, predState, indexInfo) => 
            let takeRandomFacts = fs -> {
                let filtered = Vector.filter(_ -> Random.randomFloat64() <= profilerDiscrimination(), fs);
                if (Vector.length(filtered) < profilerFactLowerBound()) {
                    // Cast NonDet to Random.
                    let shuffled = unchecked_cast(Vector.shuffle(fs) as _ \ Random);
                    Vector.take(profilerFactLowerBound(), shuffled)
                } else filtered
            };
            let profilerFacts = facts |> Map.map(takeRandomFacts |> Random.handleWithSeed(profilerSeed()));
            let programToProfile = RamProgram.Program(stmt, profilerFacts, predState, indexInfo);
            let (profile, attributeMap) = JoinProfiler.profileProgram(programToProfile);
            match profile {
                case JoinProfile.Profile(sizePerIter, expectedJoinSize) => 
                    let rowVarToRel = collectRowVarRelSym(program) |> List.toMap;
                    let arities = Map.map(match RelSym.Symbol(_, arity, _) -> arity, rowVarToRel);
                    let getOptimalJoin = getOptimalJoinWith(expectedJoinSize, sizePerIter, attributeMap, arities);
                    let scheduledStmt = scheduleStmt(getOptimalJoin, stmt);
                    RamProgram.Program(scheduledStmt, facts, predState, indexInfo)
            }
    }

    ///
    /// Reorders the `RelOp`'s in `stmt` based on `getOptimalJoin`.
    ///
    def scheduleStmt(getOptimalJoin: List[RowVar] -> List[RowVar], stmt: RamStmt): RamStmt = match stmt {
        case RamStmt.Insert(op) => RamStmt.Insert(scheduleOp(getOptimalJoin, Nil, Nil, Nil, op))
        case RamStmt.MergeInto(_, _) => stmt
        case RamStmt.Swap(_, _) => stmt
        case RamStmt.Purge(_) => stmt
        case RamStmt.Seq(xs) => RamStmt.Seq(Vector.map(scheduleStmt(getOptimalJoin), xs))
        case RamStmt.Par(xs) => RamStmt.Par(Vector.map(scheduleStmt(getOptimalJoin), xs))
        case RamStmt.Until(boolExps, body) => RamStmt.Until(boolExps, scheduleStmt(getOptimalJoin, body))
        case RamStmt.EstimateJoinSize(_, _, _, _) => unreachable!()
        case RamStmt.Comment(_) => stmt
    }

    ///
    /// Reorders `op` according to the the optimal join order given by `getOptimalJoin`
    /// and places `RelOp`'s that are independent of the join order at the bottom of the
    /// nesting.
    ///
    /// `getOptimalJoin` is a function that returns the optimal join order of the given
    /// list of `RowVar`'s'.
    ///
    /// `independent` are `RelOp`'s whose order are decided in a later phase (e.g.
    /// Hoisting).
    ///
    /// `ops` is the list of `RelOp` to be reordered.
    ///
    /// `rowVars` is the list of `RowVar`'s associated with `ops`.
    ///
    def scheduleOp(
        getOptimalJoin: List[RowVar] -> List[RowVar], 
        independent: List[RelOp], 
        ops: List[RelOp], 
        rowVars: List[RowVar], 
        op: RelOp
    ): RelOp = match op {
        case RelOp.Search(rowVar, _, body) => 
            scheduleOp(getOptimalJoin, independent, op :: ops, rowVar :: rowVars, body)
        case RelOp.Query(rowVar, _, _, _, body) => 
            scheduleOp(getOptimalJoin, independent, op :: ops, rowVar :: rowVars, body)
        case RelOp.Functional(_, _, _, body, _) => 
            scheduleOp(getOptimalJoin, op :: independent, ops, rowVars, body)
        case RelOp.Project(_, _, _) =>
            let joinOrder = List.sort(rowVars) |> getOptimalJoin;
            let opsAsVec = List.toVector(ops);
            let opsInJoinOrder = region rc {
                let asArr = Array.empty(rc, List.length(ops));
                rowVars |> List.forEachWithIndex(i -> rv -> {
                    let pos = List.indexOf(rv, joinOrder) |> getOrCrash;
                    Array.put(Vector.get(i, opsAsVec), pos, asArr)
                });
                Array.reverse(asArr);
                Array.toList(asArr)
            };
            let base = independent |> List.foldLeft(acc -> independentOp -> match independentOp {
                case RelOp.Functional(f1, f2, f3, _, f5) => RelOp.Functional(f1, f2, f3, acc, f5)
                case RelOp.If(bools, _) => RelOp.If(bools, acc)
                case _ => unreachable!()
            }, op);
            opsInJoinOrder |> List.foldLeft(acc -> opInOrder -> match opInOrder {
                case RelOp.Search(f1, f2, _) => RelOp.Search(f1, f2, acc)
                case RelOp.Query(f1, f2, f3, f4, _) => RelOp.Query(f1, f2, f3, f4, acc)
                case RelOp.Functional(f1, f2, f3, _, f5) => RelOp.Functional(f1, f2, f3, acc, f5)
                case RelOp.Project(_, _, _) => opInOrder
                case RelOp.If(f1, _) => RelOp.If(f1, acc)
            }, base)
        case RelOp.If(_, body) => 
            scheduleOp(getOptimalJoin, op :: independent, ops, rowVars, body)
    }
    
    ///
    /// Returns the cost to join `s` with `relations`, given the previous optimal joins
    /// and their cost, and the statistics returned from the join profiler.
    ///
    def costToJoin(
        relations: List[RowVar], 
        optimal: MutMap[List[RowVar], (Int64, List[RowVar]), r], 
        tuplesFromJoin: MutMap[List[RowVar], Vector[Int64], r],
        expectedJoinSize: Map[(RowVar, Vector[Int32]), Vector[Int64]],
        attributeMap: Map[RowVar, Map[RowVar, Set[Int32]]],
        arity: Int32,
        s: RowVar
    ): Int64 \ r =
        let map = Map.get(s, attributeMap) |> getOrCrash;
        // Requires that Set orders its elements
        let attr = 
            relations |> 
            List.foldLeft(acc -> rel -> Set.union(acc, Map.get(rel, map) |> getOrCrash), Set#{}) |>
            Set.toList |>
            List.toVector;
        let (costToJoinPrev, _) = MutMap.get(relations, optimal) |> getOrCrash;
        let ith = 
            Vector.zip(
                MutMap.get(relations, tuplesFromJoin) |> getOrCrash, 
                Map.get((s, attr), expectedJoinSize) |> getOrCrash
            ) |>
            Vector.map(match (x, y) -> x * y);
        MutMap.put(s :: relations, ith, tuplesFromJoin);
        let sum = ith |> Vector.foldLeft(acc -> val -> acc + val, 0i64);
        costToJoinPrev + Int32.toInt64(arity) * sum // TODO: Maybe don't multiply by arity
    
    ///
    /// Returns the subset of the powerset of `set` where each element has length `size`.
    ///
    @Internal
    pub def powerSetOfSize(size: Int32, set: List[a]): List[List[a]] = region rc {
        let len = List.length(set);
        if (size > len) {
            bug!("Size greater than len")
        } else if (size == 1) {
            set |> List.map(x -> x :: Nil)
        } else if (size == len) { 
            set :: Nil
        } else {
            let list = MutList.empty(rc);
            def forEach(tail) = match tail {
                case x :: xs if (List.length(xs) >= size - 1) => 
                    def loop(j, sizeSoFar, soFar) = {
                        if (sizeSoFar == size) {
                            MutList.push(soFar |> List.reverse, list)
                        } else {
                            if (len - j < size - sizeSoFar) ()
                            else
                                List.slice(start = j, end = len, xs) |>
                                List.forEachWithIndex(i -> next -> loop(j + i + 1, sizeSoFar + 1, next :: soFar))
                        }
                    };
                    loop(0, 1, x :: Nil);
                    forEach(xs)
                case _ => ()
            };
            forEach(set);
            list |> MutList.toList
        }
    }

    ///
    /// Returns the optimal join order of the `RowVar`'s in `relations` given the
    /// statistics from the join profiler.
    ///
    def getOptimalJoinWith(
        expectedJoinSize: Map[(RowVar, Vector[Int32]), Vector[Int64]],
        sizePerIter: Map[RowVar, Vector[Int64]],
        attributeMap: Map[RowVar, Map[RowVar, Set[Int32]]],
        arities: Map[RowVar, Int32],
        relations: List[RowVar]
    ): List[RowVar] = region rc {
        // The optimal solution is kept in reverse order, but expected in true order.
        let optimal: MutMap[List[RowVar], (Int64, List[RowVar]), rc] = MutMap.empty(rc);
        let tuplesFromJoin: MutMap[List[RowVar], Vector[Int64], rc] = MutMap.empty(rc);
        relations |> List.forEach(rel -> {
            MutMap.put(rel :: Nil, (0i64, rel :: Nil), optimal);
            let sizePerIterForRel = match Map.get(rel, sizePerIter) {
                case None => Vector#{0i64}
                case Some(v) => v
            };
            MutMap.put(rel :: Nil, sizePerIterForRel, tuplesFromJoin)
        });
        let max = List.length(relations);
        def loop(num) = {
            if (num > max) ()
            else {
                powerSetOfSize(num, relations) |>
                List.forEach(set -> {
                    let opt = set |> List.mapWithIndex(i -> x -> {
                        let (ls, right) = List.splitAt(i, set);
                        let rs = List.drop(1, right);
                        let withoutX = ls ::: rs;
                        let prevJoin = MutMap.get(withoutX, optimal) |> getOrCrash |> snd;
                        let optJoin = x :: prevJoin;
                        let arity = Map.get(x, arities) |> getOrCrash;
                        let cost = costToJoin(
                            withoutX, optimal, tuplesFromJoin, expectedJoinSize, attributeMap, arity, x
                        );
                        (cost, optJoin)
                    }) |> List.minimumBy(x -> y -> fst(x) <=> fst(y)) |> getOrCrash;
                    MutMap.put(set, opt, optimal)
                });
                loop(num + 1)
            }
        };
        loop(2);
        // Reverse to get true order.
        match MutMap.get(relations, optimal) {
            case None => Nil
            case Some(v) => snd(v) |> List.reverse
        }
    }
}