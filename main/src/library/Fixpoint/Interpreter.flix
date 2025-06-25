/*
 * Copyright 2021 Benjamin Dahse
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

mod Fixpoint.Interpreter {
    use Fixpoint.Ast.ExecutableRam.{RamStmt, RelOp, RamTerm, BoolExp, RamProgram, WriteTuple}
    use Fixpoint.Ast.Ram.{RelSym, toDenotation, Predicates, arityOfNonLat, toId, RamId, Search}
    use Fixpoint.Ast.Shared.{BoxedDenotation => Denotation}
    use Fixpoint.Ast.Shared.Denotation.{Latticenal, Relational}
    use Fixpoint.Boxed
    use Fixpoint.Boxing.{boxWith, unboxWith}
    use Fixpoint.BoxingType.{Boxing, RamIdToPos}
    use Fixpoint.Counter
    use Fixpoint.Util.{getOrCrash}
    use Fixpoint.JoinProfiler.getJoinEstimateNum
    use Fixpoint.Predicate.{allFullRelSyms}

    ///
    /// A
    ///
    type alias Tuple = Vector[Int64]

    ///
    /// The number of times the interpreter can branch recursively on a `RelOp.Search`.
    ///
    type alias AllowedBranches = Int32

    type alias SearchTuple[r: Region] = Array[Int64, r]

    ///
    /// An index mapping a tuple to its lattice element.
    ///
    type alias Index[r: Region] = BPlusTree[Tuple, Boxed, r]

    ///
    /// The indexes to be used in the program.
    ///
    type alias Indexes[r: Region] = Array[Index[r], r]

    @Internal
    pub type alias Database[r: Region] = MutMap[RelSym, MutMap[Vector[Boxed], Boxed, r], r]

    type alias SearchEnv[r: Region] = (
        Vector[SearchTuple[r]], 
        Vector[SearchTuple[r]], 
        Array[Tuple, r],
        Array[Boxed, r]
    )

    type alias Context[r: Region] = (
        Indexes[r],
        SearchEnv[r],
        Boxing[r]
    )
    
    def lookupIndex(pos: Int32, indexes: Indexes[r]): Index[r] \ r = 
        Array.get(pos, indexes)

    def storeIndex(index: Index[r], pos: Int32, indexes: Indexes[r]): Unit \ r = 
        Array.put(index, pos, indexes)

    def mkIndex(
        rc: Region[r], 
        relSym: RelSym, 
        search: Vector[Int32], 
        tuples: Vector[(Tuple, Boxed)]
    ): Index[r] \ r = 
        let index = BPlusTree.emptyWithArityAndSearch(rc, Fixpoint.Options.usedArity(), search);
        if(Vector.isEmpty(tuples)) 
            index
        else {
            Vector.forEach(match (nonLat, lat) -> {
                match toDenotation(relSym) {
                    case Relational => 
                        BPlusTree.put(nonLat, lat, index)
                    case Latticenal(_, _, lub, _) =>
                        BPlusTree.putWith(lub, nonLat, lat, index)
                }
            }, tuples);
            index
        }

    @Internal
    pub def estimateJoinSizes(rc: Region[r], input: (RamProgram, Boxing[r])): Array[MutList[(Int32, Int32), r], r] \ r = 
        let expectedJoinSize = Array.empty(rc, getJoinEstimateNum(fst(input)));
        expectedJoinSize |> Array.transform(_ -> MutList.empty(rc));
        let _ = interpretWithInput(rc, Some(expectedJoinSize), input);
        expectedJoinSize        

    @Internal
    pub def interpret(rc: Region[r], input: (RamProgram, Boxing[r])): (Database[r], Predicates) \ r = 
        interpretWithInput(rc, None, input)

    def interpretWithInput(
        rc: Region[r], 
        expectedJoinSize: Option[Array[MutList[(Int32, Int32), r], r]],
        input: (RamProgram, Boxing[r])
    ): (Database[r], Predicates) \ r =
        let (program, boxing) = input;
        let indexes = match program {
            case RamProgram.Program(_, facts, _, (indexMap, posMap), _, _) => 
                let indexNum = match Map.maximumValue(posMap) {
                    case None => 0
                    case Some((_, v)) => v + 1
                };
                let indexes = Array.empty(rc, indexNum);
                indexMap |>
                Map.forEach(relSym -> searches -> {
                    let tuples = Map.getWithDefault(relSym, Vector#{}, facts);
                    searches |> Vector.forEachWithIndex(num -> search -> {
                        let pos = match Map.get((relSym, num), posMap) {
                            case Some(v) => v
                            case None => bug!("In Fixpoint.Interpreter.interpret: ${relSym} has no index!")
                        };
                        storeIndex(mkIndex(rc, relSym, search, tuples), pos, indexes)
                    })
                });
                indexes
        };
        interpretWithDatabase(rc, indexes, boxing, expectedJoinSize, program)

    def interpretWithDatabase(
        rc: Region[r], 
        db: Indexes[r], 
        boxing: Boxing[r], 
        expectedJoinSize: Option[Array[MutList[(Int32, Int32), r], r]],
        program: RamProgram
    ): (Database[r], Predicates) \ r = match program {
        case RamProgram.Program(stmt, _, predState, (_, indexPos), (arities, constWrites), marshallIndexes) =>
            let minEnv = arities |> Vector.map(x -> Array.repeat(rc, x, Int64.minValue()));
            let maxEnv = arities |> Vector.map(x -> Array.repeat(rc, x, Int64.maxValue()));
            constWrites |> Vector.forEach(match (id1, id2, val) -> {
                Array.put(val, id2, Vector.get(id1, minEnv));
                Array.put(val, id2, Vector.get(id1, maxEnv))
            });
            let tupleEnv = Array.repeat(rc, Vector.length(arities), Vector#{});
            let latEnv = arities |> Vector.length |> Array.empty(rc);
            let env = (minEnv, maxEnv, tupleEnv, latEnv);
            let ctxt = (db, env, boxing);
            evalStmt(rc, ctxt, expectedJoinSize, Fixpoint.Options.parLevel(), stmt);
            // Don't insert when doing join size estimation. It is not used and is expensive.
            match expectedJoinSize {
                case None => (marshallDb(rc, db, boxing, indexPos, predState, marshallIndexes), predState)
                case Some(_) => (MutMap.empty(rc), predState)
            }
    }


    def marshallDb(rc: Region[r], db: Indexes[r], boxing: Boxing[r], indexPos: Map[(RelSym, Int32), Int32], predTrack: Predicates, boxingIndexes: RamIdToPos): Database[r] \ r =
        let res = MutMap.empty(rc);
        allFullRelSyms(predTrack) |>
        List.forEach(relSym -> {
            let innerMap = MutMap.empty(rc);
            let curBoxingInfo = Vector.range(0, arityOfNonLat(relSym) + 2) |>
                Vector.map(i ->
                    getOrCrash(Map.get(RamId.RelPos(toId(relSym), i), boxingIndexes))
                );
            Array.get(getOrCrash(Map.get((relSym, 0), indexPos)), db) |>
            BPlusTree.forEach(vec -> latticeElem -> {
                let boxedVec = vec |> Vector.mapWithIndex(i -> val -> boxWith(val, Vector.get(i, curBoxingInfo), boxing));
                MutMap.put(boxedVec, latticeElem, innerMap)
            });
            MutMap.put(relSym, innerMap, res)
        });
        res

    def evalStmt(
        rc: Region[r], 
        ctxt: Context[r], 
        expectedJoinSize: Option[Array[MutList[(Int32, Int32), r], r]],
        parLevel: AllowedBranches,
        stmt: RamStmt
    ): Unit \ r = match stmt {
        case RamStmt.Insert(relOp) =>
            evalOp(rc, ctxt, parLevel, relOp)
        case RamStmt.MergeInto(srcIndex, dstIndex, Relational) =>
            let (db, _, _) = ctxt;
            let src = lookupIndex(srcIndex, db);
            let dst = lookupIndex(dstIndex, db);
            BPlusTree.merge(src, dst)
        case RamStmt.MergeInto(srcIndex, dstIndex, Latticenal(_, _, lub, _)) =>
            let (db, _, _) = ctxt;
            let src = lookupIndex(srcIndex, db);
            let dst = lookupIndex(dstIndex, db);
            BPlusTree.mergeWith(lub, src, dst)
        case RamStmt.Swap(lhs, rhs) =>
            let (db, _, _) = ctxt;
            let temp = lookupIndex(lhs, db);
            storeIndex(lookupIndex(rhs, db), lhs, db);
            storeIndex(temp, rhs, db)
        case RamStmt.Purge(index) => 
            let (db, _, _) = ctxt;
            let oldIndex = lookupIndex(index, db);
            let newIndex = BPlusTree.emptyWithArityAndSearch(rc, Fixpoint.Options.usedArity(), BPlusTree.search(oldIndex));
            storeIndex(newIndex, index, db)
        case RamStmt.Seq(stmts) => 
            Vector.forEach(evalStmt(rc, ctxt, expectedJoinSize, parLevel), stmts)
        case RamStmt.Until(test, body) =>
            if (evalBoolExps(ctxt, test)) {
                ()
            } else {
                evalStmt(rc, ctxt, expectedJoinSize, parLevel, body);
                evalStmt(rc, ctxt, expectedJoinSize, parLevel, stmt)
            }
        case RamStmt.Comment(_) => ()
        case RamStmt.Par(stmts) => region rc2 {
            stmts |> Vector.forEach(innerStmt -> unchecked_cast({
                let _: Unit = spawn unchecked_cast({
                    let threadCtxt = makeCtxt(rc, ctxt);
                    evalStmt(rc, threadCtxt, expectedJoinSize, parLevel, innerStmt)
                } as _ \ IO) @ rc2; // spawn may not take an r effect, so we cast it to IO
                ()
            } as _ \ rc2)) // The IO effect is undesirable, so we cast it back to an r effect
        }
        case RamStmt.EstimateJoinSize(indexPos, writeTo, attr) =>
            let prevRef = Ref.fresh(rc, None);
            let dupRef = Counter.fresh(rc);
            let sizeRef = Counter.fresh(rc);
            let (db, _, _) = ctxt;
            let relIndex = lookupIndex(indexPos, db);
            relIndex |> BPlusTree.forEach(curr -> _ -> {
                let isDup = 
                    Ref.get(prevRef) |> 
                    Option.exists(prev -> 
                        attr |> Vector.forAll(i -> Vector.get(i, prev) == Vector.get(i, curr))
                    );
                if (isDup) {
                    Counter.increment(dupRef)
                } else ();
                Ref.put(Some(curr), prevRef);
                Counter.increment(sizeRef)
            });
            let size = Counter.get(sizeRef);
            let dup = Counter.get(dupRef);
            MutList.push((size, dup), Array.get(writeTo, getOrCrash(expectedJoinSize)))
    }

    def evalOp(rc: Region[r], ctxt: Context[r], parLevel: AllowedBranches, op: RelOp): Unit \ r = 
        let (db, env, boxing) = ctxt;
        match op {
            case RelOp.Search(tuplePos, searchIndex, _, Relational, writes, body) =>
                if(parLevel == 0) {
                    lookupIndex(searchIndex, db) |>
                        BPlusTree.forEach(relationHandlingBodyFunc(rc, tuplePos, writes, body, ctxt, parLevel))
                } else {
                    let newCtxt = (db, env, boxing);
                    lookupIndex(searchIndex, db) |>
                        BPlusTree.parForEach(parRelationHandlingBodyFunc(rc, tuplePos, writes, body, newCtxt, parLevel - 1))
                }
            case RelOp.Query(tuplePos, searchIndex, _, Relational, writes, body) =>
                let (minEnv, maxEnv, _, _) = env;
                lookupIndex(searchIndex, db) |>
                BPlusTree.rangeQueryWith(
                    relationHandlingBodyFunc(rc, tuplePos, writes, body, ctxt, parLevel),
                    // We could here use Vector.toArray, but it would create a copy. To avoid memory
                    // allocation we simply cast.
                    unchecked_cast((Vector.get(tuplePos, minEnv): Array[Int64, r]) as Tuple),
                    unchecked_cast((Vector.get(tuplePos, maxEnv): Array[Int64, r]) as Tuple)
                )
            case RelOp.If(test, then) =>
                if (evalBoolExps(ctxt, test))
                    evalOp(rc, ctxt, parLevel, then)
                else
                    ()
            case RelOp.Project(terms, rel, Relational) =>
                let relIndex = lookupIndex(rel, db);
                let tuple = Vector.map(evalTerm(env, boxing), terms);
                BPlusTree.put(tuple, Boxed.NoValue, relIndex)
            case RelOp.Search(tuplePos, searchIndex, meetWith, Latticenal(bot, leq, _, glb), writes, body) => 
                if(parLevel == 0) {
                    lookupIndex(searchIndex, db) |> 
                    BPlusTree.forEach(latticeHandlingBodyFunc(rc, tuplePos, meetWith, glb, leq, bot, writes, body, ctxt, parLevel))
                } else {
                    let newCtxt = (db, env, boxing);
                    lookupIndex(searchIndex, db) |> 
                    BPlusTree.parForEach(parLatticeHandlingBodyFunc(rc, tuplePos, meetWith, glb, leq, bot, writes, body, newCtxt, parLevel))
                }
            case RelOp.Query(tuplePos, searchIndex, meetWith, Latticenal(bot, leq, _, glb), writes, body) => 
                let (minEnv, maxEnv, _, _) = env;
                lookupIndex(searchIndex, db) |>
                BPlusTree.rangeQueryWith(
                    latticeHandlingBodyFunc(rc, tuplePos, meetWith, glb, leq, bot, writes, body, ctxt, parLevel),
                    // We could here use Vector.toArray, but it would create a copy. To avoid memory
                    // allocation we simply cast.
                    unchecked_cast((Vector.get(tuplePos, minEnv): Array[Int64, r]) as Tuple),
                    unchecked_cast((Vector.get(tuplePos, maxEnv): Array[Int64, r]) as Tuple)
                )
            case RelOp.Project(terms, rel, Latticenal(bot, leq, lub, _)) =>
                let relIndex = lookupIndex(rel, db);
                let len = Vector.length(terms);
                let tuple = evalTermsWithLat(ctxt, terms);
                let latVal = evalBoxedTerm(env, boxing, Vector.get(len - 1, terms));
                if (latVal `leq` bot) ()
                else BPlusTree.putWith(lub, tuple, latVal, relIndex)
            case RelOp.Functional(tupleIndex, f, terms, writes, body, i2) =>
                let args = 
                    terms |> 
                    Vector.map(evalBoxedTerm(env, boxing));
                let result = 
                    f(args)|> 
                    Vector.map(vec ->
                        Vector.mapWithIndex(i -> x -> unboxWith(x, Vector.get(i, i2), boxing), vec)
                    );
                let (minEnv, maxEnv, tupleEnv, _) = env;
                result |> Vector.forEach(t -> {
                    writes |> Vector.forEach(match (srcIndex, dst, dstIndex) -> {
                        Array.put(Vector.get(srcIndex, t), dstIndex, Vector.get(dst, minEnv));
                        Array.put(Vector.get(srcIndex, t), dstIndex, Vector.get(dst, maxEnv))
                    });
                    Array.put(t, tupleIndex, tupleEnv);
                    evalOp(rc, ctxt, parLevel, body)
                })
        }

    def handleWriteTuples(
        t: Tuple,
        writes: Vector[WriteTuple],
        minEnv: Vector[SearchTuple[r]],
        maxEnv: Vector[SearchTuple[r]],
        tuplePos: Int32,
        tupleEnv: Array[Tuple, r]
    ): Unit \ r =
        writes |> Vector.forEach(match (srcIndex, dst, dstIndex) -> {
            Array.put(Vector.get(srcIndex, t), dstIndex, Vector.get(dst, minEnv));
            Array.put(Vector.get(srcIndex, t), dstIndex, Vector.get(dst, maxEnv))
        });
        Array.put(t, tuplePos, tupleEnv)

    def parRelationHandlingBodyFunc(
        rc: Region[r],
        tuplePos: Int32,
        writes: Vector[WriteTuple],
        body: RelOp,
        ctxt: Context[r],
        parLevel: AllowedBranches,
        t: Tuple,
        ignored: Boxed
    ): Unit \ r =
        relationHandlingBodyFunc(rc, tuplePos, writes, body, makeCtxt(rc, ctxt), parLevel, t, ignored)

    def makeCtxt(rc: Region[r], ctxt: Context[r]): Context[r] \ r = {
        let (db, (minEnv, maxEnv, tupleEnv, latEnv), boxing) = ctxt;
        let threadMinEnv = minEnv |> Vector.map(x -> Array.copyOfRange(rc, 0, Array.length(x), x));
        let threadMaxEnv = maxEnv |> Vector.map(x -> Array.copyOfRange(rc, 0, Array.length(x), x));
        let threadTupleEnv = Array.copyOfRange(rc, 0, Array.length(tupleEnv), tupleEnv);
        let threadLatEnv = Array.copyOfRange(rc, 0, Array.length(latEnv), latEnv);
        let threadEnv = (threadMinEnv, threadMaxEnv, threadTupleEnv, threadLatEnv);
        (db, threadEnv, boxing)
    }


    def relationHandlingBodyFunc(
        rc: Region[r],
        tuplePos: Int32,
        writes: Vector[WriteTuple],
        body: RelOp,
        ctxt: Context[r],
        parLevel: AllowedBranches,
        t: Tuple,
        _: Boxed
    ): Unit \ r =
        let (_, env, _) = ctxt;
        let (minEnv, maxEnv, tupleEnv, _) = env;
        handleWriteTuples(t, writes, minEnv, maxEnv, tuplePos, tupleEnv);
        evalOp(rc, ctxt, parLevel, body)

    def parLatticeHandlingBodyFunc(
        rc: Region[r],
        tuplePos: Int32,
        meetWith: Int32,
        glb: Boxed -> Boxed -> Boxed,
        leq: Boxed -> Boxed -> Bool,
        bot: Boxed,
        writes: Vector[WriteTuple],
        body: RelOp,
        ctxt: Context[r],
        parLevel: AllowedBranches,
        t: Tuple,
        l: Boxed
    ): Unit \ r =
    latticeHandlingBodyFunc(rc, tuplePos, meetWith, glb, leq, bot, writes, body, makeCtxt(rc, ctxt), parLevel, t, l)


    def latticeHandlingBodyFunc(
        rc: Region[r],
        tuplePos: Int32,
        meetWith: Int32,
        glb: Boxed -> Boxed -> Boxed,
        leq: Boxed -> Boxed -> Bool,
        bot: Boxed,
        writes: Vector[WriteTuple],
        body: RelOp,
        ctxt: Context[r],
        parLevel: AllowedBranches,
        t: Tuple,
        l: Boxed
    ): Unit \ r =
        let (_, env, _) = ctxt;
        let (minEnv, maxEnv, tupleEnv, latEnv) = env;
        handleWriteTuples(t, writes, minEnv, maxEnv, tuplePos, tupleEnv);
        // Recurse only if the meet is not bottom
        if (meetWith == tuplePos) {
            Array.put(l, tuplePos, latEnv);
            evalOp(rc, ctxt, parLevel, body)
        } else {
            let meet = l `glb` Array.get(meetWith, latEnv);
            if (meet `leq` bot) ()
            else {
                Array.put(meet, tuplePos, latEnv);
                evalOp(rc, ctxt, parLevel, body)
            }
        }

    def evalTermsWithLat(ctxt: Context[r], terms: Vector[RamTerm]): Tuple \ r =
        let (_, env, boxing) = ctxt;
        let evalT = evalTerm(env, boxing);
        let len = Vector.length(terms);
        Vector.range(0, len - 1) |> 
        Vector.map(i -> evalT(Vector.get(i, terms)))

    def evalBoolExps(ctxt: Context[r], exps: Vector[BoolExp]): Bool \ r =
        let (db, env, boxing) = ctxt;
        let evalT = evalTerm(env, boxing);
        let evalBoxedT = evalBoxedTerm(env, boxing);
        def evalBoolExp(exp) = match exp {
            case BoolExp.Not(boolExp) => not evalBoolExp(boolExp)
            case BoolExp.IsEmpty(rel) => BPlusTree.isEmpty(Array.get(rel, db))
            case BoolExp.NotMemberOf(terms, rel, Relational) =>
                let relIndex = lookupIndex(rel, db);
                let tuple = Vector.map(evalT, terms);
                not BPlusTree.memberOf(tuple, relIndex)
            case BoolExp.NotMemberOf(terms, rel, Latticenal(_, leq, _, _)) =>
                let relIndex = lookupIndex(rel, db);
                let len = Vector.length(terms);
                let tuple = evalTermsWithLat(ctxt, terms);
                let latVal = evalBoxedTerm(env, boxing, Vector.get(len - 1, terms));
                let curLatVal = BPlusTree.getWithDefault(tuple, Boxed.NoValue, relIndex);
                if(curLatVal == Boxed.NoValue)
                    true
                else
                    not (latVal `leq` curLatVal)
            case BoolExp.Eq(lhs, rhs) => evalTerm(env, boxing, lhs) == evalTerm(env, boxing, rhs)
            case BoolExp.Leq(lhs, leq, index) => 
                let (_, _, _, latEnv) = env;
                let rightSide = Array.get(index, latEnv);
                leq(lhs, rightSide)
            case BoolExp.Guard1(f, t1) =>
                let boxed1 = evalBoxedT(t1);
                f(boxed1)
            case BoolExp.Guard2(f, t1, t2) =>
                let boxed1 = evalBoxedT(t1);
                let boxed2 = evalBoxedT(t2);
                f(boxed1)(boxed2)
            case BoolExp.Guard3(f, t1, t2, t3) =>
                let boxed1 = evalBoxedT(t1);
                let boxed2 = evalBoxedT(t2);
                let boxed3 = evalBoxedT(t3);
                f(boxed1)(boxed2)(boxed3)
            case BoolExp.Guard4(f, t1, t2, t3, t4) =>
                let boxed1 = evalBoxedT(t1);
                let boxed2 = evalBoxedT(t2);
                let boxed3 = evalBoxedT(t3);
                let boxed4 = evalBoxedT(t4);
                f(boxed1)(boxed2)(boxed3)(boxed4)
            case BoolExp.Guard5(f, t1, t2, t3, t4, t5) =>
                let boxed1 = evalBoxedT(t1);
                let boxed2 = evalBoxedT(t2);
                let boxed3 = evalBoxedT(t3);
                let boxed4 = evalBoxedT(t4);
                let boxed5 = evalBoxedT(t5);
                f(boxed1)(boxed2)(boxed3)(boxed4)(boxed5)
        };
        exps |> Vector.forAll(evalBoolExp)

    def evalBoxedTerm(env: SearchEnv[r], boxing: Boxing[r], term: RamTerm): Boxed \ r = 
        let evalT = evalBoxedTerm(env, boxing);
        match term {
            case RamTerm.Lit(_, b) => b
            case RamTerm.LoadFromTuple(tupleIndex, indexInTuple, i) => 
                let (_, _, tupleEnv, _) = env;
                let unboxed = Vector.get(indexInTuple, Array.get(tupleIndex, tupleEnv));
                boxWith(unboxed, i, boxing)
            case RamTerm.ProvMax(_) => Boxed.BoxedInt64(evalTerm(env, boxing, term))
            case RamTerm.LoadLatVar(index, _) =>
                let (_, _, _, latEnv) = env;
                Array.get(index, latEnv)
            case RamTerm.Meet(cap, lhs, rhs, _) =>
                let boxed1 = evalT(lhs);
                let boxed2 = evalT(rhs);
                boxed1 `cap` boxed2
            case RamTerm.App1(f, t, _) =>
                let v1 = evalT(t);
                f(v1)
            case RamTerm.App2(f, t1, t2, _) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                f(v1)(v2)
            case RamTerm.App3(f, t1, t2, t3, _) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                f(v1)(v2)(v3)
            case RamTerm.App4(f, t1, t2, t3, t4, _) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let v4 = evalT(t4);
                f(v1)(v2)(v3)(v4)
            case RamTerm.App5(f, t1, t2, t3, t4, t5, _) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let v4 = evalT(t4);
                let v5 = evalT(t5);
                f(v1)(v2)(v3)(v4)(v5)
        }

    def evalTerm(env: SearchEnv[r], boxing: Boxing[r], term: RamTerm): Int64 \ r = 
        let evalBoxedT = evalBoxedTerm(env, boxing);
        match term {
            case RamTerm.Lit(v, _) => v
            case RamTerm.LoadFromTuple(tupleIndex, indexInTuple, _) =>
                let (_, _, tupleEnv, _) = env;
                Vector.get(indexInTuple, Array.get(tupleIndex, tupleEnv))
            case RamTerm.LoadLatVar(index, boxingPos) => 
                let (_, _, _, latEnv) = env;
                unboxWith(Array.get(index, latEnv), boxingPos, boxing)
            case RamTerm.ProvMax(vec) =>
                let (_, _, tupleEnv, _) = env;
                1i64 + Vector.foldLeft(acc -> match (tupleIndex, indexInTuple) -> 
                    acc `Int64.max` Vector.get(indexInTuple, Array.get(tupleIndex, tupleEnv))
                , 0i64, vec)
            case RamTerm.Meet(cap, lhs, rhs, i) =>
                let boxed1 = evalBoxedT(lhs);
                let boxed2 = evalBoxedT(rhs);
                unboxWith(boxed1 `cap` boxed2, i, boxing)
            case RamTerm.App1(f, t, i) =>
                let boxed = evalBoxedT(t);
                unboxWith(f(boxed), i, boxing)
            case RamTerm.App2(f, t1, t2, i) =>
                let boxed1 = evalBoxedT(t1);
                let boxed2 = evalBoxedT(t2);
                unboxWith(f(boxed1)(boxed2), i, boxing)
            case RamTerm.App3(f, t1, t2, t3, i) =>
                let boxed1 = evalBoxedT(t1);
                let boxed2 = evalBoxedT(t2);
                let boxed3 = evalBoxedT(t3);
                unboxWith(f(boxed1)(boxed2)(boxed3), i, boxing)
            case RamTerm.App4(f, t1, t2, t3, t4, i) =>
                let boxed1 = evalBoxedT(t1);
                let boxed2 = evalBoxedT(t2);
                let boxed3 = evalBoxedT(t3);
                let boxed4 = evalBoxedT(t4);
                unboxWith(f(boxed1)(boxed2)(boxed3)(boxed4), i, boxing)
            case RamTerm.App5(f, t1, t2, t3, t4, t5, i) =>
                let boxed1 = evalBoxedT(t1);
                let boxed2 = evalBoxedT(t2);
                let boxed3 = evalBoxedT(t3);
                let boxed4 = evalBoxedT(t4);
                let boxed5 = evalBoxedT(t5);
                unboxWith(f(boxed1)(boxed2)(boxed3)(boxed4)(boxed5), i, boxing)
        }

}
