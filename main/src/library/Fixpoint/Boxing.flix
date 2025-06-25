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
/// The purpose of this file is to map boxed constants to Int64 
/// since the indices on relations work on Int64 due to the lower
/// complexity of working with integers.
///
mod Fixpoint.Boxing {
    import java.lang.{Float, Double, Object, Character, Runtime}
    use Fixpoint.Ast.Datalog.Datalog
    use Fixpoint.Ast.ExecutableRam.{Facts => EFacts}
    use Fixpoint.Ast.Ram
    use Fixpoint.Ast.Ram.{RamId, RamStmt, RelOp, RamTerm, BoolExp, RelSym, RamProgram, arityOf, arityOfNonLat, toDenotation}
    use Fixpoint.Ast.Shared.{PredSym, isRelational, Denotation}
    use Fixpoint.AtomicCounter
    use Fixpoint.Boxable
    use Fixpoint.Boxed
    use Fixpoint.Boxed.{BoxedBool, BoxedChar, BoxedInt8, BoxedInt16, BoxedInt32, BoxedInt64, BoxedFloat32, BoxedFloat64, BoxedObject}
    use Fixpoint.BoxingType.{Boxing, TypeInfo, Types, setType, getType, RamIdToPos, UnifiedTypePos}
    use Fixpoint.Predicate.relSymsOfProgram
    use Fixpoint.ReadWriteLock
    use Fixpoint.Util.getOrCrash

    ///
    /// Initialize a `Boxing` for `program` and returns it along with the `Int64` representation of all facts
    /// in `program` and a map from `RamId` to the their `UnifiedTypePos`.
    ///
    @Internal
    pub def initialize(rc: Region[r], program: RamProgram): (Boxing[r], EFacts, RamIdToPos) \ r =
        let mapping = Equality.computeMapping(program);
        let boxingInfo = initializeInternal(rc, program, mapping);
        let (facts, newBoxingInfo) = initializeFacts(rc, program, boxingInfo, mapping);
        (newBoxingInfo, facts, mapping)

    ///
    /// Maps facts of `program`, `Map[RelSym, Vector[Vector[Boxed]]]` to `Map[RelSym, Vector[Vector[Int64]]]`
    /// and returns it along a new `Boxing` for `program` which includes the information about the new mapped facts.
    ///
    def initializeFacts(rc1: Region[r], program: RamProgram, boxingInfo: Boxing[r], mapping: RamIdToPos): (EFacts, Boxing[r]) \ r = region rc2 {        
        let RamProgram.Program(_, facts, _, _) = program;
        let factsAsVec = Map.toVector(facts);
        let counters = initializeCounters(rc1, boxingInfo);
        let newFacts = Array.empty(rc2, Vector.length(factsAsVec));
        let funcsToBeRun = factsAsVec |> Vector.mapWithIndex(i -> match (relSym, factVec) -> () -> {
            let mappedResult = mapAllFacts(rc1, relSym, factVec, boxingInfo, counters, mapping);
            Array.put((relSym, mappedResult), i, newFacts)
        });
        spawnFuncs(funcsToBeRun);
        let newBoxing = fixBoxingAfterInit(rc1, counters, boxingInfo);
        (Array.toMap(newFacts), newBoxing)
    }

    ///
    /// Fixed `boxingInfo` after facts have been initialized using the old `boxingInfo` and `counters`.
    ///
    def fixBoxingAfterInit(rc: Region[r], counters: Vector[AtomicCounter[r]], boxingInfo: Boxing[r]): Boxing[r] \ r = {
        let (_, boxToRepVec, typeInfo, locks) = boxingInfo;
        let newBoxedArr = counters |> Vector.map(c -> Array.empty(rc, getOrCrash(Int64.tryToInt32(AtomicCounter.get(c)))));
        let funcsToBeRun = newBoxedArr |>
            Vector.mapWithIndex(i -> writeTo -> () -> {
                match getType(i, typeInfo) {
                    case Types.Object =>
                        let boxToRep = Vector.get(i, boxToRepVec);
                        boxToRep |> BPlusTree.forEach(val -> pos -> Array.put(val, getOrCrash(Int64.tryToInt32(pos)), writeTo))
                    case _ => ()
                }
            });
        spawnFuncs(funcsToBeRun);
        let newMutLists = newBoxedArr |> Vector.map(Array.toMutList(rc));
        (newMutLists, boxToRepVec, typeInfo, locks)
    }

    ///
    /// Spawns all functions in `funcs` and await their termination
    ///
    def spawnFuncs(funcs: Vector[Unit -> Unit \ ef]): Unit \ ef = region rc2 {
        unchecked_cast({
            let _: Unit = spawn unchecked_cast(
                ((funcs |> Vector.forEach(f -> f())): _ \ ef)
            as _ \ IO) @ rc2;
            ()
        } as _ \ ef)
    }

    ///
    /// Returns the number of threads to use for parallel evaluation.
    ///
    /// # SAFETY:
    /// This accesses the runtime environment, which is an effect.
    /// It is assumed that this function is only used in contexts
    /// where this effect is not observable outside of the RedBlackTree module.
    ///
    /// Copy pasted from RedBlackTree.flix.
    ///
    def threads(): Int32 = unsafe {
        // Note: We use a multiple of the number of physical cores for better performance.
        let multiplier = 4;
        multiplier * Runtime.getRuntime().availableProcessors()
    }

    def mapAllFacts(rc1: Region[r],
        relSym: RelSym,
        facts: Vector[Vector[Boxed]],
        boxingInfo: Boxing[r],
        counters: Vector[AtomicCounter[r]],
        mapping: RamIdToPos
    ): Vector[(Vector[Int64], Boxed)] \ r = {
        let relSymId = Ram.toId(relSym);
        let numOfFacts = Vector.length(facts);
        // We need to test for whether there are provenance facts. If `numOfFacts > 0` and 
        // `arity != Vector.length(facts[0])` then there are provenance facts and positions
        // need to be extended by RamId(-1).
        let nonExtendedPositions = Vector.range(0, arityOf(relSym)) |>
            Vector.map(i -> getOrCrash(Map.get(RamId.RelPos(relSymId, i), mapping)));
        let positions = if(numOfFacts == 0 or arityOf(relSym) == Vector.length(Vector.get(0, facts))) {
            nonExtendedPositions
        } else {
            Vector.append(nonExtendedPositions, Vector#{getOrCrash(Map.get(RamId.Id(-1), mapping)), getOrCrash(Map.get(RamId.Id(-1), mapping))})
        };
        let threadNum = threads();
        let resultArr = Array.empty(rc1, numOfFacts);
        if(numOfFacts <= threadNum) {
            mapPartOfVector(facts, 0, numOfFacts, isRelational(toDenotation(relSym)), resultArr, boxingInfo, counters, positions)
        } else {
            let inc = numOfFacts / threadNum;
            let limits = Array.init(rc1, i -> (i * inc, (i + 1) * inc), threadNum);
            Array.put((fst(Array.get(threadNum - 1, limits)), numOfFacts), threadNum - 1, limits);
            let funcsToBeRun = limits |>
            Array.toVector |>
            Vector.map(match (lower, upper) ->
                () -> mapPartOfVector(facts, lower, upper, isRelational(toDenotation(relSym)), resultArr, boxingInfo, counters, positions)
            );
            spawnFuncs(funcsToBeRun)
        };
        Array.toVector(resultArr)
    }

    def mapPartOfVector(
        factVec: Vector[Vector[Boxed]],
        lb: Int32,
        ub: Int32,
        isRelational: Bool,
        collectionArr: Array[(Vector[Int64], Boxed), r],
        boxingInfo: Boxing[r],
        counters: Vector[AtomicCounter[r]],
        unifiedPositions: Vector[UnifiedTypePos]
    ): Unit \ r = {
        def loop(i) =
            if(i >= ub) ()
            else {
                let fullTuple = Vector.get(i, factVec);
                let (tuple, boxed) =
                    if(isRelational) {
                        (fullTuple, Boxed.NoValue)
                    } else {
                        (Vector.dropRight(1, fullTuple), Vector.get(Vector.length(fullTuple) - 1, fullTuple))
                    };
                let savedVec = tuple |>
                    Vector.mapWithIndex(index -> boxedVal ->
                        let unifiedPos = Vector.get(index, unifiedPositions);
                        match boxedVal {
                            case BoxedObject(_, _) =>
                                let (_, boxToRepVec, symInfo, _) = boxingInfo;
                                setType(Types.Object, unifiedPos, symInfo);
                                let boxToRep = Vector.get(unifiedPos, boxToRepVec);
                                let counter = Vector.get(unifiedPos, counters);
                                BPlusTree.computeIfAbsent(() -> AtomicCounter.getAndIncrement(counter), boxedVal, boxToRep)
                            case _ => unboxWith(boxedVal, unifiedPos, boxingInfo)
                        }
                    );
                Array.put((savedVec, boxed), i, collectionArr);
                loop(i + 1)
            };
        loop(lb)
    }

    def initializeCounters(rc: Region[r], boxingInfo: Boxing[r]): Vector[AtomicCounter[r]] \ r = {
        let (boxedVecList, _, _, _) = boxingInfo;
        boxedVecList |>
            Vector.map(listOfBoxed ->  AtomicCounter.mkCounter(rc, Int32.toInt64(MutList.length(listOfBoxed))))
    }

    def initializeInternal(rc: Region[r], program: RamProgram, map: RamIdToPos): Boxing[r] \ r =
        let max = 1 + snd(Option.getWithDefault((RamId.Id(-1), -1), Map.maximumValue(map)));
        let intToBox = Vector.init(_ -> MutList.empty(rc), max);
        let boxToInt = Vector.init(_ -> BPlusTree.empty(rc), max);
        let locks = Vector.init(_ -> ReadWriteLock.mkLock(rc), max);
        let posToIndex = Array.init(rc, _ -> Types.Unknown, max);
        let info = (intToBox, boxToInt, posToIndex, locks);
        let relSyms = relSymsOfProgram(program);
        setType(Types.Int64, getOrCrash(Map.get(RamId.Id(-1), map)), posToIndex);
        // Add bot first to make sure it corresponds to 0.
        List.filter(match RelSym.Symbol(_, _, den) -> not isRelational(den), relSyms) |>
            List.forEach(x -> match x {
                case RelSym.Symbol(PredSym.PredSym(_, index), arity, Denotation.Latticenal(bot, _, _, _)) =>
                    unboxWith(bot, getOrCrash(Map.get(RamId.RelPos(index, arity - 1), map)), info); ()
                case _ => bug!("Should have been filtered out")
        });
        info

    def deMarshalObject(value: Int64, index: Int32, info: Boxing[r]): Boxed \ r = {
        let (objectList, _, _, locks) = info;
        let lock = Vector.get(index, locks);
        ReadWriteLock.readLock(lock);
        let res = getOrCrash(MutList.nth(getOrCrash(Int64.tryToInt32(value)), Vector.get(index, objectList)));
        ReadWriteLock.unlockRead(lock);
        res
    }

    def marshallObject(box: Boxed, index: Int32, info: Boxing[r]): Int64 \ r = {
        let (objectLists, vecObjectMap, _, locks) = info;
        let objectList = Vector.get(index, objectLists);
        let objectMap = Vector.get(index, vecObjectMap);
        let lock = Vector.get(index, locks);
        BPlusTree.computeIfAbsent(() -> {
            ReadWriteLock.writeLock(lock);
            let id = getNextIndex(objectList);
            MutList.insert(box, id, objectList);
            ReadWriteLock.unlockWrite(lock);
            Int32.toInt64(id)
        }, box, objectMap)
    }

    def getNextIndex(list: MutList[Boxed, r]): Int32 \ r = {
        MutList.size(list)
    }

    pub def unboxWith(box: Boxed, index: Int32, info: Boxing[r]): Int64 \ r =
        let (_, _, symInfo, _) = info;
        match box {
            case BoxedBool(x)       => setType(Types.Bool, index, symInfo); if (x) 1i64 else 0i64
            case BoxedChar(x)       => setType(Types.Char, index, symInfo); Int32.toInt64(Char.toBmpCodePoint(x))
            case BoxedInt8(x)       => setType(Types.Int8, index, symInfo); Int8.toInt64(x)
            case BoxedInt16(x)      => setType(Types.Int16, index, symInfo); Int16.toInt64(x)
            case BoxedInt32(x)      => setType(Types.Int32, index, symInfo); Int32.toInt64(x)
            case BoxedInt64(x)      => setType(Types.Int64, index, symInfo); x
            case BoxedFloat32(x)    => setType(Types.Float32, index, symInfo); Int32.toInt64(Float.floatToRawIntBits(Float32.valueOf(x).floatValue()))
            case BoxedFloat64(x)    => setType(Types.Float64, index, symInfo); Double.doubleToRawLongBits(Float64.valueOf(x).doubleValue())
            case BoxedObject(_, _)  => setType(Types.Object, index, symInfo); marshallObject(box, index, info) // We remap to low, so only goes wrong when dealing with more than 2^32 different RelSyms
            case Boxed.NoValue         => bug!("None should never be in a position to be unboxed unboxed")
        }

    pub def boxWith(v: Int64, index: Int32, info: Boxing[r]): Boxed \ r = 
        let (_, _, symInfo, _) = info;
        match getType(index, symInfo) {
            case Types.Bool      => Boxed.BoxedBool(not(v == 0i64))
            case Types.Char      => BoxedChar(unchecked_cast(Array.get(0, Character.toChars(getOrCrash(Int64.tryToInt32(v)))) as _ \ {}))
            case Types.Int8      => BoxedInt8(getOrCrash(Int64.tryToInt8(v)))
            case Types.Int16     => BoxedInt16(getOrCrash(Int64.tryToInt16(v)))
            case Types.Int32     => BoxedInt32(getOrCrash(Int64.tryToInt32(v)))
            case Types.Int64     => BoxedInt64(v)
            case Types.Float32   => BoxedFloat32(Float.intBitsToFloat(getOrCrash(Int64.tryToInt32(v))))
            case Types.Float64   => BoxedFloat64(Double.longBitsToDouble(v))
            case Types.Object    => deMarshalObject(v, index, info)
            case Types.Unknown   => bug!("Unormalizing value, which has never been normalized")
        }


    // Compute equality for the terms, deciding what can safely be stored together. Might miss some, but only a problem for objects.
    // Equality is on the full symbols.
    mod Equality {
        use Fixpoint.Ast.Ram.getTermRamId
        use Fixpoint.Ast.Ram
        use Fixpoint.Ast.Ram.{RamId, Predicates, RamStmt, RelOp, RamTerm, BoolExp, RamProgram, RowVar}
        use Fixpoint.Ast.Ram.{RelSym, RamProgram}
        use Fixpoint.Ast.Shared.PredSym
        use Fixpoint.BoxingType.RamIdToPos
        use Fixpoint.Counter
        use Fixpoint.Util.getOrCrash
        use Fixpoint.Predicate.{PredType, idToFullPredId, fullIdtoPredType, relSymsOfProgram}

        pub def computeMapping(d: RamProgram): RamIdToPos = region rc {
            let disjointSet = MutDisjointSets.empty(rc);
            let RamProgram.Program(s, _, predTrack, _) = d;
            MutDisjointSets.makeSet(RamId.Id(-1), disjointSet);
            unifyRamIds(d, disjointSet);
            let relSyms = relSymsOfProgram(d);
            let mutMap = MutMap.empty(rc);
            let counter = Counter.fresh(rc);
            List.forEach(match RelSym.Symbol(PredSym.PredSym(_, id), arity, _) -> {
                Vector.forEach(i -> {
                    registerRamId(RamId.RelPos(id, i), disjointSet, mutMap, counter)
                }, Vector.range(0, arity + 2)) // + 2 to ensure safety of provenance annotations.
            }, relSyms);
            computeMappingStmt(s, predTrack, disjointSet, mutMap, counter);
            registerRamId(RamId.Id(-1), disjointSet, mutMap, counter);
            MutMap.toMap(mutMap)
        }

        def unifyRamIds(d: RamProgram, set: MutDisjointSets[RamId, r]): Unit \ r = match d {
            case RamProgram.Program(stmt, _, predTrack, _) =>
                let relSyms = relSymsOfProgram(d);
                List.forEach(match RelSym.Symbol(PredSym.PredSym(_, id), arity, _) -> {
                    unifyPredTypes(id, arity, predTrack, set)
                }, relSyms);
                unifyRamIdsStmt(stmt, predTrack, set)
        }

        def unifyRamIdsStmt(s: RamStmt, predTrack: Predicates, set: MutDisjointSets[RamId, r]): Unit \ r = match s {
            case RamStmt.Insert(rest) => unifyRamIdsOp(rest, predTrack, set)
            case RamStmt.MergeInto(rel1, rel2) => unifyPredicates(rel1, rel2, set)
            case RamStmt.Swap(rel1, rel2) => unifyPredicates(rel1, rel2, set)
            case RamStmt.Purge(_) => ()
            case RamStmt.Seq(stmts) => Vector.forEach(x -> unifyRamIdsStmt(x, predTrack, set), stmts)
            case RamStmt.Par(stmts) => Vector.forEach(x -> unifyRamIdsStmt(x, predTrack, set), stmts)
            case RamStmt.Until(bools, stmt) => unifyRamIdsStmt(stmt, predTrack, set); Vector.forEach(x -> unifyRamIdsBool(x, predTrack, set), bools)
            case RamStmt.Comment(_) => ()
            case RamStmt.EstimateJoinSize(_, _, _, _) => ()
        }

        def unifyRamIdsOp(s: RelOp, predTrack: Predicates, set: MutDisjointSets[RamId, r]): Unit \ r = match s {
            case RelOp.Search(rv, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), rest) =>
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.TuplePos(rv, i), set), Vector.range(0, arity + 2));
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.RelPos(predSym, i), set), Vector.range(0, arity + 2));
                Vector.forEach(i -> MutDisjointSets.union(RamId.TuplePos(rv, i), RamId.RelPos(predSym, i), set), Vector.range(0, arity));
                unifyPredTypes(predSym, arity, predTrack, set);
                unifyRamIdsOp(rest, predTrack, set)
            case RelOp.Query(rv, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), bools, _, rest) =>
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.TuplePos(rv, i), set), Vector.range(0, arity + 2));
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.RelPos(predSym, i), set), Vector.range(0, arity + 2));
                Vector.forEach(i -> MutDisjointSets.union(RamId.TuplePos(rv, i), RamId.RelPos(predSym, i), set), Vector.range(0, arity + 2));
                unifyPredTypes(predSym, arity, predTrack, set);
                Vector.forEach(x -> unifyRamIdsBool(x, predTrack, set), bools);
                unifyRamIdsOp(rest, predTrack, set)
            case RelOp.Functional(RowVar.Named(id), _, inputTerms, rest, arity) =>
                Vector.forEachWithIndex(i -> curTerm -> {
                    let termID = Ram.getTermRamId(curTerm);
                    MutDisjointSets.makeSet(RamId.InId(id, i), set);
                    MutDisjointSets.makeSet(termID, set);
                    MutDisjointSets.union(RamId.InId(id, i), termID, set);
                    unifyRamIdsTerm(curTerm, predTrack, set)
                }, inputTerms);
                Vector.range(0, arity) |>
                Vector.forEach(i -> 
                    MutDisjointSets.makeSet(RamId.TuplePos(RowVar.Named(id), i), set)
                );
                unifyRamIdsOp(rest, predTrack, set)
            case RelOp.Project(terms, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), _) =>
                unifyPredTypes(predSym, arity, predTrack, set);
                terms |> 
                Vector.forEachWithIndex(i -> term -> {
                    unifyRamIdsTerm(term, predTrack, set);
                    let termID = Ram.getTermRamId(term);
                    MutDisjointSets.makeSet(RamId.RelPos(predSym, i), set);
                    MutDisjointSets.makeSet(termID, set);
                    MutDisjointSets.union(RamId.RelPos(predSym, i), termID, set)
                })
            case RelOp.If(bools, rest) =>
                Vector.forEach(x -> unifyRamIdsBool(x, predTrack, set), bools);
                unifyRamIdsOp(rest, predTrack, set)
        }

        def unifyRamIdsBool(s: BoolExp, predTrack: Predicates, set: MutDisjointSets[RamId, r]): Unit \ r = match s {
            case BoolExp.Not(boolExp) => unifyRamIdsBool(boolExp, predTrack, set)
            case BoolExp.IsEmpty(_) => ()
            case BoolExp.NotMemberOf(terms, RelSym.Symbol(PredSym.PredSym(_, id), _, _)) =>
                Vector.forEach(term -> unifyRamIdsTerm(term, predTrack, set), terms);
                Vector.forEachWithIndex(i -> term -> {
                    MutDisjointSets.makeSet(Ram.getTermRamId(term), set);
                    MutDisjointSets.makeSet(RamId.RelPos(id, i), set);
                    MutDisjointSets.union(Ram.getTermRamId(term), RamId.RelPos(id, i), set)
                }, terms)
            case BoolExp.NotBot(term, _, _) => unifyRamIdsTerm(term, predTrack, set)
            case BoolExp.Leq(_, _, _) => ()
            case BoolExp.Eq(term1, term2) =>
                unifyRamIdsTerm(term1, predTrack, set);
                unifyRamIdsTerm(term2, predTrack, set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term2), set);
                MutDisjointSets.union(Ram.getTermRamId(term1), Ram.getTermRamId(term2), set)
            case BoolExp.Guard1(_, term1) =>
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                unifyRamIdsTerm(term1, predTrack, set)
            case BoolExp.Guard2(_, term1, term2) =>
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term2), set);
                unifyRamIdsTerm(term1, predTrack, set);
                unifyRamIdsTerm(term2, predTrack, set)
            case BoolExp.Guard3(_, term1, term2, term3) =>
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term2), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term3), set);
                unifyRamIdsTerm(term1, predTrack, set);
                unifyRamIdsTerm(term2, predTrack, set);
                unifyRamIdsTerm(term3, predTrack, set)
            case BoolExp.Guard4(_, term1, term2, term3, term4) =>
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term2), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term3), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term4), set);
                unifyRamIdsTerm(term1, predTrack, set);
                unifyRamIdsTerm(term2, predTrack, set);
                unifyRamIdsTerm(term3, predTrack, set);
                unifyRamIdsTerm(term4, predTrack, set)
            case BoolExp.Guard5(_, term1, term2, term3, term4, term5) =>
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term2), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term3), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term5), set);
                unifyRamIdsTerm(term1, predTrack, set);
                unifyRamIdsTerm(term2, predTrack, set);
                unifyRamIdsTerm(term3, predTrack, set);
                unifyRamIdsTerm(term4, predTrack, set);
                unifyRamIdsTerm(term5, predTrack, set)
        }

        def unifyPredicates(relSym1: RelSym, relSym2: RelSym, set: MutDisjointSets[RamId, r]): Unit \ r =
            let arity = Ram.arityOf(relSym1);
            let id1 = Ram.toId(relSym1);
            let id2 = Ram.toId(relSym2);
            Vector.forEach(i -> {
                MutDisjointSets.makeSet(RamId.RelPos(id1, i), set);
                MutDisjointSets.makeSet(RamId.RelPos(id2, i), set);
                MutDisjointSets.union(RamId.RelPos(id1, i), RamId.RelPos(id2, i), set)
            }, Vector.range(0, arity))

        def unifyPredTypes(predSym: Int64, arity: Int32, predTrack: Predicates, set: MutDisjointSets[RamId, r]): Unit \ r =
            let fullSymbol = idToFullPredId(predSym, predTrack);
            let deltaSymbol = fullIdtoPredType(fullSymbol, PredType.Delta, predTrack);
            let newSymbol = fullIdtoPredType(fullSymbol, PredType.New, predTrack);
            // The `+ 2` is to ensure safety with provenance annotations.
            Vector.forEach(i -> {
                MutDisjointSets.makeSet(RamId.RelPos(fullSymbol, i), set);
                MutDisjointSets.makeSet(RamId.RelPos(deltaSymbol, i), set);
                MutDisjointSets.union(RamId.RelPos(fullSymbol, i), RamId.RelPos(deltaSymbol, i), set)
            }, Vector.range(0, arity + 2));
            Vector.forEach(i -> {
                MutDisjointSets.makeSet(RamId.RelPos(newSymbol, i), set);
                MutDisjointSets.union(RamId.RelPos(fullSymbol, i), RamId.RelPos(newSymbol, i), set)
            }, Vector.range(0, arity + 2));
            MutDisjointSets.union(RamId.RelPos(fullSymbol, arity), RamId.Id(-1), set);
            MutDisjointSets.union(RamId.RelPos(fullSymbol, arity + 1), RamId.Id(-1), set);
            ()

        def unifyAppTerms(terms: Vector[RamTerm], id: Int32, predTrack: Predicates, set: MutDisjointSets[RamId, r]): Unit \ r = 
            Vector.forEachWithIndex(i -> t -> {
                unifyRamIdsTerm(t, predTrack, set);
                let id1 = Ram.getTermRamId(t);
                MutDisjointSets.makeSet(id1, set);
                MutDisjointSets.makeSet(RamId.InId(id, i), set);
                MutDisjointSets.union(id1, RamId.InId(id, i), set)
            }, terms)

        def unifyRamIdsTerm(s: RamTerm, predTrack: Predicates, set: MutDisjointSets[RamId, r]): Unit \ r = match s {
            case RamTerm.Lit(_, id) =>
                MutDisjointSets.makeSet(id, set)
            case RamTerm.RowLoad(_, _, _) =>
                MutDisjointSets.makeSet(Ram.getTermRamId(s), set)
            case RamTerm.ProvMax(vec) =>
            let id = Ram.getTermRamId(s);
            vec |>
                Vector.forEach(match (rv, index) -> {
                    MutDisjointSets.makeSet(RamId.TuplePos(rv, index), set);
                    MutDisjointSets.union(RamId.TuplePos(rv, index), id, set)
                })
            case RamTerm.Meet(_, t1, (rv, relSym), id) => 
                unifyRamIdsTerm(t1, predTrack, set);
                let id1 = Ram.getTermRamId(t1);
                let id2 = Ram.getLatVarRamId(rv, relSym);
                MutDisjointSets.makeSet(id1, set);
                MutDisjointSets.makeSet(id2, set);
                MutDisjointSets.makeSet(id, set);
                MutDisjointSets.union(id1, id, set);
                MutDisjointSets.union(id1, id2, set)
            case RamTerm.App1(_, t1, RamId.Id(id)) =>
                unifyAppTerms(Vector#{t1}, id, predTrack, set)
            case RamTerm.App2(_, t1, t2, RamId.Id(id)) =>
                unifyAppTerms(Vector#{t1, t2}, id, predTrack, set)
            case RamTerm.App3(_, t1, t2, t3, RamId.Id(id)) =>
                unifyAppTerms(Vector#{t1, t2, t3}, id, predTrack, set)
            case RamTerm.App4(_, t1, t2, t3, t4, RamId.Id(id)) =>
                unifyAppTerms(Vector#{t1, t2, t3, t4}, id, predTrack, set)
            case RamTerm.App5(_, t1, t2, t3, t4, t5, RamId.Id(id)) =>
                unifyAppTerms(Vector#{t1, t2, t3, t4, t4, t5}, id, predTrack, set)
            case _ => unreachable!()
        }

        def computeMappingStmt(s: RamStmt, predTrack: Predicates, set: MutDisjointSets[RamId, r], map: MutMap[RamId, Int32, r], counter: Counter[r]): Unit \ r = match s {
            case RamStmt.Insert(rest) => computeMappingOp(rest, predTrack, set, map, counter)
            case RamStmt.MergeInto(rel1, rel2) =>
                insertIndexRelSym(rel1, set, map, counter);
                insertIndexRelSym(rel2, set, map, counter)
            case RamStmt.Swap(rel1, rel2) =>
                insertIndexRelSym(rel1, set, map, counter);
                insertIndexRelSym(rel2, set, map, counter)
            case RamStmt.Purge(_) => ()
            case RamStmt.Seq(stmts) => Vector.forEach(x -> computeMappingStmt(x, predTrack, set, map, counter), stmts)
            case RamStmt.Par(stmts) => Vector.forEach(x -> computeMappingStmt(x, predTrack, set, map, counter), stmts)
            case RamStmt.Until(bools, stmt) => 
                computeMappingStmt(stmt, predTrack, set, map, counter); 
                Vector.forEach(x -> computeMappingBool(x, predTrack, set, map, counter), bools)
            case RamStmt.Comment(_) => ()
            case RamStmt.EstimateJoinSize(_, _, _, _) => ()
        }

        def computeMappingOp(s: RelOp, predTrack: Predicates, set: MutDisjointSets[RamId, r], map: MutMap[RamId, Int32, r], counter: Counter[r]): Unit \ r = 
            let recurse = x -> computeMappingOp(x, predTrack, set, map, counter);
            let insert = x -> registerRamId(x, set, map, counter);
            match s {
                case RelOp.Search(rv, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), rest) =>
                    Vector.forEach(i -> insert(RamId.TuplePos(rv, i)), Vector.range(0, arity + 2));
                    Vector.forEach(i -> insert(RamId.RelPos(predSym, i)), Vector.range(0, arity + 2));
                    recurse(rest)
                case RelOp.Query(rv, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), bools, _, rest) =>
                    Vector.forEach(i -> insert(RamId.TuplePos(rv, i)), Vector.range(0, arity + 2));
                    Vector.forEach(i -> insert(RamId.RelPos(predSym, i)), Vector.range(0, arity + 2));
                    Vector.forEach(x -> computeMappingBool(x, predTrack, set, map, counter), bools);
                    recurse(rest)
                case RelOp.Functional(RowVar.Named(id), _, inputTerms, rest, arity) => // equality on the input should be handled elsewhere.
                    Vector.forEach(i -> insert(RamId.TuplePos(RowVar.Named(id), i)), Vector.range(0, arity));
                    Vector.forEach(i -> insert(RamId.InId(id, i)), Vector.range(0, Vector.length(inputTerms)));
                    Vector.forEach(x -> computeMappingTerm(x, predTrack, set, map, counter), inputTerms);
                    recurse(rest)
                case RelOp.Project(terms, RelSym.Symbol(PredSym.PredSym(_, predSym), _, _), _) =>
                    terms |> Vector.forEachWithIndex(i -> _ -> insert(RamId.RelPos(predSym, i)));
                    terms |>
                    Vector.forEach(term -> computeMappingTerm(term, predTrack, set, map, counter))
                case RelOp.If(bools, rest) =>
                    recurse(rest);
                    Vector.forEach(x -> computeMappingBool(x, predTrack, set, map, counter), bools)
            }

        def computeMappingTermApp(
            computeMappingTermRec: RamTerm -> Unit \ r,
            registerRamIdRec: RamId -> Unit \ r,
            id: RamId,
            terms: Vector[RamTerm]
        ): Unit \ r =
            registerRamIdRec(id);
            let id1 = match id {
                case RamId.Id(i) => i
                case _ => unreachable!()
            };
            terms |> Vector.forEachWithIndex(i -> t -> {
                computeMappingTermRec(t);
                registerRamIdRec(RamId.InId(id1, i))
            })

        def computeMappingTerm(
            s: RamTerm, 
            predicates: Predicates, 
            set: MutDisjointSets[RamId, r], 
            map: MutMap[RamId, Int32, r], 
            counter: Counter[r]
        ): Unit \ r = 
            let registerRamIdRec = x -> registerRamId(x, set, map, counter);
            let computeMappingTermRec = x -> computeMappingTerm(x, predicates, set, map, counter);
            let computeMappingTermAppRec = computeMappingTermApp(computeMappingTermRec, registerRamIdRec, getTermRamId(s));
            match s {
                case RamTerm.Lit(_, id) => registerRamIdRec(id)
                case RamTerm.RowLoad(_, _, _) => registerRamIdRec(getTermRamId(s))
                case RamTerm.Meet(_, t1, (rv, relSym), RamId.Id(id)) =>
                    computeMappingTermRec(t1);
                    registerRamIdRec(Ram.getLatVarRamId(rv, relSym));
                    registerRamIdRec(RamId.Id(id))
                case RamTerm.App1(_, t1, _) =>
                    Vector#{t1} |> computeMappingTermAppRec
                case RamTerm.App2(_, t1, t2, _) =>
                    Vector#{t1, t2} |> computeMappingTermAppRec
                case RamTerm.App3(_, t1, t2, t3, _) =>
                    Vector#{t1, t2, t3} |> computeMappingTermAppRec
                case RamTerm.App4(_, t1, t2, t3, t4, _) =>
                    Vector#{t1, t2, t3, t4} |> computeMappingTermAppRec
                case RamTerm.App5(_, t1, t2, t3, t4, t5, _) =>
                    Vector#{t1, t2, t3, t4, t5} |> computeMappingTermAppRec
                case RamTerm.ProvMax(loads) =>
                    loads |> Vector.forEach(match (rv, index) -> registerRamIdRec(RamId.TuplePos(rv, index)))
                case RamTerm.Meet(_, _, _, _) => unreachable!()
            }

        def computeMappingBool(
            s: BoolExp, 
            predicates: Predicates, 
            set: MutDisjointSets[RamId, r], 
            map: MutMap[RamId, Int32, r], 
            counter: Counter[r]
        ): Unit \ r = 
            let insert = x -> registerRamId(x, set, map, counter);
            let computeMappingTermRec = x -> computeMappingTerm(x, predicates, set, map, counter);
            match s {
                case BoolExp.Not(boolExp) => computeMappingBool(boolExp, predicates, set, map, counter)
                case BoolExp.IsEmpty(_) => ()
                case BoolExp.NotMemberOf(terms, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _)) =>
                    Vector.forEach(x -> computeMappingTermRec(x), terms);
                    Vector.forEach(i -> insert(RamId.RelPos(predSym, i)), Vector.range(0, arity))
                case BoolExp.Eq(t1, t2) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2)
                case BoolExp.NotBot(t1, _, _) =>
                    computeMappingTermRec(t1)
                case BoolExp.Leq(_, _, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _)) =>
                    insert(RamId.RelPos(predSym, arity - 1))
                case BoolExp.Guard1(_, t1) =>
                    computeMappingTermRec(t1)
                case BoolExp.Guard2(_, t1, t2) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2)
                case BoolExp.Guard3(_, t1, t2, t3) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2);
                    computeMappingTermRec(t3)
                case BoolExp.Guard4(_, t1, t2, t3, t4) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2);
                    computeMappingTermRec(t3);
                    computeMappingTermRec(t4)
                case BoolExp.Guard5(_, t1, t2, t3, t4, t5) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2);
                    computeMappingTermRec(t3);
                    computeMappingTermRec(t4);
                    computeMappingTermRec(t5)
            }

        def insertIndexRelSym(
            relSym: RelSym, 
            disjoint: MutDisjointSets[RamId, r], 
            map: MutMap[RamId, Int32, r], 
            counter: Counter[r]
        ): Unit \ r =
            let arity = Ram.arityOf(relSym);
            let id = Ram.toId(relSym);
            Vector.forEach(i -> {
                registerRamId(RamId.RelPos(id, i), disjoint, map, counter)
                // + 2 to ensure safety with provenance annotations
            }, Vector.range(0, arity + 2))


        def registerRamId(
            id: RamId, 
            disjoint: MutDisjointSets[RamId, r], 
            map: MutMap[RamId, Int32, r], 
            counter: Counter[r]
        ): Unit \ r = 
            let repID = getOrCrash(MutDisjointSets.find(id, disjoint)); 
            match MutMap.get(repID, map) {
                case Some(v) => MutMap.put(id, v, map)
                case None => 
                    let newID = Counter.getAndIncrement(counter);
                    MutMap.put(id, newID, map);
                    MutMap.put(repID, newID, map)
            }
    }

}
