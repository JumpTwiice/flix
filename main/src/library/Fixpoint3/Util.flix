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

mod Fixpoint3.Util {
    use Fixpoint3.Ast.Ram.{RamProgram, RamTerm, RowVar, RelSym, RamStmt, RelOp, RamId, BoolExp}
    use Fixpoint3.Boxed

    ///
    /// Unwraps an option.
    ///
    /// Causes runtime hole error when `x` is `None`.
    ///
    @Internal
    pub def getOrCrash(x: Option[a]): a = match x {
        case Some(v) => v
        case None => bug!("Attempted unwrapping none in getOrCrash")
    }

    ///
    /// Collects equality information in `stmt` and save it in `equalitySets` and `constEqualities`.
    /// Equalities between 2 `RowLoad`s are added to `equalitySets` and equalities between `RowLoad`
    /// and `Lit` are added to `constEqualities`.
    ///
    /// In `equalitySets` we unify `(rv1, i1)` with `(rv2, i2)` if they occur together
    /// in an equaltiy statement.
    ///
    /// In `constEqualities` we save a list of which literals a `(rv, i)` were equal to.
    ///
    @Internal
    pub def unifyEqualitiesStmt(
        equalitySets: MutDisjointSets[(RowVar, Int32), r],
        constEqualities: MutMap[(RowVar, Int32), List[(Boxed, RamId)], r],
        stmt: RamStmt
    ): Unit \ r = match stmt {
        case RamStmt.Seq(xs) => Vector.forEach(unifyEqualitiesStmt(equalitySets, constEqualities), xs)
        case RamStmt.Insert(op) => unifyEqualitiesOp(equalitySets, constEqualities, op)
        case RamStmt.Par(xs) => Vector.forEach(unifyEqualitiesStmt(equalitySets, constEqualities), xs)
        case RamStmt.Until(boolExps, body) =>
            Vector.forEach(boolExp -> unifyBoolExp(equalitySets, constEqualities, boolExp), boolExps);
            unifyEqualitiesStmt(equalitySets, constEqualities, body)
        case RamStmt.MergeInto(_, _) => ()
        case RamStmt.Swap(_, _) => ()
        case RamStmt.Purge(_) => ()
        case RamStmt.Comment(_) => ()
        case RamStmt.EstimateJoinSize(_, _, _, _) => ()
    }

    ///
    /// Collects equality information in `op` and save it in `equalitySets` and `constEqualities`.
    /// Equalities between 2 `RowLoad`s are added to `equalitySets` and equalities between `RowLoad`
    /// and `Lit` are added to `constEqualities`.
    ///
    /// In `equalitySets` we unify `(rv1, i1)` with `(rv2, i2)` if they occur together
    /// in an equaltiy statement.
    ///
    /// In `constEqualities` we save a list of which literals a `(rv, i)` were equal to.
    ///
    @Internal
    pub def unifyEqualitiesOp(
        equalitySets: MutDisjointSets[(RowVar, Int32), r],
        constEqualities: MutMap[(RowVar, Int32), List[(Boxed, RamId)], r],
        op: RelOp
    ): Unit \ r = match op {
        case RelOp.Search(rowVar, RelSym.Symbol(_, arity, _), body) =>
            collectLoads(rowVar, arity, equalitySets);
            unifyEqualitiesOp(equalitySets, constEqualities, body)
        case RelOp.Query(_, _, _, _, _) =>
            bug!("In Fixpoint.Phase.Hoisting.unifyEqualitiesOp: Query should not exist at this point!")
        case RelOp.Functional(rowVar, _, _, body, arity) =>
            collectLoads(rowVar, arity, equalitySets);
            unifyEqualitiesOp(equalitySets, constEqualities, body)
        case RelOp.Project(_, _) => ()
        case RelOp.If(boolExps, body) =>
            Vector.forEach(unifyBoolExp(equalitySets, constEqualities), boolExps);
            unifyEqualitiesOp(equalitySets, constEqualities, body)
    }

    ///
    /// Collects equality information in `boolExp` and save it in `equalitySets` and `constEqualities`.
    ///
    /// See `unifyEqualitiesOp`.
    ///
    def unifyBoolExp(
        equalitySets: MutDisjointSets[(RowVar, Int32), r],
        constEqualities: MutMap[(RowVar, Int32), List[(Boxed, RamId)], r],
        boolExp: BoolExp
    ): Unit \ r = match boolExp {
        case BoolExp.Eq(RamTerm.RowLoad(rv1, i1, _), RamTerm.RowLoad(rv2, i2, _)) =>
            MutDisjointSets.makeSet((rv1, i1), equalitySets);
            MutDisjointSets.makeSet((rv2, i2), equalitySets);
            MutDisjointSets.union((rv1, i1), (rv2, i2), equalitySets)
        case BoolExp.Eq(RamTerm.RowLoad(rv, i, _), RamTerm.Lit(val, id)) =>
            MutMap.putWith(_ -> list -> (val, id) :: list, (rv, i), (val, id) :: Nil, constEqualities)
        case BoolExp.Eq(RamTerm.Lit(val, id), RamTerm.RowLoad(rv, i, _)) =>
            MutMap.putWith(_ -> list -> (val, id) :: list, (rv, i), (val, id) :: Nil, constEqualities)
        case _ => ()
    }

    ///
    /// Add `(rowVar, i)` for all `i` between `0` (inclusive) and `arity` (exlusive)
    /// to `equalitySets`.
    ///
    def collectLoads(rowVar: RowVar, arity: Int32, equalitySets: MutDisjointSets[(RowVar, Int32), r]): Unit \ r =
        Vector.forEach(i -> MutDisjointSets.makeSet((rowVar, i), equalitySets), Vector.range(0, arity))

}
