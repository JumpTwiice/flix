/*
 * Copyright 2021 Benjamin Dahse
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

mod Fixpoint.Ast.Ram {

    use Fixpoint.Ast.Shared.Denotation
    use Fixpoint.Ast.Shared.PredSym
    use Fixpoint.PredSymsOf
    use Fixpoint.SubstitutePredSym

    /////////////////////////////////////////////////////////////////////////////
    // RamStmt                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    // TODO: Add 'exit' at some point, when stuff starts to work.

    @Internal
    pub enum RamStmt[v] {
        case Insert(RelOp[v])
        case Merge(RamSym[v], RamSym[v])
        case Swap(RamSym[v], RamSym[v])
        case Purge(RamSym[v])
        case Seq(Vector[RamStmt[v]])
        case Par(Vector[RamStmt[v]])
        case While(Vector[BoolExp[v]], RamStmt[v])
        case Comment(String)
    }

    instance ToString[RamStmt[v]] {
        pub def toString(stmt: RamStmt[v]): String =
            let nl = String.lineSeparator();
            match stmt {
                case RamStmt.Insert(op) => ToString.toString(op)
                case RamStmt.Merge(src, dst) => "merge ${src} into ${dst}"
                case RamStmt.Swap(lhs, rhs) => "Swap ${lhs} and ${rhs}"
                case RamStmt.Purge(ramSym) => "purge ${ramSym}"
                case RamStmt.Seq(xs) => Vector.join(";${nl}", xs)
                case RamStmt.While(test, body) =>
                    let tst = test |> Vector.join(" Λ ");
                    "until(${tst}) do${nl}${String.indent(4, "${body}")}end"
                case RamStmt.Comment(comment) => "// ${comment}"
            }
    }

    /////////////////////////////////////////////////////////////////////////////
    // RelOp                                                                   //
    /////////////////////////////////////////////////////////////////////////////
    
    @Internal
    pub enum RelOp[v] {
        case Search(TupleVar, RamSym[v], RelOp[v])
        // TODO: Add extra field describing which index to use. Could use a simple int32.
        case SearchWithIndex(TupleVar, RamSym[v], Vector[QueryExp], RelOp[v])
        case Functional(TupleVar, Vector[v] -> Vector[Vector[v]], Vector[RamTerm[v]], RelOp[v])
        case Project(Vector[RamTerm[v]], RamSym[v])
        case If(Vector[BoolExp[v]], RelOp[v])
    }

    instance ToString[RelOp[v]] {
        pub def toString(op: RelOp[v]): String =
            let nl = String.lineSeparator();
            match op {
                case RelOp.Search(var, ramSym, body) =>
                    "search ${var} ∈ ${ramSym} do${nl}${String.indent(4, "${body}")}end"
                case RelOp.SearchWithIndex(var, ramSym, prefixQuery, body) =>
                    let qry = Vector.joinWith(match (i, term) -> {
                        ToString.toString(BoolExp.Eq(RamTerm.RowLoad(var, i), term))
                    }, " ∧ ", prefixQuery);
                    "SearchWithIndex {${var} ∈ ${ramSym} | ${qry}} do${nl}${String.indent(4, "${body}")}end"
                case RelOp.Functional(TupleVar, _, terms, body) =>
                    "loop(${TupleVar} <- f(${terms |> Vector.join(", ")})) do${nl}${String.indent(4, "${body}")}end"
                case RelOp.Project(terms, ramSym) =>
                    "project (${terms |> Vector.join(", ")}) into ${ramSym}"
                case RelOp.If(test, then) =>
                    let tst = test |> Vector.join(" ∧ ");
                    "if(${tst}) then${nl}${String.indent(4, "${then}")}end"
            }
    }

    /////////////////////////////////////////////////////////////////////////////
    // QueryExp                                                                //
    /////////////////////////////////////////////////////////////////////////////

    // TODO: Possibly add support for more searches.

    @Internal
    pub enum QueryExp[v] {
        case Eq(RamTerm[v], RamTerm[v])
        case Neq(RamTerm[v], RamTerm[v])
        // case MemberOf(Vector[RamTerm[v]], RamSym[v])
    }

    instance ToString[QueryExp[v]] {
        pub def toString(exp: QueryExp[v]): String =
            match exp {
                case Eq(i1, i2) => "${i1} = ${i2}"
                case Neq(i1, i2) => "${i1} ≠ ${i2}"
            }
    }


    /////////////////////////////////////////////////////////////////////////////
    // BoolExp                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    /**
    TODO: Maybe add not equal? Could allow more optimal searching of structures
    */

    @Internal
    pub enum BoolExp[v] {
        case IsEmpty(RamSym[v])
        case NotMemberOf(Vector[RamTerm[v]], RamSym[v])
        case Eq(RamTerm[v], RamTerm[v])
        case Leq(v -> v -> Bool, RamTerm[v], RamTerm[v])
        case Guard0(Unit -> Bool)
        case Guard1(v -> Bool, RamTerm[v])
        case Guard2(v -> v -> Bool, RamTerm[v], RamTerm[v])
        case Guard3(v -> v -> v -> Bool, RamTerm[v], RamTerm[v], RamTerm[v])
        case Guard4(v -> v -> v -> v -> Bool, RamTerm[v], RamTerm[v], RamTerm[v], RamTerm[v])
        case Guard5(v -> v -> v -> v -> v -> Bool, RamTerm[v], RamTerm[v], RamTerm[v], RamTerm[v], RamTerm[v])
    }

    instance ToString[BoolExp[v]] {
        pub def toString(exp: BoolExp[v]): String =
            match exp {
                case BoolExp.IsEmpty(ramSym) => "${ramSym} == ∅"
                case BoolExp.NotMemberOf(terms, ramSym) => "(${terms |> Vector.join(", ")}) ∉ ${ramSym}"
                case BoolExp.Eq(lhs, rhs) => "${lhs} == ${rhs}"
                case BoolExp.Leq(_, lhs, rhs) => "${lhs} ≤ ${rhs}"
                case BoolExp.Guard0(_) => "<clo>()"
                case BoolExp.Guard1(_, v) => "<clo>(${v})"
                case BoolExp.Guard2(_, v1, v2) => "<clo>(${v1}, ${v2})"
                case BoolExp.Guard3(_, v1, v2, v3) => "<clo>(${v1}, ${v2}, ${v3})"
                case BoolExp.Guard4(_, v1, v2, v3, v4) => "<clo>(${v1}, ${v2}, ${v3}, ${v4})"
                case BoolExp.Guard5(_, v1, v2, v3, v4, v5) => "<clo>(${v1}, ${v2}, ${v3}, ${v4}, ${v5})"
            }
    }

    /////////////////////////////////////////////////////////////////////////////
    // RamTerm                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    ///
    /// Represents a RAM term.
    ///
    /// `RowLoad(x, i)` represents an index into the tuple
    /// bound to the local variable `x`, i.e. `x[i]`.
    ///
    /// `LoadLatVar(x)` represents the lattice component in the tuple
    /// bound to the local variable `x`.
    ///
    @Internal
    pub enum RamTerm[v] {
        case Lit(v)
        case RowLoad(TupleVar, Int32)
        case LoadLatVar(TupleVar)
        case Meet(v -> v -> v, RamTerm[v], RamTerm[v])
        case App0(Unit -> v)
        case App1(v -> v, RamTerm[v])
        case App2(v -> v -> v, RamTerm[v], RamTerm[v])
        case App3(v -> v -> v -> v, RamTerm[v], RamTerm[v], RamTerm[v])
        case App4(v -> v -> v -> v -> v, RamTerm[v], RamTerm[v], RamTerm[v], RamTerm[v])
        case App5(v -> v -> v -> v -> v -> v, RamTerm[v], RamTerm[v], RamTerm[v], RamTerm[v], RamTerm[v])
    }

    instance ToString[RamTerm[v]] {
        pub def toString(term: RamTerm[v]): String = match term {
            case RamTerm.Lit(v) => "%{v}"
            case RamTerm.RowLoad(var, index) => "${var}[${index}]"
            case RamTerm.LoadLatVar(var) => "${var}[-1]"
            case RamTerm.Meet(_, lhs, rhs) => "(${lhs} ⊓ ${rhs})"
            case RamTerm.App0(_) => "<clo>()"
            case RamTerm.App1(_, v) => "<clo>(${v})"
            case RamTerm.App2(_, v1, v2) => "<clo>(${v1}, ${v2})"
            case RamTerm.App3(_, v1, v2, v3) => "<clo>(${v1}, ${v2}, ${v3})"
            case RamTerm.App4(_, v1, v2, v3, v4) => "<clo>(${v1}, ${v2}, ${v3}, ${v4})"
            case RamTerm.App5(_, v1, v2, v3, v4, v5) => "<clo>(${v1}, ${v2}, ${v3}, ${v4}, ${v5})"
        }
    }

    /////////////////////////////////////////////////////////////////////////////
    // RamSym                                                                  //
    /////////////////////////////////////////////////////////////////////////////

    /**
        Represents the relations (also delta relations) of the program.
            The first is the symbol of the relation
            The second parameter is the arity
            The third depends denotes whether we are dealing with a lattice or a 'normal' relation.
    */

    @Internal
    pub enum RamSym[v] {
        case Symbol(PredSym, Int32, Denotation[v])
    }

    // TODO: Implement equality for PredSym using only int id.
    instance Eq[RamSym[v]] {
        pub def eq(a: RamSym[v], b: RamSym[v]): Bool = match (a, b) {
            case (RamSym.Symbol(s1, _, _),  RamSym.Symbol(s2, _, _))  => s1 == s2
        }
    }

    // TODO: Implement order for PredSym using only int id.
    instance Order[RamSym[v]] {
        pub def compare(a: RamSym[v], b: RamSym[v]): Comparison = match (a, b) {
            case (RamSym.Symbol(s1, _, _), RamSym.Symbol(s2, _, _)) =>  s1 <=> s2
        }
    }

    instance PredSymsOf[RamSym[v]] {
        pub def predSymsOf(x: RamSym[v]): Set[PredSym] = match x {
            case RamSym.Symbol(predSym, _, _)    => Set.singleton(predSym)
        }
    }

    instance SubstitutePredSym[RamSym[v]] {
        pub def substitute(x: RamSym[v], s: Map[PredSym, PredSym]): RamSym[v] = match x {
            case RamSym.Symbol(predSym, arity, den)  =>
                let newSym = Map.getWithDefault(predSym, predSym, s);
                RamSym.Symbol(newSym, arity, den)
        }
    }

    instance ToString[RamSym[v]] {
        pub def toString(ramSym: RamSym[v]): String = match ramSym {
            case RamSym.Symbol(sym, _, _)    => "${sym}"
        }
    }

    @Internal
    pub def arityOf(ramSym: RamSym[v]): Int32 = match ramSym {
        case RamSym.Symbol(_, arity, _) => arity
    }

    @Internal
    pub def toDenotation(ramSym: RamSym[v]): Denotation[v] = match ramSym {
        case RamSym.Symbol(_, _, den) => den
    }

    /////////////////////////////////////////////////////////////////////////////
    // TupleVar                                                                //
    /////////////////////////////////////////////////////////////////////////////

    /**
    Note that the id is supposed to be unique

    For code:
        search e1 ∈ Edge  do 
            search e2 ∈ Edge do
                ...

    'e1' and 'e2' would be the TupleVars.
    */

    @Internal
    pub enum TupleVar with Eq {
        case Named(Int32)
        //case Index(Int32)
    }

    instance ToString[TupleVar] {
        pub def toString(var: TupleVar): String = match var {
            case TupleVar.Named(id) => "x${i}$"
        //    case TupleVar.Index(i) => "${i}$"
        }
    }

    instance Order[TupleVar] {
        pub def compare(a: TupleVar, b: TupleVar): Comparison = match (a, b) {
            case (TupleVar.Named(i1), TupleVar.Named(i2)) => i1 <=> i2
        //    case (TupleVar.Index(i1), TupleVar.Index(i2)) => i1 <=> i2
            case _ => ?bug
        }
    }    
}
