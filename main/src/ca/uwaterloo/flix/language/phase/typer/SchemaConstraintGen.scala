/*
 * Copyright 2023 Matthew Lutze
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
package ca.uwaterloo.flix.language.phase.typer

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.*
import ca.uwaterloo.flix.language.ast.shared.SymUse.TraitSymUse
import ca.uwaterloo.flix.language.ast.shared.SymUse.AssocTypeSymUse
import ca.uwaterloo.flix.language.ast.shared.{Denotation, Scope, TraitConstraint}
import ca.uwaterloo.flix.language.phase.typer.ConstraintGen.{visitExp, visitPattern}
import ca.uwaterloo.flix.language.phase.util.PredefinedTraits
import ca.uwaterloo.flix.util.InternalCompilerException

object SchemaConstraintGen {

  def visitFixpointConstraintSet(e: KindedAst.Expr.FixpointConstraintSet)(implicit c: TypeContext, root: KindedAst.Root, flix: Flix): (Type, Type) = {
    implicit val scope: Scope = c.getScope
    e match {
      case KindedAst.Expr.FixpointConstraintSet(cs, tvar, loc) =>
        val constraintTypes = cs.map(visitConstraint)
        c.unifyAllTypes(constraintTypes, loc)
        val schemaRow = constraintTypes.headOption.getOrElse(Type.freshVar(Kind.SchemaRow, loc))
        c.unifyType(tvar, Type.mkSchema(schemaRow, loc), loc)
        val resTpe = tvar
        val resEff = Type.Pure
        (resTpe, resEff)
    }
  }

  def visitFixpointLambda(e: KindedAst.Expr.FixpointLambda)(implicit c: TypeContext, root: KindedAst.Root, flix: Flix): (Type, Type) = {
    implicit val scope: Scope = c.getScope
    e match {
      case KindedAst.Expr.FixpointLambda(pparams, exp, tvar, loc) =>

        def mkRowExtend(pparam: KindedAst.PredicateParam, restRow: Type): Type = pparam match {
          case KindedAst.PredicateParam(pred, paramTpe, _) => Type.mkSchemaRowExtend(pred, paramTpe, restRow, paramTpe.loc)
        }

        def mkFullRow(baseRow: Type): Type = pparams.foldRight(baseRow)(mkRowExtend)

        val expectedRowType = mkFullRow(Type.freshVar(Kind.SchemaRow, loc))
        val resultRowType = mkFullRow(Type.freshVar(Kind.SchemaRow, loc))

        val (tpe, eff) = visitExp(exp)
        c.unifyType(tpe, Type.mkSchema(expectedRowType, loc), loc)
        c.unifyType(tvar, Type.mkSchema(resultRowType, loc), loc)
        val resTpe = tvar
        val resEff = eff
        (resTpe, resEff)
    }
  }

  def visitFixpointMerge(e: KindedAst.Expr.FixpointMerge)(implicit c: TypeContext, root: KindedAst.Root, flix: Flix): (Type, Type) = {
    implicit val scope: Scope = c.getScope
    e match {
      case KindedAst.Expr.FixpointMerge(exp1, exp2, loc) =>
        //
        //  exp1 : #{...}    exp2 : #{...}
        //  ------------------------------
        //  exp1 <+> exp2 : #{...}
        //
        val (tpe1, eff1) = visitExp(exp1)
        val (tpe2, eff2) = visitExp(exp2)
        c.unifyType(tpe1, tpe2, Type.mkSchema(mkAnySchemaRowType(loc), loc), loc)
        val resTpe = tpe1
        val resEff = Type.mkUnion(eff1, eff2, loc)
        (resTpe, resEff)
    }
  }

  def visitFixpointQueryWithProvenance(e: KindedAst.Expr.FixpointQueryWithProvenance)(implicit c: TypeContext, root: KindedAst.Root, flix: Flix): (Type, Type) = {
    implicit val scope: Scope = c.getScope
    e match {
      case KindedAst.Expr.FixpointQueryWithProvenance(exps, select, withh, tvar, loc1) =>
        val (tpes, effs) = exps.map(visitExp).unzip
        val selectSchemaRow = select match {
          case KindedAst.Predicate.Head.Atom(_, Denotation.Relational, _, _, _) =>
            visitHeadPredicate(select)
          case _ => throw InternalCompilerException("Provenance for lattice relations is not supported", loc1)
        }
        val withSchemaRow = withh.foldRight(mkAnySchemaRowType(loc1)) {
          (pred, acc) => Type.mkSchemaRowExtend(pred, Type.freshVar(Kind.Predicate, loc1), acc, loc1)
        }
        val fresh = Type.freshVar(Kind.SchemaRow, loc1)
        c.unifyAllTypes(Type.mkSchema(fresh, loc1) :: Type.mkSchema(withSchemaRow, loc1) :: Type.mkSchema(selectSchemaRow, loc1) :: tpes, loc1)
        val resTpe = Type.mkVector(Type.mkExtensible(fresh, loc1), loc1)
        val resEff = Type.mkUnion(effs, loc1)
        c.unifyType(tvar, resTpe, loc1)
        (resTpe, resEff)
    }
  }

  def visitFixpointSolve(e: KindedAst.Expr.FixpointSolve)(implicit c: TypeContext, root: KindedAst.Root, flix: Flix): (Type, Type) = {
    implicit val scope: Scope = c.getScope
    e match {
      case KindedAst.Expr.FixpointSolve(exp, _, loc) =>
        //
        //  exp : #{...}
        //  ---------------
        //  solve exp : tpe
        //
        val (tpe, eff) = visitExp(exp)
        c.unifyType(tpe, Type.mkSchema(mkAnySchemaRowType(loc), loc), loc)
        val resEff = eff
        val resTpe = tpe
        (resTpe, resEff)
    }
  }


  def visitFixpointFilter(e: KindedAst.Expr.FixpointFilter)(implicit c: TypeContext, root: KindedAst.Root, flix: Flix): (Type, Type) = {
    implicit val scope: Scope = c.getScope
    e match {
      case KindedAst.Expr.FixpointFilter(pred, exp, tvar, loc) =>
        //
        //  exp1 : tpe    exp2 : #{ P : a  | b }
        //  -------------------------------------------
        //  project P exp2 : #{ P : a | c }
        //
        val freshPredicateTypeVar = Type.freshVar(Kind.Predicate, loc)
        val freshRestSchemaTypeVar = Type.freshVar(Kind.SchemaRow, loc)
        val freshResultSchemaTypeVar = Type.freshVar(Kind.SchemaRow, loc)

        val (tpe, eff) = visitExp(exp)
        c.unifyType(tpe, Type.mkSchema(Type.mkSchemaRowExtend(pred, freshPredicateTypeVar, freshRestSchemaTypeVar, loc), loc), loc)
        c.unifyType(tvar, Type.mkSchema(Type.mkSchemaRowExtend(pred, freshPredicateTypeVar, freshResultSchemaTypeVar, loc), loc), loc)
        val resTpe = tvar
        val resEff = eff
        (resTpe, resEff)
    }
  }

  def visitFixpointInject(e: KindedAst.Expr.FixpointInject)(implicit c: TypeContext, root: KindedAst.Root, flix: Flix): (Type, Type) = {
    implicit val scope: Scope = c.getScope
    e match {
      case KindedAst.Expr.FixpointInject(exp, pred, arity, tvar, evar, loc) =>
        //
        //  exp : F[(α₁, α₂, ...)] where F is Foldable
        //  -------------------------------------------
        //  project exp into A(_, _, ...): #{A(α₁, α₂, ...) | freshRestSchemaType}
        //
        val freshTypeConstructorVar = Type.freshVar(Kind.Star ->: Kind.Star, loc)
        val freshElmTypeVars = List.range(0, arity).map(_ => Type.freshVar(Kind.Star, loc))
        val tuple = Type.mkTuplish(freshElmTypeVars, loc)
        val freshRestSchemaTypeVar = Type.freshVar(Kind.SchemaRow, loc)

        // Require Order and Foldable instances.
        val orderSym = PredefinedTraits.lookupTraitSym("Order", root)
        val foldableSym = PredefinedTraits.lookupTraitSym("Foldable", root)
        val order = TraitConstraint(TraitSymUse(orderSym, loc), tuple, loc)
        val foldable = TraitConstraint(TraitSymUse(foldableSym, loc), freshTypeConstructorVar, loc)

        c.addClassConstraints(List(order, foldable), loc)

        val aefSym = new Symbol.AssocTypeSym(foldableSym, "Aef", loc)
        val aefTpe = Type.AssocType(AssocTypeSymUse(aefSym, loc), freshTypeConstructorVar, Kind.Eff, loc)

        val (tpe, eff) = visitExp(exp)
        c.unifyType(tpe, Type.mkApply(freshTypeConstructorVar, List(tuple), loc), loc)
        c.unifyType(tvar, Type.mkSchema(Type.mkSchemaRowExtend(pred, Type.mkRelation(freshElmTypeVars, loc), freshRestSchemaTypeVar, loc), loc), loc)
        c.unifyType(evar, Type.mkUnion(eff, aefTpe, loc), loc)
        val resTpe = tvar
        val resEff = evar
        (resTpe, resEff)
    }
  }

  def visitFixpointProject(e: KindedAst.Expr.FixpointProject)(implicit c: TypeContext, root: KindedAst.Root, flix: Flix): (Type, Type) = {
    implicit val scope: Scope = c.getScope
    e match {
      case KindedAst.Expr.FixpointProject(pred, arity, exp1, exp2, tvar, loc) =>
        //
        //  exp1: #{$freshRelOrLat(α₁, α₂, ...) | freshRestSchemaVar }
        //  exp2: freshRestSchemaVar
        //  --------------------------------------------------------------------
        //  FixpointQuery pred, exp1, exp2 : Array[(α₁, α₂, ...)]
        //
        val freshRelOrLat = Type.freshVar(Kind.mkArrowTo(arity, Kind.Predicate), loc)
        val freshElemVars = List.range(0, arity).map(_ => Type.freshVar(Kind.Star, loc))
        val tuple = Type.mkTuplish(freshElemVars, loc)
        val freshRestSchemaVar = Type.freshVar(Kind.SchemaRow, loc)
        val expectedSchemaType = Type.mkSchema(Type.mkSchemaRowExtend(pred, Type.mkApply(freshRelOrLat, freshElemVars, loc), freshRestSchemaVar, loc), loc)
        val (tpe1, eff1) = visitExp(exp1)
        val (tpe2, eff2) = visitExp(exp2)
        c.unifyType(tpe1, expectedSchemaType, loc)
        c.unifyType(tpe2, Type.mkSchema(freshRestSchemaVar, loc), loc)
        c.unifyType(tvar, Type.mkVector(tuple, loc), loc)
        val resTpe = tvar
        val resEff = Type.mkUnion(eff1, eff2, loc)
        (resTpe, resEff)
    }
  }

  private def visitConstraint(con0: KindedAst.Constraint)(implicit c: TypeContext, root: KindedAst.Root, flix: Flix): Type = {
    implicit val scope: Scope = c.getScope
    val KindedAst.Constraint(_, head0, body0, loc) = con0
    //
    //  A_0 : tpe, A_1: tpe, ..., A_n : tpe
    //  -----------------------------------
    //  A_0 :- A_1, ..., A_n : tpe
    //
    val headPredicateType = visitHeadPredicate(head0)
    val bodyPredicateTypes = body0.map(b => visitBodyPredicate(b))
    c.unifyAllTypes(bodyPredicateTypes, loc)
    val bodyPredicateType = bodyPredicateTypes.headOption.getOrElse(Type.freshVar(Kind.SchemaRow, loc))
    c.unifyType(headPredicateType, bodyPredicateType, loc)
    val resTpe = headPredicateType
    resTpe
  }


  /**
    * Infers the type of the given head predicate.
    */
  private def visitHeadPredicate(head: KindedAst.Predicate.Head)(implicit c: TypeContext, root: KindedAst.Root, flix: Flix): Type = {
    implicit val scope: Scope = c.getScope
    head match {
      case KindedAst.Predicate.Head.Atom(pred, den, terms, tvar, loc) =>
        // Adds additional type constraints if the denotation is a lattice.
        val restRow = Type.freshVar(Kind.SchemaRow, loc)
        val (termTypes, termEffs) = terms.map(visitExp(_)).unzip
        c.unifyType(Type.Pure, Type.mkUnion(termEffs, loc), loc)
        c.unifyType(tvar, mkRelationOrLatticeType(den, termTypes, loc), loc)
        val tconstrs = getTermTraitConstraints(den, termTypes, root, loc)
        c.addClassConstraints(tconstrs, loc)
        val resTpe = Type.mkSchemaRowExtend(pred, tvar, restRow, loc)
        resTpe
    }
  }

  /**
    * Infers the type of the given body predicate.
    */
  private def visitBodyPredicate(body0: KindedAst.Predicate.Body)(implicit c: TypeContext, root: KindedAst.Root, flix: Flix): Type = {
    implicit val scope: Scope = c.getScope
    body0 match {
      case KindedAst.Predicate.Body.Atom(pred, den, _, _, terms, tvar, loc) =>
        val restRow = Type.freshVar(Kind.SchemaRow, loc)
        val termTypes = terms.map(visitPattern)
        c.unifyType(tvar, mkRelationOrLatticeType(den, termTypes, loc), loc)
        val tconstrs = getTermTraitConstraints(den, termTypes, root, loc)
        c.addClassConstraints(tconstrs, loc)
        val resTpe = Type.mkSchemaRowExtend(pred, tvar, restRow, loc)
        resTpe

      case KindedAst.Predicate.Body.Functional(syms, exp, loc) =>
        val tupleType = Type.mkTuplish(syms.map(_.tvar), loc)
        val expectedType = Type.mkVector(tupleType, loc)
        val (tpe, eff) = visitExp(exp)
        c.unifyType(expectedType, tpe, loc)
        c.unifyType(Type.Pure, eff, loc)
        val resTpe = mkAnySchemaRowType(loc)
        resTpe

      case KindedAst.Predicate.Body.Guard(exp, loc) =>
        val (tpe, eff) = visitExp(exp)
        c.unifyType(Type.Pure, eff, loc)
        c.unifyType(Type.Bool, tpe, loc)
        val resTpe = mkAnySchemaRowType(loc)
        resTpe
    }
  }

  /**
    * Returns the relation or lattice type with the term types `ts`.
    */
  private def mkRelationOrLatticeType(den: Denotation, ts: List[Type], loc: SourceLocation): Type = den match {
    case Denotation.Relational => Type.mkRelation(ts, loc)
    case Denotation.Latticenal => Type.mkLattice(ts, loc)
  }

  /**
    * Returns the trait constraints for the given term types `ts` with the given denotation `den`.
    */
  private def getTermTraitConstraints(den: Denotation, ts: List[Type], root: KindedAst.Root, loc: SourceLocation): List[TraitConstraint] = den match {
    case Denotation.Relational =>
      ts.flatMap(mkTraitConstraintsForRelationalTerm(_, root, loc))
    case Denotation.Latticenal =>
      ts.init.flatMap(mkTraitConstraintsForRelationalTerm(_, root, loc)) ::: mkTraitConstraintsForLatticeTerm(ts.last, root, loc)
  }

  /**
    * Constructs the trait constraints for the given relational term type `tpe`.
    */
  private def mkTraitConstraintsForRelationalTerm(tpe: Type, root: KindedAst.Root, loc: SourceLocation): List[TraitConstraint] = {
    val traits = List(
      PredefinedTraits.lookupTraitSym("Eq", root),
      PredefinedTraits.lookupTraitSym("Order", root),
    )
    traits.map(trt => TraitConstraint(TraitSymUse(trt, loc), tpe, loc))
  }

  /**
    * Constructs the trait constraints for the given lattice term type `tpe`.
    */
  private def mkTraitConstraintsForLatticeTerm(tpe: Type, root: KindedAst.Root, loc: SourceLocation): List[TraitConstraint] = {
    val traits = List(
      PredefinedTraits.lookupTraitSym("Eq", root),
      PredefinedTraits.lookupTraitSym("Order", root),
      PredefinedTraits.lookupTraitSym("PartialOrder", root),
      PredefinedTraits.lookupTraitSym("LowerBound", root),
      PredefinedTraits.lookupTraitSym("JoinLattice", root),
      PredefinedTraits.lookupTraitSym("MeetLattice", root),
    )
    traits.map(trt => TraitConstraint(TraitSymUse(trt, loc), tpe, loc))
  }


  private def mkAnySchemaRowType(loc: SourceLocation)(implicit scope: Scope, flix: Flix): Type = Type.freshVar(Kind.SchemaRow, loc)
}
