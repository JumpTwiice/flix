/*
 *  Copyright 2017 Magnus Madsen
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package ca.uwaterloo.flix.language.ast

import ca.uwaterloo.flix.language.CompilationMessage
import ca.uwaterloo.flix.language.ast.shared.*
import ca.uwaterloo.flix.language.ast.shared.SymUse.*
import ca.uwaterloo.flix.util.collection.{ListMap, Nel}

import java.lang.reflect.Field

object ResolvedAst {

  val empty: Root = Root(Map.empty, ListMap.empty, Map.empty, Map.empty, Map.empty, Map.empty, Map.empty, Map.empty, ListMap.empty, List.empty, None, Map.empty, AvailableClasses.empty, Map.empty)

  case class Root(traits: Map[Symbol.TraitSym, Declaration.Trait],
                  instances: ListMap[Symbol.TraitSym, Declaration.Instance],
                  defs: Map[Symbol.DefnSym, Declaration.Def],
                  enums: Map[Symbol.EnumSym, Declaration.Enum],
                  structs: Map[Symbol.StructSym, Declaration.Struct],
                  restrictableEnums: Map[Symbol.RestrictableEnumSym, Declaration.RestrictableEnum],
                  effects: Map[Symbol.EffSym, Declaration.Effect],
                  typeAliases: Map[Symbol.TypeAliasSym, Declaration.TypeAlias],
                  uses: ListMap[Symbol.ModuleSym, UseOrImport],
                  taOrder: List[Symbol.TypeAliasSym],
                  mainEntryPoint: Option[Symbol.DefnSym],
                  sources: Map[Source, SourceLocation],
                  availableClasses: AvailableClasses,
                  tokens: Map[Source, Array[Token]])

  // TODO use Law for laws
  case class CompilationUnit(usesAndImports: List[UseOrImport], decls: List[Declaration], loc: SourceLocation)

  sealed trait Declaration

  object Declaration {
    case class Namespace(sym: Symbol.ModuleSym, usesAndImports: List[UseOrImport], decls: List[Declaration], loc: SourceLocation) extends Declaration

    case class Trait(doc: Doc, ann: Annotations, mod: Modifiers, sym: Symbol.TraitSym, tparam: TypeParam, superTraits: List[TraitConstraint], assocs: List[Declaration.AssocTypeSig], sigs: Map[Symbol.SigSym, Declaration.Sig], laws: List[Declaration.Def], loc: SourceLocation) extends Declaration

    case class Instance(doc: Doc, ann: Annotations, mod: Modifiers, symUse: TraitSymUse, tparams: List[TypeParam], tpe: UnkindedType, tconstrs: List[TraitConstraint], econstrs: List[EqualityConstraint], assocs: List[Declaration.AssocTypeDef], defs: List[Declaration.Def], ns: Name.NName, loc: SourceLocation) extends Declaration

    case class Sig(sym: Symbol.SigSym, spec: Spec, exp: Option[Expr], loc: SourceLocation) extends Declaration

    case class Def(sym: Symbol.DefnSym, spec: Spec, exp: Expr, loc: SourceLocation) extends Declaration

    case class Enum(doc: Doc, ann: Annotations, mod: Modifiers, sym: Symbol.EnumSym, tparams: List[TypeParam], derives: Derivations, cases: List[Declaration.Case], loc: SourceLocation) extends Declaration

    case class Struct(doc: Doc, ann: Annotations, mod: Modifiers, sym: Symbol.StructSym, tparams: List[TypeParam], fields: List[StructField], loc: SourceLocation) extends Declaration

    case class StructField(mod: Modifiers, sym: Symbol.StructFieldSym, tpe: UnkindedType, loc: SourceLocation)

    case class RestrictableEnum(doc: Doc, ann: Annotations, mod: Modifiers, sym: Symbol.RestrictableEnumSym, index: TypeParam, tparams: List[TypeParam], derives: Derivations, cases: List[Declaration.RestrictableCase], loc: SourceLocation) extends Declaration

    case class Case(sym: Symbol.CaseSym, tpes: List[UnkindedType], loc: SourceLocation) extends Declaration

    case class RestrictableCase(sym: Symbol.RestrictableCaseSym, tpes: List[UnkindedType], loc: SourceLocation) extends Declaration

    case class TypeAlias(doc: Doc, ann: Annotations, mod: Modifiers, sym: Symbol.TypeAliasSym, tparams: List[TypeParam], tpe: UnkindedType, loc: SourceLocation) extends Declaration

    case class AssocTypeSig(doc: Doc, mod: Modifiers, sym: Symbol.AssocTypeSym, tparam: TypeParam, kind: Kind, tpe: Option[UnkindedType], loc: SourceLocation) extends Declaration

    case class AssocTypeDef(doc: Doc, mod: Modifiers, symUse: AssocTypeSymUse, arg: UnkindedType, tpe: UnkindedType, loc: SourceLocation) extends Declaration

    case class Effect(doc: Doc, ann: Annotations, mod: Modifiers, sym: Symbol.EffSym, tparams: List[TypeParam], ops: List[Declaration.Op], loc: SourceLocation) extends Declaration

    case class Op(sym: Symbol.OpSym, spec: Spec, loc: SourceLocation) extends Declaration
  }

  case class Spec(doc: Doc, ann: Annotations, mod: Modifiers, tparams: List[TypeParam], fparams: List[FormalParam], tpe: UnkindedType, eff: Option[UnkindedType], tconstrs: List[TraitConstraint], econstrs: List[EqualityConstraint])

  sealed trait Expr {
    def loc: SourceLocation
  }

  object Expr {

    case class Var(sym: Symbol.VarSym, loc: SourceLocation) extends Expr

    case class Hole(sym: Symbol.HoleSym, scp: LocalScope, loc: SourceLocation) extends Expr

    case class HoleWithExp(exp: Expr, scp: LocalScope, loc: SourceLocation) extends Expr

    case class OpenAs(symUse: RestrictableEnumSymUse, exp: Expr, loc: SourceLocation) extends Expr

    case class Use(sym: Symbol, alias: Name.Ident, exp: Expr, loc: SourceLocation) extends Expr

    case class Cst(cst: Constant, loc: SourceLocation) extends Expr

    case class ApplyClo(exp1: Expr, exp2: Expr, loc: SourceLocation) extends Expr

    case class ApplyDef(symUse: DefSymUse, exps: List[Expr], loc: SourceLocation) extends Expr

    case class ApplyLocalDef(symUse: LocalDefSymUse, exps: List[Expr], loc: SourceLocation) extends Expr

    case class ApplyOp(symUse: OpSymUse, exps: List[Expr], loc: SourceLocation) extends Expr

    case class ApplySig(symUse: SigSymUse, exps: List[Expr], loc: SourceLocation) extends Expr

    case class Lambda(fparam: FormalParam, exp: Expr, allowSubeffecting: Boolean, loc: SourceLocation) extends Expr

    case class Unary(sop: SemanticOp.UnaryOp, exp: Expr, loc: SourceLocation) extends Expr

    case class Binary(sop: SemanticOp.BinaryOp, exp1: Expr, exp2: Expr, loc: SourceLocation) extends Expr

    case class IfThenElse(exp1: Expr, exp2: Expr, exp3: Expr, loc: SourceLocation) extends Expr

    case class Stm(exp1: Expr, exp2: Expr, loc: SourceLocation) extends Expr

    case class Discard(exp: Expr, loc: SourceLocation) extends Expr

    case class Let(sym: Symbol.VarSym, exp1: Expr, exp2: Expr, loc: SourceLocation) extends Expr

    case class LocalDef(sym: Symbol.VarSym, fparams: List[FormalParam], exp1: Expr, exp2: Expr, loc: SourceLocation) extends Expr

    // MATT why was this a full type
    case class Region(tpe: Type, loc: SourceLocation) extends Expr

    case class Scope(sym: Symbol.VarSym, regSym: Symbol.RegionSym, exp: Expr, loc: SourceLocation) extends Expr

    case class Match(exp: Expr, rules: List[MatchRule], loc: SourceLocation) extends Expr

    case class TypeMatch(exp: Expr, rules: List[TypeMatchRule], loc: SourceLocation) extends Expr

    case class RestrictableChoose(star: Boolean, exp: Expr, rules: List[RestrictableChooseRule], loc: SourceLocation) extends Expr

    case class ExtMatch(exp: Expr, rules: List[ExtMatchRule], loc: SourceLocation) extends Expr

    case class Tag(symUse: CaseSymUse, exps: List[Expr], loc: SourceLocation) extends Expr

    case class RestrictableTag(symUse: RestrictableCaseSymUse, exps: List[Expr], isOpen: Boolean, loc: SourceLocation) extends Expr

    case class ExtTag(label: Name.Label, exps: List[Expr], loc: SourceLocation) extends Expr

    case class Tuple(exps: List[Expr], loc: SourceLocation) extends Expr

    case class RecordSelect(exp: Expr, label: Name.Label, loc: SourceLocation) extends Expr

    case class RecordExtend(label: Name.Label, value: Expr, rest: Expr, loc: SourceLocation) extends Expr

    case class RecordRestrict(label: Name.Label, rest: Expr, loc: SourceLocation) extends Expr

    case class ArrayLit(exps: List[Expr], exp: Expr, loc: SourceLocation) extends Expr

    case class ArrayNew(exp1: Expr, exp2: Expr, exp3: Expr, loc: SourceLocation) extends Expr

    case class ArrayLoad(base: Expr, index: Expr, loc: SourceLocation) extends Expr

    case class ArrayStore(base: Expr, index: Expr, elm: Expr, loc: SourceLocation) extends Expr

    case class ArrayLength(base: Expr, loc: SourceLocation) extends Expr

    case class StructNew(sym: Symbol.StructSym, exps: List[(StructFieldSymUse, Expr)], region: Expr, loc: SourceLocation) extends Expr

    case class StructGet(exp: Expr, symUse: StructFieldSymUse, loc: SourceLocation) extends Expr

    case class StructPut(exp1: Expr, symUse: StructFieldSymUse, exp2: Expr, loc: SourceLocation) extends Expr

    case class VectorLit(exps: List[Expr], loc: SourceLocation) extends Expr

    case class VectorLoad(exp1: Expr, exp2: Expr, loc: SourceLocation) extends Expr

    case class VectorLength(exp: Expr, loc: SourceLocation) extends Expr

    case class Ascribe(exp: Expr, expectedType: Option[UnkindedType], expectedEff: Option[UnkindedType], loc: SourceLocation) extends Expr

    case class InstanceOf(exp: Expr, clazz: java.lang.Class[?], loc: SourceLocation) extends Expr

    case class CheckedCast(cast: CheckedCastType, exp: Expr, loc: SourceLocation) extends Expr

    case class UncheckedCast(exp: Expr, declaredType: Option[UnkindedType], declaredEff: Option[UnkindedType], loc: SourceLocation) extends Expr

    case class Unsafe(exp: Expr, eff: UnkindedType, loc: SourceLocation) extends Expr

    case class Without(exp: Expr, symUse: EffSymUse, loc: SourceLocation) extends Expr

    case class TryCatch(exp: Expr, rules: List[CatchRule], loc: SourceLocation) extends Expr

    case class Throw(exp: Expr, loc: SourceLocation) extends Expr

    case class Handler(symUse: EffSymUse, rules: List[HandlerRule], loc: SourceLocation) extends Expr

    case class RunWith(exp1: Expr, exp2: Expr, loc: SourceLocation) extends Expr

    case class InvokeConstructor(clazz: Class[?], exps: List[Expr], loc: SourceLocation) extends Expr

    case class InvokeMethod(exp: Expr, methodName: Name.Ident, exps: List[Expr], loc: SourceLocation) extends Expr

    case class InvokeStaticMethod(clazz: Class[?], methodName: Name.Ident, exps: List[Expr], loc: SourceLocation) extends Expr

    case class GetField(exp: Expr, fieldName: Name.Ident, loc: SourceLocation) extends Expr

    case class PutField(field: Field, clazz: java.lang.Class[?], exp1: Expr, exp2: Expr, loc: SourceLocation) extends Expr

    case class GetStaticField(field: Field, loc: SourceLocation) extends Expr

    case class PutStaticField(field: Field, exp: Expr, loc: SourceLocation) extends Expr

    case class NewObject(name: String, clazz: java.lang.Class[?], methods: List[JvmMethod], loc: SourceLocation) extends Expr

    case class NewChannel(exp: Expr, loc: SourceLocation) extends Expr

    case class GetChannel(exp: Expr, loc: SourceLocation) extends Expr

    case class PutChannel(exp1: Expr, exp2: Expr, loc: SourceLocation) extends Expr

    case class SelectChannel(rules: List[SelectChannelRule], default: Option[Expr], loc: SourceLocation) extends Expr

    case class Spawn(exp1: Expr, exp2: Expr, loc: SourceLocation) extends Expr

    case class ParYield(frags: List[ParYieldFragment], exp: Expr, loc: SourceLocation) extends Expr

    case class Lazy(exp: Expr, loc: SourceLocation) extends Expr

    case class Force(exp: Expr, loc: SourceLocation) extends Expr

    case class FixpointConstraintSet(cs: List[Constraint], loc: SourceLocation) extends Expr

    case class FixpointLambda(pparams: List[PredicateParam], exp: Expr, loc: SourceLocation) extends Expr

    case class FixpointMerge(exp1: Expr, exp2: Expr, loc: SourceLocation) extends Expr

    case class FixpointQueryWithProvenance(exps: List[Expr], select: Predicate.Head, withh: List[Name.Pred], loc: SourceLocation) extends Expr

    case class FixpointSolve(exp: Expr, mode: SolveMode, loc: SourceLocation) extends Expr

    case class FixpointFilter(pred: Name.Pred, exp: Expr, loc: SourceLocation) extends Expr

    case class FixpointInject(exp: Expr, pred: Name.Pred, arity: Int, loc: SourceLocation) extends Expr

    case class FixpointProject(pred: Name.Pred, arity: Int, exp1: Expr, exp2: Expr, loc: SourceLocation) extends Expr

    case class Error(m: CompilationMessage) extends Expr {
      override def loc: SourceLocation = m.loc
    }

  }

  sealed trait Pattern {
    def loc: SourceLocation
  }

  object Pattern {

    case class Wild(loc: SourceLocation) extends Pattern

    case class Var(sym: Symbol.VarSym, loc: SourceLocation) extends Pattern

    case class Cst(cst: Constant, loc: SourceLocation) extends Pattern

    case class Tag(symUse: CaseSymUse, pats: List[Pattern], loc: SourceLocation) extends Pattern

    case class Tuple(pats: Nel[Pattern], loc: SourceLocation) extends Pattern

    case class Record(pats: List[Record.RecordLabelPattern], pat: Pattern, loc: SourceLocation) extends Pattern

    case class Error(loc: SourceLocation) extends Pattern

    object Record {
      case class RecordLabelPattern(label: Name.Label, pat: Pattern, loc: SourceLocation)
    }

  }

  sealed trait RestrictableChoosePattern

  object RestrictableChoosePattern {

    sealed trait VarOrWild

    case class Wild(loc: SourceLocation) extends VarOrWild

    case class Var(sym: Symbol.VarSym, loc: SourceLocation) extends VarOrWild

    case class Tag(symUse: RestrictableCaseSymUse, pats: List[VarOrWild], loc: SourceLocation) extends RestrictableChoosePattern

    case class Error(loc: SourceLocation) extends VarOrWild with RestrictableChoosePattern

  }

  sealed trait ExtPattern {
    def loc: SourceLocation
  }

  object ExtPattern {

    case class Wild(loc: SourceLocation) extends ExtPattern

    case class Var(sym: Symbol.VarSym, loc: SourceLocation) extends ExtPattern

    case class Error(loc: SourceLocation) extends ExtPattern
  }


  sealed trait Predicate

  object Predicate {

    sealed trait Head extends Predicate

    object Head {

      case class Atom(pred: Name.Pred, den: Denotation, terms: List[Expr], loc: SourceLocation) extends Predicate.Head

    }

    sealed trait Body extends Predicate

    object Body {

      case class Atom(pred: Name.Pred, den: Denotation, polarity: Polarity, fixity: Fixity, terms: List[Pattern], loc: SourceLocation) extends Predicate.Body

      case class Functional(syms: List[Symbol.VarSym], exp: Expr, loc: SourceLocation) extends Predicate.Body

      case class Guard(exp: Expr, loc: SourceLocation) extends Predicate.Body

    }

  }

  case class Constraint(cparams: List[ConstraintParam], head: Predicate.Head, body: List[Predicate.Body], loc: SourceLocation)

  case class ConstraintParam(sym: Symbol.VarSym, loc: SourceLocation)

  case class FormalParam(sym: Symbol.VarSym, mod: Modifiers, tpe: Option[UnkindedType], loc: SourceLocation)

  sealed trait PredicateParam

  object PredicateParam {

    case class PredicateParamUntyped(pred: Name.Pred, loc: SourceLocation) extends PredicateParam

    case class PredicateParamWithType(pred: Name.Pred, den: Denotation, tpes: List[UnkindedType], loc: SourceLocation) extends PredicateParam

  }

  case class JvmMethod(ident: Name.Ident, fparams: List[FormalParam], exp: Expr, tpe: UnkindedType, eff: Option[UnkindedType], loc: SourceLocation)

  case class CatchRule(sym: Symbol.VarSym, clazz: java.lang.Class[?], exp: Expr, loc: SourceLocation)

  case class HandlerRule(symUse: OpSymUse, fparams: List[FormalParam], exp: Expr, loc: SourceLocation)

  case class RestrictableChooseRule(pat: RestrictableChoosePattern, exp: Expr)

  case class MatchRule(pat: Pattern, guard: Option[Expr], exp: Expr, loc: SourceLocation)

  case class ExtMatchRule(label: Name.Label, pats: List[ExtPattern], exp: Expr, loc: SourceLocation)

  case class TypeMatchRule(sym: Symbol.VarSym, tpe: UnkindedType, exp: Expr, loc: SourceLocation)

  case class SelectChannelRule(sym: Symbol.VarSym, chan: Expr, exp: Expr, loc: SourceLocation)

  sealed trait TypeParam {
    val name: Name.Ident
    val sym: Symbol.UnkindedTypeVarSym
  }

  object TypeParam {
    case class Kinded(name: Name.Ident, sym: Symbol.UnkindedTypeVarSym, kind: Kind, loc: SourceLocation) extends TypeParam

    case class Unkinded(name: Name.Ident, sym: Symbol.UnkindedTypeVarSym, loc: SourceLocation) extends TypeParam

    case class Implicit(name: Name.Ident, sym: Symbol.UnkindedTypeVarSym, loc: SourceLocation) extends TypeParam
  }

  case class TraitConstraint(symUse: TraitSymUse, tpe: UnkindedType, loc: SourceLocation)

  case class EqualityConstraint(assocTypeSymUse: AssocTypeSymUse, tpe1: UnkindedType, tpe2: UnkindedType, loc: SourceLocation)

  case class ParYieldFragment(pat: Pattern, exp: Expr, loc: SourceLocation)

}
