/*
 * Copyright 2023 Magnus Madsen
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
package ca.uwaterloo.flix.language.phase

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.{SimpleType, Purity}
import ca.uwaterloo.flix.language.ast.ReducedAst.*
import ca.uwaterloo.flix.language.ast.shared.ExpPosition
import ca.uwaterloo.flix.language.dbg.AstPrinter.*
import ca.uwaterloo.flix.util.ParOps

import java.util.concurrent.{ConcurrentHashMap, ConcurrentLinkedQueue}
import scala.annotation.tailrec
import scala.collection.immutable.Queue
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

/**
  * Objectives of this phase:
  *   1. Collect a list of the local parameters of each def
  *   1. Collect a set of all anonymous class / new object expressions
  *   1. Collect a flat set of all types of the program, i.e., if `List[String]` is
  *      in the list, so is `String`.
  */
object Reducer {

  def run(root: Root)(implicit flix: Flix): Root = flix.phase("Reducer") {
    implicit val ctx: SharedContext = SharedContext(new ConcurrentLinkedQueue, new ConcurrentHashMap())

    val newDefs = ParOps.parMapValues(root.defs)(visitDef(_)(root, ctx))
    val defTypes = ctx.defTypes.keys.asScala.toSet

    // This is an over approximation of the types in enums and structs since they are erased.
    val enumTypes = SimpleType.ErasedTypes
    val structTypes = SimpleType.ErasedTypes
    val effectTypes = root.effects.values.toSet.flatMap(typesOfEffect)

    val types = nestedTypesOf(Set.empty, Queue.from(defTypes ++ enumTypes ++ structTypes ++ effectTypes))

    root.copy(defs = newDefs, anonClasses = ctx.anonClasses.asScala.toList, types = types)
  }

  private def visitDef(d: Def)(implicit root: Root, ctx: SharedContext): Def = d match {
    case Def(ann, mod, sym, cparams, fparams, lparams, _, exp, tpe, unboxedType, loc) =>
      implicit val lctx: LocalContext = LocalContext.mk(exp.purity)
      assert(lparams.isEmpty, s"Unexpected def local params before Reducer: $lparams")
      val e = visitExpr(exp)
      val ls = lctx.lparams.toList
      val pcPoints = lctx.getPcPoints

      // Compute the types in the captured formal parameters.
      val cParamTypes = cparams.foldLeft(Set.empty[SimpleType]) {
        case (sacc, FormalParam(_, _, paramTpe, _)) => sacc + paramTpe
      }

      // `defn.fparams` and `defn.tpe` are both included in `defn.arrowType`
      ctx.defTypes.put(d.arrowType, ())
      ctx.defTypes.put(unboxedType.tpe, ())
      cParamTypes.foreach(t => ctx.defTypes.put(t, ()))

      Def(ann, mod, sym, cparams, fparams, ls, pcPoints, e, tpe, unboxedType, loc)
  }

  private def visitExpr(exp0: Expr)(implicit lctx: LocalContext, root: Root, ctx: SharedContext): Expr = {
    ctx.defTypes.put(exp0.tpe, ())
    exp0 match {
      case Expr.Cst(cst, tpe, loc) =>
        Expr.Cst(cst, tpe, loc)

      case Expr.Var(sym, tpe, loc) =>
        Expr.Var(sym, tpe, loc)

      case Expr.ApplyAtomic(op, exps, tpe, purity, loc) =>
        val es = exps.map(visitExpr)
        Expr.ApplyAtomic(op, es, tpe, purity, loc)

      case Expr.ApplyClo(exp1, exp2, ct, tpe, purity, loc) =>
        if (ct == ExpPosition.NonTail && Purity.isControlImpure(purity)) lctx.addPcPoint()
        val e1 = visitExpr(exp1)
        val e2 = visitExpr(exp2)
        Expr.ApplyClo(e1, e2, ct, tpe, purity, loc)

      case Expr.ApplyDef(sym, exps, ct, tpe, purity, loc) =>
        val defn = root.defs(sym)
        if (ct == ExpPosition.NonTail && Purity.isControlImpure(defn.expr.purity)) lctx.addPcPoint()
        val es = exps.map(visitExpr)
        Expr.ApplyDef(sym, es, ct, tpe, purity, loc)

      case Expr.ApplyOp(sym, exps, tpe, purity, loc) =>
        lctx.addPcPoint()
        val es = exps.map(visitExpr)
        Expr.ApplyOp(sym, es, tpe, purity, loc)

      case Expr.ApplySelfTail(sym, exps, tpe, purity, loc) =>
        val es = exps.map(visitExpr)
        Expr.ApplySelfTail(sym, es, tpe, purity, loc)

      case Expr.IfThenElse(exp1, exp2, exp3, tpe, purity, loc) =>
        val e1 = visitExpr(exp1)
        val e2 = visitExpr(exp2)
        val e3 = visitExpr(exp3)
        Expr.IfThenElse(e1, e2, e3, tpe, purity, loc)

      case Expr.Branch(exp, branches, tpe, purity, loc) =>
        val e = visitExpr(exp)
        val bs = branches map {
          case (label, body) => label -> visitExpr(body)
        }
        Expr.Branch(e, bs, tpe, purity, loc)

      case Expr.JumpTo(sym, tpe, purity, loc) =>
        Expr.JumpTo(sym, tpe, purity, loc)

      case Expr.Let(sym, exp1, exp2, tpe, purity, loc) =>
        lctx.lparams.addOne(LocalParam(sym, exp1.tpe))
        val e1 = visitExpr(exp1)
        val e2 = visitExpr(exp2)
        Expr.Let(sym, e1, e2, tpe, purity, loc)

      case Expr.Stmt(exp1, exp2, tpe, purity, loc) =>
        val e1 = visitExpr(exp1)
        val e2 = visitExpr(exp2)
        Expr.Stmt(e1, e2, tpe, purity, loc)

      case Expr.Scope(sym, exp, tpe, purity, loc) =>
        lctx.lparams.addOne(LocalParam(sym, SimpleType.Region))
        val e = visitExpr(exp)
        Expr.Scope(sym, e, tpe, purity, loc)

      case Expr.TryCatch(exp, rules, tpe, purity, loc) =>
        val e = visitExpr(exp)
        val rs = rules map {
          case CatchRule(sym, clazz, body) =>
            lctx.lparams.addOne(LocalParam(sym, SimpleType.Object))
            val b = visitExpr(body)
            CatchRule(sym, clazz, b)
        }
        Expr.TryCatch(e, rs, tpe, purity, loc)

      case Expr.RunWith(exp, effUse, rules, ct, tpe, purity, loc) =>
        if (ct == ExpPosition.NonTail) lctx.addPcPoint()
        val e = visitExpr(exp)
        val rs = rules.map {
          case HandlerRule(op, fparams, body) =>
            val b = visitExpr(body)
            HandlerRule(op, fparams, b)
        }
        Expr.RunWith(e, effUse, rs, ct, tpe, purity, loc)

      case Expr.NewObject(name, clazz, tpe, purity, methods, loc) =>
        val specs = methods.map {
          case JvmMethod(ident, fparams, clo, retTpe, methPurity, methLoc) =>
            val c = visitExpr(clo)
            JvmMethod(ident, fparams, c, retTpe, methPurity, methLoc)
        }
        ctx.anonClasses.add(AnonClass(name, clazz, tpe, specs, loc))

        Expr.NewObject(name, clazz, tpe, purity, specs, loc)

    }
  }

  /**
    * Companion object for [[LocalContext]].
    */
  private object LocalContext {
    def mk(purity: Purity): LocalContext = LocalContext(mutable.ArrayBuffer.empty, 0, Purity.isControlImpure(purity))
  }

  /**
    * A local non-shared context. Does not need to be thread-safe.
    *
    * @param lparams the bound variables in the def.
    */
  private case class LocalContext(lparams: mutable.ArrayBuffer[LocalParam], private var pcPoints: Int, private val isControlImpure: Boolean) {

    /**
      * Adds n to the private [[pcPoints]] field.
      */
    def addPcPoint(): Unit = {
      if (isControlImpure) {
        pcPoints += 1
      }
    }

    /**
      * Returns the pcPoints field.
      */
    def getPcPoints: Int = pcPoints
  }

  /**
    * A context shared across threads.
    *
    * We use a concurrent (non-blocking) linked queue to ensure thread-safety.
    */
  private case class SharedContext(anonClasses: ConcurrentLinkedQueue[AnonClass], defTypes: ConcurrentHashMap[SimpleType, Unit])

  /**
    * Returns all types contained in the given `Effect`.
    */
  private def typesOfEffect(e: Effect): Set[SimpleType] = {
    e.ops.toSet.map(extractFunctionType)
  }

  /**
    * Returns the function type based `op` represents.
    */
  private def extractFunctionType(op: Op): SimpleType = {
    val paramTypes = op.fparams.map(_.tpe)
    val resType = op.tpe
    val continuationType = SimpleType.Object
    val correctedFunctionType = SimpleType.Arrow(paramTypes :+ continuationType, resType)
    correctedFunctionType
  }

  /**
    * Returns all the type components of the given `types`.
    *
    * For example, if the types is just the type `Array[(Bool, Char, Int)]`
    * this returns the set `Bool`, `Char`, `Int`, `(Bool, Char, Int)`, and `Array[(Bool, Char, Int)]`
    * (and the types in `acc`).
    */
  @tailrec
  private def nestedTypesOf(acc: Set[SimpleType], types: Queue[SimpleType]): Set[SimpleType] = {
    import SimpleType.*
    types.dequeueOption match {
      case Some((tpe, taskList)) =>
        val taskList1 = tpe match {
          case Void | AnyType | Unit | Bool | Char | Float32 | Float64 | BigDecimal | Int8 | Int16 |
               Int32 | Int64 | BigInt | String | Regex | Region | RecordEmpty | ExtensibleEmpty |
               Native(_) | Null => taskList
          case Array(elm) => taskList.enqueue(elm)
          case Lazy(elm) => taskList.enqueue(elm)
          case Tuple(elms) => taskList.enqueueAll(elms)
          case Enum(_, targs) => taskList.enqueueAll(targs)
          case Struct(_, targs) => taskList.enqueueAll(targs)
          case Arrow(targs, tresult) => taskList.enqueueAll(targs).enqueue(tresult)
          case RecordExtend(_, value, rest) => taskList.enqueue(value).enqueue(rest)
          case ExtensibleExtend(_, targs, rest) => taskList.enqueueAll(targs).enqueue(rest)
        }
        nestedTypesOf(acc + tpe, taskList1)
      case None => acc
    }
  }

}
