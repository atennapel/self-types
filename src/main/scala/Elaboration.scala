import Common.*
import Common.Bind.*
import Common.Icit.*
import Debug.debug
import Core.*
import Evaluation.*
import Ctx.*
import Surface as S
import State.GlobalEntry

import scala.annotation.tailrec

object Elaboration:
  class ElaborationError(val pos: PosInfo, val msg: String)
      extends RuntimeException(msg):
    override def toString: String = s"elaboration error at $pos: $msg"
  private inline def err(msg: String)(using ctx: Ctx): Nothing =
    throw new ElaborationError(ctx.pos, msg)

  // unification
  private def unify(a: VTy, b: VTy)(using ctx: Ctx): Unit =
    debug(s"unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
    try Unification.unify(a, b)(using ctx.lvl)
    catch
      case ue: Unification.UnificationError =>
        err(
          s"failed to unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}: ${ue.msg}"
        )

  // metas
  private def closeTy(ty: Ty)(implicit ctx: Ctx): Ty =
    @tailrec
    def go(ls: Locals, xs: List[Bind], ty: Ty): Ty = (ls, xs) match
      case (Locals.Empty, Nil)                     => ty
      case (Locals.Def(ls, a, v), DoBind(x) :: xs) =>
        go(ls, xs, Tm.Let(x, a, v, ty))
      case (Locals.Bind(ls, a, i), x :: xs) => go(ls, xs, Tm.Pi(x, i, a, ty))
      case _                                => impossible()
    go(ctx.locals, ctx.binds, ty)

  private def freshMetaId(ty: VTy)(using ctx: Ctx): MetaId =
    val qa = closeTy(ctx.quote(ty))
    val vqa = eval(qa)(using Env.Empty)
    val m = State.newMeta(vqa)
    debug(s"freshMetaId ?$m : ${ctx.pretty(ty)}")
    m

  private def freshMeta(ty: VTy)(using ctx: Ctx): Tm =
    Tm.AppPruning(freshMetaId(ty), ctx.pruning)

  private def insertPi(inp: (Tm, VTy))(implicit ctx: Ctx): (Tm, VTy) =
    @tailrec
    def go(tm: Tm, ty: VTy): (Tm, VTy) =
      forceAll(ty) match
        case Val.Pi(y, Impl, a, b) =>
          val m = freshMeta(a)
          go(Tm.App(tm, m, Impl), b(ctx.eval(m)))
        case _ => (tm, ty)
    go(inp._1, inp._2)

  private def insert(inp: (Tm, VTy))(implicit ctx: Ctx): (Tm, VTy) =
    inp._1 match
      case Tm.Lam(_, Impl, _, _) => inp
      case _                     => insertPi(inp)

  private def freshMetaIgnoreDeps(ty: VTy)(using ctx: Ctx): Tm =
    def go(ctx: Ctx, ty: VTy): Tm = forceAll(ty) match
      case Val.Pi(_, i, a, b) =>
        val qa = ctx.quote(a)
        val body =
          go(ctx.bind(DontBind, i, qa, a, skip = true), b(Var1(ctx.lvl)))
        Tm.Lam(DontBind, i, qa, body)
      case _ => Tm.AppPruning(freshMetaId(ty)(using ctx), ctx.pruning)
    go(ctx, ty)

  // coercion
  private def coe(t: Tm, a1: VTy, a2: VTy)(using ctx: Ctx): Tm =
    unify(a1, a2)
    t

  // helpers
  private inline def enter[A](pos: PosInfo)(inline action: Ctx ?=> A)(using
      ctx: Ctx
  ): A =
    action(using ctx.enter(pos))

  private def addHole(mx: Option[Name], tm: Tm, ty: VTy)(using ctx: Ctx): Unit =
    mx.foreach(x => if (!State.addHole(x, tm, ty)) err(s"duplicate hole _$x"))

  private def getSelfBody(vty: VTy, arg: Tm)(using ctx: Ctx): VTy =
    forceAll(vty, true) match
      case Val.Self(_, _, b) => b(ctx.eval(arg))
      case _                 =>
        err(
          s"cannot call out on expression of type ${ctx.pretty(vty)}"
        )

  // checking
  private def check(tm: S.Tm, ty: VTy)(using ctx: Ctx): Tm = check(tm, ty, None)

  private def check(tm: S.Tm, ty: VTy, self: Option[Val])(using ctx: Ctx): Tm =
    debug(
      s"check $tm : ${ctx.pretty(ty)}${self.map(s => s" with self ${ctx.pretty(s)}").getOrElse("")}"
    )
    enter(tm.pos):
      (tm, forceAll(ty, true)) match
        case (S.Tm.Lam(_, x, i, ma, b), Val.Pi(x2, i2, t1, t2)) if i == i2 =>
          ma.foreach { sty => unify(ctx.eval(check(sty, Val.Type)), t1) }
          val qt1 = ctx.quote(t1)
          val v = Var1(ctx.lvl)
          val nself = self.map(s => app(s, v, i))
          val eb =
            check(b, t2(v), nself)(using ctx.bind(x, i, qt1, t1))
          val y = x match
            case Bind.DoBind(_) => x
            case Bind.DontBind  => x2
          Tm.Lam(y, i, qt1, eb)

        case (tm, Val.Pi(x, Impl, a, b)) =>
          val qa = ctx.quote(a)
          val v = Var1(ctx.lvl)
          val nself = self.map(s => app(s, v, Impl))
          val body = check(tm, b(v), nself)(using ctx.insert(x, Impl, qa))
          Tm.Lam(x, Impl, qa, body)

        case (S.Tm.Let(_, x, mlty, v, b), _) =>
          val (ev, lty, vlty) = mlty match
            case None =>
              val (ev, vlty) = infer(v)
              val lty = ctx.quote(vlty)
              (ev, lty, vlty)
            case Some(ty) =>
              val lty = check(ty, Val.Type)
              val vlty = ctx.eval(lty)
              val ev = check(v, vlty)
              (ev, lty, vlty)
          val eb =
            check(b, ty, self)(using ctx.define(x, lty, vlty, ev, ctx.eval(ev)))
          Tm.Let(x, lty, ev, eb)

        case (S.Tm.In(_, b), Val.Self(_, _, sty)) =>
          val s =
            self.getOrElse(err(s"self required for typechecking in-expression"))
          val eb = check(b, sty(s))
          Tm.In(eb)

        case (S.Tm.Hole(_, mx), _) =>
          val tm = freshMeta(ty)
          mx.foreach(x => State.addHole(x, tm, ty))
          tm

        case (tm, _) =>
          val (etm, vty) = insert(infer(tm))
          coe(etm, vty, ty)

  // inference
  private def infer(tm: S.Tm)(using ctx: Ctx): (Tm, VTy) =
    debug(s"infer $tm")
    enter(tm.pos):
      tm match
        case S.Tm.Hole(_, mx) =>
          val ty = ctx.eval(freshMeta(Val.Type))
          val tm = freshMeta(ty)
          mx.foreach(x => State.addHole(x, tm, ty))
          (tm, ty)

        case S.Tm.Type(_) => (Tm.Type, Val.Type)

        case S.Tm.Var(_, x) =>
          ctx.lookup(x) match
            case Some(NameInfo(x, ty)) =>
              (Tm.Var(x.toIx(using ctx.lvl)), ty)
            case None =>
              State.getGlobal(x) match
                case Some(g @ GlobalEntry(_, _, _, ty, _)) => (Tm.Global(x), ty)
                case _ => err(s"undefined variable $x")

        case S.Tm.Let(_, x, mty, v, b) =>
          val (ev, lty, vlty) = mty match
            case None =>
              val (ev, vlty) = infer(v)
              val lty = ctx.quote(vlty)
              (ev, lty, vlty)
            case Some(ty) =>
              val lty = check(ty, Val.Type)
              val vlty = ctx.eval(lty)
              val ev = check(v, vlty)
              (ev, lty, vlty)
          val (eb, rty) =
            infer(b)(using ctx.define(x, lty, vlty, ev, ctx.eval(ev)))
          (Tm.Let(x, lty, ev, eb), rty)

        case S.Tm.Pi(_, x, i, a, b) =>
          val ea = check(a, Val.Type)
          val eb = check(b, Val.Type)(using ctx.bind(x, i, ea, ctx.eval(ea)))
          (Tm.Pi(x, i, ea, eb), Val.Type)

        case S.Tm.Self(_, x, ma, b) =>
          val ea = ma match
            case Some(a) => check(a, Val.Type)
            case None    => freshMeta(Val.Type)
          val eb =
            check(b, Val.Type)(using
              ctx.bind(DoBind(x), Expl, ea, ctx.eval(ea))
            )
          (Tm.Self(x, ea, eb), Val.Type)

        case S.Tm.Lam(_, x, i, mty, b) =>
          val ety = mty match
            case None     => freshMeta(Val.Type)
            case Some(ty) => check(ty, Val.Type)
          val vty = ctx.eval(ety)
          val ctx2 = ctx.bind(x, i, ety, vty)
          val (eb, vrt) = insert(infer(b)(using ctx2))
          val qrt = ctx2.quote(vrt)
          (
            Tm.Lam(x, i, ety, eb),
            Val.Pi(x, i, vty, Clos.Clos(ctx.env, qrt))
          )

        case S.Tm.App(_, f, a, i) =>
          val (ef, fty) = i match
            case Impl => infer(f)
            case Expl => insertPi(infer(f))
          val (pty, rty) = forceAll(fty) match
            case Val.Pi(_, i2, pty, rty) =>
              if i != i2 then err(s"icit mismatch in application")
              (pty, rty)
            case _ =>
              val pty = freshMeta(Val.Type)
              val vpty = ctx.eval(pty)
              val x = Bind.DoBind(Name("x"))
              val rty = Clos.Clos(
                ctx.env,
                freshMeta(Val.Type)(using
                  ctx.bind(x, i, pty, vpty)
                )
              )
              unify(fty, Val.Pi(x, i, vpty, rty))
              (vpty, rty)
          val ea = check(a, pty)
          (Tm.App(ef, ea, i), rty(ctx.eval(ea)))

        case S.Tm.Out(_, tm) =>
          val (etm, vty) = infer(tm)
          val rty = getSelfBody(vty, etm)
          (Tm.Out(etm), rty)

        case S.Tm.In(_, tm) => err("cannot infer in-expression")

        case S.Tm.Case(_, scrut, ty, cs) =>
          val (escrut, vty) = infer(scrut)
          val vselfty = getSelfBody(vty, escrut)
          val (rty, vrty, i) = forceAll(vselfty) match
            case Val.Pi(_, i, expty, b) =>
              val arg = ty match
                case Some(ty) => check(ty, expty)
                case None     => freshMetaIgnoreDeps(expty)
              val varg = ctx.eval(arg)
              (arg, b(varg), i)
            case _ =>
              err(
                s"expected pi-type for case scrutinee type but got ${ctx.pretty(vselfty)}"
              )
          val xs = cs.map((_, x, _) => x)
          if xs.toSet.size != xs.size then err(s"duplicate constructor in case")
          val map = cs.map((pos, x, b) => x -> (pos, b)).toMap
          val etm = Tm.App(Tm.Out(escrut), rty, i)
          elaborateCases(map, etm, vrty)

  @tailrec
  private def elaborateCases(
      cs: Map[Name, (PosInfo, S.Tm)],
      tm: Tm,
      dty: VTy
  )(using
      ctx: Ctx
  ): (Tm, VTy) =
    forceAll(dty) match
      case Val.Pi(bx, i, a, b) =>
        val x = bx match
          case DoBind(x) => x
          case DontBind  =>
            err(s"case requires named parameters for the data type")
        cs.get(x) match
          case None              => err(s"missing constructor $x in case")
          case Some((pos, body)) =>
            val ebody = check(body, a)(using ctx.enter(pos))
            val vbody = ctx.eval(ebody)
            val ntm = Tm.App(tm, ebody, i)
            elaborateCases(cs - x, ntm, b(vbody))
      case _ if cs.nonEmpty => err(s"too many constructors in case")
      case _                => (tm, dty)

  // elaboration
  private def elaborate(defn: S.Def): Def =
    debug(s"elaborate $defn")
    given ctx: Ctx = Ctx.empty.enter(defn.pos)
    val x = defn.name
    if State.nameIsDefined(x) then err(s"duplicate name $x")
    val (ety, vty) = State.getGlobal(x) match
      case Some(GlobalEntry(_, _, ety, vty, _)) => (ety, vty)
      case _                                    => impossible()
    val self = Val.Unfold(UnfoldHead.Global(x), Spine.Empty)
    val ev = check(defn.value, vty, Some(self))
    val vv = ctx.eval(ev)
    State.updateGlobalValue(x, ev, vv)
    Def(x, ety, ev)

  private def prepareElaboration(defn: S.Def): Unit =
    debug(s"prepareElaboration $defn")
    given ctx: Ctx = Ctx.empty.enter(defn.pos)
    val x = defn.name
    val ety = defn.ty match
      case None     => freshMeta(Val.Type)
      case Some(ty) => check(ty, Val.Type)
    val vty = ctx.eval(ety)
    State.addGlobal(GlobalEntry(x, defn.opaque, ety, vty, None))

  def elaborate(ds: S.Defs): Defs =
    ds.foreach(prepareElaboration)
    val res = ds.map(elaborate)
    val holes = State.getHoles().map { case State.HoleEntry(ctx, x, tm, ty) =>
      s"_$x : ${ctx.pretty(ty)} = ${ctx.pretty(tm)}"
    }
    if holes.nonEmpty then
      err(s"there are holes:\n${holes.mkString("\n")}")(using Ctx.empty)
    val ums =
      State.unsolvedMetas().map((m, ty) => s"?$m : ${Ctx.empty.pretty(ty)}")
    if ums.nonEmpty then
      err(s"there are unsolved metas:\n${ums.mkString("\n")}")(using Ctx.empty)
    res
