import Common.*
import Debug.debug
import Core.*
import Evaluation.*
import Ctx.*
import Surface as S
import State.GlobalEntry

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

  // coercion
  private def coe(t: Tm, a1: VTy, a2: VTy)(using ctx: Ctx): Tm =
    def go(t: Tm, a1: VTy, a2: VTy)(using ctx: Ctx): Option[Tm] =
      debug(s"coe ${ctx.pretty(t)} from ${ctx.pretty(a1)} to ${ctx.pretty(a2)}")
      (forceAll(a1), forceAll(a2)) match
        case (Val.Pi(x, a1, b1), Val.Pi(_, a2, b2)) =>
          given ctx2: Ctx = ctx.bind(x, ctx.quote(a2), a2)
          go(Tm.Var(ix0), a2, a1) match
            case None =>
              go(
                Tm.App(Tm.Wk(t), Tm.Var(ix0)),
                b1(ctx2.eval(Tm.Var(ix0))),
                b2(Var1(ctx.lvl))
              ).map(b => Tm.Lam(x, ctx.quote(a2), b))
            case Some(coev0) =>
              Some(
                Tm.Lam(
                  x,
                  ctx.quote(a2),
                  coe(
                    Tm.App(Tm.Wk(t), coev0),
                    b1(ctx2.eval(coev0)),
                    b2(Var1(ctx.lvl))
                  )
                )
              )
        case (_, _) => unify(a1, a2); None
    go(t, a1, a2).getOrElse(t)

  // helpers
  private inline def enter[A](pos: PosInfo)(inline action: Ctx ?=> A)(using
      ctx: Ctx
  ): A =
    action(using ctx.enter(pos))

  // checking
  private def check(tm: S.Tm, ty: VTy)(using ctx: Ctx): Tm =
    debug(s"check $tm : ${ctx.pretty(ty)}")
    enter(tm.pos):
      (tm, forceAll(ty)) match
        case (S.Tm.Lam(_, x, ma, b), Val.Pi(x2, t1, t2)) =>
          ma.foreach { sty => unify(ctx.eval(check(sty, Val.Type)), t1) }
          val qt1 = ctx.quote(t1)
          val eb =
            check(b, t2(Var1(ctx.lvl)))(using ctx.bind(x, qt1, t1))
          Tm.Lam(x, qt1, eb)

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
            check(b, ty)(using ctx.define(x, lty, vlty, ev, ctx.eval(ev)))
          Tm.Let(x, lty, ev, eb)

        case (S.Tm.Hole(_, x), _) =>
          err(s"checking _${x.getOrElse("")} against ${ctx.pretty(ty)}")

        case (tm, _) =>
          val (etm, vty) = infer(tm)
          coe(etm, vty, ty)

  // inference
  private def infer(tm: S.Tm)(using ctx: Ctx): (Tm, VTy) =
    debug(s"infer $tm")
    enter(tm.pos):
      tm match
        case S.Tm.Hole(_, _) => err("cannot infer hole")

        case S.Tm.Type(_) => (Tm.Type, Val.Type)

        case S.Tm.Var(_, x) =>
          ctx.lookup(x) match
            case Some(NameInfo(x, ty)) =>
              (Tm.Var(x.toIx(using ctx.lvl)), ty)
            case None =>
              State.getGlobal(x) match
                case Some(GlobalEntry(_, _, _, v, ty)) =>
                  (Tm.Global(x, v), ty)
                case None => err(s"undefined variable $x")

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

        case S.Tm.Pi(_, x, a, b) =>
          val ea = check(a, Val.Type)
          val eb = check(b, Val.Type)(using ctx.bind(x, ea, ctx.eval(ea)))
          (Tm.Pi(x, ea, eb), Val.Type)

        case S.Tm.Lam(_, x, Some(ty), b) =>
          val ety = check(ty, Val.Type)
          val vty = ctx.eval(ety)
          val ctx2 = ctx.bind(x, ety, vty)
          val (eb, vrt) = infer(b)(using ctx2)
          val qrt = ctx2.quote(vrt)
          (
            Tm.Lam(x, ety, eb),
            Val.Pi(x, vty, Clos.Clos(ctx.env, qrt))
          )
        case S.Tm.Lam(_, _, _, _) => err("cannot infer unannotated lambda")

        case S.Tm.App(_, f, a) =>
          val (ef, fty) = infer(f)
          forceAll(fty) match
            case Val.Pi(_, pty, rty) =>
              val ea = check(a, pty)
              (Tm.App(ef, ea), rty(ctx.eval(ea)))
            case _ => err(s"cannot apply expression of type ${ctx.pretty(fty)}")

  // elaboration
  private def elaborate(defn: S.Def): Def =
    debug(s"elaborate $defn")
    given ctx: Ctx = Ctx.empty.enter(defn.pos)
    val x = defn.name
    if State.nameIsDefined(x) then err(s"duplicate name $x")
    val (ev, ety, vty) = defn.ty match
      case None =>
        val (ev, vty) = infer(defn.value)
        (ev, ctx.quote(vty), vty)
      case Some(ty) =>
        val ety = check(ty, Val.Type)
        val vty = ctx.eval(ety)
        val ev = check(defn.value, vty)
        (ev, ety, vty)
    val vv = ctx.eval(ev)
    State.addGlobal(GlobalEntry(x, ev, ety, vv, vty))
    Def(x, ety, ev)

  def elaborate(ds: S.Defs): Defs = ds.map(elaborate)
