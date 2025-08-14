import Common.*
import Core.*
import Evaluation.*
import Evaluation.QuoteOption.UnfoldNone

object Unification:
  class UnificationError(val msg: String) extends RuntimeException(msg):
    override def toString: String = s"unification error: $msg"
  private inline def err(msg: String): Nothing =
    throw new UnificationError(msg)

  // partial renaming
  private type LvlMap = Map[Lvl, Lvl]
  private final case class Ren(dom: Lvl, cod: Lvl, ren: LvlMap):
    def lift = Ren(dom + 1, cod + 1, ren + (cod -> dom))

  // inversion
  private def invert(sp: Spine)(using gamma: Lvl): Ren =
    def go(sp: Spine): (Lvl, LvlMap) = sp match
      case Spine.Out(_)        => err(s"out in meta spine")
      case Spine.Empty         => (lvl0, Map.empty)
      case Spine.App(sp, a, i) =>
        val (dom, ren) = go(sp)
        forceAll(a) match
          case Var1(x) if !ren.contains(x) => (dom + 1, ren + (x -> dom))
          case Var1(x) => err(s"duplicate variable '$x in meta spine")
          case t       =>
            err(s"non-var in meta spine: ${quote(t, QuoteOption.UnfoldNone)}")
    val (dom, ren) = go(sp)
    Ren(dom, gamma, ren)

  // renaming
  private def rename(m: MetaId, v: Val)(using ren: Ren): Tm =
    inline def goClos(c: Clos)(using ren: Ren) =
      go(c(Var1(ren.cod)))(using ren.lift)
    def goSp(hd: Tm, sp: Spine)(using ren: Ren): Tm =
      sp match
        case Spine.Empty         => hd
        case Spine.App(sp, a, i) => Tm.App(goSp(hd, sp), go(a), i)
        case Spine.Out(sp)       => Tm.Out(goSp(hd, sp))
    def go(v: Val)(using ren: Ren): Tm =
      forceMetas(v) match
        case Val.Flex(m2, sp) if m == m2 =>
          err(s"occurs check failed for meta ?$m")
        case Val.Flex(m2, sp)                     => goSp(Tm.Meta(m2), sp)
        case Val.Unfold(UnfoldHead.Global(x), sp) => goSp(Tm.Global(x), sp)
        case Val.Rigid(Head.Var(x), sp)           =>
          ren.ren.get(x) match
            case None     => err(s"escaping variable '$x")
            case Some(x2) => goSp(Tm.Var(x2.toIx(using ren.dom)), sp)

        case Val.Lam(x, i, ty, b) => Tm.Lam(x, i, go(ty), goClos(b))
        case Val.Pi(x, i, ty, b)  => Tm.Pi(x, i, go(ty), goClos(b))
        case Val.Self(x, ty, b)   => Tm.Self(x, go(ty), goClos(b))
        case Val.In(tm)           => Tm.In(go(tm))
        case Val.Type             => Tm.Type
    go(v)

  // solving
  private def lams(ty: VTy, b: Tm)(using ren: Ren): Tm =
    val l1 = ren.dom
    def go(l2: Lvl, ty: VTy): Tm =
      if l1 == l2 then b
      else
        forceAll(ty) match
          case t @ Val.Pi(x, i, pt, rt) =>
            val qpt = quote(pt, QuoteOption.UnfoldNone)(using l2)
            val qrt = go(l2 + 1, rt(Var1(l2)))
            Tm.Lam(x, i, qpt, qrt)
          case _ => impossible()
    go(lvl0, ty)

  private def solve(m: MetaId, sp: Spine, rhs: Val)(using gamma: Lvl): Unit =
    given ren: Ren = invert(sp)
    val tm = rename(m, rhs)
    val mty = State.unsolvedMetaType(m)
    val solution = eval(lams(mty, tm))(using Env.Empty)
    State.solveMeta(m, solution)

  // unification
  private def unify(top1: Val, sp1: Spine, top2: Val, sp2: Spine)(using
      lvl: Lvl
  ): Unit =
    (sp1, sp2) match
      case (Spine.Empty, Spine.Empty)                     => ()
      case (Spine.App(sp1, a1, _), Spine.App(sp2, a2, _)) =>
        unify(top1, sp1, top2, sp2); unify(a1, a2)
      case (Spine.Out(sp1), Spine.Out(sp2)) => unify(top1, sp1, top2, sp2)
      case _                                =>
        err(
          s"spine mismatch ${quote(top1, UnfoldNone)} ~ ${quote(top2, UnfoldNone)}"
        )

  def unify(a: Val, b: Val)(using lvl: Lvl): Unit =
    inline def unifyErr() =
      err(s"cannot unify ${quote(a, UnfoldNone)} ~ ${quote(b, UnfoldNone)}")
    inline def goClos(a: Clos, b: Clos): Unit =
      val v = Var1(lvl)
      unify(a(v), b(v))(using lvl + 1)
    def unfold(v: Val): Option[Val] =
      v match
        case Val.Unfold(UnfoldHead.Global(x), sp) => global(x).map(spine(_, sp))
        case _                                    => None
    def unfold2(a: Val, b: Val): Option[(Val, Val)] =
      (unfold(a), unfold(b)) match
        case (None, None)       => None
        case (Some(a), None)    => Some((a, b))
        case (None, Some(b))    => Some((a, b))
        case (Some(a), Some(b)) => Some((a, b))
    inline def unfoldUnify2(err: => Nothing): Unit =
      unfold2(a, b).fold(err)((a, b) => unify(a, b))
    (forceMetas(a), forceMetas(b)) match
      case (Val.Type, Val.Type)                             => ()
      case (Val.Rigid(x, sp1), Val.Rigid(y, sp2)) if x == y =>
        unify(a, sp1, b, sp2)

      case (Val.Pi(_, i1, ty1, b1), Val.Pi(_, i2, ty2, b2)) if i1 == i2 =>
        unify(ty1, ty2); goClos(b1, b2)
      case (Val.Self(_, ty1, b1), Val.Self(_, ty2, b2)) =>
        unify(ty1, ty2); goClos(b1, b2)
      case (Val.In(t1), Val.In(t2)) => unify(t1, t2)

      case (Val.Lam(_, _, _, b1), Val.Lam(_, _, _, b2)) => goClos(b1, b2)
      case (Val.Lam(_, i, _, b), f)                     =>
        val v = Var1(lvl)
        unify(b(v), app(f, v, i))(using lvl + 1)
      case (f, Val.Lam(_, i, _, b)) =>
        val v = Var1(lvl)
        unify(app(f, v, i), b(v))(using lvl + 1)

      case (a @ Val.Flex(m1, sp1), b @ Val.Flex(m2, sp2)) if m1 == m2 =>
        unify(a, sp1, b, sp2)
      case (Val.Flex(m, sp), b) => solve(m, sp, b)
      case (a, Val.Flex(m, sp)) => solve(m, sp, a)

      case (Val.Unfold(h1, sp1), Val.Unfold(h2, sp2)) =>
        try
          if h1 != h2 then err("head mismatch")
          unify(a, sp1, b, sp2)
        catch case err: UnificationError => unfoldUnify2(throw err)
      case (Val.Unfold(_, _), b) => unfoldUnify2(unifyErr())
      case (a, Val.Unfold(_, _)) => unfoldUnify2(unifyErr())

      case _ => unifyErr()
