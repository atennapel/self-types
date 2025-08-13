import Common.*
import Core.*
import Evaluation.*
import Evaluation.QuoteOption.UnfoldNone

object Unification:
  class UnificationError(val msg: String) extends RuntimeException(msg):
    override def toString: String = s"unification error: $msg"
  private inline def err(msg: String): Nothing =
    throw new UnificationError(msg)

  private def unify(top1: Val, sp1: Spine, top2: Val, sp2: Spine)(using
      lvl: Lvl
  ): Unit =
    (sp1, sp2) match
      case (Spine.Empty, Spine.Empty)               => ()
      case (Spine.App(sp1, a1), Spine.App(sp2, a2)) =>
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
    (a, b) match
      case (Val.Type, Val.Type)                             => ()
      case (Val.Rigid(x, sp1), Val.Rigid(y, sp2)) if x == y =>
        unify(a, sp1, b, sp2)

      case (Val.Pi(_, ty1, b1), Val.Pi(_, ty2, b2)) =>
        unify(ty1, ty2); goClos(b1, b2)
      case (Val.Self(_, ty1, b1), Val.Self(_, ty2, b2)) =>
        unify(ty1, ty2); goClos(b1, b2)
      case (Val.In(t1), Val.In(t2)) => unify(t1, t2)

      case (Val.Lam(_, _, b1), Val.Lam(_, _, b2)) => goClos(b1, b2)
      case (Val.Lam(_, _, b), f)                  =>
        val v = Var1(lvl)
        unify(b(v), app(f, v))(using lvl + 1)
      case (f, Val.Lam(_, _, b)) =>
        val v = Var1(lvl)
        unify(app(f, v), b(v))(using lvl + 1)

      case (Val.Unfold(h1, sp1), Val.Unfold(h2, sp2)) =>
        try
          if h1 != h2 then err("head mismatch")
          unify(a, sp1, b, sp2)
        catch case err: UnificationError => unfoldUnify2(throw err)
      case (Val.Unfold(_, _), b) => unfoldUnify2(unifyErr())
      case (a, Val.Unfold(_, _)) => unfoldUnify2(unifyErr())

      case _ => unifyErr()
