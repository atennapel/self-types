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
      case (Spine.Proj(sp1, p1), Spine.Proj(sp2, p2)) if p1 == p2 =>
        unify(top1, sp1, top2, sp2)
      case (Spine.Out(sp1), Spine.Out(sp2)) => unify(top1, sp1, top2, sp2)
      case _                                =>
        err(
          s"spine mismatch ${quote(top1, UnfoldNone)} ~ ${quote(top2, UnfoldNone)}"
        )

  def unify(a: Val, b: Val)(using lvl: Lvl): Unit =
    inline def goClos(a: Clos, b: Clos): Unit =
      val v = Var1(lvl)
      unify(a(v), b(v))(using lvl + 1)
    (a, b) match
      case (Val.Type, Val.Type)                             => ()
      case (Val.Rigid(x, sp1), Val.Rigid(y, sp2)) if x == y =>
        unify(a, sp1, b, sp2)

      case (Val.Pi(_, ty1, b1), Val.Pi(_, ty2, b2)) =>
        unify(ty1, ty2); goClos(b1, b2)
      case (Val.Sigma(_, ty1, b1), Val.Sigma(_, ty2, b2)) =>
        unify(ty1, ty2); goClos(b1, b2)
      case (Val.Self(_, b1), Val.Self(_, b2)) => goClos(b1, b2)
      case (Val.In(_, b1), Val.In(_, b2))     => goClos(b1, b2)

      case (Val.Lam(_, _, b1), Val.Lam(_, _, b2)) => goClos(b1, b2)
      case (Val.Lam(_, _, b), f)                  =>
        val v = Var1(lvl)
        unify(b(v), app(f, v))(using lvl + 1)
      case (f, Val.Lam(_, _, b)) =>
        val v = Var1(lvl)
        unify(app(f, v), b(v))(using lvl + 1)

      case (Val.Pair(f1, s1), Val.Pair(f2, s2)) => unify(f1, f2); unify(s1, s2)
      case (Val.Pair(f, s), t) => unify(f, fst(t)); unify(s, snd(t))
      case (t, Val.Pair(f, s)) => unify(fst(t), f); unify(snd(t), s)

      case (Val.Unfold(h1, sp1, v1), Val.Unfold(h2, sp2, v2)) =>
        try
          if h1 != h2 then err("head mismatch")
          unify(a, sp1, b, sp2)
        catch case _: UnificationError => unify(v1(), v2())
      case (Val.Unfold(_, _, v1), v2) => unify(v1(), v2)
      case (v1, Val.Unfold(_, _, v2)) => unify(v1, v2())

      case _ =>
        err(s"cannot unify ${quote(a, UnfoldNone)} ~ ${quote(b, UnfoldNone)}")
