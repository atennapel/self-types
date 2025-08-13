import Common.*
import Core.*

import scala.annotation.tailrec

object Evaluation:
  enum QuoteOption:
    case UnfoldAll
    case UnfoldNone

  extension (c: Clos)
    inline def apply(v: Val): Val = c match
      case Clos.Clos(env, tm) => eval(tm)(using Env.Ext(env, v))
      case Clos.Fun(f)        => f(v)

  @tailrec
  def lookup(ix: Ix)(using e: Env): Val =
    e match
      case Env.Ext(_, v) if ix.expose == 0 => v
      case Env.Ext(env, _)                 => lookup(ix - 1)(using env)
      case Env.Empty                       => impossible()

  def app(f: Val, a: Val): Val = f match
    case Val.Lam(x, _, b)  => b(a)
    case Val.Rigid(h, sp)  => Val.Rigid(h, Spine.App(sp, a))
    case Val.Unfold(h, sp) => Val.Unfold(h, Spine.App(sp, a))
    case _                 => impossible()

  def out(v: Val): Val = v match
    case Val.In(b)         => b
    case Val.Rigid(h, sp)  => Val.Rigid(h, Spine.Out(sp))
    case Val.Unfold(h, sp) => Val.Unfold(h, Spine.Out(sp))
    case _                 => impossible()

  def spine(v: Val, sp: Spine): Val = sp match
    case Spine.Empty      => v
    case Spine.App(sp, a) => app(spine(v, sp), a)
    case Spine.Out(sp)    => out(spine(v, sp))

  def eval(t: Tm)(using env: Env): Val =
    t match
      case Tm.Var(ix)         => lookup(ix)
      case Tm.Global(x)       => Val.Unfold(UnfoldHead.Global(x), Spine.Empty)
      case Tm.Let(_, _, v, b) => eval(b)(using Env.Ext(env, eval(v)))
      case Tm.Type            => Val.Type
      case Tm.Pi(x, ty, b)    => Val.Pi(x, eval(ty), Clos(b))
      case Tm.Lam(x, ty, b)   => Val.Lam(x, eval(ty), Clos(b))
      case Tm.App(f, a)       => app(eval(f), eval(a))
      case Tm.Self(x, ty, b)  => Val.Self(x, eval(ty), Clos(b))
      case Tm.In(tm)          => Val.In(eval(tm))
      case Tm.Out(t)          => out(eval(t))
      case Tm.Wk(tm)          => eval(tm)(using env.wk)

  // forcing
  def global(x: Name): Option[Val] =
    State.getGlobal(x) match
      case Some(State.GlobalEntry(_, _, _, Some((_, v)))) => Some(v)
      case _                                              => None

  @tailrec
  def forceAll(v: Val): Val = v match
    case Val.Unfold(UnfoldHead.Global(x), sp) =>
      global(x) match
        case None    => v
        case Some(v) => forceAll(spine(v, sp))
    case v => v

  // quoting
  private def quote(h: Tm, sp: Spine, q: QuoteOption)(using lvl: Lvl): Tm =
    sp match
      case Spine.Empty      => h
      case Spine.App(sp, v) => Tm.App(quote(h, sp, q), quote(v, q))
      case Spine.Out(sp)    => Tm.Out(quote(h, sp, q))

  def quote(v: Val, q: QuoteOption)(using lvl: Lvl): Tm =
    inline def go(v: Val): Tm = quote(v, q)
    inline def goSp(h: Tm, sp: Spine): Tm = quote(h, sp, q)
    inline def goClos(c: Clos): Tm = quote(c(Var1(lvl)), q)(using lvl + 1)
    inline def force(v: Val): Val = q match
      case QuoteOption.UnfoldAll  => forceAll(v)
      case QuoteOption.UnfoldNone => v
    force(v) match
      case Val.Type          => Tm.Type
      case Val.Rigid(hd, sp) =>
        hd match
          case Head.Var(lvl) => goSp(Tm.Var(lvl.toIx), sp)
      case Val.Unfold(UnfoldHead.Global(x), sp) => goSp(Tm.Global(x), sp)
      case Val.Pi(x, ty, b)                     => Tm.Pi(x, go(ty), goClos(b))
      case Val.Lam(x, ty, b)                    => Tm.Lam(x, go(ty), goClos(b))
      case Val.Self(x, ty, b)                   => Tm.Self(x, go(ty), goClos(b))
      case Val.In(tm)                           => Tm.In(go(tm))

  def nf(tm: Tm, q: QuoteOption = QuoteOption.UnfoldAll): Tm =
    quote(eval(tm)(using Env.Empty), q)(using lvl0)
