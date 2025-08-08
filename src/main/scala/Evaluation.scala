import Common.*
import Core.*
import Core.Spine.Proj

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
    case Val.Lam(x, _, b)     => b(a)
    case Val.Rigid(h, sp)     => Val.Rigid(h, Spine.App(sp, a))
    case Val.Unfold(h, sp, v) =>
      Val.Unfold(h, Spine.App(sp, a), () => app(v(), a))
    case _ => impossible()

  def proj(p: ProjType, v: Val): Val = v match
    case Val.Pair(fst, snd) =>
      p match
        case ProjType.Fst => fst
        case ProjType.Snd => snd
    case Val.Rigid(h, sp)     => Val.Rigid(h, Spine.Proj(sp, p))
    case Val.Unfold(h, sp, v) =>
      Val.Unfold(h, Spine.Proj(sp, p), () => proj(p, v()))
    case _ => impossible()
  def fst(v: Val): Val = proj(ProjType.Fst, v)
  def snd(v: Val): Val = proj(ProjType.Snd, v)

  def out(v: Val): Val = v match
    case Val.In(_, b)         => b(v)
    case Val.Rigid(h, sp)     => Val.Rigid(h, Spine.Out(sp))
    case Val.Unfold(h, sp, v) =>
      Val.Unfold(h, Spine.Out(sp), () => out(v()))
    case _ => impossible()

  def spine(v: Val, sp: Spine): Val = sp match
    case Spine.Empty       => v
    case Spine.App(sp, a)  => app(spine(v, sp), a)
    case Spine.Proj(sp, p) => proj(p, spine(v, sp))
    case Spine.Out(sp)     => out(spine(v, sp))

  def eval(t: Tm)(using env: Env): Val =
    t match
      case Tm.Var(ix)      => lookup(ix)
      case Tm.Global(x, v) =>
        Val.Unfold(UnfoldHead.Global(x, v), Spine.Empty, () => v)
      case Tm.Let(_, _, v, b) => eval(b)(using Env.Ext(env, eval(v)))
      case Tm.Type            => Val.Type
      case Tm.Pi(x, ty, b)    => Val.Pi(x, eval(ty), Clos(b))
      case Tm.Lam(x, ty, b)   => Val.Lam(x, eval(ty), Clos(b))
      case Tm.App(f, a)       => app(eval(f), eval(a))
      case Tm.Sigma(x, ty, b) => Val.Sigma(x, eval(ty), Clos(b))
      case Tm.Proj(p, t)      => proj(p, eval(t))
      case Tm.Pair(f, s)      => Val.Pair(eval(f), eval(s))
      case Tm.Self(x, b)      => Val.Self(x, Clos(b))
      case Tm.In(x, b)        => Val.In(x, Clos(b))
      case Tm.Out(t)          => out(eval(t))
      case Tm.Wk(tm)          => eval(tm)(using env.wk)

  // forcing
  @tailrec
  def forceAll(v: Val): Val = v match
    case Val.Unfold(_, _, v) => forceAll(v())
    case v                   => v

  // quoting
  private def quote(h: Tm, sp: Spine, q: QuoteOption)(using lvl: Lvl): Tm =
    sp match
      case Spine.Empty       => h
      case Spine.App(sp, v)  => Tm.App(quote(h, sp, q), quote(v, q))
      case Spine.Proj(sp, p) => Tm.Proj(p, quote(h, sp, q))
      case Spine.Out(sp)     => Tm.Out(quote(h, sp, q))

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
      case Val.Unfold(UnfoldHead.Global(x, v), sp, _) =>
        goSp(Tm.Global(x, v), sp)
      case Val.Pi(x, ty, b)    => Tm.Pi(x, go(ty), goClos(b))
      case Val.Lam(x, ty, b)   => Tm.Lam(x, go(ty), goClos(b))
      case Val.Sigma(x, ty, b) => Tm.Sigma(x, go(ty), goClos(b))
      case Val.Pair(f, s)      => Tm.Pair(go(f), go(s))
      case Val.Self(x, b)      => Tm.Self(x, goClos(b))
      case Val.In(x, b)        => Tm.In(x, goClos(b))

  def nf(tm: Tm, q: QuoteOption = QuoteOption.UnfoldAll): Tm =
    quote(eval(tm)(using Env.Empty), q)(using lvl0)
