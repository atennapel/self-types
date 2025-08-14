import Common.*
import Core.*

import scala.annotation.tailrec

object Evaluation:
  enum QuoteOption:
    case UnfoldAll
    case UnfoldMetas
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

  def app(f: Val, a: Val, i: Icit): Val = f match
    case Val.Lam(x, _, _, b) => b(a)
    case Val.Rigid(h, sp)    => Val.Rigid(h, Spine.App(sp, a, i))
    case Val.Flex(h, sp)     => Val.Flex(h, Spine.App(sp, a, i))
    case Val.Unfold(h, sp)   => Val.Unfold(h, Spine.App(sp, a, i))
    case _                   => impossible()

  def out(v: Val): Val = v match
    case Val.In(b)         => b
    case Val.Rigid(h, sp)  => Val.Rigid(h, Spine.Out(sp))
    case Val.Flex(h, sp)   => Val.Flex(h, Spine.Out(sp))
    case Val.Unfold(h, sp) => Val.Unfold(h, Spine.Out(sp))
    case _                 => impossible()

  def spine(v: Val, sp: Spine): Val = sp match
    case Spine.Empty         => v
    case Spine.App(sp, a, i) => app(spine(v, sp), a, i)
    case Spine.Out(sp)       => out(spine(v, sp))

  def meta(id: MetaId): Val = State.getMeta(id) match
    case State.MetaEntry.Unsolved(_)  => Val.Flex(id, Spine.Empty)
    case State.MetaEntry.Solved(v, _) => v

  def appPruning(v: Val, p: Pruning)(using env: Env): Val =
    (env, p) match
      case (Env.Empty, Nil)                      => v
      case (Env.Ext(env, _), Prune.Skip :: p)    => appPruning(v, p)(using env)
      case (Env.Ext(env, u), Prune.Bind(i) :: p) =>
        app(appPruning(v, p)(using env), u, i)
      case _ => impossible()

  def eval(t: Tm)(using env: Env): Val =
    t match
      case Tm.Var(ix)          => lookup(ix)
      case Tm.Global(x)        => Val.Unfold(UnfoldHead.Global(x), Spine.Empty)
      case Tm.Let(_, _, v, b)  => eval(b)(using Env.Ext(env, eval(v)))
      case Tm.Type             => Val.Type
      case Tm.Pi(x, i, ty, b)  => Val.Pi(x, i, eval(ty), Clos(b))
      case Tm.Lam(x, i, ty, b) => Val.Lam(x, i, eval(ty), Clos(b))
      case Tm.App(f, a, i)     => app(eval(f), eval(a), i)
      case Tm.Self(x, ty, b)   => Val.Self(x, eval(ty), Clos(b))
      case Tm.In(tm)           => Val.In(eval(tm))
      case Tm.Out(t)           => out(eval(t))
      case Tm.Wk(tm)           => eval(tm)(using env.wk)
      case Tm.Meta(m)          => meta(m)
      case Tm.AppPruning(m, p) => appPruning(meta(m), p)

  // forcing
  def global(x: Name): Option[Val] =
    State.getGlobal(x) match
      case Some(State.GlobalEntry(_, _, _, Some((_, v)))) => Some(v)
      case _                                              => None

  @tailrec
  def forceAll(v: Val): Val = v match
    case Val.Flex(m, sp) =>
      State.getMeta(m) match
        case State.MetaEntry.Unsolved(_)  => v
        case State.MetaEntry.Solved(v, _) => forceAll(spine(v, sp))
    case Val.Unfold(UnfoldHead.Global(x), sp) =>
      global(x) match
        case None    => v
        case Some(v) => forceAll(spine(v, sp))
    case v => v

  @tailrec
  def forceMetas(v: Val): Val = v match
    case Val.Flex(m, sp) =>
      State.getMeta(m) match
        case State.MetaEntry.Unsolved(_)  => v
        case State.MetaEntry.Solved(v, _) => forceMetas(spine(v, sp))
    case v => v

  // quoting
  private def quote(h: Tm, sp: Spine, q: QuoteOption)(using lvl: Lvl): Tm =
    sp match
      case Spine.Empty         => h
      case Spine.App(sp, v, i) => Tm.App(quote(h, sp, q), quote(v, q), i)
      case Spine.Out(sp)       => Tm.Out(quote(h, sp, q))

  def quote(v: Val, q: QuoteOption)(using lvl: Lvl): Tm =
    inline def go(v: Val): Tm = quote(v, q)
    inline def goSp(h: Tm, sp: Spine): Tm = quote(h, sp, q)
    inline def goClos(c: Clos): Tm = quote(c(Var1(lvl)), q)(using lvl + 1)
    inline def force(v: Val): Val = q match
      case QuoteOption.UnfoldAll   => forceAll(v)
      case QuoteOption.UnfoldMetas => forceMetas(v)
      case QuoteOption.UnfoldNone  => v
    force(v) match
      case Val.Type          => Tm.Type
      case Val.Rigid(hd, sp) =>
        hd match
          case Head.Var(lvl) => goSp(Tm.Var(lvl.toIx), sp)
      case Val.Flex(m, sp)                      => goSp(Tm.Meta(m), sp)
      case Val.Unfold(UnfoldHead.Global(x), sp) => goSp(Tm.Global(x), sp)
      case Val.Pi(x, i, ty, b)  => Tm.Pi(x, i, go(ty), goClos(b))
      case Val.Lam(x, i, ty, b) => Tm.Lam(x, i, go(ty), goClos(b))
      case Val.Self(x, ty, b)   => Tm.Self(x, go(ty), goClos(b))
      case Val.In(tm)           => Tm.In(go(tm))

  def nf(tm: Tm, q: QuoteOption = QuoteOption.UnfoldAll): Tm =
    quote(eval(tm)(using Env.Empty), q)(using lvl0)
