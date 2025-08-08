import Common.*

import scala.annotation.tailrec

object Core:
  final case class Def(name: Name, ty: Ty, value: Tm):
    override def toString: String = s"def $name : $ty = $value"

  type Defs = List[Def]

  enum ProjType:
    case Fst
    case Snd
    override def toString: String = this match
      case Fst => "fst"
      case snd => "snd"

  type Ty = Tm
  enum Tm:
    case Var(ix: Ix)
    case Global(name: Name, value: Val)
    case Let(name: Name, ty: Ty, value: Tm, body: Tm)

    case Type

    case Pi(name: Bind, ty: Ty, body: Ty)
    case Lam(name: Bind, ty: Ty, body: Tm)
    case App(fn: Tm, arg: Tm)

    case Sigma(name: Bind, ty: Ty, body: Ty)
    case Proj(proj: ProjType, scrut: Tm)
    case Pair(fst: Tm, snd: Tm)

    case Self(name: Name, body: Ty)
    case In(name: Name, body: Tm)
    case Out(tm: Tm)

    case Wk(tm: Tm)

    def wkN(n: Int) =
      @tailrec
      def go(n: Int, t: Tm): Tm = if n == 0 then t else go(n - 1, Wk(t))
      go(n, this)

    override def toString: String = this match
      case Var(ix)          => s"'$ix"
      case Global(x, _)     => s"$x"
      case Let(x, ty, v, b) => s"(let $x : $ty = $v; $b)"
      case Type             => s"Type"
      case Pi(x, ty, b)     => s"(($x : $ty) -> $b)"
      case Lam(x, ty, b)    => s"(\\($x : $ty) => $b)"
      case App(fn, arg)     => s"($fn $arg)"
      case Sigma(x, ty, b)  => s"(($x : $ty) ** $b)"
      case Proj(p, t)       => s"($p $t)"
      case Pair(f, s)       => s"($f, $s)"
      case Self(x, b)       => s"(self $x => $b)"
      case In(x, b)         => s"(in $x => $b)"
      case Out(t)           => s"(out $t)"
      case Wk(tm)           => s"Wk11($tm)"

  enum Locals:
    case Empty
    case Def(locs: Locals, ty: Ty, value: Tm)
    case Bind(locs: Locals, ty: Ty)

  // values
  enum Clos:
    case Clos(env: Env, tm: Tm)
    case Fun(fn: Val => Val)
  object Clos:
    def apply(tm: Tm)(using env: Env): Clos = Clos(env, tm)

  enum Env:
    case Empty
    case Ext(env: Env, value: Val)

    def size: Int =
      @tailrec
      def go(acc: Int, e: Env): Int = e match
        case Empty     => acc
        case Ext(e, _) => go(acc + 1, e)

      go(0, this)

    inline def wk: Env = this match
      case Ext(env, _) => env
      case _           => impossible()

    inline def tail: Env = this match
      case Ext(env, _) => env
      case _           => impossible()

  object Env:
    def apply(vs: List[Val]): Env = vs.foldLeft(Env.Empty)(Ext.apply)

  enum Spine:
    case Empty
    case App(sp: Spine, arg: Val)
    case Proj(sp: Spine, proj: ProjType)
    case Out(sp: Spine)

    def size: Int =
      @tailrec
      def go(acc: Int, sp: Spine): Int = sp match
        case Empty       => acc
        case App(sp, _)  => go(acc + 1, sp)
        case Proj(sp, _) => go(acc + 1, sp)
        case Out(sp)     => go(acc + 1, sp)
      go(0, this)

    def reverse: Spine =
      @tailrec
      def go(acc: Spine, sp: Spine): Spine = sp match
        case Empty       => acc
        case App(sp, v)  => go(App(acc, v), sp)
        case Proj(sp, p) => go(Proj(acc, p), sp)
        case Out(sp)     => go(Out(acc), sp)
      go(Empty, this)

    def isEmpty: Boolean = this match
      case Empty => true
      case _     => false

  enum Head:
    case Var(lvl: Lvl)

  enum UnfoldHead:
    case Global(name: Name, value: Val)

  type VTy = Val
  enum Val:
    case Rigid(head: Head, spine: Spine)
    case Unfold(head: UnfoldHead, spine: Spine, value: () => Val)

    case Pi(name: Bind, ty: VTy, body: Clos)
    case Lam(name: Bind, ty: VTy, body: Clos)

    case Sigma(name: Bind, ty: VTy, body: Clos)
    case Pair(fst: Val, snd: Val)

    case Self(name: Name, body: Clos)
    case In(name: Name, body: Clos)

    case Type

  private inline def bind(x: String): Bind =
    if x == "_" then Bind.DontBind else Bind.DoBind(Name(x))
  def vlam(x: String, ty: VTy, b: Val => Val): Val =
    Val.Lam(bind(x), ty, Clos.Fun(b))
  def vfun(ty: VTy, rt: VTy): Val = Val.Pi(Bind.DontBind, ty, Clos.Fun(_ => rt))
  def vpi(x: String, ty: VTy, b: Val => Val): Val =
    Val.Pi(bind(x), ty, Clos.Fun(b))

  object Var1:
    def apply(lvl: Lvl): Val = Val.Rigid(Head.Var(lvl), Spine.Empty)
    def unapply(value: Val): Option[Lvl] = value match
      case Val.Rigid(Head.Var(hd), Spine.Empty) => Some(hd)
      case _                                    => None
