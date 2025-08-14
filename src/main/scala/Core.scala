import Common.*

import scala.annotation.tailrec

object Core:
  final case class Def(name: Name, ty: Ty, value: Tm):
    override def toString: String = s"def $name : $ty = $value"

  type Defs = List[Def]

  type Ty = Tm
  enum Tm:
    case Var(ix: Ix)
    case Global(name: Name)
    case Let(name: Name, ty: Ty, value: Tm, body: Tm)

    case Type

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, icit: Icit, ty: Ty, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)

    case Self(name: Name, ty: Ty, body: Ty)
    case In(tm: Tm)
    case Out(tm: Tm)

    case Wk(tm: Tm)
    case Meta(id: MetaId)
    case AppPruning(id: MetaId, pruning: Pruning)

    def wkN(n: Int) =
      @tailrec
      def go(n: Int, t: Tm): Tm = if n == 0 then t else go(n - 1, Wk(t))
      go(n, this)

    override def toString: String = this match
      case Var(ix)                 => s"'$ix"
      case Global(x)               => s"$x"
      case Let(x, ty, v, b)        => s"(let $x : $ty = $v; $b)"
      case Type                    => s"Type"
      case Pi(x, i, ty, b)         => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam(x, i, ty, b)        => s"(\\${i.wrap(s"$x : $ty")} => $b)"
      case App(fn, arg, Icit.Expl) => s"($fn $arg)"
      case App(fn, arg, Icit.Impl) => s"($fn {$arg})"
      case Self(x, ty, b)          => s"(self ($x : $ty) => $b)"
      case In(t)                   => s"(in $t)"
      case Out(t)                  => s"(out $t)"
      case Wk(tm)                  => s"Wk11($tm)"
      case Meta(m)                 => s"?$m"
      case AppPruning(m, _)        => s"?$m"

  enum Locals:
    case Empty
    case Def(locs: Locals, ty: Ty, value: Tm)
    case Bind(locs: Locals, ty: Ty, icit: Icit)

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
    case App(sp: Spine, arg: Val, icit: Icit)
    case Out(sp: Spine)

    def size: Int =
      @tailrec
      def go(acc: Int, sp: Spine): Int = sp match
        case Empty         => acc
        case App(sp, _, _) => go(acc + 1, sp)
        case Out(sp)       => go(acc + 1, sp)
      go(0, this)

    def reverse: Spine =
      @tailrec
      def go(acc: Spine, sp: Spine): Spine = sp match
        case Empty         => acc
        case App(sp, v, i) => go(App(acc, v, i), sp)
        case Out(sp)       => go(Out(acc), sp)
      go(Empty, this)

    def isEmpty: Boolean = this match
      case Empty => true
      case _     => false

  enum Head:
    case Var(lvl: Lvl)

  enum UnfoldHead:
    case Global(name: Name)

  type VTy = Val
  enum Val:
    case Rigid(head: Head, spine: Spine)
    case Flex(id: MetaId, spine: Spine)
    case Unfold(head: UnfoldHead, spine: Spine)

    case Pi(name: Bind, icit: Icit, ty: VTy, body: Clos)
    case Lam(name: Bind, icit: Icit, ty: VTy, body: Clos)

    case Self(name: Name, ty: VTy, body: Clos)
    case In(tm: Val)

    case Type

  private inline def bind(x: String): Bind =
    if x == "_" then Bind.DontBind else Bind.DoBind(Name(x))
  def vlam(x: String, ty: VTy, b: Val => Val): Val =
    Val.Lam(bind(x), Icit.Expl, ty, Clos.Fun(b))
  def vfun(ty: VTy, rt: VTy): Val =
    Val.Pi(Bind.DontBind, Icit.Expl, ty, Clos.Fun(_ => rt))
  def vpi(x: String, ty: VTy, b: Val => Val): Val =
    Val.Pi(bind(x), Icit.Expl, ty, Clos.Fun(b))

  object Var1:
    def apply(lvl: Lvl): Val = Val.Rigid(Head.Var(lvl), Spine.Empty)
    def unapply(value: Val): Option[Lvl] = value match
      case Val.Rigid(Head.Var(hd), Spine.Empty) => Some(hd)
      case _                                    => None
