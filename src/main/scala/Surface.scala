import Common.*
import Common.Bind.*

object Surface:
  final case class Def(pos: PosInfo, name: Name, ty: Option[Ty], value: Tm):
    override def toString: String =
      s"def $name${ty.map(t => s" : $t").getOrElse("")} = $value"

  type Defs = List[Def]

  type Ty = Tm
  enum Tm:
    case Var(posInfo: PosInfo, name: Name)
    case Let(posInfo: PosInfo, name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case Type(posInfo: PosInfo)

    case Pi(posInfo: PosInfo, name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(posInfo: PosInfo, name: Bind, icit: Icit, ty: Option[Ty], body: Ty)
    case App(posInfo: PosInfo, fn: Tm, arg: Tm, icit: Icit)

    case Self(posInfo: PosInfo, name: Name, ty: Option[Ty], body: Ty)
    case In(posInfo: PosInfo, tm: Tm)
    case Out(posInfo: PosInfo, tm: Tm)

    case Hole(posInfo: PosInfo, name: Option[Name])

    def pos: PosInfo = this match
      case Tm.Var(pos, _)          => pos
      case Tm.Let(pos, _, _, _, _) => pos
      case Tm.Type(pos)            => pos
      case Tm.Pi(pos, _, _, _, _)  => pos
      case Tm.Lam(pos, _, _, _, _) => pos
      case Tm.App(pos, _, _, _)    => pos
      case Tm.Self(pos, _, _, _)   => pos
      case Tm.In(pos, _)           => pos
      case Tm.Out(pos, _)          => pos
      case Tm.Hole(pos, _)         => pos

    override def toString: String = this match
      case Var(_, x)           => s"$x"
      case Let(_, x, ty, v, b) =>
        s"(let $x${ty.map(t => s" : $t").getOrElse("")} := $v; $b)"
      case Type(_)                           => "Type"
      case Pi(_, DontBind, Icit.Expl, ty, b) => s"($ty -> $b)"
      case Pi(_, x, i, ty, b)            => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam(_, x, Icit.Expl, None, b) => s"(\\$x => $b)"
      case Lam(_, x, Icit.Impl, None, b) => s"(\\{$x} => $b)"
      case Lam(_, x, i, ty, b)           => s"(\\${i.wrap(s"$x : $ty")} => $b)"
      case App(_, fn, arg, Icit.Expl)    => s"($fn $arg)"
      case App(_, fn, arg, Icit.Impl)    => s"($fn {$arg})"
      case Self(_, x, None, b)           => s"(self $x => $b)"
      case Self(_, x, Some(t), b)        => s"(self ($x : $t) => $b)"
      case In(_, t)                      => s"(in $t)"
      case Out(_, t)                     => s"(out $t)"
      case Hole(_, None)                 => s"_"
      case Hole(_, Some(x))              => s"_$x"
