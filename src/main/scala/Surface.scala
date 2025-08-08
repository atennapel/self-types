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

    case Pi(posInfo: PosInfo, name: Bind, ty: Ty, body: Ty)
    case Lam(posInfo: PosInfo, name: Bind, ty: Option[Ty], body: Ty)
    case App(posInfo: PosInfo, fn: Tm, arg: Tm)

    case Hole(posInfo: PosInfo, name: Option[Name])

    def pos: PosInfo = this match
      case Tm.Var(pos, _)          => pos
      case Tm.Let(pos, _, _, _, _) => pos
      case Tm.Type(pos)            => pos
      case Tm.Pi(pos, _, _, _)     => pos
      case Tm.Lam(pos, _, _, _)    => pos
      case Tm.App(pos, _, _)       => pos
      case Tm.Hole(pos, _)         => pos

    override def toString: String = this match
      case Var(_, x)           => s"$x"
      case Let(_, x, ty, v, b) =>
        s"(let $x${ty.map(t => s" : $t").getOrElse("")} := $v; $b)"
      case Type(_)                => "Type"
      case Pi(_, DontBind, ty, b) => s"($ty -> $b)"
      case Pi(_, x, ty, b)        => s"(($x : $ty) -> $b)"
      case Lam(_, x, None, b)     => s"(\\$x => $b)"
      case Lam(_, x, ty, b)       => s"(\\($x : $ty) => $b)"
      case App(_, fn, arg)        => s"($fn $arg)"
      case Hole(_, None)          => s"_"
      case Hole(_, Some(x))       => s"_$x"
