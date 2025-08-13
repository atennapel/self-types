import Common.*
import Core.*

import scala.annotation.tailrec

object Pretty:
  private def prettyApp(tm: Tm)(using ns: List[Bind]): String = tm match
    case Tm.App(f, a)   => s"${prettyApp(f)} ${prettyParen(a)}"
    case tm @ Tm.Out(_) => pretty(tm)
    case f              => prettyParen(f)

  private def prettyPi(tm: Ty)(using ns: List[Bind]): String = tm match
    case Tm.Pi(Bind.DontBind, t, b) =>
      s"${prettyParen(t, true)} -> ${prettyPi(b)(using Bind.DontBind :: ns)}"
    case Tm.Pi(bx @ Bind.DoBind(x), t, b) =>
      s"($x : ${pretty(t)}) -> ${prettyPi(b)(using bx :: ns)}"
    case rest => pretty(rest)

  private def prettyLam(tm: Tm)(using ns: List[Bind]): String =
    def go(tm: Tm, first: Boolean = false)(using ns: List[Bind]): String =
      tm match
        case Tm.Lam(x, _, b) =>
          s"${if first then "" else " "}$x${go(b)(using x :: ns)}"
        case rest => s" => ${pretty(rest)}"
    s"\\${go(tm, true)}"

  @tailrec
  def prettyParen(tm: Tm, app: Boolean = false)(using
      ns: List[Bind]
  ): String =
    tm match
      case Tm.Var(_)           => pretty(tm)
      case Tm.Global(_)        => pretty(tm)
      case Tm.App(_, _) if app => pretty(tm)
      case Tm.Out(tm) if app   => pretty(tm)
      case Tm.Type             => pretty(tm)
      case Tm.Wk(tm)           => prettyParen(tm, app)(using ns.tail)
      case _                   => s"(${pretty(tm)})"

  private def prettyLift(x: Bind, tm: Tm)(using ns: List[Bind]): String =
    pretty(tm)(using x :: ns)

  def pretty(tm: Tm)(using ns: List[Bind]): String =
    tm match
      case Tm.Var(ix) =>
        ns(ix.expose) match
          case Bind.DontBind => s"_@${ns.size - ix.expose - 1}"
          case Bind.DoBind(x) if ns.take(ix.expose).contains(Bind.DoBind(x)) =>
            s"$x@${ns.size - ix.expose - 1}"
          case Bind.DoBind(x) => s"$x"
      case Tm.Global(x)       => s"$x"
      case Tm.Let(x, t, v, b) =>
        s"let $x : ${pretty(t)} = ${pretty(v)}; ${prettyLift(x.toBind, b)}"

      case Tm.Type => "Type"

      case Tm.Pi(_, _, _)  => prettyPi(tm)
      case Tm.Lam(_, _, _) => prettyLam(tm)
      case Tm.App(_, _)    => prettyApp(tm)

      case Tm.Self(x, t, b) =>
        s"self ($x : ${pretty(t)}) => ${prettyLift(x.toBind, b)}"
      case Tm.In(t)  => s"in ${prettyParen(t)}"
      case Tm.Out(t) => s"out ${prettyParen(t)}"

      case Tm.Wk(tm) => pretty(tm)(using ns.tail)
