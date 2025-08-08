import Common.*
import Core.*
import Evaluation.QuoteOption

final case class Ctx(
    lvl: Lvl,
    env: Env,
    locals: Locals,
    binds: List[Bind],
    names: Ctx.NameMap,
    pos: PosInfo
):
  import Ctx.*

  private def addName(x: Bind, info: NameInfo): NameMap =
    x match
      case Bind.DontBind  => names
      case Bind.DoBind(x) => names + (x -> info)

  def typeOfLvl(x: Lvl): Ty =
    def go(ls: Locals, i: Int): Ty = ls match
      case Locals.Empty                      => impossible()
      case Locals.Def(locs, ty, _) if i == 0 => ty
      case Locals.Bind(locs, ty) if i == 0   => ty
      case Locals.Def(ls, _, _)              => go(ls, i - 1)
      case Locals.Bind(ls, _)                => go(ls, i - 1)
    go(locals, x.toIx(using lvl).expose)

  def bindOfLvl(x: Lvl): Bind = binds.reverse(x.expose)

  def enter(pos: PosInfo): Ctx = copy(pos = pos)

  def lookup(x: Name): Option[NameInfo] = names.get(x)

  def bind(x: Bind, ty: Ty, vty: VTy): Ctx =
    Ctx(
      lvl + 1,
      Env.Ext(env, Var1(lvl)),
      Locals.Bind(locals, ty),
      x :: binds,
      addName(x, NameInfo(lvl, vty)),
      pos
    )

  def insert(x: Bind, ty: Ty): Ctx =
    Ctx(
      lvl + 1,
      Env.Ext(env, Var1(lvl)),
      Locals.Bind(locals, ty),
      x :: binds,
      names,
      pos
    )

  def define(x: Name, ty: Ty, vty: VTy, v: Tm, vv: Val): Ctx =
    Ctx(
      lvl + 1,
      Env.Ext(env, vv),
      Locals.Def(locals, ty, v),
      Bind.DoBind(x) :: binds,
      names + (x -> NameInfo(lvl, vty)),
      pos
    )

  def defineInsert(x: Name, ty: Ty, v: Tm, vv: Val): Ctx =
    Ctx(
      lvl + 1,
      Env.Ext(env, vv),
      Locals.Def(locals, ty, v),
      Bind.DoBind(x) :: binds,
      names,
      pos
    )

  def quote(v: Val, q: QuoteOption = QuoteOption.UnfoldNone): Tm =
    Evaluation.quote(v, q)(using lvl)
  def eval(t: Tm): Val = Evaluation.eval(t)(using env)

  def pretty(v: Val, q: QuoteOption = QuoteOption.UnfoldNone): String =
    Pretty.pretty(Evaluation.quote(v, q)(using lvl))(using binds)
  def pretty(v: Tm): String = Pretty.pretty(v)(using binds)
  def prettyParen1(v: Tm): String = Pretty.prettyParen(v)(using binds)

object Ctx:
  def empty: Ctx =
    Ctx(lvl0, Env.Empty, Locals.Empty, Nil, Map.empty, PosInfo.start)

  final case class NameInfo(lvl: Lvl, ty: VTy)

  private type NameMap = Map[Name, NameInfo]
