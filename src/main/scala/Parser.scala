import Common.*
import Debug.debug
import Surface.*

import scala.collection.mutable

object Parser:
  // tokenization
  private enum Token:
    case Identifier(name: String, posInfo: PosInfo)
    case Keyword(name: String, posInfo: PosInfo)
    case Symbol(name: String, posInfo: PosInfo)
    case Number(value: Int, posInfo: PosInfo)

    override def toString: String = this match
      case Identifier(x, _) => x
      case Keyword(x, _)    => x
      case Symbol(x, _)     => x
      case Number(x, _)     => x.toString

    def pos: PosInfo = this match
      case Token.Identifier(_, pos) => pos
      case Token.Keyword(_, pos)    => pos
      case Token.Symbol(_, pos)     => pos
      case Token.Number(_, pos)     => pos

  private val keywords: Set[String] =
    Set("def", "let", "Type", "fst", "snd", "with", "self", "in", "out")
  private val symbols1: Set[Char] = Set(':', ';', '=', '\\', '(', ')', ',')
  private val symbols2: Map[Char, Set[Char]] =
    Map('-' -> Set('>'), '=' -> Set('>'), '*' -> Set('*'))

  private def tokenize(s: String): Array[Token] =
    var i = 0
    val acc = mutable.ArrayBuffer.empty[Char]
    var inComment = false
    val tokens = mutable.ArrayBuffer.empty[Token]
    var col = 1
    var line = 1

    inline def pos: PosInfo = PosInfo(line, col)

    inline def handleAcc(): Unit =
      if acc.nonEmpty then
        tokens += tokenizeAcc(acc.mkString, pos)
        acc.clear()

    while i < s.length do
      val c = s(i)
      val next = if i + 1 < s.length then s(i + 1) else '\u0000'
      if inComment then
        if c == '\n' then inComment = false
      else if c == '-' && next == '-' then
        handleAcc()
        inComment = true
        i += 1
      else if symbol2Match(c, next) then
        handleAcc()
        tokens += Token.Symbol(s"$c$next", pos.subCol(1))
        i += 1
      else if symbols1.contains(c) then
        handleAcc()
        tokens += Token.Symbol(c.toString, pos)
      else if c.isWhitespace then handleAcc()
      else acc += c
      i += 1
      if c == '\n' then
        col = 1
        line += 1
      else col += 1
    handleAcc()
    tokens.toArray

  private def symbol2Match(a: Char, b: Char): Boolean =
    symbols2.get(a) match
      case None         => false
      case Some(follow) => follow.contains(b)

  private def tokenizeAcc(s: String, posAfter: PosInfo): Token =
    val pos = posAfter.subCol(s.length)
    s.toIntOption match
      case Some(n)                      => Token.Number(n, pos)
      case None if keywords.contains(s) => Token.Keyword(s, pos)
      case None if s.length == 1 && symbols1.contains(s(0)) =>
        Token.Symbol(s, pos)
      case None if s.length == 2 && symbol2Match(s(0), s(1)) =>
        Token.Symbol(s, pos)
      case None => Token.Identifier(s, pos)

  // parsing
  private final case class Ctx(
      var pos: PosInfo,
      var tokens: mutable.Buffer[Token]
  ):
    override def toString: String = s"Ctx($pos, [${tokens.mkString(" ")}])"

  class ParseError(val pos: PosInfo, val msg: String)
      extends RuntimeException(msg):
    override def toString: String = s"parse error at $pos: $msg"
  private inline def err(msg: String)(using ctx: Ctx): Nothing =
    throw new ParseError(ctx.pos, msg)

  def parse(s: String): Defs =
    val tokens = tokenize(s)
    val buffer = tokens.toBuffer
    given ctx: Ctx = Ctx(PosInfo.start, buffer)
    val result = list(parseDef)
    if ctx.tokens.nonEmpty then err(s"unparsed input at end of file")
    result

  // definitions
  private type DefParam = (PosInfo, List[Bind], Option[Ty])
  private def hole(using ctx: Ctx) = Tm.Hole(ctx.pos, None)

  private def parseDef()(using ctx: Ctx): Option[Def] =
    if tryKeyword("def") then
      val (pos, x, ty, body) = parseDefPart()
      Some(Def(pos, x, ty, body))
    else None

  private def parseDefPart()(using
      ctx: Ctx
  ): (PosInfo, Name, Option[Tm], Tm) =
    val pos = ctx.pos
    val x = name()
    val ps = parseParams()
    val prety = if trySymbol(":") then Some(parseExpr()) else None
    symbol("=")
    val prebody = parseExpr()
    val (ty, body) = prety match
      case None =>
        val body = ps.foldRight(prebody) { case ((p, xs, ty), b) =>
          xs.foldRight(b)((x, b) => Tm.Lam(p, x, ty, b))
        }
        (None, body)
      case Some(rty) =>
        val ty = createPi(ps, rty)
        val body = ps.foldRight(prebody) { case ((p, xs, _), b) =>
          xs.foldRight(b)((x, b) => Tm.Lam(p, x, None, b))
        }
        (Some(ty), body)
    (pos, x, ty, body)

  private def createPi(ps: List[DefParam], rty: Ty)(using
      ctx: Ctx
  ): Tm =
    ps.foldRight(rty) { case ((p, xs, opty), rty) =>
      val pty = opty.getOrElse(hole)
      xs.foldRight(rty) { (x, rty) => Tm.Pi(p, x, pty, rty) }
    }

  private def parseParams()(using ctx: Ctx): List[DefParam] = list(parseParam)

  private def parseGrouping()(using ctx: Ctx): (List[Bind], Option[Ty]) =
    val x = bind()
    val xs = list(tryBind)
    val ty = if trySymbol(":") then Some(parseExpr()) else None
    (x :: xs, ty)

  private def parseParam()(using ctx: Ctx): Option[DefParam] =
    if trySymbol("(") then
      val pos = ctx.pos
      val (xs, ty) = parseGrouping()
      symbol(")")
      Some((pos, xs, ty))
    else tryBind().map(x => (ctx.pos, List(x), None))

  private def tryParseAtom()(using ctx: Ctx): Option[Tm] =
    tryIdentifier() match
      case Some(x) if x.startsWith("_") =>
        Some(
          Tm.Hole(ctx.pos, if x.length == 1 then None else Some(Name(x.tail)))
        )
      case Some(x) => Some(Tm.Var(ctx.pos, Name(x)))
      case None    =>
        if tryKeyword("Type") then Some(Tm.Type(ctx.pos))
        else if trySymbol("(") then
          val pos = ctx.pos
          val expr = parseExpr()
          val rest = mutable.ArrayBuffer.empty[(PosInfo, Tm)]
          while trySymbol(",") do rest += ((ctx.pos, parseExpr()))
          symbol(")")
          val nested = ((pos, expr) :: rest.toList).reduceRight {
            case ((_, f), (p, s)) =>
              (p, Tm.Pair(p, f, s))
          }
          Some(nested._2)
        else None

  private def parseAtom()(using ctx: Ctx): Tm =
    debug(s"parseAtom: $ctx")
    tryParseAtom().getOrElse(err("expected an expression"))

  private def parseExpr()(using ctx: Ctx): Tm =
    debug(s"parseExpr: $ctx")
    if tryKeyword("let") then parseLet()
    else if trySymbol("\\") then parseLam()
    else if tryKeyword("fst") then Tm.Proj(ctx.pos, ProjType.Fst, parseAtom())
    else if tryKeyword("snd") then Tm.Proj(ctx.pos, ProjType.Snd, parseAtom())
    else if tryKeyword("with") then
      val pos = ctx.pos
      val tm = parseAtom()
      val self = parseAtom()
      Tm.With(pos, tm, self)
    else if tryKeyword("self") then
      val pos = ctx.pos
      val x = name()
      symbol("=>")
      val b = parseExpr()
      Tm.Self(pos, x, b)
    else if tryKeyword("in") then
      val pos = ctx.pos
      val x = name()
      symbol("=>")
      val b = parseExpr()
      Tm.In(pos, x, b)
    else if tryKeyword("out") then Tm.Out(ctx.pos, parseAtom())
    else
      backtrack(piSigmaParam()) match
        case None    => apps()
        case Some(p) =>
          val ps = list(piSigmaParam)
          val piOrSigma =
            if trySymbol("->") then true else { symbol("**"); false }
          val rt = parseExpr()
          (p :: ps).foldRight(rt) { case ((pos, xs, ty), rt) =>
            xs.foldRight(rt)((x, rt) =>
              if piOrSigma then Tm.Pi(pos, x, ty, rt)
              else Tm.Sigma(pos, x, ty, rt)
            )
          }

  private def piSigmaParam()(using
      ctx: Ctx
  ): Option[(PosInfo, List[Bind], Ty)] =
    if trySymbol("(") then
      if trySymbol(")") then None
      else
        val pos = ctx.pos
        tryBind() match
          case Some(x) =>
            val xs = list(tryBind)
            if trySymbol(":") then
              val ty = parseExpr()
              symbol(")")
              Some((pos, x :: xs, ty))
            else None
          case None => None
    else None

  private def apps()(using ctx: Ctx): Tm =
    debug(s"apps: $ctx")
    val pos = ctx.pos
    val hd = parseAtom()
    val tl = list(tryParseAtom)
    val optLam =
      if trySymbol("\\") then List(parseLam())
      else Nil
    val expr = (tl ++ optLam).foldLeft(hd) { case (f, a) =>
      Tm.App(a.pos, f, a)
    }
    if trySymbol("->") then
      val rt = parseExpr()
      Tm.Pi(pos, Bind.DontBind, expr, rt)
    else if trySymbol("**") then
      val rt = parseExpr()
      Tm.Sigma(pos, Bind.DontBind, expr, rt)
    else expr

  private def parseLet()(using ctx: Ctx): Tm =
    val (pos, x, ty, value) = parseDefPart()
    symbol(";")
    val body = parseExpr()
    Tm.Let(pos, x, ty, value, body)

  private def parseLam()(using ctx: Ctx): Tm =
    val ps = parseParams()
    symbol("=>")
    val body = parseExpr()
    ps.foldRight(body) { case ((p, xs, ty), b) =>
      xs.foldRight(b)((x, b) => Tm.Lam(p, x, ty, b))
    }

  // parsers
  private def keyword(kw: String)(using ctx: Ctx): Unit =
    consumeMatch(s"keyword '$kw'"):
      case Token.Keyword(kw2, _) if kw == kw2 => Some(())
      case _                                  => None

  private def symbol(s: String)(using ctx: Ctx): Unit =
    consumeMatch(s"symbol '$s'"):
      case Token.Symbol(s2, _) if s == s2 => Some(())
      case _                              => None

  private def identifier()(using ctx: Ctx): String =
    consumeMatch("identifier"):
      case Token.Identifier(id, _) => Some(id)
      case _                       => None

  private def number()(using ctx: Ctx): Int =
    consumeMatch("number"):
      case Token.Number(n, _) => Some(n)
      case _                  => None

  private def tryKeyword(kw: String)(using ctx: Ctx): Boolean =
    tryConsumeMatchBool:
      case Token.Keyword(kw2, _) if kw == kw2 => true
      case _                                  => false

  private def trySymbol(s: String)(using ctx: Ctx): Boolean =
    tryConsumeMatchBool:
      case Token.Symbol(s2, _) if s == s2 => true
      case _                              => false

  private def tryIdentifier()(using ctx: Ctx): Option[String] =
    tryConsumeMatch:
      case Token.Identifier(x, _) => Some(x)
      case _                      => None

  private def tryNumber()(using ctx: Ctx): Option[Int] =
    tryConsumeMatch:
      case Token.Number(v, _) => Some(v)
      case _                  => None

  private def name()(using ctx: Ctx): Name = Name(identifier())

  private def tryName()(using ctx: Ctx): Option[Name] =
    tryIdentifier().map(Name.apply)

  private def bind()(using ctx: Ctx): Bind = Bind.fromString(identifier())

  private def tryBind()(using ctx: Ctx): Option[Bind] =
    tryIdentifier().map(Bind.fromString)

  // util
  private def consume()(using ctx: Ctx): Option[Token] =
    val tokens = ctx.tokens
    if tokens.isEmpty then None
    else
      val token = tokens.head
      val ret = Some(token)
      tokens.dropInPlace(1)
      ctx.pos = token.pos
      ret

  private def peek(using ctx: Ctx): Option[Token] = ctx.tokens.headOption

  private inline def consumeMatch[A](msg: String)(
      inline matcher: Token => Option[A]
  )(using ctx: Ctx): A =
    consume() match
      case Some(t) =>
        matcher(t) match
          case None    => err(s"expected $msg but got '$t'")
          case Some(v) => v
      case None => err(s"expected $msg but got end of input")

  private inline def tryConsumeMatch[A](inline matcher: Token => Option[A])(
      using ctx: Ctx
  ): Option[A] =
    peek match
      case Some(t) =>
        matcher(t) match
          case None => None
          case s    =>
            consume()
            s
      case _ => None

  private inline def tryConsumeMatchBool(inline matcher: Token => Boolean)(using
      ctx: Ctx
  ): Boolean =
    tryConsumeMatch(t => if matcher(t) then Some(()) else None).isDefined

  private def list[A](p: () => Option[A]): List[A] =
    p() match
      case None    => Nil
      case Some(x) => x :: list(p)

  private def mark()(using ctx: Ctx): Ctx =
    Ctx(ctx.pos, ctx.tokens.clone())

  private def restore(markedCtx: Ctx)(using ctx: Ctx): Unit =
    ctx.pos = markedCtx.pos
    ctx.tokens = markedCtx.tokens

  private def backtrack[A](action: => Option[A])(using
      ctx: Ctx
  ): Option[A] =
    val m = mark()
    action match
      case None => restore(m); None
      case s    => s
