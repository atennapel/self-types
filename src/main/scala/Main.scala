import java.nio.file.{Files, Path}

object Main:
  @main def run(): Unit =
    Debug.setDebug(false)
    val file = "example.self"
    val text = Files.readString(Path.of(file))
    val defs = parse(text)
    val edefs = elaborate(defs, text)
    given ctx: Ctx = Ctx.empty
    edefs.foreach { d =>
      val ty = ctx.pretty(ctx.eval(d.ty))
      val v = ctx.pretty(ctx.eval(d.value))
      println(
        s"def ${d.name} : $ty = $v"
      )
    }
    /*
    State.getMetas().foreach { case (m, ty, ov) =>
      val sty = ctx.pretty(ty)
      ov.map(v => ctx.pretty(v)) match
        case None     => println(s"meta ?$m : $sty")
        case Some(sv) => println(s"meta ?$m : $sty = $sv")
    }
     */
    println()
    State.getGlobal(Common.Name("main")) match
      case Some(State.GlobalEntry(_, _, _, _, Some((tm, _)))) =>
        val nf = Evaluation.nf(tm)
        println(ctx.pretty(nf))
      case _ => ()

  // helpers
  private def parse(text: String): Surface.Defs =
    try Parser.parse(text)
    catch
      case err: Parser.ParseError =>
        val pos = err.pos
        System.err.println(err.msg)
        System.err.println(s"at $pos")
        System.err.println(showPos(text, pos))
        throw err

  private def elaborate(
      ds: Surface.Defs,
      text: String
  ): Core.Defs =
    try Elaboration.elaborate(ds)
    catch
      case err: Elaboration.ElaborationError =>
        val pos = err.pos
        System.err.println(err.msg)
        System.err.println(s"at $pos")
        System.err.println(showPos(text, pos))
        throw err

  private def showPos(text: String, pos: Common.PosInfo): String =
    val line = text.lines.toArray.apply(pos.line - 1)
    val indicator = " " * (pos.column - 1)
    s"$line\n$indicator^"
