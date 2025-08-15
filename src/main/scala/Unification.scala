import Common.*
import Debug.debug
import Core.*
import Evaluation.*

object Unification:
  class UnificationError(val msg: String) extends RuntimeException(msg):
    override def toString: String = s"unification error: $msg"
  private inline def err(msg: String): Nothing =
    throw new UnificationError(msg)

  private def quoteS(v: Val)(using k: Lvl): Tm =
    quote(v, QuoteOption.UnfoldMetas)

  // partial renaming
  private type LvlMap = Map[Lvl, Lvl]
  private final case class Ren(
      occ: Option[MetaId],
      dom: Lvl,
      cod: Lvl,
      ren: LvlMap
  ):
    def lift = Ren(occ, dom + 1, cod + 1, ren + (cod -> dom))
    def skip = Ren(occ, dom, cod + 1, ren)
    def withOcc(m: MetaId) = Ren(Some(m), dom, cod, ren)

  // inversion
  private def invert(sp: Spine)(using gamma: Lvl): (Ren, Option[Pruning]) =
    def go(sp: Spine): (Lvl, LvlMap, Set[Lvl], List[(Lvl, Icit)]) = sp match
      case Spine.Out(_)        => err(s"out in meta spine")
      case Spine.Empty         => (lvl0, Map.empty, Set.empty, Nil)
      case Spine.App(sp, a, i) =>
        forceAll(a) match
          case Var1(x) =>
            val (dom, ren, nlvars, fsp) = go(sp)
            if ren.contains(x) || nlvars.contains(x) then
              (dom + 1, ren - x, nlvars + x, (x, i) :: fsp)
            else (dom + 1, ren + (x -> dom), nlvars, (x, i) :: fsp)
          case t =>
            err(s"non-var in meta spine: ${quoteS(t)}")
    val (dom, ren, nlvars, fsp) = go(sp)
    def mask(xs: List[(Lvl, Icit)]): Pruning =
      xs match
        case Nil           => Nil
        case (x, i) :: fsp =>
          val p = if nlvars.contains(x) then Prune.Skip else Prune.Bind(i)
          p :: mask(fsp)
    (
      Ren(None, dom, gamma, ren),
      if nlvars.isEmpty then None else Some(mask(fsp))
    )

  // pruning
  private def pruneTy(rp: RevPruning, a: VTy): Ty =
    def go(p: Pruning, ren: Ren, a: VTy): Ty =
      (p, forceAll(a)) match
        case (Nil, a)                                 => rename(a)(using ren)
        case (Prune.Bind(_) :: p, Val.Pi(x, i, a, b)) =>
          Tm.Pi(x, i, rename(a)(using ren), go(p, ren.lift, b(Var1(ren.cod))))
        case (Prune.Skip :: p, Val.Pi(_, _, _, b)) =>
          go(p, ren.skip, b(Var1(ren.cod)))
        case _ => impossible()
    go(rp.expose, Ren(None, lvl0, lvl0, Map.empty), a)

  private def pruneMeta(p: Pruning, m: MetaId): MetaId =
    val mty = State.unsolvedMetaType(m)
    val prunedty = eval(pruneTy(RevPruning(p), mty))(using Env.Empty)
    val m2 = State.newMeta(prunedty)
    val solution =
      eval(lams(mkLvl(p.size), mty, Tm.AppPruning(m2, p)))(using Env.Empty)
    State.solveMeta(m, solution)
    m2

  private enum PruneStatus:
    case OKRenaming
    case OKNonRenaming
    case NeedsPruning
  import PruneStatus.*

  private def pruneFlex(m: MetaId, sp: Spine)(using ren: Ren): Tm =
    def go(sp: Spine): (List[(Option[Tm], Icit)], PruneStatus) =
      sp match
        case Spine.Empty         => (Nil, OKRenaming)
        case Spine.Out(_)        => err(s"pruning failed for ?$m")
        case Spine.App(sp, a, i) =>
          val (sp2, status) = go(sp)
          forceAll(a) match
            case Var1(x) =>
              (ren.ren.get(x), status) match
                case (Some(x), _) =>
                  ((Some(Tm.Var(x.toIx(using ren.dom))), i) :: sp2, status)
                case (None, OKNonRenaming) => err(s"pruning failed for ?$m")
                case (None, _)             => ((None, i) :: sp2, NeedsPruning)
            case _ =>
              status match
                case NeedsPruning => err(s"pruning failed for ?$m")
                case _ => ((Some(rename(a)), i) :: sp2, OKNonRenaming)
    val (sp2, status) = go(sp)
    def toPrune(e: (Option[Tm], Icit)): Prune =
      e match
        case (Some(_), i) => Prune.Bind(i)
        case _            => Prune.Skip
    val m2 = status match
      case OKRenaming    => m
      case OKNonRenaming => m
      case NeedsPruning  => pruneMeta(sp2.map(toPrune), m)
    sp2.foldRight(Tm.Meta(m2)) { case ((mu, i), tm) =>
      mu.fold(tm)(u => Tm.App(tm, u, i))
    }

  // renaming
  private def rename(v: Val)(using ren: Ren): Tm =
    inline def goClos(c: Clos)(using ren: Ren) =
      go(c(Var1(ren.cod)))(using ren.lift)
    def goSp(hd: Tm, sp: Spine)(using ren: Ren): Tm =
      sp match
        case Spine.Empty         => hd
        case Spine.App(sp, a, i) => Tm.App(goSp(hd, sp), go(a), i)
        case Spine.Out(sp)       => Tm.Out(goSp(hd, sp))
    def go(v: Val)(using ren: Ren): Tm =
      forceMetas(v) match
        case Val.Flex(m2, sp) =>
          ren.occ match
            case Some(m) if m == m2 => err(s"occurs check failed for meta ?$m2")
            case _                  => pruneFlex(m2, sp)
        case Val.Unfold(UnfoldHead.Global(x), sp) => goSp(Tm.Global(x), sp)
        case Val.Rigid(Head.Var(x), sp)           =>
          ren.ren.get(x) match
            case None     => err(s"escaping variable '$x")
            case Some(x2) => goSp(Tm.Var(x2.toIx(using ren.dom)), sp)

        case Val.Lam(x, i, ty, b) => Tm.Lam(x, i, go(ty), goClos(b))
        case Val.Pi(x, i, ty, b)  => Tm.Pi(x, i, go(ty), goClos(b))
        case Val.Self(x, ty, b)   => Tm.Self(x, go(ty), goClos(b))
        case Val.In(tm)           => Tm.In(go(tm))
        case Val.Type             => Tm.Type
    go(v)

  // solving
  private def lams(l1: Lvl, ty: VTy, b: Tm): Tm =
    def go(l2: Lvl, ty: VTy): Tm =
      if l1 == l2 then b
      else
        forceAll(ty) match
          case t @ Val.Pi(x, i, pt, rt) =>
            val qpt = quote(pt)(using l2)
            val qrt = go(l2 + 1, rt(Var1(l2)))
            Tm.Lam(x, i, qpt, qrt)
          case _ => impossible()
    go(lvl0, ty)

  private def solve(m: MetaId, sp: Spine, rhs: Val)(using gamma: Lvl): Unit =
    val (ren, mp) = invert(sp)
    solve(m, mp, rhs)(using ren)

  private def solve(m: MetaId, mp: Option[Pruning], rhs: Val)(using
      ren: Ren
  ): Unit =
    val mty = State.unsolvedMetaType(m)
    mp.foreach(pr => pruneTy(RevPruning(pr), mty))
    val tm = rename(rhs)(using ren.withOcc(m))
    val solution = lams(ren.dom, mty, tm)
    debug(s"meta solution ?$m = $solution")
    val vsolution = eval(solution)(using Env.Empty)
    State.solveMeta(m, vsolution)

  // unification
  private def unify(top1: Val, sp1: Spine, top2: Val, sp2: Spine)(using
      lvl: Lvl
  ): Unit =
    (sp1, sp2) match
      case (Spine.Empty, Spine.Empty)                     => ()
      case (Spine.App(sp1, a1, _), Spine.App(sp2, a2, _)) =>
        unify(top1, sp1, top2, sp2); unify(a1, a2)
      case (Spine.Out(sp1), Spine.Out(sp2)) => unify(top1, sp1, top2, sp2)
      case _                                =>
        err(
          s"spine mismatch ${quoteS(top1)} ~ ${quoteS(top2)}"
        )

  private def flexFlex(m1: MetaId, sp1: Spine, m2: MetaId, sp2: Spine)(using
      lvl: Lvl
  ): Unit =
    def go(m1: MetaId, sp1: Spine, m2: MetaId, sp2: Spine): Unit =
      try invert(sp1)
      catch case _: UnificationError => solve(m2, sp2, Val.Flex(m1, sp1))
    if sp1.size < sp2.size then go(m2, sp2, m1, sp1) else go(m1, sp1, m2, sp2)

  private def intersect(m: MetaId, sp1: Spine, sp2: Spine)(using
      lvl: Lvl
  ): Unit =
    def go(sp1: Spine, sp2: Spine): Option[Pruning] =
      (sp1, sp2) match
        case (Spine.Empty, Spine.Empty)                     => Some(Nil)
        case (Spine.App(sp1, a1, i), Spine.App(sp2, a2, _)) =>
          (forceAll(a1), forceAll(a2)) match
            case (Var1(x), Var1(y)) =>
              go(sp1, sp2).map(l =>
                (if x == y then Prune.Bind(i) else Prune.Skip) :: l
              )
            case _ => None
        case (Spine.Out(_), _) => err(s"failed to intersect ?$m")
        case (_, Spine.Out(_)) => err(s"failed to intersect ?$m")
        case _                 => impossible()
    go(sp1, sp2) match
      case None => unify(Val.Flex(m, sp1), sp1, Val.Flex(m, sp2), sp2)
      case Some(p) if p.containsSkips => pruneMeta(p, m)
      case _                          => ()

  def unify(a: Val, b: Val)(using lvl: Lvl): Unit =
    debug(
      s"unify ${quoteS(a)} ~ ${quoteS(b)}"
    )
    inline def unifyErr() =
      err(
        s"cannot unify ${quoteS(a)} ~ ${quoteS(b)}"
      )
    inline def goClos(a: Clos, b: Clos): Unit =
      val v = Var1(lvl)
      unify(a(v), b(v))(using lvl + 1)
    def unfold(v: Val): Option[Val] =
      v match
        case Val.Unfold(UnfoldHead.Global(x), sp) => global(x).map(spine(_, sp))
        case _                                    => None
    def unfold2(a: Val, b: Val): Option[(Val, Val)] =
      (unfold(a), unfold(b)) match
        case (None, None)       => None
        case (Some(a), None)    => Some((a, b))
        case (None, Some(b))    => Some((a, b))
        case (Some(a), Some(b)) => Some((a, b))
    inline def unfoldUnify2(a: Val, b: Val)(err: => Nothing): Unit =
      unfold2(a, b).fold(err)((a, b) => unify(a, b))
    (forceMetas(a), forceMetas(b)) match
      case (Val.Type, Val.Type)                             => ()
      case (Val.Rigid(x, sp1), Val.Rigid(y, sp2)) if x == y =>
        unify(a, sp1, b, sp2)

      case (Val.Pi(_, i1, ty1, b1), Val.Pi(_, i2, ty2, b2)) if i1 == i2 =>
        unify(ty1, ty2); goClos(b1, b2)
      case (Val.Self(_, ty1, b1), Val.Self(_, ty2, b2)) =>
        unify(ty1, ty2); goClos(b1, b2)
      case (Val.In(t1), Val.In(t2)) => unify(t1, t2)

      case (Val.Flex(m, sp1), Val.Flex(m2, sp2)) if m == m2 =>
        intersect(m, sp1, sp2)
      case (Val.Flex(m1, sp1), Val.Flex(m2, sp2)) =>
        flexFlex(m1, sp1, m2, sp2)

      case (Val.Lam(_, _, _, b1), Val.Lam(_, _, _, b2)) => goClos(b1, b2)
      case (Val.Lam(_, i, _, b), f)                     =>
        val v = Var1(lvl)
        unify(b(v), app(f, v, i))(using lvl + 1)
      case (f, Val.Lam(_, i, _, b)) =>
        val v = Var1(lvl)
        unify(app(f, v, i), b(v))(using lvl + 1)

      case (Val.Flex(m, sp), b) => solve(m, sp, b)
      case (a, Val.Flex(m, sp)) => solve(m, sp, a)

      case (u1 @ Val.Unfold(h1, sp1), u2 @ Val.Unfold(h2, sp2)) =>
        try
          if h1 != h2 then err("head mismatch")
          unify(a, sp1, b, sp2)
        catch case err: UnificationError => unfoldUnify2(u1, u2)(throw err)
      case (u1 @ Val.Unfold(_, _), b) =>
        unfold(u1).map(a => unify(a, b)).getOrElse(unifyErr())
      case (a, u2 @ Val.Unfold(_, _)) =>
        unfold(u2).map(b => unify(a, b)).getOrElse(unifyErr())

      case _ => unifyErr()
