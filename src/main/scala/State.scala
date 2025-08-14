import Common.*
import Core.*

import scala.collection.mutable

object State:
  // globals
  final case class GlobalEntry(
      name: Name,
      ty: Ty,
      vty: VTy,
      var value: Option[(Tm, Val)]
  )

  private val globals: mutable.ArrayBuffer[GlobalEntry] =
    mutable.ArrayBuffer.empty

  def addGlobal(entry: GlobalEntry): Unit = globals += entry

  def getGlobal(x: Name): Option[GlobalEntry] =
    globals.findLast(e => e.name == x)

  def updateGlobalValue(x: Name, tm: Tm, value: Val): Unit =
    getGlobal(x).get.value = Some((tm, value))

  def nameIsDefined(x: Name): Boolean =
    getGlobal(x) match
      case Some(GlobalEntry(_, _, _, Some(_))) => true
      case _                                   => false

  // metas
  private val metas: mutable.ArrayBuffer[MetaEntry] = mutable.ArrayBuffer.empty

  enum MetaEntry:
    case Unsolved(ty: VTy)
    case Solved(value: Val, ty: VTy)

  def newMeta(ty: VTy): MetaId =
    val id = metaId(metas.size)
    metas += MetaEntry.Unsolved(ty)
    id

  def getMeta(id: MetaId): MetaEntry = metas(id.expose)

  def getUnsolvedMeta(id: MetaId): MetaEntry.Unsolved = getMeta(id) match
    case u @ MetaEntry.Unsolved(_) => u
    case MetaEntry.Solved(_, _)    => impossible()

  def unsolvedMetaType(id: MetaId): VTy = getUnsolvedMeta(id).ty

  def getSolvedMeta(id: MetaId): MetaEntry.Solved = getMeta(id) match
    case MetaEntry.Unsolved(_)      => impossible()
    case s @ MetaEntry.Solved(_, _) => s

  def modifyMeta(id: MetaId)(fn: MetaEntry => MetaEntry): Unit =
    metas(id.expose) = fn(metas(id.expose))

  def solveMeta(id: MetaId, v: Val): Unit =
    val u = getUnsolvedMeta(id)
    metas(id.expose) = MetaEntry.Solved(v, u.ty)

  def getMetas(): List[(MetaId, VTy, Option[Val])] =
    metas.zipWithIndex.collect {
      case (MetaEntry.Solved(v, ty), ix) => (metaId(ix), ty, Some(v))
      case (MetaEntry.Unsolved(ty), ix)  => (metaId(ix), ty, None)
    }.toList

  def unsolvedMetas(): List[(MetaId, VTy)] =
    metas.zipWithIndex.collect { case (MetaEntry.Unsolved(ty), ix) =>
      (metaId(ix), ty)
    }.toList

  def isMetaUnsolved(id: MetaId): Boolean = getMeta(id) match
    case MetaEntry.Unsolved(ty)      => true
    case MetaEntry.Solved(value, ty) => false

  // holes
  private val holes: mutable.ArrayBuffer[HoleEntry] = mutable.ArrayBuffer.empty

  final case class HoleEntry(ctx: Ctx, name: Name, tm: Tm, ty: VTy)

  def addHole(x: Name, tm: Tm, ty: VTy)(using ctx: Ctx): Boolean =
    holes.find(e => e.name == x) match
      case Some(_) => false
      case _       =>
        holes += HoleEntry(ctx, x, tm, ty)
        true

  def getHoles(): List[HoleEntry] = holes.toList
