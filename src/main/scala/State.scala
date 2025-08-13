import Common.*
import Core.*

import scala.collection.mutable

object State:
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
