import Common.*
import Core.*

import scala.collection.mutable

object State:
  final case class GlobalEntry(
      name: Name,
      tm: Tm,
      ty: Ty,
      value: Val,
      vty: VTy
  )

  private val globals: mutable.ArrayBuffer[GlobalEntry] =
    mutable.ArrayBuffer.empty

  def addGlobal(entry: GlobalEntry): Unit = globals += entry
  def getGlobal(x: Name): Option[GlobalEntry] =
    globals.findLast(e => e.name == x)
  def nameIsDefined(x: Name): Boolean = getGlobal(x).isDefined
