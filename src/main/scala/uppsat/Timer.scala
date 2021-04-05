/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package uppsat;

import scala.collection.mutable.{ArrayStack => Stack, HashMap, ArrayBuilder}
import scala.util.Sorting

/**
 * Object for measuring the time needed by the various tasks, methods, etc.
 * The object, in particular, supports nested operations that call each other
 * and correctly measures the time spent in each of the operations.
 */

object Timer {

  case class TimeoutException(msg : String) extends Exception("Timeout: " + msg)

  private var startTime : Long = _
  private val runningOps = new Stack[String]
  private var iterations = 0

  // accumulated time spent in each operation
  private val accumulatedTimes = new HashMap[String, Long].withDefaultValue(0)

  // private val accumulatedTimes = new HashMap[String, Long] {
  //   override def default(op : String) : Long = 0
  // }


  // number of call to each operation
  private val callCounters = new HashMap[String, Int].withDefaultValue(0)
  // private val callCounters = new HashMap[String, Int] {
  //   override def default(op : String) : Int = 0
  // }

  private def addTime : Unit = {
    val now = System.nanoTime
    if (!runningOps.isEmpty) {
      val op = runningOps.top
      accumulatedTimes += (op -> (accumulatedTimes(op) + now - startTime))
    }
    startTime = now
  }

  def measure[A](op : String)(comp : => A) : A = {
    addTime
    callCounters += (op -> (callCounters(op) + 1))
    runningOps push op

    val res =
      try {
        comp
      } finally {
        addTime
        runningOps.pop
      }

    res
  }

  def reset : Unit = {
    accumulatedTimes.clear
    callCounters.clear
    iterations = 0
  }

  def newIteration = {
    iterations +=1
  }


  def ElapsedTime = accumulatedTimes.valuesIterator.foldLeft(0L)(_ + _)

  override def toString : String = {
    val resBuf = ArrayBuilder.make[(String, Int, Long)]

    for ((op, time) <- accumulatedTimes)
      resBuf += ((op, callCounters(op), time))

    val resAr = resBuf.result
    Sorting.stableSort(resAr)

    val table =
    (for ((op, count, time) <- resAr) yield {
      var paddedOp = op
      // HACK: for some reason, the <code>RichString.format</code> method does
      // not work
      while (paddedOp.size < 40)
        paddedOp = paddedOp + " "

      val timeInSec = time.toDouble / 1000000000.0

      (paddedOp + "\t" + count + "\t" + timeInSec + "s")
    }) mkString "\n"

    val totalTime = accumulatedTimes.valuesIterator.foldLeft(0L)(_ + _)
    val totalTimeInSec = totalTime.toDouble / 1000000000.0

    val totalCalls = callCounters.valuesIterator.foldLeft(0)(_ + _)

    val iter = ":iterations " + iterations
    val total = ":time "  + totalTimeInSec + "s"

    table + "\n" + iter + "\n" +  total
  }

  def stats : String = {
    val totalTime = accumulatedTimes.valuesIterator.foldLeft(0L)(_ + _)
    val totalTimeInSec = totalTime.toDouble / 1000000000.0

    val iter = ":iterations " + iterations
    val total = ":time "  + totalTimeInSec + "s"

    iter + "\n" +  total
  }
}
