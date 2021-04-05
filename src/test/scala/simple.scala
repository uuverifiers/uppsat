import org.scalatest._
import java.io.File
import scala.io.Source

import uppsat.ApproximationSolver.{Sat, Unsat, Unknown}
import uppsat.globalOptions
import uppsat.globalOptions._

class Simple extends FunSpec {

  def simpleFile(i : Int) = {
    getClass.getResource("/simple/simple" + i + ".smt2").getPath()
  }

  // Simple 1
  describe("Simple 1:") {
    val f = simpleFile(1)
    val args =  Array(f.toString(), "-t=60")
    val result = uppsat.main.main_aux(args)
    it("should finish in first iteration") {
      assert(globalOptions.STATS_ITERATIONS == 1)
    }
    it("should return SAT") {
      assert(result.isInstanceOf[Sat])
    }
    it("should NOT have reached max precision") {
      assert(!globalOptions.REACHED_MAX_PRECISON)
    }
  }
}
