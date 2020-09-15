import org.scalatest._
import java.io.File
import scala.io.Source

import uppsat.ApproximationSolver.Sat
import uppsat.ApproximationSolver.Unsat
import uppsat.ApproximationSolver.Unknown
import uppsat.globalOptions
import uppsat.globalOptions._

class Regression extends FunSpec {

  def getListOfFiles(dir: File, extensions: List[String]): List[File] = {
    dir.listFiles.filter(_.isFile).toList.filter { file =>
        extensions.exists(file.getName.endsWith(_))
    }
  }

   globalOptions.DEADLINE = Some(20000L)
   globalOptions.PARANOID = true

   val satSources = new File(getClass.getResource("/sat/").toURI())
   val satFiles = getListOfFiles(satSources, List(".smt2"))


   describe("SAT : " ) {
     for (f <- satFiles) {
         println("Testing " + f)
         val args =  Array(f.toString(), "-t=60")
         val result = uppsat.main.main_aux(args)
         result match {
           case _ : Sat =>
             it(f.toPath().toString().split('\\').reverse.head) {assert(true)}
           case Unsat =>
             it(f.toPath().toString().split('\\').reverse.head) {assert(false)}
           case Unknown =>
             ignore(f.toPath().toString().split('\\').reverse.head) {assert(false)}
         }
     }
   }


   val unsatSources = new File(getClass.getResource("/unsat/").toURI())
   val unsatFiles = getListOfFiles(unsatSources, List(".smt2"))

    describe("UNSAT : " ) {
     for (f <- unsatFiles) {
         println("Testing " + f)
         val args =  Array(f.toString(), "-t=60")
         val result = uppsat.main.main_aux(args)
         result match {
           case _ : Sat =>
             it(f.toPath().toString().split('\\').reverse.head) {assert(false)}
           case Unsat =>
             it(f.toPath().toString().split('\\').reverse.head) {assert(true)}
           case Unknown =>
             ignore(f.toPath().toString().split('\\').reverse.head) {assert(false)}
         }
     }
   }
}
