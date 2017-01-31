import org.scalatest._
import java.io.File
import scala.io.Source

import uppsat.ApproximationSolver.Sat
import uppsat.ApproximationSolver.Unsat

class Regression extends FunSpec {
  // tests go here...
  
  def getListOfFiles(dir: File, extensions: List[String]): List[File] = {
    dir.listFiles.filter(_.isFile).toList.filter { file =>
        extensions.exists(file.getName.endsWith(_))
    }
  }
   
   val satSources = new File(getClass.getResource("/sat/").toURI())
   val unsatSources = new File(getClass.getResource("/unsat/").toURI())
   val satFiles = getListOfFiles(satSources, List(".smt2"))
   val unsatFiles = getListOfFiles(unsatSources, List(".smt2"))
   
   describe("SAT : " ) {
     for (f <- satFiles) {
         it(f.toPath().toString().split('\\').reverse.head) {
           val args =  Array(f.toString())
            uppsat.main.main_aux(args) match {
              case _ : Sat => assert(true)
              case _ => assert(false)
            }         
       }
     }
   }
   
   describe("UNSAT : " ) {
     for (f <- unsatFiles) {
         it(f.toPath().toString().split('\\').reverse.head) {
           val args =  Array(f.toString())
            uppsat.main.main_aux(args) match {
              case Unsat => assert(true)
              case _ => assert(false)
            }         
       }
     }
   }
}
