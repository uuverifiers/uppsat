object timeuppsat {

  def runSolver(cmd : String, problem : String, parser : String => String) : (String, String) = {
    import sys.process._
    val stdout = new StringBuilder
    val stderr = new StringBuilder       
    val status = ("timeout 60s " + cmd + " " + problem) ! ProcessLogger(str => stdout append (str + "\n"), str => stderr append (str + "\n"))
    if (status != 0)
      ("-", "t/o")
    // throw new Exception("\"" + cmd + "\" generated " + stderr.toString)
    else
      parser(stdout.toString)
  }

  def z3parse(str : String) : String = {
    // Time or Total time?
    val timePattern = "\\s*:time\\s*([0-9.]+)\\)?".r
    var answer = "unknown"
    for (l <- str.lines) {
      l match {
        case "sat" | "unsat" | "unknown" => answer = l
        case timePattern(t) => return (answer, t.toFloat.toString)
        case _ => ()
      }
    }
    throw new Exception("Couldn't find time output from Z3: " + str)
  }

  def uppsatparse(str : String) : String = {
    val timePattern = "Solving time: (\\d+)ms".r
    var answer = "unknown"
    for (l <- str.lines) {
      l match {
        case "sat" | "unsat" | "unknown" => answer = l
        case timePattern(t) => return (answer, t.toFloat.toString)
        case _ => ()
      }
    }
    throw new Exception("Couldn't find time output from uppsat: " + str)
  }

  def main(args : Array[String]) = {
    val solvers = Map(
      "z3" -> (("z3 -smt2 -st", z3parse)),
      "uppsat" -> (("scala uppsat.jar", uppsatparse))
    ) : Map[String, (String, String => String)]

    println("Trying solvers:")
    for ((solver, (command, _)) <- solvers)
      println("\t" + solver + " (" + command + ")")

    val files = args

    val count = files.length
    var complete = 0
    println("[" + (" "*count) + "]")
    val results =
      for (f <- files) yield {
        val r = 
          for ((solver, (command, parser)) <- solvers) yield {
            val (answer, time) = runSolver(command, f, parser)
            answer +  time
          }
        complete += 1
        println("[" + ("|"*complete) + (" "*(count-complete)) + "]")
        (f, r)
      }

    println("<--- RESULTS --->")
    println(solvers.keys.mkString("\t") + "\t\t" + "Filename")
    for ((f, r) <- results) {
      println(r.mkString("\t") + "\t\t" + f)
    }
  }
}
