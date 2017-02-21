object timeuppsat {

  def runSolver(cmd : String, problem : String, parser : String => (String, String, String)) : (String, String, String) = {
    import sys.process._
    val stdout = new StringBuilder
    val stderr = new StringBuilder       
    val status = ("timeout 60s " + cmd + " " + problem) ! ProcessLogger(str => stdout append (str + "\n"), str => stderr append (str + "\n"))
    if (status != 0)
      ("-", "t/o", "-")
    // throw new Exception("\"" + cmd + "\" generated " + stderr.toString)
    else
      parser(stdout.toString)
  }

  def z3parse(str : String) : (String, String, String) = {
    // Time or Total time?
    val timePattern = "\\s*:time\\s*([0-9.]+)\\)?".r
    var answer = "unknown"
    for (l <- str.lines) {
      l match {
        case "sat" | "unsat" | "unknown" => answer = l
        case timePattern(t) => return (answer, t.toFloat.toString, "-")
        case _ => ()
      }
    }
    //throw new Exception("Couldn't find time output from Z3: " + str)
    println("Z3 time not found" + str)
    (answer, "-", "-")
  }

  def uppsatparse(str : String) : (String, String, String) = {
    val timePattern = ":time (\\d+[.]\\d+)s".r
    val iterationsPattern = ":iterations (\\d+)".r 
    var answer = "unknown"
    var iterations = "-"
    for (l <- str.lines) {
      l match {
        case "sat" | "unsat" | "unknown" => answer = l
        case iterationsPattern(i) => iterations = i
        case timePattern(t) => return (answer, t.toFloat.toString, iterations)
        case _ => ()
      }
    }
    //throw new Exception("Couldn't find time output from uppsat: " + str)
    println("uppsat time not found" + str)
    (answer, "-", iterations)    
  }

  def main(args : Array[String]) = {
    val solvers = Map(
      "z3" -> (("z3 -smt2 -st", z3parse)),
      "uppsat" -> (("scala uppsat.jar", uppsatparse))
    ) : Map[String, (String, String => (String, String, String))]

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
          for ((solver, (command, parser)) <- solvers.toList) yield {
	           runSolver(command, f, parser)
          }
        complete += 1
        println("[" + ("|"*complete) + (" "*(count-complete)) + "]")
        (f, r)
      }

    println("<--- RESULTS --->")
    println("Status\t" + solvers.keys.mkString("\t") + "\t\t" + "Filename")
    for ((f, r) <- results) {
      val (answers : List[String], times : List[String], iterations : List[String]) = r.unzip3
      val firstAnswer : String = answers.head
      val agree = answers.foldLeft(true){(a : Boolean, x : String) => a && (x == firstAnswer)}
      val head = if (agree) answers.head else answers.mkString("/")  
      
      println( head + "\t" + times.mkString("\t") + "\t" + iterations.mkString("/") + "\t" + f + "\t" + answers.mkString("\t"))
    }
  }
}
