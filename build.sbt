name := "uppsat"

version := "0.01"

scalaVersion := "2.13.5"

scalacOptions += "-Yresolve-term-conflict:package"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.1" % "test"
libraryDependencies += "org.scalactic" %% "scalactic" % "3.1.1"
libraryDependencies += "org.scala-lang.modules" %% "scala-collection-contrib" % "0.2.2"

parallelExecution in Test := false
