name := "uppsat"

version := "0.01"

scalaVersion := "2.12.7"

scalacOptions += "-Yresolve-term-conflict:package" 

libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.1"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"

libraryDependencies += "org.scalafx" %% "scalafx" % "8.0.144-R12"

fork in run := true



