name := "uppsat"

version := "0.01"

scalaVersion := "2.13.1"

scalacOptions += "-Yresolve-term-conflict:package"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.1" % "test"
libraryDependencies += "org.scalactic" %% "scalactic" % "3.1.1"
