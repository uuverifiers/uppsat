name := "uppsat"

version := "0.01"

scalaVersion := "2.13.1"

//scalacOptions ++= Seq("-Yresolve-term-conflict:package", "-deprecation", "-feature")
scalacOptions ++= Seq("-Yresolve-term-conflict:package")


libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.1" % "test"
libraryDependencies += "org.scalactic" %% "scalactic" % "3.1.1"
libraryDependencies += "org.scala-lang.modules" %% "scala-collection-contrib" % "0.2.1"

