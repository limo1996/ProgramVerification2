name := "VerifierProject"

version := "1.0"

autoScalaLibrary := true

scalaVersion := "2.11.8"

resolvers += "OSS Sonatype" at "https://repo1.maven.org/maven2/"

libraryDependencies += "org.rogach" %% "scallop" % "2.0.7"

lazy val silver = RootProject(file("../silver"))

lazy val scalaSmtlib = RootProject(file("../scala-smtlib"))

val main = Project(id = "VerifierProject", base = file(".")).dependsOn(silver,scalaSmtlib) 

enablePlugins(JavaAppPackaging)

fork in run := true