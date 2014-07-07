name := "Leon"

version := "2.3"

organization := "ch.epfl.lara"

scalaVersion := "2.10.3"

scalacOptions += "-deprecation"

scalacOptions += "-unchecked"

scalacOptions += "-feature"

javacOptions += "-Xlint:unchecked"

if(System.getProperty("sun.arch.data.model") == "64") {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "64" }
} else {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "32" }
}

resolvers += "Typesafe Repository" at "http://repo.typesafe.com/typesafe/releases/"

resolvers += "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots"

libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-compiler" % "2.10.3",
    "org.scalatest" % "scalatest_2.10" % "2.0.M5b" % "test" excludeAll(ExclusionRule(organization="org.scala-lang")),
    "junit" % "junit" % "4.8" % "test",
    "com.typesafe.akka" %% "akka-actor" % "2.2.0" excludeAll(ExclusionRule(organization="org.scala-lang")),
    "com.github.axel22" %% "scalameter" % "0.5-M2"
)

testFrameworks += new TestFramework("org.scalameter.ScalaMeterFramework")

fork in run := true

fork in Test := true

logBuffered := false

parallelExecution in Test := false

javaOptions in Test += "-Xss1G"

javaOptions in Test += "-Xms4G"

sourcesInBase in Compile := false

