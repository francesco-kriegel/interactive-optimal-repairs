
ThisBuild / organization := "de.tu_dresden.inf.lat"
ThisBuild / version := "0.1.2-SNAPSHOT"

ThisBuild / scalaVersion := "3.3.1"

lazy val root = (project in file("."))
  .settings(
    name := "interactive-optimal-repairs",
    idePackagePrefix := Some("de.tu_dresden.inf.lat")
  )

resolvers += Resolver.mavenLocal
resolvers += "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots/"

libraryDependencies += "org.scala-lang" %% "scala3-library" % "3.3.1"
//libraryDependencies += "net.sourceforge.owlapi" % "owlapi-distribution" % "5.5.0"
libraryDependencies += "net.sourceforge.owlapi" % "owlapi-osgidistribution" % "4.5.26" % "provided"
//libraryDependencies += "org.phenoscape" %% "scowl-owlapi5" % "1.4.1"
libraryDependencies += "org.phenoscape" %% "scowl" % "1.4.1" excludeAll "net.sourceforge.owlapi"
//libraryDependencies += "org.semanticweb.elk" % "elk-owlapi5" % "0.5.0-SNAPSHOT"
libraryDependencies += "org.semanticweb.elk" % "elk-owlapi" % "0.5.0-SNAPSHOT" excludeAll "net.sourceforge.owlapi"
libraryDependencies += "org.slf4j" % "slf4j-nop" % "2.0.9"
//libraryDependencies += "org.scala-lang" % "scala-library" % "2.13.11-bin-SNAPSHOT"
libraryDependencies += "edu.stanford.protege" % "protege-editor-owl" % "5.6.3" % "provided" excludeAll "net.sourceforge.owlapi"
//libraryDependencies += "se.samuelsjoberg" % "multiline" % "1.0-SNAPSHOT"

ThisBuild / assemblyMergeStrategy := {
  case PathList("module-info.class") => MergeStrategy.discard
  case x if x.endsWith("/module-info.class") => MergeStrategy.discard
  case x =>
    val oldStrategy = (ThisBuild / assemblyMergeStrategy).value
    oldStrategy(x)
}

Compile / mainClass := Some("de.tu_dresden.inf.lat.interactive_optimal_repairs.Main")

scalacOptions += "-Xfatal-warnings"
scalacOptions += "-deprecation"

// Generate the bundled jar with the command "sbt osgiBundle"
enablePlugins(SbtOsgi)
osgiSettings
OsgiKeys.bundleActivator := Some("org.protege.editor.owl.ProtegeOWL")
OsgiKeys.bundleSymbolicName := name.value + ";singleton:=true"
OsgiKeys.embeddedJars := ((Runtime / Keys.externalDependencyClasspath).value map (_.data)) // ++ ((Compile / Keys.externalDependencyClasspath).value map (_.data))
OsgiKeys.importPackage := Seq("*;resolution:=optional")
OsgiKeys.exportPackage := Seq("de.tu_dresden.inf.lat.interactive_optimal_repairs", "de.tu_dresden.inf.lat.protege_components")
//artifactName := { (sv: ScalaVersion, module: ModuleID, artifact: Artifact) => artifact.name + "-" + module.revision + "." + artifact.extension }
crossPaths := false
