package core

import java.nio.file.Path

import ch.qos.logback.classic.{Level, Logger}
import org.slf4j.LoggerFactory
import viper.silver.frontend.Frontend
import viper.silver.testing.SilSuite
import viper.silver.verifier.Verifier

class VerifierTests  extends SilSuite {

  def createVerifierInstance() = {
    val logger = LoggerFactory.getLogger(getClass.getName).asInstanceOf[Logger]
    logger.setLevel(Level.OFF)
    val verifier = new MyVerifier(logger)
    verifier.parseCommandLine(List("no-file"))
    verifier
  }

  /** The list of verifiers to be used. Should be overridden by a lazy val
    * if the verifiers need to access the config map provided by ScalaTest.
    */
  lazy val verifiers: Seq[Verifier] = List(createVerifierInstance())


  /** The frontend to be used. */
  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    require(files.length == 1)
    val frontend = new MyVerifierFrontend
    frontend.init(verifier)
    frontend.reset(files.head)
    frontend
  }

  /**
    * The test directories where tests can be found.
    * The directories must be relative because they are resolved via
    * [[java.lang.ClassLoader]].
    *
    * @see http://stackoverflow.com/a/7098501/491216.
    * @return A sequence of test directories.
    */
   override def testDirectories: Seq[String] = List("provided", "submitted")
}
