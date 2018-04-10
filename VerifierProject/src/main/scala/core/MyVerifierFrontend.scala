package core

import ch.qos.logback.classic.{Level, Logger}
import org.slf4j.LoggerFactory
import viper.silver.frontend.SilFrontend
import viper.silver.reporter._


/**
  * Reporter is a class responsible for reporting verification results to the user.
  *
  * This class reports the verification results via standard output.
  */
object StdIOReporter extends Reporter {
  val name = "stdout"

  def report(msg: Message): Unit = {
    msg match {
      case OverallSuccessMessage(verifier, timeMs) =>
        val time = f"${timeMs / 1000.0}%.3f seconds"
        println(s"$verifier finished in $time.")
        println("No errors found.")
      case OverallFailureMessage(verifier, time, failure) =>
        println(s"$verifier finished in $time seconds.")
        println("The following errors were found:")
        failure.errors.foreach(error => println(error))
      case _ =>
    }
  }
}

/**
 * The frontend is responsible for communication with a user: it parses
 * and type-checks the Viper program, calls the verifier, and reports
 * the verification results back to the user. For this project, you
 * should not need to touch the front-end code.
 */
class MyVerifierFrontend(override val reporter: Reporter, override val logger: Logger) extends SilFrontend { // “Sil” is an (old) name for the Viper intermediate language

  def this() = {
    this(StdIOReporter, LoggerFactory.getLogger(getClass.getName).asInstanceOf[Logger])
    logger.setLevel(Level.OFF)
  }

  def this(reporter: Reporter) = {
    this(reporter, LoggerFactory.getLogger(getClass.getName).asInstanceOf[Logger])
  }

  protected var verifierInstance: MyVerifier = _ // initialised to null - this will be set in the "execute" method below (which calls createVerifier)

  def createVerifier(fullCmd: String) = {
    logger.trace(s"Create verifier: $fullCmd")
    verifierInstance = new MyVerifier(logger)  // you will do your work in this class (see below)

    verifierInstance
  }

  def configureVerifier(args: Seq[String]) = {
    logger.trace(s"Configure verifier: $args")
    verifierInstance.parseCommandLine(args)
    verifierInstance.start() // not strictly needed; the current implementation doesn't do anything

    verifierInstance.config
  }
}
