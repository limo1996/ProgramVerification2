package core

import java.io.{BufferedOutputStream, File, FileOutputStream}

import ch.qos.logback.classic.Logger
import org.slf4j.LoggerFactory

import sys.process._
import smtlib.parser.Commands._
import smtlib.parser.CommandsResponses.{CheckSatResponse, CheckSatStatus, SatStatus, UnsatStatus, UnknownStatus}
import smtlib.theories.Core
import viper.silver.{ast => sil}
import viper.silver.frontend.SilFrontend
import viper.silver.reporter.{NoopReporter, Reporter}
import viper.silver.verifier.{VerificationResult, Failure => ViperFailure, Success => ViperSuccess}
import viper.silver.verifier.errors
import viper.silver.verifier.reasons

import scala.sys.process.{ProcessIO, ProcessLogger}

class MyVerifierFrontend(override val reporter: Reporter, override val logger: Logger) extends SilFrontend{ // "Sil" is an (old) name for the Viper intermediate language

  def this() = {
    this(NoopReporter, LoggerFactory.getLogger(getClass.getName).asInstanceOf[Logger])
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

object Main extends MyVerifierFrontend {

  def main(args: Array[String]) {
    try {
      execute(args)
      /* Will call createVerifier and configureVerifier (already defined below), and then verify the program (see verify method in MyVerifier)*/
    } finally {
      verifierInstance.stop() // also doesn't do anything in the current implementation - only needed if you have to "clean-up" in some way
    }

    val exitCode =
      if ( config.error.nonEmpty /* Handling command line options failed */
        || config.exit           /* We had to terminate for some other reason */
        || result != ViperSuccess) /* Verification (including parsing) failed */
        1
      else
        0

    sys.exit(exitCode)
  }

}



// This is where you will do most of your work:

class MyVerifier(private val logger: Logger) extends BareboneVerifier {

  override def name: String = "MyVerifier"

  /** Only needed if you want to do something special on (first) invocation of the verifier
    */
  override def start(): Unit = {
    logger.trace("Start verifier.")
  }

  /** Stops the verifier. Only needed if you have to perform some special clean-up on closing the verifier
    */
  override def stop(): Unit = {
    logger.trace("Stop verifier.")
  }

  /** Verifies a given Viper program and returns the result (success, or a sequence of errors)
    *
    * @param program The program to be verified.
    * @return The verification result.
    */
  override def verify(program: sil.Program): VerificationResult = {
    logger.trace("Verify.")

    if (config.printOriginal.getOrElse(false)) {
      println("Input program:\n" + program) // right now, we just print the input program - but you should verify it!
    }

    if(! util.supportedViperSyntax.isSupportedProgram(program)) {
      val failure = ViperFailure(Seq(
        errors.Internal(program, reasons.InternalReason(program, "Input program uses unsupported Viper features!"))
      ))
      logger.error(s"Failure: $failure")
      return failure
    }

    if (config.printDSA.getOrElse(false)) {
      ???
    }

    val defaultOptions = Seq("-smt2") // you may want to pass more options to z3 here, or do it via the command-line argument z3Args

    // here is a reasonable initial configuration for z3. If you're interested, you can check out the options in the Z3 documentation (some are also visible from z3 /pd etc.)
    val smtPrelude =
      """
        |(set-option :print-success false)
        |(set-info :smt-lib-version 2.0)
        |(set-option :AUTO_CONFIG false)
        |(set-option :pp.bv_literals false)
        |(set-option :MODEL.V2 true)
        |(set-option :smt.PHASE_SELECTION 0)
        |(set-option :smt.RESTART_STRATEGY 0)
        |(set-option :smt.RESTART_FACTOR |1.5|)
        |(set-option :smt.ARITH.RANDOM_INITIAL_VALUE true)
        |(set-option :smt.CASE_SPLIT 3)
        |(set-option :smt.DELAY_UNITS true)
        |(set-option :NNF.SK_HACK true)
        |(set-option :smt.MBQI false)
        |(set-option :smt.QI.EAGER_THRESHOLD 100)
        |(set-option :TYPE_CHECK true)
        |(set-option :smt.BV.REFLECT true)
        |; done setting options
        |
        |""".stripMargin

    // You can decide between writing your smt queries directly as Strings (as in the prelude above), or using the scala-smtlib library to build them up as an AST which you then print. Or indeed, you can mix both approaches, as below
    // You will want to change this query to represent the verification conditions for your input program
    val toyQuery = Assert(Core.BoolConst(false)) :: CheckSat() :: List()
    // when printed via "mkString" (to convert the list of Strings into one), this will give the String "(assert false)\n(check-sat)\n"


    // write program to a temporary file (name will be an auto-generated variant of the first parameter string)
    val tmp = File.createTempFile("mytempfile", ".smt2")
    tmp.deleteOnExit()
    val stream = new BufferedOutputStream(new FileOutputStream(tmp))
    val inputString : String = smtPrelude + toyQuery.mkString

    if(config.printSMT.getOrElse(false)) { // print the smt output if the command-line option was specified
      println(inputString)
    }
    stream.write(inputString.getBytes)
    stream.close()


    val z3Path : String = config.z3executable.toOption.get // this option is always set (possibly to the default of "z3"), so "get" is safe

    // gather any Z3 arguments provided on the command-line
    val userProvidedZ3Args: Array[String] = config.z3Args.toOption match {
      case None =>
        Array()
      case Some(args) =>
        args.split(' ').map(_.trim)
    }


    // store the outputs which come from stdout, stderr
    var result: String = ""
    var resulterr: String = ""
    def out(input: java.io.InputStream) {
      result += convertStreamToString(input)
      input.close()
    }
    def err(in: java.io.InputStream) {
      resulterr += convertStreamToString(in)
      in.close()
    }

    // run Z3, passing the tmp file as input:
    val commandToRun = Seq(z3Path) ++ defaultOptions ++ userProvidedZ3Args ++ Seq(tmp.getAbsolutePath)
    commandToRun.run(new ProcessIO(_.close(), out, err)).exitValue() // .exitValue() causes us to block until the process terminates

    assert(resulterr.isEmpty, s"Unknown error response from Z3: $resulterr")

    // Here we parse stdout using the scala-smtlib library. As an alternative,
    // you could read the Z3 response directly and parse it by hand
    // (you should get "unsat", "sat" or "unknown", if everything worked)
    val lexer = new smtlib.lexer.Lexer(new java.io.StringReader(result))
    val parser = new smtlib.parser.Parser(lexer)

    // this is a dummy Viper Assert statement, just for inserting in the error messages below; for real errors, you should insert elements of the program to be verified.
    val dummyAssert : sil.Assert = sil.Assert(sil.TrueLit()())() // Viper (sil) nodes typically take a second argument set, allowing the specification of positional and other auxiliary information. These arguments can be left blank (in which case defaults are inserted), but the parentheses are still necessary.

    // we use a scala-smtlib function to parse the response
    val z3Response: CheckSatResponse  = parser.parseCheckSatResponse

    // Build a corresponding Viper VerificationResult, depending on the response from Z3:
    val viperResult : VerificationResult = z3Response match {
    case CheckSatStatus(SatStatus) | CheckSatStatus(UnknownStatus) => // both unknown and sat should be treated as failed attempts to prove unsat
      ViperFailure(Seq(errors.AssertFailed(dummyAssert,reasons.FeatureUnsupported(dummyAssert, "Actual verification isn't implemented yet"))))

    // usually unsat is the result that means the entailment your checking holds - this is the successful case
    case CheckSatStatus(UnsatStatus) =>
      ViperSuccess

    // some kind of unusual error (e.g. the smt solver didn't understand the input)
    case res@_ =>
      ViperFailure(Seq(errors.Internal(program,reasons.InternalReason(program, "Unexpected response from Z3: " + res.toString))))
    }

    viperResult match {
      case failure: ViperFailure => logger.info(s"Failure: $failure")
      case ViperSuccess => logger.info("Success")
    }
    viperResult
  }


  // utility method for reading the input stream into a String
  def convertStreamToString(is: java.io.InputStream) : String = {
    val s = new java.util.Scanner(is).useDelimiter("\\A")
    if (s.hasNext) s.next() else ""
  }
}
