package core

import java.io.{BufferedOutputStream, File, FileOutputStream}

import ch.qos.logback.classic.Logger
import smtlib.parser.Commands
import smtlib.parser.Commands._
import smtlib.parser.CommandsResponses._
import smtlib.theories.Core
import smtlib.parser.Terms._
import viper.silver.verifier.AbstractVerificationError
import viper.silver.verifier.{VerificationResult, errors, reasons, Failure => ViperFailure, Success => ViperSuccess}
import viper.silver.{ast => sil}
import sil._

import smtlib.parser.Terms
import util._

import scala.collection.mutable.{ArrayBuffer, HashMap, ListBuffer}
import scala.sys.process.{ProcessIO, _}


// The entry point of the program when running from a command line.
// You should not need to change this object. The most important class
// for you is the MyVerifier class below.
object Main extends MyVerifierFrontend {

  def main(args: Array[String]) {
    try {
      execute(args)
        // Will call createVerifier and configureVerifier (already defined in
        // MyVerifierFrontend), and then verify the program (see verify method
        // in MyVerifier)
    } finally {
      verifierInstance.stop()
        // also doesn't do anything in the current implementation – only
        // needed if you have to "clean-up" in some way
    }
  }

}

// This is where you will do most of your work:

class MyVerifier(private val logger: Logger) extends BareboneVerifier {
  // You can change the log level that is used when running from a command line
  // in the MyVerifierFrontend constructor that takes no arguments.

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

    // should be used for statements error pairing
    var mapping = new HashMap[Int, AbstractVerificationError]()

    // TMP
    /*program.methods.forall(
      m => m match {
        case sil.Method(name, formalArgs, formalReturns, preconditions, postconditions, body)
          => body match {
          case Some(seqn) => {println(wlp(seqn)); true}
        }
      }
    )*/

    if(! util.supportedViperSyntax.isSupportedProgram(program)) {
      val failure = ViperFailure(Seq(
        errors.Internal(program, reasons.InternalReason(program, "Input program uses unsupported Viper features!"))
      ))
      logger.error(s"Failure: $failure")
      return failure
    }

    // unfold loops, add pre and post conditions, DSA etc.
    val transformer = new MethodTransformer()
    val methods = program.methods.map(m => transformer.transform(m))

    // print converted version if requested
    if (config.printDSA.getOrElse(false)) {
      methods.foreach(m => println(m))
    }

    var failures = new ArrayBuffer[AbstractVerificationError]()
    // collect axioms from all
    var axioms = program.domains.flatMap(d =>
      d.axioms.map(a => ViperToSMTConverter.convertAxiom(a)))


    methods.foreach(m => {
      if(m.body.isDefined) {
        var method_body = m.body.get
        var declarations = collectDeclarations(program, m)

        var expressions = WlpStar.wlp(method_body)
        var loc_failures = new ArrayBuffer[AbstractVerificationError]()
        expressions.foreach(e => {
          val error = checkForSuccess(e, axioms, declarations, program)
          if (error.isDefined)
            failures += error.get
          true
        })

        failures ++= loc_failures
      }
    })


    // if we detected errors than return failure with them otherwise success
    if(failures.nonEmpty)
      ViperFailure(failures)
    else
      ViperSuccess
  }

  /*
   * Collects declarations from viper. It includes:
   *  - local variables defined within the scope of method
   *  - domains as new sorts
   *  - functions in domains that are treted as uninterpreted functions
   *
   *  @param  program Viper ast for input program
   *  @param  method  Method from which we collect local vars
   *  @return Sequence of converted commands(declarations in SMT)
   */
  def collectDeclarations(program: sil.Program, method: sil.Method) : Seq[Command] = {
    var locals = getLocals(method) ++ method.formalArgs ++ method.formalReturns

    // collect locals
    locals.map(l => DeclareConst(SSymbol("sort_" + l.name), ViperToSMTConverter.getSort(l.typ))) ++
      // collect domains as new sorts
      program.domains.map(d => DeclareSort(SSymbol("sort_" + d.name), 0)) ++
        // collect functions of domains as unint. func.
        program.domains.flatMap(d => d.functions.map(f =>
          DeclareFun(SSymbol(ViperToSMTConverter.func_prefix(f.name)),
                    f.formalArgs.map(fa => ViperToSMTConverter.getSort(fa.typ)),
                    ViperToSMTConverter.getSort(f.typ))))

  }

  /**
    * Extracts local var declarations from method body.
    *
    * @param method from which will be local declarations extracted
    * @return       Sequence of local variable declarations in method body
    */
  def getLocals(method: sil.Method) : Seq[LocalVarDecl] = {
    method.body.get.scopedDecls.map(d => d.asInstanceOf[LocalVarDecl])
  }

  /*
   * Checks given expression together with declarions and axioms with smt solver. In case of error returns Some[error] otherwise None.
   *
   * @param expr          Pair of expression to evaluate and error it can cause
   * @param axioms        Converted axioms of viper program
   * @param declarations  Sequence of variable and funcion declarations
   * @param program       Used for creating internal error
   * @return              Verification error if any
   */
  def checkForSuccess(expr: SMTExpression, axioms: Seq[Term], declarations: Seq[Command], program: sil.Program) : Option[AbstractVerificationError] = {
    // each axiom is precodition to expression
    val query = axioms.map(a => Commands.Assert(a)) ++ (Commands.Assert(Core.Not(expr.term)) :: CheckSat() :: List())
    val smt_result = runSMT(declarations, query)
    smt_result match {
      case CheckSatStatus(SatStatus) | CheckSatStatus(UnknownStatus) => // both unknown and sat should be treated as failed attempts to prove unsat
        Some(expr.error)
      // usually unsat is the result that means the entailment your checking holds - this is the successful case
      case CheckSatStatus(UnsatStatus) =>
        None

      // some kind of unusual error (e.g. the smt solver didn't understand the input)
      case res@_ =>
        Some(errors.Internal(program, reasons.InternalReason(program, "Unexpected response from Z3: " + res.toString)))
    }
  }
  /*
   *  Runs Z3 with provided variable and function declarations and given sequence of queries.
   *
   *  @param declarations   Sequence of variable and funcion declarations
   *  @param query          Sequence of queries (ie. asserts) to check for
   *  @return               Result of SMT
   */
  def runSMT(declarations: Seq[Command], query: Seq[Command]) : CheckSatResponse = {
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

    // write program to a temporary file (name will be an auto-generated variant of the first parameter string)
    val tmp = File.createTempFile("mytempfile", ".smt2")
    tmp.deleteOnExit()
    val stream = new BufferedOutputStream(new FileOutputStream(tmp))
    val inputString : String = smtPrelude + declarations.mkString + query.mkString

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
    parser.parseCheckSatResponse
  }
  // utility method for reading the input stream into a String
  def convertStreamToString(is: java.io.InputStream) : String = {
    val s = new java.util.Scanner(is).useDelimiter("\\A")
    if (s.hasNext) s.next() else ""
  }
}