package core

import viper.silver.frontend.SilFrontendConfig
import org.rogach.scallop._

/**
  * You can define extra command-line arguments here (instead of opt[Boolean] you can also write opt[Int], opt[String] etc. for different parameter types)
  * Each "val" created using opt[T] will be treated as a command-line argument by the scallop command-line parsing framework
  * After processing, each command-line option will result in a field of the "config" field of the Verifier object
  */

class Config(args: Seq[String], verifierName: String) extends SilFrontendConfig(args, verifierName) {

  val printOriginal = opt[Boolean]("printOriginal",
    descr = "Print the original program",
    default  = Some(false)
  )

  val printDSA = opt[Boolean]("printDSA",
    descr = "Print the program converted into the DSA form",
    default  = Some(false)
  )

  val printSMT = opt[Boolean]("printSMT",
    descr = "Print the generated SMT output",
    default  = Some(false)
  )

  val useSP = opt[Boolean]("useSP",
    descr = "Use strongest postconditions instead of weakest preconditions.",
    default  = Some(false)
  )

  val checkWLPEquivalentSP = opt[Boolean]("checkWLPEquivalentSP",
    descr = "Check that WLP conditions are equivalent to SP.",
    default  = Some(false)
  )

  val z3executable = opt[String]("z3Exe",
    descr = "Manually-specified full path to Z3.exe executable (default: z3)",
    default = Some("z3"),
    noshort = true
  )

  val z3Args = opt[String]("z3Args",
    descr = "Command-line arguments which should be forwarded to Z3. ",
    default = None,
    noshort = true
  )

  verify() // this should always be here - it does some built-in preprocessing on the command-line options defined here
}


