package core

import viper.silver.ast.Program
import viper.silver.verifier.errors._
import viper.silver.verifier.reasons._
import viper.silver.verifier._

trait BareboneVerifier extends Verifier{
  // The trait used in Viper is rather complicated - we don't need all of the flexibility here, so we define some features with default values
  override def version: String = "1.0.0"
  override def buildVersion: String = "1.0.0"
  override def copyright: String = ""
  override def debugInfo(info: Seq[(String, Any)]) = {}
  override def dependencies = Seq() // this is unused

  private var _config: Config = _
  final def config = _config

  override def parseCommandLine(args: Seq[String]): Unit = { _config = new Config(args,name)}

  /** Only needed if you want to do something special on (first) invocation of the verifier
    */
  override def start(): Unit = {}

  /** Verifies a given Viper program and returns the result (success, or a sequence of errors)
    *
    * @param program The program to be verified.
    * @return The verification result.
    */
  override def verify(program: Program): VerificationResult

  /** Stops the verifier. Only needed if you have to perform some special clean-up on closing the verifier
    */
  override def stop(): Unit = {}
}
