package util

import java.nio.file.Path

import viper.silver.ast.Program
import viper.silver.frontend.{SilFrontend, TranslatorState}
import viper.silver.verifier.AbstractError

class BasicFrontend extends SilFrontend {
  def createVerifier(fullCmd: _root_.scala.Predef.String) = ??? // you don't need to implement this - we create the verifier directly

  def configureVerifier(args: Seq[String]) = ??? // you don't need to implement this - we configure the verifier (from the command-line) directly

  def translate(viperFile: Path): (Option[Program], Seq[AbstractError]) = {
    _verifier = None
    _state = TranslatorState.Initialized

    reset(viperFile)
    translate()

    (_program, _errors)
  }
}