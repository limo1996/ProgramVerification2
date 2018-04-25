package util

import scala.collection.mutable.ListBuffer
import viper.silver.{ast => sil} // rename package, so that we can write viper.Assert etc. to select the Viper type, rather than the scala-smtlib one
import sil._
import viper.silver.verifier.AbstractVerificationError
import smtlib.parser.Terms
import smtlib.theories.Core

case class SMTExpression(error: AbstractVerificationError, term: Terms.Term)

object WlpStar {

  /*
    * Assumes seqn is body of method that is already converted in DSA and contains only
    * {assert, assume, if(with appended assumes as condition in both branches)} and pre and post conditions appended
    * as first respectively last statements.
    * */
  def wlp(seqn: Seqn) : ListBuffer[SMTExpression] = {
    var delta = new ListBuffer[SMTExpression]()
    delta = wlp_star_seq(seqn, delta)
    delta
  }

  /*
  * Creates delta set from sequence. Takes existing delta set as parameter and returns new one.
  * */
  private def wlp_star_seq(seqn: Seqn,  delta : ListBuffer[SMTExpression]) : ListBuffer[SMTExpression] = seqn match {
    case Seqn(statements, variableDeclarations) => {
      var new_delta = delta
      for(stmt <- statements.reverse){
        new_delta = wlp_star(stmt, new_delta)
      }
      new_delta
    }
    case _ => throw new Exception("wpl_wrapper: no case matched with : " + seqn)
  }

  /*
  * Converts statement according to previous delta set and returns new one.
  * */
  private def wlp_star(stmt : sil.Stmt,  delta : ListBuffer[SMTExpression]) : ListBuffer[SMTExpression] = {
    stmt match {
      // in assert we just append converted smt expression to delta
      case sil.Assert(expression) => {
        var new_delta = delta
        new_delta += SMTExpression(expression.info.asInstanceOf[ErrorInfo].error, ViperToSMTConverter.exprToTerm(expression))
        new_delta
      }

      // in assume we add A1 => A for every A from delta where A1 is expression in assume
      // however first we need to convert A1 to term and propagate error to newly created SMTExpression
      case Inhale(expression) => {
        var new_delta = new ListBuffer[SMTExpression]()
        val expr_term = ViperToSMTConverter.exprToTerm(expression)
        for(expr <- delta){
          new_delta += SMTExpression(expr.error,
                          Core.Implies(expr_term, expr.term))
        }
        new_delta
      }

      // in we just simply convert both blocks from delta and return them
      case If(condition, ifTrue, ifFalse) => {
        var new_delta = new ListBuffer[SMTExpression]()
        new_delta ++= wlp_star_seq(ifTrue, delta)
        new_delta ++= wlp_star_seq(ifFalse, delta)
        new_delta
      }

      case s@Seqn(_,_) => wlp_star_seq(s, delta)
      case _ => throw new Exception("wpl_star: no case matched with : " + stmt)
    }
  }
}