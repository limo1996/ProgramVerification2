package util

import scala.collection.mutable.ListBuffer
import viper.silver.{ast => sil} // rename package, so that we can write viper.Assert etc. to select the Viper type, rather than the scala-smtlib one
import sil._
import viper.silver.verifier.AbstractVerificationError

case class ViperExpression(error: AbstractVerificationError, expr: sil.Exp)

object WlpStar {

  /*
    * Assumes seqn is body of method that is already converted in DSA and contains only
    * {assert, assume, if(with appended assumes as condition in both branches)} and pre and post conditions appended
    * as first respectively last statements.
    * */
  def wlp(seqn: Seqn) : ListBuffer[sil.Exp] = {
    var delta = new ListBuffer[sil.Exp]()
    delta = wlp_star_seq(seqn, delta)
    delta
  }

  /*
  * Creates delta set from sequence. Takes existing delta set as parameter and returns new one.
  * */
  private def wlp_star_seq(seqn: Seqn,  delta : ListBuffer[sil.Exp]) : ListBuffer[sil.Exp] = seqn match {
    case Seqn(statements, variableDeclarations) => {
      // println("case seqn: " + statements)
      var new_delta = delta
      for(stmt <- statements.reverse){
        new_delta = wlp_star(stmt, new_delta)
      }
      // println("delta: " + new_delta)
      new_delta
    }
    case _ => throw new Exception("wpl_wrapper: no case matched with : " + seqn)
  }

  /*
  * Converts statement according to previous delta set and returns new one.
  * */
  private def wlp_star(stmt : sil.Stmt,  delta : ListBuffer[sil.Exp]) : ListBuffer[sil.Exp] = {
    stmt match {
      case sil.Assert(expression) => {              // in assert we just append to set
        //println("case assert: " + expression)
        var new_delta = delta
        new_delta += expression
        //println("delta: " + new_delta)
        new_delta
      }
      case Inhale(expression) => {                  // in assume we add A1 => A for every A from delta where A1 is expression in assume
        //println("case assume: " + expression)
        var new_delta = new ListBuffer[sil.Exp]()
        for(expr <- delta){
          new_delta += sil.Implies(expression, expr)()
        }
        //println("delta: " + new_delta)
        new_delta
      }
      case If(condition, ifTrue, ifFalse) => {      // in if we just simply convert both blocks from delta and new delta is union of the two
        //println("case if: " + condition)
        wlp_star_seq(ifTrue, delta) ++ wlp_star_seq(ifFalse, delta)
      }
      case _ => throw new Exception("wpl_star: no case matched with : " + stmt)
    }
  }
}