package util

import viper.silver.ast._
import viper.silver.verifier.AbstractVerificationError
import viper.silver.verifier.errors.{AssertFailed, LoopInvariantNotEstablished, LoopInvariantNotPreserved, PostconditionViolated}
import viper.silver.verifier.reasons.AssertionFalse

case class ErrorInfo(error: AbstractVerificationError, exp: Exp) extends Info {
  lazy val comment: Seq[String] = Nil
}

/**
  * Adds error information to expressions of interest of a method, which are expressions in post conditions,
  * assertions and loop invariants.
  */
class ErrorInfoTagger {

  def addErrorInfo(method: Method): Method = {
    Method(method.name, method.formalArgs, method.formalReturns, method.pres,
      addErrorInfo(method.posts, method), Option(addErrorInfo(method.body.get)))(method.pos, method.info)
  }

  /**
    * Adds error information to the post condition expressions of a method.
    * @param postConditions is a sequence of the method's post condition expressions.
    * @param method is the ast node of the method, which is provided to the PostconditionViolated error.
    * @return a sequence of post condition expressions tagged with error information.
    */
  private def addErrorInfo(postConditions: Seq[Exp], method: Method): Seq[Exp] = {
    postConditions.map(post =>
      propagateErrorInfoToExpr(post, ErrorInfo(PostconditionViolated(post, method, AssertionFalse(post)), post)))
  }

  /**
    * Transforms an ast node by adding error information to it and to sub nodes of interest.
    * Nodes of interest are assertions' expressions and loop invariants' expressions.
    * In the case of loop invariants we do not specify the error yet, as it can be either LoopInvariantNotEstablished
    * or LoopInvariantNotPreserved error.
    * @param node is an ast node that lacks error information.
    * @return transformed ast node.
    */
  private def addErrorInfo[A<:Node](node: A): A = {
    val pre: PartialFunction[Node, Node] = {
      case seq@Seqn(ss, scopedDecls) =>
        Seqn(ss.map(s => addErrorInfo(s)), scopedDecls)(seq.pos, seq.info)
      case ass@Assert(e) =>
        Assert(propagateErrorInfoToExpr(e, ErrorInfo(AssertFailed(ass, AssertionFalse(e)), e)))(ass.pos, ass.info)
      case iff@If(cond, thn, els) =>
        If(cond, addErrorInfo(thn), addErrorInfo(els))(iff.pos, iff.info)
      case whi@While(cond, invs, body) =>
        val taggedInvariants = invs.map(inv => propagateErrorInfoToExpr(inv, ErrorInfo(null, inv)))
        While(cond, taggedInvariants, addErrorInfo(body))(whi.pos, whi.info)
    }

    node.transform(pre)
  }

  private def propagateErrorInfoToExpr(exp: Exp, errorInfo: ErrorInfo): Exp = exp match {
    case IntLit(i) => IntLit(i)(exp.pos, errorInfo)
    case BoolLit(b) => BoolLit(b)(exp.pos, errorInfo)
    case LocalVar(name) => LocalVar(name)(exp.typ, exp.pos, errorInfo)
    case CondExp(cond, thn, els) => CondExp(cond, thn, els)(exp.pos, errorInfo)
    case Exists(vars, body) => Exists(vars, body)(exp.pos, errorInfo)
    case Forall(vars, triggers, body) => Forall(vars, triggers, body)(exp.pos, errorInfo)
    case dfa@DomainFuncApp(name, args, typeVariables) =>
      DomainFuncApp(name, args, typeVariables)(dfa.pos, errorInfo, dfa.typ, dfa.formalArgs, dfa.domainName, dfa.errT)

    case Not(e) => Not(e)(exp.pos, errorInfo)
    case Or(l, r) => Or(l, r)(exp.pos, errorInfo)
    case And(l, r) => And(l, r)(exp.pos, errorInfo)
    case Implies(l, r) => Implies(l, r)(exp.pos, errorInfo)

    case Minus(e) => Minus(e)(exp.pos, errorInfo)
    case Add(l, r) => Add(l, r)(exp.pos, errorInfo)
    case Sub(l, r) => Sub(l, r)(exp.pos, errorInfo)
    case Mul(l, r) => Mul(l, r)(exp.pos, errorInfo)
    case Div(l, r) => Div(l, r)(exp.pos, errorInfo)
    case Mod(l, r) => Mod(l, r)(exp.pos, errorInfo)

    case LtCmp(l, r) => LtCmp(l, r)(exp.pos, errorInfo)
    case LeCmp(l, r) => LeCmp(l, r)(exp.pos, errorInfo)
    case GtCmp(l, r) => GtCmp(l, r)(exp.pos, errorInfo)
    case GeCmp(l, r) => GeCmp(l, r)(exp.pos, errorInfo)

    case EqCmp(l, r) => EqCmp(l, r)(exp.pos, errorInfo)
    case NeCmp(l, r) => NeCmp(l, r)(exp.pos, errorInfo)
  }

  def addInvariantNotEstablishedErrorInfo(invExp: Exp): Exp = {
    val origInvExp = invExp.info.asInstanceOf[ErrorInfo].exp  // original invariant expression (unaffected by renaming, etc.)
    propagateErrorInfoToExpr(invExp, ErrorInfo(LoopInvariantNotEstablished(origInvExp, AssertionFalse(origInvExp)), origInvExp))
  }

  def addInvariantNotPreservedErrorInfo(invExp: Exp): Exp = {
    val origInvExp = invExp.info.asInstanceOf[ErrorInfo].exp  // original invariant expression (unaffected by renaming, etc.)
    propagateErrorInfoToExpr(invExp, ErrorInfo(LoopInvariantNotPreserved(origInvExp, AssertionFalse(origInvExp)), origInvExp))
  }
}
