package util

import scala.collection.mutable.ListBuffer
import viper.silver.ast._
import viper.silver.ast

import smtlib.parser.Terms
import smtlib.parser.Terms._
import smtlib.parser.Commands._
import smtlib.parser.CommandsResponses._
import smtlib.theories.Core
import smtlib.theories.Ints
import viper.silver.verifier.AbstractVerificationError

object ViperToSMTConverter {

  /*
   * Converts provided axiom into SMT syntax.
   *
   * Remark:  We need to prefix variables, sorts and functions because otherwise they can have
   *          names like select which are reserved in SMT solver...
   *
   * @param ax  viper.silver.ast.DomainAxiom node
   * @return    converted node in SMT
   */
  def convertAxiom(ax: DomainAxiom) : Terms.Term = {
    exprToTerm(ax.exp)
  }

  /*
   * Converts silver expression into SMT one
   *
   * @param expr viper.silver.ast.Exp node
   * @return     converted node in SMT
   */
  def exprToTerm(expr : Exp) : Terms.Term = {
    expr match {
      // literals
      case IntLit(i) => Ints.NumeralLit(i)
      case BoolLit(b) => Core.BoolConst(b)

      // local var
      case LocalVar(name) => quantIdent(var_prefix(name))

      // iff
      case CondExp(cond, thn, els) => Core.ITE(exprToTerm(cond), exprToTerm(thn), exprToTerm(els))

      // existance quantifier
      case e@ast.Exists(vars, body) => Terms.Exists(createSortedVar(vars.head),
        vars.tail.map(v => createSortedVar(v)), exprToTerm(body))

      // forall quantifier
      case f@ast.Forall(vars, triggers, body) => Terms.Forall(createSortedVar(vars.head),
        vars.tail.map(v => createSortedVar(v)), add_triggers(exprToTerm(body), triggers, f.autoTrigger.triggers))

      // a function that is defined in some domain
      case DomainFuncApp(fname, args, typeVariables) => {
        val ident = quantIdent(func_prefix(fname))
        if (args.isEmpty)   //a function application with no argument is a qualified identifier
          return ident
        Terms.FunctionApplication(ident, args.map(a => exprToTerm(a)))
      }

      // Boolean operators => Core package
      case ast.Not(e) => Core.Not(exprToTerm(e))
      case Or(l, r) => Core.Or(exprToTerm(l), exprToTerm(r))
      case And(l, r) => Core.And(exprToTerm(l), exprToTerm(r))
      case Implies(l, r) => Core.Implies(exprToTerm(l), exprToTerm(r))

      // Int operations => Int package
      case Minus(e) => Ints.Neg(exprToTerm(e))
      case Add(l, r) => Ints.Add(exprToTerm(l), exprToTerm(r))
      case Sub(l, r) => Ints.Sub(exprToTerm(l), exprToTerm(r))
      case Mul(l, r) => Ints.Mul(exprToTerm(l), exprToTerm(r))
      case Div(l, r) => Ints.Div(exprToTerm(l), exprToTerm(r))
      case Mod(l, r) => Ints.Mod(exprToTerm(l), exprToTerm(r))

      // Int inequalities
      case LtCmp(l, r) => Ints.LessThan(exprToTerm(l), exprToTerm(r))
      case LeCmp(l, r) => Ints.LessEquals(exprToTerm(l), exprToTerm(r))
      case GtCmp(l, r) => Ints.GreaterThan(exprToTerm(l), exprToTerm(r))
      case GeCmp(l, r) => Ints.GreaterEquals(exprToTerm(l), exprToTerm(r))

      // equal/unequal
      case EqCmp(l, r) => Core.Equals(exprToTerm(l), exprToTerm(r))
      case NeCmp(l, r) => Core.Not(Core.Equals(exprToTerm(l), exprToTerm(r)))

      case _ => throw new Exception("ViperToSMTConverter.exprToTerm: Unsupported case: " + expr)
    }
  }

  /*
   * shortcut for creating quantified ident.
   */
  def quantIdent(name: String) = QualifiedIdentifier(simpleIdent(name))

  def simpleIdent(name: String) = SimpleIdentifier(SSymbol(name))

  /*
   * prefixes the function name
   */
  def func_prefix(fname: String) = "func_" + fname

  /*
   * prefixes the variable name
   */
  def var_prefix(vname: String) = "var_" + vname

  /*
   * prefixes the sort name
   */
  def sort_prefix(sname: String) = "sort_" + sname

  /*
   * Adds prioritly triggers if no are provided then tries to add implicit triggers
   */
  def add_triggers(term: Terms.Term, triggers: Seq[Trigger], impl_triggers: Seq[Trigger]) : Terms.Term = {
    if(triggers.nonEmpty)
      return Terms.AnnotatedTerm(term, toAttribute(triggers.head), triggers.tail.map(t => toAttribute(t)))

    if(impl_triggers.nonEmpty)
      return Terms.AnnotatedTerm(term, toAttribute(impl_triggers.head), impl_triggers.tail.map(t => toAttribute(t)))

    return term
  }

  /*
   * Converts trigger to attribute.
   */
  def toAttribute(trigger: Trigger) = Attribute( SKeyword("pattern"),
      Option(SList(trigger.exps.map(e => exprToTerm(e).asInstanceOf[SExpr]).toList)))

  /*
   * Creates sorted variable from LocalVarDecl.
   */
  def createSortedVar(loc_var: LocalVarDecl) = Terms.SortedVar(SSymbol(var_prefix(loc_var.name)), getSort(loc_var.typ))

  /*
   * gets sort according to type
   */
  def getSort(sort: Type) : Terms.Sort = sort match {
    case Int => Sort(simpleIdent("Int"))
    case Bool => Sort(simpleIdent("Bool"))
    case dt: DomainType => Sort(simpleIdent(sort_prefix(dt.domainName)))
    case _ => throw new Exception("getSort: Unsupported case: " + sort)
  }
}