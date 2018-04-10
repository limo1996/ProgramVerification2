package util

import viper.silver.{ast => sil} // rename package, so that we can write viper.Assert etc. to select the Viper type, rather than the scala-smtlib one
import sil._

// This defines the subset of Viper syntax that your tool should support. Note that the Viper language is much larger; you can assume that the input programs you are dealing with will satisfy isSupportedProgram, as defined here
object supportedViperSyntax {

  def isSupportedProgram(program : sil.Program) : Boolean = program match {
    case sil.Program(domains,fields,functions,predicates,methods) =>
      fields.isEmpty && // we are not dealing with heap-based programs
      predicates.isEmpty && // this is an advanced Viper feature we will not deal with here
      functions.isEmpty && // these are a different kind of function which we don't deal with; we will still support uninterpreted functions declared in domains (Domain Functions)
      domains.forall(d => isSupportedDomain(d)) && //
      methods.forall(m => isSupportedMethod(m))
  }

  def isSupportedDomain(domain : sil.Domain) : Boolean = domain match {
    case sil.Domain(name, functions, axioms, typeVariables) =>
      typeVariables.isEmpty && // we don't support polymorphic domain definitions
      functions.forall(f => f.formalArgs.forall(v => isSupportedType(v.typ)) && isSupportedType(f.typ) && !f.unique /* we don't support the "unique" annotation on functions */) &&
      axioms.forall(ax => isSupportedExpression(ax.exp))
  }

  def isSupportedMethod(method : sil.Method) : Boolean = method match {
    case sil.Method(name, formalArgs, formalReturns, preconditions, postconditions, body) =>
      formalArgs.forall(v => isSupportedType(v.typ)) &&
      formalReturns.forall(v => isSupportedType(v.typ)) &&
      preconditions.forall(p => isSupportedExpression(p)) &&
      postconditions.forall(p => isSupportedExpression(p)) &&
      (body match {
        case Some(seqn) => isSupportedSeqn(seqn)
        case None => false
      })
  }

  def isSupportedSeqn(seqn: Seqn): Boolean = seqn match {
    case Seqn(statements, variableDeclarations) =>
      // Viper sequential composition (which can be treated as a scope) takes a Scala
      // Seq of Stmt elements and variable declarations.
      statements.forall(stm => isSupportedStatement(stm)) &&
      variableDeclarations.forall {
        case decl: LocalVarDecl => isSupportedType(decl.typ)
        case _ => false
      }
  }

  def isSupportedStatement(statement: sil.Stmt) : Boolean = statement match {
    case Assert(expression) => isSupportedExpression(expression)
    case Inhale(expression) => isSupportedExpression(expression) // "Inhale" means "Assume", for this project - a statement "assume A" will result in such an AST node
    case If(condition, ifTrue, ifFalse) => isSupportedExpression(condition) && isSupportedStatement(ifTrue) && isSupportedStatement(ifFalse)
    case LocalVarAssign(variable, value) => isSupportedExpression(value)
    case seqn@Seqn(_, _) => isSupportedSeqn(seqn)
    case While(condition, invariants, body) =>
      isSupportedExpression(condition) && invariants.forall(inv => isSupportedExpression(inv)) && isSupportedStatement(body)
    case LocalVarDeclStmt(decl) => isSupportedType(decl.typ)
    case _ => false
  }

  // Note: the Viper AST doesn't differentiate (in terms of Scala types) between expressions and assertions - both are "Exp"
  def isSupportedExpression(exp : sil.Exp) : Boolean = exp match {
    case IntLit(i) => true
    case BoolLit(b) => true
    case LocalVar(name) => true
    case CondExp(cond, thn, els) => // (cond ? thn : els)
      isSupportedExpression(cond) && isSupportedExpression(thn) && isSupportedExpression(els)
    case Exists(vars, body) => vars.forall(v => isSupportedType(v.typ)) && isSupportedExpression(body)
    case Forall(vars, triggers, body) =>
      vars.forall(v => isSupportedType(v.typ)) && isSupportedExpression(body) && triggers.forall(tr => tr.exps.forall(e => isSupportedExpression(e)))

    //case fa@FuncApp(fname, args) => false // Be warned: FuncApp (which you don't have to deal with) is not the same as DomainFuncApp (which you do)
    case DomainFuncApp(fname, args, typeVariables) =>
      typeVariables.isEmpty && args.forall(a => isSupportedExpression(a))

      // Boolean operators
    case Not(e) => isSupportedExpression(e)
    case Or(l, r) => isSupportedExpression(l) && isSupportedExpression(r)
    case And(l, r) => isSupportedExpression(l) && isSupportedExpression(r)
    case Implies(l, r) => isSupportedExpression(l) && isSupportedExpression(r)

    // Int operations
    case Minus(e) => isSupportedExpression(e)
    case Add(l, r) => isSupportedExpression(l) && isSupportedExpression(r)
    case Sub(l, r) => isSupportedExpression(l) && isSupportedExpression(r)
    case Mul(l, r) => isSupportedExpression(l) && isSupportedExpression(r)
    case Div(l, r) => isSupportedExpression(l) && isSupportedExpression(r)
    case Mod(l, r) => isSupportedExpression(l) && isSupportedExpression(r)

    // Int inequalities
    case LtCmp(l, r) => isSupportedExpression(l) && isSupportedExpression(r)
    case LeCmp(l, r) => isSupportedExpression(l) && isSupportedExpression(r)
    case GtCmp(l, r) => isSupportedExpression(l) && isSupportedExpression(r)
    case GeCmp(l, r) => isSupportedExpression(l) && isSupportedExpression(r)

    // equal/unequal
    case EqCmp(l, r) => isSupportedExpression(l) && isSupportedExpression(r)
    case NeCmp(l, r) => isSupportedExpression(l) && isSupportedExpression(r)

    case _ => false
  }


  def isSupportedType(t: sil.Type) : Boolean = t match {
    case sil.Int | sil.Bool => true // built-in types
    case sil.DomainType(domainName, typeVariables) => typeVariables.isEmpty // domain types
    case _ => false
  }
}
