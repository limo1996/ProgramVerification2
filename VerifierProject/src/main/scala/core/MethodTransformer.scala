package core

import util.DSAVarVersioning
import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.Traverse

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

class MethodTransformer {
  private var varVersioning: DSAVarVersioning = _
  private var formalArgDecls: Set[LocalVarDecl] = _
  private var originalFormalRetDecls: Set[LocalVarDecl] = _
  private var originalLocalVarDecls: Set[LocalVarDecl] = _
  private var formalRetDecls: mutable.Set[LocalVarDecl] = _
  private var localVarDecls: mutable.Set[LocalVarDecl] = _

  // TODO ignore quantified variables in foralls and exists
  private def getLocalVarDecls(stmt: Stmt): Set[LocalVarDecl] = {
    val decls = mutable.Set[LocalVarDecl]()
    stmt.visit({ case stm: LocalVarDecl => decls.add(stm) })
    decls.toSet
  }

  private def getLocalVarAssigns(stmt: Stmt): Set[LocalVar] = {
    val vars = mutable.Set[LocalVar]()
    stmt.visit({ case LocalVarAssign(lvar, _) => vars += lvar })
    vars.toSet
  }

  private def collectOriginalMethodVarDecls(method: Method): Unit = {
    formalArgDecls = method.formalArgs.toSet
    originalFormalRetDecls = method.formalReturns.toSet
    originalLocalVarDecls = getLocalVarDecls(method.body.get)
  }

  def getMethodVarDecls: Seq[LocalVarDecl] = {
    formalArgDecls.toSeq ++ formalRetDecls.toSeq ++ localVarDecls.toSeq
  }

  private def versionOriginalVarDecls(): Unit = {
    for (decl <- formalArgDecls) varVersioning.addIgnoredVar(decl.name)

    formalRetDecls = mutable.Set[LocalVarDecl]()
    for (decl <- originalFormalRetDecls) {
      val newVarName = varVersioning.getNewIdentifier(decl.name)
      formalRetDecls += LocalVarDecl(newVarName, decl.typ)()
    }

    localVarDecls = mutable.Set[LocalVarDecl]()
    for (decl <- originalLocalVarDecls) {
      val newVarName = varVersioning.getNewIdentifier(decl.name)
      localVarDecls += LocalVarDecl(newVarName, decl.typ)()
    }
  }

  private def renameVarDef(localVar: LocalVar): LocalVar = {
    val newLocalVarName = varVersioning.getNewIdentifier(localVar.name)

    // Distinguish between renaming of formal return and of local variable
    if (originalFormalRetDecls.map(ret => ret.name).contains(localVar.name)) {
      formalRetDecls += LocalVarDecl(newLocalVarName, localVar.typ)()
    } else {
      localVarDecls += LocalVarDecl(newLocalVarName, localVar.typ)()
    }

    LocalVar(newLocalVarName)(localVar.typ)
  }

  private def renameVarUse(localVar: LocalVar): LocalVar = {
    LocalVar(varVersioning.getLastIdentifier(localVar.name))(localVar.typ)
  }

  private def renameVarUseInExpression(exp: Exp, quantifiedVars: Seq[String]=Seq()): Exp = {
    val pre: PartialFunction[Node, Node] = {
      case f@Forall(variables, triggers: Seq[Trigger], fexp) =>
        val newQuantifiedVars = quantifiedVars ++ variables.map(d => d.name)
        Forall(variables,
          triggers.map(t => Trigger(t.exps.map(texp => renameVarUseInExpression(texp, newQuantifiedVars)))(t.pos, t.info)),
          renameVarUseInExpression(fexp, newQuantifiedVars))(f.pos, f.info)
      case ex@Exists(variables, exexp) =>
        val newQuantifiedVars = quantifiedVars ++ variables.map(d => d.name)
        Exists(variables, renameVarUseInExpression(exexp, newQuantifiedVars))(ex.pos, ex.info)
      case node: LocalVar =>
        if (quantifiedVars.contains(node.name)) node
        else renameVarUse(node)
    }

    exp.transform(pre)
  }

  private def transformIfStmts[A<:Node](node: A): A = {
    val pre: PartialFunction[Node, Node] = {
      case If(cond, thn, els) =>
        If(cond,
          Seqn(Seq(Inhale(cond)()) ++ thn.ss, thn.scopedDecls)(),
          Seqn(Seq(Inhale(Not(cond)())()) ++ els.ss, els.scopedDecls)()
        )()
    }
    node.transform(pre, Traverse.BottomUp)
  }

  private def transformAssertStmts[A<:Node](node: A): A = {
    val pre: PartialFunction[Node, Node] = {
      case node@Assert(exp) => Seqn(Seq(node, Inhale(exp)()), Seq())()
    }
    node.transform(pre)
  }

  private def transformPreConditions(methodBody: Seqn, pres: Seq[Exp]): Seqn = {
    val transformedPres = pres.map(p => renameVarUseInExpression(p))
    Seqn(transformedPres.map(p => Inhale(p)()) ++ methodBody.ss, Seq())()
  }

  private def transformPostConditions(methodBody: Seqn, posts: Seq[Exp]): Seqn = {
    val transformedPosts = posts.map(p => renameVarUseInExpression(p))
    Seqn(methodBody.ss ++ transformedPosts.map(p => Assert(p)(p.pos, p.info)), Seq())()
  }

  private def transformIfToDSA(ifStmt: If): If = {
    // Transform the if condition and take a snapshot of the variables' versions.
    val transformedIfCondition = renameVarUseInExpression(ifStmt.cond)
    val snapshot = varVersioning.getSnapshot

    // Transform the then branch, take a snapshot of it and revert to the snapshot before the conversion.
    val transformedThenBranch = transformNodeToDSA(ifStmt.thn)
    val thenSnapshot = varVersioning.getSnapshot
    varVersioning.revertToSnapshot(snapshot)

    // Transform the else branch, take a snapshot of it and revert to the snapshot before the conversion.
    val transformedElseBranch = transformNodeToDSA(ifStmt.els)
    val elseSnapshot = varVersioning.getSnapshot
    varVersioning.revertToSnapshot(snapshot)

    val extraThenAssigns = ListBuffer[Inhale]()
    val extraElseAssigns = ListBuffer[Inhale]()

    // Check every variable that is assigned in the then or the else branch.
    for (localVar <- getLocalVarAssigns(ifStmt.thn) ++ getLocalVarAssigns(ifStmt.els)) {
      val varName = localVar.name
      val varType = localVar.typ
      val versionInThenBranch = thenSnapshot.getOrElse(varName, 0)
      val versionInElseBranch = elseSnapshot.getOrElse(varName, 0)
      val thenIdentifier = varVersioning.constructIdentifier(varName, versionInThenBranch)
      val elseIdentifier = varVersioning.constructIdentifier(varName, versionInElseBranch)

      // If a variable is assigned different number of times in the two branches, add an extra assignment to the
      // behind branch, assigning the latest version of the behind branch to the latest version of the ahead one.
      if (versionInElseBranch > versionInThenBranch) {
        extraThenAssigns += Inhale(EqCmp(LocalVar(elseIdentifier)(varType), LocalVar(thenIdentifier)(varType))())()
      } else if (versionInThenBranch > versionInElseBranch) {
        extraElseAssigns += Inhale(EqCmp(LocalVar(thenIdentifier)(varType), LocalVar(elseIdentifier)(varType))())()
      }

      // Set the variable's version to the max of the two branches.
      varVersioning.setVersion(varName, math.max(versionInThenBranch, versionInElseBranch))
    }

    If(transformedIfCondition,
      Seqn(transformedThenBranch.ss ++ extraThenAssigns, Seq())(),
      Seqn(transformedElseBranch.ss ++ extraElseAssigns, Seq())()
    )()
  }

  private def transformWhileToDsa(whileStmt: While): Seqn = {
    val invariantsToEstablish = whileStmt.invs.map(inv => renameVarUseInExpression(inv))

    // Havoc of variables assigned in the loop is simulated by increasing their version
    val varsAssigned = getLocalVarAssigns(whileStmt.body).map(v => v.name) -- whileStmt.body.scopedDecls.map(sv => sv.name)
    for (v <- varsAssigned) varVersioning.getNewIdentifier(v)

    // Take snapshot of the current version of vars
    val snapshot = varVersioning.getSnapshot

    val invariantsToAssume = whileStmt.invs.map(inv => renameVarUseInExpression(inv))
    val transformedLoopCondition = renameVarUseInExpression(whileStmt.cond)
    val transformedLoopBody = transformNodeToDSA(whileStmt.body)
    val invariantsToPreserve = whileStmt.invs.map(inv => renameVarUseInExpression(inv))

    def conjunctExpressions(expressions: Seq[Exp]): Exp = expressions match {
      case Seq() => TrueLit()()
      case Seq(t) => t
      case _ => expressions.reduce((exp1, exp2) => And(exp1, exp2)())
    }

    val transformed = Seqn(
      invariantsToEstablish.map(inv => Assert(inv)()) ++
      Seq(
        If(transformedLoopCondition,
          Seqn(Seq(Inhale(And(conjunctExpressions(invariantsToAssume), transformedLoopCondition)())(), transformedLoopBody)
              ++ invariantsToPreserve.map(inv => Assert(inv)())
              ++ Seq(Inhale(FalseLit()())())
          , Seq())(),
          Seqn(Seq(Inhale(And(conjunctExpressions(invariantsToAssume), Not(transformedLoopCondition)())())()), Seq())()
        )()
      ), Seq())()

    // Reset variables' version to the ones after the havoc, as the traces of the loop body are killed
    varVersioning.revertToSnapshot(snapshot)

    transformed
  }

  private def transformNodeToDSA[A<:Node](node: A): A = {
    val pre: PartialFunction[Node, Node] = {
      case node: LocalVarAssign =>
        val rhsExp = renameVarUseInExpression(node.rhs)
        Inhale(EqCmp(renameVarDef(node.lhs), rhsExp)())()
      case node: Exp => renameVarUseInExpression(node)
      case node: If => transformIfToDSA(node)
      case node: While => transformWhileToDsa(node)
    }

    node.transform(pre)
  }

  private def getFormalReturnsAfterDSA(originalFormalReturns: Seq[LocalVarDecl]): Seq[LocalVarDecl] = {
    val newFormalReturns = mutable.Set[LocalVarDecl]()
    for (decl <- originalFormalReturns) {
      val lastVarName = varVersioning.getLastIdentifier(decl.name)
      newFormalReturns += LocalVarDecl(lastVarName, decl.typ)()
    }
    newFormalReturns.toSeq
  }

  def transform(method: Method): Method = {
    errorInfoTagger = new ErrorInfoTagger
    varVersioning = new DSAVarVersioning()
    collectOriginalMethodVarDecls(method)
    versionOriginalVarDecls()

    var transformedBody = transformNodeToDSA(method.body.get)
    transformedBody = transformIfStmts(transformedBody)
    transformedBody = transformPreConditions(transformedBody, method.pres)
    transformedBody = transformPostConditions(transformedBody, method.posts)
    transformedBody = transformAssertStmts(transformedBody)
    val v1 = getFormalReturnsAfterDSA(method.formalReturns)
    formalRetDecls --= v1
    val v = Seqn(transformedBody.ss, formalRetDecls.toSeq ++ localVarDecls.toSeq)()

    Method(method.name, method.formalArgs, v1, Seq(), Seq(), Some(v))()
  }
}
