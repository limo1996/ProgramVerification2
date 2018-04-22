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

  private def renameVarUseInExpression(exp: Exp): Exp = {
    val pre: PartialFunction[Node, Node] = {
      case node: LocalVar => renameVarUse(node)
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

  private def transformNodeToDSA[A<:Node](node: A): A = {
    val pre: PartialFunction[Node, Node] = {
      case node: LocalVarAssign =>
        val rhsExp = renameVarUseInExpression(node.rhs)
        Inhale(EqCmp(renameVarDef(node.lhs), rhsExp)())()
      case node: Exp => renameVarUseInExpression(node)
      case node: If => transformIfToDSA(node)
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
    varVersioning = new DSAVarVersioning()
    collectOriginalMethodVarDecls(method)
    versionOriginalVarDecls()

    var transformedBody = transformNodeToDSA(method.body.get)
    transformedBody = transformIfStmts(transformedBody)
    val v1 = getFormalReturnsAfterDSA(method.formalReturns)
    formalRetDecls --= v1
    val v = Seqn(transformedBody.ss, formalRetDecls.toSeq ++ localVarDecls.toSeq)()

    Method(method.name, method.formalArgs, v1, Seq(), Seq(), Some(v))()
  }
}
