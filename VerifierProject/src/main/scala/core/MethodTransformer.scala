package core

import util.DSAVarVersioning
import viper.silver.ast._

import scala.collection.mutable

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

  private def transformNode[A<:Node](node: A): A = {
    val pre: PartialFunction[Node, Node] = {
      case node: LocalVarAssign =>
        val rhsExp = renameVarUseInExpression(node.rhs)
        Inhale(EqCmp(renameVarDef(node.lhs), rhsExp)())()
      case node: Exp => renameVarUseInExpression(node)
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

    val transformedBody = transformNode(method.body.get)
    val v1 = getFormalReturnsAfterDSA(method.formalReturns)
    formalRetDecls --= v1
    val v = Seqn(transformedBody.ss, formalRetDecls.toSeq ++ localVarDecls.toSeq)()

    Method(method.name, method.formalArgs, v1, Seq(), Seq(), Some(v))()
  }
}
