package core

import org.scalatest.{BeforeAndAfter, FunSuite}
import viper.silver.ast._

class MethodTransformerTests extends FunSuite with BeforeAndAfter {
  var transformer: MethodTransformer = _

  def createTestMethod(name: String, formalArgs: Seq[LocalVarDecl] = Seq(), formalReturns: Seq[LocalVarDecl] = Seq(),
                        pres: Seq[Exp] = Seq(), posts: Seq[Exp] = Seq(), body: Option[Seqn]): Method = {
    Method(name, formalArgs, formalReturns, pres, posts, body)()
  }

  before {
    transformer = new MethodTransformer()
  }

  def compareMethod(m1: Method, m2: Method): Unit = {
    val m1Body = m1.body.get
    val m2Body = m2.body.get

    assert(m1.formalArgs == m2.formalArgs, "difference in formal arguments")

    val m1FormalReturns = m1.formalReturns.toList.sortWith(_.toString < _.toString)
    val m2FormalReturns = m2.formalReturns.toList.sortWith(_.toString < _.toString)
    assert(m1FormalReturns == m2FormalReturns, "difference in formal returns")

    assert(m1Body.ss.toString() == m2Body.ss.toString(), "difference in body statements")

    val m1scopedDecls = m1Body.scopedDecls.toList.sortWith(_.toString < _.toString)
    val m2scopedDecls = m2Body.scopedDecls.toList.sortWith(_.toString < _.toString)
    assert(m1scopedDecls.toString() == m2scopedDecls.toString(), "difference in var declarations")
  }

  test("trivial assignment") {
    /*
      method test()
      {
        var x: Int
        x := 0
        x := 1
      }
    */
    val initialMethod = createTestMethod("test", body=Some(Seqn(
      Seq(
        LocalVarAssign(LocalVar("x")(Int), IntLit(0)())(),
        LocalVarAssign(LocalVar("x")(Int), IntLit(1)())()
      ),
      Seq(
        LocalVarDecl("x", Int)()
      ))()))
    val targetMethod: Method = createTestMethod("test", body=Some(Seqn(
      Seq(
        Inhale(EqCmp(LocalVar("x_1")(Int), IntLit(0)())())(),
        Inhale(EqCmp(LocalVar("x_2")(Int), IntLit(1)())())()
      ),
      Seq(
        LocalVarDecl("x_0", Int)(),
        LocalVarDecl("x_1", Int)(),
        LocalVarDecl("x_2", Int)()
      ))()))

    val transformedMethod = transformer.transform(initialMethod)
    compareMethod(targetMethod, transformedMethod)
  }

  test("assignment of var to itself") {
    /*
      method test()
      {
        var x: Int
        x := 0
        x := x + 10
      }
    */
    val initialMethod = createTestMethod("test", body=Some(Seqn(
      Seq(
        LocalVarAssign(LocalVar("x")(Int), IntLit(0)())(),
        LocalVarAssign(LocalVar("x")(Int), Add(LocalVar("x")(Int), IntLit(10)())())()
      ),
      Seq(
        LocalVarDecl("x", Int)()
      ))()))
    val targetMethod: Method = createTestMethod("test", body=Some(Seqn(
      Seq(
        Inhale(EqCmp(LocalVar("x_1")(Int), IntLit(0)())())(),
        Inhale(EqCmp(LocalVar("x_2")(Int), Add(LocalVar("x_1")(Int), IntLit(10)())())())()
      ),
      Seq(
        LocalVarDecl("x_0", Int)(),
        LocalVarDecl("x_1", Int)(),
        LocalVarDecl("x_2", Int)()
      ))()))

    val transformedMethod = transformer.transform(initialMethod)
    compareMethod(targetMethod, transformedMethod)
  }

  test("variables swap") {
    /*
      method test()
      {
        var x: Int
        var y: Int
        var tmp: Int
        tmp := x;
        x := y;
        y := tmp;
      }
    */
    val initialMethod = createTestMethod("test", body=Some(Seqn(
      Seq(
        LocalVarAssign(LocalVar("tmp")(Int), LocalVar("x")(Int))(),
        LocalVarAssign(LocalVar("x")(Int), LocalVar("y")(Int))(),
        LocalVarAssign(LocalVar("y")(Int), LocalVar("tmp")(Int))()
      ),
      Seq(
        LocalVarDecl("x", Int)(),
        LocalVarDecl("y", Int)(),
        LocalVarDecl("tmp", Int)()
      ))()))
    val targetMethod: Method = createTestMethod("test", body=Some(Seqn(
      Seq(
        Inhale(EqCmp(LocalVar("tmp_1")(Int), LocalVar("x_0")(Int))())(),
        Inhale(EqCmp(LocalVar("x_1")(Int), LocalVar("y_0")(Int))())(),
        Inhale(EqCmp(LocalVar("y_1")(Int), LocalVar("tmp_1")(Int))())()
      ),
      Seq(
        LocalVarDecl("x_0", Int)(),
        LocalVarDecl("y_0", Int)(),
        LocalVarDecl("tmp_0", Int)(),
        LocalVarDecl("x_1", Int)(),
        LocalVarDecl("y_1", Int)(),
        LocalVarDecl("tmp_1", Int)()
      ))()))

    val transformedMethod = transformer.transform(initialMethod)
    compareMethod(targetMethod, transformedMethod)
  }

  test("variables swap with method arguments") {
    /*
      method test(x: Int, y: Int)
      {
        var xx: Int
        var yy: Int
        var tmp: Int
        tmp := x;
        xx := y;
        yy := tmp;
      }
    */
    val initialMethod = createTestMethod("test",
      formalArgs=Seq(LocalVarDecl("x", Int)(), LocalVarDecl("y", Int)()), body=Some(Seqn(
      Seq(
        LocalVarAssign(LocalVar("tmp")(Int), LocalVar("x")(Int))(),
        LocalVarAssign(LocalVar("xx")(Int), LocalVar("y")(Int))(),
        LocalVarAssign(LocalVar("yy")(Int), LocalVar("tmp")(Int))()
      ),
      Seq(
        LocalVarDecl("xx", Int)(),
        LocalVarDecl("yy", Int)(),
        LocalVarDecl("tmp", Int)()
      ))()))
    val targetMethod: Method = createTestMethod("test",
      formalArgs=Seq(LocalVarDecl("x", Int)(), LocalVarDecl("y", Int)()), body=Some(Seqn(
      Seq(
        Inhale(EqCmp(LocalVar("tmp_1")(Int), LocalVar("x")(Int))())(),
        Inhale(EqCmp(LocalVar("xx_1")(Int), LocalVar("y")(Int))())(),
        Inhale(EqCmp(LocalVar("yy_1")(Int), LocalVar("tmp_1")(Int))())()
      ),
      Seq(
        LocalVarDecl("xx_0", Int)(),
        LocalVarDecl("yy_0", Int)(),
        LocalVarDecl("tmp_0", Int)(),
        LocalVarDecl("xx_1", Int)(),
        LocalVarDecl("yy_1", Int)(),
        LocalVarDecl("tmp_1", Int)()
      ))()))

    val transformedMethod = transformer.transform(initialMethod)
    compareMethod(targetMethod, transformedMethod)
  }

  test("variables swap with method arguments and returns") {
    /*
      method test(x: Int, y: Int) returns (xx: Int, yy: Int)
      {
        var tmp: Int
        tmp := x;
        xx := y;
        yy := tmp;
      }
    */
    val initialMethod = createTestMethod("test",
      formalArgs=Seq(LocalVarDecl("x", Int)(), LocalVarDecl("y", Int)()),
      formalReturns=Seq(LocalVarDecl("xx", Int)(), LocalVarDecl("yy", Int)()), body=Some(Seqn(
        Seq(
          LocalVarAssign(LocalVar("tmp")(Int), LocalVar("x")(Int))(),
          LocalVarAssign(LocalVar("xx")(Int), LocalVar("y")(Int))(),
          LocalVarAssign(LocalVar("yy")(Int), LocalVar("tmp")(Int))()
        ),
        Seq(
          LocalVarDecl("tmp", Int)()
        ))()))
    val targetMethod: Method = createTestMethod("test",
      formalArgs=Seq(LocalVarDecl("x", Int)(), LocalVarDecl("y", Int)()),
      formalReturns=Seq(LocalVarDecl("xx_1", Int)(), LocalVarDecl("yy_1", Int)()), body=Some(Seqn(
        Seq(
          Inhale(EqCmp(LocalVar("tmp_1")(Int), LocalVar("x")(Int))())(),
          Inhale(EqCmp(LocalVar("xx_1")(Int), LocalVar("y")(Int))())(),
          Inhale(EqCmp(LocalVar("yy_1")(Int), LocalVar("tmp_1")(Int))())()
        ),
        Seq(
          LocalVarDecl("xx_0", Int)(),
          LocalVarDecl("yy_0", Int)(),
          LocalVarDecl("tmp_0", Int)(),
          LocalVarDecl("tmp_1", Int)()
        ))()))

    val transformedMethod = transformer.transform(initialMethod)
    compareMethod(targetMethod, transformedMethod)
  }
}