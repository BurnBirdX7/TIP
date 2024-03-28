package tip.analysis

import tip.ast._
import tip.solvers._
import tip.types._
import tip.ast.AstNodeData._
import tip.util.{Log, TipProgramException}
import AstOps._

import scala.collection.mutable

/**
  * Unification-based type analysis.
  * The analysis associates a [[tip.types.Type]] with each variable declaration and expression node in the AST.
  * It is implemented using [[tip.solvers.UnionFindSolver]].
  *
  * To novice Scala programmers:
  * The parameter `declData` is declared as "implicit", which means that invocations of `TypeAnalysis` obtain its value implicitly:
  * The call to `new TypeAnalysis` in Tip.scala does not explicitly provide this parameter, but it is in scope of
  * `implicit val declData: TypeData = new DeclarationAnalysis(programNode).analyze()`.
  * The TIP implementation uses implicit parameters many places to provide easy access to the declaration information produced
  * by `DeclarationAnalysis` and the type information produced by `TypeAnalysis`.
  * For more information about implicit parameters in Scala, see [[https://docs.scala-lang.org/tour/implicit-parameters.html]].
  */
class TypeAnalysis(program: AProgram)(implicit declData: DeclarationData) extends DepthFirstAstVisitor[Unit] with Analysis[TypeData] {

  val log = Log.logger[this.type]()

  val solver = new UnionFindSolver[Type]

  implicit val allFieldNames: List[String] = program.appearingFields.toList.sorted

  /**
    * @inheritdoc
    */
  def analyze(): TypeData = {

    // generate the constraints by traversing the AST and solve them on-the-fly
    try {
      visit(program, ())
    } catch {
      case e: UnificationFailure =>
        throw new TipProgramException(s"Type error: ${e.getMessage}")
    }

    // check for accesses to absent record fields
    new DepthFirstAstVisitor[Unit] {
      visit(program, ())

      override def visit(node: AstNode, arg: Unit): Unit = {
        node match {
          case ac: AFieldAccess =>
            if (solver.find(node).isInstanceOf[AbsentFieldType.type])
              throw new TipProgramException(s"Type error: Reading from absent field ${ac.field} ${ac.loc.toStringLong}")
          case as: AAssignStmt =>
            as.left match {
              case dfw: ADirectFieldWrite =>
                if (solver.find(as.right).isInstanceOf[AbsentFieldType.type])
                  throw new TipProgramException(s"Type error: Writing to absent field ${dfw.field} ${dfw.loc.toStringLong}")
              case ifw: AIndirectFieldWrite =>
                if (solver.find(as.right).isInstanceOf[AbsentFieldType.type])
                  throw new TipProgramException(s"Type error: Writing to absent field ${ifw.field} ${ifw.loc.toStringLong}")
              case _ =>
            }
          case _ =>
        }
        visitChildren(node, ())
      }
    }

    var ret: TypeData = Map()

    // close the terms and create the TypeData
    new DepthFirstAstVisitor[Unit] {
      val sol: Map[Var[Type], Term[Type]] = solver.solution()
      log.info(s"Solution (not yet closed):\n${sol.map { case (k, v) => s"  \u27E6$k\u27E7 = $v" }.mkString("\n")}")
      val freshvars: mutable.Map[Var[Type], Var[Type]] = mutable.Map()
      visit(program, ())

      // extract the type for each identifier declaration and each non-identifier expression
      override def visit(node: AstNode, arg: Unit): Unit = {
        node match {
          case _: AIdentifier =>
          case _: ADeclaration | _: AExpr =>
            ret += node -> Some(TipTypeOps.close(VarType(node), sol, freshvars).asInstanceOf[Type])
          case _ =>
        }
        visitChildren(node, ())
      }
    }

    log.info(s"Inferred types:\n${ret.map { case (k, v) => s"  \u27E6$k\u27E7 = ${v.get}" }.mkString("\n")}")
    ret
  }

  /**
    * Generates the constraints for the given sub-AST.
    * @param node the node for which it generates the constraints
    * @param arg unused for this visitor
    */
  def visit(node: AstNode, arg: Unit): Unit = {
    log.verb(s"Visiting ${node.getClass.getSimpleName} at ${node.loc}")
    node match {
      case program: AProgram =>
      case _: ANumber => unify(node, IntType())
      case _: AInput => unify(node, IntType())
      case is: AIfStmt => unify(is.guard, IntType())
      case os: AOutputStmt => unify(os.exp, IntType())
      case ws: AWhileStmt => unify(ws.guard, IntType())
      case as: AAssignStmt =>
        as.left match {
          case id: AIdentifier => unify(id, as.right)
          case dw: ADerefWrite => unify(dw.exp, PointerType(as.right))

          // Not in the lecture. When Id1.Id2 = E
          // [[Id1]] = Record { Id2 -> [[E]], * -> ? }
          case dfw: ADirectFieldWrite =>
            unify(dfw.id, RecordType(allFieldNames.map { f =>
              if (f == dfw.field) as.right : Term[Type] else FreshVarType()
            }))

          // Not in the lecture. When (*E1).Id = E2
          // [[E1]] = & Record { Id -> [[E2]], * -> ? }
          case ifw: AIndirectFieldWrite =>
            unify(ifw.exp, PointerType(RecordType(allFieldNames.map { f =>
              if (f == ifw.field) as.right : Term[Type] else FreshVarType()
            })))
        }
      case bin: ABinaryOp =>
        bin.operator match {
          case Eqq =>
            unify(bin.left, bin.right)
            unify(node, IntType())
          case _ =>
            unify(IntType(), bin.left)
            unify(IntType(), bin.right)
            unify(IntType(), bin)
        }
      case un: AUnaryOp =>
        un.operator match {
          case DerefOp => unify(PointerType(un), un.subexp)
        }

      // Differs from lecture. When alloc E
      // [[alloc E]] = & [[E]]
      case alloc: AAlloc => unify(alloc, PointerType(alloc.exp))
      case ref: AVarRef => unify(ref, PointerType(ref.id))
      case _: ANull => unify(node, PointerType(FreshVarType()))
      case fun: AFunDeclaration =>
        val ftype = FunctionType(fun.params, fun.stmts.ret)
        unify(ftype, fun)
      case call: ACallFuncExpr =>
        val ftype = FunctionType(call.args, call)
        unify(call.targetFun, ftype)
      case _: AReturnStmt =>
      case rec: ARecord =>
        val fieldmap = rec.fields.foldLeft(Map[String, Term[Type]]()) { (a, b) =>
          a + (b.field -> b.exp)
        }
        unify(rec, RecordType(allFieldNames.map { f =>
          fieldmap.getOrElse(f, AbsentFieldType)
        }))
      case ac: AFieldAccess =>
        unify(ac.record, RecordType(allFieldNames.map { f =>
          if (f == ac.field) VarType(ac) else FreshVarType()
        }))
      case _ =>
    }
    visitChildren(node, ())
  }

  private def unify(t1: Term[Type], t2: Term[Type]): Unit = {
    log.verb(s"Generating constraint $t1 = $t2")
    solver.unify(t1, t2)
  }
}
