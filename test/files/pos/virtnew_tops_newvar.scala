object Test extends App {
  // use the CanBuildFrom type-level computation pattern to specify `applyDynamic[Variable[T]](n): T`
  trait ADbase {
    implicit def ad[X] = new AD[X]{ type T = X }
  }
  object AD extends ADbase {
    implicit def adVar[T] = new AD[Variable[T]]{ type U = T}
  }
  trait AD[T] { type U }

  trait Rep[+x] {
    // def __newVar[T](x: T): Rep[T] = error("")
    def selectDynamic[T](n: String): Rep[T] = error("")
    def applyDynamic[T](n: String)(implicit w: AD[T]): Rep[w.U] = error("")
    def updateDynamic[T](n: String)(v: Rep[Any]): Rep[Unit] = error("")
  }

  // def __newVar[T:Manifest](init: T) = var_new(Const(init))
  //def __newVar[T](init: Rep[T])(implicit o: Overloaded1, mT: Manifest[T]) = var_new(init)
  //def __newVar[T](init: Var[T])(implicit o: Overloaded2, mT: Manifest[T]) = var_new(init)

  // as in virtualization-lms-core, this is not a rep
  case class Variable[T](e: Rep[T])
  def var_new[T:Manifest](init: Rep[T]) = Variable(init)

  // representation of a statically-known constant
  case class Const[T](x: T) extends Rep[T]
  implicit def liftInt(x: Int): Rep[Int] = Const(x) 
  implicit def intToIntOps(x: Int) = new IntOps(Const(x))
  implicit def repIntToIntOps(x: Rep[Int]) = new IntOps(x)

  case class Times(lhs: Rep[Int], rhs: Rep[Int]) extends Rep[Int]
  class IntOps(lhs: Rep[Int]) {
    def *(rhs: Rep[Int]) = Times(lhs, rhs)
  }

  case class Var[T, U](self: Rep[T], x: U) extends Rep[U]
  // to represent the self/this reference in a reified object creation
  case class Self[T]() extends Rep[T] {
    // override def __newVar[T](x: T): Rep[T] = Var(this, x)
  }


  // this method is called by the virtualizing compiler
  def __new[T](args: (String, Boolean, Rep[T] => Rep[_])*): Rep[T] = {
    val me = new Self[T]()
    new Obj(me, args map {case (n, b, rhs) => (n, rhs(me))} toMap)
  }

  class Obj[T](self: Rep[T], fields: Map[String, Rep[_]]) extends Rep[T] {
    override def selectDynamic[T](n: String): Rep[T] = {
      val res = fields(n)
      println(self +" DOT "+ n + " = "+ res)
      res.asInstanceOf[Rep[T]]
    }
  }

  implicit def varToRep[T](init: Variable[T]): Rep[T] = null

  val foo = new Row[Rep] { var xx = Const(23) : Rep[Int]; 
			   var yy = (xx = xx * 2) }

  val bar = new Row[Rep] { var xx = Const(23) : Rep[Int]; 
			   val yy = Const({() => (xx = xx * 2); xx})}

  println(bar.xx)
}
