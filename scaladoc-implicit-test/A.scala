package test.implicits

class A[T] {
  def a = 1
  def b = 2
  def c = 3
}

object A {
  implicit def pimpA1[T: Numeric](a: A[T]) = new NumericA[T](a)
  implicit def pimpA2(a: A[Int]) = new IntA(a)
  implicit def pimpA3(a: A[T] forSome { type T <: Double }) = new ComplexA(a)
}

class NumericA[T: Numeric](a: A[T]) {
  def d = 4
  def e = 5
  def f = 6
  def t: T = implicitly[Numeric[T]].zero
}

class IntA(a: A[Int]) {
  def dd = 4
  def ee = 5
  def ff = 6
  def tt: Int = 0
}

class ComplexA(a: A[T] forSome { type T <: Double }) {
  def ddd = 4
  def eee = 5
  def fff = 6
  def ttt: Int = 0
}


