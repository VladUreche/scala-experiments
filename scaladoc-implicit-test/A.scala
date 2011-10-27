package test.implicits



/** Class A 
 *  - tests the complete type inference 
 *  - the following inherited methods should appear:
 * {{{
 * def inheritedByImplicitConversionToPimpedA: T
 * def inheritedByImplicitConversionToNumericA: T
 * def inheritedByImplicitConversionToIntA: Int
 * def inheritedByImplicitConversionToGtColonDoubleA: Double
 * }}}
 */
class A[T]
/** Companion object with implicit transformations  */
object A {
  implicit def pimpA0[V](a: A[V]) = new PimpedA(a)
  implicit def pimpA1[T: Numeric](a: A[T]) = new NumericA[T](a)
  implicit def pimpA2(a: A[Int]) = new IntA(a)
  implicit def pimpA3(a: A[T] forSome { type T <: Double }) = new GtColonDoubleA(a)
}


/** Class B 
 *  - tests the existential type solving 
 *  - the following inherited methods should appear:
 * {{{
 * def inheritedByImplicitConversionToPimpedA: Double
 * def inheritedByImplicitConversionToNumericA: Double
 * def inheritedByImplicitConversionToGtColonDoubleA: Double
 * }}}
 */
class B extends A[Double]
object B extends A


/** Class C 
 *  - tests asSeenFrom
 *  - the following inherited methods should appear:
 * {{{
 * def inheritedByImplicitConversionToPimpedA: Int
 * def inheritedByImplicitConversionToNumericA: Int
 * def inheritedByImplicitConversionToIntA: Int
 * }}}
 */
class C extends A[Int]
object C extends A



/** PimpedA class <br/> 
 *  - tests simple inheritance and asSeenFrom
 *  - A, B and C should be implicitly converted to this */
class PimpedA[V](a: A[V]) {
  def inheritedByImplicitConversionToPimpedA: V = sys.error("Not implemented")
}

/** NumericA class <br/>
 *  - tests the implicit conversion between parametric and fixed types
 *  - A, B and C should be implicitly converted to this */
class NumericA[U: Numeric](a: A[U]) {
  def inheritedByImplicitConversionToNumericA: U = implicitly[Numeric[U]].zero
}

/** IntA class <br/>
 *  - tests the interaction between implicit conversion and specific types
 *  - A and C should be implicitly converted to this */
class IntA(a: A[Int]) {
 def inheritedByImplicitConversionToIntA: Int = 0
}

/** GtColonDoubleA class <br/>
 *  - tests the interaction between implicit conversion and existential types
 *  - A and B should be implicitly converted to this */
class GtColonDoubleA(a: A[T] forSome { type T <: Double }) {
 def inheritedByImplicitConversionToGtColonDoubleA: Double = 0
}


