package test.implicits

class Foo[T]
class Bar[T]

/** Class A 
 *  - tests the complete type inference 
 *  - the following inherited methods should appear:
 * {{{
 * def inheritedByImplicitConversionToPimpedA: T             // no constraints
 * def inheritedByImplicitConversionToNumericA: T            // with a constraint that there is x: Numeric[T] implicit in scope
 * def inheritedByImplicitConversionToIntA: Int              // with a constraint that T = Int
 * def inheritedByImplicitConversionToGtColonDoubleA: Double // with a constraint that T <: Double
 * def inheritedByImplicitConversionToPimpedA: S             // with a constraint that T = Foo[Bar[S]]
 * def inheritedByImplicitConversionToPimpedA: Bar[Foo[T]]   // no constraints
 * }}}
 */
class A[T]
/** Companion object with implicit transformations  */
object A {
  implicit def pimpA0[V](a: A[V]) = new PimpedA(a)
  implicit def pimpA1[T: Numeric](a: A[T]) = new NumericA[T](a)
  implicit def pimpA2(a: A[Int]) = new IntA(a)
  implicit def pimpA3(a: A[T] forSome { type T <: Double }) = new GtColonDoubleA(a)
  implicit def pimpA4[S](a: A[Foo[Bar[S]]]): PimpedA[S] = sys.error("not implemented")
  implicit def pimpA5[Z](a: A[Z]): PimpedA[Bar[Foo[Z]]] = sys.error("not implemented")
}


/** Class B 
 *  - tests the existential type solving 
 *  - the following inherited methods should appear:
 * {{{
 * def inheritedByImplicitConversionToPimpedA: Double        // no constraints
 * def inheritedByImplicitConversionToNumericA: Double       // no constraints
 * def inheritedByImplicitConversionToGtColonDoubleA: Double // no constraints
 * def inheritedByImplicitConversionToPimpedA: Bar[Foo[T]]   // no constraints
 * }}}
 */
class B extends A[Double]
object B extends A


/** Class C 
 *  - tests asSeenFrom
 *  - the following inherited methods should appear:
 * {{{
 * def inheritedByImplicitConversionToPimpedA: Int           // no constraints
 * def inheritedByImplicitConversionToNumericA: Int          // no constraints
 * def inheritedByImplicitConversionToIntA: Int              // no constraints
 * def inheritedByImplicitConversionToPimpedA: Bar[Foo[T]]   // no constraints
 * }}}
 */
class C extends A[Int]
object C extends A



/** PimpedA class <br/> 
 *  - tests simple inheritance and asSeenFrom
 *  - A, B and C should be implicitly converted to this */
class PimpedA[V](a: A[V]) {
  /** The inheritedByImplicitConversionToPimpedA: V documentation... */ 
  def inheritedByImplicitConversionToPimpedA: V = sys.error("Not implemented")
}

/** NumericA class <br/>
 *  - tests the implicit conversion between parametric and fixed types
 *  - A, B and C should be implicitly converted to this */
class NumericA[U: Numeric](a: A[U]) {
  /** The inheritedByImplicitConversionToNumericA: U documentation... */ 
  def inheritedByImplicitConversionToNumericA: U = implicitly[Numeric[U]].zero
}

/** IntA class <br/>
 *  - tests the interaction between implicit conversion and specific types
 *  - A and C should be implicitly converted to this */
class IntA(a: A[Int]) {
  /** The inheritedByImplicitConversionToIntA: Int documentation... */ 
  def inheritedByImplicitConversionToIntA: Int = 0
}

/** GtColonDoubleA class <br/>
 *  - tests the interaction between implicit conversion and existential types
 *  - A and B should be implicitly converted to this */
class GtColonDoubleA(a: A[T] forSome { type T <: Double }) {
  /** The inheritedByImplicitConversionToGtColonDoubleA: Double documentation... */ 
  def inheritedByImplicitConversionToGtColonDoubleA: Double = 0
}


