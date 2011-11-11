/* NSC -- new Scala compiler -- Copyright 2007-2011 LAMP/EPFL */

package scala.tools.nsc
package doc
package model

import comment._

import scala.collection._
import scala.util.matching.Regex

import symtab.Flags
import io._

import model.{ RootPackage => RootPackageEntity }

/** This trait extracts all required information for documentation from compilation units */
trait ModelFactoryImplicitSupport {
  thisFactory: ModelFactory with CommentFactory with TreeFactory =>
	
	import global._
  import definitions.{ ObjectClass, ScalaObjectClass, RootPackage, EmptyPackage, NothingClass, AnyClass, AnyValClass, AnyRefClass }
  import model.comment.Block // shadow global's Block
  
  
  /* ============== IMPLEMENTATION PROVIDING ENTITY TYPES ============== */  

  class ImplicitConversionImpl(convertorMethodSymbol: Symbol, targetType: Type, val constraints: List[ConstraintEntity], inTpl: => TemplateImpl) extends ImplicitConversion {  	  
  	def target: TypeEntity = makeType(targetType, inTpl)
		def convertorOwner: TemplateEntity = makeTemplate(convertorMethodSymbol.owner)      
	  def convertorMethod: Either[MemberEntity, String] = convertorOwner match {
  		case doc: DocTemplateImpl =>
  			// there might be multiple entities or none at all, as the makeMember function can return any number of entities
				val allTemplates = doc.membersMap flatMap { case (sym, entity) => if (sym == convertorMethodSymbol) List(entity) else Nil }
				if (allTemplates.length > 0) Left(allTemplates.head) else Right(convertorMethodSymbol.name.toString)
  		case _ => Right(convertorMethodSymbol.name.toString)
		}
	  def getBody: Body = {
  		val header = Paragraph(Bold(Chain(Text("Member inherited by implicit conversion to ")::Monospace(Text(target.toString()))::Text(" by ")::Monospace(Text(convertorMethodSymbol.name.toString))::Text(" in ")::Monospace(Text(convertorMethodSymbol.owner.name.toString))::Text(".")::Nil)))
  		val constrs: List[Block] = constraints.length match {
  			case 0 => Nil
  			case 1 => List(Paragraph(Text("The implicit conversion will take place only if: ")), UnorderedList(constraints map { _.getConstraintText }))
  			case 2 => List(Paragraph(Text("The implicit conversion will take place only if all the constraints are satisfied:")), UnorderedList(constraints map { _.getConstraintText })) 
  		}
  		Body(header :: constrs ::: HorizontalRule() :: Nil)
	  }
  }

	class ImplicitInScopeConstraint(sym: Symbol, inTpl: => TemplateImpl) extends ConstraintEntity {
		def getConstraintText: Block = Paragraph(Chain(Text("An implicit value of type ")::Monospace(Text(sym.tpe.toString))::Text(" is in scope.")::Nil))
	}

  class BoundConstraint(tp: Type, ub: Type, lb: Type, inTpl: => TemplateImpl) extends ConstraintEntity {
		def getConstraintText: Block = Paragraph(Chain(Text(tp + " is bounded by " + lb + " and " + ub + ": ") :: Monospace(Text(tp + " >: " + lb + " <: " + ub))::Nil)) 
  }
	
  class EqualityConstraint(tp: Type, tp2: Type, inTpl: => TemplateImpl) extends ConstraintEntity {
		def getConstraintText: Block = Paragraph(Chain(Text(tp + " is equal to " + tp2 + ": ")::Monospace(Text(tp + " =: " + tp2))::Nil)) 
  }

  class UpperBoundedConstraint(tp: Type, ub: Type, inTpl: => TemplateImpl) extends ConstraintEntity {
		def getConstraintText: Block = Paragraph(Chain(Text(tp + " is upper bounded by " + ub + ": ")::Monospace(Text(tp + " <: " + ub))::Nil)) 
  }
  
  class LowerBoundedConstraint(tp: Type, lb: Type, inTpl: => TemplateImpl) extends ConstraintEntity {
		def getConstraintText: Block = Paragraph(Chain(Text(tp + " is lower bounded by " + lb + ": ")::Monospace(Text(tp + " >: " + lb))::Nil)) 
  }

  class ComplexBoundsConstraint(tp: Type, constr: TypeConstraint, inTpl: => TemplateImpl) extends ConstraintEntity {
		def getConstraintText: Block = Paragraph(Chain(Text("Complex constraint: ")::Monospace(Text(tp + " " + constr))::Nil)) 
  }

  class SubstitutionConstraint(from: Symbol, to: Type, inTpl: => TemplateImpl) extends ConstraintEntity {
		def getConstraintText: Block = Paragraph(Chain(Text("Substitute type of ")::Monospace(Text(from.toString))::Text(" to ")::Monospace(Text(to.toString))::Nil)) 
  }

	
  /* ============== MAKER METHODS ============== */
  	
	def implicitShouldDocument(aSym: Symbol): Boolean = {
  	// We shouldn't document:
  	// - constructors
		// - common methods (in Any, AnyRef, Object) as they are automatically removed
  	// - private and protected members (not accessible following an implicit conversion)
  	// - members starting with _ (usually reserved for internal stuff)
    localShouldDocument(aSym) && (!aSym.isConstructor) && (aSym.owner != ObjectClass) && (aSym.owner != AnyClass) && (aSym.owner != AnyRefClass) && 
    (!aSym.isProtected) && (!aSym.isPrivate) && (!aSym.name.toString.startsWith("_"))
  }
  
  
  def membersByImplicitConversions(sym: Symbol, inTpl: => TemplateImpl): List[(Symbol, ImplicitConversion)] = {
    if (!(sym.isClass || sym.isTrait))
      Nil
    else {
      println("\n\n" + sym.nameString + "\n" + "=" * sym.nameString.length())
      
      val context: global.analyzer.Context = global.analyzer.rootContext(NoCompilationUnit)            
      val result = global.analyzer.allViewsFrom(sym.tpe, context, sym.typeParams)
      
      result flatMap { case (result, constr) => getMembersSymbols(sym.tpe, context, sym.typeParams, result, constr, inTpl) }
    }
  }
  
  def getMembersSymbols(tp: Type, 
  										  context: global.analyzer.Context, 
  										  tpars: List[Symbol], 
  										  res: global.analyzer.SearchResult, 
  										  constrs: List[TypeConstraint], 
  										  inTpl: => TemplateImpl): List[(Symbol, ImplicitConversion)] = {

  	if (res.tree == EmptyTree)
  		Nil
		else {
  	
			// the full type can contain implicit parameters which we don't want
			val coercion = res.tree  	
	  	// and get the view applied to an argument
	    val viewApply = new ApplyImplicitView(coercion, List(Ident("<argument>") setType coercion.tpe.paramTypes.head))      
	    val typed: Tree = global.analyzer.newTyper(context.makeImplicit(context.reportAmbiguousErrors)).silent(_.typed(viewApply, global.analyzer.EXPRmode, WildcardType), false) match {
	          case ex: Throwable =>
	            println("typing coercion failed "+ ex)
	            coercion
	          case t: Tree => t
	        }
	
	    // the type vars need to be propagated until we ask for the members, then you can replace them by some simplified representation
	    // in principle, we should solve the set of type variables, but this is unlikely to work since we can't really know any of them concretely
	    // for now, just simplify them, and if their upper bounds =:= lower bounds, replace by that type,
	    // else, if the lub and the glb could be computed, use an existential with the given lower and upper bound
	    // if all that fails, you'll need some textual representation of the TypeConstraint
	    val toTp = typeVarToOriginOrWildcard(typed.tpe.finalResultType)
	    val fullTpe = wildcardToNothing(typeVarToOriginOrWildcard(typed.tpe))
	    println("conversion "+ typed.symbol +" from "+ tp +" to "+ toTp)
	
	    // Transform bound constraints into scaladoc constraints
			val implicitParamConstraints = implicitParametersToConstraints(fullTpe, inTpl)
	    val boundConstraints = boundedTParamsConstraints(tpars, constrs, inTpl) 
	    val substConstraints = (res.subst.from zip res.subst.to) map { case (from, to) => new SubstitutionConstraint(from, to, inTpl) }    
	    val constraints = implicitParamConstraints ::: boundConstraints ::: substConstraints
	    constraints foreach println
     
	    val implicitMembers = toTp.nonPrivateMembers. 
	    											  filter(implicitShouldDocument(_)).
	    											  map { symbol => symbol.cloneSymbol.setInfo(toTp memberInfo symbol) }
	    
	    implicitMembers foreach (sym => println("  - "+ sym.decodedName +" : " + sym.info))
    	    
	    // Create the implicit conversion object
	    println("res.tree.getClass: " + res.tree.getClass())
	    println("res.tree.symbol: " + res.tree.symbol)
	    val implicitConversion = new ImplicitConversionImpl(res.tree.symbol, toTp, constraints, inTpl)
	    
	    implicitMembers.map((_, implicitConversion))
		}
  }

  
  /**
   * uniteConstraints takes a TypeConstraint instance and simplifies the constraints inside
   */
  def uniteConstraints(constr: TypeConstraint): TypeConstraint =
	  try {
	  	new TypeConstraint(List(wildcardToNothing(lub(constr.loBounds  map typeVarToOriginOrWildcard))), 
	  									   List(wildcardToNothing(glb(constr.hiBounds  map typeVarToOriginOrWildcard)))) 
	  } catch { 
	  	// does this actually ever happen? (probably when type vars occur in the bounds)	
	  	case x: Throwable => new TypeConstraint(constr.loBounds.distinct, constr.hiBounds.distinct) 
	  } 

	/** 
	 * implicitParameterToConstraints transforms implicit parameters from the view result type into constraints
	 *  
	 * for the example view:
	 *   implicit def pimpMyClass[T](a: MyClass[T])(implicit ev: Numeric[T]): PimpedMyClass[T]
	 * the implicit view result type is:
	 *   (implicit ev: Numeric[T]): PimpedMyClass[T] 
	 * and implicitParametersToConstraints will output a single constraint:
	 *   ImplicitInScopeConstraint(ev: Numeric[T])
	 */
	def implicitParametersToConstraints(ty: Type, inTpl: => TemplateImpl): List[ConstraintEntity] = ty match {
	  case MethodType(params, resultType) if (params.filter(_.isImplicit).length != 0) =>
	    params.map(param => new ImplicitInScopeConstraint(param, inTpl)) ::: implicitParametersToConstraints(resultType, inTpl)
	  case other =>
	    Nil
	}  	
	
	def boundedTParamsConstraints(tpars: List[Symbol], constrs: List[TypeConstraint], inTpl: => TemplateImpl) = 
		(tpars zip (constrs map uniteConstraints)) flatMap {
	  	case (param, constr) => {
	  		val tp = param.tpe    		
	  		(constr.loBounds, constr.hiBounds) match {    			
	  			case (List(lb), List(ub)) if ((lb == NothingClass.tpe) && (ub == AnyClass.tpe)) => // Most generic bounds
		    		Nil		      
		    	case (List(lb), List(ub)) if (lb == ub) =>               // Same bound on both sides => equality		    		
		    		List(new EqualityConstraint(tp, lb, inTpl)) 
		    	case (List(lb), List(ub)) if (ub == AnyClass.tpe) =>     // Only lower bound
		    		List(new LowerBoundedConstraint(tp, lb, inTpl))		    	
		    	case (List(lb), List(ub)) if (lb == NothingClass.tpe) => // Only upper bound
		    		List(new UpperBoundedConstraint(tp, ub, inTpl))		    
		    	case (List(lb), List(ub)) =>                             // Single bounds, not obvious
		    		List(new BoundConstraint(tp, lb, ub, inTpl))		    	
		    	case _ =>                                                // Multiple bounds
		    		List(new ComplexBoundsConstraint(tp, constr, inTpl))
	  		}
	  	}
		}
	
  // we don't want typeVars, we want our original type params back
  object typeVarToOriginOrWildcard extends TypeMap {
    def apply(tp: Type): Type = mapOver(tp) match {	      	
      case tv: TypeVar =>
      	if (tv.constr.inst.typeSymbol == NothingClass)
      		WildcardType
    		else
    			tv.origin //appliedType(tv.origin.typeConstructor, tv.typeArgs map this)
      case other =>
      	if (other.typeSymbol == NothingClass)
      		WildcardType
    		else
    			other	      
    }
  }

  object wildcardToNothing extends TypeMap {
    def apply(tp: Type): Type = mapOver(tp) match {	      	
      case WildcardType =>
      	NothingClass.tpe
      case other =>
  			other	      
    }
  }
  
  def getTypeString(tp: Symbol) = tp match {
		case ts: TypeSymbol => ts.name.toString
		case _ => tp.toString
	}

}