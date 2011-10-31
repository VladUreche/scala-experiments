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
class ModelFactory(val global: Global, val settings: doc.Settings) {
  thisFactory: ModelFactory with CommentFactory with TreeFactory =>

  import global._
  import definitions.{ ObjectClass, ScalaObjectClass, RootPackage, EmptyPackage, NothingClass, AnyClass, AnyValClass, AnyRefClass }
  import model.comment.Block // shadow global's Block

  private var droppedPackages = 0
  def templatesCount = templatesCache.size - droppedPackages

  private var modelFinished = false
  private var universe: Universe = null

  //private def dbg(msg: String) = if (sys.props contains "scala.scaladoc.debug") println(msg)
  @inline private final def dbg(s: => String) = {
    if (settings.debugModelFactory.value)
      println(s)
  }
  
  private def closestPackage(sym: Symbol) = {
    if (sym.isPackage || sym.isPackageClass) sym
    else sym.enclosingPackage
  }

  private def printWithoutPrefix(memberSym: Symbol, templateSym: Symbol) = {
    (
      "memberSym " + memberSym + " templateSym " + templateSym + " encls = " + 
      closestPackage(memberSym) + ", " + closestPackage(templateSym)
    )
    memberSym.isOmittablePrefix || (closestPackage(memberSym) == closestPackage(templateSym))
  }
  
  private lazy val noSubclassCache = Set(AnyClass, AnyRefClass, ObjectClass, ScalaObjectClass)
  
  /**  */
  def makeModel: Option[Universe] = {
    dbg("makeModel - creating universe")
    val universe = new Universe { thisUniverse =>
      thisFactory.universe = thisUniverse
      val settings = thisFactory.settings
      private val rootPackageMaybe = makeRootPackage
      val rootPackage = rootPackageMaybe.orNull
    }
    dbg("makeModel - finished universe creation")
    modelFinished = true
    Some(universe) filter (_.rootPackage != null)
  }

  /** */
  protected val templatesCache =
    new mutable.LinkedHashMap[Symbol, DocTemplateImpl]

  def findTemplate(query: String): Option[DocTemplateImpl] = {
    dbg("findTemplate for " + query)
    if (!modelFinished) sys.error("cannot find template in unfinished universe")
    val result = templatesCache.values find { tpl => tpl.qualifiedName == query && !tpl.isObject }
    dbg("findTemplate - " + (if (result.isDefined) "found" else "not found"))
    result    		
  }

  def optimize(str: String): String =
    if (str.length < 16) str.intern else str

  /* ============== IMPLEMENTATION PROVIDING ENTITY TYPES ============== */

  abstract class EntityImpl(val sym: Symbol, inTpl: => TemplateImpl) extends Entity {
    dbg("EntityImpl(" + sym + ", inTpl) - started")
    val name = optimize(sym.nameString)
    def inTemplate: TemplateImpl = inTpl
    def toRoot: List[EntityImpl] = this :: inTpl.toRoot
    def qualifiedName = name
    val universe = thisFactory.universe
    def annotations = sym.annotations.map(makeAnnotation)
    dbg("EntityImpl(" + sym + ", inTpl) - finished")
  }

  trait TemplateImpl extends EntityImpl with TemplateEntity {
    dbg("TemplateImpl(" + sym + ", inTpl) - started")
    override def qualifiedName: String =
      if (inTemplate.isRootPackage) name else optimize(inTemplate.qualifiedName + "." + name)
    def isPackage = sym.isPackage
    def isTrait = sym.isTrait
    def isClass = sym.isClass && !sym.isTrait
    def isObject = sym.isModule && !sym.isPackage
    def isCaseClass = sym.isCaseClass
    def isRootPackage = false
    def selfType = if (sym.thisSym eq sym) None else Some(makeType(sym.thisSym.typeOfThis, this))
    dbg("TemplateImpl(" + sym + ", inTpl) - finished")
  }

  class NoDocTemplateImpl(sym: Symbol, inTpl: => TemplateImpl) extends EntityImpl(sym, inTpl) with TemplateImpl with NoDocTemplate {
    dbg("NoDocTemplateImpl(" + sym + ", inTpl)")
    def isDocTemplate = false
  }

  abstract class MemberImpl(sym: Symbol, implConv: ImplicitConversion = null, inTpl: => DocTemplateImpl) extends EntityImpl(sym, inTpl) with MemberEntity {
    dbg("MemberImpl(" + sym + ", inTpl) - started")
    lazy val comment =
      if (inTpl == null) None else thisFactory.comment(sym, inTpl)
    override def inTemplate = inTpl
    override def toRoot: List[MemberImpl] = this :: inTpl.toRoot
    def inDefinitionTemplates =
      if (inTpl == null)
        makeRootPackage.toList
      else
        makeTemplate(sym.owner) :: (sym.allOverriddenSymbols map { inhSym => makeTemplate(inhSym.owner) })
    def visibility = {
      if (sym.isPrivateLocal) PrivateInInstance()
      else if (sym.isProtectedLocal) ProtectedInInstance()
      else {
        val qual =
          if (sym.hasAccessBoundary)
            Some(makeTemplate(sym.privateWithin))
          else None
        if (sym.isPrivate) PrivateInTemplate(inTpl)
        else if (sym.isProtected) ProtectedInTemplate(qual getOrElse inTpl)
        else if (qual.isDefined) PrivateInTemplate(qual.get)
        else Public()
      }
    }
    def flags = {
      val fgs = mutable.ListBuffer.empty[Paragraph]
      if (sym.isImplicit) fgs += Paragraph(Text("implicit"))
      if (sym.isSealed) fgs += Paragraph(Text("sealed"))
      if (!sym.isTrait && (sym hasFlag Flags.ABSTRACT)) fgs += Paragraph(Text("abstract"))
      if (!sym.isTrait && (sym hasFlag Flags.DEFERRED)) fgs += Paragraph(Text("abstract"))
      if (!sym.isModule && (sym hasFlag Flags.FINAL)) fgs += Paragraph(Text("final"))
      fgs.toList
    }
    def deprecation =
      if (sym.isDeprecated)
        Some((sym.deprecationMessage, sym.deprecationVersion) match {
          case (Some(msg), Some(ver)) => parseWiki("''(Since version " + ver + ")'' " + msg, NoPosition)
          case (Some(msg), None) => parseWiki(msg, NoPosition)
          case (None, Some(ver)) =>  parseWiki("''(Since version " + ver + ")''", NoPosition)
          case (None, None) => Body(Nil)
        })
      else
        comment flatMap { _.deprecated }
    def migration =
      if(sym.hasMigrationAnnotation)
        Some((sym.migrationMessage, sym.migrationVersion) match {
          case (Some(msg), Some(ver)) => parseWiki("''(Changed in version " + ver + ")'' " + msg, NoPosition)
          case (Some(msg), None) => parseWiki(msg, NoPosition)
          case (None, Some(ver)) =>  parseWiki("''(Changed in version " + ver + ")''", NoPosition)
          case (None, None) => Body(Nil)
        })
      else
        None
    def inheritedFrom =
      if (inTemplate.sym == this.sym.owner || inTemplate.sym.isPackage) Nil else
        makeTemplate(this.sym.owner) :: (sym.allOverriddenSymbols map { os => makeTemplate(os.owner) })
    def resultType = {
      def resultTpe(tpe: Type): Type = tpe match { // similar to finalResultType, except that it leaves singleton types alone
        case PolyType(_, res) => resultTpe(res)
        case MethodType(_, res) => resultTpe(res)
        case NullaryMethodType(res) => resultTpe(res)
        case _ => tpe
      }
      makeTypeInTemplateContext(resultTpe(sym.tpe), inTemplate, sym)
    }
    def isDef = false
    def isVal = false
    def isLazyVal = false
    def isVar = false
    def isImplicit = sym.isImplicit
    def isConstructor = false
    def isAliasType = false
    def isAbstractType = false
    def isAbstract =
      ((!sym.isTrait && ((sym hasFlag Flags.ABSTRACT) || (sym hasFlag Flags.DEFERRED))) || 
      sym.isAbstractClass || sym.isAbstractType) && !sym.isSynthetic
    def isTemplate = false
    def implicitConversion = if (implConv ne null) Some(implConv) else None
    dbg("MemberImpl(" + sym + ", inTpl) - finished")
  }

   /** The instantiation of `TemplateImpl` triggers the creation of the following entities:
    *  All ancestors of the template and all non-package members.
    */
  abstract class DocTemplateImpl(sym: Symbol, inTpl: => DocTemplateImpl) extends MemberImpl(sym, null, inTpl) with TemplateImpl with HigherKindedImpl with DocTemplateEntity {
    //if (inTpl != null) println("mbr " + sym + " in " + (inTpl.toRoot map (_.sym)).mkString(" > "))
    dbg("DocTemplateImpl(" + sym + ", inTpl) - started")
    
    if (settings.verbose.value)
      inform("Creating doc template for " + sym)
      
    templatesCache += (sym -> this)
    lazy val definitionName = optimize(inDefinitionTemplates.head.qualifiedName + "." + name)
    override def toRoot: List[DocTemplateImpl] = this :: inTpl.toRoot
    def inSource =
      if (sym.sourceFile != null && ! sym.isSynthetic)
        Some((sym.sourceFile, sym.pos.line))
      else
        None

    def sourceUrl = {
      def fixPath(s: String) = s.replaceAll("\\" + java.io.File.separator, "/")
      val assumedSourceRoot  = fixPath(settings.sourcepath.value) stripSuffix "/"

      if (!settings.docsourceurl.isDefault)
        inSource map { case (file, _) =>
          val filePath = fixPath(file.path).replaceFirst("^" + assumedSourceRoot, "").stripSuffix(".scala")
          val tplOwner = this.inTemplate.qualifiedName
          val tplName = this.name
          val patches = new Regex("""€\{(FILE_PATH|TPL_OWNER|TPL_NAME)\}""")
          def substitute(name: String): String = name match {
            case "FILE_PATH" => filePath
            case "TPL_OWNER" => tplOwner
            case "TPL_NAME" => tplName
          }
          val patchedString = patches.replaceAllIn(settings.docsourceurl.value, m => java.util.regex.Matcher.quoteReplacement(substitute(m.group(1))) )
          new java.net.URL(patchedString)
        }
      else None
    } 
    def parentType = {
      if (sym.isPackage || sym == AnyClass) None else {
        val tps =
          (sym.tpe.parents filter (_ != ScalaObjectClass.tpe)) map { _.asSeenFrom(sym.thisType, sym) }
        Some(makeType(RefinedType(tps, EmptyScope), inTpl))
      }
    }
    val linearization: List[(TemplateEntity, TypeEntity)] = {
      sym.ancestors filter (_ != ScalaObjectClass) map { ancestor =>
        val typeEntity = makeType(sym.info.baseType(ancestor), this)
        val tmplEntity = makeTemplate(ancestor) match {
          case tmpl: DocTemplateImpl  => tmpl registerSubClass this ; tmpl
          case tmpl                   => tmpl
        }
        (tmplEntity, typeEntity)
      }
    }

    def linearizationTemplates = linearization map { _._1 }
    def linearizationTypes = linearization map { _._2 }

    private lazy val subClassesCache = (
      if (noSubclassCache(sym)) null
      else mutable.ListBuffer[DocTemplateEntity]()
    )
    def registerSubClass(sc: DocTemplateEntity): Unit = {
      if (subClassesCache != null)
        subClassesCache += sc
    }
    def subClasses = if (subClassesCache == null) Nil else subClassesCache.toList

    protected lazy val memberSyms =             
      // Only this class's constructors are part of its members, inherited constructors are not.
      sym.info.members.filter(s => localShouldDocument(s) && (!s.isConstructor || s.owner == sym))
    
    val memberNames = sym.info.members.map(_.name).toSet
    val implicitMembers = membersByImplicitConversions(sym, this).filterNot { case (sym, implConv) => memberNames.contains(sym.name) }
    
    val members       = (memberSyms flatMap (makeMember(_, null, this))) ::: (implicitMembers flatMap { case (sym, implConv) => makeMember(sym, implConv, this) })
    val templates     = members collect { case c: DocTemplateEntity => c }
    val methods       = members collect { case d: Def => d }
    val values        = members collect { case v: Val => v }
    val abstractTypes = members collect { case t: AbstractType => t }
    val aliasTypes    = members collect { case t: AliasType => t }
    
    override def isTemplate = true
    def isDocTemplate = true
    def companion = sym.companionSymbol match {
      case NoSymbol => None
      case comSym if !isEmptyJavaObject(comSym) && (comSym.isClass || comSym.isModule) =>
        Some(makeDocTemplate(comSym, inTpl))
      case _ => None
    }
    dbg("DocTemplateImpl(" + sym + ", inTpl) - finished")
  }

  abstract class PackageImpl(sym: Symbol, inTpl: => PackageImpl) extends DocTemplateImpl(sym, inTpl) with Package {
    dbg("PackageImpl(" + sym + ", inTpl) - started")
    override def inTemplate = inTpl
    override def toRoot: List[PackageImpl] = this :: inTpl.toRoot
    val packages = members collect { case p: Package => p }
    dbg("PackageImpl(" + sym + ", inTpl) - finished")
  }

  abstract class RootPackageImpl(sym: Symbol) extends PackageImpl(sym, null) with RootPackageEntity
  
  abstract class NonTemplateMemberImpl(sym: Symbol, implConv: ImplicitConversion, inTpl: => DocTemplateImpl) extends MemberImpl(sym, implConv, inTpl) with NonTemplateMemberEntity {
    dbg("NonTemplateMemberImpl(" + sym + ", inTpl, implConv) - started")
    override def qualifiedName = optimize(inTemplate.qualifiedName + "#" + name)
    lazy val definitionName = optimize(inDefinitionTemplates.head.qualifiedName + "#" + name)
    def isUseCase = sym.isSynthetic
    def isBridge = sym.isBridge
    dbg("NonTemplateMemberImpl(" + sym + ", inTpl, implConv) - finished")
  }
  
  abstract class NonTemplateParamMemberImpl(sym: Symbol, implConv: ImplicitConversion, inTpl: => DocTemplateImpl) extends NonTemplateMemberImpl(sym, implConv, inTpl) {
    dbg("NonTemplateParameterMemberImpl(" + sym + ", inTpl) - started")
    def valueParams =
      sym.paramss map { ps => (ps.zipWithIndex) map { case (p, i) =>
        if (p.nameString contains "$") makeValueParam(p, inTpl, optimize("arg" + i)) else makeValueParam(p, inTpl)
      }}
    dbg("NonTemplateParameterMemberImpl(" + sym + ", inTpl) - finished")
  }

  abstract class ParameterImpl(sym: Symbol, inTpl: => TemplateImpl) extends EntityImpl(sym, inTpl) with ParameterEntity {
    dbg("ParameterMemberImpl(" + sym + ", inTpl)")
    override def inTemplate = inTpl
  }
  
  private trait TypeBoundsImpl extends EntityImpl {
    dbg("TypeBoundsImpl(" + sym + ", inTpl) - started")
    def lo = sym.info.bounds match {
      case TypeBounds(lo, hi) if lo.typeSymbol != NothingClass =>
        Some(makeTypeInTemplateContext(appliedType(lo, sym.info.typeParams map {_.tpe}), inTemplate, sym))
      case _ => None
    }
    def hi = sym.info.bounds match {
      case TypeBounds(lo, hi) if hi.typeSymbol != AnyClass =>
        Some(makeTypeInTemplateContext(appliedType(hi, sym.info.typeParams map {_.tpe}), inTemplate, sym))
      case _ => None
    }
    dbg("TypeBoundsImpl(" + sym + ", inTpl) - started")
  }

  trait HigherKindedImpl extends EntityImpl with HigherKinded {
    dbg("HigherKindedImpl(" + sym + ", inTpl)")
    def typeParams =
      sym.typeParams map (makeTypeParam(_, inTemplate))
  }

  /* ============== MAKER METHODS ============== */

  /** */
  def normalizeTemplate(aSym: Symbol): Symbol = {
    val result = aSym match {
			case null | EmptyPackage | NoSymbol =>
			  normalizeTemplate(RootPackage)
			case ScalaObjectClass | ObjectClass =>
			  normalizeTemplate(AnyRefClass)
			case _ if aSym.isPackageObject =>
			  aSym
			case _ if aSym.isModuleClass =>
			  normalizeTemplate(aSym.sourceModule)
			case _ =>
			  aSym
    }
    //dbg("normalizeTemplate(" + aSym + ") => " + result)    
    result
  }

  def makeRootPackage: Option[PackageImpl] =
    makePackage(RootPackage, null)

  /** Creates a package entity for the given symbol or returns `None` if the symbol does not denote a package that
    * contains at least one ''documentable'' class, trait or object. Creating a package entity */
  def makePackage(aSym: Symbol, inTpl: => PackageImpl): Option[PackageImpl] = {
    dbg("makePackage(" + aSym + ", inTpl)")    
    val bSym = normalizeTemplate(aSym)
    if (templatesCache isDefinedAt (bSym))
      Some(templatesCache(bSym) match {case p: PackageImpl => p})
    else {
      val pack =
        if (bSym == RootPackage)
          new RootPackageImpl(bSym) {
            override lazy val comment = 
              if(settings.docRootContent.isDefault) None
              else {
                import Streamable._
                Path(settings.docRootContent.value) match {
                  case f : File => {
                    val rootComment = closing(f.inputStream)(is => parse(slurp(is), "", NoPosition))
                    Some(rootComment)
                  }
                  case _ => None
                }
              }
            override val name = "root"
            override def inTemplate = this
            override def toRoot = this :: Nil
            override def qualifiedName = "_root_"
            override def inheritedFrom = Nil
            override def isRootPackage = true
            override protected lazy val memberSyms =
              (bSym.info.members ++ EmptyPackage.info.members) filter { s =>
                s != EmptyPackage && s != RootPackage
              }
          }
        else
          new PackageImpl(bSym, inTpl) {}
      if (pack.templates.isEmpty) {
        droppedPackages += 1
        None
      }
      else Some(pack)
    }
  }

  /** */
  def makeTemplate(aSym: Symbol): TemplateImpl = {
    dbg("makeTemplate(" + aSym + ")")      	
    val bSym = normalizeTemplate(aSym)
    if (bSym == RootPackage)
      makeRootPackage.get
    else if (bSym.isPackage)
      makeTemplate(bSym.owner) match {
        case inPkg: PackageImpl => makePackage(bSym, inPkg) getOrElse (new NoDocTemplateImpl(bSym, inPkg))
        case _ => throw new Error("'" + bSym + "' must be in a package")
      }
    else if (templateShouldDocument(bSym))
      makeTemplate(bSym.owner) match {
        case inDTpl: DocTemplateImpl => makeDocTemplate(bSym, inDTpl)
        case _ => throw new Error("'" + bSym + "' must be in documentable template")
      }
    else
      new NoDocTemplateImpl(bSym, makeTemplate(bSym.owner))
  }

  /** */
  def makeDocTemplate(aSym: Symbol, inTpl: => DocTemplateImpl): DocTemplateImpl = {
    dbg("makeDocTemplate(" + aSym + ", inTpl)")      	
    val bSym = normalizeTemplate(aSym)
    val minimumInTpl =
      if (bSym.owner != inTpl.sym)
        makeTemplate(aSym.owner) match {
          case inDTpl: DocTemplateImpl => inDTpl
          case inNDTpl => throw new Error("'" + bSym + "' is owned by '" + inNDTpl + "' which is not documented")
        }
      else
        inTpl
    if (templatesCache isDefinedAt (bSym))
      templatesCache(bSym)
    else if (bSym.isModule || (bSym.isAliasType && bSym.tpe.typeSymbol.isModule))
      new DocTemplateImpl(bSym, minimumInTpl) with Object
    else if (bSym.isTrait || (bSym.isAliasType && bSym.tpe.typeSymbol.isTrait))
      new DocTemplateImpl(bSym, minimumInTpl) with Trait
    else if (bSym.isClass || (bSym.isAliasType && bSym.tpe.typeSymbol.isClass))
      new DocTemplateImpl(bSym, minimumInTpl) with Class {
        def valueParams =
          // we don't want params on a class (non case class) signature
          if (isCaseClass) List(sym.constrParamAccessors map (makeValueParam(_, this)))
          else List.empty
        val constructors =
          members collect { case d: Constructor => d }
        def primaryConstructor = constructors find { _.isPrimary }
      }
    else
      throw new Error("'" + bSym + "' that isn't a class, trait or object cannot be built as a documentable template")
  }

  /** */
  def makeAnnotation(annot: AnnotationInfo): Annotation = {
    dbg("makeAnnotation(" + annot + ")")      	
    val aSym = annot.symbol
    new EntityImpl(aSym, makeTemplate(aSym.owner)) with Annotation {
      lazy val annotationClass =
        makeTemplate(annot.symbol)
      val arguments = { // lazy
        def noParams = annot.args map { _ => None }
        val params: List[Option[ValueParam]] = annotationClass match {
          case aClass: Class =>
            (aClass.primaryConstructor map { _.valueParams.head }) match {
              case Some(vps) => vps map { Some(_) }
              case None => noParams
            }
          case _ => noParams
        }
        assert(params.length == annot.args.length)
        (params zip annot.args) flatMap { case (param, arg) =>
          makeTree(arg) match {
            case Some(tree) =>
              Some(new ValueArgument {
                def parameter = param
                def value = tree
              })
            case None => None
          }
        }
      }
    }
  }

  /** */
  def makeMember(aSym: Symbol, implConv: ImplicitConversion, inTpl: => DocTemplateImpl): List[MemberImpl] = {
    dbg("makeMember(" + aSym + ", inTpl)")      	

    def makeMember0(bSym: Symbol): Option[MemberImpl] = {
      if (bSym.isGetter && bSym.isLazy) 
          Some(new NonTemplateMemberImpl(bSym, implConv, inTpl) with Val {
            override lazy val comment = // The analyser does not duplicate the lazy val's DocDef when it introduces its accessor.
              thisFactory.comment(bSym.accessed, inTpl) // This hack should be removed after analyser is fixed.
            override def isLazyVal = true
          })
      else if (bSym.isGetter && bSym.accessed.isMutable)
        Some(new NonTemplateMemberImpl(bSym, implConv, inTpl) with Val {
          override def isVar = true
        })
      else if (bSym.isMethod && !bSym.hasAccessorFlag && !bSym.isConstructor && !bSym.isModule) {
        val cSym = { // This unsightly hack closes issue #4086.
          if (bSym == definitions.Object_synchronized) {
            val cSymInfo = (bSym.info: @unchecked) match {
              case PolyType(ts, MethodType(List(bp), mt)) =>
                val cp = bp.cloneSymbol.setInfo(appliedType(definitions.ByNameParamClass.typeConstructor, List(bp.info)))
                PolyType(ts, MethodType(List(cp), mt))
            }
            bSym.cloneSymbol.setInfo(cSymInfo)
          }
          else bSym
        }
        Some(new NonTemplateParamMemberImpl(cSym, implConv, inTpl) with HigherKindedImpl with Def {
          override def isDef = true
        })
      }
      else if (bSym.isConstructor)
        Some(new NonTemplateParamMemberImpl(bSym, implConv, inTpl) with Constructor {
          override def isConstructor = true
          def isPrimary = sym.isPrimaryConstructor
        })
      else if (bSym.isGetter) // Scala field accessor or Java field
        Some(new NonTemplateMemberImpl(bSym, implConv, inTpl) with Val {
          override def isVal = true
        })
      else if (bSym.isAbstractType)
        Some(new NonTemplateMemberImpl(bSym, implConv, inTpl) with TypeBoundsImpl with HigherKindedImpl with AbstractType {
          override def isAbstractType = true
        })
      else if (bSym.isAliasType)
        Some(new NonTemplateMemberImpl(bSym, implConv, inTpl) with HigherKindedImpl with AliasType {
          override def isAliasType = true
          def alias = makeTypeInTemplateContext(sym.tpe.dealias, inTpl, sym)
        })
      else if (bSym.isPackage)
        inTpl match { case inPkg: PackageImpl =>  makePackage(bSym, inPkg) }
      else if ((bSym.isClass || bSym.isModule) && templateShouldDocument(bSym))
        Some(makeDocTemplate(bSym, inTpl))
      else
        None
    }

    if (!localShouldDocument(aSym) || aSym.isModuleClass || aSym.isPackageObject || aSym.isMixinConstructor)
      Nil
    else {
      val allSyms = useCases(aSym, inTpl.sym) map { case (bSym, bComment, bPos) =>
        addCommentBody(bSym, inTpl, bComment, bPos)
      }
      (allSyms :+ aSym) flatMap { makeMember0(_) }
    }
    
  }

  /** */
  def makeTypeParam(aSym: Symbol, inTpl: => TemplateImpl): TypeParam = {
    dbg("makeTypeParam(" + aSym + ", inTpl)")      	
    new ParameterImpl(aSym, inTpl) with TypeBoundsImpl with HigherKindedImpl with TypeParam {
      def isTypeParam = true
      def isValueParam = false
      def variance: String = {
        if (sym hasFlag Flags.COVARIANT) "+"
        else if (sym hasFlag Flags.CONTRAVARIANT) "-"
        else ""
      }
    }
  }

  /** */
  def makeValueParam(aSym: Symbol, inTpl: => DocTemplateImpl): ValueParam = {
  	dbg("makeValueParam(" + aSym + ", inTpl)")
    makeValueParam(aSym, inTpl, aSym.nameString)
  }

  /** */
  def makeValueParam(aSym: Symbol, inTpl: => DocTemplateImpl, newName: String): ValueParam = {
  	dbg("makeValueParam(" + aSym + ", inTpl, " + newName + ")")
    new ParameterImpl(aSym, inTpl) with ValueParam {
      override val name = newName
      def isTypeParam = false
      def isValueParam = true
      def defaultValue =
        if (aSym.hasDefault) {
          // units.filter should return only one element
          (currentRun.units filter (_.source.file == aSym.sourceFile)).toList match {
            case List(unit) =>
              (unit.body find (_.symbol == aSym)) match {
                case Some(ValDef(_,_,_,rhs)) => makeTree(rhs)
                case _ => None
              }
            case _ => None
          }
        }
        else None
      def resultType =
        makeTypeInTemplateContext(sym.tpe, inTpl, sym)
      def isImplicit = aSym.isImplicit
    }
  }

  /** */
  def makeTypeInTemplateContext(aType: Type, inTpl: => TemplateImpl, dclSym: Symbol): TypeEntity = {
  	dbg("makeTypeInTemplateContext(" + aType + ", inTpl, " + dclSym + ")")
    def ownerTpl(sym: Symbol): Symbol =
      if (sym.isClass || sym.isModule || sym == NoSymbol) sym else ownerTpl(sym.owner)
    val tpe =
      if (thisFactory.settings.useStupidTypes.value) aType else {
        def ownerTpl(sym: Symbol): Symbol =
          if (sym.isClass || sym.isModule || sym == NoSymbol) sym else ownerTpl(sym.owner)
        val fixedSym = if (inTpl.sym.isModule) inTpl.sym.moduleClass else inTpl.sym
        aType.asSeenFrom(fixedSym.thisType, ownerTpl(dclSym))
      }
    makeType(tpe, inTpl)
  }
  
  /** */
  def makeType(aType: Type, inTpl: => TemplateImpl): TypeEntity = {
  	dbg("makeType(" + aType + ", inTpl)")
    def templatePackage = closestPackage(inTpl.sym)
    
    new TypeEntity {
      private val nameBuffer = new StringBuilder
      private var refBuffer = new immutable.TreeMap[Int, (TemplateEntity, Int)]
      private def appendTypes0(types: List[Type], sep: String): Unit = types match {
        case Nil =>
        case tp :: Nil =>
          appendType0(tp)
        case tp :: tps =>
          appendType0(tp)
          nameBuffer append sep
          appendTypes0(tps, sep)
      }

      private def appendType0(tpe: Type): Unit = tpe match {
        /* Type refs */
        case tp: TypeRef if definitions.isFunctionType(tp) =>
          val args = tp.normalize.typeArgs
          nameBuffer append '('
          appendTypes0(args.init, ", ")
          nameBuffer append ") ⇒ "
          appendType0(args.last)
        case tp: TypeRef if definitions.isScalaRepeatedParamType(tp) =>
          appendType0(tp.args.head)
          nameBuffer append '*'
        case tp: TypeRef if definitions.isByNameParamType(tp) =>
          nameBuffer append "⇒ "
          appendType0(tp.args.head)
        case tp: TypeRef if definitions.isTupleTypeOrSubtype(tp) =>
          val args = tp.normalize.typeArgs
          nameBuffer append '('
          appendTypes0(args, ", ")
          nameBuffer append ')'
        case TypeRef(pre, aSym, targs) =>
          val preSym = pre.widen.typeSymbol
          // There's a work in progress here trying to deal with the
          // places where undesirable prefixes are printed.
          // ...
          // If the prefix is something worthy of printing, see if the prefix type
          // is in the same package as the enclosing template.  If so, print it
          // unqualified and they'll figure it out.
          //
          // val stripPrefixes = List(templatePackage.fullName + ".", "package.", "java.lang.")
          // if (!preSym.printWithoutPrefix) {
          //   nameBuffer append stripPrefixes.foldLeft(pre.prefixString)(_ stripPrefix _)
          // }
          val bSym = normalizeTemplate(aSym)
          if (bSym.isNonClassType)
            nameBuffer append bSym.decodedName
          else {
            val tpl = makeTemplate(bSym)
            val pos0 = nameBuffer.length
            refBuffer += pos0 -> (tpl, tpl.name.length)
            nameBuffer append tpl.name
          }
          if (!targs.isEmpty) {
            nameBuffer append '['
            appendTypes0(targs, ", ")
            nameBuffer append ']'
          }
        /* Refined types */
        case RefinedType(parents, defs) =>
          val ignoreParents = Set(AnyClass, ObjectClass)
          val filtParents = parents filterNot (x => ignoreParents(x.typeSymbol)) match {
            case Nil    => parents
            case ps     => ps
          }
          appendTypes0(filtParents, " with ")
          // XXX Still todo: properly printing refinements.
          // Since I didn't know how to go about displaying a multi-line type, I went with
          // printing single method refinements (which should be the most common) and printing
          // the number of members if there are more.
          defs.toList match {
            case Nil      => ()
            case x :: Nil => nameBuffer append (" { " + x.defString + " }")
            case xs       => nameBuffer append (" { ... /* %d definitions in type refinement */ }" format xs.size)
          }
        /* Eval-by-name types */
        case NullaryMethodType(result) =>
          nameBuffer append '⇒'
          appendType0(result)
        /* Polymorphic types */
        case PolyType(tparams, result) => assert(tparams nonEmpty)
//          throw new Error("Polymorphic type '" + tpe + "' cannot be printed as a type")
          def typeParamsToString(tps: List[Symbol]): String = if(tps isEmpty) "" else
            tps.map{tparam =>
              tparam.varianceString + tparam.name + typeParamsToString(tparam.typeParams)
            }.mkString("[", ", ", "]")
          nameBuffer append typeParamsToString(tparams)
          appendType0(result)
        case tpen =>
          nameBuffer append tpen.toString
      }
      appendType0(aType)
      val refEntity = refBuffer
      val name = optimize(nameBuffer.toString)
    }
  }

  def templateShouldDocument(aSym: Symbol): Boolean = {  	  	
  	// TODO: document sourceless entities (e.g., Any, etc), based on a new Setting to be added
  	(aSym.isPackageClass || (aSym.sourceFile != null)) && localShouldDocument(aSym) &&
    ( aSym.owner == NoSymbol || templateShouldDocument(aSym.owner) ) && !isEmptyJavaObject(aSym)
  }
  
  def isEmptyJavaObject(aSym: Symbol): Boolean = {
    def hasMembers = aSym.info.members.exists(s => localShouldDocument(s) && (!s.isConstructor || s.owner == aSym))
    aSym.isModule && aSym.isJavaDefined && !hasMembers
  }

  def localShouldDocument(aSym: Symbol): Boolean = {
    !aSym.isPrivate && (aSym.isProtected || aSym.privateWithin == NoSymbol) && !aSym.isSynthetic
  }
  
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

  	// The implicit constraints: we gather constraints about the type. The constraints can be of several types:
  	//  - the existence of implicit parameters of certain types (see removeImplicitParameters)
    //  - type bounds and type substitutions
  	var constraints: List[Block] = Nil  	

  	// This function removes implicit values from the view and adds them as constraints
  	def removeImplicitParameters(ty: Type): Type = ty match {
  		case MethodType(params, resultType) if (params.filter(_.isImplicit).length == 0) =>
  			MethodType(params, removeImplicitParameters(resultType))
		  case MethodType(params, resultType) if (params.filterNot(_.isImplicit).length == 0) =>
		    constraints = constraints ::: params.map(param => Paragraph(Chain(Text("An implicit value of type ")::Monospace(Text(typeVarToOrigin(param.tpe).toString))::Text(" is in scope.")::Nil)))
		    removeImplicitParameters(resultType)
		  case other =>
		    other // It might be a class, a method or anything else it wants to be, we just strip all implicit params
  	}  	

    // we don't want typeVars, we want our original type params back
	  object typeVarToOrigin extends TypeMap {
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

  	// obtain the result after applying the view
    val typed: Tree = if (res.tree != EmptyTree) {
    	// here we need to remove all implicits and add them as constraints
    	val coercion = res.tree.setType(removeImplicitParameters(res.tree.tpe))

    	// and get the view applied to an argument
      val viewApply = new ApplyImplicitView(coercion, List(Ident("<argument>") setType coercion.tpe.paramTypes.head))      
      global.analyzer.newTyper(context.makeImplicit(context.reportAmbiguousErrors)).silent(_.typed(viewApply, global.analyzer.EXPRmode, WildcardType), false) match {
          case ex: Throwable =>
            println("typing coercion failed "+ ex)
            coercion
          case t: Tree => t
        }
    } else EmptyTree

    def uniteConstraints(constr: TypeConstraint): TypeConstraint =
      try {
      	new TypeConstraint(List(wildcardToNothing(lub(constr.loBounds  map typeVarToOrigin))), 
      									   List(wildcardToNothing(glb(constr.hiBounds  map typeVarToOrigin)))) 
      	// BoundedWildcardType(TypeBounds(lub(constr.loBounds), glb(constr.hiBounds)))
      } catch { 
      	// does this actually ever happen? (probably when type vars occur in the bounds)	
      	case x: Throwable => new TypeConstraint(constr.loBounds.distinct, constr.hiBounds.distinct) 
      } 

    // the type vars need to be propagated until we ask for the members, then you can replace them by some simplified representation
    // in principle, we should solve the set of type variables, but this is unlikely to work since we can't really know any of them concretely
    // for now, just simplify them, and if their upper bounds =:= lower bounds, replace by that type,
    // else, if the lub and the glb could be computed, use an existential with the given lower and upper bound
    // if all that fails, you'll need some textual representation of the TypeConstraint
    val toTp = typeVarToOrigin(typed.tpe.finalResultType)
    println("conversion "+ typed.symbol +" from "+ tp +" to "+ toTp)
    
    // Transform bound constraints into scaladoc constraints
    val boundConstraints = (tpars zip (constrs map uniteConstraints)) flatMap {
    	case (tp, constr) => {

    		// Pretty name for the type 
    		val tpString: String = tp match {
    			case ts: TypeSymbol => ts.name.toString
    			case _ => tp.toString
    		}

    		(constr.loBounds, constr.hiBounds) match {
    			// Most generic bounds
    			case (List(lb), List(ub)) if ((lb == NothingClass.tpe) && (ub == AnyClass.tpe)) =>
		    		Nil
		      // Same bound on both sides => equality
		    	case (List(lb), List(ub)) if (lb == ub) =>		    		
		    		List(Paragraph(Chain(Text(tpString + " is equal to " + lb + ": ")::Monospace(Text(tpString + " =: " + lb))::Nil)))
		    	// Only lower bound
		    	case (List(lb), List(ub)) if (ub == AnyClass.tpe) =>
		    		List(Paragraph(Chain(Text(tpString + " is lower bounded by " + lb + ": ")::Monospace(Text(tpString + " >: " + lb))::Nil)))
		    	// Only upper bound
		    	case (List(lb), List(ub)) if (lb == NothingClass.tpe) =>
		    		List(Paragraph(Chain(Text(tpString + " is upper bounded by " + ub + ": ")::Monospace(Text(tpString + " <: " + ub))::Nil)))
		    	// Single bounds, not obvious
		    	case (List(lb), List(ub)) =>
		    		List(Paragraph(Chain(Text(tpString + " is bounded by " + lb + " and " + ub + ": ")::Monospace(Text(tpString + " >: " + lb + " <: " + ub))::Nil)))
		    	// Multiple bounds - the complex case, shouldn't occur in practice
		    	case _ =>
		    		List(Paragraph(Chain(Text("Complex constraint: ")::Monospace(Text(tpString + " " + constr))::Nil)))
    		}
    	}
  	}
    
    // Transform res.subst substitutions into scaladoc constraints
    val substConstraints = (res.subst.from zip res.subst.to) flatMap { case (from, to) =>
    	List(Paragraph(Chain(Text("Substitute type of ")::Monospace(Text(from.toString))::Text(" to ")::Monospace(Text(to.toString))::Nil)))
    	
    }
    
    constraints = constraints ::: boundConstraints ::: substConstraints
    constraints foreach println
    
    val implicitMembers = toTp.nonPrivateMembers. 
    											  filter(implicitShouldDocument(_)).
    											  map { symbol => symbol.cloneSymbol.setInfo(toTp memberInfo symbol) } 
    
    implicitMembers foreach (sym => println("  - "+ sym.decodedName +" : " + sym.info))
    
    // Create the implicit conversion object
    val _constraints = constraints
    val implicitConversion = new ImplicitConversion{ 
										           val target = makeType(toTp, inTpl) 
										           val convertor = Body(List(Code(res.tree.toString)))
										           val constraints = Body(List(UnorderedList(_constraints)))
										           val getBody = {
										          	 val header = Paragraph(Bold(Chain(Text("Member inherited by implicit conversion to ")::Monospace(Text(target.toString()))::Text(" by ")::Monospace(Text(res.tree.symbol.toString))::Text(" in ")::Monospace(Text(res.tree.symbol.owner.toString))::Text(".")::Nil)))
										          	 val constraints: List[Block] = _constraints.length match {
										          		 case 0 => Nil
										          		 case 1 => List(Paragraph(Text("The implicit conversion will take place only if: ")), UnorderedList(_constraints.head :: Nil))
										          		 case 2 => List(Paragraph(Text("The implicit conversion will take place only if all the constraints are satisfied:")), UnorderedList(_constraints)) 
										          	 }
										          	 Body(header :: constraints ::: HorizontalRule() :: Nil)
										           }
										         }
    
    implicitMembers.map((_, implicitConversion))
  }
}

