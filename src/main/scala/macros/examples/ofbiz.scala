package macros.examples

import scala.collection.mutable.HashMap
import language.experimental.macros
import reflect.macros.Context
import scala.annotation.StaticAnnotation
import scala.collection.mutable.{ListBuffer, Stack}
import java.io.FileWriter

import scala.xml.Node

object OFBizMacro {

   // tuple of: (args-required, args-optional)
  def partitionOptional(service: Node): (List[Node], List[Node]) = {
    val required = (service \ "attribute").filter( x => (x \ "@optional").text != "true").toList
    val optional = (service \ "attribute").filter( x => (x \ "@optional").text == "true").toList
    (required, optional)
  }

  // tuple of: (in, out)
  def partitionMode(service: Node): (List[Node], List[Node]) = {
    val input = (service \ "attribute").filter( x => { val mode = (x \ "@mode").text; mode == "IN"  || mode == "INOUT"}).toList
    val output = (service \ "attribute").filter( x => { val mode = (x \ "@mode").text; mode == "OUT" || mode == "INOUT" }).toList
    (input, output)
  }

  def getServiceObjects(ofBizDir: String) : List[Node] = {
        import scala.xml.XML.loadFile
        import scala.sys.process.Process
        import scala.sys.process.ProcessLogger


        def run(in: String): (List[String], List[String], Int) = {
          val qb = Process(in)
          var out = List[String]()
          var err = List[String]()

          val exit = qb ! ProcessLogger((s) => out ::= s, (s) => err ::= s)

          (out.reverse, err.reverse, exit)
        }

        import scala.collection.mutable.HashMap

        def unique[U](list: List[U]) : List[U] = { val hm = new HashMap[U,Int]; for (x <- list) { hm.put(x, 1) }; hm.keys.toList }

        val q = run("find " + ofBizDir + "  -name *service*.xml")._1
        def getServices(fname: String) : List[scala.xml.Node] = { val x = loadFile(fname); (x \\ "service").filter(x =>  (x \ "@name" != "") && (x \ "@engine" != "") ).toList }
        val combined = q.map(x => { val r = getServices(x); println(x); r })
        combined.flatten
  }

  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    import scala.reflect.internal.{Flags => InternalFlags}

    val DEFAULTPARAM = InternalFlags.DEFAULTPARAM.toLong.asInstanceOf[FlagSet]
    val PARAM = InternalFlags.PARAM.toLong.asInstanceOf[FlagSet]
    val PARAMACCESSOR = InternalFlags.PARAMACCESSOR.toLong.asInstanceOf[FlagSet]
    val PRIVATE = InternalFlags.PRIVATE.toLong.asInstanceOf[FlagSet]

    val mapJavaTypeToScalaType = HashMap(
        "Int" -> "Int",
        "java.lang.String" -> "String",
        "Long" -> "Long",
        "String" -> "String",
        "Double" -> "Double",
        "java.lang.Boolean" -> "Boolean",
        "Boolean" -> "Boolean",
        "Locale" -> "Any",
        "List" -> "List",
        "Map" -> "HashMap",
        "GenericValue" -> "Any",
        "org.ofbiz.entity.GenericValue" -> "Any"
        )

    def convJavaTypeToScalaType(paramType: String) = mapJavaTypeToScalaType.getOrElse(paramType, "Any")


    def getOptionalConstantForType(attrType: String) : Constant = {
      attrType match {
        case "Int" => Constant(0)
        case "Long" => Constant(0L)
        case "Double" => Constant(0.0)
        case "String" => Constant("")
        case "java.lang.String" => Constant("")
        case "Boolean" => Constant(false)
        case "java.lang.Boolean" => Constant(false)
        case "Locale" => Constant(null)
        case "List" => Constant(null)
        case "Map" => Constant(null)
        case "HashMap" => Constant(null)
        case _ => Constant(null)
      }
    }

    def getIntroValDefs(attributes: List[Node]) : List[ValDef] = {
      def generate(attrName: String, attrType: String): ValDef = {
    	  					val scalaType = convJavaTypeToScalaType(attrType)
    	  					if (scalaType == "HashMap")
    	  						ValDef(Modifiers(PARAMACCESSOR),
    	  						       TermName(attrName),
    	  						       AppliedTypeTree(Ident(TypeName("HashMap")), List(Ident(TypeName("Any")), Ident(TypeName("Any")))),
    	  						       EmptyTree)
    	  					else if (scalaType == "List")
    	  						ValDef(Modifiers(PARAMACCESSOR),
    	  						       TermName(attrName),
    	  						       AppliedTypeTree(Ident(TypeName("FastList")), List(Ident(TypeName("Any")))),
    	  						       EmptyTree)
    	  					else
    	  						ValDef(Modifiers(PARAMACCESSOR), TermName(attrName), Ident(TypeName(scalaType)), EmptyTree)
      }
      val subList = attributes.map( attr => { generate((attr \ "@name").text, (attr \ "@type").text) } )
      subList ++ List(generate("responseMessage", "String"))
    }

    def getInitializeValDefs(attributes: List[Node], allowOptional: Boolean=false) : List[ValDef] = {
      def generate(attrName: String, attrType: String, attrOptional: Boolean) : ValDef = {
    	  					val scalaType = convJavaTypeToScalaType(attrType)
    	  					val termName = if (scalaType == "HashMap")
                                   AppliedTypeTree(Ident(TypeName("HashMap")), List(Ident(TypeName("Any")), Ident(TypeName("Any"))))
    	  					               else if (scalaType == "List")
                                   AppliedTypeTree(Ident(TypeName("FastList")), List(Ident(TypeName("Any"))))
    	  									       else
    	  										       Ident(TypeName(scalaType))

    	  					if (attrOptional) {
    	  					    val optionalConstant = getOptionalConstantForType(attrType)
    	  						ValDef(Modifiers(PARAM | DEFAULTPARAM | PARAMACCESSOR), TermName(attrName), termName, Literal(optionalConstant))
    	  					} else {
    	  						ValDef(Modifiers(PARAM | PARAMACCESSOR), TermName(attrName), termName, EmptyTree)
    	  					}
      }
      val subList = attributes.map( attr => {
                                              val attrName = (attr \ "@name").text
                                              val attrType = (attr \ "@type").text
                                              val attrOptional = if (allowOptional) (attr \ "@optional").text == "true" else false
                                              generate(attrName, attrType, attrOptional)
                                                } )
     subList ++ List(generate("responseMessage", "String", true))    // because it is last, allow it to be optional
    }

    def getInitializeDefDef(attributes: List[Node],
                            allowOptional: Boolean=false,
                            requiresAuth: Boolean=false) : List[ValDef] = {

      def generate(attrName: String, attrType: String, attrOptional: Boolean): ValDef = {
    	  					val scalaType = convJavaTypeToScalaType(attrType)
    	  					val termName = if (scalaType == "HashMap")
    	  										       AppliedTypeTree(Ident(TypeName("HashMap")), List(Ident(TypeName("Any")), Ident(TypeName("Any"))))
    	  										     else if (scalaType == "List")
    	  										       AppliedTypeTree(Ident(TypeName("List")), List(Ident(TypeName("Any"))))
    	  									       else
    	  										      Ident(TypeName(scalaType))

    	  					if (attrOptional) {
    	  					    val optionalConstant = getOptionalConstantForType(attrType)
    	  						ValDef(Modifiers(PARAM | DEFAULTPARAM ), TermName(attrName), termName, Literal(optionalConstant))
    	  					} else {
    	  						ValDef(Modifiers(PARAM ), TermName(attrName), termName, EmptyTree)
    	  					}
      }

      val subList = attributes.map( attr => {
                                              val attrName = (attr \ "@name").text
                                              val attrType = (attr \ "@type").text
                                              val attrOptional = if (allowOptional) (attr \ "@optional").text == "true" else false
                                              generate(attrName, attrType, attrOptional)
                                             } )

     if (requiresAuth) {
         subList ++ List(generate("login__username", "String", true),
                         generate("login__password", "String", true))
     } else {
         subList
     }
    }

    def getMapBuilder(attributes: List[Node], requiresAuth: Boolean = false) : List[Apply] = {
      def generate(attrName: String): Apply = {
          val realAttrName = attrName.replaceAll("__", ".")    // really just used for login.username  and login.password
          Apply(Select(Literal(Constant(realAttrName)), TermName("$minus$greater")),
                List(Ident(TermName(attrName))))
      }

      val subList = attributes.map( attr => { generate((attr \ "@name").text) })

     if (requiresAuth) {
       subList ++ List(generate("login__username"), generate("login__password"))
     } else {
       subList
     }
  }


    def getResponseBuilder(outAttributes: List[Node]) : List[GenericApply] = {
      def generate(attrName: String,
                   attrType: String) : GenericApply = {
                  val scalaType = convJavaTypeToScalaType(attrType)
                  val optionalConstant = getOptionalConstantForType(attrType)
                  val res = if (scalaType == "HashMap")
                        Apply(Ident(TermName("toMap")),
                              List(TypeApply(Select(Apply(Select(Ident(TermName("__result")),
                                                             TermName("getOrElse")),
                                                      List(Literal(Constant(attrName)),
                                                           Literal(optionalConstant))),
                                                TermName("asInstanceOf")),
                                                              List(AppliedTypeTree(Ident(TypeName("FastMap")),
                                                                                   List(Ident(TypeName("Any")),
                                                                                        Ident(TypeName("Any"))))))))

                        else if (scalaType == "List")
                          TypeApply(Select(Apply(Select(Ident(TermName("__result")),
                                                             TermName("getOrElse")),
                                                      List(Literal(Constant(attrName)),
                                                           Literal(optionalConstant))),
                                                TermName("asInstanceOf")),
                                         List(AppliedTypeTree(Ident(TypeName("FastList")),
                                                                                   List(Ident(TypeName("Any"))))))
                    else
                            TypeApply(Select(Apply(Select(Ident(TermName("__result")), TermName("getOrElse")),
                                                   List(Literal(Constant(attrName)), Literal(optionalConstant))),
                                             TermName("asInstanceOf")), List(Ident(TypeName(scalaType))))
                  res

      }
      val subList = outAttributes.map( attr => { generate((attr \ "@name").text, (attr \ "@type").text) })
      subList ++ List(generate("responseMessage", "String"))
    }

    def getValDefsOptional(attributes: List[Node]) : List[ValDef] = {
      attributes.map( attr => {
    	  					val attrName = (attr \ "@name").text
    	  					val attrType = (attr \ "@type").text
    	  					val scalaType = convJavaTypeToScalaType(attrType)
    	  					ValDef(Modifiers(PARAMACCESSOR), TermName(attrName), Ident(TypeName(scalaType)), EmptyTree)
        				} )
    }

    // response class definition, call method
    def generateResponseClassForService(service: Node) : ClassDef = {
        val serviceName = (service \ "@name").text

    	// required IN
    	val inRequired = (service \ "attribute").filter( x => { val mode = (x \ "@mode").text
    															val optional = (x \ "@optional").text
    															(mode == "IN"  || mode == "INOUT") && (optional != "true")
    														  }).toList
    	// optional IN
    	val inOptional = (service \ "attribute").filter( x => { val mode = (x \ "@mode").text
    															val optional = (x \ "@optional").text
    															(mode == "IN"  || mode == "INOUT") && (optional == "true")
    														  }).toList

    	// OUT
    	val out = (service \ "attribute").filter( x => { val mode = (x \ "@mode").text
                                                       mode == "OUT"  || mode == "INOUT"
    														                     }).toList

      val allIntroValDefs = getIntroValDefs(out)
      val allInitializeValDefs= getInitializeValDefs(out, false)



      val allValDefInOptional = getValDefsOptional(inOptional)

      val theList = List(Select(Ident("scala"), TypeName("AnyRef")))

        val info = List(DefDef(Modifiers(),
    															             termNames.CONSTRUCTOR,
    															             List(),
    															             List(allInitializeValDefs),
    															                  TypeTree(), Block(List(pendingSuperCall), Literal(Constant(())))))

       val combined = allIntroValDefs ++ info

       ClassDef(Modifiers(), TypeName(serviceName + "ResponseC"), List(), Template(theList, noSelfType, combined))
    }

    // response class definition, call method
    def generateMethodCodeForService(service: Node) : DefDef = {
      val attributes = (service \ "attribute") //makeUnique((service \ "attribute").toList, (node: Node) => (node \ "@name").text)

      val serviceName = (service \ "@name").text
      val requiresAuth = (service \ "@auth").text == "true"

    	// required IN
    	val inRequired = attributes.filter( x => { val mode = (x \ "@mode").text
    															val optional = (x \ "@optional").text
    															(mode == "IN"  || mode == "INOUT") && (optional != "true")
    														  }).toList
    	// optional IN
    	val inOptional = attributes.filter( x => { val mode = (x \ "@mode").text
    															val optional = (x \ "@optional").text
    															(mode == "IN"  || mode == "INOUT") && (optional == "true")
    														  }).toList

    	// OUT
    	val out = attributes.filter( x => { val mode = (x \ "@mode").text
                                                       mode == "OUT"  || mode == "INOUT"
    														                     }).toList

      val initParams = getInitializeDefDef(inRequired ++ inOptional, true, requiresAuth)    // allow optional
      val mapBuilder = getMapBuilder(inRequired ++ inOptional, requiresAuth)
      val responseBuilder = getResponseBuilder(out)

      val allValDefInOptional = getValDefsOptional(inOptional)

  val responseClassName = serviceName + "ResponseC"

  val oneDef = DefDef(Modifiers(),
                   TermName(serviceName),
                   List(),
                   List(initParams),
                   Ident(TypeName(responseClassName)),
                   Block(List(ValDef(Modifiers(),
                                     TermName("__result"),
                                     TypeTree(),
                                     Apply(Ident(TermName("call")),
                                           List(Literal(Constant(serviceName)),
                                                Apply(Ident(TermName("HashMap")), mapBuilder))))),
                         Apply(Select(New(Ident(TypeName(responseClassName))), termNames.CONSTRUCTOR),
                               responseBuilder)))
       oneDef
  }

    def makeUnique[U, V](items: List[U], keyFun: (U) => V) : List[U] = {
      val hm = new HashMap[V, U]()
      for (item <- items) {
        val key = keyFun(item)
        hm.put(key, item)
      }
      hm.values.toList
    }

    def readServices(): List[Node] = {
      val services = MacroUtils.getServiceObjects()
      makeUnique(services, (node: Node) => (node \ "@name").text).filter( (node:Node) =>  {
                                                                             val name = (node \ "@name").text
                                                                             (name!= "createDataResource"
                                                                              && name != "EbayStoreImportTransaction"
                                                                              && name != "EbayStoreCreateTransactionShoppingCart"
                                                                              && name != "authenticationInterface")    //authenticationInterface has input args "login.username" and "login.password"
                                                                          })
    }

    val services = readServices() //MacroUtils.getServiceObjects()

    val manyResponseClasses = services.map(generateResponseClassForService(_))

    val manyMethods = services.map(generateMethodCodeForService(_))

    import Flag._
    val __result = {
      annottees.map(_.tree).toList match {
        case q"object $name extends ..$parents { ..$body }" :: Nil =>
          q"""
                object $name extends ..$parents {
                  import java.rmi.Naming
                  import javolution.util.FastMap
                  import javolution.util.FastList
                  import org.ofbiz.service.rmi.RemoteDispatcher
                  import scala.collection.mutable.HashMap
                  import scala.collection.JavaConversions._

                  var RMI_URL = "rmi://127.0.0.1:1099/RMIDispatcher"
                  var AUTH_USER_NAME = ""
                  var AUTH_PASSWORD = ""

                  def setRMIURL(newURL: String) { RMI_URL = newURL }
                  def setUserName(newUserName: String) { AUTH_USER_NAME = newUserName }
                  def setPassword(newPass: String) { AUTH_PASSWORD = newPass }

                  // ===================================
                  def toMap(info: FastList[FastMap[Any,Any]]) : List[HashMap[Any,Any]] = {
                    for (fm <- info.iterator().toList) yield {
                       val hm = new HashMap[Any,Any]
                       for (k <- fm.keySet()) {
                         hm.put(k, fm.get(k))
                       }
                       hm
                    }
                  }

                  def toMap(fm: FastMap[Any,Any]) : HashMap[Any,Any] = {
                       val hm = new HashMap[Any,Any]
                       for (k <- fm.keySet()) {
                         hm.put(k, fm.get(k))
                       }
                       hm
                  }

                 def call(serviceName: String, params: HashMap[String,Any]) : HashMap[String, Any] = {
                        val rd = Naming.lookup(RMI_URL).asInstanceOf[RemoteDispatcher]
                        val theMap: FastMap[String,Any] = FastMap.newInstance()
                        params.foreach{ case (key, value) => theMap.put(key, value) }
                        val result = rd.runSync(serviceName, theMap)
                        val hm = new HashMap[String,Any]
                        for (key <- result.keySet()) {
                          hm.put(key, result.get(key))
                        }
                        hm
                  }
                  // ===================================

                  ..$manyResponseClasses
                  ..$manyMethods

                ..$body

                }
        """
      }
    }
    val result = {
      annottees.map(_.tree).toList match {
        case q"object $name extends ..$parents { ..$body }" :: Nil =>
          q"""
                object $name extends ..$parents {
                  def conflict = 0
                }
        """
      }
    }
    debug(result)
    c.Expr[Any](result)
  }
}

class ofbizmacro extends StaticAnnotation {
  def macroTransform(annottees: Any*) = macro OFBizMacro.impl
}

