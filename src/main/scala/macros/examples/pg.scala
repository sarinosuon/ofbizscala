package macros.examples

import scala.collection.mutable.HashMap
import language.experimental.macros
import reflect.macros.Context
import scala.annotation.StaticAnnotation
import scala.collection.mutable.{ListBuffer, Stack}
import java.io.FileWriter
import java.util.Properties
import java.util.ArrayList
import java.sql.DriverManager

object PGMacro {

 def getProcs(server: String, db: String, username: String, password: String, schema: String) : List[List[String]] =  {
    val url = s"jdbc:postgresql://$server:5432/$db:retrieveMessagesFromServerOnGetMessage=true"

    val prop = new Properties
    prop.setProperty("user", username)
    prop.setProperty("password", password)
    Class.forName("org.postgresql.Driver")
    val conn = DriverManager.getConnection(url)

    val SQL = """
        SELECT n.nspname as "Schema",
         p.proname as "name",
         pg_catalog.pg_get_function_result(p.oid) as "args_out",
         pg_catalog.pg_get_function_arguments(p.oid) as "args_in",
        CASE
         WHEN p.proisagg THEN 'agg'
         WHEN p.proiswindow THEN 'window'
         WHEN p.prorettype = 'pg_catalog.trigger'::pg_catalog.regtype THEN 'trigger'
         ELSE 'normal'
        END as "Type",
        CASE
         WHEN p.provolatile = 'i' THEN 'immutable'
         WHEN p.provolatile = 's' THEN 'stable'
         WHEN p.provolatile = 'v' THEN 'volatile'
        END as "Volatility",
         pg_catalog.pg_get_userbyid(p.proowner) as "Owner",
         l.lanname as "Language",
         p.prosrc as "Source code",
         pg_catalog.obj_description(p.oid, 'pg_proc') as "Description"
        FROM pg_catalog.pg_proc p
            LEFT JOIN pg_catalog.pg_namespace n ON n.oid = p.pronamespace
            LEFT JOIN pg_catalog.pg_language l ON l.oid = p.prolang
             WHERE n.nspname = ?
        ORDER BY 1, 2, 4;
    """
    val st = conn.prepareStatement(SQL)
    st.setString(1, schema)
    val rs = st.executeQuery()

    val arr = new ArrayList[List[String]]

    while (rs.next()) {
        arr.add(List(rs.getString("name"), rs.getString("args_in"), rs.getString("args_out")))
    }
    rs.close()
    st.close()
    conn.close()
    arr.toArray.toList.asInstanceOf[List[List[String]]]
}



  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._
    var data: List[List[String]] = Nil

    val mapPGToScalaType = HashMap(
        "integer" -> "Int",
        "numeric" -> "Int",
        "real" -> "Double",
        "smallint" -> "Int",
        "text" -> "String",
        "double precision" -> "Double",
        "character varying" -> "String")

    def convPGToScalaType(theType: String) = mapPGToScalaType.getOrElse(theType, "Any")

    val mapPGToJDBCJavaMethod = HashMap(
        "integer" -> "Int",
        "numeric" -> "Int",
        "real" -> "Double",
        "smallint" -> "Int",
        "double precision" -> "Double",
        "text" -> "String",
        "character varying" -> "String")

    def convPGToJDBCJavaMethod(paramType: String) = mapPGToJDBCJavaMethod.getOrElse(paramType, "String")

    val mapPGToJDBCOracleType = HashMap(
        "integer" -> "INTEGER",
        "numeric" -> "INTEGER",
        "real" -> "DOUBLE",
        "smallint" -> "INTEGER",
        "double precision" -> "DOUBLE",
        "text" -> "VARCHAR",
        "character varying" -> "VARCHAR")

    def convPGToJDBCOracleType(paramType: String) = mapPGToJDBCOracleType.getOrElse(paramType, "VARCHAR")

    def generateCodeBlock(procName: String,
    					  setMethods: List[(String, String)],
    					  argOut: String) : Block = {
      val multipleInjects = List.fill(setMethods.length)("?").mkString(", ")
      val sqlText = Literal(Constant("{ ? = call math." + procName + "(" + multipleInjects + ") }"))
      val paramOut = Select(Ident(TermName("Types")), TermName(convPGToJDBCOracleType(argOut)))

      val setMethodsExpr = setMethods.zipWithIndex.map{ case(e, i) =>
        						Apply(Select(Ident(TermName("fun")), TermName(e._2)),
        							  List(Literal(Constant(i+2)), Ident(TermName(e._1))))
                              }

      // always first pos
      val resultExpr = Apply(Select(Ident(TermName("fun")), TermName("get" + convPGToJDBCJavaMethod(argOut))), List(Literal(Constant(1))))

      val rest = q"""
        import java.sql.Types
      	val fun = getConn().prepareCall($sqlText)
        fun.registerOutParameter(1, $paramOut)
        ..$setMethodsExpr
        fun.execute()
        val res = $resultExpr
        fun.close()
        res
      """
      rest.asInstanceOf[Block]
    }

    def generateArgsIn(procName: String, s: String, argOut: String) : (List[ValDef], Block) = {
      val allInfo = s.split(",").toList.map((one: String) => {
    	  val parts = one.trim().split(" ")
    	  val paramName = parts(0)
    	  val paramType = parts.toList.drop(1).mkString(" ")	// may be multiple words
    	  val scalaType = convPGToScalaType(paramType)
    	  val valdef = ValDef(Modifiers(), TermName(paramName), Ident(TypeName(scalaType)), EmptyTree)
    	  (valdef, paramName, paramType)
      })
      val allValDefs = allInfo.map{ x => x._1 }
  	  val inArgsSetMethod = allInfo.map{ x => (x._2, "set" + convPGToJDBCJavaMethod(x._3)) }

      val block = generateCodeBlock(procName, inArgsSetMethod, argOut)
  	  (allValDefs, block)
    }

    def convertNameToCamelCase(name: String): String = {
    	val nameParts = name.split("_")
      nameParts(0) + nameParts.drop(1).map{ x => x.substring(0,1).toUpperCase + x.substring(1)}.mkString("")
    }

    def generateMethods(infoList: List[List[String]]) : List[DefDef] = {
      infoList.map((arr: List[String]) => {
                                                val originalName = arr(0)
                                                val camelCaseName = convertNameToCamelCase(originalName)
                                                val argsIn = arr(1)
                                                val argOut = arr(2)
                                                val (argsInList, codeBlock) = generateArgsIn(originalName, argsIn, argOut)
                                                DefDef(Modifiers(),
                                                             TermName(camelCaseName),
                                                             List(),
                                                             List(argsInList),
                                                             Ident(TypeName(convPGToScalaType(argOut))),
                                                             codeBlock )
                                         })
    }

    val methods = generateMethods(data)

    import Flag._
    val result = {
      annottees.map(_.tree).toList match {
        case q"object $name extends ..$parents { ..$body }" :: Nil =>
          q"""
                object $name extends ..$parents {
                ..$methods
                ..$body
                }
          """
      }
    }
    c.Expr[Any](result)
  }
}


class pgmacro extends StaticAnnotation {
  def macroTransform(annottees: Any*) = macro PGMacro.impl
}

