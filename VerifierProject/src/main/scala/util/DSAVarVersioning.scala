package util

import scala.collection.mutable

/**
  * 
  */
class DSAVarVersioning {
  private val separator = "_"
  private val versioning = mutable.HashMap[String, Int]()
  private val snapshot = mutable.HashMap[String, Int]()
  private val ignoredVars = mutable.Set[String]()                // variables that should not be versioned

  private def getVersion(varName: String): Int = versioning.getOrElse(varName, -1)
  private def setVersion(varName: String, varVersion: Int): Unit = versioning.put(varName, varVersion)

  private def constructIdentifier(varName: String, varVersion: Int): String = varName + separator + varVersion

  /**
    * Adds variable to the ignored list, i.e., the variables that should not be versioned
    * @param varName is the name of the variable
    */
  def addIgnoredVar(varName: String): Unit = ignoredVars += varName

  /**
    * Returns a fresh identifier for a variable based on its name and the underlying versioning system.
    * @param varName is the name of the variable for which we request a new identifier.
    * @return a fresh identifier.
    */
  def getNewIdentifier(varName: String): String = {
    var version = getVersion(varName)
    version += 1
    setVersion(varName, version)
    constructIdentifier(varName, version)
  }

  /**
    * Returns the last identifier that has been created for a variable.
    * @param varName is the name of the variable for which we request the last created identifier.
    * @return the last created identifier.
    */
  def getLastIdentifier(varName: String): String = {
    if (ignoredVars.contains(varName)) return varName

    val version = getVersion(varName)
    require(version >= 0, s"Variable $varName has not been versioned!")
    constructIdentifier(varName, version)
  }

  def takeSnapshot(): Unit = {
    snapshot.clear()
    snapshot ++= versioning
  }

  def revertToSnapshot(): Unit = {
    versioning.clear()
    versioning ++= snapshot
  }
}
