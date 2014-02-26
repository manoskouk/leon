/**
 * Working around not being able to find files by hard-coding the regression directory
 */

package leon.test
import leon.test._
import java.io.File
/**
 * topResourcesDir is the hardcoded resource directory on this machine
 */
class LeonEclipseTestSuite(private val topResourcesDir:String, private val topOutputDir:String) extends LeonTestSuite {
  
  override def filesInResourceDir(dir : String, filter : String=>Boolean = all) : Iterable[File] = {
    import scala.collection.JavaConversions._

    val asFile = new File(topResourcesDir + dir)

    asFile.listFiles().filter(f => filter(f.getPath()))
    
  }
  
  override def resourceDir(dir : String ) = new File(topResourcesDir + dir)  
  
  def outputDir(dir : String) = new File(topOutputDir + dir)
}