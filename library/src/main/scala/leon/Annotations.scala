/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import scala.annotation.StaticAnnotation

object Annotations {
  class induct extends StaticAnnotation
  class axiomatize extends StaticAnnotation
  class main extends StaticAnnotation
  class forceMemo extends StaticAnnotation // annotates functions that the user wants to force-memoize during memoization transformation
}
