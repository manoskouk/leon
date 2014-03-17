/* Copyright 2009-2014 EPFL, Lausanne */

package leon

import scala.annotation.StaticAnnotation

@annotation.ignore
object annotation {
  class induct     extends StaticAnnotation
  class axiomatize extends StaticAnnotation
  class main       extends StaticAnnotation
  class verified   extends StaticAnnotation
  class proxy      extends StaticAnnotation
  class ignore     extends StaticAnnotation
  class forceMemo  extends StaticAnnotation
}

