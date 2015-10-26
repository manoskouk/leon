/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test

import leon.DefaultReporter

class TestSilentReporter extends DefaultReporter(Set()) {
  var lastErrors: List[String] = Nil

  override def emit(msg: Message): Unit = msg match { 
    case Message(this.ERROR | this.FATAL, _, msg) =>
      lastErrors :+= msg.toString
    case _ =>
  }
}
