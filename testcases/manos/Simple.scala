object Simple {

  abstract sealed class Top
    
  abstract sealed class Middle extends Top

  case class Node1(i:Int, t:Top) extends Top
  case class Leaf1(i:Int)        extends Top
  

  case class Node2(i:Int, m:Middle) extends Middle 
  case class Leaf2()                extends Middle

  def fun1(t: Top) : Int = t match {
    case Node1(i, t) => i + fun1(t)
    case Leaf1(i)    => i

    case Node2(i, m) => i * fun2(m)
    case Leaf2()     => 1
  }

  def fun2(m : Middle) : Int = m match {
    case Node2(i, m) => 2 * i + fun2(m)
    case Leaf2()     => 42
  }

  def fun3(n : Node2) : Int = n match {
    case Node2(i,m) => m match {
      case n2@Node2(_,_) => 1 + fun3(n2)
      case Leaf2()       => 0   
    }
  }
  /*
  // Problematic functions that will be transormed incorrectly
  // (but are detected as such)
  def ft1(t : Top) : Int = ft2(t) + 1
  def ft2(t : Top) : Int = ft1(t) - 1
  */

  /**************/
  // Test patterm matching

  abstract sealed class Foo
  case class Foo1(child : Foo) extends Foo
  case class Foo2()            extends Foo
  def fooFun(f: Foo) : Int = f match {
    case Foo1(child)      => fooFun(child) * 2
    case Foo2() if true   => 0
    case Foo2() if false  => 1
  }



}
