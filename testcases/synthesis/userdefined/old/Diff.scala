import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._
import leon.grammar.Grammar._
import leon.annotation.grammar._

object Diff {

  def delete[A](in1: List[A], v: A): List[A] = {
    in1 match {
      case Cons(h,t) =>
        if (h == v) {
          delete(t, v)
        } else {
          Cons(h, delete(t, v))
        }
      case Nil() =>
        Nil[A]()
    }
  } ensuring { _.content == in1.content -- Set(v) }

  @production(100) def useDelete[A](in1: List[A], v: A): List[A] = delete(in1, v)
  /*
  def diff[A](in1: List[A], in2: List[A]): List[A] = {
    in2 match {
      case Nil() =>
        in1
      case Cons(h, t) =>
        delete(diff(in1, t), h)
    }
  } ensuring { _.content == in1.content -- in2.content }
  */
  def diff[A](in1: List[A], in2: List[A]) = choose {
    (out : List[A]) =>
      out.content == in1.content -- in2.content
  }
}
