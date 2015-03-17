package shapeless.examples

import shapeless._
import ops.coproduct.IsCCons
import ops.hlist.IsHCons


trait Pointed[F[_]] { def point[A](a: A): F[A] }


sealed trait IList[+A]
case class ICons[A](h: A, t: IList[A]) extends IList[A]
case object INil extends IList[Nothing]
// case class INil[A]() extends IList[A]


package PointedDemoDefns {
  case class Foo[T](t: T, ts: List[T])

  sealed trait Tree[T]
  case class Leaf[T](t: T) extends Tree[T]
  case class Node[T](l: Tree[T], r: Tree[T]) extends Tree[T]
}

object PointedDemo extends App {
  import PointedDemoDefns._
  import pointedSyntax._

  type L[A] = A :: HNil
  Pointed[L]

  type C[A] = A :+: CNil
  Pointed[C]

  type C2[A] = Id[A] :+: CNil
  Pointed[C2]

  type C3[A] = L[A] :+: CNil
  Pointed[C3]

  Pointed[Option]

  Pointed[Tree]

  type C4[A] = Const[INil.type]#λ[A] :: HNil
  IsHCons1[C4, Pointed, Pointed]

  // FAILS FOR UNKNOWN REASON YET
  type C5[A] = A :: Const[INil.type]#λ[A] :: HNil
  IsHCons1[C5, Pointed, Pointed]

  type C6[A] = A :: IList[A] :: HNil
  IsHCons1[C6, Pointed, Pointed]

  Pointed[List]

  Pointed[Foo]

  assert(5.point[Option] == Some(5))
  assert("toto".point[Tree] == Leaf("toto"))
  assert(true.point[IList] == ICons(true, INil))
  assert(1.234.point[List] == List(1.234))

  assert("tata".point[Foo] == Foo("tata", Nil))

}


object Pointed extends Pointed0 with Pointed1{
  def apply[F[_]](implicit f: Lazy[Pointed[F]]): Pointed[F] = f.value

  implicit val idPointed: Pointed[Id] =
    new Pointed[Id] {
      def point[A](a: A): Id[A] = a
    }


  // implicit def hcons1[F[_]: Pointed, C](
  //   implicit pt: Pointed[({type λ[A] = Const[C]#λ[A] :: HNil})#λ]
  // ) = new IsHCons1[({type λ[A] = F[A] :: Const[C]#λ[A] :: HNil})#λ, Pointed, Pointed] {
  //   type H[t] = F[t]
  //   type T[u] = ({type λ[A] = Const[C]#λ[A] :: HNil})#λ[u]

  //   def pack[A](u: (F[A], ({type λ[A] = Const[C]#λ[A] :: HNil})#λ[A])): ({type λ[A] = F[A] :: Const[C]#λ[A] :: HNil})#λ[A] = u._1 :: u._2
  //   def unpack[A](p: ({type λ[A] = F[A] :: Const[C]#λ[A] :: HNil})#λ[A]): (F[A], ({type λ[A] = Const[C]#λ[A] :: HNil})#λ[A]) = p.head -> p.tail

  //   def mkFhh: Pointed[F] = Pointed[F]
  //   def mkFtt: Pointed[({type λ[A] = Const[C]#λ[A] :: HNil})#λ] = pt
  // }

  // HACKING the fact that CNil can't be pointed
  implicit def isHPointedSingle[C](
    implicit pc: Lazy[Pointed[Const[C]#λ]]
  ): Pointed[({type λ[A] = Const[C]#λ[A] :: HNil })#λ] =
    new Pointed[({type λ[A] = Const[C]#λ[A] :: HNil })#λ] {
        def point[A](a: A): Const[C]#λ[A] :: HNil = pc.value.point(a) :: HNil
    }

  // HACKING the fact that CNil can't be pointed
  implicit def isCPointedSingle2[C](
    implicit pc: Lazy[Pointed[Const[C]#λ]]
  ): Pointed[({type λ[A] = Const[C]#λ[A] :+: CNil })#λ] =
    new Pointed[({type λ[A] = Const[C]#λ[A] :+: CNil })#λ] {
        def point[A](a: A): Const[C]#λ[A] :+: CNil = Inl(pc.value.point(a))
    }

  implicit def generic[F[_]](implicit gen: Generic1[F, Pointed]): Pointed[F] =
    new Pointed[F] {
      def point[A](a: A): F[A] = gen.from(gen.fr.point(a))
    }
}

trait Pointed0 {
  // HACKING the fact that CNil can't be pointed
  implicit def isCPointedSingle[F[_]](
    implicit pf: Lazy[Pointed[F]]
  ): Pointed[({type λ[A] = F[A] :+: Const[CNil]#λ[A] })#λ] =
    new Pointed[({type λ[A] = F[A] :+: Const[CNil]#λ[A] })#λ] {
        def point[A](a: A): F[A] :+: Const[CNil]#λ[A] = Inl(pf.value.point(a))
    }


  implicit def hcons[F[_]](implicit ihc: IsHCons1[F, Pointed, Pointed]): Pointed[F] =
    new Pointed[F] {
      def point[A](a: A): F[A] = {
        ihc.pack(ihc.fh.point(a), ihc.ft.point(a))
      }
    }

  implicit def ccons[F[_]](implicit ihc: IsCCons1[F, Pointed, Pointed]): Pointed[F] =
    new Pointed[F] {
      def point[A](a: A): F[A] = {
        ihc.pack(Left(ihc.fh.point(a)))
      }
    }


}

trait Pointed1 {

  // HACKING the fact that CNil can't be pointed
  implicit def isCPointedSingle2: Pointed[({type λ[A] = A :+: Const[CNil]#λ[A] })#λ] =
    new Pointed[({type λ[A] = A :+: Const[CNil]#λ[A] })#λ] {
        def point[A](a: A): A :+: Const[CNil]#λ[A] = Inl(a)
    }

  implicit def constHNilPointed: Pointed[Const[HNil]#λ] =
    new Pointed[Const[HNil]#λ] {
      def point[A](a: A): HNil = HNil
    }

  // HACKING the fact that Pointed can't be built with all Const (just for singletons)
  implicit def constNilPointed: Pointed[Const[Nil.type]#λ] =
    new Pointed[Const[Nil.type]#λ] {
      def point[A](a: A): Nil.type = Nil
    }

  implicit def constINilPointed: Pointed[Const[INil.type]#λ] =
    new Pointed[Const[INil.type]#λ] {
      def point[A](a: A): INil.type = INil
    }

  implicit def constNonePointed: Pointed[Const[None.type]#λ] =
    new Pointed[Const[None.type]#λ] {
      def point[A](a: A): None.type = None
    }
}

// Pointed syntax
object pointedSyntax {
  implicit def pointedOps[A](a: A): PointedOps[A] = new PointedOps(a)

  class PointedOps[A](a: A) {
    def point[F[_]](implicit F: Pointed[F]): F[A] = F.point(a)
  }
}
