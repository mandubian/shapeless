package shapeless.examples

import shapeless._
import ops.coproduct.IsCCons
import ops.hlist.IsHCons


trait Pointed[F[_]] { def point[A](a: A): F[A] }

sealed trait IList[A]
case class ICons[A](h: A, t:A) extends IList[A]
case object INil extends IList[Nothing]

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

  // Pointed[List]

  assert(5.point[Option] == Some(5))
  assert(5.point[Tree] == Leaf(5))

}


object Pointed extends Pointed0 {
  def apply[F[_]](implicit f: Lazy[Pointed[F]]): Pointed[F] = f.value

  implicit val idPointed: Pointed[Id] =
    new Pointed[Id] {
      def point[A](a: A): Id[A] = a
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

  // HACKING the fact that CNil can't be pointed
  implicit def isCPointedSingle[F[_]](
    implicit pf: Lazy[Pointed[F]]
  ): Pointed[({type λ[A] = F[A] :+: Const[CNil]#λ[A] })#λ] =
    new Pointed[({type λ[A] = F[A] :+: Const[CNil]#λ[A] })#λ] {
        def point[A](a: A): F[A] :+: Const[CNil]#λ[A] = Inl(pf.value.point(a))
    }

  implicit def generic[F[_]](implicit gen: Generic1[F, Pointed]): Pointed[F] =
    new Pointed[F] {
      def point[A](a: A): F[A] = gen.from(gen.fr.point(a))
    }
}

trait Pointed0 {

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

trait Pointed1 {

}

// Pointed syntax
object pointedSyntax {
  implicit def pointedOps[A](a: A): PointedOps[A] = new PointedOps(a)

  class PointedOps[A](a: A) {
    def point[F[_]](implicit F: Pointed[F]): F[A] = F.point(a)
  }
}
