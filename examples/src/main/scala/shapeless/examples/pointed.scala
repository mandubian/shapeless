package shapeless.examples

import shapeless._
import ops.coproduct.IsCCons
import ops.hlist.IsHCons

import scala.language.existentials
import scala.language.experimental.macros

import scala.annotation.{ StaticAnnotation, tailrec }
import scala.reflect.api.Universe
import scala.reflect.macros.{ blackbox, whitebox }

import ops.{ hlist, coproduct }

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

  Pointed[Const[HNil]#λ]
  Pointed[Const[HNil.type]#λ]

  type L[A] = A :: HNil
  Pointed[L]

  type L2[A] = A :: A :: HNil
  Pointed[L2]

  type C[A] = A :+: CNil
  Pointed[C]

  type C2[A] = A :+: A :+: CNil
  Pointed[C2]

  type C3[A] = Id[A] :+: CNil
  Pointed[C3]

  type C4[A] = L[A] :+: CNil
  Pointed[C4]

  // OPTION
  Pointed[Const[None.type]#λ]
  Pointed[Some]
  Pointed[Option]
  // works
  type C5[A] = Const[None.type]#λ[A] :: HNil
  Pointed[C5]
  // doesnt work ???
  // Pointed[({ type λ[A] = Const[None.type]#λ[A] :: Const[HNil]#λ })#λ]


  // ILIST
  Pointed[Const[INil.type]#λ]
  Pointed[ICons]

  Pointed[IList]


  // LIST
  Pointed[Const[collection.immutable.Nil.type]#λ]
  Pointed[collection.immutable.::]
  Pointed[List]

  // Tree
  Pointed[Leaf]
  Pointed[Node]
  Pointed[Tree]

  // Foo
  Pointed[Foo]

  type C6[A] = Tree[A] :: List[A] :: Option[A] :: IList[A] :: Foo[A] :: HNil
  Pointed[C6]

  type C7[A] = Tree[A] :+: List[A] :+: Option[A] :+: IList[A] :+: Foo[A] :+: CNil
  Pointed[C7]


/** STILL BUGGY
  // assert("toto".point[Tree] == Leaf("toto"))
  // Pointed[Option]
  type C10[A] = Const[None.type]#λ[A] :: HNil
  implicitly[C10[Int] =:= ({ type λ[A] = Const[None.type]#λ[A] :: HNil })#λ[Int]] 

  type T[A] = Some[A] :+: CNil
  type T2[A] = Const[None.type]#λ[A] :+: Some[A] :+: CNil
  // OK
  val r: IsCCons1.Aux[T2, Pointed, Pointed, Const[None.type]#λ, T] = IsCCons1.mkIsCCons1[T2, Pointed, Pointed]
  // KO
  implicitly[IsCCons1.Aux[T2, Pointed, Pointed, Const[None.type]#λ, T]]

  // Pointed.cconsLeft[Option]

  // Pointed.cconsRight[T2, Const[None.type]#λ, T, None.type]
  // println("====>"+5.point[Option])
  // assert(5.point[Option] == Some(5))
  // assert(true.point[IList] == ICons(true, INil))
  // assert(1.234.point[List] == List(1.234))

  // assert("tata".point[Foo] == Foo("tata", Nil))
*/
}


object Pointed extends Pointed0 {
  def apply[F[_]](implicit f: Lazy[Pointed[F]]): Pointed[F] = f.value

  import scala.language.experimental.macros

  implicit val idPointed: Pointed[Id] =
    new Pointed[Id] {
      def point[A](a: A): Id[A] = a
    }


  // HACKING the fact that Pointed can't be built with all Const (just for singletons)
  implicit def constSingletonPointed[T](implicit w: Witness.Aux[T]): Pointed[Const[T]#λ] =
    new Pointed[Const[T]#λ] {
      def point[A](a: A): T = w.value
    }

  implicit def isCPointedSingleSingleton[C](
    implicit w: Witness.Aux[C], pf: Lazy[Pointed[Const[C]#λ]]
  ): Pointed[({type λ[A] = Const[C]#λ[A] :+: Const[CNil]#λ[A] })#λ] =
    new Pointed[({type λ[A] = Const[C]#λ[A] :+: Const[CNil]#λ[A] })#λ] {
      def point[A](a: A): Const[C]#λ[A] :+: Const[CNil]#λ[A] = Inl(pf.value.point(a))
    }

  implicit def isCPointedSingle[F[_]](
    implicit pf: Lazy[Pointed[F]]
  ): Pointed[({type λ[A] = F[A] :+: Const[CNil]#λ[A] })#λ] =
    new Pointed[({type λ[A] = F[A] :+: Const[CNil]#λ[A] })#λ] {
      def point[A](a: A): F[A] :+: Const[CNil]#λ[A] = Inl(pf.value.point(a))
    }

}

trait Pointed0 extends Pointed1 {

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

  implicit def generic[F[_]](implicit gen: Generic1[F, Pointed]): Pointed[F] =
    new Pointed[F] {
      def point[A](a: A): F[A] = gen.from(gen.fr.point(a))
    }

}

trait Pointed1 {

  // HACKING the fact that CNil can't be pointed
  implicit def isCPointedSimpleType: Pointed[({type λ[A] = A :+: Const[CNil]#λ[A] })#λ] =
    new Pointed[({type λ[A] = A :+: Const[CNil]#λ[A] })#λ] {
      def point[A](a: A): A :+: Const[CNil]#λ[A] = Inl(a)
    }
    

  implicit val constHNilPointed: Pointed[Const[HNil]#λ] =
    new Pointed[Const[HNil]#λ] {
      def point[A](a: A): HNil = HNil
    }

}

// Pointed syntax
object pointedSyntax {
  implicit def pointedOps[A](a: A): PointedOps[A] = new PointedOps(a)

  class PointedOps[A](a: A) {
    def point[F[_]](implicit F: Pointed[F]): F[A] = F.point(a)
  }
}




  // implicit def isHConsConstH[C](
  //   implicit w: Witness.Aux[C], pc: Lazy[Pointed[Const[C]#λ]], phnil: Lazy[Pointed[Const[HNil]#λ]]
  // ): IsHCons1[({type λ[A] = Const[C]#λ[A] :: HNil})#λ, Pointed, Pointed] = 
  //   new IsHCons1[({type λ[A] = Const[C]#λ[A] :: HNil})#λ, Pointed, Pointed] {
  //     type H[t] = Const[C]#λ[t]
  //     type T[t] = Const[HNil]#λ[t]

  //     def pack[A](u: (Const[C]#λ[A], Const[HNil]#λ[A])): ({type λ[A] = Const[C]#λ[A] :: HNil })#λ[A] = u._1 :: u._2
  //     def unpack[A](p: ({type λ[A] = Const[C]#λ[A] :: HNil })#λ[A]): (Const[C]#λ[A], Const[HNil]#λ[A]) = p.head -> p.tail

  //     def mkFhh: Pointed[Const[C]#λ] = lazily[]pc.value
  //     def mkFtt: Pointed[Const[HNil]#λ] = phnil.value
  //   }

  // implicit def isHConsConstH: IsHCons1S[({type λ[A] = Const[None.type]#λ[A] :: HNil})#λ, Pointed, Pointed] = 
  //   new IsHCons1S[({type λ[A] = Const[None.type]#λ[A] :: HNil})#λ, Pointed, Pointed] {
  //     type H[t] = Const[None.type]#λ[t]
  //     type T[t] = Const[HNil]#λ[t]

  //     def pack[A](u: (Const[None.type]#λ[A], Const[HNil]#λ[A])): ({type λ[A] = Const[None.type]#λ[A] :: HNil })#λ[A] = u._1 :: u._2
  //     def unpack[A](p: ({type λ[A] = Const[None.type]#λ[A] :: HNil })#λ[A]): (Const[None.type]#λ[A], Const[HNil]#λ[A]) = p.head -> p.tail

  //     def mkFhh: Pointed[Const[None.type]#λ] = lazily[Pointed[Const[None.type]#λ]]
  //     def mkFtt: Pointed[Const[HNil]#λ] = lazily[Pointed[Const[HNil]#λ]]
  //   }

  // HACKING the fact that CNil can't be pointed
  /*implicit def isHPointedSingle[C](
    implicit w: Witness.Aux[C], pc: Lazy[Pointed[Const[C]#λ]]
  ): Pointed[({type λ[A] = Const[C]#λ[A] :: HNil })#λ] =
    new Pointed[({type λ[A] = Const[C]#λ[A] :: HNil })#λ] {
      def point[A](a: A): Const[C]#λ[A] :: HNil = pc.value.point(a) :: HNil
    }*/

  // HACKING the fact that CNil can't be pointed
  /*implicit def isCPointedSingle[C](
    implicit w: Witness.Aux[C], pc: Lazy[Pointed[Const[C]#λ]]
  ): Pointed[({type λ[A] = Const[C]#λ[A] :+: CNil })#λ] =
    new Pointed[({type λ[A] = Const[C]#λ[A] :+: CNil })#λ] {
      def point[A](a: A): Const[C]#λ[A] :+: CNil = Inl(pc.value.point(a))
    }*/

  // HACKING the fact that CNil can't be pointed
  // implicit def isCPointedSingleF[F[_]](
  //   implicit pf: Lazy[Pointed[F]]
  // ): Pointed[({type λ[A] = F[A] :+: Const[CNil]#λ[A] })#λ] =
  //   new Pointed[({type λ[A] = F[A] :+: Const[CNil]#λ[A] })#λ] {
  //     def point[A](a: A): F[A] :+: Const[CNil]#λ[A] = Inl(pf.value.point(a))
  //   }

  // implicit def isHConsConst[C](
  //   implicit w: Witness.Aux[C], pc: Lazy[Pointed[Const[C]#λ]], phnil: Lazy[Pointed[Const[HNil]#λ]]
  // ): IsHCons1[({type λ[A] = Const[C]#λ[A] :: HNil})#λ, Pointed, Pointed] = 
  //   new IsHCons1[({type λ[A] = Const[C]#λ[A] :: HNil})#λ, Pointed, Pointed] {
  //     type H[t] = Const[C]#λ[t]
  //     type T[t] = Const[HNil]#λ[t]

  //     def pack[A](u: (Const[C]#λ[A], Const[HNil]#λ[A])): ({type λ[A] = Const[C]#λ[A] :: HNil })#λ[A] = u._1 :: u._2
  //     def unpack[A](p: ({type λ[A] = Const[C]#λ[A] :: HNil })#λ[A]): (Const[C]#λ[A], Const[HNil]#λ[A]) = p.head -> p.tail

  //     def mkFhh: Pointed[Const[C]#λ] = pc.value
  //     def mkFtt: Pointed[Const[HNil]#λ] = phnil.value
  //   }

  // implicit def isCConsConst[C](
  //   implicit w: Witness.Aux[C], pc: Lazy[Pointed[Const[C]#λ]]
  // ): IsCCons1[({type λ[A] = Const[C]#λ[A] :+: CNil })#λ, Pointed, Pointed] = 
  //   new IsCCons1[({type λ[A] = Const[C]#λ[A] :+: CNil })#λ, Pointed, Pointed] {
  //     type H[t] = Const[C]#λ[t]
  //     type T[t] = Const[CNil]#λ[t]

  //     def pack[A](u: Either[Const[C]#λ[A], Const[CNil]#λ[A]]): ({type λ[A] = Const[C]#λ[A] :+: CNil })#λ[A] = u match {
  //       case Left(a) => Coproduct[Const[C]#λ[A] :+: CNil](a)
  //       case Right(b) => throw new RuntimeException("can't happen")
  //     }
  //     def unpack[A](p: ({type λ[A] = Const[C]#λ[A] :+: CNil })#λ[A]): Either[Const[C]#λ[A], CNil] = p match {
  //       case Inl(a) => Left(a)
  //       case Inr(c) => throw new RuntimeException("can't happen")
  //     }

  //     def mkFhh: Pointed[Const[C]#λ] = pc.value
  //     def mkFtt: Pointed[Const[CNil]#λ] = null
  //   }

  // implicit def isCConsConst2[F[_], C](
  //   implicit pf: Lazy[Pointed[F]], w: Witness.Aux[C], pc: Lazy[Pointed[({type λ[A] = Const[C]#λ[A] :+: CNil })#λ]]
  // ): IsCCons1[({type λ[A] = F[A] :+: Const[C]#λ[A] :+: CNil })#λ, Pointed, Pointed] = 
  //   new IsCCons1[({type λ[A] = F[A] :+: Const[C]#λ[A] :+: CNil })#λ, Pointed, Pointed] {
  //     type H[t] = F[t]
  //     type T[t] = ({type λ[A] = Const[C]#λ[A] :+: CNil })#λ[t]

  //     def pack[A](u: Either[F[A], ({type λ[A] = Const[C]#λ[A] :+: CNil })#λ[A]]): ({type λ[A] = F[A] :+: Const[C]#λ[A] :+: CNil })#λ[A] = u match {
  //       case Left(a) => Coproduct[F[A] :+: Const[C]#λ[A] :+: CNil](a)
  //       case Right(b) => b.extendLeft[F[A]]
  //     }
  //     def unpack[A](p: ({type λ[A] = F[A] :+: Const[C]#λ[A] :+: CNil })#λ[A]): Either[F[A], ({type λ[A] = Const[C]#λ[A] :+: CNil })#λ[A]] = p match {
  //       case Inl(a) => Left(a)
  //       case Inr(c) => Right(c)
  //     }

  //     def mkFhh: Pointed[F] = pf.value
  //     def mkFtt: Pointed[({type λ[A] = Const[C]#λ[A] :+: CNil })#λ] = pc.value
  //   }
