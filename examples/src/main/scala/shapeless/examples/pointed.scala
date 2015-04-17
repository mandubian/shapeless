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

  // type L[A] = A :: HNil
  // Pointed[L]

  // type C[A] = A :+: CNil
  // Pointed[C]

  // type C2[A] = Id[A] :+: CNil
  // Pointed[C2]

  // type C3[A] = L[A] :+: CNil
  // Pointed[C3]

  // Pointed[Option]

  // Pointed[Tree]

  // type C4[A] = Const[INil.type]#λ[A] :: HNil
  // IsHCons1[C4, Pointed, Pointed]

  // // FAILS FOR UNKNOWN REASON YET
  // type C5[A] = A :: Const[INil.type]#λ[A] :: HNil
  // IsHCons1[C5, Pointed, Pointed]

  // type C6[A] = A :: IList[A] :: HNil
  // IsHCons1[C6, Pointed, Pointed]

  // Pointed[Option]

  // Pointed[List]

  // Pointed[Foo]

  // assert(5.point[Option] == Some(5))
  // assert("toto".point[Tree] == Leaf("toto"))
  // assert(true.point[IList] == ICons(true, INil))
  // assert(1.234.point[List] == List(1.234))

  // assert("tata".point[Foo] == Foo("tata", Nil))

  Witness[None.type]
  Pointed[Const[None.type]#λ]
  Pointed[Some]
  type C8[A] = Some[A] :: Const[None.type]#λ[A] :: HNil
  IsHCons1.mkIsHCons1[C8, Pointed, Pointed]
  Pointed.isHConsConstT[Some, ({type λ[A] = Const[None.type]#λ[A] :: HNil })#λ]
  // Pointed.hcons[C8]
  // Pointed[Some]
  // Pointed[Option]

  // type C7[A] = Id[A] :+: Some[A] :+: Const[None.type]#λ[A] :+: CNil
  // Pointed.hcons[C7]
  // Pointed.ccons[C7]

  // type C8[A] = Some[A] :: Const[None.type]#λ[A] :: HNil
  // Pointed.hcons[C8]

  // IsCCons1.mkIsCCons1[C7, Pointed, Pointed]

  // type H[T] = None.type
  // lazily[Pointed[H]]
  // lazily[Pointed[Const[None.type]#λ]]
  // IsHCons1.mkIsHCons1[C7, Pointed, Pointed]
  // Pointed.hcons[C7]
  // IsHCons1.mkIsHCons1[C7, Pointed, Pointed]
  // Pointed.isHConsConst[None.type]
  // Pointed.isCConsConst[Some, None.type]
  // Pointed[Option]
}


object Pointed extends Pointed0 {
  def apply[F[_]](implicit f: Lazy[Pointed[F]]): Pointed[F] = f.value

  implicit val idPointed: Pointed[Id] =
    new Pointed[Id] {
      def point[A](a: A): Id[A] = a
    }

  // HACKING the fact that CNil can't be pointed
  implicit def isHPointedSingle[C](
    implicit w: Witness.Aux[C], pc: Lazy[Pointed[Const[C]#λ]]
  ): Pointed[({type λ[A] = Const[C]#λ[A] :: HNil })#λ] =
    new Pointed[({type λ[A] = Const[C]#λ[A] :: HNil })#λ] {
      def point[A](a: A): Const[C]#λ[A] :: HNil = pc.value.point(a) :: HNil
    }

  // HACKING the fact that CNil can't be pointed
  implicit def isCPointedSingle[C](
    implicit w: Witness.Aux[C], pc: Lazy[Pointed[Const[C]#λ]]
  ): Pointed[({type λ[A] = Const[C]#λ[A] :+: CNil })#λ] =
    new Pointed[({type λ[A] = Const[C]#λ[A] :+: CNil })#λ] {
      def point[A](a: A): Const[C]#λ[A] :+: CNil = Inl(pc.value.point(a))
    }

  // implicit def isHConsConstH[C](
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

  // implicit def isHConsConstT[F[_], G[_] <: HList](
  //   implicit pf: Lazy[Pointed[F]], pg: Lazy[Pointed[G]]
  // ): IsHCons1[({type λ[A] = F[A] :: G[A]})#λ, Pointed, Pointed] = 
  //   new IsHCons1[({type λ[A] = F[A] :: G[A]})#λ, Pointed, Pointed] {
  //     type H[t] = F[t]
  //     type T[t] = ({type λ[A] = G[A]})#λ[t]

  //     def pack[A](u: (F[A], G[A])): ({type λ[A] = F[A] :: G[A]})#λ[A] = u._1 :: u._2
  //     def unpack[A](p: ({type λ[A] = F[A] :: G[A]})#λ[A]): (F[A], G[A]) = p.head -> p.tail

  //     def mkFhh: Pointed[F] = pf.value
  //     def mkFtt: Pointed[G] = pg.value
  //   }

  implicit def generic[F[_]](implicit gen: Generic1[F, Pointed]): Pointed[F] =
    new Pointed[F] {
      def point[A](a: A): F[A] = gen.from(gen.fr.point(a))
    }
}

trait Pointed0 extends Pointed1 {
  // HACKING the fact that CNil can't be pointed
  // implicit def isCPointedSingleF[F[_]](
  //   implicit pf: Lazy[Pointed[F]]
  // ): Pointed[({type λ[A] = F[A] :+: Const[CNil]#λ[A] })#λ] =
  //   new Pointed[({type λ[A] = F[A] :+: Const[CNil]#λ[A] })#λ] {
  //       def point[A](a: A): F[A] :+: Const[CNil]#λ[A] = Inl(pf.value.point(a))
  //   }

  // implicit def isHPointedSingleF[F[_]](
  //   implicit pf: Lazy[Pointed[F]]
  // ): Pointed[({type λ[A] = F[A] :: Const[HNil]#λ[A] })#λ] =
  //   new Pointed[({type λ[A] = F[A] :: Const[HNil]#λ[A] })#λ] {
  //       def point[A](a: A): F[A] :: Const[HNil]#λ[A] = pf.value.point(a) :: HNil
  //   }


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
  // implicit def isCPointedSimpleType: Pointed[({type λ[A] = A :+: Const[CNil]#λ[A] })#λ] =
  //   new Pointed[({type λ[A] = A :+: Const[CNil]#λ[A] })#λ] {
  //       def point[A](a: A): A :+: Const[CNil]#λ[A] = Inl(a)
  //   }

  implicit def isHPointedSimpleType[T](implicit w: Witness.Aux[T]): Pointed[({type λ[A] = Const[T]#λ[A] :: HNil })#λ] =
    new Pointed[({type λ[A] = Const[T]#λ[A] :: HNil })#λ] {
        def point[A](a: A): Const[T]#λ[A] :: HNil = w.value :: HNil
    }

  implicit def constHNilPointed: Pointed[Const[HNil]#λ] =
    new Pointed[Const[HNil]#λ] {
      def point[A](a: A): HNil = HNil
    }

  // HACKING the fact that Pointed can't be built with all Const (just for singletons)
  implicit def constSingletonPointed[T](implicit w: Witness.Aux[T]): Pointed[Const[T]#λ] =
    new Pointed[Const[T]#λ] {
      def point[A](a: A): T = w.value
    }

  // implicit def constNilPointed: Pointed[Const[Nil.type]#λ] =
  //   new Pointed[Const[Nil.type]#λ] {
  //     def point[A](a: A): Nil.type = Nil
  //   }

  // implicit def constINilPointed: Pointed[Const[INil.type]#λ] =
  //   new Pointed[Const[INil.type]#λ] {
  //     def point[A](a: A): INil.type = INil
  //   }

  // implicit def constNonePointed: Pointed[Const[None.type]#λ] =
  //   new Pointed[Const[None.type]#λ] {
  //     def point[A](a: A): None.type = None
  //   }
}

// Pointed syntax
object pointedSyntax {
  implicit def pointedOps[A](a: A): PointedOps[A] = new PointedOps(a)

  class PointedOps[A](a: A) {
    def point[F[_]](implicit F: Pointed[F]): F[A] = F.point(a)
  }
}





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
