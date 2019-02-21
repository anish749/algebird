package com.twitter.algebird.mutable

import java.io.{ByteArrayOutputStream, ObjectOutputStream}

import com.twitter.algebird.{
  BloomFilter => _,
  BloomFilterAggregator => _,
  BloomFilterMonoid => _,
  BFHash => _,
  BF => _,
  _
}
import org.scalacheck.{Arbitrary, Gen}
import org.scalatest.{Matchers, WordSpec}
import org.scalacheck.Prop._

class BloomFilterLaws extends CheckProperties {

  import com.twitter.algebird.BaseProperties._

  val NUM_HASHES = 6
  val WIDTH = 32

  implicit val bfMonoid = new BloomFilterMonoid[String](NUM_HASHES, WIDTH)

  implicit val bfGen: Arbitrary[MutableBF[String]] =
    Arbitrary {
      val item = Gen.choose(0, 10000).map { v =>
        bfMonoid.create(v.toString)
      }
      val zero = Gen.const(bfMonoid.zero)
      Gen.frequency((1, zero), (10, item))
    }

  property("BloomFilter is a Monoid") {
    commutativeMonoidLaws[MutableBF[String]]
  }

  property("++= is the same as plus") {
    forAll { (a: MutableBF[String], b: MutableBF[String]) =>
      Equiv[MutableBF[String]].equiv(a ++= b, bfMonoid.plus(a, b))
    }
  }

  property("the distance between a filter and itself should be 0") {
    forAll { (a: MutableBF[String]) =>
      a.hammingDistance(a) == 0
    }
  }

  property(
    "the distance between a filter and an empty filter should be the number of bits" +
      "set in the existing filter") {
    forAll { (a: MutableBF[String]) =>
      a.hammingDistance(bfMonoid.zero) == a.numBits
    }
  }

  property("all equivalent filters should have 0 Hamming distance") {
    forAll { (a: MutableBF[String], b: MutableBF[String]) =>
      if (Equiv[MutableBF[String]].equiv(a, b))
        a.hammingDistance(b) == 0
      else {
        val dist = a.hammingDistance(b)
        (dist > 0) && (dist <= a.width)
      }
    }
  }

  property("distance between filters should be symmetrical") {
    forAll { (a: MutableBF[String], b: MutableBF[String]) =>
      a.hammingDistance(b) == b.hammingDistance(a)
    }
  }

  property("calculating hamming distance should not modify the Bloom Filter") {
    forAll { (a: MutableBF[String], b: MutableBF[String]) =>
      val acopy = a.copy
      a.hammingDistance(b)
      Equiv[MutableBF[String]].equiv(a, acopy)
    }
  }

  property("+ is the same as adding with create") {
    forAll { (a: MutableBF[String], b: String) =>
      Equiv[MutableBF[String]].equiv(a += b, bfMonoid.plus(a, bfMonoid.create(b)))
    }
  }

  property("maybeContains is consistent with contains") {
    forAll { (a: MutableBF[String], b: String) =>
      a.maybeContains(b) == a.contains(b).isTrue
    }
  }

  property("after + maybeContains is true") {
    forAll { (a: MutableBF[String], b: String) =>
      (a += b).maybeContains(b)
    }
  }

  property("checkAndAdd works like check the add") {
    forAll { (a: MutableBF[String], b: String) =>
      val (next, check) = a.copy.checkAndAdd(b) // Treat as immutable BF by creating copies
      val next1 = a.copy += b

      Equiv[MutableBF[String]].equiv(next, next1) &&
      (check == a.contains(b))
    }
  }

  property("a ++ a = a for BF") {
    forAll { (a: MutableBF[String]) =>
      Equiv[MutableBF[String]].equiv(a ++= a, a)
    }
  }
}

class BFHashIndices extends CheckProperties {

  val NUM_HASHES = 10
  val WIDTH = 4752800

  implicit val bfHash: Arbitrary[MutableBFHash[String]] =
    Arbitrary {
      for {
        hashes <- Gen.choose(1, 10)
        width <- Gen.choose(100, 5000000)
      } yield MutableBFHash[String](hashes, width)
    }

  property("Indices are non negative") {
    forAll { (hash: MutableBFHash[String], v: Long) =>
      hash.apply(v.toString).forall { e =>
        e >= 0
      }
    }
  }

}

class BloomFilterFalsePositives[T: Gen: Hash128](falsePositiveRate: Double) extends ApproximateProperty {

  type Exact = Set[T]
  type Approx = MutableBF[T]

  type Input = T
  type Result = Boolean

  val maxNumEntries = 1000

  def exactGenerator =
    for {
      numEntries <- Gen.choose(1, maxNumEntries)
      set <- Gen.containerOfN[Set, T](numEntries, implicitly[Gen[T]])
    } yield set

  def makeApproximate(set: Set[T]) = {
    val bfMonoid = BloomFilter[T](set.size, falsePositiveRate)

    val values = set.toSeq
    bfMonoid.create(values: _*)
  }

  def inputGenerator(set: Set[T]) =
    for {
      randomValues <- Gen.listOfN[T](set.size, implicitly[Gen[T]])
      x <- Gen.oneOf((set ++ randomValues).toSeq)
    } yield x

  def exactResult(s: Set[T], t: T) = s.contains(t)

  def approximateResult(bf: MutableBF[T], t: T) = bf.contains(t)
}

class BloomFilterCardinality[T: Gen: Hash128] extends ApproximateProperty {

  type Exact = Set[T]
  type Approx = MutableBF[T]

  type Input = Unit
  type Result = Long

  val maxNumEntries = 10000
  val falsePositiveRate = 0.01

  def exactGenerator =
    for {
      numEntries <- Gen.choose(1, maxNumEntries)
      set <- Gen.containerOfN[Set, T](numEntries, implicitly[Gen[T]])
    } yield set

  def makeApproximate(set: Set[T]) = {
    val bfMonoid = BloomFilter[T](set.size, falsePositiveRate)

    val values = set.toSeq
    bfMonoid.create(values: _*)
  }

  def inputGenerator(set: Set[T]) = Gen.const(())

  def exactResult(s: Set[T], u: Unit) = s.size
  def approximateResult(bf: MutableBF[T], u: Unit) = bf.size
}

class BloomFilterProperties extends ApproximateProperties("BloomFilter") {
  import ApproximateProperty.toProp

  for (falsePositiveRate <- List(0.1, 0.01, 0.001)) {
    property(s"has small false positive rate with false positive rate = $falsePositiveRate") = {
      implicit val intGen = Gen.choose(1, 1000)
      toProp(new BloomFilterFalsePositives[Int](falsePositiveRate), 50, 50, 0.01)
    }
  }

  property("approximate cardinality") = {
    implicit val intGen = Gen.choose(1, 1000)
    toProp(new BloomFilterCardinality[Int], 50, 1, 0.01)
  }
}

class BloomFilterTest extends WordSpec with Matchers {

  val RAND = new scala.util.Random

  "MutableBloomFilter" should {

    "be possible to create from an iterator" in {
      val bfMonoid = new BloomFilterMonoid[String](RAND.nextInt(5) + 1, RAND.nextInt(64) + 32)
      val entries = (0 until 100).map(_ => RAND.nextInt.toString)
      val bf = bfMonoid.create(entries.iterator)
      assert(bf.isInstanceOf[MutableBF[String]])
    }

    "be possible to create from a sequence" in {
      val bfMonoid = new BloomFilterMonoid[String](RAND.nextInt(5) + 1, RAND.nextInt(64) + 32)
      val entries = (0 until 100).map(_ => RAND.nextInt.toString)
      val bf = bfMonoid.create(entries: _*)
      assert(bf.isInstanceOf[MutableBF[String]])
    }

    "identify all true positives" in {
      (0 to 100).foreach { _ =>
        {
          val bfMonoid = new BloomFilterMonoid[String](RAND.nextInt(5) + 1, RAND.nextInt(64) + 32)
          val numEntries = 5
          val entries = (0 until numEntries).map(_ => RAND.nextInt.toString)
          val bf = bfMonoid.create(entries: _*)

          entries.foreach { i =>
            assert(bf.contains(i.toString).isTrue)
          }
        }
      }
    }

    "have small false positive rate" in {
      val iter = 10000

      Seq(0.1, 0.01, 0.005).foreach { fpProb =>
        {
          val fps = (0 until iter).par.map { _ =>
            {
              val numEntries = RAND.nextInt(10) + 1

              val bfMonoid = BloomFilter[String](numEntries, fpProb)

              val entries = RAND
                .shuffle((0 until 1000).toList)
                .take(numEntries + 1)
                .map(_.toString)
              val bf = bfMonoid.create(entries.drop(1): _*)

              if (bf.contains(entries(0)).isTrue) 1.0 else 0.0
            }
          }

          val observedFpProb = fps.sum / fps.size

          // the 5 is a fudge factor to make the probability of it relatively low
          // in tests - This is different from the immutable implementation
          // as the underlying hash functions are different.
          assert(observedFpProb <= 5 * fpProb)
        }
      }
    }

    "approximate cardinality" in {
      val bfMonoid = BloomFilterMonoid[String](10, 100000)
      Seq(10, 100, 1000, 10000).foreach { exactCardinality =>
        val items = (1 until exactCardinality).map { _.toString }
        val bf = bfMonoid.create(items: _*)
        val size = bf.size

        assert(size ~ exactCardinality)
        assert(size.min <= size.estimate)
        assert(size.max >= size.estimate)
      }
    }

    "work as an Aggregator" in {
      (0 to 10).foreach { _ =>
        {
          val aggregator = BloomFilterAggregator[String](RAND.nextInt(5) + 1, RAND.nextInt(64) + 32)
          val numEntries = 5
          val entries = (0 until numEntries).map(_ => RAND.nextInt.toString)
          val bf = aggregator(entries)

          entries.foreach { i =>
            assert(bf.contains(i.toString).isTrue)
          }
        }
      }
    }

    "not serialize @transient BFInstance" in {
      def serialize(bf: MutableBF[String]): Array[Byte] = {
        val stream = new ByteArrayOutputStream()
        val out = new ObjectOutputStream(stream)
        out.writeObject(bf)
        out.close()
        stream.close()
        stream.toByteArray
      }

      val items = (1 until 10).map(_.toString)
      val bf = BloomFilter[String](10, 0.1).create(items: _*)
      val bytesBeforeSizeCalled = Bytes(serialize(bf))
      val beforeSize = bf.size
      assert(bf.contains("1").isTrue)
      val bytesAfterSizeCalled = Bytes(serialize(bf))
      assert(bytesBeforeSizeCalled.size == bytesAfterSizeCalled.size)
      assert(beforeSize == bf.size)
    }

    "not have negative hash values" in {
      val NUM_HASHES = 2
      val WIDTH = 4752800
      val bfHash = MutableBFHash[String](NUM_HASHES, WIDTH)
      val s = "7024497610539761509"
      val index = bfHash.apply(s).head

      assert(index >= 0)
    }
  }

  "BloomFilter method `checkAndAdd`" should {

    "be identical to method `+`" in {
      (0 to 100).foreach { _ =>
        val bfMonoid = new BloomFilterMonoid[String](RAND.nextInt(5) + 1, RAND.nextInt(64) + 32)
        val numEntries = 5
        val entries = (0 until numEntries).map(_ => RAND.nextInt.toString)
        val bf = bfMonoid.create(entries: _*)
        val bfWithCheckAndAdd = entries
          .map { entry =>
            (entry, bfMonoid.create(entry))
          }
          .foldLeft((bfMonoid.zero, bfMonoid.zero)) {
            case ((left, leftAlt), (entry, right)) =>
              val (newLeftAlt, contained) = leftAlt.checkAndAdd(entry)
              left.contains(entry) shouldBe contained
              (left += entry, newLeftAlt)
          }

        entries.foreach { i =>
          assert(bf.contains(i.toString).isTrue)
        }
      }
    }
  }

  "BloomFilters" should {

    /**
     *  The distances are different from the immutable bloom filter implementation
     *  as they use a different method to find the hashes.
     */
    "be able to compute Hamming distance to each other" in {

      def createBFWithItems(entries: Seq[String]): MutableBF[String] = {
        val numOfHashes = 3
        val width = 64
        val bfMonoid = new BloomFilterMonoid[String](numOfHashes, width)
        bfMonoid.create(entries: _*)
      }

      val firstBloomFilter = createBFWithItems(Seq("A"))
      val secondBloomFilter = createBFWithItems(Seq("C"))

      val distance1 = firstBloomFilter.hammingDistance(secondBloomFilter)
      assert(distance1 === 6)

      val thirdBloomFilter = createBFWithItems(Seq("A", "B", "C"))
      val forthBloomFilter = createBFWithItems(Seq("C", "D", "E"))

      val distance2 = thirdBloomFilter.hammingDistance(forthBloomFilter)
      assert(distance2 === 6)

      val emptyBloomFilter = createBFWithItems(List())
      val distanceToEmpty = thirdBloomFilter.hammingDistance(emptyBloomFilter)
      assert(distanceToEmpty === thirdBloomFilter.numBits)

    }
  }

}
