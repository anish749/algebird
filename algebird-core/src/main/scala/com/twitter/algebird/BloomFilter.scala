/*
Copyright 2012 Twitter, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
 */

package com.twitter.algebird

import java.util.{BitSet => jBitSet}

import algebra.BoundedSemilattice
import com.googlecode.javaewah.{EWAHCompressedBitmap => CBitSet}

object RichCBitSet {
  def apply(xs: Int*): CBitSet = fromArray(xs.toArray)

  // this sorts the array in-place
  def fromArray(x: Array[Int]): CBitSet = {
    val bs = new CBitSet
    bs += x
  }

  def fromJBitSet(bs: jBitSet): CBitSet = {
    val nbs = new CBitSet
    var i = bs.nextSetBit(0)
    while (i >= 0 && i != Int.MaxValue) {
      nbs.set(i)
      i = bs.nextSetBit(i + 1)
    }
    nbs
  }

  implicit def cb2rcb(cb: CBitSet): RichCBitSet = new RichCBitSet(cb)
}

// An enrichment to give some scala-like operators to the compressed
// bit set.
class RichCBitSet(val cb: CBitSet) extends AnyVal {
  def ++(b: CBitSet): CBitSet = cb.or(b)

  def ==(b: CBitSet): Boolean = cb.equals(b)

  def +=(xs: Array[Int]): cb.type = {
    var idx = 0
    java.util.Arrays.sort(xs)
    while (idx < xs.length) {
      cb.set(xs(idx))
      idx += 1
    }
    cb
  }

  /**
   * Assumption Width is more than number of set bits in CBitSet.
   */
  def toJBitSet(width: Int): jBitSet = {
    val a = new jBitSet(width)
    val iter = cb.intIterator
    while (iter.hasNext) {
      val i = iter.next
      a.set(i)
    }
    a
  }
}

object RichJavaBitSet {
  def apply(setBits: Array[Int], width: Int): jBitSet = {
    val bs = new jBitSet(width)
    bs += setBits
  }

  implicit def jb2rjb(jb: jBitSet): RichJavaBitSet = new RichJavaBitSet(jb)
}

class RichJavaBitSet(val jb: jBitSet) extends AnyVal {
  import RichJavaBitSet._

  private def doCopy: jBitSet =
    jBitSet.valueOf(jb.toLongArray) // toLongArray and valueOf both return a new copy

  def ++(b: jBitSet): jBitSet = {
    val copy = doCopy
    copy.or(b)
    copy
  }

  def |(b: jBitSet): jBitSet = jb ++ b

  def ^(b: jBitSet): jBitSet = {
    val copy = doCopy
    copy.xor(b)
    copy
  }

  def +=(xs: Array[Int]): jBitSet = {
    var idx = 0
    java.util.Arrays.sort(xs)
    while (idx < xs.length) {
      jb.set(xs(idx))
      idx += 1
    }
    jb
  }
}

///**
// * A mutable BitSet which uses Array[Long] as BitMask.
// * Provides all operations necessary for BloonFilter operations.
// * @param bitMask
// */
//private[algebird] case class LongaasasBitSet(bitMask: Array[Long]) extends AnyVal {
//  def toBitSetNoCopy: BitSet =
//    BitSet.fromBitMaskNoCopy(bitMask)
//
//  def set(i: Int): Unit =
//    bitMask(i / 64) |= 1L << (i % 64)
//
//  def +=(xs: Array[Int]): Unit = {
//    var idx = 0
//    while (idx < xs.length) {
//      set(xs(idx))
//      idx += 1
//    }
//  }
//
//  def +=(xs: Array[Long]): Unit = {
//    var idx = 0
//    while (idx < xs.length) {
//      set(xs(idx))
//      idx += 1
//    }
//  }
//
//  def +=(it: IntIterator): Unit =
//    while (it.hasNext) { set(it.next) }
//
//  /**
//   * A boolean OR operation of the two LongBitSets.
//   */
//  def |(other: LongBitSet): LongBitSet = {
//    require(bitMask.length == other.bitMask.length, "Width of two filters should be same")
//    val bm = new Array[Long](bitMask.length)
//    val lbs = LongBitSet(Array.copy(bitMask, 0, bm, 0, bitMask.length))
//    lbs += other.bitMask
//    lbs
//  }
//
//
//}
//
//private[algebird] object LongBitSet {
//  def empty(size: Int): LongBitSet =
//    LongBitSet(new Array[Long]((size + 63) / 64))
//
//  def fromCBitSet(cb: CBitSet, width: Int): LongBitSet = {
//    val lbs = empty(width)
//    lbs += cb.intIterator
//    lbs
//  }
//}

object BloomFilter {

  def apply[A](numEntries: Int, fpProb: Double)(implicit hash: Hash128[A]): BloomFilterMonoid[A] =
    BloomFilter.optimalWidth(numEntries, fpProb) match {
      case None =>
        throw new java.lang.IllegalArgumentException(
          s"BloomFilter cannot guarantee the specified false positive probability for the number of entries! (numEntries: $numEntries, fpProb: $fpProb)")
      case Some(width) =>
        val numHashes = BloomFilter.optimalNumHashes(numEntries, width)
        BloomFilterMonoid[A](numHashes, width)(hash)
    }

  // Compute optimal number of hashes: k = m/n ln(2)
  def optimalNumHashes(numEntries: Int, width: Int): Int =
    math.ceil(width / numEntries * math.log(2)).toInt

  // Compute optimal width: m = - n ln(p) / (ln(2))^2
  // return None if we can't meet this false positive probability
  def optimalWidth(numEntries: Int, fpProb: Double): Option[Int] = {
    val widthEstimate = math
      .ceil(-1 * numEntries * math.log(fpProb) / math.log(2) / math.log(2))
      .toInt

    if (widthEstimate == Int.MaxValue) None
    else Some(widthEstimate)
  }

  /**
   * Cardinality estimates are taken from Theorem 1 on page 15 of
   * "Cardinality estimation and dynamic length adaptation for Bloom filters"
   * by Papapetrou, Siberski, and Nejdl:
   * http://www.softnet.tuc.gr/~papapetrou/publications/Bloomfilters-DAPD.pdf
   *
   * Roughly, by using bounds on the expected number of true bits after n elements
   * have been inserted into the Bloom filter, we can go from the actual number of
   * true bits (which is known) to an estimate of the cardinality.
   *
   * approximationWidth defines an interval around the maximum-likelihood cardinality
   * estimate. Namely, the approximation returned is of the form
   * (min, estimate, max) =
   *   ((1 - approxWidth) * estimate, estimate, (1 + approxWidth) * estimate)
   */
  def sizeEstimate(numBits: Int,
                   numHashes: Int,
                   width: Int,
                   approximationWidth: Double = 0.05): Approximate[Long] = {
    assert(0 <= approximationWidth && approximationWidth < 1, "approximationWidth must lie in [0, 1)")

    /**
     * s(n) is the expected number of bits that have been set to true after
     * n elements have been inserted into the Bloom filter.
     * This is \hat{S}(n) in the cardinality estimation paper used above.
     */
    def s(n: Int): Double =
      width * (1 - scala.math.pow(1 - 1.0 / width, numHashes * n))

    /**
     * sInverse(t) is the maximum likelihood value for the number of elements
     * that have been inserted into the Bloom filter when it has t bits set to true.
     * This is \hat{S}^{-1}(t) in the cardinality estimation paper used above.
     **/
    def sInverse(t: Int): Double =
      scala.math.log1p(-t.toDouble / width) / (numHashes * scala.math.log1p(-1.0 / width))

    // Variable names correspond to those used in the paper.
    val t = numBits
    val n = sInverse(t).round.toInt
    // Take the min and max because the probability formula assumes
    // nl <= sInverse(t - 1) and sInverse(t + 1) <= nr
    val nl =
      scala.math.min(sInverse(t - 1).floor, (1 - approximationWidth) * n).toInt
    val nr =
      scala.math.max(sInverse(t + 1).ceil, (1 + approximationWidth) * n).toInt
    val prob =
      1 -
        scala.math.exp(t - 1 - s(nl)) *
          scala.math.pow(s(nl) / (t - 1), t - 1) -
        scala.math.exp(-scala.math.pow(t + 1 - s(nr), 2) / (2 * s(nr)))

    Approximate[Long](nl, n, nr, scala.math.max(0, prob))
  }
}

/**
 * Bloom Filter - a probabilistic data structure to test presence of an element.
 *
 * Operations
 * 1) insert: hash the value k times, updating the bitfield at the index equal to each hashed value
 * 2) query: hash the value k times.  If there are k collisions, then return true; otherwise false.
 *
 * http://en.wikipedia.org/wiki/Bloom_filter
 *
 */
case class BloomFilterMonoid[A](numHashes: Int, width: Int)(implicit hash: Hash128[A])
    extends Monoid[BF[A]]
    with BoundedSemilattice[BF[A]] {
  import RichCBitSet._
  import RichJavaBitSet._

  val hashes: BFHash[A] = BFHash[A](numHashes, width)(hash)

  val zero: BF[A] = BFZero[A](hashes, width)

  /**
   * Assume the bloom filters are compatible (same width and same hashing functions).  This
   * is the union of the 2 bloom filters.
   */
  def plus(left: BF[A], right: BF[A]): BF[A] = left ++ right

//  /**
//   * Assume that all the bloom filters have same width and hashing functions.
//   */
//  override def sumOption(as: TraversableOnce[BF[A]]): Option[BF[A]] =
//    as.toList match {
//      case Nil                               => None
//      case BFZero(_, _) :: Nil               => Some(zero) // One BF and that is zero
//      case (bf @ BFInstance(_, _, _)) :: Nil => Some(bf)
//      case (bf @ BFSparse(_, _, _)) :: Nil   => Some(bf)
//      case BFZero(_, _) :: tail              => sumOption(tail)
//      case nonZeroBF :: tail =>
//        var bits = nonZeroBF match {
//          case BFItem(item, _, _)       => new jBitSet(hashes(item): _*)
//          case BFInstance(_, bitset, _) => bitset
//          case BFSparse(_, cbitset, wid) =>
//            LongBitSet
//              .fromCBitSet(cbitset, wid) // This also does a copy
//              .toBitSetNoCopy
//        }
//
//        tail.foreach {
//          case BFZero(_, _) => ()
//          case BFItem(item, _, _) =>
//            bits = bits | BitSet(hashes(item): _*)
//          case BFSparse(_, cbitset, _) =>
//            bits = bits | BitSet(cbitset.toArray: _*)
//          case BFInstance(_, bitset, _) =>
//            bits = bits | bitset
//        }
//
//        val sumedBF: BFInstance[A] = BFInstance(hashes, bits, width)
//        // Convert to Sparse if the density if low
//        if (sumedBF.density < 0.1) {
//          Some(sumedBF.toSparse)
//        } else {
//          Some(sumedBF)
//        }
//    }

  /**
   * Assume that all the bloom filters have same width and hashing functions.
   */
  override def sumOption(as: TraversableOnce[BF[A]]): Option[BF[A]] =
    as.toList match {
      case Nil                               => None
      case BFZero(_, _) :: Nil               => Some(zero) // One BF and that is zero
      case (bf @ BFInstance(_, _, _)) :: Nil => Some(bf)
      case (bf @ BFSparse(_, _, _)) :: Nil   => Some(bf)
      case BFZero(_, _) :: tail              => sumOption(tail)
      case nonZeroBF :: tail =>
        var bits = nonZeroBF match {
          case BFItem(item, _, _)       => RichJavaBitSet(hashes(item), width)
          case BFInstance(_, bitset, _) => bitset
          case BFSparse(_, cbitset, wid) =>
            cbitset.toJBitSet(wid)
        }

        tail.foreach { // TODO remove var using fold
          case BFZero(_, _) => ()
          case BFItem(item, h, wid) =>
            bits = bits | RichJavaBitSet(h(item), wid)
          case BFSparse(_, cbitset, wid) =>
            bits = bits | RichJavaBitSet(cbitset.toArray, wid)
          case BFInstance(_, bitset, _) =>
            bits = bits | bitset
        }

        val sumedBF: BFInstance[A] = BFInstance(hashes, bits, width)
        // Convert to Sparse if the density if low
        if (sumedBF.density < 0.1) {
          Some(sumedBF.toSparse)
        } else {
          Some(sumedBF)
        }
    }

  /**
   * Create a bloom filter with one item.
   */
  def create(item: A): BF[A] = BFItem(item, hashes, width)

  /**
   * Create a bloom filter with multiple items.
   */
  def create(data: A*): BF[A] = create(data.iterator)

  /**
   * Create a bloom filter with multiple items from an iterator
   */
  def create(data: Iterator[A]): BF[A] = sum(data.map(BFItem(_, hashes, width)))
}

object BF {
  implicit def equiv[A]: Equiv[BF[A]] =
    new Equiv[BF[A]] {
      def equiv(a: BF[A], b: BF[A]): Boolean =
        (a eq b) || ((a.numHashes == b.numHashes) &&
          (a.width == b.width) && a.toBitSet.equals(b.toBitSet))
    }
}

/**
 * Bloom Filter data structure
 */
sealed abstract class BF[A] extends java.io.Serializable {

  import RichJavaBitSet._ // TODO remove this

  def numHashes: Int

  def width: Int

  /**
   * The number of bits set to true in the bloom filter
   */
  def numBits: Int

  /**
   * Proportion of bits that are set to true.
   */
  def density = numBits.toDouble / width

  def ++(other: BF[A]): BF[A]

  def +(other: A): BF[A]

  def checkAndAdd(item: A): (BF[A], ApproximateBoolean)

  def contains(item: A): ApproximateBoolean =
    if (maybeContains(item)) {
      // The false positive probability (the probability that the Bloom filter erroneously
      // claims that an element x is in the set when x is not) is roughly
      // p = (1 - e^(-numHashes * setCardinality / width))^numHashes
      // See: http://en.wikipedia.org/wiki/Bloom_filter#Probability_of_false_positives
      //
      // However, the true set cardinality may not be known. From empirical evidence, though,
      // it is upper bounded with high probability by 1.1 * estimatedCardinality (as long as the
      // Bloom filter is not too full), so we plug this into the formula instead.
      // TODO: investigate this upper bound and density more closely (or derive a better formula).
      val fpProb =
        if (density > 0.95)
          1.0 // No confidence in the upper bound on cardinality.
        else
          scala.math.pow(1 - scala.math.exp(-numHashes * size.estimate * 1.1 / width), numHashes)

      ApproximateBoolean(true, 1 - fpProb)
    } else {
      // False negatives are not possible.
      ApproximateBoolean.exactFalse
    }

  /**
   * This may be faster if you don't care about evaluating
   * the false positive probability
   */
  def maybeContains(item: A): Boolean

  // Estimates the cardinality of the set of elements that have been
  // inserted into the Bloom Filter.
  def size: Approximate[Long]

  def toBitSet: jBitSet

  /**
   * Compute the Hamming distance between the two Bloom filters
   * `a` and `b`. The distance is defined as the number of bits that
   * need to change to in order to transform one filter into the other.
   */
  def hammingDistance(that: BF[A]): Int =
    (this, that) match {
      // Comparing with empty filter should give number
      // of bits in other set
      case (x: BFZero[A], y: BFZero[A]) => 0
      case (x: BFZero[A], y: BF[A])     => y.numBits
      case (x: BF[A], y: BFZero[A])     => x.numBits

      // Special case for Sparse vs. Sparse
      case (x: BFSparse[A], y: BFSparse[A]) => x.bits.xorCardinality(y.bits)

      // Otherwise compare as bit sets
      case (_, _) => (this.toBitSet ^ that.toBitSet).cardinality
    }

}

/**
 * Empty bloom filter.
 */
case class BFZero[A](hashes: BFHash[A], width: Int) extends BF[A] {

  def toBitSet: jBitSet = new jBitSet(width)

  def numHashes: Int = hashes.size

  def numBits = 0

  def ++(other: BF[A]) = other

  def +(other: A) = BFItem[A](other, hashes, width)

  def checkAndAdd(other: A): (BF[A], ApproximateBoolean) =
    (this + other, ApproximateBoolean.exactFalse)

  override def contains(item: A) = ApproximateBoolean.exactFalse

  def maybeContains(item: A): Boolean = false

  def size = Approximate.exact[Long](0)
}

/**
 * Bloom Filter with 1 value.
 */
case class BFItem[A](item: A, hashes: BFHash[A], width: Int) extends BF[A] {
  def numHashes: Int = hashes.size

  def numBits = numHashes

  def toBitSet: jBitSet = {
    val hashvalues = hashes(item)
    // Remove duplicates
    val hashBitsAsSet = Set(hashvalues: _*)
    RichJavaBitSet(hashBitsAsSet.toArray, width)
  }

  private[algebird] def toSparse: BFSparse[A] =
    BFSparse[A](hashes, RichCBitSet.fromArray(hashes(item)), width)

  def ++(other: BF[A]): BF[A] =
    other match {
      case bf @ BFZero(_, _)            => this
      case bf @ BFItem(otherItem, _, _) => toSparse + otherItem
      case _                            => other + item
    }

  def +(other: A) = this ++ BFItem(other, hashes, width)

  def checkAndAdd(other: A): (BF[A], ApproximateBoolean) =
    if (other == item) {
      (this, ApproximateBoolean.exactTrue)
    } else {
      (this + other, ApproximateBoolean.exactFalse)
    }

  override def contains(x: A) = ApproximateBoolean.exact(item == x)

  def maybeContains(x: A): Boolean =
    item == x

  def size = Approximate.exact[Long](1)
}

case class BFSparse[A](hashes: BFHash[A], bits: CBitSet, width: Int) extends BF[A] {

  import RichCBitSet._
  import RichJavaBitSet._

  def numHashes: Int = hashes.size

  def toBitSet: jBitSet = bits.toJBitSet(width)

  /**
   * Returns number of bits set to true
   */
  def numBits: Int = {
    val it = bits.intIterator
    var count = 0
    while (it.hasNext) {
      count += 1
      it.next
    }
    count
  }

  /**
   * Convert to a dense representation
   */
  def dense: BFInstance[A] = BFInstance[A](hashes, bits.toJBitSet(width), width)

  def ++(other: BF[A]): BF[A] = {
    require(this.width == other.width)
    require(this.numHashes == other.numHashes)

    other match {
      case bf @ BFZero(_, _)       => this
      case bf @ BFItem(item, _, _) => this + item
      case bf @ BFSparse(_, otherBits, _) => {
        // assume same hashes and width used

        // This is expensive in general.
        // We check to see if we are filling < 5%
        // of the bits, if so, stay sparse, if not go dense
        val newMaxSize = numBits + bf.numBits
        if (newMaxSize < (width / 10)) {
          BFSparse(hashes, bits ++ otherBits, width)
        } else {
          // Make a dense bitset
          BFInstance(hashes, bits.toJBitSet(width) | otherBits.toJBitSet(width), width)
        }
      }
      case _ => other ++ this
    }
  }

  def +(item: A): BF[A] = {
    val bitsToActivate = bits.clone
    bitsToActivate += hashes(item)

    BFSparse(hashes, bitsToActivate, width)
  }

  def checkAndAdd(other: A): (BF[A], ApproximateBoolean) =
    (this + other, contains(other))

  def maybeContains(item: A): Boolean = {
    val il = hashes(item)
    var idx = 0
    while (idx < il.length) {
      val i = il(idx)
      if (!bits.get(i)) return false
      idx += 1
    }
    true
  }

  def size: Approximate[Long] =
    BloomFilter.sizeEstimate(numBits, numHashes, width, 0.05)
}

/*
 * Bloom filter with multiple values
 */
case class BFInstance[A](hashes: BFHash[A], bits: jBitSet, width: Int) extends BF[A] {

  import RichCBitSet._
  import RichJavaBitSet._

  def numHashes: Int = hashes.size

  /**
   * The number of bits set to true
   */
  def numBits: Int = bits.cardinality()

  def toBitSet: jBitSet = bits

  def ++(other: BF[A]) = {
    require(this.width == other.width)
    require(this.numHashes == other.numHashes)

    other match {
      case BFZero(_, _)              => this
      case BFItem(item, _, _)        => this + item
      case BFSparse(_, otherBits, _) =>
        // assume same hashes used and same width
        BFInstance(hashes, bits | otherBits.toJBitSet(width), width)
      case bf @ BFInstance(_, otherBits, _) => {
        // assume same hashes used
        BFInstance(hashes, bits | otherBits, width) // TODO I have changed here.
      }
    }
  }

  def +(item: A): BFInstance[A] = {
    val itemHashes = hashes(item)
    BFInstance[A](hashes, bits | RichJavaBitSet(itemHashes, width), width)
  }

  def checkAndAdd(other: A): (BF[A], ApproximateBoolean) =
    (this + other, contains(other))

  def maybeContains(item: A): Boolean = {
    val il = hashes(item)
    var idx = 0
    while (idx < il.length) {
      val i = il(idx)
      if (!bits.get(i)) return false
      idx += 1
    }
    true
  }

  private[algebird] def toSparse: BFSparse[A] =
    BFSparse[A](hashes, RichCBitSet.fromJBitSet(bits), width)

  // use an approximation width of 0.05
  def size: Approximate[Long] =
    BloomFilter.sizeEstimate(numBits, numHashes, width, 0.05)
}

object BFInstance {
  def apply[A](hashes: BFHash[A], width: Int): BFInstance[A] =
    empty(hashes, width)

  def empty[A](hashes: BFHash[A], width: Int): BFInstance[A] =
    BFInstance(hashes, new jBitSet(width), width)
}

case class BFHash[A](numHashes: Int, width: Int)(implicit hash: Hash128[A]) {
  def size = numHashes

  def apply(s: A): Array[Int] =
    nextHash(s, 0, new Array[Int](4), 4, new Array[Int](numHashes))

  private def splitLong(x: Long, buffer: Array[Int], idx: Int): Unit = {
    // unfortunately, this is the function we committed to some time ago, and we have tests
    // locking it down. x.toInt & 0x7fffffff should work, but this gives a few different values
    def toNonNegativeInt(x: Long): Int =
      (math
        .abs(x)
        .toInt) & 0x7fffffff // no change for positive numbers, converts Integer.MIN_VALUE to positive number

    val upper = toNonNegativeInt(x >> 32)
    val lower = toNonNegativeInt((x << 32) >> 32)
    buffer(idx) = upper
    buffer(idx + 1) = lower
  }

  @annotation.tailrec
  private def nextHash(valueToHash: A,
                       hashIndex: Int,
                       buffer: Array[Int],
                       bidx: Int,
                       target: Array[Int]): Array[Int] =
    if (hashIndex == numHashes) target
    else {
      val thisBidx = if (bidx > 3) {
        val (a, b) =
          hash.hashWithSeed((numHashes - hashIndex).toLong, valueToHash)
        splitLong(a, buffer, 0)
        splitLong(b, buffer, 2)
        0
      } else bidx

      target(hashIndex) = buffer(thisBidx) % width
      nextHash(valueToHash, hashIndex + 1, buffer, thisBidx + 1, target)
    }
}

case class BloomFilterAggregator[A](bfMonoid: BloomFilterMonoid[A])
    extends MonoidAggregator[A, BF[A], BF[A]] {
  val monoid = bfMonoid

  def prepare(value: A) = monoid.create(value)
  def present(bf: BF[A]) = bf
}

object BloomFilterAggregator {
  def apply[A](numHashes: Int, width: Int)(implicit hash: Hash128[A]): BloomFilterAggregator[A] =
    BloomFilterAggregator[A](BloomFilterMonoid[A](numHashes, width))
}
