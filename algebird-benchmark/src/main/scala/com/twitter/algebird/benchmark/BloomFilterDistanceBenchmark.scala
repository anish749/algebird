package com.twitter.algebird
package benchmark

import org.openjdk.jmh.annotations._

object BloomFilterDistanceBenchmark {

  @State(Scope.Benchmark)
  class BloomFilterState {

    val nbrOfElements: Int = 1000
    val falsePositiveRate = 0.01

    def randomElements =
      BloomFilterCreateBenchmark.createRandomString(nbrOfElements, 10)

    val emptyBF1: BF[String] =
      BloomFilter[String](nbrOfElements, falsePositiveRate).zero
    val emptyBF2: BF[String] =
      BloomFilter[String](nbrOfElements, falsePositiveRate).zero

    val bF1: BF[String] =
      BloomFilter[String](nbrOfElements, falsePositiveRate)
        .create(randomElements: _*)
    val bF2: BF[String] =
      BloomFilter[String](nbrOfElements, falsePositiveRate)
        .create(randomElements: _*)

  }
}

class BloomFilterDistanceBenchmark {

  import BloomFilterDistanceBenchmark._

  @Benchmark
  def distanceOfEmptyVsEmpty(bloomFilterState: BloomFilterState): Int =
    bloomFilterState.emptyBF1.hammingDistance(bloomFilterState.emptyBF2)

  @Benchmark
  def distanceOfEmptyVsDense(bloomFilterState: BloomFilterState): Int =
    bloomFilterState.emptyBF1.hammingDistance(bloomFilterState.bF1)

  @Benchmark
  def distanceOfDenseVsDense(bloomFilterState: BloomFilterState): Int =
    bloomFilterState.bF1.hammingDistance(bloomFilterState.bF2)

  @Benchmark
  def distanceOfSame(bloomFilterState: BloomFilterState): Int =
    bloomFilterState.bF1.hammingDistance(bloomFilterState.bF1)

}
