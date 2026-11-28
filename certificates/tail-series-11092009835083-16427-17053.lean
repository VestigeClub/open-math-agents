import certificates.«tail-sieve-11092009835083-16427-16553»
import certificates.«tail-sieve-11092009835083-16553-16661»
import certificates.«tail-sieve-11092009835083-16661-16811»
import certificates.«tail-sieve-11092009835083-16811-16927»
import certificates.«tail-sieve-11092009835083-16927-17029»
import certificates.«tail-sieve-11092009835083-17029-17053»

/-! Exact changes for the consecutive sieve primes from 16,427 to 17,053. -/
namespace TailSeries11092009835083From16427To17053

private theorem to16661 : FinalSeventhSieve.rough 11092009835083 16661+858744430=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine Tail11092009835083From16427To16553.change Tail11092009835083From16553To16661.change rfl

private theorem to16811 : FinalSeventhSieve.rough 11092009835083 16811+1283004918=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16661 Tail11092009835083From16661To16811.change rfl

private theorem to16927 : FinalSeventhSieve.rough 11092009835083 16927+1703375237=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16811 Tail11092009835083From16811To16927.change rfl

private theorem to17029 : FinalSeventhSieve.rough 11092009835083 17029+2120755890=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16927 Tail11092009835083From16927To17029.change rfl

theorem change : FinalSeventhSieve.rough 11092009835083 17053+2259326425=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to17029 Tail11092009835083From17029To17053.change rfl

end TailSeries11092009835083From16427To17053
