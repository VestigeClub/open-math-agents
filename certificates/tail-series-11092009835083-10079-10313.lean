import certificates.«tail-sieve-11092009835083-10079-10169»
import certificates.«tail-sieve-11092009835083-10169-10273»
import certificates.«tail-sieve-11092009835083-10273-10313»

/-! Exact changes for the consecutive sieve primes from 10,079 to 10,313. -/
namespace TailSeries11092009835083From10079To10313

private theorem to10273 : FinalSeventhSieve.rough 11092009835083 10273+1506823181=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine Tail11092009835083From10079To10169.change Tail11092009835083From10169To10273.change rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10313+1754461236=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine to10273 Tail11092009835083From10273To10313.change rfl

end TailSeries11092009835083From10079To10313
