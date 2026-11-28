import certificates.«tail-sieve-11092009835083-10559-10663»
import certificates.«tail-sieve-11092009835083-10663-10781»
import certificates.«tail-sieve-11092009835083-10781-10799»

/-! Exact changes for the consecutive sieve primes from 10,559 to 10,799. -/
namespace TailSeries11092009835083From10559To10799

private theorem to10781 : FinalSeventhSieve.rough 11092009835083 10781+1425646044=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine Tail11092009835083From10559To10663.change Tail11092009835083From10663To10781.change rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10799+1542870737=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine to10781 Tail11092009835083From10781To10799.change rfl

end TailSeries11092009835083From10559To10799
