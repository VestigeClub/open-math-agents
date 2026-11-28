import certificates.«tail-sieve-11092009835083-12671-12799»
import certificates.«tail-sieve-11092009835083-12799-12917»
import certificates.«tail-sieve-11092009835083-12917-13007»
import certificates.«tail-sieve-11092009835083-13007-13049»

/-! Exact changes for the consecutive sieve primes from 12,671 to 13,049. -/
namespace TailSeries11092009835083From12671To13049

private theorem to12917 : FinalSeventhSieve.rough 11092009835083 12917+1151959269=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine Tail11092009835083From12671To12799.change Tail11092009835083From12799To12917.change rfl

private theorem to13007 : FinalSeventhSieve.rough 11092009835083 13007+1719420272=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine to12917 Tail11092009835083From12917To13007.change rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13049+1954414345=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine to13007 Tail11092009835083From13007To13049.change rfl

end TailSeries11092009835083From12671To13049
