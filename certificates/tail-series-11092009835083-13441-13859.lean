import certificates.«tail-sieve-11092009835083-13441-13567»
import certificates.«tail-sieve-11092009835083-13567-13687»
import certificates.«tail-sieve-11092009835083-13687-13763»
import certificates.«tail-sieve-11092009835083-13763-13859»

/-! Exact changes for the consecutive sieve primes from 13,441 to 13,859. -/
namespace TailSeries11092009835083From13441To13859

private theorem to13687 : FinalSeventhSieve.rough 11092009835083 13687+1077113874=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine Tail11092009835083From13441To13567.change Tail11092009835083From13567To13687.change rfl

private theorem to13763 : FinalSeventhSieve.rough 11092009835083 13763+1608409251=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine to13687 Tail11092009835083From13687To13763.change rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13859+1959875278=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine to13763 Tail11092009835083From13763To13859.change rfl

end TailSeries11092009835083From13441To13859
