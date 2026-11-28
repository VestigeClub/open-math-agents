import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 1275 through 1275. -/
open Finset
namespace Tail11092009835083From10399To10427

set_option maxRecDepth 16000 in
private theorem row10427 :
    FinalSeventhSieve.rough 11092009835083 10427+61049426=FinalSeventhSieve.rough 11092009835083 10399 :=
  LargeQuotientSieve.row (p:=10427) (q:=1063777676) (s:=32615) (rank:=53920177) (tiny:=1274) (pairs:=7130522)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1063777676 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10427+61049426=FinalSeventhSieve.rough 11092009835083 10399 := row10427

end Tail11092009835083From10399To10427
