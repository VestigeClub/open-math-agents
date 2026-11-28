import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 1277 through 1277. -/
open Finset
namespace Tail11092009835083From10429To10433

set_option maxRecDepth 16000 in
private theorem row10433 :
    FinalSeventhSieve.rough 11092009835083 10433+60996580=FinalSeventhSieve.rough 11092009835083 10429 :=
  LargeQuotientSieve.row (p:=10433) (q:=1063165900) (s:=32606) (rank:=53890703) (tiny:=1276) (pairs:=7107152)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1063165900 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10433+60996580=FinalSeventhSieve.rough 11092009835083 10429 := row10433

end Tail11092009835083From10429To10433
