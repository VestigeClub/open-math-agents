import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1025000000-1050000000»

/-! Exact changes for sieve primes 1314 through 1315. -/
open Finset
namespace Tail11092009835083From10781To10799

set_option maxRecDepth 16000 in
private theorem row10789 :
    FinalSeventhSieve.rough 11092009835083 10789+58643921=FinalSeventhSieve.rough 11092009835083 10781 :=
  LargeQuotientSieve.row (p:=10789) (q:=1028085071) (s:=32063) (rank:=52201906) (tiny:=1313) (pairs:=6443327)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1028085071 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row10799 :
    FinalSeventhSieve.rough 11092009835083 10799+58580772=FinalSeventhSieve.rough 11092009835083 10789 :=
  LargeQuotientSieve.row (p:=10799) (q:=1027133052) (s:=32048) (rank:=52156212) (tiny:=1314) (pairs:=6425873)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1027133052 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10799 : FinalSeventhSieve.rough 11092009835083 10799+117224693=FinalSeventhSieve.rough 11092009835083 10781 :=
  LargeQuotientSieve.combine row10789 row10799 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10799+117224693=FinalSeventhSieve.rough 11092009835083 10781 := to10799

end Tail11092009835083From10781To10799
