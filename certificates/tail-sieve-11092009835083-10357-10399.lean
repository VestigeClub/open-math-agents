import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 1272 through 1274. -/
open Finset
namespace Tail11092009835083From10357To10399

set_option maxRecDepth 16000 in
private theorem row10369 :
    FinalSeventhSieve.rough 11092009835083 10369+61424476=FinalSeventhSieve.rough 11092009835083 10357 :=
  LargeQuotientSieve.row (p:=10369) (q:=1069728019) (s:=32706) (rank:=54206875) (tiny:=1271) (pairs:=7218871)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1069728019 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row10391 :
    FinalSeventhSieve.rough 11092009835083 10391+61283013=FinalSeventhSieve.rough 11092009835083 10369 :=
  LargeQuotientSieve.row (p:=10391) (q:=1067463173) (s:=32672) (rank:=54097908) (tiny:=1272) (pairs:=7186376)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1067463173 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10391 : FinalSeventhSieve.rough 11092009835083 10391+122707489=FinalSeventhSieve.rough 11092009835083 10357 :=
  LargeQuotientSieve.combine row10369 row10391 rfl

set_option maxRecDepth 16000 in
private theorem row10399 :
    FinalSeventhSieve.rough 11092009835083 10399+61226220=FinalSeventhSieve.rough 11092009835083 10391 :=
  LargeQuotientSieve.row (p:=10399) (q:=1066641968) (s:=32659) (rank:=54058322) (tiny:=1273) (pairs:=7169170)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1066641968 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10399 : FinalSeventhSieve.rough 11092009835083 10399+183933709=FinalSeventhSieve.rough 11092009835083 10357 :=
  LargeQuotientSieve.combine to10391 row10399 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10399+183933709=FinalSeventhSieve.rough 11092009835083 10357 := to10399

end Tail11092009835083From10357To10399
