import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 1269 through 1271. -/
open Finset
namespace Tail11092009835083From10333To10357

set_option maxRecDepth 16000 in
private theorem row10337 :
    FinalSeventhSieve.rough 11092009835083 10337+61644794=FinalSeventhSieve.rough 11092009835083 10333 :=
  LargeQuotientSieve.row (p:=10337) (q:=1073039550) (s:=32757) (rank:=54366279) (tiny:=1268) (pairs:=7279782)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1073039550 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row10343 :
    FinalSeventhSieve.rough 11092009835083 10343+61599685=FinalSeventhSieve.rough 11092009835083 10337 :=
  LargeQuotientSieve.row (p:=10343) (q:=1072417077) (s:=32747) (rank:=54336446) (tiny:=1269) (pairs:=7264507)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1072417077 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10343 : FinalSeventhSieve.rough 11092009835083 10343+123244479=FinalSeventhSieve.rough 11092009835083 10333 :=
  LargeQuotientSieve.combine row10337 row10343 rfl

set_option maxRecDepth 16000 in
private theorem row10357 :
    FinalSeventhSieve.rough 11092009835083 10357+61505873=FinalSeventhSieve.rough 11092009835083 10343 :=
  LargeQuotientSieve.row (p:=10357) (q:=1070967445) (s:=32725) (rank:=54266659) (tiny:=1270) (pairs:=7240483)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1070967445 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10357 : FinalSeventhSieve.rough 11092009835083 10357+184750352=FinalSeventhSieve.rough 11092009835083 10333 :=
  LargeQuotientSieve.combine to10343 row10357 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10357+184750352=FinalSeventhSieve.rough 11092009835083 10333 := to10357

end Tail11092009835083From10333To10357
