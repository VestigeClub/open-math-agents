import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-775000000-800000000»

/-! Exact changes for sieve primes 1674 through 1678. -/
open Finset
namespace Tail11092009835083From14243To14303

set_option maxRecDepth 16000 in
private theorem row14249 :
    FinalSeventhSieve.rough 11092009835083 14249+42419247=FinalSeventhSieve.rough 11092009835083 14243 :=
  LargeQuotientSieve.row (p:=14249) (q:=778441282) (s:=27900) (rank:=40093416) (tiny:=1673) (pairs:=2327503)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 778441282 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row14251 :
    FinalSeventhSieve.rough 11092009835083 14251+42409276=FinalSeventhSieve.rough 11092009835083 14249 :=
  LargeQuotientSieve.row (p:=14251) (q:=778332035) (s:=27898) (rank:=40088071) (tiny:=1674) (pairs:=2322878)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 778332035 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14251 : FinalSeventhSieve.rough 11092009835083 14251+84828523=FinalSeventhSieve.rough 11092009835083 14243 :=
  LargeQuotientSieve.combine row14249 row14251 rfl

set_option maxRecDepth 16000 in
private theorem row14281 :
    FinalSeventhSieve.rough 11092009835083 14281+42315007=FinalSeventhSieve.rough 11092009835083 14251 :=
  LargeQuotientSieve.row (p:=14281) (q:=776696998) (s:=27869) (rank:=40008080) (tiny:=1675) (pairs:=2308601)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 776696998 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14281 : FinalSeventhSieve.rough 11092009835083 14281+127143530=FinalSeventhSieve.rough 11092009835083 14243 :=
  LargeQuotientSieve.combine to14251 row14281 rfl

set_option maxRecDepth 16000 in
private theorem row14293 :
    FinalSeventhSieve.rough 11092009835083 14293+42275264=FinalSeventhSieve.rough 11092009835083 14281 :=
  LargeQuotientSieve.row (p:=14293) (q:=776044905) (s:=27857) (rank:=39976355) (tiny:=1676) (pairs:=2300584)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 776044905 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14293 : FinalSeventhSieve.rough 11092009835083 14293+169418794=FinalSeventhSieve.rough 11092009835083 14243 :=
  LargeQuotientSieve.combine to14281 row14293 rfl

set_option maxRecDepth 16000 in
private theorem row14303 :
    FinalSeventhSieve.rough 11092009835083 14303+42241588=FinalSeventhSieve.rough 11092009835083 14293 :=
  LargeQuotientSieve.row (p:=14303) (q:=775502330) (s:=27847) (rank:=39949995) (tiny:=1677) (pairs:=2293269)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 775502330 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14303 : FinalSeventhSieve.rough 11092009835083 14303+211660382=FinalSeventhSieve.rough 11092009835083 14243 :=
  LargeQuotientSieve.combine to14293 row14303 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 14303+211660382=FinalSeventhSieve.rough 11092009835083 14243 := to14303

end Tail11092009835083From14243To14303
