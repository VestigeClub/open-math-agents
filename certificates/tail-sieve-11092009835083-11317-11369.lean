import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-975000000-1000000000»

/-! Exact changes for sieve primes 1369 through 1373. -/
open Finset
namespace Tail11092009835083From11317To11369

set_option maxRecDepth 16000 in
private theorem row11321 :
    FinalSeventhSieve.rough 11092009835083 11321+55431189=FinalSeventhSieve.rough 11092009835083 11317 :=
  LargeQuotientSieve.row (p:=11321) (q:=979772973) (s:=31301) (rank:=49870588) (tiny:=1368) (pairs:=5561968)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 979772973 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row11329 :
    FinalSeventhSieve.rough 11092009835083 11329+55384233=FinalSeventhSieve.rough 11092009835083 11321 :=
  LargeQuotientSieve.row (p:=11329) (q:=979081104) (s:=31290) (rank:=49837179) (tiny:=1369) (pairs:=5548422)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 979081104 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11329 : FinalSeventhSieve.rough 11092009835083 11329+110815422=FinalSeventhSieve.rough 11092009835083 11317 :=
  LargeQuotientSieve.combine row11321 row11329 rfl

set_option maxRecDepth 16000 in
private theorem row11351 :
    FinalSeventhSieve.rough 11092009835083 11351+55267828=FinalSeventhSieve.rough 11092009835083 11329 :=
  LargeQuotientSieve.row (p:=11351) (q:=977183493) (s:=31259) (rank:=49745707) (tiny:=1370) (pairs:=5523490)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 977183493 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11351 : FinalSeventhSieve.rough 11092009835083 11351+166083250=FinalSeventhSieve.rough 11092009835083 11317 :=
  LargeQuotientSieve.combine to11329 row11351 rfl

set_option maxRecDepth 16000 in
private theorem row11353 :
    FinalSeventhSieve.rough 11092009835083 11353+55250848=FinalSeventhSieve.rough 11092009835083 11351 :=
  LargeQuotientSieve.row (p:=11353) (q:=977011348) (s:=31257) (rank:=49737340) (tiny:=1371) (pairs:=5514878)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 977011348 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11353 : FinalSeventhSieve.rough 11092009835083 11353+221334098=FinalSeventhSieve.rough 11092009835083 11317 :=
  LargeQuotientSieve.combine to11351 row11353 rfl

set_option maxRecDepth 16000 in
private theorem row11369 :
    FinalSeventhSieve.rough 11092009835083 11369+55164396=FinalSeventhSieve.rough 11092009835083 11353 :=
  LargeQuotientSieve.row (p:=11369) (q:=975636365) (s:=31235) (rank:=49670916) (tiny:=1372) (pairs:=5494851)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 975636365 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11369 : FinalSeventhSieve.rough 11092009835083 11369+276498494=FinalSeventhSieve.rough 11092009835083 11317 :=
  LargeQuotientSieve.combine to11353 row11369 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 11369+276498494=FinalSeventhSieve.rough 11092009835083 11317 := to11369

end Tail11092009835083From11317To11369
