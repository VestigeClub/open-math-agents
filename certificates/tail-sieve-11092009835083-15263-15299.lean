import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-725000000-750000000»

/-! Exact changes for sieve primes 1782 through 1787. -/
open Finset
namespace Tail11092009835083From15263To15299

set_option maxRecDepth 16000 in
private theorem row15269 :
    FinalSeventhSieve.rough 11092009835083 15269+39189984=FinalSeventhSieve.rough 11092009835083 15263 :=
  LargeQuotientSieve.row (p:=15269) (q:=726439834) (s:=26952) (rank:=37549981) (tiny:=1781) (pairs:=1641783)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 726439834 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row15271 :
    FinalSeventhSieve.rough 11092009835083 15271+39181735=FinalSeventhSieve.rough 11092009835083 15269 :=
  LargeQuotientSieve.row (p:=15271) (q:=726344694) (s:=26950) (rank:=37545382) (tiny:=1782) (pairs:=1638134)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 726344694 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15271 : FinalSeventhSieve.rough 11092009835083 15271+78371719=FinalSeventhSieve.rough 11092009835083 15263 :=
  LargeQuotientSieve.combine row15269 row15271 rfl

set_option maxRecDepth 16000 in
private theorem row15277 :
    FinalSeventhSieve.rough 11092009835083 15277+39163021=FinalSeventhSieve.rough 11092009835083 15271 :=
  LargeQuotientSieve.row (p:=15277) (q:=726059424) (s:=26945) (rank:=37531292) (tiny:=1783) (pairs:=1633511)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 726059424 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15277 : FinalSeventhSieve.rough 11092009835083 15277+117534740=FinalSeventhSieve.rough 11092009835083 15263 :=
  LargeQuotientSieve.combine to15271 row15277 rfl

set_option maxRecDepth 16000 in
private theorem row15287 :
    FinalSeventhSieve.rough 11092009835083 15287+39134112=FinalSeventhSieve.rough 11092009835083 15277 :=
  LargeQuotientSieve.row (p:=15287) (q:=725584472) (s:=26936) (rank:=37508070) (tiny:=1784) (pairs:=1627825)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 725584472 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15287 : FinalSeventhSieve.rough 11092009835083 15287+156668852=FinalSeventhSieve.rough 11092009835083 15263 :=
  LargeQuotientSieve.combine to15277 row15287 rfl

set_option maxRecDepth 16000 in
private theorem row15289 :
    FinalSeventhSieve.rough 11092009835083 15289+39125769=FinalSeventhSieve.rough 11092009835083 15287 :=
  LargeQuotientSieve.row (p:=15289) (q:=725489556) (s:=26934) (rank:=37503359) (tiny:=1785) (pairs:=1624194)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 725489556 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15289 : FinalSeventhSieve.rough 11092009835083 15289+195794621=FinalSeventhSieve.rough 11092009835083 15263 :=
  LargeQuotientSieve.combine to15287 row15289 rfl

set_option maxRecDepth 16000 in
private theorem row15299 :
    FinalSeventhSieve.rough 11092009835083 15299+39096996=FinalSeventhSieve.rough 11092009835083 15289 :=
  LargeQuotientSieve.row (p:=15299) (q:=725015349) (s:=26926) (rank:=37480236) (tiny:=1786) (pairs:=1618545)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 725015349 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15299 : FinalSeventhSieve.rough 11092009835083 15299+234891617=FinalSeventhSieve.rough 11092009835083 15263 :=
  LargeQuotientSieve.combine to15289 row15299 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 15299+234891617=FinalSeventhSieve.rough 11092009835083 15263 := to15299

end Tail11092009835083From15263To15299
