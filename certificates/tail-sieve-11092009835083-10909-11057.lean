import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1000000000-1025000000»

/-! Exact changes for sieve primes 1328 through 1339. -/
open Finset
namespace Tail11092009835083From10909To11057

set_option maxRecDepth 16000 in
private theorem row10937 :
    FinalSeventhSieve.rough 11092009835083 10937+57725623=FinalSeventhSieve.rough 11092009835083 10909 :=
  LargeQuotientSieve.row (p:=10937) (q:=1014172975) (s:=31846) (rank:=51531238) (tiny:=1327) (pairs:=6195711)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1014172975 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row10939 :
    FinalSeventhSieve.rough 11092009835083 10939+57707172=FinalSeventhSieve.rough 11092009835083 10937 :=
  LargeQuotientSieve.row (p:=10939) (q:=1013987552) (s:=31843) (rank:=51522229) (tiny:=1328) (pairs:=6186270)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1013987552 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10939 : FinalSeventhSieve.rough 11092009835083 10939+115432795=FinalSeventhSieve.rough 11092009835083 10909 :=
  LargeQuotientSieve.combine row10937 row10939 rfl

set_option maxRecDepth 16000 in
private theorem row10949 :
    FinalSeventhSieve.rough 11092009835083 10949+57645850=FinalSeventhSieve.rough 11092009835083 10939 :=
  LargeQuotientSieve.row (p:=10949) (q:=1013061451) (s:=31828) (rank:=51477673) (tiny:=1329) (pairs:=6169505)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1013061451 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10949 : FinalSeventhSieve.rough 11092009835083 10949+173078645=FinalSeventhSieve.rough 11092009835083 10909 :=
  LargeQuotientSieve.combine to10939 row10949 rfl

set_option maxRecDepth 16000 in
private theorem row10957 :
    FinalSeventhSieve.rough 11092009835083 10957+57595328=FinalSeventhSieve.rough 11092009835083 10949 :=
  LargeQuotientSieve.row (p:=10957) (q:=1012321788) (s:=31817) (rank:=51442024) (tiny:=1330) (pairs:=6154633)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1012321788 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10957 : FinalSeventhSieve.rough 11092009835083 10957+230673973=FinalSeventhSieve.rough 11092009835083 10909 :=
  LargeQuotientSieve.combine to10949 row10957 rfl

set_option maxRecDepth 16000 in
private theorem row10973 :
    FinalSeventhSieve.rough 11092009835083 10973+57501824=FinalSeventhSieve.rough 11092009835083 10957 :=
  LargeQuotientSieve.row (p:=10973) (q:=1010845697) (s:=31793) (rank:=51370722) (tiny:=1331) (pairs:=6132432)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1010845697 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10973 : FinalSeventhSieve.rough 11092009835083 10973+288175797=FinalSeventhSieve.rough 11092009835083 10909 :=
  LargeQuotientSieve.combine to10957 row10973 rfl

set_option maxRecDepth 16000 in
private theorem row10979 :
    FinalSeventhSieve.rough 11092009835083 10979+57462164=FinalSeventhSieve.rough 11092009835083 10973 :=
  LargeQuotientSieve.row (p:=10979) (q:=1010293272) (s:=31785) (rank:=51344055) (tiny:=1332) (pairs:=6119440)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1010293272 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10979 : FinalSeventhSieve.rough 11092009835083 10979+345637961=FinalSeventhSieve.rough 11092009835083 10909 :=
  LargeQuotientSieve.combine to10973 row10979 rfl

set_option maxRecDepth 16000 in
private theorem row10987 :
    FinalSeventhSieve.rough 11092009835083 10987+57411949=FinalSeventhSieve.rough 11092009835083 10979 :=
  LargeQuotientSieve.row (p:=10987) (q:=1009557644) (s:=31773) (rank:=51308607) (tiny:=1333) (pairs:=6104674)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1009557644 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10987 : FinalSeventhSieve.rough 11092009835083 10987+403049910=FinalSeventhSieve.rough 11092009835083 10909 :=
  LargeQuotientSieve.combine to10979 row10987 rfl

set_option maxRecDepth 16000 in
private theorem row10993 :
    FinalSeventhSieve.rough 11092009835083 10993+57372309=FinalSeventhSieve.rough 11092009835083 10987 :=
  LargeQuotientSieve.row (p:=10993) (q:=1009006625) (s:=31764) (rank:=51281971) (tiny:=1334) (pairs:=6091671)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1009006625 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10993 : FinalSeventhSieve.rough 11092009835083 10993+460422219=FinalSeventhSieve.rough 11092009835083 10909 :=
  LargeQuotientSieve.combine to10987 row10993 rfl

set_option maxRecDepth 16000 in
private theorem row11003 :
    FinalSeventhSieve.rough 11092009835083 11003+57311655=FinalSeventhSieve.rough 11092009835083 10993 :=
  LargeQuotientSieve.row (p:=11003) (q:=1008089596) (s:=31750) (rank:=51237840) (tiny:=1335) (pairs:=6075149)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1008089596 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11003 : FinalSeventhSieve.rough 11092009835083 11003+517733874=FinalSeventhSieve.rough 11092009835083 10909 :=
  LargeQuotientSieve.combine to10993 row11003 rfl

set_option maxRecDepth 16000 in
private theorem row11027 :
    FinalSeventhSieve.rough 11092009835083 11027+57176741=FinalSeventhSieve.rough 11092009835083 11003 :=
  LargeQuotientSieve.row (p:=11027) (q:=1005895514) (s:=31715) (rank:=51132064) (tiny:=1336) (pairs:=6046012)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1005895514 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11027 : FinalSeventhSieve.rough 11092009835083 11027+574910615=FinalSeventhSieve.rough 11092009835083 10909 :=
  LargeQuotientSieve.combine to11003 row11027 rfl

set_option maxRecDepth 16000 in
private theorem row11047 :
    FinalSeventhSieve.rough 11092009835083 11047+57063306=FinalSeventhSieve.rough 11092009835083 11027 :=
  LargeQuotientSieve.row (p:=11047) (q:=1004074394) (s:=31687) (rank:=51043926) (tiny:=1337) (pairs:=6020716)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1004074394 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11047 : FinalSeventhSieve.rough 11092009835083 11047+631973921=FinalSeventhSieve.rough 11092009835083 10909 :=
  LargeQuotientSieve.combine to11027 row11047 rfl

set_option maxRecDepth 16000 in
private theorem row11057 :
    FinalSeventhSieve.rough 11092009835083 11057+57003217=FinalSeventhSieve.rough 11092009835083 11047 :=
  LargeQuotientSieve.row (p:=11057) (q:=1003166305) (s:=31672) (rank:=51000170) (tiny:=1338) (pairs:=6004384)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1003166305 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11057 : FinalSeventhSieve.rough 11092009835083 11057+688977138=FinalSeventhSieve.rough 11092009835083 10909 :=
  LargeQuotientSieve.combine to11047 row11057 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 11057+688977138=FinalSeventhSieve.rough 11092009835083 10909 := to11057

end Tail11092009835083From10909To11057
