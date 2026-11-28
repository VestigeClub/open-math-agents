import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-675000000-700000000»

/-! Exact changes for sieve primes 1860 through 1871. -/
open Finset
namespace Tail11092009835083From15959To16073

set_option maxRecDepth 16000 in
private theorem row15971 :
    FinalSeventhSieve.rough 11092009835083 15971+37233829=FinalSeventhSieve.rough 11092009835083 15959 :=
  LargeQuotientSieve.row (p:=15971) (q:=694509413) (s:=26353) (rank:=35983244) (tiny:=1859) (pairs:=1252443)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 694509413 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row15973 :
    FinalSeventhSieve.rough 11092009835083 15973+37226401=FinalSeventhSieve.rough 11092009835083 15971 :=
  LargeQuotientSieve.row (p:=15973) (q:=694422452) (s:=26351) (rank:=35978913) (tiny:=1860) (pairs:=1249347)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 694422452 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15973 : FinalSeventhSieve.rough 11092009835083 15973+74460230=FinalSeventhSieve.rough 11092009835083 15959 :=
  LargeQuotientSieve.combine row15971 row15973 rfl

set_option maxRecDepth 16000 in
private theorem row15991 :
    FinalSeventhSieve.rough 11092009835083 15991+37181605=FinalSeventhSieve.rough 11092009835083 15973 :=
  LargeQuotientSieve.row (p:=15991) (q:=693640787) (s:=26337) (rank:=35940507) (tiny:=1861) (pairs:=1242958)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 693640787 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15991 : FinalSeventhSieve.rough 11092009835083 15991+111641835=FinalSeventhSieve.rough 11092009835083 15959 :=
  LargeQuotientSieve.combine to15973 row15991 rfl

set_option maxRecDepth 16000 in
private theorem row16001 :
    FinalSeventhSieve.rough 11092009835083 16001+37155620=FinalSeventhSieve.rough 11092009835083 15991 :=
  LargeQuotientSieve.row (p:=16001) (q:=693207289) (s:=26328) (rank:=35919249) (tiny:=1862) (pairs:=1238232)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 693207289 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16001 : FinalSeventhSieve.rough 11092009835083 16001+148797455=FinalSeventhSieve.rough 11092009835083 15959 :=
  LargeQuotientSieve.combine to15991 row16001 rfl

set_option maxRecDepth 16000 in
private theorem row16007 :
    FinalSeventhSieve.rough 11092009835083 16007+37139050=FinalSeventhSieve.rough 11092009835083 16001 :=
  LargeQuotientSieve.row (p:=16007) (q:=692947450) (s:=26323) (rank:=35906588) (tiny:=1863) (pairs:=1234324)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 692947450 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16007 : FinalSeventhSieve.rough 11092009835083 16007+185936505=FinalSeventhSieve.rough 11092009835083 15959 :=
  LargeQuotientSieve.combine to16001 row16007 rfl

set_option maxRecDepth 16000 in
private theorem row16033 :
    FinalSeventhSieve.rough 11092009835083 16033+37076002=FinalSeventhSieve.rough 11092009835083 16007 :=
  LargeQuotientSieve.row (p:=16033) (q:=691823728) (s:=26302) (rank:=35851524) (tiny:=1864) (pairs:=1226341)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 691823728 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16033 : FinalSeventhSieve.rough 11092009835083 16033+223012507=FinalSeventhSieve.rough 11092009835083 15959 :=
  LargeQuotientSieve.combine to16007 row16033 rfl

set_option maxRecDepth 16000 in
private theorem row16057 :
    FinalSeventhSieve.rough 11092009835083 16057+37017593=FinalSeventhSieve.rough 11092009835083 16033 :=
  LargeQuotientSieve.row (p:=16057) (q:=690789676) (s:=26282) (rank:=35800689) (tiny:=1865) (pairs:=1218768)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 690789676 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16057 : FinalSeventhSieve.rough 11092009835083 16057+260030100=FinalSeventhSieve.rough 11092009835083 15959 :=
  LargeQuotientSieve.combine to16033 row16057 rfl

set_option maxRecDepth 16000 in
private theorem row16061 :
    FinalSeventhSieve.rough 11092009835083 16061+37005720=FinalSeventhSieve.rough 11092009835083 16057 :=
  LargeQuotientSieve.row (p:=16061) (q:=690617634) (s:=26279) (rank:=35792222) (tiny:=1866) (pairs:=1215363)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 690617634 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16061 : FinalSeventhSieve.rough 11092009835083 16061+297035820=FinalSeventhSieve.rough 11092009835083 15959 :=
  LargeQuotientSieve.combine to16057 row16061 rfl

set_option maxRecDepth 16000 in
private theorem row16063 :
    FinalSeventhSieve.rough 11092009835083 16063+36998497=FinalSeventhSieve.rough 11092009835083 16061 :=
  LargeQuotientSieve.row (p:=16063) (q:=690531646) (s:=26277) (rank:=35788013) (tiny:=1867) (pairs:=1212350)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 690531646 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16063 : FinalSeventhSieve.rough 11092009835083 16063+334034317=FinalSeventhSieve.rough 11092009835083 15959 :=
  LargeQuotientSieve.combine to16061 row16063 rfl

set_option maxRecDepth 16000 in
private theorem row16067 :
    FinalSeventhSieve.rough 11092009835083 16067+36986497=FinalSeventhSieve.rough 11092009835083 16063 :=
  LargeQuotientSieve.row (p:=16067) (q:=690359733) (s:=26274) (rank:=35779485) (tiny:=1868) (pairs:=1208879)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 690359733 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16067 : FinalSeventhSieve.rough 11092009835083 16067+371020814=FinalSeventhSieve.rough 11092009835083 15959 :=
  LargeQuotientSieve.combine to16063 row16067 rfl

set_option maxRecDepth 16000 in
private theorem row16069 :
    FinalSeventhSieve.rough 11092009835083 16069+36979194=FinalSeventhSieve.rough 11092009835083 16067 :=
  LargeQuotientSieve.row (p:=16069) (q:=690273808) (s:=26273) (rank:=35775220) (tiny:=1869) (pairs:=1205842)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 690273808 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16069 : FinalSeventhSieve.rough 11092009835083 16069+408000008=FinalSeventhSieve.rough 11092009835083 15959 :=
  LargeQuotientSieve.combine to16067 row16069 rfl

set_option maxRecDepth 16000 in
private theorem row16073 :
    FinalSeventhSieve.rough 11092009835083 16073+36967376=FinalSeventhSieve.rough 11092009835083 16069 :=
  LargeQuotientSieve.row (p:=16073) (q:=690102024) (s:=26269) (rank:=35766822) (tiny:=1870) (pairs:=1202423)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 690102024 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16073 : FinalSeventhSieve.rough 11092009835083 16073+444967384=FinalSeventhSieve.rough 11092009835083 15959 :=
  LargeQuotientSieve.combine to16069 row16073 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 16073+444967384=FinalSeventhSieve.rough 11092009835083 15959 := to16073

end Tail11092009835083From15959To16073
