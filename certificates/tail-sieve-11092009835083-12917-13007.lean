import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-850000000-875000000»

/-! Exact changes for sieve primes 1539 through 1550. -/
open Finset
namespace Tail11092009835083From12917To13007

set_option maxRecDepth 16000 in
private theorem row12919 :
    FinalSeventhSieve.rough 11092009835083 12919+47496170=FinalSeventhSieve.rough 11092009835083 12917 :=
  LargeQuotientSieve.row (p:=12919) (q:=858581146) (s:=29301) (rank:=43999086) (tiny:=1538) (pairs:=3498621)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 858581146 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row12923 :
    FinalSeventhSieve.rough 11092009835083 12923+47476184=FinalSeventhSieve.rough 11092009835083 12919 :=
  LargeQuotientSieve.row (p:=12923) (q:=858315393) (s:=29297) (rank:=43986207) (tiny:=1539) (pairs:=3491515)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 858315393 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12923 : FinalSeventhSieve.rough 11092009835083 12923+94972354=FinalSeventhSieve.rough 11092009835083 12917 :=
  LargeQuotientSieve.combine row12919 row12923 rfl

set_option maxRecDepth 16000 in
private theorem row12941 :
    FinalSeventhSieve.rough 11092009835083 12941+47403811=FinalSeventhSieve.rough 11092009835083 12923 :=
  LargeQuotientSieve.row (p:=12941) (q:=857121538) (s:=29276) (rank:=43928111) (tiny:=1540) (pairs:=3477239)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 857121538 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12941 : FinalSeventhSieve.rough 11092009835083 12941+142376165=FinalSeventhSieve.rough 11092009835083 12917 :=
  LargeQuotientSieve.combine to12923 row12941 rfl

set_option maxRecDepth 16000 in
private theorem row12953 :
    FinalSeventhSieve.rough 11092009835083 12953+47354127=FinalSeventhSieve.rough 11092009835083 12941 :=
  LargeQuotientSieve.row (p:=12953) (q:=856327478) (s:=29263) (rank:=43889609) (tiny:=1541) (pairs:=3466058)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 856327478 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12953 : FinalSeventhSieve.rough 11092009835083 12953+189730292=FinalSeventhSieve.rough 11092009835083 12917 :=
  LargeQuotientSieve.combine to12941 row12953 rfl

set_option maxRecDepth 16000 in
private theorem row12959 :
    FinalSeventhSieve.rough 11092009835083 12959+47326792=FinalSeventhSieve.rough 11092009835083 12953 :=
  LargeQuotientSieve.row (p:=12959) (q:=855931000) (s:=29256) (rank:=43870368) (tiny:=1542) (pairs:=3457965)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 855931000 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12959 : FinalSeventhSieve.rough 11092009835083 12959+237057084=FinalSeventhSieve.rough 11092009835083 12917 :=
  LargeQuotientSieve.combine to12953 row12959 rfl

set_option maxRecDepth 16000 in
private theorem row12967 :
    FinalSeventhSieve.rough 11092009835083 12967+47291901=FinalSeventhSieve.rough 11092009835083 12959 :=
  LargeQuotientSieve.row (p:=12967) (q:=855402933) (s:=29247) (rank:=43844577) (tiny:=1543) (pairs:=3448866)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 855402933 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12967 : FinalSeventhSieve.rough 11092009835083 12967+284348985=FinalSeventhSieve.rough 11092009835083 12917 :=
  LargeQuotientSieve.combine to12959 row12967 rfl

set_option maxRecDepth 16000 in
private theorem row12973 :
    FinalSeventhSieve.rough 11092009835083 12973+47264647=FinalSeventhSieve.rough 11092009835083 12967 :=
  LargeQuotientSieve.row (p:=12973) (q:=855007310) (s:=29240) (rank:=43825398) (tiny:=1544) (pairs:=3440792)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 855007310 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12973 : FinalSeventhSieve.rough 11092009835083 12973+331613632=FinalSeventhSieve.rough 11092009835083 12917 :=
  LargeQuotientSieve.combine to12967 row12973 rfl

set_option maxRecDepth 16000 in
private theorem row12979 :
    FinalSeventhSieve.rough 11092009835083 12979+47237303=FinalSeventhSieve.rough 11092009835083 12973 :=
  LargeQuotientSieve.row (p:=12979) (q:=854612052) (s:=29233) (rank:=43806102) (tiny:=1545) (pairs:=3432745)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 854612052 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12979 : FinalSeventhSieve.rough 11092009835083 12979+378850935=FinalSeventhSieve.rough 11092009835083 12917 :=
  LargeQuotientSieve.combine to12973 row12979 rfl

set_option maxRecDepth 16000 in
private theorem row12983 :
    FinalSeventhSieve.rough 11092009835083 12983+47217440=FinalSeventhSieve.rough 11092009835083 12979 :=
  LargeQuotientSieve.row (p:=12983) (q:=854348751) (s:=29229) (rank:=43793346) (tiny:=1546) (pairs:=3425639)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 854348751 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12983 : FinalSeventhSieve.rough 11092009835083 12983+426068375=FinalSeventhSieve.rough 11092009835083 12917 :=
  LargeQuotientSieve.combine to12979 row12983 rfl

set_option maxRecDepth 16000 in
private theorem row13001 :
    FinalSeventhSieve.rough 11092009835083 13001+47145683=FinalSeventhSieve.rough 11092009835083 12983 :=
  LargeQuotientSieve.row (p:=13001) (q:=853165897) (s:=29209) (rank:=43735664) (tiny:=1547) (pairs:=3411565)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 853165897 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13001 : FinalSeventhSieve.rough 11092009835083 13001+473214058=FinalSeventhSieve.rough 11092009835083 12917 :=
  LargeQuotientSieve.combine to12983 row13001 rfl

set_option maxRecDepth 16000 in
private theorem row13003 :
    FinalSeventhSieve.rough 11092009835083 13003+47133351=FinalSeventhSieve.rough 11092009835083 13001 :=
  LargeQuotientSieve.row (p:=13003) (q:=853034671) (s:=29206) (rank:=43729313) (tiny:=1548) (pairs:=3405585)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 853034671 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13003 : FinalSeventhSieve.rough 11092009835083 13003+520347409=FinalSeventhSieve.rough 11092009835083 12917 :=
  LargeQuotientSieve.combine to13001 row13003 rfl

set_option maxRecDepth 16000 in
private theorem row13007 :
    FinalSeventhSieve.rough 11092009835083 13007+47113594=FinalSeventhSieve.rough 11092009835083 13003 :=
  LargeQuotientSieve.row (p:=13007) (q:=852772340) (s:=29202) (rank:=43716553) (tiny:=1549) (pairs:=3398589)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 852772340 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13007 : FinalSeventhSieve.rough 11092009835083 13007+567461003=FinalSeventhSieve.rough 11092009835083 12917 :=
  LargeQuotientSieve.combine to13003 row13007 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13007+567461003=FinalSeventhSieve.rough 11092009835083 12917 := to13007

end Tail11092009835083From12917To13007
