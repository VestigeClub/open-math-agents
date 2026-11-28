import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-800000000-825000000»

/-! Exact changes for sieve primes 1618 through 1629. -/
open Finset
namespace Tail11092009835083From13687To13763

set_option maxRecDepth 16000 in
private theorem row13691 :
    FinalSeventhSieve.rough 11092009835083 13691+44411251=FinalSeventhSieve.rough 11092009835083 13687 :=
  LargeQuotientSieve.row (p:=13691) (q:=810167981) (s:=28463) (rank:=41642371) (tiny:=1617) (pairs:=2770496)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 810167981 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row13693 :
    FinalSeventhSieve.rough 11092009835083 13693+44400220=FinalSeventhSieve.rough 11092009835083 13691 :=
  LargeQuotientSieve.row (p:=13693) (q:=810049648) (s:=28461) (rank:=41636511) (tiny:=1618) (pairs:=2765326)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 810049648 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13693 : FinalSeventhSieve.rough 11092009835083 13693+88811471=FinalSeventhSieve.rough 11092009835083 13687 :=
  LargeQuotientSieve.combine row13691 row13693 rfl

set_option maxRecDepth 16000 in
private theorem row13697 :
    FinalSeventhSieve.rough 11092009835083 13697+44382742=FinalSeventhSieve.rough 11092009835083 13693 :=
  LargeQuotientSieve.row (p:=13697) (q:=809813085) (s:=28457) (rank:=41625055) (tiny:=1619) (pairs:=2759305)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 809813085 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13697 : FinalSeventhSieve.rough 11092009835083 13697+133194213=FinalSeventhSieve.rough 11092009835083 13687 :=
  LargeQuotientSieve.combine to13693 row13697 rfl

set_option maxRecDepth 16000 in
private theorem row13709 :
    FinalSeventhSieve.rough 11092009835083 13709+44338867=FinalSeventhSieve.rough 11092009835083 13697 :=
  LargeQuotientSieve.row (p:=13709) (q:=809104226) (s:=28444) (rank:=41590474) (tiny:=1620) (pairs:=2750012)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 809104226 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13709 : FinalSeventhSieve.rough 11092009835083 13709+177533080=FinalSeventhSieve.rough 11092009835083 13687 :=
  LargeQuotientSieve.combine to13697 row13709 rfl

set_option maxRecDepth 16000 in
private theorem row13711 :
    FinalSeventhSieve.rough 11092009835083 13711+44327914=FinalSeventhSieve.rough 11092009835083 13709 :=
  LargeQuotientSieve.row (p:=13711) (q:=808986203) (s:=28442) (rank:=41584697) (tiny:=1621) (pairs:=2744837)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 808986203 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13711 : FinalSeventhSieve.rough 11092009835083 13711+221860994=FinalSeventhSieve.rough 11092009835083 13687 :=
  LargeQuotientSieve.combine to13709 row13711 rfl

set_option maxRecDepth 16000 in
private theorem row13721 :
    FinalSeventhSieve.rough 11092009835083 13721+44290778=FinalSeventhSieve.rough 11092009835083 13711 :=
  LargeQuotientSieve.row (p:=13721) (q:=808396606) (s:=28432) (rank:=41555943) (tiny:=1622) (pairs:=2736456)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 808396606 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13721 : FinalSeventhSieve.rough 11092009835083 13721+266151772=FinalSeventhSieve.rough 11092009835083 13687 :=
  LargeQuotientSieve.combine to13711 row13721 rfl

set_option maxRecDepth 16000 in
private theorem row13723 :
    FinalSeventhSieve.rough 11092009835083 13723+44279854=FinalSeventhSieve.rough 11092009835083 13721 :=
  LargeQuotientSieve.row (p:=13723) (q:=808278789) (s:=28430) (rank:=41550167) (tiny:=1623) (pairs:=2731309)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 808278789 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13723 : FinalSeventhSieve.rough 11092009835083 13723+310431626=FinalSeventhSieve.rough 11092009835083 13687 :=
  LargeQuotientSieve.combine to13721 row13723 rfl

set_option maxRecDepth 16000 in
private theorem row13729 :
    FinalSeventhSieve.rough 11092009835083 13729+44255847=FinalSeventhSieve.rough 11092009835083 13723 :=
  LargeQuotientSieve.row (p:=13729) (q:=807925547) (s:=28424) (rank:=41532949) (tiny:=1624) (pairs:=2724521)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 807925547 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13729 : FinalSeventhSieve.rough 11092009835083 13729+354687473=FinalSeventhSieve.rough 11092009835083 13687 :=
  LargeQuotientSieve.combine to13723 row13729 rfl

set_option maxRecDepth 16000 in
private theorem row13751 :
    FinalSeventhSieve.rough 11092009835083 13751+44179720=FinalSeventhSieve.rough 11092009835083 13729 :=
  LargeQuotientSieve.row (p:=13751) (q:=806632960) (s:=28401) (rank:=41470025) (tiny:=1625) (pairs:=2711319)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 806632960 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13751 : FinalSeventhSieve.rough 11092009835083 13751+398867193=FinalSeventhSieve.rough 11092009835083 13687 :=
  LargeQuotientSieve.combine to13729 row13751 rfl

set_option maxRecDepth 16000 in
private theorem row13757 :
    FinalSeventhSieve.rough 11092009835083 13757+44155712=FinalSeventhSieve.rough 11092009835083 13751 :=
  LargeQuotientSieve.row (p:=13757) (q:=806281153) (s:=28395) (rank:=41452754) (tiny:=1626) (pairs:=2704583)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 806281153 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13757 : FinalSeventhSieve.rough 11092009835083 13757+443022905=FinalSeventhSieve.rough 11092009835083 13687 :=
  LargeQuotientSieve.combine to13751 row13757 rfl

set_option maxRecDepth 16000 in
private theorem row13759 :
    FinalSeventhSieve.rough 11092009835083 13759+44144920=FinalSeventhSieve.rough 11092009835083 13757 :=
  LargeQuotientSieve.row (p:=13759) (q:=806163953) (s:=28393) (rank:=41447075) (tiny:=1627) (pairs:=2699471)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 806163953 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13759 : FinalSeventhSieve.rough 11092009835083 13759+487167825=FinalSeventhSieve.rough 11092009835083 13687 :=
  LargeQuotientSieve.combine to13757 row13759 rfl

set_option maxRecDepth 16000 in
private theorem row13763 :
    FinalSeventhSieve.rough 11092009835083 13763+44127552=FinalSeventhSieve.rough 11092009835083 13759 :=
  LargeQuotientSieve.row (p:=13763) (q:=805929654) (s:=28388) (rank:=41435579) (tiny:=1628) (pairs:=2693600)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 805929654 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13763 : FinalSeventhSieve.rough 11092009835083 13763+531295377=FinalSeventhSieve.rough 11092009835083 13687 :=
  LargeQuotientSieve.combine to13759 row13763 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13763+531295377=FinalSeventhSieve.rough 11092009835083 13687 := to13763

end Tail11092009835083From13687To13763
