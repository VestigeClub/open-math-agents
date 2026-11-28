import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-750000000-775000000»

/-! Exact changes for sieve primes 1715 through 1726. -/
open Finset
namespace Tail11092009835083From14633To14741

set_option maxRecDepth 16000 in
private theorem row14639 :
    FinalSeventhSieve.rough 11092009835083 14639+41124002=FinalSeventhSieve.rough 11092009835083 14633 :=
  LargeQuotientSieve.row (p:=14639) (q:=757702700) (s:=27526) (rank:=39080052) (tiny:=1714) (pairs:=2045663)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 757702700 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row14653 :
    FinalSeventhSieve.rough 11092009835083 14653+41080650=FinalSeventhSieve.rough 11092009835083 14639 :=
  LargeQuotientSieve.row (p:=14653) (q:=756978764) (s:=27513) (rank:=39044633) (tiny:=1715) (pairs:=2037731)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 756978764 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14653 : FinalSeventhSieve.rough 11092009835083 14653+82204652=FinalSeventhSieve.rough 11092009835083 14633 :=
  LargeQuotientSieve.combine row14639 row14653 rfl

set_option maxRecDepth 16000 in
private theorem row14657 :
    FinalSeventhSieve.rough 11092009835083 14657+41065761=FinalSeventhSieve.rough 11092009835083 14653 :=
  LargeQuotientSieve.row (p:=14657) (q:=756772179) (s:=27509) (rank:=39034580) (tiny:=1716) (pairs:=2032896)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 756772179 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14657 : FinalSeventhSieve.rough 11092009835083 14657+123270413=FinalSeventhSieve.rough 11092009835083 14633 :=
  LargeQuotientSieve.combine to14653 row14657 rfl

set_option maxRecDepth 16000 in
private theorem row14669 :
    FinalSeventhSieve.rough 11092009835083 14669+41028231=FinalSeventhSieve.rough 11092009835083 14657 :=
  LargeQuotientSieve.row (p:=14669) (q:=756153100) (s:=27498) (rank:=39004323) (tiny:=1717) (pairs:=2025624)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 756153100 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14669 : FinalSeventhSieve.rough 11092009835083 14669+164298644=FinalSeventhSieve.rough 11092009835083 14633 :=
  LargeQuotientSieve.combine to14657 row14669 rfl

set_option maxRecDepth 16000 in
private theorem row14683 :
    FinalSeventhSieve.rough 11092009835083 14683+40984868=FinalSeventhSieve.rough 11092009835083 14669 :=
  LargeQuotientSieve.row (p:=14683) (q:=755432121) (s:=27485) (rank:=38968862) (tiny:=1718) (pairs:=2017723)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 755432121 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14683 : FinalSeventhSieve.rough 11092009835083 14683+205283512=FinalSeventhSieve.rough 11092009835083 14633 :=
  LargeQuotientSieve.combine to14669 row14683 rfl

set_option maxRecDepth 16000 in
private theorem row14699 :
    FinalSeventhSieve.rough 11092009835083 14699+40936088=FinalSeventhSieve.rough 11092009835083 14683 :=
  LargeQuotientSieve.row (p:=14699) (q:=754609826) (s:=27470) (rank:=38928464) (tiny:=1719) (pairs:=2009342)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 754609826 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14699 : FinalSeventhSieve.rough 11092009835083 14699+246219600=FinalSeventhSieve.rough 11092009835083 14633 :=
  LargeQuotientSieve.combine to14683 row14699 rfl

set_option maxRecDepth 16000 in
private theorem row14713 :
    FinalSeventhSieve.rough 11092009835083 14713+40893162=FinalSeventhSieve.rough 11092009835083 14699 :=
  LargeQuotientSieve.row (p:=14713) (q:=753891785) (s:=27457) (rank:=38893338) (tiny:=1720) (pairs:=2001543)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 753891785 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14713 : FinalSeventhSieve.rough 11092009835083 14713+287112762=FinalSeventhSieve.rough 11092009835083 14633 :=
  LargeQuotientSieve.combine to14699 row14713 rfl

set_option maxRecDepth 16000 in
private theorem row14717 :
    FinalSeventhSieve.rough 11092009835083 14717+40878396=FinalSeventhSieve.rough 11092009835083 14713 :=
  LargeQuotientSieve.row (p:=14717) (q:=753686881) (s:=27453) (rank:=38883350) (tiny:=1721) (pairs:=1996766)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 753686881 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14717 : FinalSeventhSieve.rough 11092009835083 14717+327991158=FinalSeventhSieve.rough 11092009835083 14633 :=
  LargeQuotientSieve.combine to14713 row14717 rfl

set_option maxRecDepth 16000 in
private theorem row14723 :
    FinalSeventhSieve.rough 11092009835083 14723+40858179=FinalSeventhSieve.rough 11092009835083 14717 :=
  LargeQuotientSieve.row (p:=14723) (q:=753379734) (s:=27447) (rank:=38868443) (tiny:=1722) (pairs:=1991457)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 753379734 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14723 : FinalSeventhSieve.rough 11092009835083 14723+368849337=FinalSeventhSieve.rough 11092009835083 14633 :=
  LargeQuotientSieve.combine to14717 row14723 rfl

set_option maxRecDepth 16000 in
private theorem row14731 :
    FinalSeventhSieve.rough 11092009835083 14731+40832308=FinalSeventhSieve.rough 11092009835083 14723 :=
  LargeQuotientSieve.row (p:=14731) (q:=752970595) (s:=27440) (rank:=38848487) (tiny:=1723) (pairs:=1985543)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 752970595 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14731 : FinalSeventhSieve.rough 11092009835083 14731+409681645=FinalSeventhSieve.rough 11092009835083 14633 :=
  LargeQuotientSieve.combine to14723 row14731 rfl

set_option maxRecDepth 16000 in
private theorem row14737 :
    FinalSeventhSieve.rough 11092009835083 14737+40811992=FinalSeventhSieve.rough 11092009835083 14731 :=
  LargeQuotientSieve.row (p:=14737) (q:=752664031) (s:=27434) (rank:=38833526) (tiny:=1724) (pairs:=1980189)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 752664031 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14737 : FinalSeventhSieve.rough 11092009835083 14737+450493637=FinalSeventhSieve.rough 11092009835083 14633 :=
  LargeQuotientSieve.combine to14731 row14737 rfl

set_option maxRecDepth 16000 in
private theorem row14741 :
    FinalSeventhSieve.rough 11092009835083 14741+40797306=FinalSeventhSieve.rough 11092009835083 14737 :=
  LargeQuotientSieve.row (p:=14741) (q:=752459794) (s:=27431) (rank:=38823575) (tiny:=1725) (pairs:=1975455)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 752459794 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14741 : FinalSeventhSieve.rough 11092009835083 14741+491290943=FinalSeventhSieve.rough 11092009835083 14633 :=
  LargeQuotientSieve.combine to14737 row14741 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 14741+491290943=FinalSeventhSieve.rough 11092009835083 14633 := to14741

end Tail11092009835083From14633To14741
