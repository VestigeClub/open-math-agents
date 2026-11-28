import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1075000000-1100000000»

/-! Exact changes for sieve primes 3018 through 3029. -/
open Finset
namespace Tail30110134441897From27653To27763

set_option maxRecDepth 16000 in
private theorem row27673 :
    FinalSeventhSieve.rough 30110134441897 27673+55370768=FinalSeventhSieve.rough 30110134441897 27653 :=
  LargeQuotientSieve.row (p:=27673) (q:=1088069036) (s:=32985) (rank:=55089130) (tiny:=3017) (pairs:=284654)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1088069036 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row27689 :
    FinalSeventhSieve.rough 30110134441897 27689+55338404=FinalSeventhSieve.rough 30110134441897 27673 :=
  LargeQuotientSieve.row (p:=27689) (q:=1087440299) (s:=32976) (rank:=55058916) (tiny:=3018) (pairs:=282505)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1087440299 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27689 : FinalSeventhSieve.rough 30110134441897 27689+110709172=FinalSeventhSieve.rough 30110134441897 27653 :=
  LargeQuotientSieve.combine row27673 row27689 rfl

set_option maxRecDepth 16000 in
private theorem row27691 :
    FinalSeventhSieve.rough 30110134441897 27691+55333391=FinalSeventhSieve.rough 30110134441897 27689 :=
  LargeQuotientSieve.row (p:=27691) (q:=1087361758) (s:=32975) (rank:=55055133) (tiny:=3019) (pairs:=281276)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1087361758 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27691 : FinalSeventhSieve.rough 30110134441897 27691+166042563=FinalSeventhSieve.rough 30110134441897 27653 :=
  LargeQuotientSieve.combine to27689 row27691 rfl

set_option maxRecDepth 16000 in
private theorem row27697 :
    FinalSeventhSieve.rough 30110134441897 27697+55320437=FinalSeventhSieve.rough 30110134441897 27691 :=
  LargeQuotientSieve.row (p:=27697) (q:=1087126202) (s:=32971) (rank:=55043672) (tiny:=3020) (pairs:=279784)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1087126202 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27697 : FinalSeventhSieve.rough 30110134441897 27697+221363000=FinalSeventhSieve.rough 30110134441897 27653 :=
  LargeQuotientSieve.combine to27691 row27697 rfl

set_option maxRecDepth 16000 in
private theorem row27701 :
    FinalSeventhSieve.rough 30110134441897 27701+55311447=FinalSeventhSieve.rough 30110134441897 27697 :=
  LargeQuotientSieve.row (p:=27701) (q:=1086969222) (s:=32969) (rank:=55036063) (tiny:=3021) (pairs:=278404)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1086969222 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27701 : FinalSeventhSieve.rough 30110134441897 27701+276674447=FinalSeventhSieve.rough 30110134441897 27653 :=
  LargeQuotientSieve.combine to27697 row27701 rfl

set_option maxRecDepth 16000 in
private theorem row27733 :
    FinalSeventhSieve.rough 30110134441897 27733+55248011=FinalSeventhSieve.rough 30110134441897 27701 :=
  LargeQuotientSieve.row (p:=27733) (q:=1085715012) (s:=32950) (rank:=54975760) (tiny:=3022) (pairs:=275272)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1085715012 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27733 : FinalSeventhSieve.rough 30110134441897 27733+331922458=FinalSeventhSieve.rough 30110134441897 27653 :=
  LargeQuotientSieve.combine to27701 row27733 rfl

set_option maxRecDepth 16000 in
private theorem row27737 :
    FinalSeventhSieve.rough 30110134441897 27737+55239040=FinalSeventhSieve.rough 30110134441897 27733 :=
  LargeQuotientSieve.row (p:=27737) (q:=1085558439) (s:=32947) (rank:=54968153) (tiny:=3023) (pairs:=273909)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1085558439 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27737 : FinalSeventhSieve.rough 30110134441897 27737+387161498=FinalSeventhSieve.rough 30110134441897 27653 :=
  LargeQuotientSieve.combine to27733 row27737 rfl

set_option maxRecDepth 16000 in
private theorem row27739 :
    FinalSeventhSieve.rough 30110134441897 27739+55234124=FinalSeventhSieve.rough 30110134441897 27737 :=
  LargeQuotientSieve.row (p:=27739) (q:=1085480170) (s:=32946) (rank:=54964457) (tiny:=3024) (pairs:=272690)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1085480170 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27739 : FinalSeventhSieve.rough 30110134441897 27739+442395622=FinalSeventhSieve.rough 30110134441897 27653 :=
  LargeQuotientSieve.combine to27737 row27739 rfl

set_option maxRecDepth 16000 in
private theorem row27743 :
    FinalSeventhSieve.rough 30110134441897 27743+55225261=FinalSeventhSieve.rough 30110134441897 27739 :=
  LargeQuotientSieve.row (p:=27743) (q:=1085323665) (s:=32944) (rank:=54956943) (tiny:=3025) (pairs:=271342)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1085323665 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27743 : FinalSeventhSieve.rough 30110134441897 27743+497620883=FinalSeventhSieve.rough 30110134441897 27653 :=
  LargeQuotientSieve.combine to27739 row27743 rfl

set_option maxRecDepth 16000 in
private theorem row27749 :
    FinalSeventhSieve.rough 30110134441897 27749+55212597=FinalSeventhSieve.rough 30110134441897 27743 :=
  LargeQuotientSieve.row (p:=27749) (q:=1085088992) (s:=32940) (rank:=54945760) (tiny:=3026) (pairs:=269862)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1085088992 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27749 : FinalSeventhSieve.rough 30110134441897 27749+552833480=FinalSeventhSieve.rough 30110134441897 27653 :=
  LargeQuotientSieve.combine to27743 row27749 rfl

set_option maxRecDepth 16000 in
private theorem row27751 :
    FinalSeventhSieve.rough 30110134441897 27751+55207597=FinalSeventhSieve.rough 30110134441897 27749 :=
  LargeQuotientSieve.row (p:=27751) (q:=1085010790) (s:=32939) (rank:=54941970) (tiny:=3027) (pairs:=268653)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1085010790 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27751 : FinalSeventhSieve.rough 30110134441897 27751+608041077=FinalSeventhSieve.rough 30110134441897 27653 :=
  LargeQuotientSieve.combine to27749 row27751 rfl

set_option maxRecDepth 16000 in
private theorem row27763 :
    FinalSeventhSieve.rough 30110134441897 27763+55183117=FinalSeventhSieve.rough 30110134441897 27751 :=
  LargeQuotientSieve.row (p:=27763) (q:=1084541816) (s:=32932) (rank:=54919310) (tiny:=3028) (pairs:=266834)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1084541816 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27763 : FinalSeventhSieve.rough 30110134441897 27763+663224194=FinalSeventhSieve.rough 30110134441897 27653 :=
  LargeQuotientSieve.combine to27751 row27763 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 27763+663224194=FinalSeventhSieve.rough 30110134441897 27653 := to27763

end Tail30110134441897From27653To27763
