import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1000000000-1025000000»

/-! Exact changes for sieve primes 3203 through 3214. -/
open Finset
namespace Tail30110134441897From29473To29611

set_option maxRecDepth 16000 in
private theorem row29483 :
    FinalSeventhSieve.rough 30110134441897 29483+51926581=FinalSeventhSieve.rough 30110134441897 29473 :=
  LargeQuotientSieve.row (p:=29483) (q:=1021271052) (s:=31957) (rank:=51873713) (tiny:=3202) (pairs:=56069)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1021271052 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row29501 :
    FinalSeventhSieve.rough 30110134441897 29501+51895653=FinalSeventhSieve.rough 30110134441897 29483 :=
  LargeQuotientSieve.row (p:=29501) (q:=1020647925) (s:=31947) (rank:=51843722) (tiny:=3203) (pairs:=55133)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1020647925 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29501 : FinalSeventhSieve.rough 30110134441897 29501+103822234=FinalSeventhSieve.rough 30110134441897 29473 :=
  LargeQuotientSieve.combine row29483 row29501 rfl

set_option maxRecDepth 16000 in
private theorem row29527 :
    FinalSeventhSieve.rough 30110134441897 29527+51851037=FinalSeventhSieve.rough 30110134441897 29501 :=
  LargeQuotientSieve.row (p:=29527) (q:=1019749193) (s:=31933) (rank:=51800253) (tiny:=3204) (pairs:=53987)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1019749193 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29527 : FinalSeventhSieve.rough 30110134441897 29527+155673271=FinalSeventhSieve.rough 30110134441897 29473 :=
  LargeQuotientSieve.combine to29501 row29527 rfl

set_option maxRecDepth 16000 in
private theorem row29531 :
    FinalSeventhSieve.rough 30110134441897 29531+51843721=FinalSeventhSieve.rough 30110134441897 29527 :=
  LargeQuotientSieve.row (p:=29531) (q:=1019611067) (s:=31931) (rank:=51793524) (tiny:=3205) (pairs:=53401)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1019611067 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29531 : FinalSeventhSieve.rough 30110134441897 29531+207516992=FinalSeventhSieve.rough 30110134441897 29473 :=
  LargeQuotientSieve.combine to29527 row29531 rfl

set_option maxRecDepth 16000 in
private theorem row29537 :
    FinalSeventhSieve.rough 30110134441897 29537+51833157=FinalSeventhSieve.rough 30110134441897 29531 :=
  LargeQuotientSieve.row (p:=29537) (q:=1019403949) (s:=31928) (rank:=51783590) (tiny:=3206) (pairs:=52772)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1019403949 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29537 : FinalSeventhSieve.rough 30110134441897 29537+259350149=FinalSeventhSieve.rough 30110134441897 29473 :=
  LargeQuotientSieve.combine to29531 row29537 rfl

set_option maxRecDepth 16000 in
private theorem row29567 :
    FinalSeventhSieve.rough 30110134441897 29567+51782185=FinalSeventhSieve.rough 30110134441897 29537 :=
  LargeQuotientSieve.row (p:=29567) (q:=1018369616) (s:=31911) (rank:=51733858) (tiny:=3207) (pairs:=51533)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1018369616 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29567 : FinalSeventhSieve.rough 30110134441897 29567+311132334=FinalSeventhSieve.rough 30110134441897 29473 :=
  LargeQuotientSieve.combine to29537 row29567 rfl

set_option maxRecDepth 16000 in
private theorem row29569 :
    FinalSeventhSieve.rough 30110134441897 29569+51778328=FinalSeventhSieve.rough 30110134441897 29567 :=
  LargeQuotientSieve.row (p:=29569) (q:=1018300735) (s:=31910) (rank:=51730518) (tiny:=3208) (pairs:=51017)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1018300735 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29569 : FinalSeventhSieve.rough 30110134441897 29569+362910662=FinalSeventhSieve.rough 30110134441897 29473 :=
  LargeQuotientSieve.combine to29567 row29569 rfl

set_option maxRecDepth 16000 in
private theorem row29573 :
    FinalSeventhSieve.rough 30110134441897 29573+51771150=FinalSeventhSieve.rough 30110134441897 29569 :=
  LargeQuotientSieve.row (p:=29573) (q:=1018163001) (s:=31908) (rank:=51723918) (tiny:=3209) (pairs:=50440)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1018163001 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29573 : FinalSeventhSieve.rough 30110134441897 29573+414681812=FinalSeventhSieve.rough 30110134441897 29473 :=
  LargeQuotientSieve.combine to29569 row29573 rfl

set_option maxRecDepth 16000 in
private theorem row29581 :
    FinalSeventhSieve.rough 30110134441897 29581+51757186=FinalSeventhSieve.rough 30110134441897 29573 :=
  LargeQuotientSieve.row (p:=29581) (q:=1017887645) (s:=31904) (rank:=51710618) (tiny:=3210) (pairs:=49777)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1017887645 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29581 : FinalSeventhSieve.rough 30110134441897 29581+466438998=FinalSeventhSieve.rough 30110134441897 29473 :=
  LargeQuotientSieve.combine to29573 row29581 rfl

set_option maxRecDepth 16000 in
private theorem row29587 :
    FinalSeventhSieve.rough 30110134441897 29587+51746616=FinalSeventhSieve.rough 30110134441897 29581 :=
  LargeQuotientSieve.row (p:=29587) (q:=1017681226) (s:=31901) (rank:=51700664) (tiny:=3211) (pairs:=49162)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1017681226 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29587 : FinalSeventhSieve.rough 30110134441897 29587+518185614=FinalSeventhSieve.rough 30110134441897 29473 :=
  LargeQuotientSieve.combine to29581 row29587 rfl

set_option maxRecDepth 16000 in
private theorem row29599 :
    FinalSeventhSieve.rough 30110134441897 29599+51725890=FinalSeventhSieve.rough 30110134441897 29587 :=
  LargeQuotientSieve.row (p:=29599) (q:=1017268638) (s:=31894) (rank:=51680679) (tiny:=3212) (pairs:=48422)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1017268638 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29599 : FinalSeventhSieve.rough 30110134441897 29599+569911504=FinalSeventhSieve.rough 30110134441897 29473 :=
  LargeQuotientSieve.combine to29587 row29599 rfl

set_option maxRecDepth 16000 in
private theorem row29611 :
    FinalSeventhSieve.rough 30110134441897 29611+51705301=FinalSeventhSieve.rough 30110134441897 29599 :=
  LargeQuotientSieve.row (p:=29611) (q:=1016856385) (s:=31888) (rank:=51660844) (tiny:=3213) (pairs:=47669)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1016856385 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29611 : FinalSeventhSieve.rough 30110134441897 29611+621616805=FinalSeventhSieve.rough 30110134441897 29473 :=
  LargeQuotientSieve.combine to29599 row29611 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 29611+621616805=FinalSeventhSieve.rough 30110134441897 29473 := to29611

end Tail30110134441897From29473To29611
