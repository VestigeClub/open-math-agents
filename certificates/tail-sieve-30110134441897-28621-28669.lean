import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 3117 through 3124. -/
open Finset
namespace Tail30110134441897From28621To28669

set_option maxRecDepth 16000 in
private theorem row28627 :
    FinalSeventhSieve.rough 30110134441897 28627+53481223=FinalSeventhSieve.rough 30110134441897 28621 :=
  LargeQuotientSieve.row (p:=28627) (q:=1051808937) (s:=32431) (rank:=53344534) (tiny:=3116) (pairs:=139804)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1051808937 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row28631 :
    FinalSeventhSieve.rough 30110134441897 28631+53473182=FinalSeventhSieve.rough 30110134441897 28627 :=
  LargeQuotientSieve.row (p:=28631) (q:=1051661990) (s:=32429) (rank:=53337455) (tiny:=3117) (pairs:=138843)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1051661990 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28631 : FinalSeventhSieve.rough 30110134441897 28631+106954405=FinalSeventhSieve.rough 30110134441897 28621 :=
  LargeQuotientSieve.combine row28627 row28631 rfl

set_option maxRecDepth 16000 in
private theorem row28643 :
    FinalSeventhSieve.rough 30110134441897 28643+53450657=FinalSeventhSieve.rough 30110134441897 28631 :=
  LargeQuotientSieve.row (p:=28643) (q:=1051221395) (s:=32422) (rank:=53316203) (tiny:=3118) (pairs:=137571)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1051221395 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28643 : FinalSeventhSieve.rough 30110134441897 28643+160405062=FinalSeventhSieve.rough 30110134441897 28621 :=
  LargeQuotientSieve.combine to28631 row28643 rfl

set_option maxRecDepth 16000 in
private theorem row28649 :
    FinalSeventhSieve.rough 30110134441897 28649+53439016=FinalSeventhSieve.rough 30110134441897 28643 :=
  LargeQuotientSieve.row (p:=28649) (q:=1051001237) (s:=32419) (rank:=53305581) (tiny:=3119) (pairs:=136553)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1051001237 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28649 : FinalSeventhSieve.rough 30110134441897 28649+213844078=FinalSeventhSieve.rough 30110134441897 28621 :=
  LargeQuotientSieve.combine to28643 row28649 rfl

set_option maxRecDepth 16000 in
private theorem row28657 :
    FinalSeventhSieve.rough 30110134441897 28657+53423783=FinalSeventhSieve.rough 30110134441897 28649 :=
  LargeQuotientSieve.row (p:=28657) (q:=1050707835) (s:=32414) (rank:=53291470) (tiny:=3120) (pairs:=135432)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1050707835 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28657 : FinalSeventhSieve.rough 30110134441897 28657+267267861=FinalSeventhSieve.rough 30110134441897 28621 :=
  LargeQuotientSieve.combine to28649 row28657 rfl

set_option maxRecDepth 16000 in
private theorem row28661 :
    FinalSeventhSieve.rough 30110134441897 28661+53415765=FinalSeventhSieve.rough 30110134441897 28657 :=
  LargeQuotientSieve.row (p:=28661) (q:=1050561196) (s:=32412) (rank:=53284376) (tiny:=3121) (pairs:=134509)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1050561196 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28661 : FinalSeventhSieve.rough 30110134441897 28661+320683626=FinalSeventhSieve.rough 30110134441897 28621 :=
  LargeQuotientSieve.combine to28657 row28661 rfl

set_option maxRecDepth 16000 in
private theorem row28663 :
    FinalSeventhSieve.rough 30110134441897 28663+53411421=FinalSeventhSieve.rough 30110134441897 28661 :=
  LargeQuotientSieve.row (p:=28663) (q:=1050487891) (s:=32411) (rank:=53280889) (tiny:=3122) (pairs:=133653)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1050487891 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28663 : FinalSeventhSieve.rough 30110134441897 28663+374095047=FinalSeventhSieve.rough 30110134441897 28621 :=
  LargeQuotientSieve.combine to28661 row28663 rfl

set_option maxRecDepth 16000 in
private theorem row28669 :
    FinalSeventhSieve.rough 30110134441897 28669+53399746=FinalSeventhSieve.rough 30110134441897 28663 :=
  LargeQuotientSieve.row (p:=28669) (q:=1050268040) (s:=32407) (rank:=53270214) (tiny:=3123) (pairs:=132654)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1050268040 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28669 : FinalSeventhSieve.rough 30110134441897 28669+427494793=FinalSeventhSieve.rough 30110134441897 28621 :=
  LargeQuotientSieve.combine to28663 row28669 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 28669+427494793=FinalSeventhSieve.rough 30110134441897 28621 := to28669

end Tail30110134441897From28621To28669
