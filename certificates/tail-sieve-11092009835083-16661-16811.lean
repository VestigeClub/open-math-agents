import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-650000000-675000000»

/-! Exact changes for sieve primes 1929 through 1940. -/
open Finset
namespace Tail11092009835083From16661To16811

set_option maxRecDepth 16000 in
private theorem row16673 :
    FinalSeventhSieve.rough 11092009835083 16673+35494523=FinalSeventhSieve.rough 11092009835083 16661 :=
  LargeQuotientSieve.row (p:=16673) (q:=665267788) (s:=25792) (rank:=34545644) (tiny:=1928) (pairs:=950806)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 665267788 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row16691 :
    FinalSeventhSieve.rough 11092009835083 16691+35453967=FinalSeventhSieve.rough 11092009835083 16673 :=
  LargeQuotientSieve.row (p:=16691) (q:=664550346) (s:=25778) (rank:=34510344) (tiny:=1929) (pairs:=945551)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 664550346 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16691 : FinalSeventhSieve.rough 11092009835083 16691+70948490=FinalSeventhSieve.rough 11092009835083 16661 :=
  LargeQuotientSieve.combine row16673 row16691 rfl

set_option maxRecDepth 16000 in
private theorem row16693 :
    FinalSeventhSieve.rough 11092009835083 16693+35447450=FinalSeventhSieve.rough 11092009835083 16691 :=
  LargeQuotientSieve.row (p:=16693) (q:=664470726) (s:=25777) (rank:=34506418) (tiny:=1930) (pairs:=942961)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 664470726 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16693 : FinalSeventhSieve.rough 11092009835083 16693+106395940=FinalSeventhSieve.rough 11092009835083 16661 :=
  LargeQuotientSieve.combine to16691 row16693 rfl

set_option maxRecDepth 16000 in
private theorem row16699 :
    FinalSeventhSieve.rough 11092009835083 16699+35432499=FinalSeventhSieve.rough 11092009835083 16693 :=
  LargeQuotientSieve.row (p:=16699) (q:=664231980) (s:=25772) (rank:=34494714) (tiny:=1931) (pairs:=939715)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 664231980 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16699 : FinalSeventhSieve.rough 11092009835083 16699+141828439=FinalSeventhSieve.rough 11092009835083 16661 :=
  LargeQuotientSieve.combine to16693 row16699 rfl

set_option maxRecDepth 16000 in
private theorem row16703 :
    FinalSeventhSieve.rough 11092009835083 16703+35421774=FinalSeventhSieve.rough 11092009835083 16699 :=
  LargeQuotientSieve.row (p:=16703) (q:=664072911) (s:=25769) (rank:=34486909) (tiny:=1932) (pairs:=936796)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 664072911 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16703 : FinalSeventhSieve.rough 11092009835083 16703+177250213=FinalSeventhSieve.rough 11092009835083 16661 :=
  LargeQuotientSieve.combine to16699 row16703 rfl

set_option maxRecDepth 16000 in
private theorem row16729 :
    FinalSeventhSieve.rough 11092009835083 16729+35364289=FinalSeventhSieve.rough 11092009835083 16703 :=
  LargeQuotientSieve.row (p:=16729) (q:=663040817) (s:=25749) (rank:=34435984) (tiny:=1933) (pairs:=930237)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 663040817 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16729 : FinalSeventhSieve.rough 11092009835083 16729+212614502=FinalSeventhSieve.rough 11092009835083 16661 :=
  LargeQuotientSieve.combine to16703 row16729 rfl

set_option maxRecDepth 16000 in
private theorem row16741 :
    FinalSeventhSieve.rough 11092009835083 16741+35336777=FinalSeventhSieve.rough 11092009835083 16729 :=
  LargeQuotientSieve.row (p:=16741) (q:=662565547) (s:=25740) (rank:=34412675) (tiny:=1934) (pairs:=926035)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 662565547 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16741 : FinalSeventhSieve.rough 11092009835083 16741+247951279=FinalSeventhSieve.rough 11092009835083 16661 :=
  LargeQuotientSieve.combine to16729 row16741 rfl

set_option maxRecDepth 16000 in
private theorem row16747 :
    FinalSeventhSieve.rough 11092009835083 16747+35321856=FinalSeventhSieve.rough 11092009835083 16741 :=
  LargeQuotientSieve.row (p:=16747) (q:=662328168) (s:=25735) (rank:=34400947) (tiny:=1935) (pairs:=922843)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 662328168 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16747 : FinalSeventhSieve.rough 11092009835083 16747+283273135=FinalSeventhSieve.rough 11092009835083 16661 :=
  LargeQuotientSieve.combine to16741 row16747 rfl

set_option maxRecDepth 16000 in
private theorem row16759 :
    FinalSeventhSieve.rough 11092009835083 16759+35294322=FinalSeventhSieve.rough 11092009835083 16747 :=
  LargeQuotientSieve.row (p:=16759) (q:=661853919) (s:=25726) (rank:=34377580) (tiny:=1936) (pairs:=918677)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 661853919 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16759 : FinalSeventhSieve.rough 11092009835083 16759+318567457=FinalSeventhSieve.rough 11092009835083 16661 :=
  LargeQuotientSieve.combine to16747 row16759 rfl

set_option maxRecDepth 16000 in
private theorem row16763 :
    FinalSeventhSieve.rough 11092009835083 16763+35283739=FinalSeventhSieve.rough 11092009835083 16759 :=
  LargeQuotientSieve.row (p:=16763) (q:=661695987) (s:=25723) (rank:=34369884) (tiny:=1937) (pairs:=915791)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 661695987 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16763 : FinalSeventhSieve.rough 11092009835083 16763+353851196=FinalSeventhSieve.rough 11092009835083 16661 :=
  LargeQuotientSieve.combine to16759 row16763 rfl

set_option maxRecDepth 16000 in
private theorem row16787 :
    FinalSeventhSieve.rough 11092009835083 16787+35230906=FinalSeventhSieve.rough 11092009835083 16763 :=
  LargeQuotientSieve.row (p:=16787) (q:=660749975) (s:=25705) (rank:=34323146) (tiny:=1938) (pairs:=909697)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 660749975 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16787 : FinalSeventhSieve.rough 11092009835083 16787+389082102=FinalSeventhSieve.rough 11092009835083 16661 :=
  LargeQuotientSieve.combine to16763 row16787 rfl

set_option maxRecDepth 16000 in
private theorem row16811 :
    FinalSeventhSieve.rough 11092009835083 16811+35178386=FinalSeventhSieve.rough 11092009835083 16787 :=
  LargeQuotientSieve.row (p:=16811) (q:=659806664) (s:=25686) (rank:=34276664) (tiny:=1939) (pairs:=903660)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 659806664 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16811 : FinalSeventhSieve.rough 11092009835083 16811+424260488=FinalSeventhSieve.rough 11092009835083 16661 :=
  LargeQuotientSieve.combine to16787 row16811 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 16811+424260488=FinalSeventhSieve.rough 11092009835083 16661 := to16811

end Tail11092009835083From16661To16811
