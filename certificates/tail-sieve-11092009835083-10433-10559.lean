import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 1278 through 1289. -/
open Finset
namespace Tail11092009835083From10433To10559

set_option maxRecDepth 16000 in
private theorem row10453 :
    FinalSeventhSieve.rough 11092009835083 10453+60868820=FinalSeventhSieve.rough 11092009835083 10433 :=
  LargeQuotientSieve.row (p:=10453) (q:=1061131716) (s:=32575) (rank:=53792937) (tiny:=1277) (pairs:=7077159)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1061131716 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row10457 :
    FinalSeventhSieve.rough 11092009835083 10457+60836584=FinalSeventhSieve.rough 11092009835083 10453 :=
  LargeQuotientSieve.row (p:=10457) (q:=1060725813) (s:=32568) (rank:=53773410) (tiny:=1278) (pairs:=7064451)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1060725813 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10457 : FinalSeventhSieve.rough 11092009835083 10457+121705404=FinalSeventhSieve.rough 11092009835083 10433 :=
  LargeQuotientSieve.combine row10453 row10457 rfl

set_option maxRecDepth 16000 in
private theorem row10459 :
    FinalSeventhSieve.rough 11092009835083 10459+60816344=FinalSeventhSieve.rough 11092009835083 10457 :=
  LargeQuotientSieve.row (p:=10459) (q:=1060522978) (s:=32565) (rank:=53763765) (tiny:=1279) (pairs:=7053857)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1060522978 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10459 : FinalSeventhSieve.rough 11092009835083 10459+182521748=FinalSeventhSieve.rough 11092009835083 10433 :=
  LargeQuotientSieve.combine to10457 row10459 rfl

set_option maxRecDepth 16000 in
private theorem row10463 :
    FinalSeventhSieve.rough 11092009835083 10463+60784124=FinalSeventhSieve.rough 11092009835083 10459 :=
  LargeQuotientSieve.row (p:=10463) (q:=1060117541) (s:=32559) (rank:=53744187) (tiny:=1280) (pairs:=7041216)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1060117541 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10463 : FinalSeventhSieve.rough 11092009835083 10463+243305872=FinalSeventhSieve.rough 11092009835083 10433 :=
  LargeQuotientSieve.combine to10459 row10463 rfl

set_option maxRecDepth 16000 in
private theorem row10477 :
    FinalSeventhSieve.rough 11092009835083 10477+60692707=FinalSeventhSieve.rough 11092009835083 10463 :=
  LargeQuotientSieve.row (p:=10477) (q:=1058700948) (s:=32537) (rank:=53676046) (tiny:=1281) (pairs:=7017941)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1058700948 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10477 : FinalSeventhSieve.rough 11092009835083 10477+303998579=FinalSeventhSieve.rough 11092009835083 10433 :=
  LargeQuotientSieve.combine to10463 row10477 rfl

set_option maxRecDepth 16000 in
private theorem row10487 :
    FinalSeventhSieve.rough 11092009835083 10487+60625171=FinalSeventhSieve.rough 11092009835083 10477 :=
  LargeQuotientSieve.row (p:=10487) (q:=1057691411) (s:=32522) (rank:=53627404) (tiny:=1282) (pairs:=6999048)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1057691411 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10487 : FinalSeventhSieve.rough 11092009835083 10487+364623750=FinalSeventhSieve.rough 11092009835083 10433 :=
  LargeQuotientSieve.combine to10477 row10487 rfl

set_option maxRecDepth 16000 in
private theorem row10499 :
    FinalSeventhSieve.rough 11092009835083 10499+60546014=FinalSeventhSieve.rough 11092009835083 10487 :=
  LargeQuotientSieve.row (p:=10499) (q:=1056482506) (s:=32503) (rank:=53569292) (tiny:=1283) (pairs:=6978004)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1056482506 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10499 : FinalSeventhSieve.rough 11092009835083 10499+425169764=FinalSeventhSieve.rough 11092009835083 10433 :=
  LargeQuotientSieve.combine to10487 row10499 rfl

set_option maxRecDepth 16000 in
private theorem row10501 :
    FinalSeventhSieve.rough 11092009835083 10501+60525860=FinalSeventhSieve.rough 11092009835083 10499 :=
  LargeQuotientSieve.row (p:=10501) (q:=1056281290) (s:=32500) (rank:=53559590) (tiny:=1284) (pairs:=6967553)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1056281290 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10501 : FinalSeventhSieve.rough 11092009835083 10501+485695624=FinalSeventhSieve.rough 11092009835083 10433 :=
  LargeQuotientSieve.combine to10499 row10501 rfl

set_option maxRecDepth 16000 in
private theorem row10513 :
    FinalSeventhSieve.rough 11092009835083 10513+60447064=FinalSeventhSieve.rough 11092009835083 10501 :=
  LargeQuotientSieve.row (p:=10513) (q:=1055075604) (s:=32481) (rank:=53501677) (tiny:=1285) (pairs:=6946671)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1055075604 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10513 : FinalSeventhSieve.rough 11092009835083 10513+546142688=FinalSeventhSieve.rough 11092009835083 10433 :=
  LargeQuotientSieve.combine to10501 row10513 rfl

set_option maxRecDepth 16000 in
private theorem row10529 :
    FinalSeventhSieve.rough 11092009835083 10529+60345127=FinalSeventhSieve.rough 11092009835083 10513 :=
  LargeQuotientSieve.row (p:=10529) (q:=1053472298) (s:=32457) (rank:=53424710) (tiny:=1286) (pairs:=6921702)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1053472298 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10529 : FinalSeventhSieve.rough 11092009835083 10529+606487815=FinalSeventhSieve.rough 11092009835083 10433 :=
  LargeQuotientSieve.combine to10513 row10529 rfl

set_option maxRecDepth 16000 in
private theorem row10531 :
    FinalSeventhSieve.rough 11092009835083 10531+60325134=FinalSeventhSieve.rough 11092009835083 10529 :=
  LargeQuotientSieve.row (p:=10531) (q:=1053272228) (s:=32454) (rank:=53415113) (tiny:=1287) (pairs:=6911307)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1053272228 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10531 : FinalSeventhSieve.rough 11092009835083 10531+666812949=FinalSeventhSieve.rough 11092009835083 10433 :=
  LargeQuotientSieve.combine to10529 row10531 rfl

set_option maxRecDepth 16000 in
private theorem row10559 :
    FinalSeventhSieve.rough 11092009835083 10559+60153322=FinalSeventhSieve.rough 11092009835083 10531 :=
  LargeQuotientSieve.row (p:=10559) (q:=1050479196) (s:=32411) (rank:=53280483) (tiny:=1288) (pairs:=6874126)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1050479196 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10559 : FinalSeventhSieve.rough 11092009835083 10559+726966271=FinalSeventhSieve.rough 11092009835083 10433 :=
  LargeQuotientSieve.combine to10531 row10559 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10559+726966271=FinalSeventhSieve.rough 11092009835083 10433 := to10559

end Tail11092009835083From10433To10559
