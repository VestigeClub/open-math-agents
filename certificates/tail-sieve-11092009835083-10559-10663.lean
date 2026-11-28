import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1025000000-1050000000»

/-! Exact changes for sieve primes 1290 through 1301. -/
open Finset
namespace Tail11092009835083From10559To10663

set_option maxRecDepth 16000 in
private theorem row10567 :
    FinalSeventhSieve.rough 11092009835083 10567+60098482=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.row (p:=10567) (q:=1049683906) (s:=32398) (rank:=53242158) (tiny:=1289) (pairs:=6857612)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1049683906 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row10589 :
    FinalSeventhSieve.rough 11092009835083 10589+59962888=FinalSeventhSieve.rough 11092009835083 10567 :=
  LargeQuotientSieve.row (p:=10589) (q:=1047503053) (s:=32365) (rank:=53137366) (tiny:=1290) (pairs:=6826811)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1047503053 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10589 : FinalSeventhSieve.rough 11092009835083 10589+120061370=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine row10567 row10589 rfl

set_option maxRecDepth 16000 in
private theorem row10597 :
    FinalSeventhSieve.rough 11092009835083 10597+59908511=FinalSeventhSieve.rough 11092009835083 10589 :=
  LargeQuotientSieve.row (p:=10597) (q:=1046712261) (s:=32352) (rank:=53099399) (tiny:=1291) (pairs:=6810402)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1046712261 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10597 : FinalSeventhSieve.rough 11092009835083 10597+179969881=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine to10589 row10597 rfl

set_option maxRecDepth 16000 in
private theorem row10601 :
    FinalSeventhSieve.rough 11092009835083 10601+59877250=FinalSeventhSieve.rough 11092009835083 10597 :=
  LargeQuotientSieve.row (p:=10601) (q:=1046317312) (s:=32346) (rank:=53080412) (tiny:=1292) (pairs:=6798129)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1046317312 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10601 : FinalSeventhSieve.rough 11092009835083 10601+239847131=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine to10597 row10601 rfl

set_option maxRecDepth 16000 in
private theorem row10607 :
    FinalSeventhSieve.rough 11092009835083 10607+59834442=FinalSeventhSieve.rough 11092009835083 10601 :=
  LargeQuotientSieve.row (p:=10607) (q:=1045725448) (s:=32337) (rank:=53051846) (tiny:=1293) (pairs:=6783888)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1045725448 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10607 : FinalSeventhSieve.rough 11092009835083 10607+299681573=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine to10601 row10607 rfl

set_option maxRecDepth 16000 in
private theorem row10613 :
    FinalSeventhSieve.rough 11092009835083 10613+59791688=FinalSeventhSieve.rough 11092009835083 10607 :=
  LargeQuotientSieve.row (p:=10613) (q:=1045134253) (s:=32328) (rank:=53023434) (tiny:=1294) (pairs:=6769547)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1045134253 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10613 : FinalSeventhSieve.rough 11092009835083 10613+359473261=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine to10607 row10613 rfl

set_option maxRecDepth 16000 in
private theorem row10627 :
    FinalSeventhSieve.rough 11092009835083 10627+59703172=FinalSeventhSieve.rough 11092009835083 10613 :=
  LargeQuotientSieve.row (p:=10627) (q:=1043757394) (s:=32307) (rank:=52957278) (tiny:=1295) (pairs:=6747188)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1043757394 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10627 : FinalSeventhSieve.rough 11092009835083 10627+419176433=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine to10613 row10627 rfl

set_option maxRecDepth 16000 in
private theorem row10631 :
    FinalSeventhSieve.rough 11092009835083 10631+59671991=FinalSeventhSieve.rough 11092009835083 10627 :=
  LargeQuotientSieve.row (p:=10631) (q:=1043364672) (s:=32301) (rank:=52938279) (tiny:=1296) (pairs:=6735007)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1043364672 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10631 : FinalSeventhSieve.rough 11092009835083 10631+478848424=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine to10627 row10631 rfl

set_option maxRecDepth 16000 in
private theorem row10639 :
    FinalSeventhSieve.rough 11092009835083 10639+59618110=FinalSeventhSieve.rough 11092009835083 10631 :=
  LargeQuotientSieve.row (p:=10639) (q:=1042580114) (s:=32289) (rank:=52900588) (tiny:=1297) (pairs:=6718818)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1042580114 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10639 : FinalSeventhSieve.rough 11092009835083 10639+538466534=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine to10631 row10639 rfl

set_option maxRecDepth 16000 in
private theorem row10651 :
    FinalSeventhSieve.rough 11092009835083 10651+59541247=FinalSeventhSieve.rough 11092009835083 10639 :=
  LargeQuotientSieve.row (p:=10651) (q:=1041405486) (s:=32270) (rank:=52843808) (tiny:=1298) (pairs:=6698736)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1041405486 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10651 : FinalSeventhSieve.rough 11092009835083 10651+598007781=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine to10639 row10651 rfl

set_option maxRecDepth 16000 in
private theorem row10657 :
    FinalSeventhSieve.rough 11092009835083 10657+59498990=FinalSeventhSieve.rough 11092009835083 10651 :=
  LargeQuotientSieve.row (p:=10657) (q:=1040819164) (s:=32261) (rank:=52815644) (tiny:=1299) (pairs:=6684644)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1040819164 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10657 : FinalSeventhSieve.rough 11092009835083 10657+657506771=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine to10651 row10657 rfl

set_option maxRecDepth 16000 in
private theorem row10663 :
    FinalSeventhSieve.rough 11092009835083 10663+59456734=FinalSeventhSieve.rough 11092009835083 10657 :=
  LargeQuotientSieve.row (p:=10663) (q:=1040233502) (s:=32252) (rank:=52787484) (tiny:=1300) (pairs:=6670549)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1040233502 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10663 : FinalSeventhSieve.rough 11092009835083 10663+716963505=FinalSeventhSieve.rough 11092009835083 10559 :=
  LargeQuotientSieve.combine to10657 row10663 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10663+716963505=FinalSeventhSieve.rough 11092009835083 10559 := to10663

end Tail11092009835083From10559To10663
