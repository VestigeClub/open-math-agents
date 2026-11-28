import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-625000000-650000000»

/-! Exact changes for sieve primes 2017 through 2028. -/
open Finset
namespace Tail11092009835083From17519To17657

set_option maxRecDepth 16000 in
private theorem row17539 :
    FinalSeventhSieve.rough 11092009835083 17539+33570307=FinalSeventhSieve.rough 11092009835083 17519 :=
  LargeQuotientSieve.row (p:=17539) (q:=632419740) (s:=25147) (rank:=32926679) (tiny:=2016) (pairs:=645643)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 632419740 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row17551 :
    FinalSeventhSieve.rough 11092009835083 17551+33545645=FinalSeventhSieve.rough 11092009835083 17539 :=
  LargeQuotientSieve.row (p:=17551) (q:=631987341) (s:=25139) (rank:=32905329) (tiny:=2017) (pairs:=642332)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 631987341 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17551 : FinalSeventhSieve.rough 11092009835083 17551+67115952=FinalSeventhSieve.rough 11092009835083 17519 :=
  LargeQuotientSieve.combine row17539 row17551 rfl

set_option maxRecDepth 16000 in
private theorem row17569 :
    FinalSeventhSieve.rough 11092009835083 17569+33509564=FinalSeventhSieve.rough 11092009835083 17551 :=
  LargeQuotientSieve.row (p:=17569) (q:=631339850) (s:=25126) (rank:=32873311) (tiny:=2018) (pairs:=638270)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 631339850 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17569 : FinalSeventhSieve.rough 11092009835083 17569+100625516=FinalSeventhSieve.rough 11092009835083 17519 :=
  LargeQuotientSieve.combine to17551 row17569 rfl

set_option maxRecDepth 16000 in
private theorem row17573 :
    FinalSeventhSieve.rough 11092009835083 17573+33500149=FinalSeventhSieve.rough 11092009835083 17569 :=
  LargeQuotientSieve.row (p:=17573) (q:=631196143) (s:=25123) (rank:=32866205) (tiny:=2019) (pairs:=635962)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 631196143 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17573 : FinalSeventhSieve.rough 11092009835083 17573+134125665=FinalSeventhSieve.rough 11092009835083 17519 :=
  LargeQuotientSieve.combine to17569 row17573 rfl

set_option maxRecDepth 16000 in
private theorem row17579 :
    FinalSeventhSieve.rough 11092009835083 17579+33487018=FinalSeventhSieve.rough 11092009835083 17573 :=
  LargeQuotientSieve.row (p:=17579) (q:=630980706) (s:=25119) (rank:=32855603) (tiny:=2020) (pairs:=633434)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 630980706 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17579 : FinalSeventhSieve.rough 11092009835083 17579+167612683=FinalSeventhSieve.rough 11092009835083 17519 :=
  LargeQuotientSieve.combine to17573 row17579 rfl

set_option maxRecDepth 16000 in
private theorem row17581 :
    FinalSeventhSieve.rough 11092009835083 17581+33481414=FinalSeventhSieve.rough 11092009835083 17579 :=
  LargeQuotientSieve.row (p:=17581) (q:=630908926) (s:=25117) (rank:=32852036) (tiny:=2021) (pairs:=631398)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 630908926 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17581 : FinalSeventhSieve.rough 11092009835083 17581+201094097=FinalSeventhSieve.rough 11092009835083 17519 :=
  LargeQuotientSieve.combine to17579 row17581 rfl

set_option maxRecDepth 16000 in
private theorem row17597 :
    FinalSeventhSieve.rough 11092009835083 17597+33449442=FinalSeventhSieve.rough 11092009835083 17581 :=
  LargeQuotientSieve.row (p:=17597) (q:=630335275) (s:=25106) (rank:=32823842) (tiny:=2022) (pairs:=627621)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 630335275 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17597 : FinalSeventhSieve.rough 11092009835083 17597+234543539=FinalSeventhSieve.rough 11092009835083 17519 :=
  LargeQuotientSieve.combine to17581 row17597 rfl

set_option maxRecDepth 16000 in
private theorem row17599 :
    FinalSeventhSieve.rough 11092009835083 17599+33443869=FinalSeventhSieve.rough 11092009835083 17597 :=
  LargeQuotientSieve.row (p:=17599) (q:=630263641) (s:=25105) (rank:=32820298) (tiny:=2023) (pairs:=625593)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 630263641 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17599 : FinalSeventhSieve.rough 11092009835083 17599+267987408=FinalSeventhSieve.rough 11092009835083 17519 :=
  LargeQuotientSieve.combine to17597 row17599 rfl

set_option maxRecDepth 16000 in
private theorem row17609 :
    FinalSeventhSieve.rough 11092009835083 17609+33423145=FinalSeventhSieve.rough 11092009835083 17599 :=
  LargeQuotientSieve.row (p:=17609) (q:=629905720) (s:=25097) (rank:=32802563) (tiny:=2024) (pairs:=622605)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 629905720 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17609 : FinalSeventhSieve.rough 11092009835083 17609+301410553=FinalSeventhSieve.rough 11092009835083 17519 :=
  LargeQuotientSieve.combine to17599 row17609 rfl

set_option maxRecDepth 16000 in
private theorem row17623 :
    FinalSeventhSieve.rough 11092009835083 17623+33395067=FinalSeventhSieve.rough 11092009835083 17609 :=
  LargeQuotientSieve.row (p:=17623) (q:=629405313) (s:=25087) (rank:=32777964) (tiny:=2025) (pairs:=619127)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 629405313 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17623 : FinalSeventhSieve.rough 11092009835083 17623+334805620=FinalSeventhSieve.rough 11092009835083 17519 :=
  LargeQuotientSieve.combine to17609 row17623 rfl

set_option maxRecDepth 16000 in
private theorem row17627 :
    FinalSeventhSieve.rough 11092009835083 17627+33385718=FinalSeventhSieve.rough 11092009835083 17623 :=
  LargeQuotientSieve.row (p:=17627) (q:=629262485) (s:=25085) (rank:=32770884) (tiny:=2026) (pairs:=616859)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 629262485 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17627 : FinalSeventhSieve.rough 11092009835083 17627+368191338=FinalSeventhSieve.rough 11092009835083 17519 :=
  LargeQuotientSieve.combine to17623 row17627 rfl

set_option maxRecDepth 16000 in
private theorem row17657 :
    FinalSeventhSieve.rough 11092009835083 17657+33327548=FinalSeventhSieve.rough 11092009835083 17627 :=
  LargeQuotientSieve.row (p:=17657) (q:=628193341) (s:=25063) (rank:=32718132) (tiny:=2027) (pairs:=611442)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 628193341 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17657 : FinalSeventhSieve.rough 11092009835083 17657+401518886=FinalSeventhSieve.rough 11092009835083 17519 :=
  LargeQuotientSieve.combine to17627 row17657 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 17657+401518886=FinalSeventhSieve.rough 11092009835083 17519 := to17657

end Tail11092009835083From17519To17657
