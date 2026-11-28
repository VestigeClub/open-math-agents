import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-625000000-650000000»

/-! Exact changes for sieve primes 1981 through 1992. -/
open Finset
namespace Tail11092009835083From17191To17327

set_option maxRecDepth 16000 in
private theorem row17203 :
    FinalSeventhSieve.rough 11092009835083 17203+34292348=FinalSeventhSieve.rough 11092009835083 17191 :=
  LargeQuotientSieve.row (p:=17203) (q:=644771832) (s:=25392) (rank:=33535546) (tiny:=1980) (pairs:=758781)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 644771832 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row17207 :
    FinalSeventhSieve.rough 11092009835083 17207+34282386=FinalSeventhSieve.rough 11092009835083 17203 :=
  LargeQuotientSieve.row (p:=17207) (q:=644621946) (s:=25389) (rank:=33528099) (tiny:=1981) (pairs:=756267)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 644621946 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17207 : FinalSeventhSieve.rough 11092009835083 17207+68574734=FinalSeventhSieve.rough 11092009835083 17191 :=
  LargeQuotientSieve.combine row17203 row17207 rfl

set_option maxRecDepth 16000 in
private theorem row17209 :
    FinalSeventhSieve.rough 11092009835083 17209+34276452=FinalSeventhSieve.rough 11092009835083 17207 :=
  LargeQuotientSieve.row (p:=17209) (q:=644547029) (s:=25387) (rank:=33524427) (tiny:=1982) (pairs:=754006)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 644547029 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17209 : FinalSeventhSieve.rough 11092009835083 17209+102851186=FinalSeventhSieve.rough 11092009835083 17191 :=
  LargeQuotientSieve.combine to17207 row17209 rfl

set_option maxRecDepth 16000 in
private theorem row17231 :
    FinalSeventhSieve.rough 11092009835083 17231+34230933=FinalSeventhSieve.rough 11092009835083 17209 :=
  LargeQuotientSieve.row (p:=17231) (q:=643724092) (s:=25371) (rank:=33484023) (tiny:=1983) (pairs:=748892)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 643724092 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17231 : FinalSeventhSieve.rough 11092009835083 17231+137082119=FinalSeventhSieve.rough 11092009835083 17191 :=
  LargeQuotientSieve.combine to17209 row17231 rfl

set_option maxRecDepth 16000 in
private theorem row17239 :
    FinalSeventhSieve.rough 11092009835083 17239+34213189=FinalSeventhSieve.rough 11092009835083 17231 :=
  LargeQuotientSieve.row (p:=17239) (q:=643425363) (s:=25365) (rank:=33469337) (tiny:=1984) (pairs:=745835)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 643425363 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17239 : FinalSeventhSieve.rough 11092009835083 17239+171295308=FinalSeventhSieve.rough 11092009835083 17191 :=
  LargeQuotientSieve.combine to17231 row17239 rfl

set_option maxRecDepth 16000 in
private theorem row17257 :
    FinalSeventhSieve.rough 11092009835083 17257+34175689=FinalSeventhSieve.rough 11092009835083 17239 :=
  LargeQuotientSieve.row (p:=17257) (q:=642754235) (s:=25352) (rank:=33436326) (tiny:=1985) (pairs:=741347)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 642754235 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17257 : FinalSeventhSieve.rough 11092009835083 17257+205470997=FinalSeventhSieve.rough 11092009835083 17191 :=
  LargeQuotientSieve.combine to17239 row17257 rfl

set_option maxRecDepth 16000 in
private theorem row17291 :
    FinalSeventhSieve.rough 11092009835083 17291+34106820=FinalSeventhSieve.rough 11092009835083 17257 :=
  LargeQuotientSieve.row (p:=17291) (q:=641490361) (s:=25327) (rank:=33374138) (tiny:=1986) (pairs:=734667)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 641490361 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17291 : FinalSeventhSieve.rough 11092009835083 17291+239577817=FinalSeventhSieve.rough 11092009835083 17191 :=
  LargeQuotientSieve.combine to17257 row17291 rfl

set_option maxRecDepth 16000 in
private theorem row17293 :
    FinalSeventhSieve.rough 11092009835083 17293+34100945=FinalSeventhSieve.rough 11092009835083 17291 :=
  LargeQuotientSieve.row (p:=17293) (q:=641416170) (s:=25326) (rank:=33370457) (tiny:=1987) (pairs:=732474)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 641416170 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17293 : FinalSeventhSieve.rough 11092009835083 17293+273678762=FinalSeventhSieve.rough 11092009835083 17191 :=
  LargeQuotientSieve.combine to17291 row17293 rfl

set_option maxRecDepth 16000 in
private theorem row17299 :
    FinalSeventhSieve.rough 11092009835083 17299+34087174=FinalSeventhSieve.rough 11092009835083 17293 :=
  LargeQuotientSieve.row (p:=17299) (q:=641193701) (s:=25321) (rank:=33359454) (tiny:=1988) (pairs:=729707)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 641193701 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17299 : FinalSeventhSieve.rough 11092009835083 17299+307765936=FinalSeventhSieve.rough 11092009835083 17191 :=
  LargeQuotientSieve.combine to17293 row17299 rfl

set_option maxRecDepth 16000 in
private theorem row17317 :
    FinalSeventhSieve.rough 11092009835083 17317+34049846=FinalSeventhSieve.rough 11092009835083 17299 :=
  LargeQuotientSieve.row (p:=17317) (q:=640527218) (s:=25308) (rank:=33326527) (tiny:=1989) (pairs:=725307)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 640527218 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17317 : FinalSeventhSieve.rough 11092009835083 17317+341815782=FinalSeventhSieve.rough 11092009835083 17191 :=
  LargeQuotientSieve.combine to17299 row17317 rfl

set_option maxRecDepth 16000 in
private theorem row17321 :
    FinalSeventhSieve.rough 11092009835083 17321+34040097=FinalSeventhSieve.rough 11092009835083 17317 :=
  LargeQuotientSieve.row (p:=17321) (q:=640379298) (s:=25305) (rank:=33319275) (tiny:=1990) (pairs:=722811)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 640379298 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17321 : FinalSeventhSieve.rough 11092009835083 17321+375855879=FinalSeventhSieve.rough 11092009835083 17191 :=
  LargeQuotientSieve.combine to17317 row17321 rfl

set_option maxRecDepth 16000 in
private theorem row17327 :
    FinalSeventhSieve.rough 11092009835083 17327+34026345=FinalSeventhSieve.rough 11092009835083 17321 :=
  LargeQuotientSieve.row (p:=17327) (q:=640157548) (s:=25301) (rank:=33308287) (tiny:=1991) (pairs:=720048)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 640157548 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17327 : FinalSeventhSieve.rough 11092009835083 17327+409882224=FinalSeventhSieve.rough 11092009835083 17191 :=
  LargeQuotientSieve.combine to17321 row17327 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 17327+409882224=FinalSeventhSieve.rough 11092009835083 17191 := to17327

end Tail11092009835083From17191To17327
