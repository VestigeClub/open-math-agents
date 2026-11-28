import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-625000000-650000000»

/-! Exact changes for sieve primes 1993 through 2004. -/
open Finset
namespace Tail11092009835083From17327To17419

set_option maxRecDepth 16000 in
private theorem row17333 :
    FinalSeventhSieve.rough 11092009835083 17333+34012603=FinalSeventhSieve.rough 11092009835083 17327 :=
  LargeQuotientSieve.row (p:=17333) (q:=639935950) (s:=25296) (rank:=33297294) (tiny:=1992) (pairs:=717300)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 639935950 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row17341 :
    FinalSeventhSieve.rough 11092009835083 17341+33995112=FinalSeventhSieve.rough 11092009835083 17333 :=
  LargeQuotientSieve.row (p:=17341) (q:=639640726) (s:=25291) (rank:=33282775) (tiny:=1993) (pairs:=714329)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 639640726 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17341 : FinalSeventhSieve.rough 11092009835083 17341+68007715=FinalSeventhSieve.rough 11092009835083 17327 :=
  LargeQuotientSieve.combine row17333 row17341 rfl

set_option maxRecDepth 16000 in
private theorem row17351 :
    FinalSeventhSieve.rough 11092009835083 17351+33973702=FinalSeventhSieve.rough 11092009835083 17341 :=
  LargeQuotientSieve.row (p:=17351) (q:=639272078) (s:=25283) (rank:=33264624) (tiny:=1994) (pairs:=711071)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 639272078 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17351 : FinalSeventhSieve.rough 11092009835083 17351+101981417=FinalSeventhSieve.rough 11092009835083 17327 :=
  LargeQuotientSieve.combine to17341 row17351 rfl

set_option maxRecDepth 16000 in
private theorem row17359 :
    FinalSeventhSieve.rough 11092009835083 17359+33956175=FinalSeventhSieve.rough 11092009835083 17351 :=
  LargeQuotientSieve.row (p:=17359) (q:=638977466) (s:=25278) (rank:=33250073) (tiny:=1995) (pairs:=708096)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 638977466 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17359 : FinalSeventhSieve.rough 11092009835083 17359+135937592=FinalSeventhSieve.rough 11092009835083 17327 :=
  LargeQuotientSieve.combine to17351 row17359 rfl

set_option maxRecDepth 16000 in
private theorem row17377 :
    FinalSeventhSieve.rough 11092009835083 17377+33919225=FinalSeventhSieve.rough 11092009835083 17359 :=
  LargeQuotientSieve.row (p:=17377) (q:=638315580) (s:=25264) (rank:=33217460) (tiny:=1996) (pairs:=703760)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 638315580 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17377 : FinalSeventhSieve.rough 11092009835083 17377+169856817=FinalSeventhSieve.rough 11092009835083 17327 :=
  LargeQuotientSieve.combine to17359 row17377 rfl

set_option maxRecDepth 16000 in
private theorem row17383 :
    FinalSeventhSieve.rough 11092009835083 17383+33905737=FinalSeventhSieve.rough 11092009835083 17377 :=
  LargeQuotientSieve.row (p:=17383) (q:=638095256) (s:=25260) (rank:=33206676) (tiny:=1997) (pairs:=701057)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 638095256 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17383 : FinalSeventhSieve.rough 11092009835083 17383+203762554=FinalSeventhSieve.rough 11092009835083 17327 :=
  LargeQuotientSieve.combine to17377 row17383 rfl

set_option maxRecDepth 16000 in
private theorem row17387 :
    FinalSeventhSieve.rough 11092009835083 17387+33896034=FinalSeventhSieve.rough 11092009835083 17383 :=
  LargeQuotientSieve.row (p:=17387) (q:=637948457) (s:=25257) (rank:=33199374) (tiny:=1998) (pairs:=698657)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 637948457 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17387 : FinalSeventhSieve.rough 11092009835083 17387+237658588=FinalSeventhSieve.rough 11092009835083 17327 :=
  LargeQuotientSieve.combine to17383 row17387 rfl

set_option maxRecDepth 16000 in
private theorem row17389 :
    FinalSeventhSieve.rough 11092009835083 17389+33890255=FinalSeventhSieve.rough 11092009835083 17387 :=
  LargeQuotientSieve.row (p:=17389) (q:=637875083) (s:=25256) (rank:=33195749) (tiny:=1999) (pairs:=696504)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 637875083 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17389 : FinalSeventhSieve.rough 11092009835083 17389+271548843=FinalSeventhSieve.rough 11092009835083 17327 :=
  LargeQuotientSieve.combine to17387 row17389 rfl

set_option maxRecDepth 16000 in
private theorem row17393 :
    FinalSeventhSieve.rough 11092009835083 17393+33880632=FinalSeventhSieve.rough 11092009835083 17389 :=
  LargeQuotientSieve.row (p:=17393) (q:=637728386) (s:=25253) (rank:=33188549) (tiny:=2000) (pairs:=694082)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 637728386 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17393 : FinalSeventhSieve.rough 11092009835083 17393+305429475=FinalSeventhSieve.rough 11092009835083 17327 :=
  LargeQuotientSieve.combine to17389 row17393 rfl

set_option maxRecDepth 16000 in
private theorem row17401 :
    FinalSeventhSieve.rough 11092009835083 17401+33863206=FinalSeventhSieve.rough 11092009835083 17393 :=
  LargeQuotientSieve.row (p:=17401) (q:=637435195) (s:=25247) (rank:=33174085) (tiny:=2001) (pairs:=691121)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 637435195 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17401 : FinalSeventhSieve.rough 11092009835083 17401+339292681=FinalSeventhSieve.rough 11092009835083 17327 :=
  LargeQuotientSieve.combine to17393 row17401 rfl

set_option maxRecDepth 16000 in
private theorem row17417 :
    FinalSeventhSieve.rough 11092009835083 17417+33830273=FinalSeventhSieve.rough 11092009835083 17401 :=
  LargeQuotientSieve.row (p:=17417) (q:=636849620) (s:=25235) (rank:=33145118) (tiny:=2002) (pairs:=687156)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 636849620 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17417 : FinalSeventhSieve.rough 11092009835083 17417+373122954=FinalSeventhSieve.rough 11092009835083 17327 :=
  LargeQuotientSieve.combine to17401 row17417 rfl

set_option maxRecDepth 16000 in
private theorem row17419 :
    FinalSeventhSieve.rough 11092009835083 17419+33824491=FinalSeventhSieve.rough 11092009835083 17417 :=
  LargeQuotientSieve.row (p:=17419) (q:=636776498) (s:=25234) (rank:=33141479) (tiny:=2003) (pairs:=685014)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 636776498 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17419 : FinalSeventhSieve.rough 11092009835083 17419+406947445=FinalSeventhSieve.rough 11092009835083 17327 :=
  LargeQuotientSieve.combine to17417 row17419 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 17419+406947445=FinalSeventhSieve.rough 11092009835083 17327 := to17419

end Tail11092009835083From17327To17419
