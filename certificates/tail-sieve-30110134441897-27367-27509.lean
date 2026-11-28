import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1075000000-1100000000»

/-! Exact changes for sieve primes 2994 through 3005. -/
open Finset
namespace Tail30110134441897From27367To27509

set_option maxRecDepth 16000 in
private theorem row27397 :
    FinalSeventhSieve.rough 30110134441897 27397+55944188=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.row (p:=27397) (q:=1099030347) (s:=33151) (rank:=55615755) (tiny:=2993) (pairs:=331425)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1099030347 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row27407 :
    FinalSeventhSieve.rough 30110134441897 27407+55923062=FinalSeventhSieve.rough 30110134441897 27397 :=
  LargeQuotientSieve.row (p:=27407) (q:=1098629344) (s:=33145) (rank:=55596556) (tiny:=2994) (pairs:=329499)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1098629344 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27407 : FinalSeventhSieve.rough 30110134441897 27407+111867250=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine row27397 row27407 rfl

set_option maxRecDepth 16000 in
private theorem row27409 :
    FinalSeventhSieve.rough 30110134441897 27409+55917892=FinalSeventhSieve.rough 30110134441897 27407 :=
  LargeQuotientSieve.row (p:=27409) (q:=1098549178) (s:=33144) (rank:=55592749) (tiny:=2995) (pairs:=328137)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1098549178 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27409 : FinalSeventhSieve.rough 30110134441897 27409+167785142=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27407 row27409 rfl

set_option maxRecDepth 16000 in
private theorem row27427 :
    FinalSeventhSieve.rough 30110134441897 27427+55880745=FinalSeventhSieve.rough 30110134441897 27409 :=
  LargeQuotientSieve.row (p:=27427) (q:=1097828214) (s:=33133) (rank:=55558109) (tiny:=2996) (pairs:=325631)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1097828214 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27427 : FinalSeventhSieve.rough 30110134441897 27427+223665887=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27409 row27427 rfl

set_option maxRecDepth 16000 in
private theorem row27431 :
    FinalSeventhSieve.rough 30110134441897 27431+55871594=FinalSeventhSieve.rough 30110134441897 27427 :=
  LargeQuotientSieve.row (p:=27431) (q:=1097668128) (s:=33131) (rank:=55550439) (tiny:=2997) (pairs:=324151)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1097668128 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27431 : FinalSeventhSieve.rough 30110134441897 27431+279537481=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27427 row27431 rfl

set_option maxRecDepth 16000 in
private theorem row27437 :
    FinalSeventhSieve.rough 30110134441897 27437+55858451=FinalSeventhSieve.rough 30110134441897 27431 :=
  LargeQuotientSieve.row (p:=27437) (q:=1097428087) (s:=33127) (rank:=55538891) (tiny:=2998) (pairs:=322557)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1097428087 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27437 : FinalSeventhSieve.rough 30110134441897 27437+335395932=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27431 row27437 rfl

set_option maxRecDepth 16000 in
private theorem row27449 :
    FinalSeventhSieve.rough 30110134441897 27449+55833316=FinalSeventhSieve.rough 30110134441897 27437 :=
  LargeQuotientSieve.row (p:=27449) (q:=1096948320) (s:=33120) (rank:=55515796) (tiny:=2999) (pairs:=320518)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1096948320 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27449 : FinalSeventhSieve.rough 30110134441897 27449+391229248=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27437 row27449 rfl

set_option maxRecDepth 16000 in
private theorem row27457 :
    FinalSeventhSieve.rough 30110134441897 27457+55816136=FinalSeventhSieve.rough 30110134441897 27449 :=
  LargeQuotientSieve.row (p:=27457) (q:=1096628708) (s:=33115) (rank:=55500363) (tiny:=3000) (pairs:=318772)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1096628708 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27457 : FinalSeventhSieve.rough 30110134441897 27457+447045384=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27449 row27457 rfl

set_option maxRecDepth 16000 in
private theorem row27479 :
    FinalSeventhSieve.rough 30110134441897 27479+55771184=FinalSeventhSieve.rough 30110134441897 27457 :=
  LargeQuotientSieve.row (p:=27479) (q:=1095750734) (s:=33102) (rank:=55458104) (tiny:=3001) (pairs:=316080)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1095750734 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27479 : FinalSeventhSieve.rough 30110134441897 27479+502816568=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27457 row27479 rfl

set_option maxRecDepth 16000 in
private theorem row27481 :
    FinalSeventhSieve.rough 30110134441897 27481+55766058=FinalSeventhSieve.rough 30110134441897 27479 :=
  LargeQuotientSieve.row (p:=27481) (q:=1095670988) (s:=33100) (rank:=55454315) (tiny:=3002) (pairs:=314744)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1095670988 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27481 : FinalSeventhSieve.rough 30110134441897 27481+558582626=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27479 row27481 rfl

set_option maxRecDepth 16000 in
private theorem row27487 :
    FinalSeventhSieve.rough 30110134441897 27487+55752924=FinalSeventhSieve.rough 30110134441897 27481 :=
  LargeQuotientSieve.row (p:=27487) (q:=1095431820) (s:=33097) (rank:=55442796) (tiny:=3003) (pairs:=313130)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1095431820 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27487 : FinalSeventhSieve.rough 30110134441897 27487+614335550=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27481 row27487 rfl

set_option maxRecDepth 16000 in
private theorem row27509 :
    FinalSeventhSieve.rough 30110134441897 27509+55708223=FinalSeventhSieve.rough 30110134441897 27487 :=
  LargeQuotientSieve.row (p:=27509) (q:=1094555761) (s:=33084) (rank:=55400772) (tiny:=3004) (pairs:=310454)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1094555761 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27509 : FinalSeventhSieve.rough 30110134441897 27509+670043773=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27487 row27509 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 27509+670043773=FinalSeventhSieve.rough 30110134441897 27367 := to27509

end Tail30110134441897From27367To27509
