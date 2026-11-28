import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 3081 through 3092. -/
open Finset
namespace Tail30110134441897From28283To28411

set_option maxRecDepth 16000 in
private theorem row28289 :
    FinalSeventhSieve.rough 30110134441897 28289+54131681=FinalSeventhSieve.rough 30110134441897 28283 :=
  LargeQuotientSieve.row (p:=28289) (q:=1064376062) (s:=32624) (rank:=53949098) (tiny:=3080) (pairs:=185662)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1064376062 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row28297 :
    FinalSeventhSieve.rough 30110134441897 28297+54115704=FinalSeventhSieve.rough 30110134441897 28289 :=
  LargeQuotientSieve.row (p:=28297) (q:=1064075147) (s:=32620) (rank:=53934409) (tiny:=3081) (pairs:=184375)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1064075147 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28297 : FinalSeventhSieve.rough 30110134441897 28297+108247385=FinalSeventhSieve.rough 30110134441897 28283 :=
  LargeQuotientSieve.combine row28289 row28297 rfl

set_option maxRecDepth 16000 in
private theorem row28307 :
    FinalSeventhSieve.rough 30110134441897 28307+54096377=FinalSeventhSieve.rough 30110134441897 28297 :=
  LargeQuotientSieve.row (p:=28307) (q:=1063699241) (s:=32614) (rank:=53916478) (tiny:=3082) (pairs:=182980)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1063699241 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28307 : FinalSeventhSieve.rough 30110134441897 28307+162343762=FinalSeventhSieve.rough 30110134441897 28283 :=
  LargeQuotientSieve.combine to28297 row28307 rfl

set_option maxRecDepth 16000 in
private theorem row28309 :
    FinalSeventhSieve.rough 30110134441897 28309+54091707=FinalSeventhSieve.rough 30110134441897 28307 :=
  LargeQuotientSieve.row (p:=28309) (q:=1063624092) (s:=32613) (rank:=53912810) (tiny:=3083) (pairs:=181979)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1063624092 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28309 : FinalSeventhSieve.rough 30110134441897 28309+216435469=FinalSeventhSieve.rough 30110134441897 28283 :=
  LargeQuotientSieve.combine to28307 row28309 rfl

set_option maxRecDepth 16000 in
private theorem row28319 :
    FinalSeventhSieve.rough 30110134441897 28319+54072153=FinalSeventhSieve.rough 30110134441897 28309 :=
  LargeQuotientSieve.row (p:=28319) (q:=1063248506) (s:=32607) (rank:=53894649) (tiny:=3084) (pairs:=180587)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1063248506 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28319 : FinalSeventhSieve.rough 30110134441897 28319+270507622=FinalSeventhSieve.rough 30110134441897 28283 :=
  LargeQuotientSieve.combine to28309 row28319 rfl

set_option maxRecDepth 16000 in
private theorem row28349 :
    FinalSeventhSieve.rough 30110134441897 28349+54015773=FinalSeventhSieve.rough 30110134441897 28319 :=
  LargeQuotientSieve.row (p:=28349) (q:=1062123335) (s:=32590) (rank:=53840614) (tiny:=3085) (pairs:=178243)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1062123335 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28349 : FinalSeventhSieve.rough 30110134441897 28349+324523395=FinalSeventhSieve.rough 30110134441897 28283 :=
  LargeQuotientSieve.combine to28319 row28349 rfl

set_option maxRecDepth 16000 in
private theorem row28351 :
    FinalSeventhSieve.rough 30110134441897 28351+54011212=FinalSeventhSieve.rough 30110134441897 28349 :=
  LargeQuotientSieve.row (p:=28351) (q:=1062048408) (s:=32589) (rank:=53837022) (tiny:=3086) (pairs:=177275)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1062048408 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28351 : FinalSeventhSieve.rough 30110134441897 28351+378534607=FinalSeventhSieve.rough 30110134441897 28283 :=
  LargeQuotientSieve.combine to28349 row28351 rfl

set_option maxRecDepth 16000 in
private theorem row28387 :
    FinalSeventhSieve.rough 30110134441897 28387+53943812=FinalSeventhSieve.rough 30110134441897 28351 :=
  LargeQuotientSieve.row (p:=28387) (q:=1060701533) (s:=32568) (rank:=53772230) (tiny:=3087) (pairs:=174668)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1060701533 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28387 : FinalSeventhSieve.rough 30110134441897 28387+432478419=FinalSeventhSieve.rough 30110134441897 28283 :=
  LargeQuotientSieve.combine to28351 row28387 rfl

set_option maxRecDepth 16000 in
private theorem row28393 :
    FinalSeventhSieve.rough 30110134441897 28393+53931942=FinalSeventhSieve.rough 30110134441897 28387 :=
  LargeQuotientSieve.row (p:=28393) (q:=1060477386) (s:=32564) (rank:=53761505) (tiny:=3088) (pairs:=173524)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1060477386 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28393 : FinalSeventhSieve.rough 30110134441897 28393+486410361=FinalSeventhSieve.rough 30110134441897 28283 :=
  LargeQuotientSieve.combine to28387 row28393 rfl

set_option maxRecDepth 16000 in
private theorem row28403 :
    FinalSeventhSieve.rough 30110134441897 28403+53912633=FinalSeventhSieve.rough 30110134441897 28393 :=
  LargeQuotientSieve.row (p:=28403) (q:=1060104018) (s:=32559) (rank:=53743551) (tiny:=3089) (pairs:=172170)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1060104018 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28403 : FinalSeventhSieve.rough 30110134441897 28403+540322994=FinalSeventhSieve.rough 30110134441897 28283 :=
  LargeQuotientSieve.combine to28393 row28403 rfl

set_option maxRecDepth 16000 in
private theorem row28409 :
    FinalSeventhSieve.rough 30110134441897 28409+53900766=FinalSeventhSieve.rough 30110134441897 28403 :=
  LargeQuotientSieve.row (p:=28409) (q:=1059880123) (s:=32555) (rank:=53732846) (tiny:=3090) (pairs:=171009)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1059880123 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28409 : FinalSeventhSieve.rough 30110134441897 28409+594223760=FinalSeventhSieve.rough 30110134441897 28283 :=
  LargeQuotientSieve.combine to28403 row28409 rfl

set_option maxRecDepth 16000 in
private theorem row28411 :
    FinalSeventhSieve.rough 30110134441897 28411+53896228=FinalSeventhSieve.rough 30110134441897 28409 :=
  LargeQuotientSieve.row (p:=28411) (q:=1059805513) (s:=32554) (rank:=53729259) (tiny:=3091) (pairs:=170059)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1059805513 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28411 : FinalSeventhSieve.rough 30110134441897 28411+648119988=FinalSeventhSieve.rough 30110134441897 28283 :=
  LargeQuotientSieve.combine to28409 row28411 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 28411+648119988=FinalSeventhSieve.rough 30110134441897 28283 := to28411

end Tail30110134441897From28283To28411
