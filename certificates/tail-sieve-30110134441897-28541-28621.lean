import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 3105 through 3116. -/
open Finset
namespace Tail30110134441897From28541To28621

set_option maxRecDepth 16000 in
private theorem row28547 :
    FinalSeventhSieve.rough 30110134441897 28547+53636259=FinalSeventhSieve.rough 30110134441897 28541 :=
  LargeQuotientSieve.row (p:=28547) (q:=1054756522) (s:=32477) (rank:=53486487) (tiny:=3104) (pairs:=152875)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1054756522 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row28549 :
    FinalSeventhSieve.rough 30110134441897 28549+53631723=FinalSeventhSieve.rough 30110134441897 28547 :=
  LargeQuotientSieve.row (p:=28549) (q:=1054682631) (s:=32475) (rank:=53482872) (tiny:=3105) (pairs:=151955)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1054682631 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28549 : FinalSeventhSieve.rough 30110134441897 28549+107267982=FinalSeventhSieve.rough 30110134441897 28541 :=
  LargeQuotientSieve.combine row28547 row28549 rfl

set_option maxRecDepth 16000 in
private theorem row28559 :
    FinalSeventhSieve.rough 30110134441897 28559+53612685=FinalSeventhSieve.rough 30110134441897 28549 :=
  LargeQuotientSieve.row (p:=28559) (q:=1054313331) (s:=32470) (rank:=53465073) (tiny:=3106) (pairs:=150717)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1054313331 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28559 : FinalSeventhSieve.rough 30110134441897 28559+160880667=FinalSeventhSieve.rough 30110134441897 28541 :=
  LargeQuotientSieve.combine to28549 row28559 rfl

set_option maxRecDepth 16000 in
private theorem row28571 :
    FinalSeventhSieve.rough 30110134441897 28571+53589979=FinalSeventhSieve.rough 30110134441897 28559 :=
  LargeQuotientSieve.row (p:=28571) (q:=1053870513) (s:=32463) (rank:=53443730) (tiny:=3107) (pairs:=149355)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1053870513 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28571 : FinalSeventhSieve.rough 30110134441897 28571+214470646=FinalSeventhSieve.rough 30110134441897 28541 :=
  LargeQuotientSieve.combine to28559 row28571 rfl

set_option maxRecDepth 16000 in
private theorem row28573 :
    FinalSeventhSieve.rough 30110134441897 28573+53585494=FinalSeventhSieve.rough 30110134441897 28571 :=
  LargeQuotientSieve.row (p:=28573) (q:=1053796746) (s:=32462) (rank:=53440132) (tiny:=3108) (pairs:=148469)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1053796746 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28573 : FinalSeventhSieve.rough 30110134441897 28573+268056140=FinalSeventhSieve.rough 30110134441897 28541 :=
  LargeQuotientSieve.combine to28571 row28573 rfl

set_option maxRecDepth 16000 in
private theorem row28579 :
    FinalSeventhSieve.rough 30110134441897 28579+53573934=FinalSeventhSieve.rough 30110134441897 28573 :=
  LargeQuotientSieve.row (p:=28579) (q:=1053575507) (s:=32458) (rank:=53429630) (tiny:=3109) (pairs:=147412)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1053575507 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28579 : FinalSeventhSieve.rough 30110134441897 28579+321630074=FinalSeventhSieve.rough 30110134441897 28541 :=
  LargeQuotientSieve.combine to28573 row28579 rfl

set_option maxRecDepth 16000 in
private theorem row28591 :
    FinalSeventhSieve.rough 30110134441897 28591+53551305=FinalSeventhSieve.rough 30110134441897 28579 :=
  LargeQuotientSieve.row (p:=28591) (q:=1053133309) (s:=32452) (rank:=53408335) (tiny:=3110) (pairs:=146079)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1053133309 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28591 : FinalSeventhSieve.rough 30110134441897 28591+375181379=FinalSeventhSieve.rough 30110134441897 28541 :=
  LargeQuotientSieve.combine to28579 row28591 rfl

set_option maxRecDepth 16000 in
private theorem row28597 :
    FinalSeventhSieve.rough 30110134441897 28597+53539638=FinalSeventhSieve.rough 30110134441897 28591 :=
  LargeQuotientSieve.row (p:=28597) (q:=1052912348) (s:=32448) (rank:=53397725) (tiny:=3111) (pairs:=145023)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1052912348 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28597 : FinalSeventhSieve.rough 30110134441897 28597+428721017=FinalSeventhSieve.rough 30110134441897 28541 :=
  LargeQuotientSieve.combine to28591 row28597 rfl

set_option maxRecDepth 16000 in
private theorem row28603 :
    FinalSeventhSieve.rough 30110134441897 28603+53527980=FinalSeventhSieve.rough 30110134441897 28597 :=
  LargeQuotientSieve.row (p:=28603) (q:=1052691481) (s:=32445) (rank:=53387123) (tiny:=3112) (pairs:=143968)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1052691481 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28603 : FinalSeventhSieve.rough 30110134441897 28603+482248997=FinalSeventhSieve.rough 30110134441897 28541 :=
  LargeQuotientSieve.combine to28597 row28603 rfl

set_option maxRecDepth 16000 in
private theorem row28607 :
    FinalSeventhSieve.rough 30110134441897 28607+53519805=FinalSeventhSieve.rough 30110134441897 28603 :=
  LargeQuotientSieve.row (p:=28607) (q:=1052544287) (s:=32442) (rank:=53379907) (tiny:=3113) (pairs:=143010)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1052544287 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28607 : FinalSeventhSieve.rough 30110134441897 28607+535768802=FinalSeventhSieve.rough 30110134441897 28541 :=
  LargeQuotientSieve.combine to28603 row28607 rfl

set_option maxRecDepth 16000 in
private theorem row28619 :
    FinalSeventhSieve.rough 30110134441897 28619+53497216=FinalSeventhSieve.rough 30110134441897 28607 :=
  LargeQuotientSieve.row (p:=28619) (q:=1052102954) (s:=32436) (rank:=53358629) (tiny:=3114) (pairs:=141700)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1052102954 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28619 : FinalSeventhSieve.rough 30110134441897 28619+589266018=FinalSeventhSieve.rough 30110134441897 28541 :=
  LargeQuotientSieve.combine to28607 row28619 rfl

set_option maxRecDepth 16000 in
private theorem row28621 :
    FinalSeventhSieve.rough 30110134441897 28621+53492816=FinalSeventhSieve.rough 30110134441897 28619 :=
  LargeQuotientSieve.row (p:=28621) (q:=1052029434) (s:=32435) (rank:=53355091) (tiny:=3115) (pairs:=140839)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1052029434 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28621 : FinalSeventhSieve.rough 30110134441897 28621+642758834=FinalSeventhSieve.rough 30110134441897 28541 :=
  LargeQuotientSieve.combine to28619 row28621 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 28621+642758834=FinalSeventhSieve.rough 30110134441897 28541 := to28621

end Tail30110134441897From28541To28621
