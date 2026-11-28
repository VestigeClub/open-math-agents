import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 3093 through 3104. -/
open Finset
namespace Tail30110134441897From28411To28541

set_option maxRecDepth 16000 in
private theorem row28429 :
    FinalSeventhSieve.rough 30110134441897 28429+53862200=FinalSeventhSieve.rough 30110134441897 28411 :=
  LargeQuotientSieve.row (p:=28429) (q:=1059134490) (s:=32544) (rank:=53696925) (tiny:=3092) (pairs:=168366)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1059134490 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row28433 :
    FinalSeventhSieve.rough 30110134441897 28433+53854047=FinalSeventhSieve.rough 30110134441897 28429 :=
  LargeQuotientSieve.row (p:=28433) (q:=1058985490) (s:=32542) (rank:=53689827) (tiny:=3093) (pairs:=167312)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1058985490 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28433 : FinalSeventhSieve.rough 30110134441897 28433+107716247=FinalSeventhSieve.rough 30110134441897 28411 :=
  LargeQuotientSieve.combine row28429 row28433 rfl

set_option maxRecDepth 16000 in
private theorem row28439 :
    FinalSeventhSieve.rough 30110134441897 28439+53842108=FinalSeventhSieve.rough 30110134441897 28433 :=
  LargeQuotientSieve.row (p:=28439) (q:=1058762067) (s:=32538) (rank:=53679013) (tiny:=3094) (pairs:=166188)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1058762067 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28439 : FinalSeventhSieve.rough 30110134441897 28439+161558355=FinalSeventhSieve.rough 30110134441897 28411 :=
  LargeQuotientSieve.combine to28433 row28439 rfl

set_option maxRecDepth 16000 in
private theorem row28447 :
    FinalSeventhSieve.rough 30110134441897 28447+53826517=FinalSeventhSieve.rough 30110134441897 28439 :=
  LargeQuotientSieve.row (p:=28447) (q:=1058464317) (s:=32534) (rank:=53664660) (tiny:=3095) (pairs:=164951)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1058464317 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28447 : FinalSeventhSieve.rough 30110134441897 28447+215384872=FinalSeventhSieve.rough 30110134441897 28411 :=
  LargeQuotientSieve.combine to28439 row28447 rfl

set_option maxRecDepth 16000 in
private theorem row28463 :
    FinalSeventhSieve.rough 30110134441897 28463+53796184=FinalSeventhSieve.rough 30110134441897 28447 :=
  LargeQuotientSieve.row (p:=28463) (q:=1057869319) (s:=32524) (rank:=53635928) (tiny:=3096) (pairs:=163351)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1057869319 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28463 : FinalSeventhSieve.rough 30110134441897 28463+269181056=FinalSeventhSieve.rough 30110134441897 28411 :=
  LargeQuotientSieve.combine to28447 row28463 rfl

set_option maxRecDepth 16000 in
private theorem row28477 :
    FinalSeventhSieve.rough 30110134441897 28477+53769672=FinalSeventhSieve.rough 30110134441897 28463 :=
  LargeQuotientSieve.row (p:=28477) (q:=1057349244) (s:=32516) (rank:=53610926) (tiny:=3097) (pairs:=161842)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1057349244 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28477 : FinalSeventhSieve.rough 30110134441897 28477+322950728=FinalSeventhSieve.rough 30110134441897 28411 :=
  LargeQuotientSieve.combine to28463 row28477 rfl

set_option maxRecDepth 16000 in
private theorem row28493 :
    FinalSeventhSieve.rough 30110134441897 28493+53739524=FinalSeventhSieve.rough 30110134441897 28477 :=
  LargeQuotientSieve.row (p:=28493) (q:=1056755499) (s:=32507) (rank:=53582366) (tiny:=3098) (pairs:=160255)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1056755499 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28493 : FinalSeventhSieve.rough 30110134441897 28493+376690252=FinalSeventhSieve.rough 30110134441897 28411 :=
  LargeQuotientSieve.combine to28477 row28493 rfl

set_option maxRecDepth 16000 in
private theorem row28499 :
    FinalSeventhSieve.rough 30110134441897 28499+53727736=FinalSeventhSieve.rough 30110134441897 28493 :=
  LargeQuotientSieve.row (p:=28499) (q:=1056533016) (s:=32504) (rank:=53571693) (tiny:=3099) (pairs:=159141)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1056533016 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28499 : FinalSeventhSieve.rough 30110134441897 28499+430417988=FinalSeventhSieve.rough 30110134441897 28411 :=
  LargeQuotientSieve.combine to28493 row28499 rfl

set_option maxRecDepth 16000 in
private theorem row28513 :
    FinalSeventhSieve.rough 30110134441897 28513+53701309=FinalSeventhSieve.rough 30110134441897 28499 :=
  LargeQuotientSieve.row (p:=28513) (q:=1056014254) (s:=32496) (rank:=53546720) (tiny:=3100) (pairs:=157688)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1056014254 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28513 : FinalSeventhSieve.rough 30110134441897 28513+484119297=FinalSeventhSieve.rough 30110134441897 28411 :=
  LargeQuotientSieve.combine to28499 row28513 rfl

set_option maxRecDepth 16000 in
private theorem row28517 :
    FinalSeventhSieve.rough 30110134441897 28517+53693222=FinalSeventhSieve.rough 30110134441897 28513 :=
  LargeQuotientSieve.row (p:=28517) (q:=1055866130) (s:=32494) (rank:=53539639) (tiny:=3101) (pairs:=156683)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1055866130 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28517 : FinalSeventhSieve.rough 30110134441897 28517+537812519=FinalSeventhSieve.rough 30110134441897 28411 :=
  LargeQuotientSieve.combine to28513 row28517 rfl

set_option maxRecDepth 16000 in
private theorem row28537 :
    FinalSeventhSieve.rough 30110134441897 28537+53655969=FinalSeventhSieve.rough 30110134441897 28517 :=
  LargeQuotientSieve.row (p:=28537) (q:=1055126132) (s:=32482) (rank:=53504127) (tiny:=3102) (pairs:=154943)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1055126132 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28537 : FinalSeventhSieve.rough 30110134441897 28537+591468488=FinalSeventhSieve.rough 30110134441897 28411 :=
  LargeQuotientSieve.combine to28517 row28537 rfl

set_option maxRecDepth 16000 in
private theorem row28541 :
    FinalSeventhSieve.rough 30110134441897 28541+53647855=FinalSeventhSieve.rough 30110134441897 28537 :=
  LargeQuotientSieve.row (p:=28541) (q:=1054978257) (s:=32480) (rank:=53496992) (tiny:=3103) (pairs:=153965)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1054978257 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28541 : FinalSeventhSieve.rough 30110134441897 28541+645116343=FinalSeventhSieve.rough 30110134441897 28411 :=
  LargeQuotientSieve.combine to28537 row28541 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 28541+645116343=FinalSeventhSieve.rough 30110134441897 28411 := to28541

end Tail30110134441897From28411To28541
