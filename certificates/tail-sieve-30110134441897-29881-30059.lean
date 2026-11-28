import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1000000000-1025000000»

/-! Exact changes for sieve primes 3239 through 3250. -/
open Finset
namespace Tail30110134441897From29881To30059

set_option maxRecDepth 16000 in
private theorem row29917 :
    FinalSeventhSieve.rough 30110134441897 29917+51186589=FinalSeventhSieve.rough 30110134441897 29881 :=
  LargeQuotientSieve.row (p:=29917) (q:=1006455675) (s:=31724) (rank:=51158968) (tiny:=3238) (pairs:=30858)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1006455675 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row29921 :
    FinalSeventhSieve.rough 30110134441897 29921+51179693=FinalSeventhSieve.rough 30110134441897 29917 :=
  LargeQuotientSieve.row (p:=29921) (q:=1006321127) (s:=31722) (rank:=51152522) (tiny:=3239) (pairs:=30409)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1006321127 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29921 : FinalSeventhSieve.rough 30110134441897 29921+102366282=FinalSeventhSieve.rough 30110134441897 29881 :=
  LargeQuotientSieve.combine row29917 row29921 rfl

set_option maxRecDepth 16000 in
private theorem row29927 :
    FinalSeventhSieve.rough 30110134441897 29927+51169497=FinalSeventhSieve.rough 30110134441897 29921 :=
  LargeQuotientSieve.row (p:=29927) (q:=1006119371) (s:=31719) (rank:=51142802) (tiny:=3240) (pairs:=29934)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1006119371 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29927 : FinalSeventhSieve.rough 30110134441897 29927+153535779=FinalSeventhSieve.rough 30110134441897 29881 :=
  LargeQuotientSieve.combine to29921 row29927 rfl

set_option maxRecDepth 16000 in
private theorem row29947 :
    FinalSeventhSieve.rough 30110134441897 29947+51136357=FinalSeventhSieve.rough 30110134441897 29927 :=
  LargeQuotientSieve.row (p:=29947) (q:=1005447438) (s:=31708) (rank:=51110405) (tiny:=3241) (pairs:=29192)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1005447438 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29947 : FinalSeventhSieve.rough 30110134441897 29947+204672136=FinalSeventhSieve.rough 30110134441897 29881 :=
  LargeQuotientSieve.combine to29927 row29947 rfl

set_option maxRecDepth 16000 in
private theorem row29959 :
    FinalSeventhSieve.rough 30110134441897 29959+51116219=FinalSeventhSieve.rough 30110134441897 29947 :=
  LargeQuotientSieve.row (p:=29959) (q:=1005044709) (s:=31702) (rank:=51090825) (tiny:=3242) (pairs:=28635)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1005044709 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29959 : FinalSeventhSieve.rough 30110134441897 29959+255788355=FinalSeventhSieve.rough 30110134441897 29881 :=
  LargeQuotientSieve.combine to29947 row29959 rfl

set_option maxRecDepth 16000 in
private theorem row29983 :
    FinalSeventhSieve.rough 30110134441897 29983+51076544=FinalSeventhSieve.rough 30110134441897 29959 :=
  LargeQuotientSieve.row (p:=29983) (q:=1004240217) (s:=31689) (rank:=51051939) (tiny:=3243) (pairs:=27847)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1004240217 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29983 : FinalSeventhSieve.rough 30110134441897 29983+306864899=FinalSeventhSieve.rough 30110134441897 29881 :=
  LargeQuotientSieve.combine to29959 row29983 rfl

set_option maxRecDepth 16000 in
private theorem row29989 :
    FinalSeventhSieve.rough 30110134441897 29989+51066450=FinalSeventhSieve.rough 30110134441897 29983 :=
  LargeQuotientSieve.row (p:=29989) (q:=1004039295) (s:=31686) (rank:=51042297) (tiny:=3244) (pairs:=27396)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1004039295 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29989 : FinalSeventhSieve.rough 30110134441897 29989+357931349=FinalSeventhSieve.rough 30110134441897 29881 :=
  LargeQuotientSieve.combine to29983 row29989 rfl

set_option maxRecDepth 16000 in
private theorem row30011 :
    FinalSeventhSieve.rough 30110134441897 30011+51030145=FinalSeventhSieve.rough 30110134441897 29989 :=
  LargeQuotientSieve.row (p:=30011) (q:=1003303270) (s:=31674) (rank:=51006715) (tiny:=3245) (pairs:=26674)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1003303270 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30011 : FinalSeventhSieve.rough 30110134441897 30011+408961494=FinalSeventhSieve.rough 30110134441897 29881 :=
  LargeQuotientSieve.combine to29989 row30011 rfl

set_option maxRecDepth 16000 in
private theorem row30013 :
    FinalSeventhSieve.rough 30110134441897 30013+51026588=FinalSeventhSieve.rough 30110134441897 30011 :=
  LargeQuotientSieve.row (p:=30013) (q:=1003236412) (s:=31673) (rank:=51003529) (tiny:=3246) (pairs:=26304)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1003236412 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30013 : FinalSeventhSieve.rough 30110134441897 30013+459988082=FinalSeventhSieve.rough 30110134441897 29881 :=
  LargeQuotientSieve.combine to30011 row30013 rfl

set_option maxRecDepth 16000 in
private theorem row30029 :
    FinalSeventhSieve.rough 30110134441897 30029+51000143=FinalSeventhSieve.rough 30110134441897 30013 :=
  LargeQuotientSieve.row (p:=30029) (q:=1002701869) (s:=31665) (rank:=50977680) (tiny:=3247) (pairs:=25709)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1002701869 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30029 : FinalSeventhSieve.rough 30110134441897 30029+510988225=FinalSeventhSieve.rough 30110134441897 29881 :=
  LargeQuotientSieve.combine to30013 row30029 rfl

set_option maxRecDepth 16000 in
private theorem row30047 :
    FinalSeventhSieve.rough 30110134441897 30047+50970647=FinalSeventhSieve.rough 30110134441897 30029 :=
  LargeQuotientSieve.row (p:=30047) (q:=1002101189) (s:=31655) (rank:=50948824) (tiny:=3248) (pairs:=25070)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1002101189 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30047 : FinalSeventhSieve.rough 30110134441897 30047+561958872=FinalSeventhSieve.rough 30110134441897 29881 :=
  LargeQuotientSieve.combine to30029 row30047 rfl

set_option maxRecDepth 16000 in
private theorem row30059 :
    FinalSeventhSieve.rough 30110134441897 30059+50950935=FinalSeventhSieve.rough 30110134441897 30047 :=
  LargeQuotientSieve.row (p:=30059) (q:=1001701135) (s:=31649) (rank:=50929628) (tiny:=3249) (pairs:=24555)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1001701135 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30059 : FinalSeventhSieve.rough 30110134441897 30059+612909807=FinalSeventhSieve.rough 30110134441897 29881 :=
  LargeQuotientSieve.combine to30047 row30059 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 30059+612909807=FinalSeventhSieve.rough 30110134441897 29881 := to30059

end Tail30110134441897From29881To30059
