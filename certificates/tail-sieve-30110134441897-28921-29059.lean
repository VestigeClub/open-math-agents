import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1025000000-1050000000»

/-! Exact changes for sieve primes 3149 through 3160. -/
open Finset
namespace Tail30110134441897From28921To29059

set_option maxRecDepth 16000 in
private theorem row28927 :
    FinalSeventhSieve.rough 30110134441897 28927+52921267=FinalSeventhSieve.rough 30110134441897 28921 :=
  LargeQuotientSieve.row (p:=28927) (q:=1040900696) (s:=32262) (rank:=52819613) (tiny:=3148) (pairs:=104801)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1040900696 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row28933 :
    FinalSeventhSieve.rough 30110134441897 28933+52909912=FinalSeventhSieve.rough 30110134441897 28927 :=
  LargeQuotientSieve.row (p:=28933) (q:=1040684838) (s:=32259) (rank:=52809155) (tiny:=3149) (pairs:=103905)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1040684838 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28933 : FinalSeventhSieve.rough 30110134441897 28933+105831179=FinalSeventhSieve.rough 30110134441897 28921 :=
  LargeQuotientSieve.combine row28927 row28933 rfl

set_option maxRecDepth 16000 in
private theorem row28949 :
    FinalSeventhSieve.rough 30110134441897 28949+52881000=FinalSeventhSieve.rough 30110134441897 28933 :=
  LargeQuotientSieve.row (p:=28949) (q:=1040109656) (s:=32250) (rank:=52781479) (tiny:=3150) (pairs:=102670)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1040109656 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28949 : FinalSeventhSieve.rough 30110134441897 28949+158712179=FinalSeventhSieve.rough 30110134441897 28921 :=
  LargeQuotientSieve.combine to28933 row28949 rfl

set_option maxRecDepth 16000 in
private theorem row28961 :
    FinalSeventhSieve.rough 30110134441897 28961+52858988=FinalSeventhSieve.rough 30110134441897 28949 :=
  LargeQuotientSieve.row (p:=28961) (q:=1039678686) (s:=32244) (rank:=52760568) (tiny:=3151) (pairs:=101570)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1039678686 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28961 : FinalSeventhSieve.rough 30110134441897 28961+211571167=FinalSeventhSieve.rough 30110134441897 28921 :=
  LargeQuotientSieve.combine to28949 row28961 rfl

set_option maxRecDepth 16000 in
private theorem row28979 :
    FinalSeventhSieve.rough 30110134441897 28979+52826652=FinalSeventhSieve.rough 30110134441897 28961 :=
  LargeQuotientSieve.row (p:=28979) (q:=1039032901) (s:=32234) (rank:=52729504) (tiny:=3152) (pairs:=100299)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1039032901 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28979 : FinalSeventhSieve.rough 30110134441897 28979+264397819=FinalSeventhSieve.rough 30110134441897 28921 :=
  LargeQuotientSieve.combine to28961 row28979 rfl

set_option maxRecDepth 16000 in
private theorem row29009 :
    FinalSeventhSieve.rough 30110134441897 29009+52773063=FinalSeventhSieve.rough 30110134441897 28979 :=
  LargeQuotientSieve.row (p:=29009) (q:=1037958372) (s:=32217) (rank:=52677615) (tiny:=3153) (pairs:=98600)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1037958372 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29009 : FinalSeventhSieve.rough 30110134441897 29009+317170882=FinalSeventhSieve.rough 30110134441897 28921 :=
  LargeQuotientSieve.combine to28979 row29009 rfl

set_option maxRecDepth 16000 in
private theorem row29017 :
    FinalSeventhSieve.rough 30110134441897 29017+52758389=FinalSeventhSieve.rough 30110134441897 29009 :=
  LargeQuotientSieve.row (p:=29017) (q:=1037672207) (s:=32212) (rank:=52663881) (tiny:=3154) (pairs:=97661)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1037672207 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29017 : FinalSeventhSieve.rough 30110134441897 29017+369929271=FinalSeventhSieve.rough 30110134441897 28921 :=
  LargeQuotientSieve.combine to29009 row29017 rfl

set_option maxRecDepth 16000 in
private theorem row29021 :
    FinalSeventhSieve.rough 30110134441897 29021+52750643=FinalSeventhSieve.rough 30110134441897 29017 :=
  LargeQuotientSieve.row (p:=29021) (q:=1037529183) (s:=32210) (rank:=52656916) (tiny:=3155) (pairs:=96881)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1037529183 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29021 : FinalSeventhSieve.rough 30110134441897 29021+422679914=FinalSeventhSieve.rough 30110134441897 28921 :=
  LargeQuotientSieve.combine to29017 row29021 rfl

set_option maxRecDepth 16000 in
private theorem row29023 :
    FinalSeventhSieve.rough 30110134441897 29023+52746494=FinalSeventhSieve.rough 30110134441897 29021 :=
  LargeQuotientSieve.row (p:=29023) (q:=1037457686) (s:=32209) (rank:=52653484) (tiny:=3156) (pairs:=96165)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1037457686 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29023 : FinalSeventhSieve.rough 30110134441897 29023+475426408=FinalSeventhSieve.rough 30110134441897 28921 :=
  LargeQuotientSieve.combine to29021 row29023 rfl

set_option maxRecDepth 16000 in
private theorem row29027 :
    FinalSeventhSieve.rough 30110134441897 29027+52738851=FinalSeventhSieve.rough 30110134441897 29023 :=
  LargeQuotientSieve.row (p:=29027) (q:=1037314722) (s:=32207) (rank:=52646602) (tiny:=3157) (pairs:=95405)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1037314722 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29027 : FinalSeventhSieve.rough 30110134441897 29027+528165259=FinalSeventhSieve.rough 30110134441897 28921 :=
  LargeQuotientSieve.combine to29023 row29027 rfl

set_option maxRecDepth 16000 in
private theorem row29033 :
    FinalSeventhSieve.rough 30110134441897 29033+52727760=FinalSeventhSieve.rough 30110134441897 29027 :=
  LargeQuotientSieve.row (p:=29033) (q:=1037100349) (s:=32204) (rank:=52636354) (tiny:=3158) (pairs:=94563)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1037100349 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29033 : FinalSeventhSieve.rough 30110134441897 29033+580893019=FinalSeventhSieve.rough 30110134441897 28921 :=
  LargeQuotientSieve.combine to29027 row29033 rfl

set_option maxRecDepth 16000 in
private theorem row29059 :
    FinalSeventhSieve.rough 30110134441897 29059+52681370=FinalSeventhSieve.rough 30110134441897 29033 :=
  LargeQuotientSieve.row (p:=29059) (q:=1036172423) (s:=32189) (rank:=52591497) (tiny:=3159) (pairs:=93031)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1036172423 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29059 : FinalSeventhSieve.rough 30110134441897 29059+633574389=FinalSeventhSieve.rough 30110134441897 28921 :=
  LargeQuotientSieve.combine to29033 row29059 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 29059+633574389=FinalSeventhSieve.rough 30110134441897 28921 := to29059

end Tail30110134441897From28921To29059
