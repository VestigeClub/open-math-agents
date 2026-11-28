import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1025000000-1050000000»

/-! Exact changes for sieve primes 3185 through 3190. -/
open Finset
namespace Tail30110134441897From29303To29363

set_option maxRecDepth 16000 in
private theorem row29311 :
    FinalSeventhSieve.rough 30110134441897 29311+52229573=FinalSeventhSieve.rough 30110134441897 29303 :=
  LargeQuotientSieve.row (p:=29311) (q:=1027263977) (s:=32050) (rank:=52162487) (tiny:=3184) (pairs:=70269)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1027263977 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row29327 :
    FinalSeventhSieve.rough 30110134441897 29327+52201714=FinalSeventhSieve.rough 30110134441897 29311 :=
  LargeQuotientSieve.row (p:=29327) (q:=1026703530) (s:=32042) (rank:=52135654) (tiny:=3185) (pairs:=69244)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1026703530 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29327 : FinalSeventhSieve.rough 30110134441897 29327+104431287=FinalSeventhSieve.rough 30110134441897 29303 :=
  LargeQuotientSieve.combine row29311 row29327 rfl

set_option maxRecDepth 16000 in
private theorem row29333 :
    FinalSeventhSieve.rough 30110134441897 29333+52190815=FinalSeventhSieve.rough 30110134441897 29327 :=
  LargeQuotientSieve.row (p:=29333) (q:=1026493520) (s:=32038) (rank:=52125472) (tiny:=3186) (pairs:=68528)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1026493520 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29333 : FinalSeventhSieve.rough 30110134441897 29333+156622102=FinalSeventhSieve.rough 30110134441897 29303 :=
  LargeQuotientSieve.combine to29327 row29333 rfl

set_option maxRecDepth 16000 in
private theorem row29339 :
    FinalSeventhSieve.rough 30110134441897 29339+52179959=FinalSeventhSieve.rough 30110134441897 29333 :=
  LargeQuotientSieve.row (p:=29339) (q:=1026283596) (s:=32035) (rank:=52115329) (tiny:=3187) (pairs:=67816)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1026283596 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29339 : FinalSeventhSieve.rough 30110134441897 29339+208802061=FinalSeventhSieve.rough 30110134441897 29303 :=
  LargeQuotientSieve.combine to29333 row29339 rfl

set_option maxRecDepth 16000 in
private theorem row29347 :
    FinalSeventhSieve.rough 30110134441897 29347+52165673=FinalSeventhSieve.rough 30110134441897 29339 :=
  LargeQuotientSieve.row (p:=29347) (q:=1026003831) (s:=32031) (rank:=52101811) (tiny:=3188) (pairs:=67049)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1026003831 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29347 : FinalSeventhSieve.rough 30110134441897 29347+260967734=FinalSeventhSieve.rough 30110134441897 29303 :=
  LargeQuotientSieve.combine to29339 row29347 rfl

set_option maxRecDepth 16000 in
private theorem row29363 :
    FinalSeventhSieve.rough 30110134441897 29363+52137718=FinalSeventhSieve.rough 30110134441897 29347 :=
  LargeQuotientSieve.row (p:=29363) (q:=1025444758) (s:=32022) (rank:=52074841) (tiny:=3189) (pairs:=66065)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1025444758 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29363 : FinalSeventhSieve.rough 30110134441897 29363+313105452=FinalSeventhSieve.rough 30110134441897 29303 :=
  LargeQuotientSieve.combine to29347 row29363 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 29363+313105452=FinalSeventhSieve.rough 30110134441897 29303 := to29363

end Tail30110134441897From29303To29363
