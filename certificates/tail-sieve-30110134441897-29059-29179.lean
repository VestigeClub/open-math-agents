import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1025000000-1050000000»

/-! Exact changes for sieve primes 3161 through 3172. -/
open Finset
namespace Tail30110134441897From29059To29179

set_option maxRecDepth 16000 in
private theorem row29063 :
    FinalSeventhSieve.rough 30110134441897 29063+52673807=FinalSeventhSieve.rough 30110134441897 29059 :=
  LargeQuotientSieve.row (p:=29063) (q:=1036029812) (s:=32187) (rank:=52584685) (tiny:=3160) (pairs:=92281)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1036029812 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row29077 :
    FinalSeventhSieve.rough 30110134441897 29077+52648758=FinalSeventhSieve.rough 30110134441897 29063 :=
  LargeQuotientSieve.row (p:=29077) (q:=1035530984) (s:=32179) (rank:=52560758) (tiny:=3161) (pairs:=91160)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1035530984 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29077 : FinalSeventhSieve.rough 30110134441897 29077+105322565=FinalSeventhSieve.rough 30110134441897 29059 :=
  LargeQuotientSieve.combine row29063 row29077 rfl

set_option maxRecDepth 16000 in
private theorem row29101 :
    FinalSeventhSieve.rough 30110134441897 29101+52606106=FinalSeventhSieve.rough 30110134441897 29077 :=
  LargeQuotientSieve.row (p:=29101) (q:=1034676967) (s:=32166) (rank:=52519532) (tiny:=3162) (pairs:=89735)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1034676967 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29101 : FinalSeventhSieve.rough 30110134441897 29101+157928671=FinalSeventhSieve.rough 30110134441897 29059 :=
  LargeQuotientSieve.combine to29077 row29101 rfl

set_option maxRecDepth 16000 in
private theorem row29123 :
    FinalSeventhSieve.rough 30110134441897 29123+52567095=FinalSeventhSieve.rough 30110134441897 29101 :=
  LargeQuotientSieve.row (p:=29123) (q:=1033895355) (s:=32154) (rank:=52481855) (tiny:=3163) (pairs:=88402)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1033895355 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29123 : FinalSeventhSieve.rough 30110134441897 29123+210495766=FinalSeventhSieve.rough 30110134441897 29059 :=
  LargeQuotientSieve.combine to29101 row29123 rfl

set_option maxRecDepth 16000 in
private theorem row29129 :
    FinalSeventhSieve.rough 30110134441897 29129+52556038=FinalSeventhSieve.rough 30110134441897 29123 :=
  LargeQuotientSieve.row (p:=29129) (q:=1033682393) (s:=32150) (rank:=52471616) (tiny:=3164) (pairs:=87585)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1033682393 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29129 : FinalSeventhSieve.rough 30110134441897 29129+263051804=FinalSeventhSieve.rough 30110134441897 29059 :=
  LargeQuotientSieve.combine to29123 row29129 rfl

set_option maxRecDepth 16000 in
private theorem row29131 :
    FinalSeventhSieve.rough 30110134441897 29131+52551921=FinalSeventhSieve.rough 30110134441897 29129 :=
  LargeQuotientSieve.row (p:=29131) (q:=1033611425) (s:=32149) (rank:=52468180) (tiny:=3165) (pairs:=86905)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1033611425 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29131 : FinalSeventhSieve.rough 30110134441897 29131+315603725=FinalSeventhSieve.rough 30110134441897 29059 :=
  LargeQuotientSieve.combine to29129 row29131 rfl

set_option maxRecDepth 16000 in
private theorem row29137 :
    FinalSeventhSieve.rough 30110134441897 29137+52540904=FinalSeventhSieve.rough 30110134441897 29131 :=
  LargeQuotientSieve.row (p:=29137) (q:=1033398580) (s:=32146) (rank:=52457975) (tiny:=3166) (pairs:=86094)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1033398580 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29137 : FinalSeventhSieve.rough 30110134441897 29137+368144629=FinalSeventhSieve.rough 30110134441897 29059 :=
  LargeQuotientSieve.combine to29131 row29137 rfl

set_option maxRecDepth 16000 in
private theorem row29147 :
    FinalSeventhSieve.rough 30110134441897 29147+52522924=FinalSeventhSieve.rough 30110134441897 29137 :=
  LargeQuotientSieve.row (p:=29147) (q:=1033044033) (s:=32141) (rank:=52440940) (tiny:=3167) (pairs:=85150)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1033044033 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29147 : FinalSeventhSieve.rough 30110134441897 29147+420667553=FinalSeventhSieve.rough 30110134441897 29059 :=
  LargeQuotientSieve.combine to29137 row29147 rfl

set_option maxRecDepth 16000 in
private theorem row29153 :
    FinalSeventhSieve.rough 30110134441897 29153+52511976=FinalSeventhSieve.rough 30110134441897 29147 :=
  LargeQuotientSieve.row (p:=29153) (q:=1032831421) (s:=32137) (rank:=52430783) (tiny:=3168) (pairs:=84360)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1032831421 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29153 : FinalSeventhSieve.rough 30110134441897 29153+473179529=FinalSeventhSieve.rough 30110134441897 29059 :=
  LargeQuotientSieve.combine to29147 row29153 rfl

set_option maxRecDepth 16000 in
private theorem row29167 :
    FinalSeventhSieve.rough 30110134441897 29167+52487020=FinalSeventhSieve.rough 30110134441897 29153 :=
  LargeQuotientSieve.row (p:=29167) (q:=1032335668) (s:=32129) (rank:=52406873) (tiny:=3169) (pairs:=83315)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1032335668 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29167 : FinalSeventhSieve.rough 30110134441897 29167+525666549=FinalSeventhSieve.rough 30110134441897 29059 :=
  LargeQuotientSieve.combine to29153 row29167 rfl

set_option maxRecDepth 16000 in
private theorem row29173 :
    FinalSeventhSieve.rough 30110134441897 29173+52476075=FinalSeventhSieve.rough 30110134441897 29167 :=
  LargeQuotientSieve.row (p:=29173) (q:=1032123348) (s:=32126) (rank:=52396714) (tiny:=3170) (pairs:=82530)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1032123348 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29173 : FinalSeventhSieve.rough 30110134441897 29173+578142624=FinalSeventhSieve.rough 30110134441897 29059 :=
  LargeQuotientSieve.combine to29167 row29173 rfl

set_option maxRecDepth 16000 in
private theorem row29179 :
    FinalSeventhSieve.rough 30110134441897 29179+52465061=FinalSeventhSieve.rough 30110134441897 29173 :=
  LargeQuotientSieve.row (p:=29179) (q:=1031911115) (s:=32123) (rank:=52386481) (tiny:=3171) (pairs:=81750)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1031911115 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29179 : FinalSeventhSieve.rough 30110134441897 29179+630607685=FinalSeventhSieve.rough 30110134441897 29059 :=
  LargeQuotientSieve.combine to29173 row29179 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 29179+630607685=FinalSeventhSieve.rough 30110134441897 29059 := to29179

end Tail30110134441897From29059To29179
