import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-650000000-675000000»

/-! Exact changes for sieve primes 1965 through 1968. -/
open Finset
namespace Tail11092009835083From17029To17053

set_option maxRecDepth 16000 in
private theorem row17033 :
    FinalSeventhSieve.rough 11092009835083 17033+34667053=FinalSeventhSieve.rough 11092009835083 17029 :=
  LargeQuotientSieve.row (p:=17033) (q:=651207058) (s:=25518) (rank:=33853014) (tiny:=1964) (pairs:=816002)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 651207058 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row17041 :
    FinalSeventhSieve.rough 11092009835083 17041+34648734=FinalSeventhSieve.rough 11092009835083 17033 :=
  LargeQuotientSieve.row (p:=17041) (q:=650901345) (s:=25512) (rank:=33837968) (tiny:=1965) (pairs:=812730)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 650901345 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17041 : FinalSeventhSieve.rough 11092009835083 17041+69315787=FinalSeventhSieve.rough 11092009835083 17029 :=
  LargeQuotientSieve.combine row17033 row17041 rfl

set_option maxRecDepth 16000 in
private theorem row17047 :
    FinalSeventhSieve.rough 11092009835083 17047+34634504=FinalSeventhSieve.rough 11092009835083 17041 :=
  LargeQuotientSieve.row (p:=17047) (q:=650672249) (s:=25508) (rank:=33826677) (tiny:=1966) (pairs:=809792)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 650672249 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17047 : FinalSeventhSieve.rough 11092009835083 17047+103950291=FinalSeventhSieve.rough 11092009835083 17029 :=
  LargeQuotientSieve.combine to17041 row17047 rfl

set_option maxRecDepth 16000 in
private theorem row17053 :
    FinalSeventhSieve.rough 11092009835083 17053+34620244=FinalSeventhSieve.rough 11092009835083 17047 :=
  LargeQuotientSieve.row (p:=17053) (q:=650443314) (s:=25503) (rank:=33815351) (tiny:=1967) (pairs:=806859)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 650443314 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17053 : FinalSeventhSieve.rough 11092009835083 17053+138570535=FinalSeventhSieve.rough 11092009835083 17029 :=
  LargeQuotientSieve.combine to17047 row17053 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 17053+138570535=FinalSeventhSieve.rough 11092009835083 17029 := to17053

end Tail11092009835083From17029To17053
