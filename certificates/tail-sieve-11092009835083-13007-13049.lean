import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-850000000-875000000»

/-! Exact changes for sieve primes 1551 through 1555. -/
open Finset
namespace Tail11092009835083From13007To13049

set_option maxRecDepth 16000 in
private theorem row13009 :
    FinalSeventhSieve.rough 11092009835083 13009+47101281=FinalSeventhSieve.rough 11092009835083 13007 :=
  LargeQuotientSieve.row (p:=13009) (q:=852641235) (s:=29200) (rank:=43710263) (tiny:=1550) (pairs:=3392567)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 852641235 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row13033 :
    FinalSeventhSieve.rough 11092009835083 13033+47008145=FinalSeventhSieve.rough 11092009835083 13009 :=
  LargeQuotientSieve.row (p:=13033) (q:=851071114) (s:=29173) (rank:=43633971) (tiny:=1551) (pairs:=3375724)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 851071114 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13033 : FinalSeventhSieve.rough 11092009835083 13033+94109426=FinalSeventhSieve.rough 11092009835083 13007 :=
  LargeQuotientSieve.combine row13009 row13033 rfl

set_option maxRecDepth 16000 in
private theorem row13037 :
    FinalSeventhSieve.rough 11092009835083 13037+46988494=FinalSeventhSieve.rough 11092009835083 13033 :=
  LargeQuotientSieve.row (p:=13037) (q:=850809989) (s:=29168) (rank:=43621270) (tiny:=1552) (pairs:=3368775)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 850809989 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13037 : FinalSeventhSieve.rough 11092009835083 13037+141097920=FinalSeventhSieve.rough 11092009835083 13007 :=
  LargeQuotientSieve.combine to13033 row13037 rfl

set_option maxRecDepth 16000 in
private theorem row13043 :
    FinalSeventhSieve.rough 11092009835083 13043+46961512=FinalSeventhSieve.rough 11092009835083 13037 :=
  LargeQuotientSieve.row (p:=13043) (q:=850418602) (s:=29161) (rank:=43602215) (tiny:=1553) (pairs:=3360849)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 850418602 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13043 : FinalSeventhSieve.rough 11092009835083 13043+188059432=FinalSeventhSieve.rough 11092009835083 13007 :=
  LargeQuotientSieve.combine to13037 row13043 rfl

set_option maxRecDepth 16000 in
private theorem row13049 :
    FinalSeventhSieve.rough 11092009835083 13049+46934641=FinalSeventhSieve.rough 11092009835083 13043 :=
  LargeQuotientSieve.row (p:=13049) (q:=850027575) (s:=29155) (rank:=43583308) (tiny:=1554) (pairs:=3352886)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 850027575 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13049 : FinalSeventhSieve.rough 11092009835083 13049+234994073=FinalSeventhSieve.rough 11092009835083 13007 :=
  LargeQuotientSieve.combine to13043 row13049 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13049+234994073=FinalSeventhSieve.rough 11092009835083 13007 := to13049

end Tail11092009835083From13007To13049
