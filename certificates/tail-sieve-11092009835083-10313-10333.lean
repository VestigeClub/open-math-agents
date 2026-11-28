import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 1266 through 1268. -/
open Finset
namespace Tail11092009835083From10313To10333

set_option maxRecDepth 16000 in
private theorem row10321 :
    FinalSeventhSieve.rough 11092009835083 10321+61768376=FinalSeventhSieve.rough 11092009835083 10313 :=
  LargeQuotientSieve.row (p:=10321) (q:=1074703016) (s:=32782) (rank:=54446301) (tiny:=1265) (pairs:=7323339)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1074703016 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row10331 :
    FinalSeventhSieve.rough 11092009835083 10331+61698597=FinalSeventhSieve.rough 11092009835083 10321 :=
  LargeQuotientSieve.row (p:=10331) (q:=1073662746) (s:=32766) (rank:=54396195) (tiny:=1266) (pairs:=7303667)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1073662746 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10331 : FinalSeventhSieve.rough 11092009835083 10331+123466973=FinalSeventhSieve.rough 11092009835083 10313 :=
  LargeQuotientSieve.combine row10321 row10331 rfl

set_option maxRecDepth 16000 in
private theorem row10333 :
    FinalSeventhSieve.rough 11092009835083 10333+61677847=FinalSeventhSieve.rough 11092009835083 10331 :=
  LargeQuotientSieve.row (p:=10333) (q:=1073454934) (s:=32763) (rank:=54386318) (tiny:=1267) (pairs:=7292795)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1073454934 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10333 : FinalSeventhSieve.rough 11092009835083 10333+185144820=FinalSeventhSieve.rough 11092009835083 10313 :=
  LargeQuotientSieve.combine to10331 row10333 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10333+185144820=FinalSeventhSieve.rough 11092009835083 10313 := to10333

end Tail11092009835083From10313To10333
