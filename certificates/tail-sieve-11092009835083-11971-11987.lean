import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-925000000-950000000»

/-! Exact changes for sieve primes 1437 through 1438. -/
open Finset
namespace Tail11092009835083From11971To11987

set_option maxRecDepth 16000 in
private theorem row11981 :
    FinalSeventhSieve.rough 11092009835083 11981+51882128=FinalSeventhSieve.rough 11092009835083 11971 :=
  LargeQuotientSieve.row (p:=11981) (q:=925800002) (s:=30426) (rank:=47260481) (tiny:=1436) (pairs:=4623082)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 925800002 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row11987 :
    FinalSeventhSieve.rough 11092009835083 11987+51849500=FinalSeventhSieve.rough 11092009835083 11981 :=
  LargeQuotientSieve.row (p:=11987) (q:=925336600) (s:=30419) (rank:=47237963) (tiny:=1437) (pairs:=4612973)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 925336600 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11987 : FinalSeventhSieve.rough 11092009835083 11987+103731628=FinalSeventhSieve.rough 11092009835083 11971 :=
  LargeQuotientSieve.combine row11981 row11987 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 11987+103731628=FinalSeventhSieve.rough 11092009835083 11971 := to11987

end Tail11092009835083From11971To11987
