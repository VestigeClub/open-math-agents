import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1000000000-1025000000»

/-! Exact changes for sieve primes 1340 through 1344. -/
open Finset
namespace Tail11092009835083From11057To11087

set_option maxRecDepth 16000 in
private theorem row11059 :
    FinalSeventhSieve.rough 11092009835083 11059+56985257=FinalSeventhSieve.rough 11092009835083 11057 :=
  LargeQuotientSieve.row (p:=11059) (q:=1002984884) (s:=31669) (rank:=50991433) (tiny:=1339) (pairs:=5995162)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1002984884 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row11069 :
    FinalSeventhSieve.rough 11092009835083 11069+56925218=FinalSeventhSieve.rough 11092009835083 11059 :=
  LargeQuotientSieve.row (p:=11069) (q:=1002078763) (s:=31655) (rank:=50947718) (tiny:=1340) (pairs:=5978839)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1002078763 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11069 : FinalSeventhSieve.rough 11092009835083 11069+113910475=FinalSeventhSieve.rough 11092009835083 11057 :=
  LargeQuotientSieve.combine row11059 row11069 rfl

set_option maxRecDepth 16000 in
private theorem row11071 :
    FinalSeventhSieve.rough 11092009835083 11071+56907324=FinalSeventhSieve.rough 11092009835083 11069 :=
  LargeQuotientSieve.row (p:=11071) (q:=1001897735) (s:=31652) (rank:=50939049) (tiny:=1341) (pairs:=5969615)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1001897735 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11071 : FinalSeventhSieve.rough 11092009835083 11071+170817799=FinalSeventhSieve.rough 11092009835083 11057 :=
  LargeQuotientSieve.combine to11069 row11071 rfl

set_option maxRecDepth 16000 in
private theorem row11083 :
    FinalSeventhSieve.rough 11092009835083 11083+56836989=FinalSeventhSieve.rough 11092009835083 11071 :=
  LargeQuotientSieve.row (p:=11083) (q:=1000812941) (s:=31635) (rank:=50886651) (tiny:=1342) (pairs:=5951679)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1000812941 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11083 : FinalSeventhSieve.rough 11092009835083 11083+227654788=FinalSeventhSieve.rough 11092009835083 11057 :=
  LargeQuotientSieve.combine to11071 row11083 rfl

set_option maxRecDepth 16000 in
private theorem row11087 :
    FinalSeventhSieve.rough 11092009835083 11087+56808584=FinalSeventhSieve.rough 11092009835083 11083 :=
  LargeQuotientSieve.row (p:=11087) (q:=1000451865) (s:=31629) (rank:=50869258) (tiny:=1343) (pairs:=5940668)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1000451865 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11087 : FinalSeventhSieve.rough 11092009835083 11087+284463372=FinalSeventhSieve.rough 11092009835083 11057 :=
  LargeQuotientSieve.combine to11083 row11087 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 11087+284463372=FinalSeventhSieve.rough 11092009835083 11057 := to11087

end Tail11092009835083From11057To11087
