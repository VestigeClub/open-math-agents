import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-950000000-975000000»

/-! Exact changes for sieve primes 1398 through 1400. -/
open Finset
namespace Tail11092009835083From11617To11657

set_option maxRecDepth 16000 in
private theorem row11621 :
    FinalSeventhSieve.rough 11092009835083 11621+53774922=FinalSeventhSieve.rough 11092009835083 11617 :=
  LargeQuotientSieve.row (p:=11621) (q:=954479806) (s:=30894) (rank:=48648123) (tiny:=1397) (pairs:=5128195)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 954479806 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row11633 :
    FinalSeventhSieve.rough 11092009835083 11633+53711736=FinalSeventhSieve.rough 11092009835083 11621 :=
  LargeQuotientSieve.row (p:=11633) (q:=953495214) (s:=30878) (rank:=48600464) (tiny:=1398) (pairs:=5112669)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 953495214 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11633 : FinalSeventhSieve.rough 11092009835083 11633+107486658=FinalSeventhSieve.rough 11092009835083 11617 :=
  LargeQuotientSieve.combine row11621 row11633 rfl

set_option maxRecDepth 16000 in
private theorem row11657 :
    FinalSeventhSieve.rough 11092009835083 11657+53592324=FinalSeventhSieve.rough 11092009835083 11633 :=
  LargeQuotientSieve.row (p:=11657) (q:=951532112) (s:=30846) (rank:=48505408) (tiny:=1399) (pairs:=5088314)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 951532112 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11657 : FinalSeventhSieve.rough 11092009835083 11657+161078982=FinalSeventhSieve.rough 11092009835083 11617 :=
  LargeQuotientSieve.combine to11633 row11657 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 11657+161078982=FinalSeventhSieve.rough 11092009835083 11617 := to11657

end Tail11092009835083From11617To11657
