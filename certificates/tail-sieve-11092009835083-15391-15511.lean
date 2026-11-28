import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-700000000-725000000»

/-! Exact changes for sieve primes 1800 through 1811. -/
open Finset
namespace Tail11092009835083From15391To15511

set_option maxRecDepth 16000 in
private theorem row15401 :
    FinalSeventhSieve.rough 11092009835083 15401+38795764=FinalSeventhSieve.rough 11092009835083 15391 :=
  LargeQuotientSieve.row (p:=15401) (q:=720213611) (s:=26836) (rank:=37244474) (tiny:=1799) (pairs:=1553088)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 720213611 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row15413 :
    FinalSeventhSieve.rough 11092009835083 15413+38762402=FinalSeventhSieve.rough 11092009835083 15401 :=
  LargeQuotientSieve.row (p:=15413) (q:=719652879) (s:=26826) (rank:=37217136) (tiny:=1800) (pairs:=1547065)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 719652879 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15413 : FinalSeventhSieve.rough 11092009835083 15413+77558166=FinalSeventhSieve.rough 11092009835083 15391 :=
  LargeQuotientSieve.combine row15401 row15413 rfl

set_option maxRecDepth 16000 in
private theorem row15427 :
    FinalSeventhSieve.rough 11092009835083 15427+38723767=FinalSeventhSieve.rough 11092009835083 15413 :=
  LargeQuotientSieve.row (p:=15427) (q:=718999794) (s:=26814) (rank:=37184989) (tiny:=1801) (pairs:=1540578)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 718999794 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15427 : FinalSeventhSieve.rough 11092009835083 15427+116281933=FinalSeventhSieve.rough 11092009835083 15391 :=
  LargeQuotientSieve.combine to15413 row15427 rfl

set_option maxRecDepth 16000 in
private theorem row15439 :
    FinalSeventhSieve.rough 11092009835083 15439+38690488=FinalSeventhSieve.rough 11092009835083 15427 :=
  LargeQuotientSieve.row (p:=15439) (q:=718440950) (s:=26803) (rank:=37157675) (tiny:=1802) (pairs:=1534614)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 718440950 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15439 : FinalSeventhSieve.rough 11092009835083 15439+154972421=FinalSeventhSieve.rough 11092009835083 15391 :=
  LargeQuotientSieve.combine to15427 row15439 rfl

set_option maxRecDepth 16000 in
private theorem row15443 :
    FinalSeventhSieve.rough 11092009835083 15443+38677392=FinalSeventhSieve.rough 11092009835083 15439 :=
  LargeQuotientSieve.row (p:=15443) (q:=718254862) (s:=26800) (rank:=37148548) (tiny:=1803) (pairs:=1530646)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 718254862 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15443 : FinalSeventhSieve.rough 11092009835083 15443+193649813=FinalSeventhSieve.rough 11092009835083 15391 :=
  LargeQuotientSieve.combine to15439 row15443 rfl

set_option maxRecDepth 16000 in
private theorem row15451 :
    FinalSeventhSieve.rough 11092009835083 15451+38654227=FinalSeventhSieve.rough 11092009835083 15443 :=
  LargeQuotientSieve.row (p:=15451) (q:=717882974) (s:=26793) (rank:=37130311) (tiny:=1804) (pairs:=1525719)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 717882974 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15451 : FinalSeventhSieve.rough 11092009835083 15451+232304040=FinalSeventhSieve.rough 11092009835083 15391 :=
  LargeQuotientSieve.combine to15443 row15451 rfl

set_option maxRecDepth 16000 in
private theorem row15461 :
    FinalSeventhSieve.rough 11092009835083 15461+38625987=FinalSeventhSieve.rough 11092009835083 15451 :=
  LargeQuotientSieve.row (p:=15461) (q:=717418655) (s:=26784) (rank:=37107506) (tiny:=1805) (pairs:=1520285)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 717418655 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15461 : FinalSeventhSieve.rough 11092009835083 15461+270930027=FinalSeventhSieve.rough 11092009835083 15391 :=
  LargeQuotientSieve.combine to15451 row15461 rfl

set_option maxRecDepth 16000 in
private theorem row15467 :
    FinalSeventhSieve.rough 11092009835083 15467+38607906=FinalSeventhSieve.rough 11092009835083 15461 :=
  LargeQuotientSieve.row (p:=15467) (q:=717140352) (s:=26779) (rank:=37093837) (tiny:=1806) (pairs:=1515874)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 717140352 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15467 : FinalSeventhSieve.rough 11092009835083 15467+309537933=FinalSeventhSieve.rough 11092009835083 15391 :=
  LargeQuotientSieve.combine to15461 row15467 rfl

set_option maxRecDepth 16000 in
private theorem row15473 :
    FinalSeventhSieve.rough 11092009835083 15473+38589761=FinalSeventhSieve.rough 11092009835083 15467 :=
  LargeQuotientSieve.row (p:=15473) (q:=716862265) (s:=26774) (rank:=37080176) (tiny:=1807) (pairs:=1511391)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 716862265 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15473 : FinalSeventhSieve.rough 11092009835083 15473+348127694=FinalSeventhSieve.rough 11092009835083 15391 :=
  LargeQuotientSieve.combine to15467 row15473 rfl

set_option maxRecDepth 16000 in
private theorem row15493 :
    FinalSeventhSieve.rough 11092009835083 15493+38536571=FinalSeventhSieve.rough 11092009835083 15473 :=
  LargeQuotientSieve.row (p:=15493) (q:=715936864) (s:=26756) (rank:=37034828) (tiny:=1808) (pairs:=1503550)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 715936864 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15493 : FinalSeventhSieve.rough 11092009835083 15493+386664265=FinalSeventhSieve.rough 11092009835083 15391 :=
  LargeQuotientSieve.combine to15473 row15493 rfl

set_option maxRecDepth 16000 in
private theorem row15497 :
    FinalSeventhSieve.rough 11092009835083 15497+38523593=FinalSeventhSieve.rough 11092009835083 15493 :=
  LargeQuotientSieve.row (p:=15497) (q:=715752070) (s:=26753) (rank:=37025795) (tiny:=1809) (pairs:=1499606)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 715752070 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15497 : FinalSeventhSieve.rough 11092009835083 15497+425187858=FinalSeventhSieve.rough 11092009835083 15391 :=
  LargeQuotientSieve.combine to15493 row15497 rfl

set_option maxRecDepth 16000 in
private theorem row15511 :
    FinalSeventhSieve.rough 11092009835083 15511+38485663=FinalSeventhSieve.rough 11092009835083 15497 :=
  LargeQuotientSieve.row (p:=15511) (q:=715106043) (s:=26741) (rank:=36994159) (tiny:=1810) (pairs:=1493313)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 715106043 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15511 : FinalSeventhSieve.rough 11092009835083 15511+463673521=FinalSeventhSieve.rough 11092009835083 15391 :=
  LargeQuotientSieve.combine to15497 row15511 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 15511+463673521=FinalSeventhSieve.rough 11092009835083 15391 := to15511

end Tail11092009835083From15391To15511
