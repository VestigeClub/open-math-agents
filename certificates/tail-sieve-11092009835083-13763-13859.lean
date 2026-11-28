import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-800000000-825000000»

/-! Exact changes for sieve primes 1630 through 1637. -/
open Finset
namespace Tail11092009835083From13763To13859

set_option maxRecDepth 16000 in
private theorem row13781 :
    FinalSeventhSieve.rough 11092009835083 13781+44064610=FinalSeventhSieve.rough 11092009835083 13763 :=
  LargeQuotientSieve.row (p:=13781) (q:=804876992) (s:=28370) (rank:=41384151) (tiny:=1629) (pairs:=2682087)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 804876992 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row13789 :
    FinalSeventhSieve.rough 11092009835083 13789+44034300=FinalSeventhSieve.rough 11092009835083 13781 :=
  LargeQuotientSieve.row (p:=13789) (q:=804410025) (s:=28362) (rank:=41361261) (tiny:=1630) (pairs:=2674668)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 804410025 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13789 : FinalSeventhSieve.rough 11092009835083 13789+88098910=FinalSeventhSieve.rough 11092009835083 13763 :=
  LargeQuotientSieve.combine row13781 row13789 rfl

set_option maxRecDepth 16000 in
private theorem row13799 :
    FinalSeventhSieve.rough 11092009835083 13799+43997606=FinalSeventhSieve.rough 11092009835083 13789 :=
  LargeQuotientSieve.row (p:=13799) (q:=803827076) (s:=28351) (rank:=41332804) (tiny:=1631) (pairs:=2666432)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 803827076 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13799 : FinalSeventhSieve.rough 11092009835083 13799+132096516=FinalSeventhSieve.rough 11092009835083 13763 :=
  LargeQuotientSieve.combine to13789 row13799 rfl

set_option maxRecDepth 16000 in
private theorem row13807 :
    FinalSeventhSieve.rough 11092009835083 13807+43967406=FinalSeventhSieve.rough 11092009835083 13799 :=
  LargeQuotientSieve.row (p:=13807) (q:=803361326) (s:=28343) (rank:=41310093) (tiny:=1632) (pairs:=2658944)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 803361326 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13807 : FinalSeventhSieve.rough 11092009835083 13807+176063922=FinalSeventhSieve.rough 11092009835083 13763 :=
  LargeQuotientSieve.combine to13799 row13807 rfl

set_option maxRecDepth 16000 in
private theorem row13829 :
    FinalSeventhSieve.rough 11092009835083 13829+43892295=FinalSeventhSieve.rough 11092009835083 13807 :=
  LargeQuotientSieve.row (p:=13829) (q:=802083291) (s:=28321) (rank:=41247940) (tiny:=1633) (pairs:=2645987)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 802083291 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13829 : FinalSeventhSieve.rough 11092009835083 13829+219956217=FinalSeventhSieve.rough 11092009835083 13763 :=
  LargeQuotientSieve.combine to13807 row13829 rfl

set_option maxRecDepth 16000 in
private theorem row13831 :
    FinalSeventhSieve.rough 11092009835083 13831+43881586=FinalSeventhSieve.rough 11092009835083 13829 :=
  LargeQuotientSieve.row (p:=13831) (q:=801967307) (s:=28319) (rank:=41242261) (tiny:=1634) (pairs:=2640958)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 801967307 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13831 : FinalSeventhSieve.rough 11092009835083 13831+263837803=FinalSeventhSieve.rough 11092009835083 13763 :=
  LargeQuotientSieve.combine to13829 row13831 rfl

set_option maxRecDepth 16000 in
private theorem row13841 :
    FinalSeventhSieve.rough 11092009835083 13841+43845176=FinalSeventhSieve.rough 11092009835083 13831 :=
  LargeQuotientSieve.row (p:=13841) (q:=801387893) (s:=28308) (rank:=41214069) (tiny:=1635) (pairs:=2632741)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 801387893 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13841 : FinalSeventhSieve.rough 11092009835083 13841+307682979=FinalSeventhSieve.rough 11092009835083 13763 :=
  LargeQuotientSieve.combine to13831 row13841 rfl

set_option maxRecDepth 16000 in
private theorem row13859 :
    FinalSeventhSieve.rough 11092009835083 13859+43783048=FinalSeventhSieve.rough 11092009835083 13841 :=
  LargeQuotientSieve.row (p:=13859) (q:=800347054) (s:=28290) (rank:=41163175) (tiny:=1636) (pairs:=2621508)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 800347054 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13859 : FinalSeventhSieve.rough 11092009835083 13859+351466027=FinalSeventhSieve.rough 11092009835083 13763 :=
  LargeQuotientSieve.combine to13841 row13859 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13859+351466027=FinalSeventhSieve.rough 11092009835083 13763 := to13859

end Tail11092009835083From13763To13859
