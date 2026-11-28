import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-925000000-950000000»

/-! Exact changes for sieve primes 1401 through 1412. -/
open Finset
namespace Tail11092009835083From11657To11783

set_option maxRecDepth 16000 in
private theorem row11677 :
    FinalSeventhSieve.rough 11092009835083 11677+53492070=FinalSeventhSieve.rough 11092009835083 11657 :=
  LargeQuotientSieve.row (p:=11677) (q:=949902358) (s:=30820) (rank:=48426715) (tiny:=1400) (pairs:=5066754)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 949902358 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row11681 :
    FinalSeventhSieve.rough 11092009835083 11681+53466890=FinalSeventhSieve.rough 11092009835083 11677 :=
  LargeQuotientSieve.row (p:=11681) (q:=949577076) (s:=30815) (rank:=48411041) (tiny:=1401) (pairs:=5057249)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 949577076 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11681 : FinalSeventhSieve.rough 11092009835083 11681+106958960=FinalSeventhSieve.rough 11092009835083 11657 :=
  LargeQuotientSieve.combine row11677 row11681 rfl

set_option maxRecDepth 16000 in
private theorem row11689 :
    FinalSeventhSieve.rough 11092009835083 11689+53422943=FinalSeventhSieve.rough 11092009835083 11681 :=
  LargeQuotientSieve.row (p:=11689) (q:=948927182) (s:=30804) (rank:=48379612) (tiny:=1402) (pairs:=5044732)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 948927182 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11689 : FinalSeventhSieve.rough 11092009835083 11689+160381903=FinalSeventhSieve.rough 11092009835083 11657 :=
  LargeQuotientSieve.combine to11681 row11689 rfl

set_option maxRecDepth 16000 in
private theorem row11699 :
    FinalSeventhSieve.rough 11092009835083 11699+53369921=FinalSeventhSieve.rough 11092009835083 11689 :=
  LargeQuotientSieve.row (p:=11699) (q:=948116064) (s:=30791) (rank:=48340412) (tiny:=1403) (pairs:=5030911)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 948116064 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11699 : FinalSeventhSieve.rough 11092009835083 11699+213751824=FinalSeventhSieve.rough 11092009835083 11657 :=
  LargeQuotientSieve.combine to11689 row11699 rfl

set_option maxRecDepth 16000 in
private theorem row11701 :
    FinalSeventhSieve.rough 11092009835083 11701+53354063=FinalSeventhSieve.rough 11092009835083 11699 :=
  LargeQuotientSieve.row (p:=11701) (q:=947954006) (s:=30788) (rank:=48332586) (tiny:=1404) (pairs:=5022880)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 947954006 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11701 : FinalSeventhSieve.rough 11092009835083 11701+267105887=FinalSeventhSieve.rough 11092009835083 11657 :=
  LargeQuotientSieve.combine to11699 row11701 rfl

set_option maxRecDepth 16000 in
private theorem row11717 :
    FinalSeventhSieve.rough 11092009835083 11717+53273020=FinalSeventhSieve.rough 11092009835083 11701 :=
  LargeQuotientSieve.row (p:=11717) (q:=946659540) (s:=30767) (rank:=48269802) (tiny:=1405) (pairs:=5004622)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 946659540 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11717 : FinalSeventhSieve.rough 11092009835083 11717+320378907=FinalSeventhSieve.rough 11092009835083 11657 :=
  LargeQuotientSieve.combine to11701 row11717 rfl

set_option maxRecDepth 16000 in
private theorem row11719 :
    FinalSeventhSieve.rough 11092009835083 11719+53257235=FinalSeventhSieve.rough 11092009835083 11717 :=
  LargeQuotientSieve.row (p:=11719) (q:=946497980) (s:=30765) (rank:=48261981) (tiny:=1406) (pairs:=4996659)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 946497980 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11719 : FinalSeventhSieve.rough 11092009835083 11719+373636142=FinalSeventhSieve.rough 11092009835083 11657 :=
  LargeQuotientSieve.combine to11717 row11719 rfl

set_option maxRecDepth 16000 in
private theorem row11731 :
    FinalSeventhSieve.rough 11092009835083 11731+53195115=FinalSeventhSieve.rough 11092009835083 11719 :=
  LargeQuotientSieve.row (p:=11731) (q:=945529778) (s:=30749) (rank:=48215090) (tiny:=1407) (pairs:=4981431)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 945529778 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11731 : FinalSeventhSieve.rough 11092009835083 11731+426831257=FinalSeventhSieve.rough 11092009835083 11657 :=
  LargeQuotientSieve.combine to11719 row11731 rfl

set_option maxRecDepth 16000 in
private theorem row11743 :
    FinalSeventhSieve.rough 11092009835083 11743+53133187=FinalSeventhSieve.rough 11092009835083 11731 :=
  LargeQuotientSieve.row (p:=11743) (q:=944563555) (s:=30733) (rank:=48168430) (tiny:=1408) (pairs:=4966164)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 944563555 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11743 : FinalSeventhSieve.rough 11092009835083 11743+479964444=FinalSeventhSieve.rough 11092009835083 11657 :=
  LargeQuotientSieve.combine to11731 row11743 rfl

set_option maxRecDepth 16000 in
private theorem row11777 :
    FinalSeventhSieve.rough 11092009835083 11777+52970196=FinalSeventhSieve.rough 11092009835083 11743 :=
  LargeQuotientSieve.row (p:=11777) (q:=941836616) (s:=30689) (rank:=48036416) (tiny:=1409) (pairs:=4935188)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 941836616 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11777 : FinalSeventhSieve.rough 11092009835083 11777+532934640=FinalSeventhSieve.rough 11092009835083 11657 :=
  LargeQuotientSieve.combine to11743 row11777 rfl

set_option maxRecDepth 16000 in
private theorem row11779 :
    FinalSeventhSieve.rough 11092009835083 11779+52954689=FinalSeventhSieve.rough 11092009835083 11777 :=
  LargeQuotientSieve.row (p:=11779) (q:=941676698) (s:=30686) (rank:=48028791) (tiny:=1410) (pairs:=4927307)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 941676698 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11779 : FinalSeventhSieve.rough 11092009835083 11779+585889329=FinalSeventhSieve.rough 11092009835083 11657 :=
  LargeQuotientSieve.combine to11777 row11779 rfl

set_option maxRecDepth 16000 in
private theorem row11783 :
    FinalSeventhSieve.rough 11092009835083 11783+52929839=FinalSeventhSieve.rough 11092009835083 11779 :=
  LargeQuotientSieve.row (p:=11783) (q:=941357025) (s:=30681) (rank:=48013214) (tiny:=1411) (pairs:=4918035)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 941357025 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11783 : FinalSeventhSieve.rough 11092009835083 11783+638819168=FinalSeventhSieve.rough 11092009835083 11657 :=
  LargeQuotientSieve.combine to11779 row11783 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 11783+638819168=FinalSeventhSieve.rough 11092009835083 11657 := to11783

end Tail11092009835083From11657To11783
