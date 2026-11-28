import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-775000000-800000000»

/-! Exact changes for sieve primes 1650 through 1661. -/
open Finset
namespace Tail11092009835083From13963To14083

set_option maxRecDepth 16000 in
private theorem row13967 :
    FinalSeventhSieve.rough 11092009835083 13967+43385467=FinalSeventhSieve.rough 11092009835083 13963 :=
  LargeQuotientSieve.row (p:=13967) (q:=794158361) (s:=28180) (rank:=40861245) (tiny:=1649) (pairs:=2525870)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 794158361 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row13997 :
    FinalSeventhSieve.rough 11092009835083 13997+43286912=FinalSeventhSieve.rough 11092009835083 13967 :=
  LargeQuotientSieve.row (p:=13997) (q:=792456228) (s:=28150) (rank:=40778104) (tiny:=1650) (pairs:=2510457)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 792456228 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13997 : FinalSeventhSieve.rough 11092009835083 13997+86672379=FinalSeventhSieve.rough 11092009835083 13963 :=
  LargeQuotientSieve.combine row13967 row13997 rfl

set_option maxRecDepth 16000 in
private theorem row13999 :
    FinalSeventhSieve.rough 11092009835083 13999+43276562=FinalSeventhSieve.rough 11092009835083 13997 :=
  LargeQuotientSieve.row (p:=13999) (q:=792343012) (s:=28148) (rank:=40772598) (tiny:=1651) (pairs:=2505614)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 792343012 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13999 : FinalSeventhSieve.rough 11092009835083 13999+129948941=FinalSeventhSieve.rough 11092009835083 13963 :=
  LargeQuotientSieve.combine to13997 row13999 rfl

set_option maxRecDepth 16000 in
private theorem row14009 :
    FinalSeventhSieve.rough 11092009835083 14009+43241123=FinalSeventhSieve.rough 11092009835083 13999 :=
  LargeQuotientSieve.row (p:=14009) (q:=791777417) (s:=28138) (rank:=40744994) (tiny:=1652) (pairs:=2497780)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 791777417 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14009 : FinalSeventhSieve.rough 11092009835083 14009+173190064=FinalSeventhSieve.rough 11092009835083 13963 :=
  LargeQuotientSieve.combine to13999 row14009 rfl

set_option maxRecDepth 16000 in
private theorem row14011 :
    FinalSeventhSieve.rough 11092009835083 14011+43230821=FinalSeventhSieve.rough 11092009835083 14009 :=
  LargeQuotientSieve.row (p:=14011) (q:=791664394) (s:=28136) (rank:=40739505) (tiny:=1653) (pairs:=2492968)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 791664394 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14011 : FinalSeventhSieve.rough 11092009835083 14011+216420885=FinalSeventhSieve.rough 11092009835083 13963 :=
  LargeQuotientSieve.combine to14009 row14011 rfl

set_option maxRecDepth 16000 in
private theorem row14029 :
    FinalSeventhSieve.rough 11092009835083 14029+43170473=FinalSeventhSieve.rough 11092009835083 14011 :=
  LargeQuotientSieve.row (p:=14029) (q:=790648644) (s:=28118) (rank:=40689970) (tiny:=1654) (pairs:=2482156)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 790648644 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14029 : FinalSeventhSieve.rough 11092009835083 14029+259591358=FinalSeventhSieve.rough 11092009835083 13963 :=
  LargeQuotientSieve.combine to14011 row14029 rfl

set_option maxRecDepth 16000 in
private theorem row14033 :
    FinalSeventhSieve.rough 11092009835083 14033+43153869=FinalSeventhSieve.rough 11092009835083 14029 :=
  LargeQuotientSieve.row (p:=14033) (q:=790423276) (s:=28114) (rank:=40678890) (tiny:=1655) (pairs:=2476633)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 790423276 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14033 : FinalSeventhSieve.rough 11092009835083 14033+302745227=FinalSeventhSieve.rough 11092009835083 13963 :=
  LargeQuotientSieve.combine to14029 row14033 rfl

set_option maxRecDepth 16000 in
private theorem row14051 :
    FinalSeventhSieve.rough 11092009835083 14051+43093656=FinalSeventhSieve.rough 11092009835083 14033 :=
  LargeQuotientSieve.row (p:=14051) (q:=789410706) (s:=28096) (rank:=40629385) (tiny:=1656) (pairs:=2465926)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 789410706 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14051 : FinalSeventhSieve.rough 11092009835083 14051+345838883=FinalSeventhSieve.rough 11092009835083 13963 :=
  LargeQuotientSieve.combine to14033 row14051 rfl

set_option maxRecDepth 16000 in
private theorem row14057 :
    FinalSeventhSieve.rough 11092009835083 14057+43070908=FinalSeventhSieve.rough 11092009835083 14051 :=
  LargeQuotientSieve.row (p:=14057) (q:=789073759) (s:=28090) (rank:=40612867) (tiny:=1657) (pairs:=2459697)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 789073759 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14057 : FinalSeventhSieve.rough 11092009835083 14057+388909791=FinalSeventhSieve.rough 11092009835083 13963 :=
  LargeQuotientSieve.combine to14051 row14057 rfl

set_option maxRecDepth 16000 in
private theorem row14071 :
    FinalSeventhSieve.rough 11092009835083 14071+43023267=FinalSeventhSieve.rough 11092009835083 14057 :=
  LargeQuotientSieve.row (p:=14071) (q:=788288667) (s:=28076) (rank:=40574398) (tiny:=1658) (pairs:=2450526)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 788288667 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14071 : FinalSeventhSieve.rough 11092009835083 14071+431933058=FinalSeventhSieve.rough 11092009835083 13963 :=
  LargeQuotientSieve.combine to14057 row14071 rfl

set_option maxRecDepth 16000 in
private theorem row14081 :
    FinalSeventhSieve.rough 11092009835083 14081+42988358=FinalSeventhSieve.rough 11092009835083 14071 :=
  LargeQuotientSieve.row (p:=14081) (q:=787728842) (s:=28066) (rank:=40547115) (tiny:=1659) (pairs:=2442901)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 787728842 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14081 : FinalSeventhSieve.rough 11092009835083 14081+474921416=FinalSeventhSieve.rough 11092009835083 13963 :=
  LargeQuotientSieve.combine to14071 row14081 rfl

set_option maxRecDepth 16000 in
private theorem row14083 :
    FinalSeventhSieve.rough 11092009835083 14083+42978185=FinalSeventhSieve.rough 11092009835083 14081 :=
  LargeQuotientSieve.row (p:=14083) (q:=787616973) (s:=28064) (rank:=40541711) (tiny:=1660) (pairs:=2438133)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 787616973 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14083 : FinalSeventhSieve.rough 11092009835083 14083+517899601=FinalSeventhSieve.rough 11092009835083 13963 :=
  LargeQuotientSieve.combine to14081 row14083 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 14083+517899601=FinalSeventhSieve.rough 11092009835083 13963 := to14083

end Tail11092009835083From13963To14083
