import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-800000000-825000000»

/-! Exact changes for sieve primes 1606 through 1617. -/
open Finset
namespace Tail11092009835083From13567To13687

set_option maxRecDepth 16000 in
private theorem row13577 :
    FinalSeventhSieve.rough 11092009835083 13577+44843596=FinalSeventhSieve.rough 11092009835083 13567 :=
  LargeQuotientSieve.row (p:=13577) (q:=816970599) (s:=28582) (rank:=41973993) (tiny:=1605) (pairs:=2871207)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 816970599 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row13591 :
    FinalSeventhSieve.rough 11092009835083 13591+44792117=FinalSeventhSieve.rough 11092009835083 13577 :=
  LargeQuotientSieve.row (p:=13591) (q:=816129043) (s:=28567) (rank:=41932879) (tiny:=1606) (pairs:=2860843)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 816129043 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13591 : FinalSeventhSieve.rough 11092009835083 13591+89635713=FinalSeventhSieve.rough 11092009835083 13567 :=
  LargeQuotientSieve.combine row13577 row13591 rfl

set_option maxRecDepth 16000 in
private theorem row13597 :
    FinalSeventhSieve.rough 11092009835083 13597+44767556=FinalSeventhSieve.rough 11092009835083 13591 :=
  LargeQuotientSieve.row (p:=13597) (q:=815768907) (s:=28561) (rank:=41915304) (tiny:=1607) (pairs:=2853858)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 815768907 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13597 : FinalSeventhSieve.rough 11092009835083 13597+134403269=FinalSeventhSieve.rough 11092009835083 13567 :=
  LargeQuotientSieve.combine to13591 row13597 rfl

set_option maxRecDepth 16000 in
private theorem row13613 :
    FinalSeventhSieve.rough 11092009835083 13613+44709585=FinalSeventhSieve.rough 11092009835083 13597 :=
  LargeQuotientSieve.row (p:=13613) (q:=814810095) (s:=28544) (rank:=41868499) (tiny:=1608) (pairs:=2842693)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 814810095 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13613 : FinalSeventhSieve.rough 11092009835083 13613+179112854=FinalSeventhSieve.rough 11092009835083 13567 :=
  LargeQuotientSieve.combine to13597 row13613 rfl

set_option maxRecDepth 16000 in
private theorem row13619 :
    FinalSeventhSieve.rough 11092009835083 13619+44685025=FinalSeventhSieve.rough 11092009835083 13613 :=
  LargeQuotientSieve.row (p:=13619) (q:=814451122) (s:=28538) (rank:=41850941) (tiny:=1609) (pairs:=2835692)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 814451122 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13619 : FinalSeventhSieve.rough 11092009835083 13619+223797879=FinalSeventhSieve.rough 11092009835083 13567 :=
  LargeQuotientSieve.combine to13613 row13619 rfl

set_option maxRecDepth 16000 in
private theorem row13627 :
    FinalSeventhSieve.rough 11092009835083 13627+44653900=FinalSeventhSieve.rough 11092009835083 13619 :=
  LargeQuotientSieve.row (p:=13627) (q:=813972982) (s:=28530) (rank:=41827612) (tiny:=1610) (pairs:=2827897)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 813972982 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13627 : FinalSeventhSieve.rough 11092009835083 13627+268451779=FinalSeventhSieve.rough 11092009835083 13567 :=
  LargeQuotientSieve.combine to13619 row13627 rfl

set_option maxRecDepth 16000 in
private theorem row13633 :
    FinalSeventhSieve.rough 11092009835083 13633+44629439=FinalSeventhSieve.rough 11092009835083 13627 :=
  LargeQuotientSieve.row (p:=13633) (q:=813614746) (s:=28523) (rank:=41810133) (tiny:=1611) (pairs:=2820916)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 813614746 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13633 : FinalSeventhSieve.rough 11092009835083 13633+313081218=FinalSeventhSieve.rough 11092009835083 13567 :=
  LargeQuotientSieve.combine to13627 row13633 rfl

set_option maxRecDepth 16000 in
private theorem row13649 :
    FinalSeventhSieve.rough 11092009835083 13649+44571883=FinalSeventhSieve.rough 11092009835083 13633 :=
  LargeQuotientSieve.row (p:=13649) (q:=812660988) (s:=28507) (rank:=41763673) (tiny:=1612) (pairs:=2809821)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 812660988 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13649 : FinalSeventhSieve.rough 11092009835083 13649+357653101=FinalSeventhSieve.rough 11092009835083 13567 :=
  LargeQuotientSieve.combine to13633 row13649 rfl

set_option maxRecDepth 16000 in
private theorem row13669 :
    FinalSeventhSieve.rough 11092009835083 13669+44501467=FinalSeventhSieve.rough 11092009835083 13649 :=
  LargeQuotientSieve.row (p:=13669) (q:=811471931) (s:=28486) (rank:=41706012) (tiny:=1613) (pairs:=2797067)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 811471931 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13669 : FinalSeventhSieve.rough 11092009835083 13669+402154568=FinalSeventhSieve.rough 11092009835083 13567 :=
  LargeQuotientSieve.combine to13649 row13669 rfl

set_option maxRecDepth 16000 in
private theorem row13679 :
    FinalSeventhSieve.rough 11092009835083 13679+44464074=FinalSeventhSieve.rough 11092009835083 13669 :=
  LargeQuotientSieve.row (p:=13679) (q:=810878707) (s:=28475) (rank:=41677094) (tiny:=1614) (pairs:=2788593)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 810878707 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13679 : FinalSeventhSieve.rough 11092009835083 13679+446618642=FinalSeventhSieve.rough 11092009835083 13567 :=
  LargeQuotientSieve.combine to13669 row13679 rfl

set_option maxRecDepth 16000 in
private theorem row13681 :
    FinalSeventhSieve.rough 11092009835083 13681+44453056=FinalSeventhSieve.rough 11092009835083 13679 :=
  LargeQuotientSieve.row (p:=13681) (q:=810760166) (s:=28473) (rank:=41671246) (tiny:=1615) (pairs:=2783424)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 810760166 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13681 : FinalSeventhSieve.rough 11092009835083 13681+491071698=FinalSeventhSieve.rough 11092009835083 13567 :=
  LargeQuotientSieve.combine to13679 row13681 rfl

set_option maxRecDepth 16000 in
private theorem row13687 :
    FinalSeventhSieve.rough 11092009835083 13687+44428893=FinalSeventhSieve.rough 11092009835083 13681 :=
  LargeQuotientSieve.row (p:=13687) (q:=810404751) (s:=28467) (rank:=41653985) (tiny:=1616) (pairs:=2776523)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 810404751 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13687 : FinalSeventhSieve.rough 11092009835083 13687+535500591=FinalSeventhSieve.rough 11092009835083 13567 :=
  LargeQuotientSieve.combine to13681 row13687 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13687+535500591=FinalSeventhSieve.rough 11092009835083 13567 := to13687

end Tail11092009835083From13567To13687
