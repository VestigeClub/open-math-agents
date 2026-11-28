import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-850000000-875000000»

/-! Exact changes for sieve primes 1515 through 1526. -/
open Finset
namespace Tail11092009835083From12671To12799

set_option maxRecDepth 16000 in
private theorem row12689 :
    FinalSeventhSieve.rough 11092009835083 12689+48499177=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.row (p:=12689) (q:=874143733) (s:=29565) (rank:=44755124) (tiny:=1514) (pairs:=3745566)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 874143733 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row12697 :
    FinalSeventhSieve.rough 11092009835083 12697+48462823=FinalSeventhSieve.rough 11092009835083 12689 :=
  LargeQuotientSieve.row (p:=12697) (q:=873592961) (s:=29556) (rank:=44728495) (tiny:=1515) (pairs:=3735842)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 873592961 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12697 : FinalSeventhSieve.rough 11092009835083 12697+96962000=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine row12689 row12697 rfl

set_option maxRecDepth 16000 in
private theorem row12703 :
    FinalSeventhSieve.rough 11092009835083 12703+48434114=FinalSeventhSieve.rough 11092009835083 12697 :=
  LargeQuotientSieve.row (p:=12703) (q:=873180338) (s:=29549) (rank:=44708386) (tiny:=1516) (pairs:=3727243)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 873180338 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12703 : FinalSeventhSieve.rough 11092009835083 12703+145396114=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine to12697 row12703 rfl

set_option maxRecDepth 16000 in
private theorem row12713 :
    FinalSeventhSieve.rough 11092009835083 12713+48389892=FinalSeventhSieve.rough 11092009835083 12703 :=
  LargeQuotientSieve.row (p:=12713) (q:=872493497) (s:=29538) (rank:=44674878) (tiny:=1517) (pairs:=3716530)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 872493497 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12713 : FinalSeventhSieve.rough 11092009835083 12713+193786006=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine to12703 row12713 rfl

set_option maxRecDepth 16000 in
private theorem row12721 :
    FinalSeventhSieve.rough 11092009835083 12721+48353622=FinalSeventhSieve.rough 11092009835083 12713 :=
  LargeQuotientSieve.row (p:=12721) (q:=871944802) (s:=29528) (rank:=44648272) (tiny:=1518) (pairs:=3706867)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 871944802 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12721 : FinalSeventhSieve.rough 11092009835083 12721+242139628=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine to12713 row12721 rfl

set_option maxRecDepth 16000 in
private theorem row12739 :
    FinalSeventhSieve.rough 11092009835083 12739+48278851=FinalSeventhSieve.rough 11092009835083 12721 :=
  LargeQuotientSieve.row (p:=12739) (q:=870712758) (s:=29507) (rank:=44588559) (tiny:=1519) (pairs:=3691810)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 870712758 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12739 : FinalSeventhSieve.rough 11092009835083 12739+290418479=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine to12721 row12739 rfl

set_option maxRecDepth 16000 in
private theorem row12743 :
    FinalSeventhSieve.rough 11092009835083 12743+48258109=FinalSeventhSieve.rough 11092009835083 12739 :=
  LargeQuotientSieve.row (p:=12743) (q:=870439444) (s:=29503) (rank:=44575301) (tiny:=1520) (pairs:=3684327)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 870439444 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12743 : FinalSeventhSieve.rough 11092009835083 12743+338676588=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine to12739 row12743 rfl

set_option maxRecDepth 16000 in
private theorem row12757 :
    FinalSeventhSieve.rough 11092009835083 12757+48198810=FinalSeventhSieve.rough 11092009835083 12743 :=
  LargeQuotientSieve.row (p:=12757) (q:=869484191) (s:=29487) (rank:=44528750) (tiny:=1521) (pairs:=3671580)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 869484191 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12757 : FinalSeventhSieve.rough 11092009835083 12757+386875398=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine to12743 row12757 rfl

set_option maxRecDepth 16000 in
private theorem row12763 :
    FinalSeventhSieve.rough 11092009835083 12763+48170448=FinalSeventhSieve.rough 11092009835083 12757 :=
  LargeQuotientSieve.row (p:=12763) (q:=869075439) (s:=29480) (rank:=44508953) (tiny:=1522) (pairs:=3663016)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 869075439 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12763 : FinalSeventhSieve.rough 11092009835083 12763+435045846=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine to12757 row12763 rfl

set_option maxRecDepth 16000 in
private theorem row12781 :
    FinalSeventhSieve.rough 11092009835083 12781+48096119=FinalSeventhSieve.rough 11092009835083 12763 :=
  LargeQuotientSieve.row (p:=12781) (q:=867851485) (s:=29459) (rank:=44449484) (tiny:=1523) (pairs:=3648157)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 867851485 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12781 : FinalSeventhSieve.rough 11092009835083 12781+483141965=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine to12763 row12781 rfl

set_option maxRecDepth 16000 in
private theorem row12791 :
    FinalSeventhSieve.rough 11092009835083 12791+48052578=FinalSeventhSieve.rough 11092009835083 12781 :=
  LargeQuotientSieve.row (p:=12791) (q:=867172999) (s:=29447) (rank:=44416430) (tiny:=1524) (pairs:=3637671)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 867172999 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12791 : FinalSeventhSieve.rough 11092009835083 12791+531194543=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine to12781 row12791 rfl

set_option maxRecDepth 16000 in
private theorem row12799 :
    FinalSeventhSieve.rough 11092009835083 12799+48016601=FinalSeventhSieve.rough 11092009835083 12791 :=
  LargeQuotientSieve.row (p:=12799) (q:=866630973) (s:=29438) (rank:=44389961) (tiny:=1525) (pairs:=3628164)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 866630973 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12799 : FinalSeventhSieve.rough 11092009835083 12799+579211144=FinalSeventhSieve.rough 11092009835083 12671 :=
  LargeQuotientSieve.combine to12791 row12799 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 12799+579211144=FinalSeventhSieve.rough 11092009835083 12671 := to12799

end Tail11092009835083From12671To12799
