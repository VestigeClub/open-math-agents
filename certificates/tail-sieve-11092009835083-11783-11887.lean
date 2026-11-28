import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-925000000-950000000»

/-! Exact changes for sieve primes 1413 through 1424. -/
open Finset
namespace Tail11092009835083From11783To11887

set_option maxRecDepth 16000 in
private theorem row11789 :
    FinalSeventhSieve.rough 11092009835083 11789+52896026=FinalSeventhSieve.rough 11092009835083 11783 :=
  LargeQuotientSieve.row (p:=11789) (q:=940877923) (s:=30673) (rank:=47990101) (tiny:=1412) (pairs:=4907336)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 940877923 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row11801 :
    FinalSeventhSieve.rough 11092009835083 11801+52834607=FinalSeventhSieve.rough 11092009835083 11789 :=
  LargeQuotientSieve.row (p:=11801) (q:=939921179) (s:=30658) (rank:=47943660) (tiny:=1413) (pairs:=4892359)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 939921179 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11801 : FinalSeventhSieve.rough 11092009835083 11801+105730633=FinalSeventhSieve.rough 11092009835083 11783 :=
  LargeQuotientSieve.combine row11789 row11801 rfl

set_option maxRecDepth 16000 in
private theorem row11807 :
    FinalSeventhSieve.rough 11092009835083 11807+52800947=FinalSeventhSieve.rough 11092009835083 11801 :=
  LargeQuotientSieve.row (p:=11807) (q:=939443536) (s:=30650) (rank:=47920707) (tiny:=1414) (pairs:=4881653)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 939443536 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11807 : FinalSeventhSieve.rough 11092009835083 11807+158531580=FinalSeventhSieve.rough 11092009835083 11783 :=
  LargeQuotientSieve.combine to11801 row11807 rfl

set_option maxRecDepth 16000 in
private theorem row11813 :
    FinalSeventhSieve.rough 11092009835083 11813+52767274=FinalSeventhSieve.rough 11092009835083 11807 :=
  LargeQuotientSieve.row (p:=11813) (q:=938966378) (s:=30642) (rank:=47897694) (tiny:=1415) (pairs:=4870994)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 938966378 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11813 : FinalSeventhSieve.rough 11092009835083 11813+211298854=FinalSeventhSieve.rough 11092009835083 11783 :=
  LargeQuotientSieve.combine to11807 row11813 rfl

set_option maxRecDepth 16000 in
private theorem row11821 :
    FinalSeventhSieve.rough 11092009835083 11821+52724433=FinalSeventhSieve.rough 11092009835083 11813 :=
  LargeQuotientSieve.row (p:=11821) (q:=938330922) (s:=30632) (rank:=47866895) (tiny:=1416) (pairs:=4858953)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 938330922 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11821 : FinalSeventhSieve.rough 11092009835083 11821+264023287=FinalSeventhSieve.rough 11092009835083 11783 :=
  LargeQuotientSieve.combine to11813 row11821 rfl

set_option maxRecDepth 16000 in
private theorem row11827 :
    FinalSeventhSieve.rough 11092009835083 11827+52690829=FinalSeventhSieve.rough 11092009835083 11821 :=
  LargeQuotientSieve.row (p:=11827) (q:=937854894) (s:=30624) (rank:=47843861) (tiny:=1417) (pairs:=4848384)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 937854894 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11827 : FinalSeventhSieve.rough 11092009835083 11827+316714116=FinalSeventhSieve.rough 11092009835083 11783 :=
  LargeQuotientSieve.combine to11821 row11827 rfl

set_option maxRecDepth 16000 in
private theorem row11831 :
    FinalSeventhSieve.rough 11092009835083 11831+52666307=FinalSeventhSieve.rough 11092009835083 11827 :=
  LargeQuotientSieve.row (p:=11831) (q:=937537810) (s:=30619) (rank:=47828545) (tiny:=1418) (pairs:=4839179)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 937537810 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11831 : FinalSeventhSieve.rough 11092009835083 11831+369380423=FinalSeventhSieve.rough 11092009835083 11783 :=
  LargeQuotientSieve.combine to11827 row11831 rfl

set_option maxRecDepth 16000 in
private theorem row11833 :
    FinalSeventhSieve.rough 11092009835083 11833+52650874=FinalSeventhSieve.rough 11092009835083 11831 :=
  LargeQuotientSieve.row (p:=11833) (q:=937379348) (s:=30616) (rank:=47820854) (tiny:=1419) (pairs:=4831438)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 937379348 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11833 : FinalSeventhSieve.rough 11092009835083 11833+422031297=FinalSeventhSieve.rough 11092009835083 11783 :=
  LargeQuotientSieve.combine to11831 row11833 rfl

set_option maxRecDepth 16000 in
private theorem row11839 :
    FinalSeventhSieve.rough 11092009835083 11839+52617407=FinalSeventhSieve.rough 11092009835083 11833 :=
  LargeQuotientSieve.row (p:=11839) (q:=936904285) (s:=30608) (rank:=47797912) (tiny:=1420) (pairs:=4820914)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 936904285 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11839 : FinalSeventhSieve.rough 11092009835083 11839+474648704=FinalSeventhSieve.rough 11092009835083 11783 :=
  LargeQuotientSieve.combine to11833 row11839 rfl

set_option maxRecDepth 16000 in
private theorem row11863 :
    FinalSeventhSieve.rough 11092009835083 11863+52502453=FinalSeventhSieve.rough 11092009835083 11839 :=
  LargeQuotientSieve.row (p:=11863) (q:=935008837) (s:=30577) (rank:=47706097) (tiny:=1421) (pairs:=4797776)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 935008837 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11863 : FinalSeventhSieve.rough 11092009835083 11863+527151157=FinalSeventhSieve.rough 11092009835083 11783 :=
  LargeQuotientSieve.combine to11839 row11863 rfl

set_option maxRecDepth 16000 in
private theorem row11867 :
    FinalSeventhSieve.rough 11092009835083 11867+52478076=FinalSeventhSieve.rough 11092009835083 11863 :=
  LargeQuotientSieve.row (p:=11867) (q:=934693674) (s:=30572) (rank:=47690862) (tiny:=1422) (pairs:=4788635)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 934693674 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11867 : FinalSeventhSieve.rough 11092009835083 11867+579629233=FinalSeventhSieve.rough 11092009835083 11783 :=
  LargeQuotientSieve.combine to11863 row11867 rfl

set_option maxRecDepth 16000 in
private theorem row11887 :
    FinalSeventhSieve.rough 11092009835083 11887+52381598=FinalSeventhSieve.rough 11092009835083 11867 :=
  LargeQuotientSieve.row (p:=11887) (q:=933121042) (s:=30547) (rank:=47614645) (tiny:=1423) (pairs:=4768375)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 933121042 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11887 : FinalSeventhSieve.rough 11092009835083 11887+632010831=FinalSeventhSieve.rough 11092009835083 11783 :=
  LargeQuotientSieve.combine to11867 row11887 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 11887+632010831=FinalSeventhSieve.rough 11092009835083 11783 := to11887

end Tail11092009835083From11783To11887
