import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-750000000-775000000»

/-! Exact changes for sieve primes 1703 through 1714. -/
open Finset
namespace Tail11092009835083From14537To14633

set_option maxRecDepth 16000 in
private theorem row14543 :
    FinalSeventhSieve.rough 11092009835083 14543+41442399=FinalSeventhSieve.rough 11092009835083 14537 :=
  LargeQuotientSieve.row (p:=14543) (q:=762704382) (s:=27617) (rank:=39324590) (tiny:=1702) (pairs:=2119510)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 762704382 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row14549 :
    FinalSeventhSieve.rough 11092009835083 14549+41421466=FinalSeventhSieve.rough 11092009835083 14543 :=
  LargeQuotientSieve.row (p:=14549) (q:=762389843) (s:=27611) (rank:=39309231) (tiny:=1703) (pairs:=2113937)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 762389843 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14549 : FinalSeventhSieve.rough 11092009835083 14549+82863865=FinalSeventhSieve.rough 11092009835083 14537 :=
  LargeQuotientSieve.combine row14543 row14549 rfl

set_option maxRecDepth 16000 in
private theorem row14551 :
    FinalSeventhSieve.rough 11092009835083 14551+41411994=FinalSeventhSieve.rough 11092009835083 14549 :=
  LargeQuotientSieve.row (p:=14551) (q:=762285054) (s:=27609) (rank:=39304070) (tiny:=1704) (pairs:=2109627)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 762285054 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14551 : FinalSeventhSieve.rough 11092009835083 14551+124275859=FinalSeventhSieve.rough 11092009835083 14537 :=
  LargeQuotientSieve.combine to14549 row14551 rfl

set_option maxRecDepth 16000 in
private theorem row14557 :
    FinalSeventhSieve.rough 11092009835083 14557+41391047=FinalSeventhSieve.rough 11092009835083 14551 :=
  LargeQuotientSieve.row (p:=14557) (q:=761970861) (s:=27603) (rank:=39288664) (tiny:=1705) (pairs:=2104087)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 761970861 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14557 : FinalSeventhSieve.rough 11092009835083 14557+165666906=FinalSeventhSieve.rough 11092009835083 14537 :=
  LargeQuotientSieve.combine to14551 row14557 rfl

set_option maxRecDepth 16000 in
private theorem row14561 :
    FinalSeventhSieve.rough 11092009835083 14561+41375862=FinalSeventhSieve.rough 11092009835083 14557 :=
  LargeQuotientSieve.row (p:=14561) (q:=761761543) (s:=27600) (rank:=39278418) (tiny:=1706) (pairs:=2099149)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 761761543 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14561 : FinalSeventhSieve.rough 11092009835083 14561+207042768=FinalSeventhSieve.rough 11092009835083 14537 :=
  LargeQuotientSieve.combine to14557 row14561 rfl

set_option maxRecDepth 16000 in
private theorem row14563 :
    FinalSeventhSieve.rough 11092009835083 14563+41366482=FinalSeventhSieve.rough 11092009835083 14561 :=
  LargeQuotientSieve.row (p:=14563) (q:=761656927) (s:=27598) (rank:=39273325) (tiny:=1707) (pairs:=2094863)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 761656927 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14563 : FinalSeventhSieve.rough 11092009835083 14563+248409250=FinalSeventhSieve.rough 11092009835083 14537 :=
  LargeQuotientSieve.combine to14561 row14563 rfl

set_option maxRecDepth 16000 in
private theorem row14591 :
    FinalSeventhSieve.rough 11092009835083 14591+41282433=FinalSeventhSieve.rough 11092009835083 14563 :=
  LargeQuotientSieve.row (p:=14591) (q:=760195314) (s:=27571) (rank:=39201797) (tiny:=1708) (pairs:=2082343)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 760195314 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14591 : FinalSeventhSieve.rough 11092009835083 14591+289691683=FinalSeventhSieve.rough 11092009835083 14537 :=
  LargeQuotientSieve.combine to14563 row14591 rfl

set_option maxRecDepth 16000 in
private theorem row14593 :
    FinalSeventhSieve.rough 11092009835083 14593+41273120=FinalSeventhSieve.rough 11092009835083 14591 :=
  LargeQuotientSieve.row (p:=14593) (q:=760091128) (s:=27569) (rank:=39196697) (tiny:=1709) (pairs:=2078131)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 760091128 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14593 : FinalSeventhSieve.rough 11092009835083 14593+330964803=FinalSeventhSieve.rough 11092009835083 14537 :=
  LargeQuotientSieve.combine to14591 row14593 rfl

set_option maxRecDepth 16000 in
private theorem row14621 :
    FinalSeventhSieve.rough 11092009835083 14621+41189460=FinalSeventhSieve.rough 11092009835083 14593 :=
  LargeQuotientSieve.row (p:=14621) (q:=758635512) (s:=27543) (rank:=39125510) (tiny:=1710) (pairs:=2065659)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 758635512 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14621 : FinalSeventhSieve.rough 11092009835083 14621+372154263=FinalSeventhSieve.rough 11092009835083 14537 :=
  LargeQuotientSieve.combine to14593 row14621 rfl

set_option maxRecDepth 16000 in
private theorem row14627 :
    FinalSeventhSieve.rough 11092009835083 14627+41168787=FinalSeventhSieve.rough 11092009835083 14621 :=
  LargeQuotientSieve.row (p:=14627) (q:=758324320) (s:=27537) (rank:=39110299) (tiny:=1711) (pairs:=2060198)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 758324320 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14627 : FinalSeventhSieve.rough 11092009835083 14627+413323050=FinalSeventhSieve.rough 11092009835083 14537 :=
  LargeQuotientSieve.combine to14621 row14627 rfl

set_option maxRecDepth 16000 in
private theorem row14629 :
    FinalSeventhSieve.rough 11092009835083 14629+41159518=FinalSeventhSieve.rough 11092009835083 14627 :=
  LargeQuotientSieve.row (p:=14629) (q:=758220646) (s:=27535) (rank:=39105256) (tiny:=1712) (pairs:=2055973)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 758220646 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14629 : FinalSeventhSieve.rough 11092009835083 14629+454482568=FinalSeventhSieve.rough 11092009835083 14537 :=
  LargeQuotientSieve.combine to14627 row14629 rfl

set_option maxRecDepth 16000 in
private theorem row14633 :
    FinalSeventhSieve.rough 11092009835083 14633+41144632=FinalSeventhSieve.rough 11092009835083 14629 :=
  LargeQuotientSieve.row (p:=14633) (q:=758013383) (s:=27532) (rank:=39095222) (tiny:=1713) (pairs:=2051122)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 758013383 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14633 : FinalSeventhSieve.rough 11092009835083 14633+495627200=FinalSeventhSieve.rough 11092009835083 14537 :=
  LargeQuotientSieve.combine to14629 row14633 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 14633+495627200=FinalSeventhSieve.rough 11092009835083 14537 := to14633

end Tail11092009835083From14537To14633
