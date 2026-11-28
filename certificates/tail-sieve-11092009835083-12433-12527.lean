import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-875000000-900000000»

/-! Exact changes for sieve primes 1485 through 1496. -/
open Finset
namespace Tail11092009835083From12433To12527

set_option maxRecDepth 16000 in
private theorem row12437 :
    FinalSeventhSieve.rough 11092009835083 12437+49665552=FinalSeventhSieve.rough 11092009835083 12433 :=
  LargeQuotientSieve.row (p:=12437) (q:=891855739) (s:=29863) (rank:=45614228) (tiny:=1484) (pairs:=4052807)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 891855739 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row12451 :
    FinalSeventhSieve.rough 11092009835083 12451+49603270=FinalSeventhSieve.rough 11092009835083 12437 :=
  LargeQuotientSieve.row (p:=12451) (q:=890852930) (s:=29847) (rank:=45565823) (tiny:=1485) (pairs:=4038931)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 890852930 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12451 : FinalSeventhSieve.rough 11092009835083 12451+99268822=FinalSeventhSieve.rough 11092009835083 12433 :=
  LargeQuotientSieve.combine row12437 row12451 rfl

set_option maxRecDepth 16000 in
private theorem row12457 :
    FinalSeventhSieve.rough 11092009835083 12457+49573363=FinalSeventhSieve.rough 11092009835083 12451 :=
  LargeQuotientSieve.row (p:=12457) (q:=890423844) (s:=29839) (rank:=45545067) (tiny:=1486) (pairs:=4029781)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 890423844 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12457 : FinalSeventhSieve.rough 11092009835083 12457+148842185=FinalSeventhSieve.rough 11092009835083 12433 :=
  LargeQuotientSieve.combine to12451 row12457 rfl

set_option maxRecDepth 16000 in
private theorem row12473 :
    FinalSeventhSieve.rough 11092009835083 12473+49503085=FinalSeventhSieve.rough 11092009835083 12457 :=
  LargeQuotientSieve.row (p:=12473) (q:=889281635) (s:=29820) (rank:=45489677) (tiny:=1487) (pairs:=4014894)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 889281635 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12473 : FinalSeventhSieve.rough 11092009835083 12473+198345270=FinalSeventhSieve.rough 11092009835083 12433 :=
  LargeQuotientSieve.combine to12457 row12473 rfl

set_option maxRecDepth 16000 in
private theorem row12479 :
    FinalSeventhSieve.rough 11092009835083 12479+49473243=FinalSeventhSieve.rough 11092009835083 12473 :=
  LargeQuotientSieve.row (p:=12479) (q:=888854061) (s:=29813) (rank:=45468941) (tiny:=1488) (pairs:=4005789)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 888854061 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12479 : FinalSeventhSieve.rough 11092009835083 12479+247818513=FinalSeventhSieve.rough 11092009835083 12433 :=
  LargeQuotientSieve.combine to12473 row12479 rfl

set_option maxRecDepth 16000 in
private theorem row12487 :
    FinalSeventhSieve.rough 11092009835083 12487+49435405=FinalSeventhSieve.rough 11092009835083 12479 :=
  LargeQuotientSieve.row (p:=12487) (q:=888284602) (s:=29804) (rank:=45441323) (tiny:=1489) (pairs:=3995570)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 888284602 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12487 : FinalSeventhSieve.rough 11092009835083 12487+297253918=FinalSeventhSieve.rough 11092009835083 12433 :=
  LargeQuotientSieve.combine to12479 row12487 rfl

set_option maxRecDepth 16000 in
private theorem row12491 :
    FinalSeventhSieve.rough 11092009835083 12491+49413690=FinalSeventhSieve.rough 11092009835083 12487 :=
  LargeQuotientSieve.row (p:=12491) (q:=888000146) (s:=29799) (rank:=45427523) (tiny:=1490) (pairs:=3987656)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 888000146 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12491 : FinalSeventhSieve.rough 11092009835083 12491+346667608=FinalSeventhSieve.rough 11092009835083 12433 :=
  LargeQuotientSieve.combine to12487 row12491 rfl

set_option maxRecDepth 16000 in
private theorem row12497 :
    FinalSeventhSieve.rough 11092009835083 12497+49383895=FinalSeventhSieve.rough 11092009835083 12491 :=
  LargeQuotientSieve.row (p:=12497) (q:=887573804) (s:=29792) (rank:=45406726) (tiny:=1491) (pairs:=3978659)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 887573804 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12497 : FinalSeventhSieve.rough 11092009835083 12497+396051503=FinalSeventhSieve.rough 11092009835083 12433 :=
  LargeQuotientSieve.combine to12491 row12497 rfl

set_option maxRecDepth 16000 in
private theorem row12503 :
    FinalSeventhSieve.rough 11092009835083 12503+49354160=FinalSeventhSieve.rough 11092009835083 12497 :=
  LargeQuotientSieve.row (p:=12503) (q:=887147871) (s:=29785) (rank:=45386000) (tiny:=1492) (pairs:=3969651)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 887147871 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12503 : FinalSeventhSieve.rough 11092009835083 12503+445405663=FinalSeventhSieve.rough 11092009835083 12433 :=
  LargeQuotientSieve.combine to12497 row12503 rfl

set_option maxRecDepth 16000 in
private theorem row12511 :
    FinalSeventhSieve.rough 11092009835083 12511+49316486=FinalSeventhSieve.rough 11092009835083 12503 :=
  LargeQuotientSieve.row (p:=12511) (q:=886580595) (s:=29775) (rank:=45358500) (tiny:=1493) (pairs:=3959478)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 886580595 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12511 : FinalSeventhSieve.rough 11092009835083 12511+494722149=FinalSeventhSieve.rough 11092009835083 12433 :=
  LargeQuotientSieve.combine to12503 row12511 rfl

set_option maxRecDepth 16000 in
private theorem row12517 :
    FinalSeventhSieve.rough 11092009835083 12517+49286818=FinalSeventhSieve.rough 11092009835083 12511 :=
  LargeQuotientSieve.row (p:=12517) (q:=886155615) (s:=29768) (rank:=45337806) (tiny:=1494) (pairs:=3950505)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 886155615 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12517 : FinalSeventhSieve.rough 11092009835083 12517+544008967=FinalSeventhSieve.rough 11092009835083 12433 :=
  LargeQuotientSieve.combine to12511 row12517 rfl

set_option maxRecDepth 16000 in
private theorem row12527 :
    FinalSeventhSieve.rough 11092009835083 12527+49241326=FinalSeventhSieve.rough 11092009835083 12517 :=
  LargeQuotientSieve.row (p:=12527) (q:=885448218) (s:=29756) (rank:=45303535) (tiny:=1495) (pairs:=3939285)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 885448218 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12527 : FinalSeventhSieve.rough 11092009835083 12527+593250293=FinalSeventhSieve.rough 11092009835083 12433 :=
  LargeQuotientSieve.combine to12517 row12527 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 12527+593250293=FinalSeventhSieve.rough 11092009835083 12433 := to12527

end Tail11092009835083From12433To12527
