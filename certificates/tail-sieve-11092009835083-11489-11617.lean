import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-950000000-975000000»

/-! Exact changes for sieve primes 1386 through 1397. -/
open Finset
namespace Tail11092009835083From11489To11617

set_option maxRecDepth 16000 in
private theorem row11491 :
    FinalSeventhSieve.rough 11092009835083 11491+54477617=FinalSeventhSieve.rough 11092009835083 11489 :=
  LargeQuotientSieve.row (p:=11491) (q:=965278029) (s:=31068) (rank:=49170628) (tiny:=1385) (pairs:=5308373)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 965278029 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row11497 :
    FinalSeventhSieve.rough 11092009835083 11497+54441795=FinalSeventhSieve.rough 11092009835083 11491 :=
  LargeQuotientSieve.row (p:=11497) (q:=964774274) (s:=31060) (rank:=49146310) (tiny:=1386) (pairs:=5296870)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 964774274 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11497 : FinalSeventhSieve.rough 11092009835083 11497+108919412=FinalSeventhSieve.rough 11092009835083 11489 :=
  LargeQuotientSieve.combine row11491 row11497 rfl

set_option maxRecDepth 16000 in
private theorem row11503 :
    FinalSeventhSieve.rough 11092009835083 11503+54406085=FinalSeventhSieve.rough 11092009835083 11497 :=
  LargeQuotientSieve.row (p:=11503) (q:=964271045) (s:=31052) (rank:=49122031) (tiny:=1387) (pairs:=5285440)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 964271045 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11503 : FinalSeventhSieve.rough 11092009835083 11503+163325497=FinalSeventhSieve.rough 11092009835083 11489 :=
  LargeQuotientSieve.combine to11497 row11503 rfl

set_option maxRecDepth 16000 in
private theorem row11519 :
    FinalSeventhSieve.rough 11092009835083 11519+54322065=FinalSeventhSieve.rough 11092009835083 11503 :=
  LargeQuotientSieve.row (p:=11519) (q:=962931663) (s:=31031) (rank:=49057185) (tiny:=1388) (pairs:=5266267)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 962931663 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11519 : FinalSeventhSieve.rough 11092009835083 11519+217647562=FinalSeventhSieve.rough 11092009835083 11489 :=
  LargeQuotientSieve.combine to11503 row11519 rfl

set_option maxRecDepth 16000 in
private theorem row11527 :
    FinalSeventhSieve.rough 11092009835083 11527+54276745=FinalSeventhSieve.rough 11092009835083 11519 :=
  LargeQuotientSieve.row (p:=11527) (q:=962263367) (s:=31020) (rank:=49024733) (tiny:=1389) (pairs:=5253400)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 962263367 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11527 : FinalSeventhSieve.rough 11092009835083 11527+271924307=FinalSeventhSieve.rough 11092009835083 11489 :=
  LargeQuotientSieve.combine to11519 row11527 rfl

set_option maxRecDepth 16000 in
private theorem row11549 :
    FinalSeventhSieve.rough 11092009835083 11549+54164503=FinalSeventhSieve.rough 11092009835083 11527 :=
  LargeQuotientSieve.row (p:=11549) (q:=960430326) (s:=30990) (rank:=48936258) (tiny:=1390) (pairs:=5229634)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 960430326 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11549 : FinalSeventhSieve.rough 11092009835083 11549+326088810=FinalSeventhSieve.rough 11092009835083 11489 :=
  LargeQuotientSieve.combine to11527 row11549 rfl

set_option maxRecDepth 16000 in
private theorem row11551 :
    FinalSeventhSieve.rough 11092009835083 11551+54148110=FinalSeventhSieve.rough 11092009835083 11549 :=
  LargeQuotientSieve.row (p:=11551) (q:=960264032) (s:=30988) (rank:=48928162) (tiny:=1391) (pairs:=5221338)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 960264032 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11551 : FinalSeventhSieve.rough 11092009835083 11551+380236920=FinalSeventhSieve.rough 11092009835083 11489 :=
  LargeQuotientSieve.combine to11549 row11551 rfl

set_option maxRecDepth 16000 in
private theorem row11579 :
    FinalSeventhSieve.rough 11092009835083 11579+54007532=FinalSeventhSieve.rough 11092009835083 11551 :=
  LargeQuotientSieve.row (p:=11579) (q:=957941949) (s:=30950) (rank:=48815705) (tiny:=1392) (pairs:=5193218)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 957941949 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11579 : FinalSeventhSieve.rough 11092009835083 11579+434244452=FinalSeventhSieve.rough 11092009835083 11489 :=
  LargeQuotientSieve.combine to11551 row11579 rfl

set_option maxRecDepth 16000 in
private theorem row11587 :
    FinalSeventhSieve.rough 11092009835083 11587+53962721=FinalSeventhSieve.rough 11092009835083 11579 :=
  LargeQuotientSieve.row (p:=11587) (q:=957280558) (s:=30939) (rank:=48783585) (tiny:=1393) (pairs:=5180528)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 957280558 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11587 : FinalSeventhSieve.rough 11092009835083 11587+488207173=FinalSeventhSieve.rough 11092009835083 11489 :=
  LargeQuotientSieve.combine to11579 row11587 rfl

set_option maxRecDepth 16000 in
private theorem row11593 :
    FinalSeventhSieve.rough 11092009835083 11593+53927554=FinalSeventhSieve.rough 11092009835083 11587 :=
  LargeQuotientSieve.row (p:=11593) (q:=956785114) (s:=30931) (rank:=48759557) (tiny:=1394) (pairs:=5169390)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 956785114 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11593 : FinalSeventhSieve.rough 11092009835083 11593+542134727=FinalSeventhSieve.rough 11092009835083 11489 :=
  LargeQuotientSieve.combine to11587 row11593 rfl

set_option maxRecDepth 16000 in
private theorem row11597 :
    FinalSeventhSieve.rough 11092009835083 11597+53901788=FinalSeventhSieve.rough 11092009835083 11593 :=
  LargeQuotientSieve.row (p:=11597) (q:=956455103) (s:=30926) (rank:=48743541) (tiny:=1395) (pairs:=5159641)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 956455103 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11597 : FinalSeventhSieve.rough 11092009835083 11597+596036515=FinalSeventhSieve.rough 11092009835083 11489 :=
  LargeQuotientSieve.combine to11593 row11597 rfl

set_option maxRecDepth 16000 in
private theorem row11617 :
    FinalSeventhSieve.rough 11092009835083 11617+53800504=FinalSeventhSieve.rough 11092009835083 11597 :=
  LargeQuotientSieve.row (p:=11617) (q:=954808456) (s:=30899) (rank:=48664101) (tiny:=1396) (pairs:=5137798)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 954808456 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11617 : FinalSeventhSieve.rough 11092009835083 11617+649837019=FinalSeventhSieve.rough 11092009835083 11489 :=
  LargeQuotientSieve.combine to11597 row11617 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 11617+649837019=FinalSeventhSieve.rough 11092009835083 11489 := to11617

end Tail11092009835083From11489To11617
