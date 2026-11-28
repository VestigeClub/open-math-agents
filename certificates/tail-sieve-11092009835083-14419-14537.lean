import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-750000000-775000000»

/-! Exact changes for sieve primes 1691 through 1702. -/
open Finset
namespace Tail11092009835083From14419To14537

set_option maxRecDepth 16000 in
private theorem row14423 :
    FinalSeventhSieve.rough 11092009835083 14423+41836078=FinalSeventhSieve.rough 11092009835083 14419 :=
  LargeQuotientSieve.row (p:=14423) (q:=769050116) (s:=27731) (rank:=39634480) (tiny:=1690) (pairs:=2203287)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 769050116 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row14431 :
    FinalSeventhSieve.rough 11092009835083 14431+41808800=FinalSeventhSieve.rough 11092009835083 14423 :=
  LargeQuotientSieve.row (p:=14431) (q:=768623784) (s:=27724) (rank:=39613604) (tiny:=1691) (pairs:=2196886)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 768623784 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14431 : FinalSeventhSieve.rough 11092009835083 14431+83644878=FinalSeventhSieve.rough 11092009835083 14419 :=
  LargeQuotientSieve.combine row14423 row14431 rfl

set_option maxRecDepth 16000 in
private theorem row14437 :
    FinalSeventhSieve.rough 11092009835083 14437+41787346=FinalSeventhSieve.rough 11092009835083 14431 :=
  LargeQuotientSieve.row (p:=14437) (q:=768304345) (s:=27718) (rank:=39597872) (tiny:=1692) (pairs:=2191165)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 768304345 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14437 : FinalSeventhSieve.rough 11092009835083 14437+125432224=FinalSeventhSieve.rough 11092009835083 14419 :=
  LargeQuotientSieve.combine to14431 row14437 rfl

set_option maxRecDepth 16000 in
private theorem row14447 :
    FinalSeventhSieve.rough 11092009835083 14447+41754368=FinalSeventhSieve.rough 11092009835083 14437 :=
  LargeQuotientSieve.row (p:=14447) (q:=767772536) (s:=27708) (rank:=39571918) (tiny:=1693) (pairs:=2184142)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 767772536 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14447 : FinalSeventhSieve.rough 11092009835083 14447+167186592=FinalSeventhSieve.rough 11092009835083 14419 :=
  LargeQuotientSieve.combine to14437 row14447 rfl

set_option maxRecDepth 16000 in
private theorem row14449 :
    FinalSeventhSieve.rough 11092009835083 14449+41744793=FinalSeventhSieve.rough 11092009835083 14447 :=
  LargeQuotientSieve.row (p:=14449) (q:=767666263) (s:=27706) (rank:=39566723) (tiny:=1694) (pairs:=2179763)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 767666263 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14449 : FinalSeventhSieve.rough 11092009835083 14449+208931385=FinalSeventhSieve.rough 11092009835083 14419 :=
  LargeQuotientSieve.combine to14447 row14449 rfl

set_option maxRecDepth 16000 in
private theorem row14461 :
    FinalSeventhSieve.rough 11092009835083 14461+41705922=FinalSeventhSieve.rough 11092009835083 14449 :=
  LargeQuotientSieve.row (p:=14461) (q:=767029239) (s:=27695) (rank:=39535506) (tiny:=1695) (pairs:=2172110)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 767029239 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14461 : FinalSeventhSieve.rough 11092009835083 14461+250637307=FinalSeventhSieve.rough 11092009835083 14419 :=
  LargeQuotientSieve.combine to14449 row14461 rfl

set_option maxRecDepth 16000 in
private theorem row14479 :
    FinalSeventhSieve.rough 11092009835083 14479+41649721=FinalSeventhSieve.rough 11092009835083 14461 :=
  LargeQuotientSieve.row (p:=14479) (q:=766075684) (s:=27678) (rank:=39488910) (tiny:=1696) (pairs:=2162506)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 766075684 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14479 : FinalSeventhSieve.rough 11092009835083 14479+292287028=FinalSeventhSieve.rough 11092009835083 14419 :=
  LargeQuotientSieve.combine to14461 row14479 rfl

set_option maxRecDepth 16000 in
private theorem row14489 :
    FinalSeventhSieve.rough 11092009835083 14489+41616902=FinalSeventhSieve.rough 11092009835083 14479 :=
  LargeQuotientSieve.row (p:=14489) (q:=765546955) (s:=27668) (rank:=39463092) (tiny:=1697) (pairs:=2155506)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 765546955 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14489 : FinalSeventhSieve.rough 11092009835083 14489+333903930=FinalSeventhSieve.rough 11092009835083 14419 :=
  LargeQuotientSieve.combine to14479 row14489 rfl

set_option maxRecDepth 16000 in
private theorem row14503 :
    FinalSeventhSieve.rough 11092009835083 14503+41572583=FinalSeventhSieve.rough 11092009835083 14489 :=
  LargeQuotientSieve.row (p:=14503) (q:=764807959) (s:=27655) (rank:=39427091) (tiny:=1698) (pairs:=2147189)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 764807959 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14503 : FinalSeventhSieve.rough 11092009835083 14503+375476513=FinalSeventhSieve.rough 11092009835083 14419 :=
  LargeQuotientSieve.combine to14489 row14503 rfl

set_option maxRecDepth 16000 in
private theorem row14519 :
    FinalSeventhSieve.rough 11092009835083 14519+41522662=FinalSeventhSieve.rough 11092009835083 14503 :=
  LargeQuotientSieve.row (p:=14519) (q:=763965137) (s:=27639) (rank:=39386058) (tiny:=1699) (pairs:=2138302)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 763965137 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14519 : FinalSeventhSieve.rough 11092009835083 14519+416999175=FinalSeventhSieve.rough 11092009835083 14419 :=
  LargeQuotientSieve.combine to14503 row14519 rfl

set_option maxRecDepth 16000 in
private theorem row14533 :
    FinalSeventhSieve.rough 11092009835083 14533+41478562=FinalSeventhSieve.rough 11092009835083 14519 :=
  LargeQuotientSieve.row (p:=14533) (q:=763229191) (s:=27626) (rank:=39350234) (tiny:=1700) (pairs:=2130027)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 763229191 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14533 : FinalSeventhSieve.rough 11092009835083 14533+458477737=FinalSeventhSieve.rough 11092009835083 14419 :=
  LargeQuotientSieve.combine to14519 row14533 rfl

set_option maxRecDepth 16000 in
private theorem row14537 :
    FinalSeventhSieve.rough 11092009835083 14537+41463423=FinalSeventhSieve.rough 11092009835083 14533 :=
  LargeQuotientSieve.row (p:=14537) (q:=763019181) (s:=27622) (rank:=39340046) (tiny:=1701) (pairs:=2125077)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 763019181 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14537 : FinalSeventhSieve.rough 11092009835083 14537+499941160=FinalSeventhSieve.rough 11092009835083 14419 :=
  LargeQuotientSieve.combine to14533 row14537 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 14537+499941160=FinalSeventhSieve.rough 11092009835083 14419 := to14537

end Tail11092009835083From14419To14537
