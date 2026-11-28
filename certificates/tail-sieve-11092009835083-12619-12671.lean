import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-875000000-900000000»

/-! Exact changes for sieve primes 1509 through 1514. -/
open Finset
namespace Tail11092009835083From12619To12671

set_option maxRecDepth 16000 in
private theorem row12637 :
    FinalSeventhSieve.rough 11092009835083 12637+48734385=FinalSeventhSieve.rough 11092009835083 12619 :=
  LargeQuotientSieve.row (p:=12637) (q:=877740748) (s:=29626) (rank:=44929522) (tiny:=1508) (pairs:=3806370)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 877740748 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row12641 :
    FinalSeventhSieve.rough 11092009835083 12641+48713277=FinalSeventhSieve.rough 11092009835083 12637 :=
  LargeQuotientSieve.row (p:=12641) (q:=877463004) (s:=29622) (rank:=44915983) (tiny:=1509) (pairs:=3798802)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 877463004 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12641 : FinalSeventhSieve.rough 11092009835083 12641+97447662=FinalSeventhSieve.rough 11092009835083 12619 :=
  LargeQuotientSieve.combine row12637 row12641 rfl

set_option maxRecDepth 16000 in
private theorem row12647 :
    FinalSeventhSieve.rough 11092009835083 12647+48684484=FinalSeventhSieve.rough 11092009835083 12641 :=
  LargeQuotientSieve.row (p:=12647) (q:=877046717) (s:=29614) (rank:=44895916) (tiny:=1510) (pairs:=3790077)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 877046717 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12647 : FinalSeventhSieve.rough 11092009835083 12647+146132146=FinalSeventhSieve.rough 11092009835083 12619 :=
  LargeQuotientSieve.combine to12641 row12647 rfl

set_option maxRecDepth 16000 in
private theorem row12653 :
    FinalSeventhSieve.rough 11092009835083 12653+48655616=FinalSeventhSieve.rough 11092009835083 12647 :=
  LargeQuotientSieve.row (p:=12653) (q:=876630825) (s:=29607) (rank:=44875754) (tiny:=1511) (pairs:=3781372)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 876630825 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12653 : FinalSeventhSieve.rough 11092009835083 12653+194787762=FinalSeventhSieve.rough 11092009835083 12619 :=
  LargeQuotientSieve.combine to12647 row12653 rfl

set_option maxRecDepth 16000 in
private theorem row12659 :
    FinalSeventhSieve.rough 11092009835083 12659+48626835=FinalSeventhSieve.rough 11092009835083 12653 :=
  LargeQuotientSieve.row (p:=12659) (q:=876215327) (s:=29600) (rank:=44855633) (tiny:=1512) (pairs:=3772713)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 876215327 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12659 : FinalSeventhSieve.rough 11092009835083 12659+243414597=FinalSeventhSieve.rough 11092009835083 12619 :=
  LargeQuotientSieve.combine to12653 row12659 rfl

set_option maxRecDepth 16000 in
private theorem row12671 :
    FinalSeventhSieve.rough 11092009835083 12671+48574740=FinalSeventhSieve.rough 11092009835083 12659 :=
  LargeQuotientSieve.row (p:=12671) (q:=875385512) (s:=29586) (rank:=44815516) (tiny:=1513) (pairs:=3760736)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 875385512 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12671 : FinalSeventhSieve.rough 11092009835083 12671+291989337=FinalSeventhSieve.rough 11092009835083 12619 :=
  LargeQuotientSieve.combine to12659 row12671 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 12671+291989337=FinalSeventhSieve.rough 11092009835083 12619 := to12671

end Tail11092009835083From12619To12671
