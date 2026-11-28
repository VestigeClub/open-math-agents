import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-750000000-775000000»

/-! Exact changes for sieve primes 1727 through 1733. -/
open Finset
namespace Tail11092009835083From14741To14783

set_option maxRecDepth 16000 in
private theorem row14747 :
    FinalSeventhSieve.rough 11092009835083 14747+40776911=FinalSeventhSieve.rough 11092009835083 14741 :=
  LargeQuotientSieve.row (p:=14747) (q:=752153647) (s:=27425) (rank:=38808493) (tiny:=1726) (pairs:=1970143)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 752153647 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row14753 :
    FinalSeventhSieve.rough 11092009835083 14753+40756631=FinalSeventhSieve.rough 11092009835083 14747 :=
  LargeQuotientSieve.row (p:=14753) (q:=751847748) (s:=27419) (rank:=38793513) (tiny:=1727) (pairs:=1964844)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 751847748 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14753 : FinalSeventhSieve.rough 11092009835083 14753+81533542=FinalSeventhSieve.rough 11092009835083 14741 :=
  LargeQuotientSieve.combine row14747 row14753 rfl

set_option maxRecDepth 16000 in
private theorem row14759 :
    FinalSeventhSieve.rough 11092009835083 14759+40736297=FinalSeventhSieve.rough 11092009835083 14753 :=
  LargeQuotientSieve.row (p:=14759) (q:=751542098) (s:=27414) (rank:=38778472) (tiny:=1728) (pairs:=1959552)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 751542098 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14759 : FinalSeventhSieve.rough 11092009835083 14759+122269839=FinalSeventhSieve.rough 11092009835083 14741 :=
  LargeQuotientSieve.combine to14753 row14759 rfl

set_option maxRecDepth 16000 in
private theorem row14767 :
    FinalSeventhSieve.rough 11092009835083 14767+40710531=FinalSeventhSieve.rough 11092009835083 14759 :=
  LargeQuotientSieve.row (p:=14767) (q:=751134951) (s:=27406) (rank:=38758628) (tiny:=1729) (pairs:=1953631)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 751134951 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14767 : FinalSeventhSieve.rough 11092009835083 14767+162980370=FinalSeventhSieve.rough 11092009835083 14741 :=
  LargeQuotientSieve.combine to14759 row14767 rfl

set_option maxRecDepth 16000 in
private theorem row14771 :
    FinalSeventhSieve.rough 11092009835083 14771+40695900=FinalSeventhSieve.rough 11092009835083 14767 :=
  LargeQuotientSieve.row (p:=14771) (q:=750931543) (s:=27403) (rank:=38748684) (tiny:=1730) (pairs:=1948945)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 750931543 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14771 : FinalSeventhSieve.rough 11092009835083 14771+203676270=FinalSeventhSieve.rough 11092009835083 14741 :=
  LargeQuotientSieve.combine to14767 row14771 rfl

set_option maxRecDepth 16000 in
private theorem row14779 :
    FinalSeventhSieve.rough 11092009835083 14779+40670172=FinalSeventhSieve.rough 11092009835083 14771 :=
  LargeQuotientSieve.row (p:=14779) (q:=750525058) (s:=27395) (rank:=38728843) (tiny:=1731) (pairs:=1943059)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 750525058 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14779 : FinalSeventhSieve.rough 11092009835083 14779+244346442=FinalSeventhSieve.rough 11092009835083 14741 :=
  LargeQuotientSieve.combine to14771 row14779 rfl

set_option maxRecDepth 16000 in
private theorem row14783 :
    FinalSeventhSieve.rough 11092009835083 14783+40655486=FinalSeventhSieve.rough 11092009835083 14779 :=
  LargeQuotientSieve.row (p:=14783) (q:=750321980) (s:=27392) (rank:=38718819) (tiny:=1732) (pairs:=1938398)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 750321980 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14783 : FinalSeventhSieve.rough 11092009835083 14783+285001928=FinalSeventhSieve.rough 11092009835083 14741 :=
  LargeQuotientSieve.combine to14779 row14783 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 14783+285001928=FinalSeventhSieve.rough 11092009835083 14741 := to14783

end Tail11092009835083From14741To14783
