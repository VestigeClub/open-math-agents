import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-600000000-625000000»

/-! Exact changes for sieve primes 2074 through 2085. -/
open Finset
namespace Tail11092009835083From18089To18199

set_option maxRecDepth 16000 in
private theorem row18097 :
    FinalSeventhSieve.rough 11092009835083 18097+32447767=FinalSeventhSieve.rough 11092009835083 18089 :=
  LargeQuotientSieve.row (p:=18097) (q:=612919811) (s:=24757) (rank:=31963800) (tiny:=2073) (pairs:=486039)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 612919811 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row18119 :
    FinalSeventhSieve.rough 11092009835083 18119+32407014=FinalSeventhSieve.rough 11092009835083 18097 :=
  LargeQuotientSieve.row (p:=18119) (q:=612175607) (s:=24742) (rank:=31926867) (tiny:=2074) (pairs:=482220)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 612175607 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18119 : FinalSeventhSieve.rough 11092009835083 18119+64854781=FinalSeventhSieve.rough 11092009835083 18089 :=
  LargeQuotientSieve.combine row18097 row18119 rfl

set_option maxRecDepth 16000 in
private theorem row18121 :
    FinalSeventhSieve.rough 11092009835083 18121+32401925=FinalSeventhSieve.rough 11092009835083 18119 :=
  LargeQuotientSieve.row (p:=18121) (q:=612108042) (s:=24740) (rank:=31923509) (tiny:=2075) (pairs:=480490)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 612108042 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18121 : FinalSeventhSieve.rough 11092009835083 18121+97256706=FinalSeventhSieve.rough 11092009835083 18089 :=
  LargeQuotientSieve.combine to18119 row18121 rfl

set_option maxRecDepth 16000 in
private theorem row18127 :
    FinalSeventhSieve.rough 11092009835083 18127+32389812=FinalSeventhSieve.rough 11092009835083 18121 :=
  LargeQuotientSieve.row (p:=18127) (q:=611905435) (s:=24736) (rank:=31913558) (tiny:=2076) (pairs:=478329)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 611905435 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18127 : FinalSeventhSieve.rough 11092009835083 18127+129646518=FinalSeventhSieve.rough 11092009835083 18089 :=
  LargeQuotientSieve.combine to18121 row18127 rfl

set_option maxRecDepth 16000 in
private theorem row18131 :
    FinalSeventhSieve.rough 11092009835083 18131+32381126=FinalSeventhSieve.rough 11092009835083 18127 :=
  LargeQuotientSieve.row (p:=18131) (q:=611770439) (s:=24733) (rank:=31906848) (tiny:=2077) (pairs:=476354)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 611770439 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18131 : FinalSeventhSieve.rough 11092009835083 18131+162027644=FinalSeventhSieve.rough 11092009835083 18089 :=
  LargeQuotientSieve.combine to18127 row18131 rfl

set_option maxRecDepth 16000 in
private theorem row18133 :
    FinalSeventhSieve.rough 11092009835083 18133+32376100=FinalSeventhSieve.rough 11092009835083 18131 :=
  LargeQuotientSieve.row (p:=18133) (q:=611702963) (s:=24732) (rank:=31903550) (tiny:=2078) (pairs:=474627)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 611702963 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18133 : FinalSeventhSieve.rough 11092009835083 18133+194403744=FinalSeventhSieve.rough 11092009835083 18089 :=
  LargeQuotientSieve.combine to18131 row18133 rfl

set_option maxRecDepth 16000 in
private theorem row18143 :
    FinalSeventhSieve.rough 11092009835083 18143+32356871=FinalSeventhSieve.rough 11092009835083 18133 :=
  LargeQuotientSieve.row (p:=18143) (q:=611365806) (s:=24725) (rank:=31886829) (tiny:=2079) (pairs:=472120)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 611365806 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18143 : FinalSeventhSieve.rough 11092009835083 18143+226760615=FinalSeventhSieve.rough 11092009835083 18089 :=
  LargeQuotientSieve.combine to18133 row18143 rfl

set_option maxRecDepth 16000 in
private theorem row18149 :
    FinalSeventhSieve.rough 11092009835083 18149+32344888=FinalSeventhSieve.rough 11092009835083 18143 :=
  LargeQuotientSieve.row (p:=18149) (q:=611163691) (s:=24721) (rank:=31876987) (tiny:=2080) (pairs:=469980)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 611163691 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18149 : FinalSeventhSieve.rough 11092009835083 18149+259105503=FinalSeventhSieve.rough 11092009835083 18089 :=
  LargeQuotientSieve.combine to18143 row18149 rfl

set_option maxRecDepth 16000 in
private theorem row18169 :
    FinalSeventhSieve.rough 11092009835083 18169+32308158=FinalSeventhSieve.rough 11092009835083 18149 :=
  LargeQuotientSieve.row (p:=18169) (q:=610490937) (s:=24708) (rank:=31843807) (tiny:=2081) (pairs:=466431)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 610490937 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18169 : FinalSeventhSieve.rough 11092009835083 18169+291413661=FinalSeventhSieve.rough 11092009835083 18089 :=
  LargeQuotientSieve.combine to18149 row18169 rfl

set_option maxRecDepth 16000 in
private theorem row18181 :
    FinalSeventhSieve.rough 11092009835083 18181+32285441=FinalSeventhSieve.rough 11092009835083 18169 :=
  LargeQuotientSieve.row (p:=18181) (q:=610087994) (s:=24699) (rank:=31823813) (tiny:=2082) (pairs:=463709)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 610087994 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18181 : FinalSeventhSieve.rough 11092009835083 18181+323699102=FinalSeventhSieve.rough 11092009835083 18089 :=
  LargeQuotientSieve.combine to18169 row18181 rfl

set_option maxRecDepth 16000 in
private theorem row18191 :
    FinalSeventhSieve.rough 11092009835083 18191+32266336=FinalSeventhSieve.rough 11092009835083 18181 :=
  LargeQuotientSieve.row (p:=18191) (q:=609752615) (s:=24693) (rank:=31807201) (tiny:=2083) (pairs:=461217)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 609752615 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18191 : FinalSeventhSieve.rough 11092009835083 18191+355965438=FinalSeventhSieve.rough 11092009835083 18089 :=
  LargeQuotientSieve.combine to18181 row18191 rfl

set_option maxRecDepth 16000 in
private theorem row18199 :
    FinalSeventhSieve.rough 11092009835083 18199+32250762=FinalSeventhSieve.rough 11092009835083 18191 :=
  LargeQuotientSieve.row (p:=18199) (q:=609484578) (s:=24687) (rank:=31793945) (tiny:=2084) (pairs:=458900)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 609484578 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18199 : FinalSeventhSieve.rough 11092009835083 18199+388216200=FinalSeventhSieve.rough 11092009835083 18089 :=
  LargeQuotientSieve.combine to18191 row18199 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 18199+388216200=FinalSeventhSieve.rough 11092009835083 18089 := to18199

end Tail11092009835083From18089To18199
