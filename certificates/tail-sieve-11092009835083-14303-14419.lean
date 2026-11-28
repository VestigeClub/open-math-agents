import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-750000000-775000000»

/-! Exact changes for sieve primes 1679 through 1690. -/
open Finset
namespace Tail11092009835083From14303To14419

set_option maxRecDepth 16000 in
private theorem row14321 :
    FinalSeventhSieve.rough 11092009835083 14321+42183889=FinalSeventhSieve.rough 11092009835083 14303 :=
  LargeQuotientSieve.row (p:=14321) (q:=774527605) (s:=27830) (rank:=39902269) (tiny:=1678) (pairs:=2283297)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 774527605 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row14323 :
    FinalSeventhSieve.rough 11092009835083 14323+42174108=FinalSeventhSieve.rough 11092009835083 14321 :=
  LargeQuotientSieve.row (p:=14323) (q:=774419453) (s:=27828) (rank:=39896992) (tiny:=1679) (pairs:=2278794)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 774419453 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14323 : FinalSeventhSieve.rough 11092009835083 14323+84357997=FinalSeventhSieve.rough 11092009835083 14303 :=
  LargeQuotientSieve.combine row14321 row14323 rfl

set_option maxRecDepth 16000 in
private theorem row14327 :
    FinalSeventhSieve.rough 11092009835083 14327+42158284=FinalSeventhSieve.rough 11092009835083 14323 :=
  LargeQuotientSieve.row (p:=14327) (q:=774203241) (s:=27824) (rank:=39886391) (tiny:=1680) (pairs:=2273572)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 774203241 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14327 : FinalSeventhSieve.rough 11092009835083 14327+126516281=FinalSeventhSieve.rough 11092009835083 14303 :=
  LargeQuotientSieve.combine to14323 row14327 rfl

set_option maxRecDepth 16000 in
private theorem row14341 :
    FinalSeventhSieve.rough 11092009835083 14341+42112767=FinalSeventhSieve.rough 11092009835083 14327 :=
  LargeQuotientSieve.row (p:=14341) (q:=773447446) (s:=27810) (rank:=39849495) (tiny:=1681) (pairs:=2264952)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 773447446 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14341 : FinalSeventhSieve.rough 11092009835083 14341+168629048=FinalSeventhSieve.rough 11092009835083 14303 :=
  LargeQuotientSieve.combine to14327 row14341 rfl

set_option maxRecDepth 16000 in
private theorem row14347 :
    FinalSeventhSieve.rough 11092009835083 14347+42091193=FinalSeventhSieve.rough 11092009835083 14341 :=
  LargeQuotientSieve.row (p:=14347) (q:=773123986) (s:=27805) (rank:=39833785) (tiny:=1682) (pairs:=2259089)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 773123986 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14347 : FinalSeventhSieve.rough 11092009835083 14347+210720241=FinalSeventhSieve.rough 11092009835083 14303 :=
  LargeQuotientSieve.combine to14341 row14347 rfl

set_option maxRecDepth 16000 in
private theorem row14369 :
    FinalSeventhSieve.rough 11092009835083 14369+42021982=FinalSeventhSieve.rough 11092009835083 14347 :=
  LargeQuotientSieve.row (p:=14369) (q:=771940276) (s:=27783) (rank:=39775865) (tiny:=1683) (pairs:=2247799)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 771940276 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14369 : FinalSeventhSieve.rough 11092009835083 14369+252742223=FinalSeventhSieve.rough 11092009835083 14303 :=
  LargeQuotientSieve.combine to14347 row14369 rfl

set_option maxRecDepth 16000 in
private theorem row14387 :
    FinalSeventhSieve.rough 11092009835083 14387+41964889=FinalSeventhSieve.rough 11092009835083 14369 :=
  LargeQuotientSieve.row (p:=14387) (q:=770974479) (s:=27766) (rank:=39728672) (tiny:=1684) (pairs:=2237900)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 770974479 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14387 : FinalSeventhSieve.rough 11092009835083 14387+294707112=FinalSeventhSieve.rough 11092009835083 14303 :=
  LargeQuotientSieve.combine to14369 row14387 rfl

set_option maxRecDepth 16000 in
private theorem row14389 :
    FinalSeventhSieve.rough 11092009835083 14389+41955145=FinalSeventhSieve.rough 11092009835083 14387 :=
  LargeQuotientSieve.row (p:=14389) (q:=770867317) (s:=27764) (rank:=39723363) (tiny:=1685) (pairs:=2233466)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 770867317 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14389 : FinalSeventhSieve.rough 11092009835083 14389+336662257=FinalSeventhSieve.rough 11092009835083 14303 :=
  LargeQuotientSieve.combine to14387 row14389 rfl

set_option maxRecDepth 16000 in
private theorem row14401 :
    FinalSeventhSieve.rough 11092009835083 14401+41916021=FinalSeventhSieve.rough 11092009835083 14389 :=
  LargeQuotientSieve.row (p:=14401) (q:=770224972) (s:=27752) (rank:=39692016) (tiny:=1686) (pairs:=2225690)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 770224972 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14401 : FinalSeventhSieve.rough 11092009835083 14401+378578278=FinalSeventhSieve.rough 11092009835083 14303 :=
  LargeQuotientSieve.combine to14389 row14401 rfl

set_option maxRecDepth 16000 in
private theorem row14407 :
    FinalSeventhSieve.rough 11092009835083 14407+41894588=FinalSeventhSieve.rough 11092009835083 14401 :=
  LargeQuotientSieve.row (p:=14407) (q:=769904201) (s:=27747) (rank:=39676346) (tiny:=1687) (pairs:=2219928)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 769904201 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14407 : FinalSeventhSieve.rough 11092009835083 14407+420472866=FinalSeventhSieve.rough 11092009835083 14303 :=
  LargeQuotientSieve.combine to14401 row14407 rfl

set_option maxRecDepth 16000 in
private theorem row14411 :
    FinalSeventhSieve.rough 11092009835083 14411+41878953=FinalSeventhSieve.rough 11092009835083 14407 :=
  LargeQuotientSieve.row (p:=14411) (q:=769690502) (s:=27743) (rank:=39665821) (tiny:=1688) (pairs:=2214819)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 769690502 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14411 : FinalSeventhSieve.rough 11092009835083 14411+462351819=FinalSeventhSieve.rough 11092009835083 14303 :=
  LargeQuotientSieve.combine to14407 row14411 rfl

set_option maxRecDepth 16000 in
private theorem row14419 :
    FinalSeventhSieve.rough 11092009835083 14419+41851600=FinalSeventhSieve.rough 11092009835083 14411 :=
  LargeQuotientSieve.row (p:=14419) (q:=769263460) (s:=27735) (rank:=39644910) (tiny:=1689) (pairs:=2208378)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ750000000To775000000.count_correct 769263460 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14419 : FinalSeventhSieve.rough 11092009835083 14419+504203419=FinalSeventhSieve.rough 11092009835083 14303 :=
  LargeQuotientSieve.combine to14411 row14419 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 14419+504203419=FinalSeventhSieve.rough 11092009835083 14303 := to14419

end Tail11092009835083From14303To14419
