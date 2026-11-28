import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-800000000-825000000»

/-! Exact changes for sieve primes 1594 through 1605. -/
open Finset
namespace Tail11092009835083From13441To13567

set_option maxRecDepth 16000 in
private theorem row13451 :
    FinalSeventhSieve.rough 11092009835083 13451+45325065=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.row (p:=13451) (q:=824623435) (s:=28716) (rank:=42346665) (tiny:=1593) (pairs:=2979992)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 824623435 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row13457 :
    FinalSeventhSieve.rough 11092009835083 13457+45299994=FinalSeventhSieve.rough 11092009835083 13451 :=
  LargeQuotientSieve.row (p:=13457) (q:=824255765) (s:=28709) (rank:=42328784) (tiny:=1594) (pairs:=2972803)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 824255765 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13457 : FinalSeventhSieve.rough 11092009835083 13457+90625059=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine row13451 row13457 rfl

set_option maxRecDepth 16000 in
private theorem row13463 :
    FinalSeventhSieve.rough 11092009835083 13463+45275005=FinalSeventhSieve.rough 11092009835083 13457 :=
  LargeQuotientSieve.row (p:=13463) (q:=823888422) (s:=28703) (rank:=42310969) (tiny:=1595) (pairs:=2965630)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 823888422 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13463 : FinalSeventhSieve.rough 11092009835083 13463+135900064=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine to13457 row13463 rfl

set_option maxRecDepth 16000 in
private theorem row13469 :
    FinalSeventhSieve.rough 11092009835083 13469+45249827=FinalSeventhSieve.rough 11092009835083 13463 :=
  LargeQuotientSieve.row (p:=13469) (q:=823521407) (s:=28697) (rank:=42293013) (tiny:=1596) (pairs:=2958409)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 823521407 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13469 : FinalSeventhSieve.rough 11092009835083 13469+181149891=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine to13463 row13469 rfl

set_option maxRecDepth 16000 in
private theorem row13477 :
    FinalSeventhSieve.rough 11092009835083 13477+45218009=FinalSeventhSieve.rough 11092009835083 13469 :=
  LargeQuotientSieve.row (p:=13477) (q:=823032561) (s:=28688) (rank:=42269201) (tiny:=1597) (pairs:=2950404)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 823032561 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13477 : FinalSeventhSieve.rough 11092009835083 13477+226367900=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine to13469 row13477 rfl

set_option maxRecDepth 16000 in
private theorem row13487 :
    FinalSeventhSieve.rough 11092009835083 13487+45179223=FinalSeventhSieve.rough 11092009835083 13477 :=
  LargeQuotientSieve.row (p:=13487) (q:=822422320) (s:=28677) (rank:=42239410) (tiny:=1598) (pairs:=2941410)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 822422320 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13487 : FinalSeventhSieve.rough 11092009835083 13487+271547123=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine to13477 row13487 rfl

set_option maxRecDepth 16000 in
private theorem row13499 :
    FinalSeventhSieve.rough 11092009835083 13499+45133992=FinalSeventhSieve.rough 11092009835083 13487 :=
  LargeQuotientSieve.row (p:=13499) (q:=821691224) (s:=28665) (rank:=42203905) (tiny:=1599) (pairs:=2931685)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 821691224 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13499 : FinalSeventhSieve.rough 11092009835083 13499+316681115=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine to13487 row13499 rfl

set_option maxRecDepth 16000 in
private theorem row13513 :
    FinalSeventhSieve.rough 11092009835083 13513+45081988=FinalSeventhSieve.rough 11092009835083 13499 :=
  LargeQuotientSieve.row (p:=13513) (q:=820839919) (s:=28650) (rank:=42162437) (tiny:=1600) (pairs:=2921150)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 820839919 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13513 : FinalSeventhSieve.rough 11092009835083 13513+361763103=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine to13499 row13513 rfl

set_option maxRecDepth 16000 in
private theorem row13523 :
    FinalSeventhSieve.rough 11092009835083 13523+45043560=FinalSeventhSieve.rough 11092009835083 13513 :=
  LargeQuotientSieve.row (p:=13523) (q:=820232924) (s:=28639) (rank:=42132820) (tiny:=1601) (pairs:=2912340)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 820232924 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13523 : FinalSeventhSieve.rough 11092009835083 13523+406806663=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine to13513 row13523 rfl

set_option maxRecDepth 16000 in
private theorem row13537 :
    FinalSeventhSieve.rough 11092009835083 13537+44991685=FinalSeventhSieve.rough 11092009835083 13523 :=
  LargeQuotientSieve.row (p:=13537) (q:=819384637) (s:=28624) (rank:=42091463) (tiny:=1602) (pairs:=2901823)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 819384637 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13537 : FinalSeventhSieve.rough 11092009835083 13537+451798348=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine to13523 row13537 rfl

set_option maxRecDepth 16000 in
private theorem row13553 :
    FinalSeventhSieve.rough 11092009835083 13553+44933218=FinalSeventhSieve.rough 11092009835083 13537 :=
  LargeQuotientSieve.row (p:=13553) (q:=818417312) (s:=28607) (rank:=42044367) (tiny:=1603) (pairs:=2890453)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 818417312 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13553 : FinalSeventhSieve.rough 11092009835083 13553+496731566=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine to13537 row13553 rfl

set_option maxRecDepth 16000 in
private theorem row13567 :
    FinalSeventhSieve.rough 11092009835083 13567+44881717=FinalSeventhSieve.rough 11092009835083 13553 :=
  LargeQuotientSieve.row (p:=13567) (q:=817572774) (s:=28593) (rank:=42003372) (tiny:=1604) (pairs:=2879948)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ800000000To825000000.count_correct 817572774 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13567 : FinalSeventhSieve.rough 11092009835083 13567+541613283=FinalSeventhSieve.rough 11092009835083 13441 :=
  LargeQuotientSieve.combine to13553 row13567 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13567+541613283=FinalSeventhSieve.rough 11092009835083 13441 := to13567

end Tail11092009835083From13441To13567
