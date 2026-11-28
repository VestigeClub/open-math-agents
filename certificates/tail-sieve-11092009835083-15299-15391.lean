import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-700000000-725000000»

/-! Exact changes for sieve primes 1788 through 1799. -/
open Finset
namespace Tail11092009835083From15299To15391

set_option maxRecDepth 16000 in
private theorem row15307 :
    FinalSeventhSieve.rough 11092009835083 15307+39073255=FinalSeventhSieve.rough 11092009835083 15299 :=
  LargeQuotientSieve.row (p:=15307) (q:=724636430) (s:=26919) (rank:=37461637) (tiny:=1787) (pairs:=1613404)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 724636430 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row15313 :
    FinalSeventhSieve.rough 11092009835083 15313+39054722=FinalSeventhSieve.rough 11092009835083 15307 :=
  LargeQuotientSieve.row (p:=15313) (q:=724352500) (s:=26913) (rank:=37447707) (tiny:=1788) (pairs:=1608802)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 724352500 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15313 : FinalSeventhSieve.rough 11092009835083 15313+78127977=FinalSeventhSieve.rough 11092009835083 15299 :=
  LargeQuotientSieve.combine row15307 row15313 rfl

set_option maxRecDepth 16000 in
private theorem row15319 :
    FinalSeventhSieve.rough 11092009835083 15319+39036198=FinalSeventhSieve.rough 11092009835083 15313 :=
  LargeQuotientSieve.row (p:=15319) (q:=724068792) (s:=26908) (rank:=37433801) (tiny:=1789) (pairs:=1604185)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 724068792 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15319 : FinalSeventhSieve.rough 11092009835083 15319+117164175=FinalSeventhSieve.rough 11092009835083 15299 :=
  LargeQuotientSieve.combine to15313 row15319 rfl

set_option maxRecDepth 16000 in
private theorem row15329 :
    FinalSeventhSieve.rough 11092009835083 15329+39007423=FinalSeventhSieve.rough 11092009835083 15319 :=
  LargeQuotientSieve.row (p:=15329) (q:=723596440) (s:=26899) (rank:=37410612) (tiny:=1790) (pairs:=1598600)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 723596440 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15329 : FinalSeventhSieve.rough 11092009835083 15329+156171598=FinalSeventhSieve.rough 11092009835083 15299 :=
  LargeQuotientSieve.combine to15319 row15329 rfl

set_option maxRecDepth 16000 in
private theorem row15331 :
    FinalSeventhSieve.rough 11092009835083 15331+38999213=FinalSeventhSieve.rough 11092009835083 15329 :=
  LargeQuotientSieve.row (p:=15331) (q:=723502043) (s:=26897) (rank:=37405983) (tiny:=1791) (pairs:=1595020)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 723502043 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15331 : FinalSeventhSieve.rough 11092009835083 15331+195170811=FinalSeventhSieve.rough 11092009835083 15299 :=
  LargeQuotientSieve.combine to15329 row15331 rfl

set_option maxRecDepth 16000 in
private theorem row15349 :
    FinalSeventhSieve.rough 11092009835083 15349+38950025=FinalSeventhSieve.rough 11092009835083 15331 :=
  LargeQuotientSieve.row (p:=15349) (q:=722653582) (s:=26882) (rank:=37364410) (tiny:=1792) (pairs:=1587406)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 722653582 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15349 : FinalSeventhSieve.rough 11092009835083 15349+234120836=FinalSeventhSieve.rough 11092009835083 15299 :=
  LargeQuotientSieve.combine to15331 row15349 rfl

set_option maxRecDepth 16000 in
private theorem row15359 :
    FinalSeventhSieve.rough 11092009835083 15359+38921300=FinalSeventhSieve.rough 11092009835083 15349 :=
  LargeQuotientSieve.row (p:=15359) (q:=722183074) (s:=26873) (rank:=37341240) (tiny:=1793) (pairs:=1581852)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 722183074 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15359 : FinalSeventhSieve.rough 11092009835083 15359+273042136=FinalSeventhSieve.rough 11092009835083 15299 :=
  LargeQuotientSieve.combine to15349 row15359 rfl

set_option maxRecDepth 16000 in
private theorem row15361 :
    FinalSeventhSieve.rough 11092009835083 15361+38913096=FinalSeventhSieve.rough 11092009835083 15359 :=
  LargeQuotientSieve.row (p:=15361) (q:=722089045) (s:=26871) (rank:=37336606) (tiny:=1794) (pairs:=1578283)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 722089045 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15361 : FinalSeventhSieve.rough 11092009835083 15361+311955232=FinalSeventhSieve.rough 11092009835083 15299 :=
  LargeQuotientSieve.combine to15359 row15361 rfl

set_option maxRecDepth 16000 in
private theorem row15373 :
    FinalSeventhSieve.rough 11092009835083 15373+38879389=FinalSeventhSieve.rough 11092009835083 15361 :=
  LargeQuotientSieve.row (p:=15373) (q:=721525390) (s:=26861) (rank:=37308934) (tiny:=1795) (pairs:=1572249)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 721525390 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15373 : FinalSeventhSieve.rough 11092009835083 15373+350834621=FinalSeventhSieve.rough 11092009835083 15299 :=
  LargeQuotientSieve.combine to15361 row15373 rfl

set_option maxRecDepth 16000 in
private theorem row15377 :
    FinalSeventhSieve.rough 11092009835083 15377+38866161=FinalSeventhSieve.rough 11092009835083 15373 :=
  LargeQuotientSieve.row (p:=15377) (q:=721337701) (s:=26857) (rank:=37299748) (tiny:=1796) (pairs:=1568208)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 721337701 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15377 : FinalSeventhSieve.rough 11092009835083 15377+389700782=FinalSeventhSieve.rough 11092009835083 15299 :=
  LargeQuotientSieve.combine to15373 row15377 rfl

set_option maxRecDepth 16000 in
private theorem row15383 :
    FinalSeventhSieve.rough 11092009835083 15383+38847812=FinalSeventhSieve.rough 11092009835083 15377 :=
  LargeQuotientSieve.row (p:=15383) (q:=721056350) (s:=26852) (rank:=37285943) (tiny:=1797) (pairs:=1563665)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 721056350 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15383 : FinalSeventhSieve.rough 11092009835083 15383+428548594=FinalSeventhSieve.rough 11092009835083 15299 :=
  LargeQuotientSieve.combine to15377 row15383 rfl

set_option maxRecDepth 16000 in
private theorem row15391 :
    FinalSeventhSieve.rough 11092009835083 15391+38824403=FinalSeventhSieve.rough 11092009835083 15383 :=
  LargeQuotientSieve.row (p:=15391) (q:=720681556) (s:=26845) (rank:=37267633) (tiny:=1798) (pairs:=1558567)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 720681556 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15391 : FinalSeventhSieve.rough 11092009835083 15391+467372997=FinalSeventhSieve.rough 11092009835083 15299 :=
  LargeQuotientSieve.combine to15383 row15391 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 15391+467372997=FinalSeventhSieve.rough 11092009835083 15299 := to15391

end Tail11092009835083From15299To15391
