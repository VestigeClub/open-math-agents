import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1000000000-1025000000»

/-! Exact changes for sieve primes 3191 through 3202. -/
open Finset
namespace Tail30110134441897From29363To29473

set_option maxRecDepth 16000 in
private theorem row29383 :
    FinalSeventhSieve.rough 30110134441897 29383+52102954=FinalSeventhSieve.rough 30110134441897 29363 :=
  LargeQuotientSieve.row (p:=29383) (q:=1024746773) (s:=32011) (rank:=52041184) (tiny:=3190) (pairs:=64959)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1024746773 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row29387 :
    FinalSeventhSieve.rough 30110134441897 29387+52095507=FinalSeventhSieve.rough 30110134441897 29383 :=
  LargeQuotientSieve.row (p:=29387) (q:=1024607290) (s:=32009) (rank:=52034385) (tiny:=3191) (pairs:=64312)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1024607290 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29387 : FinalSeventhSieve.rough 30110134441897 29387+104198461=FinalSeventhSieve.rough 30110134441897 29363 :=
  LargeQuotientSieve.combine row29383 row29387 rfl

set_option maxRecDepth 16000 in
private theorem row29389 :
    FinalSeventhSieve.rough 30110134441897 29389+52091563=FinalSeventhSieve.rough 30110134441897 29387 :=
  LargeQuotientSieve.row (p:=29389) (q:=1024537563) (s:=32008) (rank:=52031025) (tiny:=3192) (pairs:=63729)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1024537563 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29389 : FinalSeventhSieve.rough 30110134441897 29389+156290024=FinalSeventhSieve.rough 30110134441897 29363 :=
  LargeQuotientSieve.combine to29387 row29389 rfl

set_option maxRecDepth 16000 in
private theorem row29399 :
    FinalSeventhSieve.rough 30110134441897 29399+52073941=FinalSeventhSieve.rough 30110134441897 29389 :=
  LargeQuotientSieve.row (p:=29399) (q:=1024189069) (s:=32002) (rank:=52014206) (tiny:=3193) (pairs:=62927)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1024189069 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29399 : FinalSeventhSieve.rough 30110134441897 29399+208363965=FinalSeventhSieve.rough 30110134441897 29363 :=
  LargeQuotientSieve.combine to29389 row29399 rfl

set_option maxRecDepth 16000 in
private theorem row29401 :
    FinalSeventhSieve.rough 30110134441897 29401+52070050=FinalSeventhSieve.rough 30110134441897 29399 :=
  LargeQuotientSieve.row (p:=29401) (q:=1024119398) (s:=32001) (rank:=52010892) (tiny:=3194) (pairs:=62351)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1024119398 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29401 : FinalSeventhSieve.rough 30110134441897 29401+260434015=FinalSeventhSieve.rough 30110134441897 29363 :=
  LargeQuotientSieve.combine to29399 row29401 rfl

set_option maxRecDepth 16000 in
private theorem row29411 :
    FinalSeventhSieve.rough 30110134441897 29411+52052502=FinalSeventhSieve.rough 30110134441897 29401 :=
  LargeQuotientSieve.row (p:=29411) (q:=1023771189) (s:=31996) (rank:=51994123) (tiny:=3195) (pairs:=61573)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1023771189 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29411 : FinalSeventhSieve.rough 30110134441897 29411+312486517=FinalSeventhSieve.rough 30110134441897 29363 :=
  LargeQuotientSieve.combine to29401 row29411 rfl

set_option maxRecDepth 16000 in
private theorem row29423 :
    FinalSeventhSieve.rough 30110134441897 29423+52031482=FinalSeventhSieve.rough 30110134441897 29411 :=
  LargeQuotientSieve.row (p:=29423) (q:=1023353649) (s:=31989) (rank:=51973956) (tiny:=3196) (pairs:=60721)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1023353649 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29423 : FinalSeventhSieve.rough 30110134441897 29423+364517999=FinalSeventhSieve.rough 30110134441897 29363 :=
  LargeQuotientSieve.combine to29411 row29423 rfl

set_option maxRecDepth 16000 in
private theorem row29429 :
    FinalSeventhSieve.rough 30110134441897 29429+52020837=FinalSeventhSieve.rough 30110134441897 29423 :=
  LargeQuotientSieve.row (p:=29429) (q:=1023145008) (s:=31986) (rank:=51963983) (tiny:=3197) (pairs:=60050)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1023145008 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29429 : FinalSeventhSieve.rough 30110134441897 29429+416538836=FinalSeventhSieve.rough 30110134441897 29363 :=
  LargeQuotientSieve.combine to29423 row29429 rfl

set_option maxRecDepth 16000 in
private theorem row29437 :
    FinalSeventhSieve.rough 30110134441897 29437+52006629=FinalSeventhSieve.rough 30110134441897 29429 :=
  LargeQuotientSieve.row (p:=29437) (q:=1022866951) (s:=31982) (rank:=51950505) (tiny:=3198) (pairs:=59321)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1022866951 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29437 : FinalSeventhSieve.rough 30110134441897 29437+468545465=FinalSeventhSieve.rough 30110134441897 29363 :=
  LargeQuotientSieve.combine to29429 row29437 rfl

set_option maxRecDepth 16000 in
private theorem row29443 :
    FinalSeventhSieve.rough 30110134441897 29443+51995898=FinalSeventhSieve.rough 30110134441897 29437 :=
  LargeQuotientSieve.row (p:=29443) (q:=1022658507) (s:=31979) (rank:=51940455) (tiny:=3199) (pairs:=58641)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1022658507 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29443 : FinalSeventhSieve.rough 30110134441897 29443+520541363=FinalSeventhSieve.rough 30110134441897 29363 :=
  LargeQuotientSieve.combine to29437 row29443 rfl

set_option maxRecDepth 16000 in
private theorem row29453 :
    FinalSeventhSieve.rough 30110134441897 29453+51978360=FinalSeventhSieve.rough 30110134441897 29443 :=
  LargeQuotientSieve.row (p:=29453) (q:=1022311290) (s:=31973) (rank:=51923698) (tiny:=3200) (pairs:=57861)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1022311290 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29453 : FinalSeventhSieve.rough 30110134441897 29453+572519723=FinalSeventhSieve.rough 30110134441897 29363 :=
  LargeQuotientSieve.combine to29443 row29453 rfl

set_option maxRecDepth 16000 in
private theorem row29473 :
    FinalSeventhSieve.rough 30110134441897 29473+51943998=FinalSeventhSieve.rough 30110134441897 29453 :=
  LargeQuotientSieve.row (p:=29473) (q:=1021617563) (s:=31962) (rank:=51890358) (tiny:=3201) (pairs:=56840)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1021617563 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29473 : FinalSeventhSieve.rough 30110134441897 29473+624463721=FinalSeventhSieve.rough 30110134441897 29363 :=
  LargeQuotientSieve.combine to29453 row29473 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 29473+624463721=FinalSeventhSieve.rough 30110134441897 29363 := to29473

end Tail30110134441897From29363To29473
