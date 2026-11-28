import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-600000000-625000000»

/-! Exact changes for sieve primes 2110 through 2117. -/
open Finset
namespace Tail11092009835083From18413To18481

set_option maxRecDepth 16000 in
private theorem row18427 :
    FinalSeventhSieve.rough 11092009835083 18427+31820008=FinalSeventhSieve.rough 11092009835083 18413 :=
  LargeQuotientSieve.row (p:=18427) (q:=601943335) (s:=24534) (rank:=31420976) (tiny:=2109) (pairs:=401140)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 601943335 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row18433 :
    FinalSeventhSieve.rough 11092009835083 18433+31808438=FinalSeventhSieve.rough 11092009835083 18427 :=
  LargeQuotientSieve.row (p:=18433) (q:=601747400) (s:=24530) (rank:=31411354) (tiny:=2110) (pairs:=399193)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 601747400 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18433 : FinalSeventhSieve.rough 11092009835083 18433+63628446=FinalSeventhSieve.rough 11092009835083 18413 :=
  LargeQuotientSieve.combine row18427 row18433 rfl

set_option maxRecDepth 16000 in
private theorem row18439 :
    FinalSeventhSieve.rough 11092009835083 18439+31796804=FinalSeventhSieve.rough 11092009835083 18433 :=
  LargeQuotientSieve.row (p:=18439) (q:=601551593) (s:=24526) (rank:=31401630) (tiny:=2111) (pairs:=397284)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 601551593 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18439 : FinalSeventhSieve.rough 11092009835083 18439+95425250=FinalSeventhSieve.rough 11092009835083 18413 :=
  LargeQuotientSieve.combine to18433 row18439 rfl

set_option maxRecDepth 16000 in
private theorem row18443 :
    FinalSeventhSieve.rough 11092009835083 18443+31788512=FinalSeventhSieve.rough 11092009835083 18439 :=
  LargeQuotientSieve.row (p:=18443) (q:=601421126) (s:=24523) (rank:=31395118) (tiny:=2112) (pairs:=395505)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 601421126 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18443 : FinalSeventhSieve.rough 11092009835083 18443+127213762=FinalSeventhSieve.rough 11092009835083 18413 :=
  LargeQuotientSieve.combine to18439 row18443 rfl

set_option maxRecDepth 16000 in
private theorem row18451 :
    FinalSeventhSieve.rough 11092009835083 18451+31773521=FinalSeventhSieve.rough 11092009835083 18443 :=
  LargeQuotientSieve.row (p:=18451) (q:=601160361) (s:=24518) (rank:=31382219) (tiny:=2113) (pairs:=393414)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 601160361 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18451 : FinalSeventhSieve.rough 11092009835083 18451+158987283=FinalSeventhSieve.rough 11092009835083 18413 :=
  LargeQuotientSieve.combine to18443 row18451 rfl

set_option maxRecDepth 16000 in
private theorem row18457 :
    FinalSeventhSieve.rough 11092009835083 18457+31761956=FinalSeventhSieve.rough 11092009835083 18451 :=
  LargeQuotientSieve.row (p:=18457) (q:=600964936) (s:=24514) (rank:=31372576) (tiny:=2114) (pairs:=391493)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 600964936 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18457 : FinalSeventhSieve.rough 11092009835083 18457+190749239=FinalSeventhSieve.rough 11092009835083 18413 :=
  LargeQuotientSieve.combine to18451 row18457 rfl

set_option maxRecDepth 16000 in
private theorem row18461 :
    FinalSeventhSieve.rough 11092009835083 18461+31753746=FinalSeventhSieve.rough 11092009835083 18457 :=
  LargeQuotientSieve.row (p:=18461) (q:=600834723) (s:=24511) (rank:=31366090) (tiny:=2115) (pairs:=389770)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 600834723 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18461 : FinalSeventhSieve.rough 11092009835083 18461+222502985=FinalSeventhSieve.rough 11092009835083 18413 :=
  LargeQuotientSieve.combine to18457 row18461 rfl

set_option maxRecDepth 16000 in
private theorem row18481 :
    FinalSeventhSieve.rough 11092009835083 18481+31718399=FinalSeventhSieve.rough 11092009835083 18461 :=
  LargeQuotientSieve.row (p:=18481) (q:=600184504) (s:=24498) (rank:=31333917) (tiny:=2116) (pairs:=386597)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 600184504 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18481 : FinalSeventhSieve.rough 11092009835083 18481+254221384=FinalSeventhSieve.rough 11092009835083 18413 :=
  LargeQuotientSieve.combine to18461 row18481 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 18481+254221384=FinalSeventhSieve.rough 11092009835083 18413 := to18481

end Tail11092009835083From18413To18481
