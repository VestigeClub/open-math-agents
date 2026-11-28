import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-950000000-975000000»

/-! Exact changes for sieve primes 1374 through 1385. -/
open Finset
namespace Tail11092009835083From11369To11489

set_option maxRecDepth 16000 in
private theorem row11383 :
    FinalSeventhSieve.rough 11092009835083 11383+55088247=FinalSeventhSieve.rough 11092009835083 11369 :=
  LargeQuotientSieve.row (p:=11383) (q:=974436425) (s:=31215) (rank:=49613055) (tiny:=1373) (pairs:=5476564)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 974436425 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row11393 :
    FinalSeventhSieve.rough 11092009835083 11393+55031979=FinalSeventhSieve.rough 11092009835083 11383 :=
  LargeQuotientSieve.row (p:=11393) (q:=973581131) (s:=31202) (rank:=49571768) (tiny:=1374) (pairs:=5461584)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 973581131 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11393 : FinalSeventhSieve.rough 11092009835083 11393+110120226=FinalSeventhSieve.rough 11092009835083 11369 :=
  LargeQuotientSieve.combine row11383 row11393 rfl

set_option maxRecDepth 16000 in
private theorem row11399 :
    FinalSeventhSieve.rough 11092009835083 11399+54995497=FinalSeventhSieve.rough 11092009835083 11393 :=
  LargeQuotientSieve.row (p:=11399) (q:=973068675) (s:=31194) (rank:=49547044) (tiny:=1375) (pairs:=5449827)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 973068675 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11399 : FinalSeventhSieve.rough 11092009835083 11399+165115723=FinalSeventhSieve.rough 11092009835083 11369 :=
  LargeQuotientSieve.combine to11393 row11399 rfl

set_option maxRecDepth 16000 in
private theorem row11411 :
    FinalSeventhSieve.rough 11092009835083 11411+54929603=FinalSeventhSieve.rough 11092009835083 11399 :=
  LargeQuotientSieve.row (p:=11411) (q:=972045380) (s:=31177) (rank:=49497681) (tiny:=1376) (pairs:=5433297)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 972045380 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11411 : FinalSeventhSieve.rough 11092009835083 11411+220045326=FinalSeventhSieve.rough 11092009835083 11369 :=
  LargeQuotientSieve.combine to11399 row11411 rfl

set_option maxRecDepth 16000 in
private theorem row11423 :
    FinalSeventhSieve.rough 11092009835083 11423+54863813=FinalSeventhSieve.rough 11092009835083 11411 :=
  LargeQuotientSieve.row (p:=11423) (q:=971024234) (s:=31161) (rank:=49448443) (tiny:=1377) (pairs:=5416746)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 971024234 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11423 : FinalSeventhSieve.rough 11092009835083 11423+274909139=FinalSeventhSieve.rough 11092009835083 11369 :=
  LargeQuotientSieve.combine to11411 row11423 rfl

set_option maxRecDepth 16000 in
private theorem row11437 :
    FinalSeventhSieve.rough 11092009835083 11437+54788226=FinalSeventhSieve.rough 11092009835083 11423 :=
  LargeQuotientSieve.row (p:=11437) (q:=969835606) (s:=31142) (rank:=49390864) (tiny:=1378) (pairs:=5398739)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 969835606 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11437 : FinalSeventhSieve.rough 11092009835083 11437+329697365=FinalSeventhSieve.rough 11092009835083 11369 :=
  LargeQuotientSieve.combine to11423 row11437 rfl

set_option maxRecDepth 16000 in
private theorem row11443 :
    FinalSeventhSieve.rough 11092009835083 11443+54752045=FinalSeventhSieve.rough 11092009835083 11437 :=
  LargeQuotientSieve.row (p:=11443) (q:=969327085) (s:=31134) (rank:=49366306) (tiny:=1379) (pairs:=5387117)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 969327085 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11443 : FinalSeventhSieve.rough 11092009835083 11443+384449410=FinalSeventhSieve.rough 11092009835083 11369 :=
  LargeQuotientSieve.combine to11437 row11443 rfl

set_option maxRecDepth 16000 in
private theorem row11447 :
    FinalSeventhSieve.rough 11092009835083 11447+54725594=FinalSeventhSieve.rough 11092009835083 11443 :=
  LargeQuotientSieve.row (p:=11447) (q:=968988366) (s:=31128) (rank:=49349865) (tiny:=1380) (pairs:=5377108)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 968988366 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11447 : FinalSeventhSieve.rough 11092009835083 11447+439175004=FinalSeventhSieve.rough 11092009835083 11369 :=
  LargeQuotientSieve.combine to11443 row11447 rfl

set_option maxRecDepth 16000 in
private theorem row11467 :
    FinalSeventhSieve.rough 11092009835083 11467+54621240=FinalSeventhSieve.rough 11092009835083 11447 :=
  LargeQuotientSieve.row (p:=11467) (q:=967298319) (s:=31101) (rank:=49268116) (tiny:=1381) (pairs:=5354504)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 967298319 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11467 : FinalSeventhSieve.rough 11092009835083 11467+493796244=FinalSeventhSieve.rough 11092009835083 11369 :=
  LargeQuotientSieve.combine to11447 row11467 rfl

set_option maxRecDepth 16000 in
private theorem row11471 :
    FinalSeventhSieve.rough 11092009835083 11471+54594989=FinalSeventhSieve.rough 11092009835083 11467 :=
  LargeQuotientSieve.row (p:=11471) (q:=966961017) (s:=31095) (rank:=49251907) (tiny:=1382) (pairs:=5344463)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 966961017 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11471 : FinalSeventhSieve.rough 11092009835083 11471+548391233=FinalSeventhSieve.rough 11092009835083 11369 :=
  LargeQuotientSieve.combine to11467 row11471 rfl

set_option maxRecDepth 16000 in
private theorem row11483 :
    FinalSeventhSieve.rough 11092009835083 11483+54529957=FinalSeventhSieve.rough 11092009835083 11471 :=
  LargeQuotientSieve.row (p:=11483) (q:=965950521) (s:=31079) (rank:=49203042) (tiny:=1383) (pairs:=5328297)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 965950521 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11483 : FinalSeventhSieve.rough 11092009835083 11483+602921190=FinalSeventhSieve.rough 11092009835083 11369 :=
  LargeQuotientSieve.combine to11471 row11483 rfl

set_option maxRecDepth 16000 in
private theorem row11489 :
    FinalSeventhSieve.rough 11092009835083 11489+54494129=FinalSeventhSieve.rough 11092009835083 11483 :=
  LargeQuotientSieve.row (p:=11489) (q:=965446064) (s:=31071) (rank:=49178780) (tiny:=1384) (pairs:=5316732)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 965446064 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11489 : FinalSeventhSieve.rough 11092009835083 11489+657415319=FinalSeventhSieve.rough 11092009835083 11369 :=
  LargeQuotientSieve.combine to11483 row11489 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 11489+657415319=FinalSeventhSieve.rough 11092009835083 11369 := to11489

end Tail11092009835083From11369To11489
