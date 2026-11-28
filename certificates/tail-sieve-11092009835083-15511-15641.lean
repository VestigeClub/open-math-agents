import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-700000000-725000000»

/-! Exact changes for sieve primes 1812 through 1823. -/
open Finset
namespace Tail11092009835083From15511To15641

set_option maxRecDepth 16000 in
private theorem row15527 :
    FinalSeventhSieve.rough 11092009835083 15527+38442879=FinalSeventhSieve.rough 11092009835083 15511 :=
  LargeQuotientSieve.row (p:=15527) (q:=714369152) (s:=26727) (rank:=36958163) (tiny:=1811) (pairs:=1486526)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 714369152 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row15541 :
    FinalSeventhSieve.rough 11092009835083 15541+38405073=FinalSeventhSieve.rough 11092009835083 15527 :=
  LargeQuotientSieve.row (p:=15541) (q:=713725618) (s:=26715) (rank:=36926641) (tiny:=1812) (pairs:=1480243)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 713725618 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15541 : FinalSeventhSieve.rough 11092009835083 15541+76847952=FinalSeventhSieve.rough 11092009835083 15511 :=
  LargeQuotientSieve.combine row15527 row15541 rfl

set_option maxRecDepth 16000 in
private theorem row15551 :
    FinalSeventhSieve.rough 11092009835083 15551+38377339=FinalSeventhSieve.rough 11092009835083 15541 :=
  LargeQuotientSieve.row (p:=15551) (q:=713266660) (s:=26707) (rank:=36904215) (tiny:=1813) (pairs:=1474936)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 713266660 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15551 : FinalSeventhSieve.rough 11092009835083 15551+115225291=FinalSeventhSieve.rough 11092009835083 15511 :=
  LargeQuotientSieve.combine to15541 row15551 rfl

set_option maxRecDepth 16000 in
private theorem row15559 :
    FinalSeventhSieve.rough 11092009835083 15559+38354412=FinalSeventhSieve.rough 11092009835083 15551 :=
  LargeQuotientSieve.row (p:=15559) (q:=712899918) (s:=26700) (rank:=36886109) (tiny:=1814) (pairs:=1470116)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 712899918 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15559 : FinalSeventhSieve.rough 11092009835083 15559+153579703=FinalSeventhSieve.rough 11092009835083 15511 :=
  LargeQuotientSieve.combine to15551 row15559 rfl

set_option maxRecDepth 16000 in
private theorem row15569 :
    FinalSeventhSieve.rough 11092009835083 15569+38326721=FinalSeventhSieve.rough 11092009835083 15559 :=
  LargeQuotientSieve.row (p:=15569) (q:=712442021) (s:=26691) (rank:=36863735) (tiny:=1815) (pairs:=1464800)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 712442021 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15569 : FinalSeventhSieve.rough 11092009835083 15569+191906424=FinalSeventhSieve.rough 11092009835083 15511 :=
  LargeQuotientSieve.combine to15559 row15569 rfl

set_option maxRecDepth 16000 in
private theorem row15581 :
    FinalSeventhSieve.rough 11092009835083 15581+38293952=FinalSeventhSieve.rough 11092009835083 15569 :=
  LargeQuotientSieve.row (p:=15581) (q:=711893321) (s:=26681) (rank:=36836671) (tiny:=1816) (pairs:=1459096)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 711893321 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15581 : FinalSeventhSieve.rough 11092009835083 15581+230200376=FinalSeventhSieve.rough 11092009835083 15511 :=
  LargeQuotientSieve.combine to15569 row15581 rfl

set_option maxRecDepth 16000 in
private theorem row15583 :
    FinalSeventhSieve.rough 11092009835083 15583+38286096=FinalSeventhSieve.rough 11092009835083 15581 :=
  LargeQuotientSieve.row (p:=15583) (q:=711801953) (s:=26679) (rank:=36832196) (tiny:=1817) (pairs:=1455716)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 711801953 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15583 : FinalSeventhSieve.rough 11092009835083 15583+268486472=FinalSeventhSieve.rough 11092009835083 15511 :=
  LargeQuotientSieve.combine to15581 row15583 rfl

set_option maxRecDepth 16000 in
private theorem row15601 :
    FinalSeventhSieve.rough 11092009835083 15601+38238607=FinalSeventhSieve.rough 11092009835083 15583 :=
  LargeQuotientSieve.row (p:=15601) (q:=710980695) (s:=26664) (rank:=36791866) (tiny:=1818) (pairs:=1448558)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 710980695 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15601 : FinalSeventhSieve.rough 11092009835083 15601+306725079=FinalSeventhSieve.rough 11092009835083 15511 :=
  LargeQuotientSieve.combine to15583 row15601 rfl

set_option maxRecDepth 16000 in
private theorem row15607 :
    FinalSeventhSieve.rough 11092009835083 15607+38220941=FinalSeventhSieve.rough 11092009835083 15601 :=
  LargeQuotientSieve.row (p:=15607) (q:=710707364) (s:=26659) (rank:=36778480) (tiny:=1819) (pairs:=1444279)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 710707364 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15607 : FinalSeventhSieve.rough 11092009835083 15607+344946020=FinalSeventhSieve.rough 11092009835083 15511 :=
  LargeQuotientSieve.combine to15601 row15607 rfl

set_option maxRecDepth 16000 in
private theorem row15619 :
    FinalSeventhSieve.rough 11092009835083 15619+38188437=FinalSeventhSieve.rough 11092009835083 15607 :=
  LargeQuotientSieve.row (p:=15619) (q:=710161331) (s:=26648) (rank:=36751719) (tiny:=1820) (pairs:=1438537)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 710161331 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15619 : FinalSeventhSieve.rough 11092009835083 15619+383134457=FinalSeventhSieve.rough 11092009835083 15511 :=
  LargeQuotientSieve.combine to15607 row15619 rfl

set_option maxRecDepth 16000 in
private theorem row15629 :
    FinalSeventhSieve.rough 11092009835083 15629+38161061=FinalSeventhSieve.rough 11092009835083 15619 :=
  LargeQuotientSieve.row (p:=15629) (q:=709706944) (s:=26640) (rank:=36729566) (tiny:=1821) (pairs:=1433315)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 709706944 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15629 : FinalSeventhSieve.rough 11092009835083 15629+421295518=FinalSeventhSieve.rough 11092009835083 15511 :=
  LargeQuotientSieve.combine to15619 row15629 rfl

set_option maxRecDepth 16000 in
private theorem row15641 :
    FinalSeventhSieve.rough 11092009835083 15641+38128601=FinalSeventhSieve.rough 11092009835083 15629 :=
  LargeQuotientSieve.row (p:=15641) (q:=709162447) (s:=26630) (rank:=36702765) (tiny:=1822) (pairs:=1427657)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 709162447 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15641 : FinalSeventhSieve.rough 11092009835083 15641+459424119=FinalSeventhSieve.rough 11092009835083 15511 :=
  LargeQuotientSieve.combine to15629 row15641 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 15641+459424119=FinalSeventhSieve.rough 11092009835083 15511 := to15641

end Tail11092009835083From15511To15641
