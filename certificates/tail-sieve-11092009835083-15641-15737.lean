import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-700000000-725000000»

/-! Exact changes for sieve primes 1824 through 1835. -/
open Finset
namespace Tail11092009835083From15641To15737

set_option maxRecDepth 16000 in
private theorem row15643 :
    FinalSeventhSieve.rough 11092009835083 15643+38120821=FinalSeventhSieve.rough 11092009835083 15641 :=
  LargeQuotientSieve.row (p:=15643) (q:=709071778) (s:=26628) (rank:=36698332) (tiny:=1823) (pairs:=1424311)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 709071778 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row15647 :
    FinalSeventhSieve.rough 11092009835083 15647+38108110=FinalSeventhSieve.rough 11092009835083 15643 :=
  LargeQuotientSieve.row (p:=15647) (q:=708890511) (s:=26624) (rank:=36689397) (tiny:=1824) (pairs:=1420536)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 708890511 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15647 : FinalSeventhSieve.rough 11092009835083 15647+76228931=FinalSeventhSieve.rough 11092009835083 15641 :=
  LargeQuotientSieve.combine row15643 row15647 rfl

set_option maxRecDepth 16000 in
private theorem row15649 :
    FinalSeventhSieve.rough 11092009835083 15649+38100348=FinalSeventhSieve.rough 11092009835083 15647 :=
  LargeQuotientSieve.row (p:=15649) (q:=708799912) (s:=26623) (rank:=36684997) (tiny:=1825) (pairs:=1417175)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 708799912 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15649 : FinalSeventhSieve.rough 11092009835083 15649+114329279=FinalSeventhSieve.rough 11092009835083 15641 :=
  LargeQuotientSieve.combine to15647 row15649 rfl

set_option maxRecDepth 16000 in
private theorem row15661 :
    FinalSeventhSieve.rough 11092009835083 15661+38068062=FinalSeventhSieve.rough 11092009835083 15649 :=
  LargeQuotientSieve.row (p:=15661) (q:=708256805) (s:=26613) (rank:=36658324) (tiny:=1826) (pairs:=1411563)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 708256805 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15661 : FinalSeventhSieve.rough 11092009835083 15661+152397341=FinalSeventhSieve.rough 11092009835083 15641 :=
  LargeQuotientSieve.combine to15649 row15661 rfl

set_option maxRecDepth 16000 in
private theorem row15667 :
    FinalSeventhSieve.rough 11092009835083 15667+38050497=FinalSeventhSieve.rough 11092009835083 15661 :=
  LargeQuotientSieve.row (p:=15667) (q:=707985564) (s:=26607) (rank:=36644987) (tiny:=1827) (pairs:=1407336)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 707985564 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15667 : FinalSeventhSieve.rough 11092009835083 15667+190447838=FinalSeventhSieve.rough 11092009835083 15641 :=
  LargeQuotientSieve.combine to15661 row15667 rfl

set_option maxRecDepth 16000 in
private theorem row15671 :
    FinalSeventhSieve.rough 11092009835083 15671+38037835=FinalSeventhSieve.rough 11092009835083 15667 :=
  LargeQuotientSieve.row (p:=15671) (q:=707804851) (s:=26604) (rank:=36636095) (tiny:=1828) (pairs:=1403567)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 707804851 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15671 : FinalSeventhSieve.rough 11092009835083 15671+228485673=FinalSeventhSieve.rough 11092009835083 15641 :=
  LargeQuotientSieve.combine to15667 row15671 rfl

set_option maxRecDepth 16000 in
private theorem row15679 :
    FinalSeventhSieve.rough 11092009835083 15679+38015453=FinalSeventhSieve.rough 11092009835083 15671 :=
  LargeQuotientSieve.row (p:=15679) (q:=707443704) (s:=26597) (rank:=36618372) (tiny:=1829) (pairs:=1398909)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 707443704 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15679 : FinalSeventhSieve.rough 11092009835083 15679+266501126=FinalSeventhSieve.rough 11092009835083 15641 :=
  LargeQuotientSieve.combine to15671 row15679 rfl

set_option maxRecDepth 16000 in
private theorem row15683 :
    FinalSeventhSieve.rough 11092009835083 15683+38002844=FinalSeventhSieve.rough 11092009835083 15679 :=
  LargeQuotientSieve.row (p:=15683) (q:=707263268) (s:=26594) (rank:=36609552) (tiny:=1830) (pairs:=1395121)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 707263268 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15683 : FinalSeventhSieve.rough 11092009835083 15683+304503970=FinalSeventhSieve.rough 11092009835083 15641 :=
  LargeQuotientSieve.combine to15679 row15683 rfl

set_option maxRecDepth 16000 in
private theorem row15727 :
    FinalSeventhSieve.rough 11092009835083 15727+37892937=FinalSeventhSieve.rough 11092009835083 15683 :=
  LargeQuotientSieve.row (p:=15727) (q:=705284532) (s:=26557) (rank:=36512417) (tiny:=1831) (pairs:=1382350)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 705284532 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15727 : FinalSeventhSieve.rough 11092009835083 15727+342396907=FinalSeventhSieve.rough 11092009835083 15641 :=
  LargeQuotientSieve.combine to15683 row15727 rfl

set_option maxRecDepth 16000 in
private theorem row15731 :
    FinalSeventhSieve.rough 11092009835083 15731+37880438=FinalSeventhSieve.rough 11092009835083 15727 :=
  LargeQuotientSieve.row (p:=15731) (q:=705105195) (s:=26553) (rank:=36503622) (tiny:=1832) (pairs:=1378647)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 705105195 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15731 : FinalSeventhSieve.rough 11092009835083 15731+380277345=FinalSeventhSieve.rough 11092009835083 15641 :=
  LargeQuotientSieve.combine to15727 row15731 rfl

set_option maxRecDepth 16000 in
private theorem row15733 :
    FinalSeventhSieve.rough 11092009835083 15733+37872732=FinalSeventhSieve.rough 11092009835083 15731 :=
  LargeQuotientSieve.row (p:=15733) (q:=705015561) (s:=26552) (rank:=36499205) (tiny:=1833) (pairs:=1375359)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 705015561 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15733 : FinalSeventhSieve.rough 11092009835083 15733+418150077=FinalSeventhSieve.rough 11092009835083 15641 :=
  LargeQuotientSieve.combine to15731 row15733 rfl

set_option maxRecDepth 16000 in
private theorem row15737 :
    FinalSeventhSieve.rough 11092009835083 15737+37860238=FinalSeventhSieve.rough 11092009835083 15733 :=
  LargeQuotientSieve.row (p:=15737) (q:=704836362) (s:=26548) (rank:=36490443) (tiny:=1834) (pairs:=1371628)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ700000000To725000000.count_correct 704836362 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15737 : FinalSeventhSieve.rough 11092009835083 15737+456010315=FinalSeventhSieve.rough 11092009835083 15641 :=
  LargeQuotientSieve.combine to15733 row15737 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 15737+456010315=FinalSeventhSieve.rough 11092009835083 15641 := to15737

end Tail11092009835083From15641To15737
