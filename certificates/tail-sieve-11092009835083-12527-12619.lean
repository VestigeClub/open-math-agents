import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-875000000-900000000»

/-! Exact changes for sieve primes 1497 through 1508. -/
open Finset
namespace Tail11092009835083From12527To12619

set_option maxRecDepth 16000 in
private theorem row12539 :
    FinalSeventhSieve.rough 11092009835083 12539+49188003=FinalSeventhSieve.rough 11092009835083 12527 :=
  LargeQuotientSieve.row (p:=12539) (q:=884600832) (s:=29742) (rank:=45262616) (tiny:=1496) (pairs:=3926882)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 884600832 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row12541 :
    FinalSeventhSieve.rough 11092009835083 12541+49174472=FinalSeventhSieve.rough 11092009835083 12539 :=
  LargeQuotientSieve.row (p:=12541) (q:=884459758) (s:=29739) (rank:=45255755) (tiny:=1497) (pairs:=3920213)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 884459758 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12541 : FinalSeventhSieve.rough 11092009835083 12541+98362475=FinalSeventhSieve.rough 11092009835083 12527 :=
  LargeQuotientSieve.combine row12539 row12541 rfl

set_option maxRecDepth 16000 in
private theorem row12547 :
    FinalSeventhSieve.rough 11092009835083 12547+49145032=FinalSeventhSieve.rough 11092009835083 12541 :=
  LargeQuotientSieve.row (p:=12547) (q:=884036808) (s:=29732) (rank:=45235203) (tiny:=1498) (pairs:=3911326)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 884036808 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12547 : FinalSeventhSieve.rough 11092009835083 12547+147507507=FinalSeventhSieve.rough 11092009835083 12527 :=
  LargeQuotientSieve.combine to12541 row12547 rfl

set_option maxRecDepth 16000 in
private theorem row12553 :
    FinalSeventhSieve.rough 11092009835083 12553+49115598=FinalSeventhSieve.rough 11092009835083 12547 :=
  LargeQuotientSieve.row (p:=12553) (q:=883614262) (s:=29725) (rank:=45214627) (tiny:=1499) (pairs:=3902469)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 883614262 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12553 : FinalSeventhSieve.rough 11092009835083 12553+196623105=FinalSeventhSieve.rough 11092009835083 12527 :=
  LargeQuotientSieve.combine to12547 row12553 rfl

set_option maxRecDepth 16000 in
private theorem row12569 :
    FinalSeventhSieve.rough 11092009835083 12569+49046482=FinalSeventhSieve.rough 11092009835083 12553 :=
  LargeQuotientSieve.row (p:=12569) (q:=882489445) (s:=29706) (rank:=45160054) (tiny:=1500) (pairs:=3887927)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 882489445 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12569 : FinalSeventhSieve.rough 11092009835083 12569+245669587=FinalSeventhSieve.rough 11092009835083 12527 :=
  LargeQuotientSieve.combine to12553 row12569 rfl

set_option maxRecDepth 16000 in
private theorem row12577 :
    FinalSeventhSieve.rough 11092009835083 12577+49009223=FinalSeventhSieve.rough 11092009835083 12569 :=
  LargeQuotientSieve.row (p:=12577) (q:=881928109) (s:=29697) (rank:=45132764) (tiny:=1501) (pairs:=3877959)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 881928109 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12577 : FinalSeventhSieve.rough 11092009835083 12577+294678810=FinalSeventhSieve.rough 11092009835083 12527 :=
  LargeQuotientSieve.combine to12569 row12577 rfl

set_option maxRecDepth 16000 in
private theorem row12583 :
    FinalSeventhSieve.rough 11092009835083 12583+48979966=FinalSeventhSieve.rough 11092009835083 12577 :=
  LargeQuotientSieve.row (p:=12583) (q:=881507576) (s:=29690) (rank:=45112366) (tiny:=1502) (pairs:=3869101)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 881507576 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12583 : FinalSeventhSieve.rough 11092009835083 12583+343658776=FinalSeventhSieve.rough 11092009835083 12527 :=
  LargeQuotientSieve.combine to12577 row12583 rfl

set_option maxRecDepth 16000 in
private theorem row12589 :
    FinalSeventhSieve.rough 11092009835083 12589+48950711=FinalSeventhSieve.rough 11092009835083 12583 :=
  LargeQuotientSieve.row (p:=12589) (q:=881087444) (s:=29683) (rank:=45091943) (tiny:=1503) (pairs:=3860270)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 881087444 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12589 : FinalSeventhSieve.rough 11092009835083 12589+392609487=FinalSeventhSieve.rough 11092009835083 12527 :=
  LargeQuotientSieve.combine to12583 row12589 rfl

set_option maxRecDepth 16000 in
private theorem row12601 :
    FinalSeventhSieve.rough 11092009835083 12601+48897970=FinalSeventhSieve.rough 11092009835083 12589 :=
  LargeQuotientSieve.row (p:=12601) (q:=880248379) (s:=29668) (rank:=45051393) (tiny:=1504) (pairs:=3848080)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 880248379 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12601 : FinalSeventhSieve.rough 11092009835083 12601+441507457=FinalSeventhSieve.rough 11092009835083 12527 :=
  LargeQuotientSieve.combine to12589 row12601 rfl

set_option maxRecDepth 16000 in
private theorem row12611 :
    FinalSeventhSieve.rough 11092009835083 12611+48852986=FinalSeventhSieve.rough 11092009835083 12601 :=
  LargeQuotientSieve.row (p:=12611) (q:=879550379) (s:=29657) (rank:=45017459) (tiny:=1505) (pairs:=3837031)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 879550379 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12611 : FinalSeventhSieve.rough 11092009835083 12611+490360443=FinalSeventhSieve.rough 11092009835083 12527 :=
  LargeQuotientSieve.combine to12601 row12611 rfl

set_option maxRecDepth 16000 in
private theorem row12613 :
    FinalSeventhSieve.rough 11092009835083 12613+48839714=FinalSeventhSieve.rough 11092009835083 12611 :=
  LargeQuotientSieve.row (p:=12613) (q:=879410912) (s:=29654) (rank:=45010721) (tiny:=1506) (pairs:=3830498)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 879410912 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12613 : FinalSeventhSieve.rough 11092009835083 12613+539200157=FinalSeventhSieve.rough 11092009835083 12527 :=
  LargeQuotientSieve.combine to12611 row12613 rfl

set_option maxRecDepth 16000 in
private theorem row12619 :
    FinalSeventhSieve.rough 11092009835083 12619+48810684=FinalSeventhSieve.rough 11092009835083 12613 :=
  LargeQuotientSieve.row (p:=12619) (q:=878992775) (s:=29647) (rank:=44990447) (tiny:=1507) (pairs:=3821743)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 878992775 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12619 : FinalSeventhSieve.rough 11092009835083 12619+588010841=FinalSeventhSieve.rough 11092009835083 12527 :=
  LargeQuotientSieve.combine to12613 row12619 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 12619+588010841=FinalSeventhSieve.rough 11092009835083 12527 := to12619

end Tail11092009835083From12527To12619
