import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-675000000-700000000»

/-! Exact changes for sieve primes 1896 through 1904. -/
open Finset
namespace Tail11092009835083From16339To16427

set_option maxRecDepth 16000 in
private theorem row16349 :
    FinalSeventhSieve.rough 11092009835083 16349+36277650=FinalSeventhSieve.rough 11092009835083 16339 :=
  LargeQuotientSieve.row (p:=16349) (q:=678451882) (s:=26047) (rank:=35193881) (tiny:=1895) (pairs:=1085663)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 678451882 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row16361 :
    FinalSeventhSieve.rough 11092009835083 16361+36248462=FinalSeventhSieve.rough 11092009835083 16349 :=
  LargeQuotientSieve.row (p:=16361) (q:=677954271) (s:=26037) (rank:=35169326) (tiny:=1896) (pairs:=1081031)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 677954271 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16361 : FinalSeventhSieve.rough 11092009835083 16361+72526112=FinalSeventhSieve.rough 11092009835083 16339 :=
  LargeQuotientSieve.combine row16349 row16361 rfl

set_option maxRecDepth 16000 in
private theorem row16363 :
    FinalSeventhSieve.rough 11092009835083 16363+36241624=FinalSeventhSieve.rough 11092009835083 16361 :=
  LargeQuotientSieve.row (p:=16363) (q:=677871407) (s:=26035) (rank:=35165321) (tiny:=1897) (pairs:=1078199)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 677871407 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16363 : FinalSeventhSieve.rough 11092009835083 16363+108767736=FinalSeventhSieve.rough 11092009835083 16339 :=
  LargeQuotientSieve.combine to16361 row16363 rfl

set_option maxRecDepth 16000 in
private theorem row16369 :
    FinalSeventhSieve.rough 11092009835083 16369+36225770=FinalSeventhSieve.rough 11092009835083 16363 :=
  LargeQuotientSieve.row (p:=16369) (q:=677622935) (s:=26031) (rank:=35153019) (tiny:=1898) (pairs:=1074648)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 677622935 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16369 : FinalSeventhSieve.rough 11092009835083 16369+144993506=FinalSeventhSieve.rough 11092009835083 16339 :=
  LargeQuotientSieve.combine to16363 row16369 rfl

set_option maxRecDepth 16000 in
private theorem row16381 :
    FinalSeventhSieve.rough 11092009835083 16381+36196829=FinalSeventhSieve.rough 11092009835083 16369 :=
  LargeQuotientSieve.row (p:=16381) (q:=677126538) (s:=26021) (rank:=35128696) (tiny:=1899) (pairs:=1070031)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 677126538 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16381 : FinalSeventhSieve.rough 11092009835083 16381+181190335=FinalSeventhSieve.rough 11092009835083 16339 :=
  LargeQuotientSieve.combine to16369 row16381 rfl

set_option maxRecDepth 16000 in
private theorem row16411 :
    FinalSeventhSieve.rough 11092009835083 16411+36128077=FinalSeventhSieve.rough 11092009835083 16381 :=
  LargeQuotientSieve.row (p:=16411) (q:=675888723) (s:=25997) (rank:=35067903) (tiny:=1900) (pairs:=1062073)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 675888723 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16411 : FinalSeventhSieve.rough 11092009835083 16411+217318412=FinalSeventhSieve.rough 11092009835083 16339 :=
  LargeQuotientSieve.combine to16381 row16411 rfl

set_option maxRecDepth 16000 in
private theorem row16417 :
    FinalSeventhSieve.rough 11092009835083 16417+36112511=FinalSeventhSieve.rough 11092009835083 16411 :=
  LargeQuotientSieve.row (p:=16417) (q:=675641702) (s:=25993) (rank:=35055849) (tiny:=1901) (pairs:=1058562)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 675641702 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16417 : FinalSeventhSieve.rough 11092009835083 16417+253430923=FinalSeventhSieve.rough 11092009835083 16339 :=
  LargeQuotientSieve.combine to16411 row16417 rfl

set_option maxRecDepth 16000 in
private theorem row16421 :
    FinalSeventhSieve.rough 11092009835083 16421+36101220=FinalSeventhSieve.rough 11092009835083 16417 :=
  LargeQuotientSieve.row (p:=16421) (q:=675477122) (s:=25989) (rank:=35047695) (tiny:=1902) (pairs:=1055426)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 675477122 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16421 : FinalSeventhSieve.rough 11092009835083 16421+289532143=FinalSeventhSieve.rough 11092009835083 16339 :=
  LargeQuotientSieve.combine to16417 row16421 rfl

set_option maxRecDepth 16000 in
private theorem row16427 :
    FinalSeventhSieve.rough 11092009835083 16427+36085683=FinalSeventhSieve.rough 11092009835083 16421 :=
  LargeQuotientSieve.row (p:=16427) (q:=675230403) (s:=25985) (rank:=35035616) (tiny:=1903) (pairs:=1051969)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 675230403 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16427 : FinalSeventhSieve.rough 11092009835083 16427+325617826=FinalSeventhSieve.rough 11092009835083 16339 :=
  LargeQuotientSieve.combine to16421 row16427 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 16427+325617826=FinalSeventhSieve.rough 11092009835083 16339 := to16427

end Tail11092009835083From16339To16427
