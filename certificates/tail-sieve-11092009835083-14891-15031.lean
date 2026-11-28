import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-725000000-750000000»

/-! Exact changes for sieve primes 1746 through 1757. -/
open Finset
namespace Tail11092009835083From14891To15031

set_option maxRecDepth 16000 in
private theorem row14897 :
    FinalSeventhSieve.rough 11092009835083 14897+40296872=FinalSeventhSieve.rough 11092009835083 14891 :=
  LargeQuotientSieve.row (p:=14897) (q:=744580105) (s:=27286) (rank:=38438244) (tiny:=1745) (pairs:=1860372)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 744580105 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row14923 :
    FinalSeventhSieve.rough 11092009835083 14923+40222560=FinalSeventhSieve.rough 11092009835083 14897 :=
  LargeQuotientSieve.row (p:=14923) (q:=743282840) (s:=27263) (rank:=38374823) (tiny:=1746) (pairs:=1849482)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 743282840 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14923 : FinalSeventhSieve.rough 11092009835083 14923+80519432=FinalSeventhSieve.rough 11092009835083 14891 :=
  LargeQuotientSieve.combine row14897 row14923 rfl

set_option maxRecDepth 16000 in
private theorem row14929 :
    FinalSeventhSieve.rough 11092009835083 14929+40202996=FinalSeventhSieve.rough 11092009835083 14923 :=
  LargeQuotientSieve.row (p:=14929) (q:=742984113) (s:=27257) (rank:=38360348) (tiny:=1747) (pairs:=1844394)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 742984113 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14929 : FinalSeventhSieve.rough 11092009835083 14929+120722428=FinalSeventhSieve.rough 11092009835083 14891 :=
  LargeQuotientSieve.combine to14923 row14929 rfl

set_option maxRecDepth 16000 in
private theorem row14939 :
    FinalSeventhSieve.rough 11092009835083 14939+40172435=FinalSeventhSieve.rough 11092009835083 14929 :=
  LargeQuotientSieve.row (p:=14939) (q:=742486768) (s:=27248) (rank:=38336038) (tiny:=1748) (pairs:=1838144)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 742486768 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14939 : FinalSeventhSieve.rough 11092009835083 14939+160894863=FinalSeventhSieve.rough 11092009835083 14891 :=
  LargeQuotientSieve.combine to14929 row14939 rfl

set_option maxRecDepth 16000 in
private theorem row14947 :
    FinalSeventhSieve.rough 11092009835083 14947+40147307=FinalSeventhSieve.rough 11092009835083 14939 :=
  LargeQuotientSieve.row (p:=14947) (q:=742089371) (s:=27241) (rank:=38316532) (tiny:=1749) (pairs:=1832523)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 742089371 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14947 : FinalSeventhSieve.rough 11092009835083 14947+201042170=FinalSeventhSieve.rough 11092009835083 14891 :=
  LargeQuotientSieve.combine to14939 row14947 rfl

set_option maxRecDepth 16000 in
private theorem row14951 :
    FinalSeventhSieve.rough 11092009835083 14951+40133080=FinalSeventhSieve.rough 11092009835083 14947 :=
  LargeQuotientSieve.row (p:=14951) (q:=741890832) (s:=27237) (rank:=38306816) (tiny:=1750) (pairs:=1828013)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 741890832 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14951 : FinalSeventhSieve.rough 11092009835083 14951+241175250=FinalSeventhSieve.rough 11092009835083 14891 :=
  LargeQuotientSieve.combine to14947 row14951 rfl

set_option maxRecDepth 16000 in
private theorem row14957 :
    FinalSeventhSieve.rough 11092009835083 14957+40113438=FinalSeventhSieve.rough 11092009835083 14951 :=
  LargeQuotientSieve.row (p:=14957) (q:=741593222) (s:=27232) (rank:=38292244) (tiny:=1751) (pairs:=1822944)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 741593222 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14957 : FinalSeventhSieve.rough 11092009835083 14957+281288688=FinalSeventhSieve.rough 11092009835083 14891 :=
  LargeQuotientSieve.combine to14951 row14957 rfl

set_option maxRecDepth 16000 in
private theorem row14969 :
    FinalSeventhSieve.rough 11092009835083 14969+40077424=FinalSeventhSieve.rough 11092009835083 14957 :=
  LargeQuotientSieve.row (p:=14969) (q:=740998719) (s:=27221) (rank:=38262927) (tiny:=1752) (pairs:=1816248)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 740998719 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14969 : FinalSeventhSieve.rough 11092009835083 14969+321366112=FinalSeventhSieve.rough 11092009835083 14891 :=
  LargeQuotientSieve.combine to14957 row14969 rfl

set_option maxRecDepth 16000 in
private theorem row14983 :
    FinalSeventhSieve.rough 11092009835083 14983+40036228=FinalSeventhSieve.rough 11092009835083 14969 :=
  LargeQuotientSieve.row (p:=14983) (q:=740306336) (s:=27208) (rank:=38228972) (tiny:=1753) (pairs:=1809008)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 740306336 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14983 : FinalSeventhSieve.rough 11092009835083 14983+361402340=FinalSeventhSieve.rough 11092009835083 14891 :=
  LargeQuotientSieve.combine to14969 row14983 rfl

set_option maxRecDepth 16000 in
private theorem row15013 :
    FinalSeventhSieve.rough 11092009835083 15013+39952053=FinalSeventhSieve.rough 11092009835083 14983 :=
  LargeQuotientSieve.row (p:=15013) (q:=738827005) (s:=27181) (rank:=38156473) (tiny:=1754) (pairs:=1797333)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 738827005 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15013 : FinalSeventhSieve.rough 11092009835083 15013+401354393=FinalSeventhSieve.rough 11092009835083 14891 :=
  LargeQuotientSieve.combine to14983 row15013 rfl

set_option maxRecDepth 16000 in
private theorem row15017 :
    FinalSeventhSieve.rough 11092009835083 15017+39937882=FinalSeventhSieve.rough 11092009835083 15013 :=
  LargeQuotientSieve.row (p:=15017) (q:=738630208) (s:=27177) (rank:=38146721) (tiny:=1755) (pairs:=1792915)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 738630208 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15017 : FinalSeventhSieve.rough 11092009835083 15017+441292275=FinalSeventhSieve.rough 11092009835083 14891 :=
  LargeQuotientSieve.combine to15013 row15017 rfl

set_option maxRecDepth 16000 in
private theorem row15031 :
    FinalSeventhSieve.rough 11092009835083 15031+39896970=FinalSeventhSieve.rough 11092009835083 15017 :=
  LargeQuotientSieve.row (p:=15031) (q:=737942241) (s:=27165) (rank:=38112987) (tiny:=1756) (pairs:=1785738)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 737942241 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15031 : FinalSeventhSieve.rough 11092009835083 15031+481189245=FinalSeventhSieve.rough 11092009835083 14891 :=
  LargeQuotientSieve.combine to15017 row15031 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 15031+481189245=FinalSeventhSieve.rough 11092009835083 14891 := to15031

end Tail11092009835083From14891To15031
