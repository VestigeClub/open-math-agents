import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1075000000-1100000000»

/-! Exact changes for sieve primes 3042 through 3053. -/
open Finset
namespace Tail30110134441897From27847To27967

set_option maxRecDepth 16000 in
private theorem row27851 :
    FinalSeventhSieve.rough 30110134441897 27851+54998737=FinalSeventhSieve.rough 30110134441897 27847 :=
  LargeQuotientSieve.row (p:=27851) (q:=1081115020) (s:=32880) (rank:=54754186) (tiny:=3041) (pairs:=247591)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1081115020 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row27883 :
    FinalSeventhSieve.rough 30110134441897 27883+54936230=FinalSeventhSieve.rough 30110134441897 27851 :=
  LargeQuotientSieve.row (p:=27883) (q:=1079874276) (s:=32861) (rank:=54694592) (tiny:=3042) (pairs:=244679)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1079874276 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27883 : FinalSeventhSieve.rough 30110134441897 27883+109934967=FinalSeventhSieve.rough 30110134441897 27847 :=
  LargeQuotientSieve.combine row27851 row27883 rfl

set_option maxRecDepth 16000 in
private theorem row27893 :
    FinalSeventhSieve.rough 30110134441897 27893+54915952=FinalSeventhSieve.rough 30110134441897 27883 :=
  LargeQuotientSieve.row (p:=27893) (q:=1079487127) (s:=32855) (rank:=54675916) (tiny:=3043) (pairs:=243078)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1079487127 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27893 : FinalSeventhSieve.rough 30110134441897 27893+164850919=FinalSeventhSieve.rough 30110134441897 27847 :=
  LargeQuotientSieve.combine to27883 row27893 rfl

set_option maxRecDepth 16000 in
private theorem row27901 :
    FinalSeventhSieve.rough 30110134441897 27901+54899585=FinalSeventhSieve.rough 30110134441897 27893 :=
  LargeQuotientSieve.row (p:=27901) (q:=1079177608) (s:=32850) (rank:=54661070) (tiny:=3044) (pairs:=241558)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1079177608 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27901 : FinalSeventhSieve.rough 30110134441897 27901+219750504=FinalSeventhSieve.rough 30110134441897 27847 :=
  LargeQuotientSieve.combine to27893 row27901 rfl

set_option maxRecDepth 16000 in
private theorem row27917 :
    FinalSeventhSieve.rough 30110134441897 27917+54867987=FinalSeventhSieve.rough 30110134441897 27901 :=
  LargeQuotientSieve.row (p:=27917) (q:=1078559101) (s:=32841) (rank:=54631418) (tiny:=3045) (pairs:=239613)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1078559101 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27917 : FinalSeventhSieve.rough 30110134441897 27917+274618491=FinalSeventhSieve.rough 30110134441897 27847 :=
  LargeQuotientSieve.combine to27901 row27917 rfl

set_option maxRecDepth 16000 in
private theorem row27919 :
    FinalSeventhSieve.rough 30110134441897 27919+54863171=FinalSeventhSieve.rough 30110134441897 27917 :=
  LargeQuotientSieve.row (p:=27919) (q:=1078481838) (s:=32840) (rank:=54627744) (tiny:=3046) (pairs:=238472)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1078481838 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27919 : FinalSeventhSieve.rough 30110134441897 27919+329481662=FinalSeventhSieve.rough 30110134441897 27847 :=
  LargeQuotientSieve.combine to27917 row27919 rfl

set_option maxRecDepth 16000 in
private theorem row27941 :
    FinalSeventhSieve.rough 30110134441897 27941+54820053=FinalSeventhSieve.rough 30110134441897 27919 :=
  LargeQuotientSieve.row (p:=27941) (q:=1077632670) (s:=32827) (rank:=54586868) (tiny:=3047) (pairs:=236231)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1077632670 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27941 : FinalSeventhSieve.rough 30110134441897 27941+384301715=FinalSeventhSieve.rough 30110134441897 27847 :=
  LargeQuotientSieve.combine to27919 row27941 rfl

set_option maxRecDepth 16000 in
private theorem row27943 :
    FinalSeventhSieve.rough 30110134441897 27943+54815254=FinalSeventhSieve.rough 30110134441897 27941 :=
  LargeQuotientSieve.row (p:=27943) (q:=1077555539) (s:=32826) (rank:=54583194) (tiny:=3048) (pairs:=235107)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1077555539 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27943 : FinalSeventhSieve.rough 30110134441897 27943+439116969=FinalSeventhSieve.rough 30110134441897 27847 :=
  LargeQuotientSieve.combine to27941 row27943 rfl

set_option maxRecDepth 16000 in
private theorem row27947 :
    FinalSeventhSieve.rough 30110134441897 27947+54806573=FinalSeventhSieve.rough 30110134441897 27943 :=
  LargeQuotientSieve.row (p:=27947) (q:=1077401311) (s:=32823) (rank:=54575763) (tiny:=3049) (pairs:=233858)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1077401311 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27947 : FinalSeventhSieve.rough 30110134441897 27947+493923542=FinalSeventhSieve.rough 30110134441897 27847 :=
  LargeQuotientSieve.combine to27943 row27947 rfl

set_option maxRecDepth 16000 in
private theorem row27953 :
    FinalSeventhSieve.rough 30110134441897 27953+54794052=FinalSeventhSieve.rough 30110134441897 27947 :=
  LargeQuotientSieve.row (p:=27953) (q:=1077170051) (s:=32820) (rank:=54564601) (tiny:=3050) (pairs:=232500)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1077170051 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27953 : FinalSeventhSieve.rough 30110134441897 27953+548717594=FinalSeventhSieve.rough 30110134441897 27847 :=
  LargeQuotientSieve.combine to27947 row27953 rfl

set_option maxRecDepth 16000 in
private theorem row27961 :
    FinalSeventhSieve.rough 30110134441897 27961+54777900=FinalSeventhSieve.rough 30110134441897 27953 :=
  LargeQuotientSieve.row (p:=27961) (q:=1076861859) (s:=32815) (rank:=54549926) (tiny:=3051) (pairs:=231024)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1076861859 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27961 : FinalSeventhSieve.rough 30110134441897 27961+603495494=FinalSeventhSieve.rough 30110134441897 27847 :=
  LargeQuotientSieve.combine to27953 row27961 rfl

set_option maxRecDepth 16000 in
private theorem row27967 :
    FinalSeventhSieve.rough 30110134441897 27967+54765427=FinalSeventhSieve.rough 30110134441897 27961 :=
  LargeQuotientSieve.row (p:=27967) (q:=1076630830) (s:=32812) (rank:=54538810) (tiny:=3052) (pairs:=229668)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1076630830 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27967 : FinalSeventhSieve.rough 30110134441897 27967+658260921=FinalSeventhSieve.rough 30110134441897 27847 :=
  LargeQuotientSieve.combine to27961 row27967 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 27967+658260921=FinalSeventhSieve.rough 30110134441897 27847 := to27967

end Tail30110134441897From27847To27967
