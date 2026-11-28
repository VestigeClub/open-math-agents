import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1000000000-1025000000»

/-! Exact changes for sieve primes 3251 through 3256. -/
open Finset
namespace Tail30110134441897From30059To30109

set_option maxRecDepth 16000 in
private theorem row30071 :
    FinalSeventhSieve.rough 30110134441897 30071+50931069=FinalSeventhSieve.rough 30110134441897 30059 :=
  LargeQuotientSieve.row (p:=30071) (q:=1001301401) (s:=31643) (rank:=50910279) (tiny:=3250) (pairs:=24039)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1001301401 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row30089 :
    FinalSeventhSieve.rough 30110134441897 30089+50901511=FinalSeventhSieve.rough 30110134441897 30071 :=
  LargeQuotientSieve.row (p:=30089) (q:=1000702397) (s:=31633) (rank:=50881316) (tiny:=3251) (pairs:=23445)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1000702397 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30089 : FinalSeventhSieve.rough 30110134441897 30089+101832580=FinalSeventhSieve.rough 30110134441897 30059 :=
  LargeQuotientSieve.combine row30071 row30089 rfl

set_option maxRecDepth 16000 in
private theorem row30091 :
    FinalSeventhSieve.rough 30110134441897 30091+50897940=FinalSeventhSieve.rough 30110134441897 30089 :=
  LargeQuotientSieve.row (p:=30091) (q:=1000635885) (s:=31632) (rank:=50878078) (tiny:=3252) (pairs:=23113)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1000635885 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30091 : FinalSeventhSieve.rough 30110134441897 30091+152730520=FinalSeventhSieve.rough 30110134441897 30059 :=
  LargeQuotientSieve.combine to30089 row30091 rfl

set_option maxRecDepth 16000 in
private theorem row30097 :
    FinalSeventhSieve.rough 30110134441897 30097+50887987=FinalSeventhSieve.rough 30110134441897 30091 :=
  LargeQuotientSieve.row (p:=30097) (q:=1000436403) (s:=31629) (rank:=50868543) (tiny:=3253) (pairs:=22696)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1000436403 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30097 : FinalSeventhSieve.rough 30110134441897 30097+203618507=FinalSeventhSieve.rough 30110134441897 30059 :=
  LargeQuotientSieve.combine to30091 row30097 rfl

set_option maxRecDepth 16000 in
private theorem row30103 :
    FinalSeventhSieve.rough 30110134441897 30103+50877978=FinalSeventhSieve.rough 30110134441897 30097 :=
  LargeQuotientSieve.row (p:=30103) (q:=1000237001) (s:=31626) (rank:=50858935) (tiny:=3254) (pairs:=22296)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1000237001 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30103 : FinalSeventhSieve.rough 30110134441897 30103+254496485=FinalSeventhSieve.rough 30110134441897 30059 :=
  LargeQuotientSieve.combine to30097 row30103 rfl

set_option maxRecDepth 16000 in
private theorem row30109 :
    FinalSeventhSieve.rough 30110134441897 30109+50867990=FinalSeventhSieve.rough 30110134441897 30103 :=
  LargeQuotientSieve.row (p:=30109) (q:=1000037677) (s:=31623) (rank:=50849353) (tiny:=3255) (pairs:=21891)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1000037677 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30109 : FinalSeventhSieve.rough 30110134441897 30109+305364475=FinalSeventhSieve.rough 30110134441897 30059 :=
  LargeQuotientSieve.combine to30103 row30109 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 30109+305364475=FinalSeventhSieve.rough 30110134441897 30059 := to30109

end Tail30110134441897From30059To30109
