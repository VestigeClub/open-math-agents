import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1075000000-1100000000»

/-! Exact changes for sieve primes 3054 through 3056. -/
open Finset
namespace Tail30110134441897From27967To28001

set_option maxRecDepth 16000 in
private theorem row27983 :
    FinalSeventhSieve.rough 30110134441897 27983+54733940=FinalSeventhSieve.rough 30110134441897 27967 :=
  LargeQuotientSieve.row (p:=27983) (q:=1076015239) (s:=32802) (rank:=54509214) (tiny:=3053) (pairs:=227778)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1076015239 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row27997 :
    FinalSeventhSieve.rough 30110134441897 27997+54706325=FinalSeventhSieve.rough 30110134441897 27983 :=
  LargeQuotientSieve.row (p:=27997) (q:=1075477174) (s:=32794) (rank:=54483397) (tiny:=3054) (pairs:=225981)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1075477174 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27997 : FinalSeventhSieve.rough 30110134441897 27997+109440265=FinalSeventhSieve.rough 30110134441897 27967 :=
  LargeQuotientSieve.combine row27983 row27997 rfl

set_option maxRecDepth 16000 in
private theorem row28001 :
    FinalSeventhSieve.rough 30110134441897 28001+54697706=FinalSeventhSieve.rough 30110134441897 27997 :=
  LargeQuotientSieve.row (p:=28001) (q:=1075323539) (s:=32792) (rank:=54476004) (tiny:=3055) (pairs:=224756)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1075323539 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28001 : FinalSeventhSieve.rough 30110134441897 28001+164137971=FinalSeventhSieve.rough 30110134441897 27967 :=
  LargeQuotientSieve.combine to27997 row28001 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 28001+164137971=FinalSeventhSieve.rough 30110134441897 27967 := to28001

end Tail30110134441897From27967To28001
