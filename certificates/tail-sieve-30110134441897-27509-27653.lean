import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1075000000-1100000000»

/-! Exact changes for sieve primes 3006 through 3017. -/
open Finset
namespace Tail30110134441897From27509To27653

set_option maxRecDepth 16000 in
private theorem row27527 :
    FinalSeventhSieve.rough 30110134441897 27527+55671642=FinalSeventhSieve.rough 30110134441897 27509 :=
  LargeQuotientSieve.row (p:=27527) (q:=1093840027) (s:=33073) (rank:=55366607) (tiny:=3005) (pairs:=308039)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1093840027 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row27529 :
    FinalSeventhSieve.rough 30110134441897 27529+55666573=FinalSeventhSieve.rough 30110134441897 27527 :=
  LargeQuotientSieve.row (p:=27529) (q:=1093760559) (s:=33072) (rank:=55362841) (tiny:=3006) (pairs:=306737)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1093760559 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27529 : FinalSeventhSieve.rough 30110134441897 27529+111338215=FinalSeventhSieve.rough 30110134441897 27509 :=
  LargeQuotientSieve.combine row27527 row27529 rfl

set_option maxRecDepth 16000 in
private theorem row27539 :
    FinalSeventhSieve.rough 30110134441897 27539+55645456=FinalSeventhSieve.rough 30110134441897 27529 :=
  LargeQuotientSieve.row (p:=27539) (q:=1093363391) (s:=33066) (rank:=55343547) (tiny:=3007) (pairs:=304915)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1093363391 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27539 : FinalSeventhSieve.rough 30110134441897 27539+166983671=FinalSeventhSieve.rough 30110134441897 27509 :=
  LargeQuotientSieve.combine to27529 row27539 rfl

set_option maxRecDepth 16000 in
private theorem row27541 :
    FinalSeventhSieve.rough 30110134441897 27541+55640319=FinalSeventhSieve.rough 30110134441897 27539 :=
  LargeQuotientSieve.row (p:=27541) (q:=1093283992) (s:=33064) (rank:=55339701) (tiny:=3008) (pairs:=303625)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1093283992 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27541 : FinalSeventhSieve.rough 30110134441897 27541+222623990=FinalSeventhSieve.rough 30110134441897 27509 :=
  LargeQuotientSieve.combine to27539 row27541 rfl

set_option maxRecDepth 16000 in
private theorem row27551 :
    FinalSeventhSieve.rough 30110134441897 27551+55619346=FinalSeventhSieve.rough 30110134441897 27541 :=
  LargeQuotientSieve.row (p:=27551) (q:=1092887170) (s:=33058) (rank:=55320577) (tiny:=3009) (pairs:=301777)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1092887170 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27551 : FinalSeventhSieve.rough 30110134441897 27551+278243336=FinalSeventhSieve.rough 30110134441897 27509 :=
  LargeQuotientSieve.combine to27541 row27551 rfl

set_option maxRecDepth 16000 in
private theorem row27581 :
    FinalSeventhSieve.rough 30110134441897 27581+55559009=FinalSeventhSieve.rough 30110134441897 27551 :=
  LargeQuotientSieve.row (p:=27581) (q:=1091698431) (s:=33040) (rank:=55263403) (tiny:=3010) (pairs:=298615)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1091698431 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27581 : FinalSeventhSieve.rough 30110134441897 27581+333802345=FinalSeventhSieve.rough 30110134441897 27509 :=
  LargeQuotientSieve.combine to27551 row27581 rfl

set_option maxRecDepth 16000 in
private theorem row27583 :
    FinalSeventhSieve.rough 30110134441897 27583+55553889=FinalSeventhSieve.rough 30110134441897 27581 :=
  LargeQuotientSieve.row (p:=27583) (q:=1091619274) (s:=33039) (rank:=55259566) (tiny:=3011) (pairs:=297333)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1091619274 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27583 : FinalSeventhSieve.rough 30110134441897 27583+389356234=FinalSeventhSieve.rough 30110134441897 27509 :=
  LargeQuotientSieve.combine to27581 row27583 rfl

set_option maxRecDepth 16000 in
private theorem row27611 :
    FinalSeventhSieve.rough 30110134441897 27611+55497731=FinalSeventhSieve.rough 30110134441897 27583 :=
  LargeQuotientSieve.row (p:=27611) (q:=1090512275) (s:=33022) (rank:=55206406) (tiny:=3012) (pairs:=294336)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1090512275 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27611 : FinalSeventhSieve.rough 30110134441897 27611+444853965=FinalSeventhSieve.rough 30110134441897 27509 :=
  LargeQuotientSieve.combine to27583 row27611 rfl

set_option maxRecDepth 16000 in
private theorem row27617 :
    FinalSeventhSieve.rough 30110134441897 27617+55484816=FinalSeventhSieve.rough 30110134441897 27611 :=
  LargeQuotientSieve.row (p:=27617) (q:=1090275353) (s:=33019) (rank:=55195009) (tiny:=3013) (pairs:=292819)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1090275353 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27617 : FinalSeventhSieve.rough 30110134441897 27617+500338781=FinalSeventhSieve.rough 30110134441897 27509 :=
  LargeQuotientSieve.combine to27611 row27617 rfl

set_option maxRecDepth 16000 in
private theorem row27631 :
    FinalSeventhSieve.rough 30110134441897 27631+55456205=FinalSeventhSieve.rough 30110134441897 27617 :=
  LargeQuotientSieve.row (p:=27631) (q:=1089722935) (s:=33010) (rank:=55168447) (tiny:=3014) (pairs:=290771)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1089722935 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27631 : FinalSeventhSieve.rough 30110134441897 27631+555794986=FinalSeventhSieve.rough 30110134441897 27509 :=
  LargeQuotientSieve.combine to27617 row27631 rfl

set_option maxRecDepth 16000 in
private theorem row27647 :
    FinalSeventhSieve.rough 30110134441897 27647+55423762=FinalSeventhSieve.rough 30110134441897 27631 :=
  LargeQuotientSieve.row (p:=27647) (q:=1089092286) (s:=33001) (rank:=55138126) (tiny:=3015) (pairs:=288650)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1089092286 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27647 : FinalSeventhSieve.rough 30110134441897 27647+611218748=FinalSeventhSieve.rough 30110134441897 27509 :=
  LargeQuotientSieve.combine to27631 row27647 rfl

set_option maxRecDepth 16000 in
private theorem row27653 :
    FinalSeventhSieve.rough 30110134441897 27653+55410911=FinalSeventhSieve.rough 30110134441897 27647 :=
  LargeQuotientSieve.row (p:=27653) (q:=1088855980) (s:=32997) (rank:=55126784) (tiny:=3016) (pairs:=287142)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1088855980 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27653 : FinalSeventhSieve.rough 30110134441897 27653+666629659=FinalSeventhSieve.rough 30110134441897 27509 :=
  LargeQuotientSieve.combine to27647 row27653 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 27653+666629659=FinalSeventhSieve.rough 30110134441897 27509 := to27653

end Tail30110134441897From27509To27653
