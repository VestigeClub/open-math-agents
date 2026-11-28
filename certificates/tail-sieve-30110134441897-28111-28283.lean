import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 3069 through 3080. -/
open Finset
namespace Tail30110134441897From28111To28283

set_option maxRecDepth 16000 in
private theorem row28123 :
    FinalSeventhSieve.rough 30110134441897 28123+54454037=FinalSeventhSieve.rough 30110134441897 28111 :=
  LargeQuotientSieve.row (p:=28123) (q:=1070658693) (s:=32720) (rank:=54251680) (tiny:=3068) (pairs:=205424)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1070658693 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row28151 :
    FinalSeventhSieve.rough 30110134441897 28151+54400410=FinalSeventhSieve.rough 30110134441897 28123 :=
  LargeQuotientSieve.row (p:=28151) (q:=1069593777) (s:=32704) (rank:=54200503) (tiny:=3069) (pairs:=202975)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1069593777 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28151 : FinalSeventhSieve.rough 30110134441897 28151+108854447=FinalSeventhSieve.rough 30110134441897 28111 :=
  LargeQuotientSieve.combine row28123 row28151 rfl

set_option maxRecDepth 16000 in
private theorem row28163 :
    FinalSeventhSieve.rough 30110134441897 28163+54376888=FinalSeventhSieve.rough 30110134441897 28151 :=
  LargeQuotientSieve.row (p:=28163) (q:=1069138033) (s:=32697) (rank:=54178572) (tiny:=3070) (pairs:=201385)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1069138033 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28163 : FinalSeventhSieve.rough 30110134441897 28163+163231335=FinalSeventhSieve.rough 30110134441897 28111 :=
  LargeQuotientSieve.combine to28151 row28163 rfl

set_option maxRecDepth 16000 in
private theorem row28181 :
    FinalSeventhSieve.rough 30110134441897 28181+54342053=FinalSeventhSieve.rough 30110134441897 28163 :=
  LargeQuotientSieve.row (p:=28181) (q:=1068455145) (s:=32687) (rank:=54145605) (tiny:=3071) (pairs:=199518)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1068455145 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28181 : FinalSeventhSieve.rough 30110134441897 28181+217573388=FinalSeventhSieve.rough 30110134441897 28111 :=
  LargeQuotientSieve.combine to28163 row28181 rfl

set_option maxRecDepth 16000 in
private theorem row28183 :
    FinalSeventhSieve.rough 30110134441897 28183+54337428=FinalSeventhSieve.rough 30110134441897 28181 :=
  LargeQuotientSieve.row (p:=28183) (q:=1068379322) (s:=32686) (rank:=54142035) (tiny:=3072) (pairs:=198464)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1068379322 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28183 : FinalSeventhSieve.rough 30110134441897 28183+271910816=FinalSeventhSieve.rough 30110134441897 28111 :=
  LargeQuotientSieve.combine to28181 row28183 rfl

set_option maxRecDepth 16000 in
private theorem row28201 :
    FinalSeventhSieve.rough 30110134441897 28201+54302762=FinalSeventhSieve.rough 30110134441897 28183 :=
  LargeQuotientSieve.row (p:=28201) (q:=1067697402) (s:=32675) (rank:=54109227) (tiny:=3073) (pairs:=196607)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1067697402 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28201 : FinalSeventhSieve.rough 30110134441897 28201+326213578=FinalSeventhSieve.rough 30110134441897 28111 :=
  LargeQuotientSieve.combine to28183 row28201 rfl

set_option maxRecDepth 16000 in
private theorem row28211 :
    FinalSeventhSieve.rough 30110134441897 28211+54282967=FinalSeventhSieve.rough 30110134441897 28201 :=
  LargeQuotientSieve.row (p:=28211) (q:=1067318933) (s:=32669) (rank:=54090889) (tiny:=3074) (pairs:=195151)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1067318933 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28211 : FinalSeventhSieve.rough 30110134441897 28211+380496545=FinalSeventhSieve.rough 30110134441897 28111 :=
  LargeQuotientSieve.combine to28201 row28211 rfl

set_option maxRecDepth 16000 in
private theorem row28219 :
    FinalSeventhSieve.rough 30110134441897 28219+54267043=FinalSeventhSieve.rough 30110134441897 28211 :=
  LargeQuotientSieve.row (p:=28219) (q:=1067016352) (s:=32665) (rank:=54076327) (tiny:=3075) (pairs:=193790)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1067016352 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28219 : FinalSeventhSieve.rough 30110134441897 28219+434763588=FinalSeventhSieve.rough 30110134441897 28111 :=
  LargeQuotientSieve.combine to28211 row28219 rfl

set_option maxRecDepth 16000 in
private theorem row28229 :
    FinalSeventhSieve.rough 30110134441897 28229+54247440=FinalSeventhSieve.rough 30110134441897 28219 :=
  LargeQuotientSieve.row (p:=28229) (q:=1066638366) (s:=32659) (rank:=54058137) (tiny:=3076) (pairs:=192378)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1066638366 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28229 : FinalSeventhSieve.rough 30110134441897 28229+489011028=FinalSeventhSieve.rough 30110134441897 28111 :=
  LargeQuotientSieve.combine to28219 row28229 rfl

set_option maxRecDepth 16000 in
private theorem row28277 :
    FinalSeventhSieve.rough 30110134441897 28277+54156924=FinalSeventhSieve.rough 30110134441897 28229 :=
  LargeQuotientSieve.row (p:=28277) (q:=1064827755) (s:=32631) (rank:=53970993) (tiny:=3077) (pairs:=189007)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1064827755 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28277 : FinalSeventhSieve.rough 30110134441897 28277+543167952=FinalSeventhSieve.rough 30110134441897 28111 :=
  LargeQuotientSieve.combine to28229 row28277 rfl

set_option maxRecDepth 16000 in
private theorem row28279 :
    FinalSeventhSieve.rough 30110134441897 28279+54152240=FinalSeventhSieve.rough 30110134441897 28277 :=
  LargeQuotientSieve.row (p:=28279) (q:=1064752446) (s:=32630) (rank:=53967319) (tiny:=3078) (pairs:=187998)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1064752446 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28279 : FinalSeventhSieve.rough 30110134441897 28279+597320192=FinalSeventhSieve.rough 30110134441897 28111 :=
  LargeQuotientSieve.combine to28277 row28279 rfl

set_option maxRecDepth 16000 in
private theorem row28283 :
    FinalSeventhSieve.rough 30110134441897 28283+54143790=FinalSeventhSieve.rough 30110134441897 28279 :=
  LargeQuotientSieve.row (p:=28283) (q:=1064601861) (s:=32628) (rank:=53959983) (tiny:=3079) (pairs:=186885)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1064601861 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28283 : FinalSeventhSieve.rough 30110134441897 28283+651463982=FinalSeventhSieve.rough 30110134441897 28111 :=
  LargeQuotientSieve.combine to28279 row28283 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 28283+651463982=FinalSeventhSieve.rough 30110134441897 28111 := to28283

end Tail30110134441897From28111To28283
