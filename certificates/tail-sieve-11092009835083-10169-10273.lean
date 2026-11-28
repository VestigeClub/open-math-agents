import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1075000000-1100000000»

/-! Exact changes for sieve primes 1250 through 1261. -/
open Finset
namespace Tail11092009835083From10169To10273

set_option maxRecDepth 16000 in
private theorem row10177 :
    FinalSeventhSieve.rough 11092009835083 10177+62803831=FinalSeventhSieve.rough 11092009835083 10169 :=
  LargeQuotientSieve.row (p:=10177) (q:=1089909583) (s:=33013) (rank:=55177427) (tiny:=1249) (pairs:=7627652)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1089909583 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row10181 :
    FinalSeventhSieve.rough 11092009835083 10181+62769642=FinalSeventhSieve.rough 11092009835083 10177 :=
  LargeQuotientSieve.row (p:=10181) (q:=1089481370) (s:=33007) (rank:=55156804) (tiny:=1250) (pairs:=7614087)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1089481370 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10181 : FinalSeventhSieve.rough 11092009835083 10181+125573473=FinalSeventhSieve.rough 11092009835083 10169 :=
  LargeQuotientSieve.combine row10177 row10181 rfl

set_option maxRecDepth 16000 in
private theorem row10193 :
    FinalSeventhSieve.rough 11092009835083 10193+62685265=FinalSeventhSieve.rough 11092009835083 10181 :=
  LargeQuotientSieve.row (p:=10193) (q:=1088198747) (s:=32987) (rank:=55095316) (tiny:=1251) (pairs:=7591199)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1088198747 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10193 : FinalSeventhSieve.rough 11092009835083 10193+188258738=FinalSeventhSieve.rough 11092009835083 10169 :=
  LargeQuotientSieve.combine to10181 row10193 rfl

set_option maxRecDepth 16000 in
private theorem row10211 :
    FinalSeventhSieve.rough 11092009835083 10211+62563320=FinalSeventhSieve.rough 11092009835083 10193 :=
  LargeQuotientSieve.row (p:=10211) (q:=1086280465) (s:=32958) (rank:=55002939) (tiny:=1252) (pairs:=7561632)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1086280465 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10211 : FinalSeventhSieve.rough 11092009835083 10211+250822058=FinalSeventhSieve.rough 11092009835083 10169 :=
  LargeQuotientSieve.combine to10193 row10211 rfl

set_option maxRecDepth 16000 in
private theorem row10223 :
    FinalSeventhSieve.rough 11092009835083 10223+62479437=FinalSeventhSieve.rough 11092009835083 10211 :=
  LargeQuotientSieve.row (p:=10223) (q:=1085005363) (s:=32939) (rank:=54941714) (tiny:=1253) (pairs:=7538975)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1085005363 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10223 : FinalSeventhSieve.rough 11092009835083 10223+313301495=FinalSeventhSieve.rough 11092009835083 10169 :=
  LargeQuotientSieve.combine to10211 row10223 rfl

set_option maxRecDepth 16000 in
private theorem row10243 :
    FinalSeventhSieve.rough 11092009835083 10243+62345754=FinalSeventhSieve.rough 11092009835083 10223 :=
  LargeQuotientSieve.row (p:=10243) (q:=1082886833) (s:=32907) (rank:=54839628) (tiny:=1254) (pairs:=7507379)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1082886833 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10243 : FinalSeventhSieve.rough 11092009835083 10243+375647249=FinalSeventhSieve.rough 11092009835083 10169 :=
  LargeQuotientSieve.combine to10223 row10243 rfl

set_option maxRecDepth 16000 in
private theorem row10247 :
    FinalSeventhSieve.rough 11092009835083 10247+62312108=FinalSeventhSieve.rough 11092009835083 10243 :=
  LargeQuotientSieve.row (p:=10247) (q:=1082464119) (s:=32900) (rank:=54819390) (tiny:=1255) (pairs:=7493972)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1082464119 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10247 : FinalSeventhSieve.rough 11092009835083 10247+437959357=FinalSeventhSieve.rough 11092009835083 10169 :=
  LargeQuotientSieve.combine to10243 row10247 rfl

set_option maxRecDepth 16000 in
private theorem row10253 :
    FinalSeventhSieve.rough 11092009835083 10253+62265996=FinalSeventhSieve.rough 11092009835083 10247 :=
  LargeQuotientSieve.row (p:=10253) (q:=1081830667) (s:=32891) (rank:=54788831) (tiny:=1256) (pairs:=7478420)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1081830667 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10253 : FinalSeventhSieve.rough 11092009835083 10253+500225353=FinalSeventhSieve.rough 11092009835083 10169 :=
  LargeQuotientSieve.combine to10247 row10253 rfl

set_option maxRecDepth 16000 in
private theorem row10259 :
    FinalSeventhSieve.rough 11092009835083 10259+62219799=FinalSeventhSieve.rough 11092009835083 10253 :=
  LargeQuotientSieve.row (p:=10259) (q:=1081197956) (s:=32881) (rank:=54758218) (tiny:=1257) (pairs:=7462837)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1081197956 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10259 : FinalSeventhSieve.rough 11092009835083 10259+562445152=FinalSeventhSieve.rough 11092009835083 10169 :=
  LargeQuotientSieve.combine to10253 row10259 rfl

set_option maxRecDepth 16000 in
private theorem row10267 :
    FinalSeventhSieve.rough 11092009835083 10267+62161538=FinalSeventhSieve.rough 11092009835083 10259 :=
  LargeQuotientSieve.row (p:=10267) (q:=1080355491) (s:=32868) (rank:=54717811) (tiny:=1258) (pairs:=7444984)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1080355491 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10267 : FinalSeventhSieve.rough 11092009835083 10267+624606690=FinalSeventhSieve.rough 11092009835083 10169 :=
  LargeQuotientSieve.combine to10259 row10267 rfl

set_option maxRecDepth 16000 in
private theorem row10271 :
    FinalSeventhSieve.rough 11092009835083 10271+62128011=FinalSeventhSieve.rough 11092009835083 10267 :=
  LargeQuotientSieve.row (p:=10271) (q:=1079934751) (s:=32862) (rank:=54697531) (tiny:=1259) (pairs:=7431738)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1079934751 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10271 : FinalSeventhSieve.rough 11092009835083 10271+686734701=FinalSeventhSieve.rough 11092009835083 10169 :=
  LargeQuotientSieve.combine to10267 row10271 rfl

set_option maxRecDepth 16000 in
private theorem row10273 :
    FinalSeventhSieve.rough 11092009835083 10273+62106837=FinalSeventhSieve.rough 11092009835083 10271 :=
  LargeQuotientSieve.row (p:=10273) (q:=1079724504) (s:=32859) (rank:=54687387) (tiny:=1260) (pairs:=7420709)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1079724504 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10273 : FinalSeventhSieve.rough 11092009835083 10273+748841538=FinalSeventhSieve.rough 11092009835083 10169 :=
  LargeQuotientSieve.combine to10271 row10273 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10273+748841538=FinalSeventhSieve.rough 11092009835083 10169 := to10273

end Tail11092009835083From10169To10273
