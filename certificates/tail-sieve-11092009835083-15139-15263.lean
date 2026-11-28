import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-725000000-750000000»

/-! Exact changes for sieve primes 1770 through 1781. -/
open Finset
namespace Tail11092009835083From15139To15263

set_option maxRecDepth 16000 in
private theorem row15149 :
    FinalSeventhSieve.rough 11092009835083 15149+39541272=FinalSeventhSieve.rough 11092009835083 15139 :=
  LargeQuotientSieve.row (p:=15149) (q:=732194193) (s:=27059) (rank:=37831662) (tiny:=1769) (pairs:=1711378)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 732194193 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row15161 :
    FinalSeventhSieve.rough 11092009835083 15161+39506461=FinalSeventhSieve.rough 11092009835083 15149 :=
  LargeQuotientSieve.row (p:=15161) (q:=731614658) (s:=27048) (rank:=37803217) (tiny:=1770) (pairs:=1705013)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 731614658 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15161 : FinalSeventhSieve.rough 11092009835083 15161+79047733=FinalSeventhSieve.rough 11092009835083 15139 :=
  LargeQuotientSieve.combine row15149 row15161 rfl

set_option maxRecDepth 16000 in
private theorem row15173 :
    FinalSeventhSieve.rough 11092009835083 15173+39471760=FinalSeventhSieve.rough 11092009835083 15161 :=
  LargeQuotientSieve.row (p:=15173) (q:=731036040) (s:=27037) (rank:=37774914) (tiny:=1771) (pairs:=1698616)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 731036040 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15173 : FinalSeventhSieve.rough 11092009835083 15173+118519493=FinalSeventhSieve.rough 11092009835083 15139 :=
  LargeQuotientSieve.combine to15161 row15173 rfl

set_option maxRecDepth 16000 in
private theorem row15187 :
    FinalSeventhSieve.rough 11092009835083 15187+39431759=FinalSeventhSieve.rough 11092009835083 15173 :=
  LargeQuotientSieve.row (p:=15187) (q:=730362140) (s:=27025) (rank:=37741810) (tiny:=1772) (pairs:=1691720)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 730362140 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15187 : FinalSeventhSieve.rough 11092009835083 15187+157951252=FinalSeventhSieve.rough 11092009835083 15139 :=
  LargeQuotientSieve.combine to15173 row15187 rfl

set_option maxRecDepth 16000 in
private theorem row15193 :
    FinalSeventhSieve.rough 11092009835083 15193+39412932=FinalSeventhSieve.rough 11092009835083 15187 :=
  LargeQuotientSieve.row (p:=15193) (q:=730073707) (s:=27019) (rank:=37727753) (tiny:=1773) (pairs:=1686951)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 730073707 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15193 : FinalSeventhSieve.rough 11092009835083 15193+197364184=FinalSeventhSieve.rough 11092009835083 15139 :=
  LargeQuotientSieve.combine to15187 row15193 rfl

set_option maxRecDepth 16000 in
private theorem row15199 :
    FinalSeventhSieve.rough 11092009835083 15199+39394117=FinalSeventhSieve.rough 11092009835083 15193 :=
  LargeQuotientSieve.row (p:=15199) (q:=729785501) (s:=27014) (rank:=37713661) (tiny:=1774) (pairs:=1682229)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 729785501 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15199 : FinalSeventhSieve.rough 11092009835083 15199+236758301=FinalSeventhSieve.rough 11092009835083 15139 :=
  LargeQuotientSieve.combine to15193 row15199 rfl

set_option maxRecDepth 16000 in
private theorem row15217 :
    FinalSeventhSieve.rough 11092009835083 15217+39344148=FinalSeventhSieve.rough 11092009835083 15199 :=
  LargeQuotientSieve.row (p:=15217) (q:=728922247) (s:=26998) (rank:=37671613) (tiny:=1775) (pairs:=1674309)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 728922247 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15217 : FinalSeventhSieve.rough 11092009835083 15217+276102449=FinalSeventhSieve.rough 11092009835083 15139 :=
  LargeQuotientSieve.combine to15199 row15217 rfl

set_option maxRecDepth 16000 in
private theorem row15227 :
    FinalSeventhSieve.rough 11092009835083 15227+39314927=FinalSeventhSieve.rough 11092009835083 15217 :=
  LargeQuotientSieve.row (p:=15227) (q:=728443543) (s:=26989) (rank:=37648191) (tiny:=1776) (pairs:=1668511)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 728443543 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15227 : FinalSeventhSieve.rough 11092009835083 15227+315417376=FinalSeventhSieve.rough 11092009835083 15139 :=
  LargeQuotientSieve.combine to15217 row15227 rfl

set_option maxRecDepth 16000 in
private theorem row15233 :
    FinalSeventhSieve.rough 11092009835083 15233+39296127=FinalSeventhSieve.rough 11092009835083 15227 :=
  LargeQuotientSieve.row (p:=15233) (q:=728156622) (s:=26984) (rank:=37634161) (tiny:=1777) (pairs:=1663742)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 728156622 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15233 : FinalSeventhSieve.rough 11092009835083 15233+354713503=FinalSeventhSieve.rough 11092009835083 15139 :=
  LargeQuotientSieve.combine to15227 row15233 rfl

set_option maxRecDepth 16000 in
private theorem row15241 :
    FinalSeventhSieve.rough 11092009835083 15241+39272099=FinalSeventhSieve.rough 11092009835083 15233 :=
  LargeQuotientSieve.row (p:=15241) (q:=727774413) (s:=26977) (rank:=37615392) (tiny:=1778) (pairs:=1658484)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 727774413 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15241 : FinalSeventhSieve.rough 11092009835083 15241+393985602=FinalSeventhSieve.rough 11092009835083 15139 :=
  LargeQuotientSieve.combine to15233 row15241 rfl

set_option maxRecDepth 16000 in
private theorem row15259 :
    FinalSeventhSieve.rough 11092009835083 15259+39222073=FinalSeventhSieve.rough 11092009835083 15241 :=
  LargeQuotientSieve.row (p:=15259) (q:=726915907) (s:=26961) (rank:=37573177) (tiny:=1779) (pairs:=1650674)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 726915907 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15259 : FinalSeventhSieve.rough 11092009835083 15259+433207675=FinalSeventhSieve.rough 11092009835083 15139 :=
  LargeQuotientSieve.combine to15241 row15259 rfl

set_option maxRecDepth 16000 in
private theorem row15263 :
    FinalSeventhSieve.rough 11092009835083 15263+39208562=FinalSeventhSieve.rough 11092009835083 15259 :=
  LargeQuotientSieve.row (p:=15263) (q:=726725403) (s:=26957) (rank:=37563844) (tiny:=1780) (pairs:=1646497)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 726725403 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15263 : FinalSeventhSieve.rough 11092009835083 15263+472416237=FinalSeventhSieve.rough 11092009835083 15139 :=
  LargeQuotientSieve.combine to15259 row15263 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 15263+472416237=FinalSeventhSieve.rough 11092009835083 15139 := to15263

end Tail11092009835083From15139To15263
