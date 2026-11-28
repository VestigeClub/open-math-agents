import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1075000000-1100000000»

/-! Exact changes for sieve primes 1238 through 1249. -/
open Finset
namespace Tail11092009835083From10079To10169

set_option maxRecDepth 16000 in
private theorem row10091 :
    FinalSeventhSieve.rough 11092009835083 10091+63459752=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.row (p:=10091) (q:=1099198279) (s:=33154) (rank:=55623931) (tiny:=1237) (pairs:=7837057)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1099198279 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row10093 :
    FinalSeventhSieve.rough 11092009835083 10093+63437707=FinalSeventhSieve.rough 11092009835083 10091 :=
  LargeQuotientSieve.row (p:=10093) (q:=1098980465) (s:=33150) (rank:=55613401) (tiny:=1238) (pairs:=7825543)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1098980465 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10093 : FinalSeventhSieve.rough 11092009835083 10093+126897459=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine row10091 row10093 rfl

set_option maxRecDepth 16000 in
private theorem row10099 :
    FinalSeventhSieve.rough 11092009835083 10099+63390257=FinalSeventhSieve.rough 11092009835083 10093 :=
  LargeQuotientSieve.row (p:=10099) (q:=1098327540) (s:=33141) (rank:=55582198) (tiny:=1239) (pairs:=7809297)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1098327540 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10099 : FinalSeventhSieve.rough 11092009835083 10099+190287716=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine to10093 row10099 rfl

set_option maxRecDepth 16000 in
private theorem row10103 :
    FinalSeventhSieve.rough 11092009835083 10103+63355412=FinalSeventhSieve.rough 11092009835083 10099 :=
  LargeQuotientSieve.row (p:=10103) (q:=1097892688) (s:=33134) (rank:=55561172) (tiny:=1240) (pairs:=7795479)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1097892688 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10103 : FinalSeventhSieve.rough 11092009835083 10103+253643128=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine to10099 row10103 rfl

set_option maxRecDepth 16000 in
private theorem row10111 :
    FinalSeventhSieve.rough 11092009835083 10111+63295157=FinalSeventhSieve.rough 11092009835083 10103 :=
  LargeQuotientSieve.row (p:=10111) (q:=1097024016) (s:=33121) (rank:=55519443) (tiny:=1241) (pairs:=7776954)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1097024016 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10111 : FinalSeventhSieve.rough 11092009835083 10111+316938285=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine to10103 row10111 rfl

set_option maxRecDepth 16000 in
private theorem row10133 :
    FinalSeventhSieve.rough 11092009835083 10133+63145698=FinalSeventhSieve.rough 11092009835083 10111 :=
  LargeQuotientSieve.row (p:=10133) (q:=1094642241) (s:=33085) (rank:=55404920) (tiny:=1242) (pairs:=7742019)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1094642241 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10133 : FinalSeventhSieve.rough 11092009835083 10133+380083983=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine to10111 row10133 rfl

set_option maxRecDepth 16000 in
private theorem row10139 :
    FinalSeventhSieve.rough 11092009835083 10139+63098592=FinalSeventhSieve.rough 11092009835083 10133 :=
  LargeQuotientSieve.row (p:=10139) (q:=1093994460) (s:=33075) (rank:=55373963) (tiny:=1243) (pairs:=7725871)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1093994460 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10139 : FinalSeventhSieve.rough 11092009835083 10139+443182575=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine to10133 row10139 rfl

set_option maxRecDepth 16000 in
private theorem row10141 :
    FinalSeventhSieve.rough 11092009835083 10141+63076920=FinalSeventhSieve.rough 11092009835083 10139 :=
  LargeQuotientSieve.row (p:=10141) (q:=1093778703) (s:=33072) (rank:=55363687) (tiny:=1244) (pairs:=7714476)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1093778703 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10141 : FinalSeventhSieve.rough 11092009835083 10141+506259495=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine to10139 row10141 rfl

set_option maxRecDepth 16000 in
private theorem row10151 :
    FinalSeventhSieve.rough 11092009835083 10151+63004280=FinalSeventhSieve.rough 11092009835083 10141 :=
  LargeQuotientSieve.row (p:=10151) (q:=1092701195) (s:=33056) (rank:=55311643) (tiny:=1245) (pairs:=7693881)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1092701195 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10151 : FinalSeventhSieve.rough 11092009835083 10151+569263775=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine to10141 row10151 rfl

set_option maxRecDepth 16000 in
private theorem row10159 :
    FinalSeventhSieve.rough 11092009835083 10159+62944478=FinalSeventhSieve.rough 11092009835083 10151 :=
  LargeQuotientSieve.row (p:=10159) (q:=1091840716) (s:=33043) (rank:=55270271) (tiny:=1246) (pairs:=7675452)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1091840716 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10159 : FinalSeventhSieve.rough 11092009835083 10159+632208253=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine to10151 row10159 rfl

set_option maxRecDepth 16000 in
private theorem row10163 :
    FinalSeventhSieve.rough 11092009835083 10163+62910161=FinalSeventhSieve.rough 11092009835083 10159 :=
  LargeQuotientSieve.row (p:=10163) (q:=1091410984) (s:=33036) (rank:=55249513) (tiny:=1247) (pairs:=7661894)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1091410984 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10163 : FinalSeventhSieve.rough 11092009835083 10163+695118414=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine to10159 row10163 rfl

set_option maxRecDepth 16000 in
private theorem row10169 :
    FinalSeventhSieve.rough 11092009835083 10169+62863229=FinalSeventhSieve.rough 11092009835083 10163 :=
  LargeQuotientSieve.row (p:=10169) (q:=1090767020) (s:=33026) (rank:=55218583) (tiny:=1248) (pairs:=7645893)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1090767020 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10169 : FinalSeventhSieve.rough 11092009835083 10169+757981643=FinalSeventhSieve.rough 11092009835083 10079 :=
  LargeQuotientSieve.combine to10163 row10169 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10169+757981643=FinalSeventhSieve.rough 11092009835083 10079 := to10169

end Tail11092009835083From10079To10169
