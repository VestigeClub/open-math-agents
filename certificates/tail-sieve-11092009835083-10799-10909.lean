import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1000000000-1025000000»

/-! Exact changes for sieve primes 1316 through 1327. -/
open Finset
namespace Tail11092009835083From10799To10909

set_option maxRecDepth 16000 in
private theorem row10831 :
    FinalSeventhSieve.rough 11092009835083 10831+58396035=FinalSeventhSieve.rough 11092009835083 10799 :=
  LargeQuotientSieve.row (p:=10831) (q:=1024098405) (s:=32001) (rank:=52009862) (tiny:=1315) (pairs:=6387487)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1024098405 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row10837 :
    FinalSeventhSieve.rough 11092009835083 10837+58355216=FinalSeventhSieve.rough 11092009835083 10831 :=
  LargeQuotientSieve.row (p:=10837) (q:=1023531404) (s:=31992) (rank:=51982559) (tiny:=1316) (pairs:=6373972)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1023531404 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10837 : FinalSeventhSieve.rough 11092009835083 10837+116751251=FinalSeventhSieve.rough 11092009835083 10799 :=
  LargeQuotientSieve.combine row10831 row10837 rfl

set_option maxRecDepth 16000 in
private theorem row10847 :
    FinalSeventhSieve.rough 11092009835083 10847+58292509=FinalSeventhSieve.rough 11092009835083 10837 :=
  LargeQuotientSieve.row (p:=10847) (q:=1022587797) (s:=31977) (rank:=51937045) (tiny:=1317) (pairs:=6356780)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1022587797 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10847 : FinalSeventhSieve.rough 11092009835083 10847+175043760=FinalSeventhSieve.rough 11092009835083 10799 :=
  LargeQuotientSieve.combine to10837 row10847 rfl

set_option maxRecDepth 16000 in
private theorem row10853 :
    FinalSeventhSieve.rough 11092009835083 10853+58251951=FinalSeventhSieve.rough 11092009835083 10847 :=
  LargeQuotientSieve.row (p:=10853) (q:=1022022467) (s:=31969) (rank:=51909922) (tiny:=1318) (pairs:=6343346)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1022022467 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10853 : FinalSeventhSieve.rough 11092009835083 10853+233295711=FinalSeventhSieve.rough 11092009835083 10799 :=
  LargeQuotientSieve.combine to10847 row10853 rfl

set_option maxRecDepth 16000 in
private theorem row10859 :
    FinalSeventhSieve.rough 11092009835083 10859+58211245=FinalSeventhSieve.rough 11092009835083 10853 :=
  LargeQuotientSieve.row (p:=10859) (q:=1021457761) (s:=31960) (rank:=51882705) (tiny:=1319) (pairs:=6329858)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1021457761 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10859 : FinalSeventhSieve.rough 11092009835083 10859+291506956=FinalSeventhSieve.rough 11092009835083 10799 :=
  LargeQuotientSieve.combine to10853 row10859 rfl

set_option maxRecDepth 16000 in
private theorem row10861 :
    FinalSeventhSieve.rough 11092009835083 10861+58192579=FinalSeventhSieve.rough 11092009835083 10859 :=
  LargeQuotientSieve.row (p:=10861) (q:=1021269665) (s:=31957) (rank:=51873653) (tiny:=1320) (pairs:=6320245)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1021269665 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10861 : FinalSeventhSieve.rough 11092009835083 10861+349699535=FinalSeventhSieve.rough 11092009835083 10799 :=
  LargeQuotientSieve.combine to10859 row10861 rfl

set_option maxRecDepth 16000 in
private theorem row10867 :
    FinalSeventhSieve.rough 11092009835083 10867+58152054=FinalSeventhSieve.rough 11092009835083 10861 :=
  LargeQuotientSieve.row (p:=10867) (q:=1020705791) (s:=31948) (rank:=51846567) (tiny:=1321) (pairs:=6306807)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1020705791 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10867 : FinalSeventhSieve.rough 11092009835083 10867+407851589=FinalSeventhSieve.rough 11092009835083 10799 :=
  LargeQuotientSieve.combine to10861 row10867 rfl

set_option maxRecDepth 16000 in
private theorem row10883 :
    FinalSeventhSieve.rough 11092009835083 10883+58056897=FinalSeventhSieve.rough 11092009835083 10867 :=
  LargeQuotientSieve.row (p:=10883) (q:=1019205167) (s:=31924) (rank:=51774035) (tiny:=1322) (pairs:=6284183)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1019205167 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10883 : FinalSeventhSieve.rough 11092009835083 10883+465908486=FinalSeventhSieve.rough 11092009835083 10799 :=
  LargeQuotientSieve.combine to10867 row10883 rfl

set_option maxRecDepth 16000 in
private theorem row10889 :
    FinalSeventhSieve.rough 11092009835083 10889+58016560=FinalSeventhSieve.rough 11092009835083 10883 :=
  LargeQuotientSieve.row (p:=10889) (q:=1018643570) (s:=31916) (rank:=51747024) (tiny:=1323) (pairs:=6270858)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1018643570 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10889 : FinalSeventhSieve.rough 11092009835083 10889+523925046=FinalSeventhSieve.rough 11092009835083 10799 :=
  LargeQuotientSieve.combine to10883 row10889 rfl

set_option maxRecDepth 16000 in
private theorem row10891 :
    FinalSeventhSieve.rough 11092009835083 10891+57997987=FinalSeventhSieve.rough 11092009835083 10889 :=
  LargeQuotientSieve.row (p:=10891) (q:=1018456508) (s:=31913) (rank:=51738041) (tiny:=1324) (pairs:=6261269)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1018456508 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10891 : FinalSeventhSieve.rough 11092009835083 10891+581923033=FinalSeventhSieve.rough 11092009835083 10799 :=
  LargeQuotientSieve.combine to10889 row10891 rfl

set_option maxRecDepth 16000 in
private theorem row10903 :
    FinalSeventhSieve.rough 11092009835083 10903+57925033=FinalSeventhSieve.rough 11092009835083 10891 :=
  LargeQuotientSieve.row (p:=10903) (q:=1017335580) (s:=31895) (rank:=51683875) (tiny:=1325) (pairs:=6242482)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1017335580 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10903 : FinalSeventhSieve.rough 11092009835083 10903+639848066=FinalSeventhSieve.rough 11092009835083 10799 :=
  LargeQuotientSieve.combine to10891 row10903 rfl

set_option maxRecDepth 16000 in
private theorem row10909 :
    FinalSeventhSieve.rough 11092009835083 10909+57884789=FinalSeventhSieve.rough 11092009835083 10903 :=
  LargeQuotientSieve.row (p:=10909) (q:=1016776041) (s:=31886) (rank:=51656918) (tiny:=1326) (pairs:=6229196)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1016776041 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10909 : FinalSeventhSieve.rough 11092009835083 10909+697732855=FinalSeventhSieve.rough 11092009835083 10799 :=
  LargeQuotientSieve.combine to10903 row10909 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10909+697732855=FinalSeventhSieve.rough 11092009835083 10799 := to10909

end Tail11092009835083From10799To10909
