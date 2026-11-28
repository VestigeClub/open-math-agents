import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-675000000-700000000»

/-! Exact changes for sieve primes 1884 through 1895. -/
open Finset
namespace Tail11092009835083From16193To16339

set_option maxRecDepth 16000 in
private theorem row16217 :
    FinalSeventhSieve.rough 11092009835083 16217+36603760=FinalSeventhSieve.rough 11092009835083 16193 :=
  LargeQuotientSieve.row (p:=16217) (q:=683974214) (s:=26152) (rank:=35465189) (tiny:=1883) (pairs:=1140453)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 683974214 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row16223 :
    FinalSeventhSieve.rough 11092009835083 16223+36587594=FinalSeventhSieve.rough 11092009835083 16217 :=
  LargeQuotientSieve.row (p:=16223) (q:=683721249) (s:=26148) (rank:=35452690) (tiny:=1884) (pairs:=1136787)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 683721249 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16223 : FinalSeventhSieve.rough 11092009835083 16223+73191354=FinalSeventhSieve.rough 11092009835083 16193 :=
  LargeQuotientSieve.combine row16217 row16223 rfl

set_option maxRecDepth 16000 in
private theorem row16229 :
    FinalSeventhSieve.rough 11092009835083 16229+36571457=FinalSeventhSieve.rough 11092009835083 16223 :=
  LargeQuotientSieve.row (p:=16229) (q:=683468472) (s:=26143) (rank:=35440243) (tiny:=1885) (pairs:=1133098)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 683468472 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16229 : FinalSeventhSieve.rough 11092009835083 16229+109762811=FinalSeventhSieve.rough 11092009835083 16193 :=
  LargeQuotientSieve.combine to16223 row16229 rfl

set_option maxRecDepth 16000 in
private theorem row16231 :
    FinalSeventhSieve.rough 11092009835083 16231+36564384=FinalSeventhSieve.rough 11092009835083 16229 :=
  LargeQuotientSieve.row (p:=16231) (q:=683384254) (s:=26141) (rank:=35436070) (tiny:=1886) (pairs:=1130199)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 683384254 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16231 : FinalSeventhSieve.rough 11092009835083 16231+146327195=FinalSeventhSieve.rough 11092009835083 16193 :=
  LargeQuotientSieve.combine to16229 row16231 rfl

set_option maxRecDepth 16000 in
private theorem row16249 :
    FinalSeventhSieve.rough 11092009835083 16249+36521328=FinalSeventhSieve.rough 11092009835083 16231 :=
  LargeQuotientSieve.row (p:=16249) (q:=682627228) (s:=26127) (rank:=35398993) (tiny:=1887) (pairs:=1124221)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 682627228 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16249 : FinalSeventhSieve.rough 11092009835083 16249+182848523=FinalSeventhSieve.rough 11092009835083 16193 :=
  LargeQuotientSieve.combine to16231 row16249 rfl

set_option maxRecDepth 16000 in
private theorem row16253 :
    FinalSeventhSieve.rough 11092009835083 16253+36509779=FinalSeventhSieve.rough 11092009835083 16249 :=
  LargeQuotientSieve.row (p:=16253) (q:=682459228) (s:=26123) (rank:=35390700) (tiny:=1888) (pairs:=1120966)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 682459228 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16253 : FinalSeventhSieve.rough 11092009835083 16253+219358302=FinalSeventhSieve.rough 11092009835083 16193 :=
  LargeQuotientSieve.combine to16249 row16253 rfl

set_option maxRecDepth 16000 in
private theorem row16267 :
    FinalSeventhSieve.rough 11092009835083 16267+36475918=FinalSeventhSieve.rough 11092009835083 16253 :=
  LargeQuotientSieve.row (p:=16267) (q:=681871877) (s:=26112) (rank:=35361950) (tiny:=1889) (pairs:=1115856)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 681871877 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16267 : FinalSeventhSieve.rough 11092009835083 16267+255834220=FinalSeventhSieve.rough 11092009835083 16193 :=
  LargeQuotientSieve.combine to16253 row16267 rfl

set_option maxRecDepth 16000 in
private theorem row16273 :
    FinalSeventhSieve.rough 11092009835083 16273+36459976=FinalSeventhSieve.rough 11092009835083 16267 :=
  LargeQuotientSieve.row (p:=16273) (q:=681620465) (s:=26107) (rank:=35349670) (tiny:=1890) (pairs:=1112195)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 681620465 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16273 : FinalSeventhSieve.rough 11092009835083 16273+292294196=FinalSeventhSieve.rough 11092009835083 16193 :=
  LargeQuotientSieve.combine to16267 row16273 rfl

set_option maxRecDepth 16000 in
private theorem row16301 :
    FinalSeventhSieve.rough 11092009835083 16301+36394741=FinalSeventhSieve.rough 11092009835083 16273 :=
  LargeQuotientSieve.row (p:=16301) (q:=680449655) (s:=26085) (rank:=35292178) (tiny:=1891) (pairs:=1104453)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 680449655 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16301 : FinalSeventhSieve.rough 11092009835083 16301+328688937=FinalSeventhSieve.rough 11092009835083 16193 :=
  LargeQuotientSieve.combine to16273 row16301 rfl

set_option maxRecDepth 16000 in
private theorem row16319 :
    FinalSeventhSieve.rough 11092009835083 16319+36351981=FinalSeventhSieve.rough 11092009835083 16301 :=
  LargeQuotientSieve.row (p:=16319) (q:=679699113) (s:=26071) (rank:=35255269) (tiny:=1892) (pairs:=1098603)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 679699113 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16319 : FinalSeventhSieve.rough 11092009835083 16319+365040918=FinalSeventhSieve.rough 11092009835083 16193 :=
  LargeQuotientSieve.combine to16301 row16319 rfl

set_option maxRecDepth 16000 in
private theorem row16333 :
    FinalSeventhSieve.rough 11092009835083 16333+36318196=FinalSeventhSieve.rough 11092009835083 16319 :=
  LargeQuotientSieve.row (p:=16333) (q:=679116502) (s:=26059) (rank:=35226596) (tiny:=1893) (pairs:=1093492)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 679116502 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16333 : FinalSeventhSieve.rough 11092009835083 16333+401359114=FinalSeventhSieve.rough 11092009835083 16193 :=
  LargeQuotientSieve.combine to16319 row16333 rfl

set_option maxRecDepth 16000 in
private theorem row16339 :
    FinalSeventhSieve.rough 11092009835083 16339+36302330=FinalSeventhSieve.rough 11092009835083 16333 :=
  LargeQuotientSieve.row (p:=16339) (q:=678867117) (s:=26055) (rank:=35214281) (tiny:=1894) (pairs:=1089942)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 678867117 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16339 : FinalSeventhSieve.rough 11092009835083 16339+437661444=FinalSeventhSieve.rough 11092009835083 16193 :=
  LargeQuotientSieve.combine to16333 row16339 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 16339+437661444=FinalSeventhSieve.rough 11092009835083 16193 := to16339

end Tail11092009835083From16193To16339
