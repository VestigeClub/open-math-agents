import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1075000000-1100000000»

/-! Exact changes for sieve primes 1262 through 1265. -/
open Finset
namespace Tail11092009835083From10273To10313

set_option maxRecDepth 16000 in
private theorem row10289 :
    FinalSeventhSieve.rough 11092009835083 10289+61999367=FinalSeventhSieve.rough 11092009835083 10273 :=
  LargeQuotientSieve.row (p:=10289) (q:=1078045469) (s:=32833) (rank:=54606687) (tiny:=1261) (pairs:=7393940)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1078045469 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row10301 :
    FinalSeventhSieve.rough 11092009835083 10301+61916868=FinalSeventhSieve.rough 11092009835083 10289 :=
  LargeQuotientSieve.row (p:=10301) (q:=1076789616) (s:=32814) (rank:=54546401) (tiny:=1262) (pairs:=7371728)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1076789616 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10301 : FinalSeventhSieve.rough 11092009835083 10301+123916235=FinalSeventhSieve.rough 11092009835083 10273 :=
  LargeQuotientSieve.combine row10289 row10301 rfl

set_option maxRecDepth 16000 in
private theorem row10303 :
    FinalSeventhSieve.rough 11092009835083 10303+61895876=FinalSeventhSieve.rough 11092009835083 10301 :=
  LargeQuotientSieve.row (p:=10303) (q:=1076580591) (s:=32811) (rank:=54536370) (tiny:=1263) (pairs:=7360768)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1076580591 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10303 : FinalSeventhSieve.rough 11092009835083 10303+185812111=FinalSeventhSieve.rough 11092009835083 10273 :=
  LargeQuotientSieve.combine to10301 row10303 rfl

set_option maxRecDepth 16000 in
private theorem row10313 :
    FinalSeventhSieve.rough 11092009835083 10313+61825944=FinalSeventhSieve.rough 11092009835083 10303 :=
  LargeQuotientSieve.row (p:=10313) (q:=1075536685) (s:=32795) (rank:=54486219) (tiny:=1264) (pairs:=7340988)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1075536685 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10313 : FinalSeventhSieve.rough 11092009835083 10313+247638055=FinalSeventhSieve.rough 11092009835083 10273 :=
  LargeQuotientSieve.combine to10303 row10313 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10313+247638055=FinalSeventhSieve.rough 11092009835083 10273 := to10313

end Tail11092009835083From10273To10313
