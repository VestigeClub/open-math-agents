import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-975000000-1000000000»

/-! Exact changes for sieve primes 1345 through 1356. -/
open Finset
namespace Tail11092009835083From11087To11197

set_option maxRecDepth 16000 in
private theorem row11093 :
    FinalSeventhSieve.rough 11092009835083 11093+56769945=FinalSeventhSieve.rough 11092009835083 11087 :=
  LargeQuotientSieve.row (p:=11093) (q:=999910739) (s:=31621) (rank:=50843238) (tiny:=1344) (pairs:=5928050)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 999910739 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row11113 :
    FinalSeventhSieve.rough 11092009835083 11113+56658292=FinalSeventhSieve.rough 11092009835083 11093 :=
  LargeQuotientSieve.row (p:=11113) (q:=998111206) (s:=31592) (rank:=50756455) (tiny:=1345) (pairs:=5903181)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 998111206 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11113 : FinalSeventhSieve.rough 11092009835083 11113+113428237=FinalSeventhSieve.rough 11092009835083 11087 :=
  LargeQuotientSieve.combine row11093 row11113 rfl

set_option maxRecDepth 16000 in
private theorem row11117 :
    FinalSeventhSieve.rough 11092009835083 11117+56630043=FinalSeventhSieve.rough 11092009835083 11113 :=
  LargeQuotientSieve.row (p:=11117) (q:=997752076) (s:=31587) (rank:=50739034) (tiny:=1346) (pairs:=5892354)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 997752076 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11117 : FinalSeventhSieve.rough 11092009835083 11117+170058280=FinalSeventhSieve.rough 11092009835083 11087 :=
  LargeQuotientSieve.combine to11113 row11117 rfl

set_option maxRecDepth 16000 in
private theorem row11119 :
    FinalSeventhSieve.rough 11092009835083 11119+56612320=FinalSeventhSieve.rough 11092009835083 11117 :=
  LargeQuotientSieve.row (p:=11119) (q:=997572608) (s:=31584) (rank:=50730416) (tiny:=1347) (pairs:=5883250)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 997572608 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11119 : FinalSeventhSieve.rough 11092009835083 11119+226670600=FinalSeventhSieve.rough 11092009835083 11087 :=
  LargeQuotientSieve.combine to11117 row11119 rfl

set_option maxRecDepth 16000 in
private theorem row11131 :
    FinalSeventhSieve.rough 11092009835083 11131+56542635=FinalSeventhSieve.rough 11092009835083 11119 :=
  LargeQuotientSieve.row (p:=11131) (q:=996497155) (s:=31567) (rank:=50678454) (tiny:=1348) (pairs:=5865528)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 996497155 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11131 : FinalSeventhSieve.rough 11092009835083 11131+283213235=FinalSeventhSieve.rough 11092009835083 11087 :=
  LargeQuotientSieve.combine to11119 row11131 rfl

set_option maxRecDepth 16000 in
private theorem row11149 :
    FinalSeventhSieve.rough 11092009835083 11149+56442126=FinalSeventhSieve.rough 11092009835083 11131 :=
  LargeQuotientSieve.row (p:=11149) (q:=994888315) (s:=31541) (rank:=50600749) (tiny:=1349) (pairs:=5842725)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 994888315 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11149 : FinalSeventhSieve.rough 11092009835083 11149+339655361=FinalSeventhSieve.rough 11092009835083 11087 :=
  LargeQuotientSieve.combine to11131 row11149 rfl

set_option maxRecDepth 16000 in
private theorem row11159 :
    FinalSeventhSieve.rough 11092009835083 11159+56383143=FinalSeventhSieve.rough 11092009835083 11149 :=
  LargeQuotientSieve.row (p:=11159) (q:=993996759) (s:=31527) (rank:=50557691) (tiny:=1350) (pairs:=5826801)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 993996759 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11159 : FinalSeventhSieve.rough 11092009835083 11159+396038504=FinalSeventhSieve.rough 11092009835083 11087 :=
  LargeQuotientSieve.combine to11149 row11159 rfl

set_option maxRecDepth 16000 in
private theorem row11161 :
    FinalSeventhSieve.rough 11092009835083 11161+56365548=FinalSeventhSieve.rough 11092009835083 11159 :=
  LargeQuotientSieve.row (p:=11161) (q:=993818639) (s:=31524) (rank:=50549103) (tiny:=1351) (pairs:=5817795)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 993818639 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11161 : FinalSeventhSieve.rough 11092009835083 11161+452404052=FinalSeventhSieve.rough 11092009835083 11087 :=
  LargeQuotientSieve.combine to11159 row11161 rfl

set_option maxRecDepth 16000 in
private theorem row11171 :
    FinalSeventhSieve.rough 11092009835083 11171+56306800=FinalSeventhSieve.rough 11092009835083 11161 :=
  LargeQuotientSieve.row (p:=11171) (q:=992928997) (s:=31510) (rank:=50506196) (tiny:=1352) (pairs:=5801955)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 992928997 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11171 : FinalSeventhSieve.rough 11092009835083 11171+508710852=FinalSeventhSieve.rough 11092009835083 11087 :=
  LargeQuotientSieve.combine to11161 row11171 rfl

set_option maxRecDepth 16000 in
private theorem row11173 :
    FinalSeventhSieve.rough 11092009835083 11173+56289192=FinalSeventhSieve.rough 11092009835083 11171 :=
  LargeQuotientSieve.row (p:=11173) (q:=992751260) (s:=31507) (rank:=50497547) (tiny:=1353) (pairs:=5792997)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 992751260 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11173 : FinalSeventhSieve.rough 11092009835083 11173+565000044=FinalSeventhSieve.rough 11092009835083 11087 :=
  LargeQuotientSieve.combine to11171 row11173 rfl

set_option maxRecDepth 16000 in
private theorem row11177 :
    FinalSeventhSieve.rough 11092009835083 11177+56261414=FinalSeventhSieve.rough 11092009835083 11173 :=
  LargeQuotientSieve.row (p:=11177) (q:=992395977) (s:=31502) (rank:=50480424) (tiny:=1354) (pairs:=5782343)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 992395977 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11177 : FinalSeventhSieve.rough 11092009835083 11177+621261458=FinalSeventhSieve.rough 11092009835083 11087 :=
  LargeQuotientSieve.combine to11173 row11177 rfl

set_option maxRecDepth 16000 in
private theorem row11197 :
    FinalSeventhSieve.rough 11092009835083 11197+56151577=FinalSeventhSieve.rough 11092009835083 11177 :=
  LargeQuotientSieve.row (p:=11197) (q:=990623366) (s:=31474) (rank:=50394801) (tiny:=1355) (pairs:=5758130)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 990623366 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11197 : FinalSeventhSieve.rough 11092009835083 11197+677413035=FinalSeventhSieve.rough 11092009835083 11087 :=
  LargeQuotientSieve.combine to11177 row11197 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 11197+677413035=FinalSeventhSieve.rough 11092009835083 11087 := to11197

end Tail11092009835083From11087To11197
