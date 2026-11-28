import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-975000000-1000000000»

/-! Exact changes for sieve primes 1357 through 1368. -/
open Finset
namespace Tail11092009835083From11197To11317

set_option maxRecDepth 16000 in
private theorem row11213 :
    FinalSeventhSieve.rough 11092009835083 11213+56062605=FinalSeventhSieve.rough 11092009835083 11197 :=
  LargeQuotientSieve.row (p:=11213) (q:=989209831) (s:=31451) (rank:=50326608) (tiny:=1356) (pairs:=5737352)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 989209831 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row11239 :
    FinalSeventhSieve.rough 11092009835083 11239+55922953=FinalSeventhSieve.rough 11092009835083 11213 :=
  LargeQuotientSieve.row (p:=11239) (q:=986921419) (s:=31415) (rank:=50216138) (tiny:=1357) (pairs:=5708171)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 986921419 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11239 : FinalSeventhSieve.rough 11092009835083 11239+111985558=FinalSeventhSieve.rough 11092009835083 11197 :=
  LargeQuotientSieve.combine row11213 row11239 rfl

set_option maxRecDepth 16000 in
private theorem row11243 :
    FinalSeventhSieve.rough 11092009835083 11243+55895422=FinalSeventhSieve.rough 11092009835083 11239 :=
  LargeQuotientSieve.row (p:=11243) (q:=986570295) (s:=31409) (rank:=50199169) (tiny:=1358) (pairs:=5697610)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 986570295 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11243 : FinalSeventhSieve.rough 11092009835083 11243+167880980=FinalSeventhSieve.rough 11092009835083 11197 :=
  LargeQuotientSieve.combine to11239 row11243 rfl

set_option maxRecDepth 16000 in
private theorem row11251 :
    FinalSeventhSieve.rough 11092009835083 11251+55847664=FinalSeventhSieve.rough 11092009835083 11243 :=
  LargeQuotientSieve.row (p:=11251) (q:=985868797) (s:=31398) (rank:=50165261) (tiny:=1359) (pairs:=5683761)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 985868797 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11251 : FinalSeventhSieve.rough 11092009835083 11251+223728644=FinalSeventhSieve.rough 11092009835083 11197 :=
  LargeQuotientSieve.combine to11243 row11251 rfl

set_option maxRecDepth 16000 in
private theorem row11257 :
    FinalSeventhSieve.rough 11092009835083 11257+55810124=FinalSeventhSieve.rough 11092009835083 11251 :=
  LargeQuotientSieve.row (p:=11257) (q:=985343327) (s:=31390) (rank:=50139915) (tiny:=1360) (pairs:=5671568)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 985343327 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11257 : FinalSeventhSieve.rough 11092009835083 11257+279538768=FinalSeventhSieve.rough 11092009835083 11197 :=
  LargeQuotientSieve.combine to11251 row11257 rfl

set_option maxRecDepth 16000 in
private theorem row11261 :
    FinalSeventhSieve.rough 11092009835083 11261+55782713=FinalSeventhSieve.rough 11092009835083 11257 :=
  LargeQuotientSieve.row (p:=11261) (q:=984993325) (s:=31384) (rank:=50123002) (tiny:=1361) (pairs:=5661071)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 984993325 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11261 : FinalSeventhSieve.rough 11092009835083 11261+335321481=FinalSeventhSieve.rough 11092009835083 11197 :=
  LargeQuotientSieve.combine to11257 row11261 rfl

set_option maxRecDepth 16000 in
private theorem row11273 :
    FinalSeventhSieve.rough 11092009835083 11273+55714901=FinalSeventhSieve.rough 11092009835083 11261 :=
  LargeQuotientSieve.row (p:=11273) (q:=983944809) (s:=31367) (rank:=50072260) (tiny:=1362) (pairs:=5644002)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 983944809 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11273 : FinalSeventhSieve.rough 11092009835083 11273+391036382=FinalSeventhSieve.rough 11092009835083 11197 :=
  LargeQuotientSieve.combine to11261 row11273 rfl

set_option maxRecDepth 16000 in
private theorem row11279 :
    FinalSeventhSieve.rough 11092009835083 11279+55677521=FinalSeventhSieve.rough 11092009835083 11273 :=
  LargeQuotientSieve.row (p:=11279) (q:=983421387) (s:=31359) (rank:=50046924) (tiny:=1363) (pairs:=5631959)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 983421387 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11279 : FinalSeventhSieve.rough 11092009835083 11279+446713903=FinalSeventhSieve.rough 11092009835083 11197 :=
  LargeQuotientSieve.combine to11273 row11279 rfl

set_option maxRecDepth 16000 in
private theorem row11287 :
    FinalSeventhSieve.rough 11092009835083 11287+55630063=FinalSeventhSieve.rough 11092009835083 11279 :=
  LargeQuotientSieve.row (p:=11287) (q:=982724358) (s:=31348) (rank:=50013137) (tiny:=1364) (pairs:=5618289)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 982724358 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11287 : FinalSeventhSieve.rough 11092009835083 11287+502343966=FinalSeventhSieve.rough 11092009835083 11197 :=
  LargeQuotientSieve.combine to11279 row11287 rfl

set_option maxRecDepth 16000 in
private theorem row11299 :
    FinalSeventhSieve.rough 11092009835083 11299+55562695=FinalSeventhSieve.rough 11092009835083 11287 :=
  LargeQuotientSieve.row (p:=11299) (q:=981680665) (s:=31331) (rank:=49962793) (tiny:=1365) (pairs:=5601266)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 981680665 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11299 : FinalSeventhSieve.rough 11092009835083 11299+557906661=FinalSeventhSieve.rough 11092009835083 11197 :=
  LargeQuotientSieve.combine to11287 row11299 rfl

set_option maxRecDepth 16000 in
private theorem row11311 :
    FinalSeventhSieve.rough 11092009835083 11311+55495329=FinalSeventhSieve.rough 11092009835083 11299 :=
  LargeQuotientSieve.row (p:=11311) (q:=980639186) (s:=31315) (rank:=49912444) (tiny:=1366) (pairs:=5584250)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 980639186 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11311 : FinalSeventhSieve.rough 11092009835083 11311+613401990=FinalSeventhSieve.rough 11092009835083 11197 :=
  LargeQuotientSieve.combine to11299 row11311 rfl

set_option maxRecDepth 16000 in
private theorem row11317 :
    FinalSeventhSieve.rough 11092009835083 11317+55458292=FinalSeventhSieve.rough 11092009835083 11311 :=
  LargeQuotientSieve.row (p:=11317) (q:=980119274) (s:=31306) (rank:=49887396) (tiny:=1367) (pairs:=5572262)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 980119274 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11317 : FinalSeventhSieve.rough 11092009835083 11317+668860282=FinalSeventhSieve.rough 11092009835083 11197 :=
  LargeQuotientSieve.combine to11311 row11317 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 11317+668860282=FinalSeventhSieve.rough 11092009835083 11197 := to11317

end Tail11092009835083From11197To11317
