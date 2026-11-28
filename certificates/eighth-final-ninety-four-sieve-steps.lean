import certificates.«eighth-final-nineteen-sieve-steps»
import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-975000000-1000000000»

/-! The final 94 sieve primes at the eighth endpoint remove 4,706,933,946 survivors. -/

/- Exact changes for sieve primes 3257 through 3268. -/
open Finset
namespace Tail30110134441897From30109To30211

set_option maxRecDepth 16000 in
private theorem row30113 :
    FinalSeventhSieve.rough 30110134441897 30113+50861195=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.row (p:=30113) (q:=999904839) (s:=31621) (rank:=50842926) (tiny:=3256) (pairs:=21524)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 999904839 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row30119 :
    FinalSeventhSieve.rough 30110134441897 30119+50851283=FinalSeventhSieve.rough 30110134441897 30113 :=
  LargeQuotientSieve.row (p:=30119) (q:=999705648) (s:=31618) (rank:=50833410) (tiny:=3257) (pairs:=21129)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 999705648 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30119 : FinalSeventhSieve.rough 30110134441897 30119+101712478=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine row30113 row30119 rfl

set_option maxRecDepth 16000 in
private theorem row30133 :
    FinalSeventhSieve.rough 30110134441897 30133+50828460=FinalSeventhSieve.rough 30110134441897 30119 :=
  LargeQuotientSieve.row (p:=30133) (q:=999241178) (s:=31610) (rank:=50811116) (tiny:=3258) (pairs:=20601)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 999241178 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30133 : FinalSeventhSieve.rough 30110134441897 30133+152540938=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30119 row30133 rfl

set_option maxRecDepth 16000 in
private theorem row30137 :
    FinalSeventhSieve.rough 30110134441897 30137+50821741=FinalSeventhSieve.rough 30110134441897 30133 :=
  LargeQuotientSieve.row (p:=30137) (q:=999108552) (s:=31608) (rank:=50804752) (tiny:=3259) (pairs:=20247)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 999108552 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30137 : FinalSeventhSieve.rough 30110134441897 30137+203362679=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30133 row30137 rfl

set_option maxRecDepth 16000 in
private theorem row30139 :
    FinalSeventhSieve.rough 30110134441897 30139+50818216=FinalSeventhSieve.rough 30110134441897 30137 :=
  LargeQuotientSieve.row (p:=30139) (q:=999042252) (s:=31607) (rank:=50801549) (tiny:=3260) (pairs:=19926)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 999042252 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30139 : FinalSeventhSieve.rough 30110134441897 30139+254180895=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30137 row30139 rfl

set_option maxRecDepth 16000 in
private theorem row30161 :
    FinalSeventhSieve.rough 30110134441897 30161+50782303=FinalSeventhSieve.rough 30110134441897 30139 :=
  LargeQuotientSieve.row (p:=30161) (q:=998313532) (s:=31596) (rank:=50766263) (tiny:=3261) (pairs:=19300)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 998313532 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30161 : FinalSeventhSieve.rough 30110134441897 30161+304963198=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30139 row30161 rfl

set_option maxRecDepth 16000 in
private theorem row30169 :
    FinalSeventhSieve.rough 30110134441897 30169+50769080=FinalSeventhSieve.rough 30110134441897 30161 :=
  LargeQuotientSieve.row (p:=30169) (q:=998048806) (s:=31591) (rank:=50753438) (tiny:=3262) (pairs:=18903)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 998048806 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30169 : FinalSeventhSieve.rough 30110134441897 30169+355732278=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30161 row30169 rfl

set_option maxRecDepth 16000 in
private theorem row30181 :
    FinalSeventhSieve.rough 30110134441897 30181+50749394=FinalSeventhSieve.rough 30110134441897 30169 :=
  LargeQuotientSieve.row (p:=30181) (q:=997651981) (s:=31585) (rank:=50734216) (tiny:=3263) (pairs:=18440)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 997651981 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30181 : FinalSeventhSieve.rough 30110134441897 30181+406481672=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30169 row30181 rfl

set_option maxRecDepth 16000 in
private theorem row30187 :
    FinalSeventhSieve.rough 30110134441897 30187+50739437=FinalSeventhSieve.rough 30110134441897 30181 :=
  LargeQuotientSieve.row (p:=30187) (q:=997453686) (s:=31582) (rank:=50724623) (tiny:=3264) (pairs:=18077)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 997453686 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30187 : FinalSeventhSieve.rough 30110134441897 30187+457221109=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30181 row30187 rfl

set_option maxRecDepth 16000 in
private theorem row30197 :
    FinalSeventhSieve.rough 30110134441897 30197+50723101=FinalSeventhSieve.rough 30110134441897 30187 :=
  LargeQuotientSieve.row (p:=30197) (q:=997123371) (s:=31577) (rank:=50708691) (tiny:=3265) (pairs:=17674)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 997123371 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30197 : FinalSeventhSieve.rough 30110134441897 30197+507944210=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30187 row30197 rfl

set_option maxRecDepth 16000 in
private theorem row30203 :
    FinalSeventhSieve.rough 30110134441897 30203+50713175=FinalSeventhSieve.rough 30110134441897 30197 :=
  LargeQuotientSieve.row (p:=30203) (q:=996925286) (s:=31574) (rank:=50699121) (tiny:=3266) (pairs:=17319)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 996925286 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30203 : FinalSeventhSieve.rough 30110134441897 30203+558657385=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30197 row30203 rfl

set_option maxRecDepth 16000 in
private theorem row30211 :
    FinalSeventhSieve.rough 30110134441897 30211+50700047=FinalSeventhSieve.rough 30110134441897 30203 :=
  LargeQuotientSieve.row (p:=30211) (q:=996661296) (s:=31569) (rank:=50686383) (tiny:=3267) (pairs:=16930)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 996661296 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30211 : FinalSeventhSieve.rough 30110134441897 30211+609357432=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30203 row30211 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 30211+609357432=FinalSeventhSieve.rough 30110134441897 30109 := to30211

end Tail30110134441897From30109To30211

/- Exact changes for sieve primes 3269 through 3280. -/
open Finset
namespace Tail30110134441897From30211To30341

set_option maxRecDepth 16000 in
private theorem row30223 :
    FinalSeventhSieve.rough 30110134441897 30223+50680503=FinalSeventhSieve.rough 30110134441897 30211 :=
  LargeQuotientSieve.row (p:=30223) (q:=996265573) (s:=31563) (rank:=50667253) (tiny:=3268) (pairs:=16517)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 996265573 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row30241 :
    FinalSeventhSieve.rough 30110134441897 30241+50651308=FinalSeventhSieve.rough 30110134441897 30223 :=
  LargeQuotientSieve.row (p:=30241) (q:=995672578) (s:=31554) (rank:=50638570) (tiny:=3269) (pairs:=16006)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 995672578 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30241 : FinalSeventhSieve.rough 30110134441897 30241+101331811=FinalSeventhSieve.rough 30110134441897 30211 :=
  LargeQuotientSieve.combine row30223 row30241 rfl

set_option maxRecDepth 16000 in
private theorem row30253 :
    FinalSeventhSieve.rough 30110134441897 30253+50631928=FinalSeventhSieve.rough 30110134441897 30241 :=
  LargeQuotientSieve.row (p:=30253) (q:=995277639) (s:=31548) (rank:=50619601) (tiny:=3270) (pairs:=15596)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 995277639 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30253 : FinalSeventhSieve.rough 30110134441897 30253+151963739=FinalSeventhSieve.rough 30110134441897 30211 :=
  LargeQuotientSieve.combine to30241 row30253 rfl

set_option maxRecDepth 16000 in
private theorem row30259 :
    FinalSeventhSieve.rough 30110134441897 30259+50622039=FinalSeventhSieve.rough 30110134441897 30253 :=
  LargeQuotientSieve.row (p:=30259) (q:=995080288) (s:=31544) (rank:=50610046) (tiny:=3271) (pairs:=15263)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 995080288 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30259 : FinalSeventhSieve.rough 30110134441897 30259+202585778=FinalSeventhSieve.rough 30110134441897 30211 :=
  LargeQuotientSieve.combine to30253 row30259 rfl

set_option maxRecDepth 16000 in
private theorem row30269 :
    FinalSeventhSieve.rough 30110134441897 30269+50605750=FinalSeventhSieve.rough 30110134441897 30259 :=
  LargeQuotientSieve.row (p:=30269) (q:=994751542) (s:=31539) (rank:=50594129) (tiny:=3272) (pairs:=14892)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 994751542 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30269 : FinalSeventhSieve.rough 30110134441897 30269+253191528=FinalSeventhSieve.rough 30110134441897 30211 :=
  LargeQuotientSieve.combine to30259 row30269 rfl

set_option maxRecDepth 16000 in
private theorem row30271 :
    FinalSeventhSieve.rough 30110134441897 30271+50602334=FinalSeventhSieve.rough 30110134441897 30269 :=
  LargeQuotientSieve.row (p:=30271) (q:=994685819) (s:=31538) (rank:=50590989) (tiny:=3273) (pairs:=14617)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 994685819 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30271 : FinalSeventhSieve.rough 30110134441897 30271+303793862=FinalSeventhSieve.rough 30110134441897 30211 :=
  LargeQuotientSieve.combine to30269 row30271 rfl

set_option maxRecDepth 16000 in
private theorem row30293 :
    FinalSeventhSieve.rough 30110134441897 30293+50566937=FinalSeventhSieve.rough 30110134441897 30271 :=
  LargeQuotientSieve.row (p:=30293) (q:=993963438) (s:=31527) (rank:=50556113) (tiny:=3274) (pairs:=14097)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 993963438 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30293 : FinalSeventhSieve.rough 30110134441897 30293+354360799=FinalSeventhSieve.rough 30110134441897 30211 :=
  LargeQuotientSieve.combine to30271 row30293 rfl

set_option maxRecDepth 16000 in
private theorem row30307 :
    FinalSeventhSieve.rough 30110134441897 30307+50544344=FinalSeventhSieve.rough 30110134441897 30293 :=
  LargeQuotientSieve.row (p:=30307) (q:=993504287) (s:=31519) (rank:=50533944) (tiny:=3275) (pairs:=13674)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 993504287 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30307 : FinalSeventhSieve.rough 30110134441897 30307+404905143=FinalSeventhSieve.rough 30110134441897 30211 :=
  LargeQuotientSieve.combine to30293 row30307 rfl

set_option maxRecDepth 16000 in
private theorem row30313 :
    FinalSeventhSieve.rough 30110134441897 30313+50534599=FinalSeventhSieve.rough 30110134441897 30307 :=
  LargeQuotientSieve.row (p:=30313) (q:=993307638) (s:=31516) (rank:=50524524) (tiny:=3276) (pairs:=13350)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 993307638 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30313 : FinalSeventhSieve.rough 30110134441897 30313+455439742=FinalSeventhSieve.rough 30110134441897 30211 :=
  LargeQuotientSieve.combine to30307 row30313 rfl

set_option maxRecDepth 16000 in
private theorem row30319 :
    FinalSeventhSieve.rough 30110134441897 30319+50524746=FinalSeventhSieve.rough 30110134441897 30313 :=
  LargeQuotientSieve.row (p:=30319) (q:=993111067) (s:=31513) (rank:=50514971) (tiny:=3277) (pairs:=13051)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 993111067 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30319 : FinalSeventhSieve.rough 30110134441897 30319+505964488=FinalSeventhSieve.rough 30110134441897 30211 :=
  LargeQuotientSieve.combine to30313 row30319 rfl

set_option maxRecDepth 16000 in
private theorem row30323 :
    FinalSeventhSieve.rough 30110134441897 30323+50518136=FinalSeventhSieve.rough 30110134441897 30319 :=
  LargeQuotientSieve.row (p:=30323) (q:=992980062) (s:=31511) (rank:=50508644) (tiny:=3278) (pairs:=12769)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 992980062 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30323 : FinalSeventhSieve.rough 30110134441897 30323+556482624=FinalSeventhSieve.rough 30110134441897 30211 :=
  LargeQuotientSieve.combine to30319 row30323 rfl

set_option maxRecDepth 16000 in
private theorem row30341 :
    FinalSeventhSieve.rough 30110134441897 30341+50489235=FinalSeventhSieve.rough 30110134441897 30323 :=
  LargeQuotientSieve.row (p:=30341) (q:=992390970) (s:=31502) (rank:=50480174) (tiny:=3279) (pairs:=12339)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 992390970 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30341 : FinalSeventhSieve.rough 30110134441897 30341+606971859=FinalSeventhSieve.rough 30110134441897 30211 :=
  LargeQuotientSieve.combine to30323 row30341 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 30341+606971859=FinalSeventhSieve.rough 30110134441897 30211 := to30341

end Tail30110134441897From30211To30341

/- Exact changes for sieve primes 3281 through 3292. -/
open Finset
namespace Tail30110134441897From30341To30493

set_option maxRecDepth 16000 in
private theorem row30347 :
    FinalSeventhSieve.rough 30110134441897 30347+50479488=FinalSeventhSieve.rough 30110134441897 30341 :=
  LargeQuotientSieve.row (p:=30347) (q:=992194761) (s:=31499) (rank:=50470721) (tiny:=3280) (pairs:=12046)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 992194761 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row30367 :
    FinalSeventhSieve.rough 30110134441897 30367+50447677=FinalSeventhSieve.rough 30110134441897 30347 :=
  LargeQuotientSieve.row (p:=30367) (q:=991541292) (s:=31488) (rank:=50439378) (tiny:=3281) (pairs:=11579)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 991541292 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30367 : FinalSeventhSieve.rough 30110134441897 30367+100927165=FinalSeventhSieve.rough 30110134441897 30341 :=
  LargeQuotientSieve.combine row30347 row30367 rfl

set_option maxRecDepth 16000 in
private theorem row30389 :
    FinalSeventhSieve.rough 30110134441897 30389+50412350=FinalSeventhSieve.rough 30110134441897 30367 :=
  LargeQuotientSieve.row (p:=30389) (q:=990823470) (s:=31477) (rank:=50404510) (tiny:=3282) (pairs:=11121)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 990823470 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30389 : FinalSeventhSieve.rough 30110134441897 30389+151339515=FinalSeventhSieve.rough 30110134441897 30341 :=
  LargeQuotientSieve.combine to30367 row30389 rfl

set_option maxRecDepth 16000 in
private theorem row30391 :
    FinalSeventhSieve.rough 30110134441897 30391+50408988=FinalSeventhSieve.rough 30110134441897 30389 :=
  LargeQuotientSieve.row (p:=30391) (q:=990758265) (s:=31476) (rank:=50401383) (tiny:=3283) (pairs:=10887)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 990758265 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30391 : FinalSeventhSieve.rough 30110134441897 30391+201748503=FinalSeventhSieve.rough 30110134441897 30341 :=
  LargeQuotientSieve.combine to30389 row30391 rfl

set_option maxRecDepth 16000 in
private theorem row30403 :
    FinalSeventhSieve.rough 30110134441897 30403+50389738=FinalSeventhSieve.rough 30110134441897 30391 :=
  LargeQuotientSieve.row (p:=30403) (q:=990367215) (s:=31470) (rank:=50382470) (tiny:=3284) (pairs:=10551)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 990367215 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30403 : FinalSeventhSieve.rough 30110134441897 30403+252138241=FinalSeventhSieve.rough 30110134441897 30341 :=
  LargeQuotientSieve.combine to30391 row30403 rfl

set_option maxRecDepth 16000 in
private theorem row30427 :
    FinalSeventhSieve.rough 30110134441897 30427+50351535=FinalSeventhSieve.rough 30110134441897 30403 :=
  LargeQuotientSieve.row (p:=30427) (q:=989586040) (s:=31457) (rank:=50344732) (tiny:=3285) (pairs:=10087)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 989586040 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30427 : FinalSeventhSieve.rough 30110134441897 30427+302489776=FinalSeventhSieve.rough 30110134441897 30341 :=
  LargeQuotientSieve.combine to30403 row30427 rfl

set_option maxRecDepth 16000 in
private theorem row30431 :
    FinalSeventhSieve.rough 30110134441897 30431+50344999=FinalSeventhSieve.rough 30110134441897 30427 :=
  LargeQuotientSieve.row (p:=30431) (q:=989455964) (s:=31455) (rank:=50338443) (tiny:=3286) (pairs:=9841)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 989455964 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30431 : FinalSeventhSieve.rough 30110134441897 30431+352834775=FinalSeventhSieve.rough 30110134441897 30341 :=
  LargeQuotientSieve.combine to30427 row30431 rfl

set_option maxRecDepth 16000 in
private theorem row30449 :
    FinalSeventhSieve.rough 30110134441897 30449+50316401=FinalSeventhSieve.rough 30110134441897 30431 :=
  LargeQuotientSieve.row (p:=30449) (q:=988871044) (s:=31446) (rank:=50310233) (tiny:=3287) (pairs:=9454)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 988871044 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30449 : FinalSeventhSieve.rough 30110134441897 30449+403151176=FinalSeventhSieve.rough 30110134441897 30341 :=
  LargeQuotientSieve.combine to30431 row30449 rfl

set_option maxRecDepth 16000 in
private theorem row30467 :
    FinalSeventhSieve.rough 30110134441897 30467+50287822=FinalSeventhSieve.rough 30110134441897 30449 :=
  LargeQuotientSieve.row (p:=30467) (q:=988286816) (s:=31437) (rank:=50282033) (tiny:=3288) (pairs:=9076)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 988286816 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30467 : FinalSeventhSieve.rough 30110134441897 30467+453438998=FinalSeventhSieve.rough 30110134441897 30341 :=
  LargeQuotientSieve.combine to30449 row30467 rfl

set_option maxRecDepth 16000 in
private theorem row30469 :
    FinalSeventhSieve.rough 30110134441897 30469+50284521=FinalSeventhSieve.rough 30110134441897 30467 :=
  LargeQuotientSieve.row (p:=30469) (q:=988221944) (s:=31435) (rank:=50278955) (tiny:=3289) (pairs:=8854)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 988221944 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30469 : FinalSeventhSieve.rough 30110134441897 30469+503723519=FinalSeventhSieve.rough 30110134441897 30341 :=
  LargeQuotientSieve.combine to30467 row30469 rfl

set_option maxRecDepth 16000 in
private theorem row30491 :
    FinalSeventhSieve.rough 30110134441897 30491+50249654=FinalSeventhSieve.rough 30110134441897 30469 :=
  LargeQuotientSieve.row (p:=30491) (q:=987508918) (s:=31424) (rank:=50244485) (tiny:=3290) (pairs:=8458)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 987508918 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30491 : FinalSeventhSieve.rough 30110134441897 30491+553973173=FinalSeventhSieve.rough 30110134441897 30341 :=
  LargeQuotientSieve.combine to30469 row30491 rfl

set_option maxRecDepth 16000 in
private theorem row30493 :
    FinalSeventhSieve.rough 30110134441897 30493+50246328=FinalSeventhSieve.rough 30110134441897 30491 :=
  LargeQuotientSieve.row (p:=30493) (q:=987444149) (s:=31423) (rank:=50241369) (tiny:=3291) (pairs:=8249)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 987444149 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30493 : FinalSeventhSieve.rough 30110134441897 30493+604219501=FinalSeventhSieve.rough 30110134441897 30341 :=
  LargeQuotientSieve.combine to30491 row30493 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 30493+604219501=FinalSeventhSieve.rough 30110134441897 30341 := to30493

end Tail30110134441897From30341To30493

/- Exact changes for sieve primes 3293 through 3304. -/
open Finset
namespace Tail30110134441897From30493To30637

set_option maxRecDepth 16000 in
private theorem row30497 :
    FinalSeventhSieve.rough 30110134441897 30497+50239915=FinalSeventhSieve.rough 30110134441897 30493 :=
  LargeQuotientSieve.row (p:=30497) (q:=987314635) (s:=31421) (rank:=50235182) (tiny:=3292) (pairs:=8024)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 987314635 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row30509 :
    FinalSeventhSieve.rough 30110134441897 30509+50220836=FinalSeventhSieve.rough 30110134441897 30497 :=
  LargeQuotientSieve.row (p:=30509) (q:=986926298) (s:=31415) (rank:=50216388) (tiny:=3293) (pairs:=7740)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 986926298 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30509 : FinalSeventhSieve.rough 30110134441897 30509+100460751=FinalSeventhSieve.rough 30110134441897 30493 :=
  LargeQuotientSieve.combine row30497 row30509 rfl

set_option maxRecDepth 16000 in
private theorem row30517 :
    FinalSeventhSieve.rough 30110134441897 30517+50208088=FinalSeventhSieve.rough 30110134441897 30509 :=
  LargeQuotientSieve.row (p:=30517) (q:=986667576) (s:=31411) (rank:=50203881) (tiny:=3294) (pairs:=7500)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 986667576 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30517 : FinalSeventhSieve.rough 30110134441897 30517+150668839=FinalSeventhSieve.rough 30110134441897 30493 :=
  LargeQuotientSieve.combine to30509 row30517 rfl

set_option maxRecDepth 16000 in
private theorem row30529 :
    FinalSeventhSieve.rough 30110134441897 30529+50189043=FinalSeventhSieve.rough 30110134441897 30517 :=
  LargeQuotientSieve.row (p:=30529) (q:=986279748) (s:=31405) (rank:=50185111) (tiny:=3295) (pairs:=7226)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 986279748 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30529 : FinalSeventhSieve.rough 30110134441897 30529+200857882=FinalSeventhSieve.rough 30110134441897 30493 :=
  LargeQuotientSieve.combine to30517 row30529 rfl

set_option maxRecDepth 16000 in
private theorem row30539 :
    FinalSeventhSieve.rough 30110134441897 30539+50173171=FinalSeventhSieve.rough 30110134441897 30529 :=
  LargeQuotientSieve.row (p:=30539) (q:=985956791) (s:=31399) (rank:=50169496) (tiny:=3296) (pairs:=6970)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 985956791 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30539 : FinalSeventhSieve.rough 30110134441897 30539+251031053=FinalSeventhSieve.rough 30110134441897 30493 :=
  LargeQuotientSieve.combine to30529 row30539 rfl

set_option maxRecDepth 16000 in
private theorem row30553 :
    FinalSeventhSieve.rough 30110134441897 30553+50151102=FinalSeventhSieve.rough 30110134441897 30539 :=
  LargeQuotientSieve.row (p:=30553) (q:=985505005) (s:=31392) (rank:=50147707) (tiny:=3297) (pairs:=6691)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 985505005 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30553 : FinalSeventhSieve.rough 30110134441897 30553+301182155=FinalSeventhSieve.rough 30110134441897 30493 :=
  LargeQuotientSieve.combine to30539 row30553 rfl

set_option maxRecDepth 16000 in
private theorem row30557 :
    FinalSeventhSieve.rough 30110134441897 30557+50144721=FinalSeventhSieve.rough 30110134441897 30553 :=
  LargeQuotientSieve.row (p:=30557) (q:=985376000) (s:=31390) (rank:=50141519) (tiny:=3298) (pairs:=6499)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 985376000 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30557 : FinalSeventhSieve.rough 30110134441897 30557+351326876=FinalSeventhSieve.rough 30110134441897 30493 :=
  LargeQuotientSieve.combine to30553 row30557 rfl

set_option maxRecDepth 16000 in
private theorem row30559 :
    FinalSeventhSieve.rough 30110134441897 30559+50141332=FinalSeventhSieve.rough 30110134441897 30557 :=
  LargeQuotientSieve.row (p:=30559) (q:=985311510) (s:=31389) (rank:=50138306) (tiny:=3299) (pairs:=6324)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 985311510 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30559 : FinalSeventhSieve.rough 30110134441897 30559+401468208=FinalSeventhSieve.rough 30110134441897 30493 :=
  LargeQuotientSieve.combine to30557 row30559 rfl

set_option maxRecDepth 16000 in
private theorem row30577 :
    FinalSeventhSieve.rough 30110134441897 30577+50113093=FinalSeventhSieve.rough 30110134441897 30559 :=
  LargeQuotientSieve.row (p:=30577) (q:=984731479) (s:=31380) (rank:=50110355) (tiny:=3300) (pairs:=6037)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 984731479 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30577 : FinalSeventhSieve.rough 30110134441897 30577+451581301=FinalSeventhSieve.rough 30110134441897 30493 :=
  LargeQuotientSieve.combine to30559 row30577 rfl

set_option maxRecDepth 16000 in
private theorem row30593 :
    FinalSeventhSieve.rough 30110134441897 30593+50087951=FinalSeventhSieve.rough 30110134441897 30577 :=
  LargeQuotientSieve.row (p:=30593) (q:=984216469) (s:=31372) (rank:=50085481) (tiny:=3301) (pairs:=5770)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 984216469 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30593 : FinalSeventhSieve.rough 30110134441897 30593+501669252=FinalSeventhSieve.rough 30110134441897 30493 :=
  LargeQuotientSieve.combine to30577 row30593 rfl

set_option maxRecDepth 16000 in
private theorem row30631 :
    FinalSeventhSieve.rough 30110134441897 30631+50028384=FinalSeventhSieve.rough 30110134441897 30593 :=
  LargeQuotientSieve.row (p:=30631) (q:=982995476) (s:=31352) (rank:=50026340) (tiny:=3302) (pairs:=5345)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 982995476 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30631 : FinalSeventhSieve.rough 30110134441897 30631+551697636=FinalSeventhSieve.rough 30110134441897 30493 :=
  LargeQuotientSieve.combine to30593 row30631 rfl

set_option maxRecDepth 16000 in
private theorem row30637 :
    FinalSeventhSieve.rough 30110134441897 30637+50018794=FinalSeventhSieve.rough 30110134441897 30631 :=
  LargeQuotientSieve.row (p:=30637) (q:=982802965) (s:=31349) (rank:=50016941) (tiny:=3303) (pairs:=5155)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 982802965 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30637 : FinalSeventhSieve.rough 30110134441897 30637+601716430=FinalSeventhSieve.rough 30110134441897 30493 :=
  LargeQuotientSieve.combine to30631 row30637 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 30637+601716430=FinalSeventhSieve.rough 30110134441897 30493 := to30637

end Tail30110134441897From30493To30637

/- Exact changes for sieve primes 3305 through 3316. -/
open Finset
namespace Tail30110134441897From30637To30757

set_option maxRecDepth 16000 in
private theorem row30643 :
    FinalSeventhSieve.rough 30110134441897 30643+50009360=FinalSeventhSieve.rough 30110134441897 30637 :=
  LargeQuotientSieve.row (p:=30643) (q:=982610529) (s:=31346) (rank:=50007685) (tiny:=3304) (pairs:=4978)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 982610529 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row30649 :
    FinalSeventhSieve.rough 30110134441897 30649+49999801=FinalSeventhSieve.rough 30110134441897 30643 :=
  LargeQuotientSieve.row (p:=30649) (q:=982418168) (s:=31343) (rank:=49998303) (tiny:=3305) (pairs:=4802)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 982418168 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30649 : FinalSeventhSieve.rough 30110134441897 30649+100009161=FinalSeventhSieve.rough 30110134441897 30637 :=
  LargeQuotientSieve.combine row30643 row30649 rfl

set_option maxRecDepth 16000 in
private theorem row30661 :
    FinalSeventhSieve.rough 30110134441897 30661+49981034=FinalSeventhSieve.rough 30110134441897 30649 :=
  LargeQuotientSieve.row (p:=30661) (q:=982033672) (s:=31337) (rank:=49979728) (tiny:=3306) (pairs:=4611)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 982033672 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30661 : FinalSeventhSieve.rough 30110134441897 30661+149990195=FinalSeventhSieve.rough 30110134441897 30637 :=
  LargeQuotientSieve.combine to30649 row30661 rfl

set_option maxRecDepth 16000 in
private theorem row30671 :
    FinalSeventhSieve.rough 30110134441897 30671+49965486=FinalSeventhSieve.rough 30110134441897 30661 :=
  LargeQuotientSieve.row (p:=30671) (q:=981713489) (s:=31332) (rank:=49964371) (tiny:=3307) (pairs:=4421)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 981713489 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30671 : FinalSeventhSieve.rough 30110134441897 30671+199955681=FinalSeventhSieve.rough 30110134441897 30637 :=
  LargeQuotientSieve.combine to30661 row30671 rfl

set_option maxRecDepth 16000 in
private theorem row30677 :
    FinalSeventhSieve.rough 30110134441897 30677+49956058=FinalSeventhSieve.rough 30110134441897 30671 :=
  LargeQuotientSieve.row (p:=30677) (q:=981521479) (s:=31329) (rank:=49955112) (tiny:=3308) (pairs:=4253)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 981521479 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30677 : FinalSeventhSieve.rough 30110134441897 30677+249911739=FinalSeventhSieve.rough 30110134441897 30637 :=
  LargeQuotientSieve.combine to30671 row30677 rfl

set_option maxRecDepth 16000 in
private theorem row30689 :
    FinalSeventhSieve.rough 30110134441897 30689+49937250=FinalSeventhSieve.rough 30110134441897 30677 :=
  LargeQuotientSieve.row (p:=30689) (q:=981137685) (s:=31323) (rank:=49936500) (tiny:=3309) (pairs:=4058)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 981137685 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30689 : FinalSeventhSieve.rough 30110134441897 30689+299848989=FinalSeventhSieve.rough 30110134441897 30637 :=
  LargeQuotientSieve.combine to30677 row30689 rfl

set_option maxRecDepth 16000 in
private theorem row30697 :
    FinalSeventhSieve.rough 30110134441897 30697+49924711=FinalSeventhSieve.rough 30110134441897 30689 :=
  LargeQuotientSieve.row (p:=30697) (q:=980881989) (s:=31319) (rank:=49924125) (tiny:=3310) (pairs:=3895)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 980881989 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30697 : FinalSeventhSieve.rough 30110134441897 30697+349773700=FinalSeventhSieve.rough 30110134441897 30637 :=
  LargeQuotientSieve.combine to30689 row30697 rfl

set_option maxRecDepth 16000 in
private theorem row30703 :
    FinalSeventhSieve.rough 30110134441897 30703+49915346=FinalSeventhSieve.rough 30110134441897 30697 :=
  LargeQuotientSieve.row (p:=30703) (q:=980690305) (s:=31315) (rank:=49914914) (tiny:=3311) (pairs:=3742)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 980690305 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30703 : FinalSeventhSieve.rough 30110134441897 30703+399689046=FinalSeventhSieve.rough 30110134441897 30637 :=
  LargeQuotientSieve.combine to30697 row30703 rfl

set_option maxRecDepth 16000 in
private theorem row30707 :
    FinalSeventhSieve.rough 30110134441897 30707+49909094=FinalSeventhSieve.rough 30110134441897 30703 :=
  LargeQuotientSieve.row (p:=30707) (q:=980562557) (s:=31313) (rank:=49908801) (tiny:=3312) (pairs:=3604)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 980562557 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30707 : FinalSeventhSieve.rough 30110134441897 30707+449598140=FinalSeventhSieve.rough 30110134441897 30637 :=
  LargeQuotientSieve.combine to30703 row30707 rfl

set_option maxRecDepth 16000 in
private theorem row30713 :
    FinalSeventhSieve.rough 30110134441897 30713+49899678=FinalSeventhSieve.rough 30110134441897 30707 :=
  LargeQuotientSieve.row (p:=30713) (q:=980370997) (s:=31310) (rank:=49899534) (tiny:=3313) (pairs:=3456)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 980370997 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30713 : FinalSeventhSieve.rough 30110134441897 30713+499497818=FinalSeventhSieve.rough 30110134441897 30637 :=
  LargeQuotientSieve.combine to30707 row30713 rfl

set_option maxRecDepth 16000 in
private theorem row30727 :
    FinalSeventhSieve.rough 30110134441897 30727+49877902=FinalSeventhSieve.rough 30110134441897 30713 :=
  LargeQuotientSieve.row (p:=30727) (q:=979924315) (s:=31303) (rank:=49877943) (tiny:=3314) (pairs:=3272)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 979924315 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30727 : FinalSeventhSieve.rough 30110134441897 30727+549375720=FinalSeventhSieve.rough 30110134441897 30637 :=
  LargeQuotientSieve.combine to30713 row30727 rfl

set_option maxRecDepth 16000 in
private theorem row30757 :
    FinalSeventhSieve.rough 30110134441897 30757+49831470=FinalSeventhSieve.rough 30110134441897 30727 :=
  LargeQuotientSieve.row (p:=30757) (q:=978968509) (s:=31288) (rank:=49831777) (tiny:=3315) (pairs:=3007)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 978968509 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30757 : FinalSeventhSieve.rough 30110134441897 30757+599207190=FinalSeventhSieve.rough 30110134441897 30637 :=
  LargeQuotientSieve.combine to30727 row30757 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 30757+599207190=FinalSeventhSieve.rough 30110134441897 30637 := to30757

end Tail30110134441897From30637To30757

/- Exact changes for sieve primes 3317 through 3328. -/
open Finset
namespace Tail30110134441897From30757To30859

set_option maxRecDepth 16000 in
private theorem row30763 :
    FinalSeventhSieve.rough 30110134441897 30763+49822088=FinalSeventhSieve.rough 30110134441897 30757 :=
  LargeQuotientSieve.row (p:=30763) (q:=978777571) (s:=31285) (rank:=49822539) (tiny:=3316) (pairs:=2864)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 978777571 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row30773 :
    FinalSeventhSieve.rough 30110134441897 30773+49806706=FinalSeventhSieve.rough 30110134441897 30763 :=
  LargeQuotientSieve.row (p:=30773) (q:=978459508) (s:=31280) (rank:=49807310) (tiny:=3317) (pairs:=2712)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 978459508 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30773 : FinalSeventhSieve.rough 30110134441897 30773+99628794=FinalSeventhSieve.rough 30110134441897 30757 :=
  LargeQuotientSieve.combine row30763 row30773 rfl

set_option maxRecDepth 16000 in
private theorem row30781 :
    FinalSeventhSieve.rough 30110134441897 30781+49794257=FinalSeventhSieve.rough 30110134441897 30773 :=
  LargeQuotientSieve.row (p:=30781) (q:=978205205) (s:=31276) (rank:=49795000) (tiny:=3318) (pairs:=2574)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 978205205 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30781 : FinalSeventhSieve.rough 30110134441897 30781+149423051=FinalSeventhSieve.rough 30110134441897 30757 :=
  LargeQuotientSieve.combine to30773 row30781 rfl

set_option maxRecDepth 16000 in
private theorem row30803 :
    FinalSeventhSieve.rough 30110134441897 30803+49760330=FinalSeventhSieve.rough 30110134441897 30781 :=
  LargeQuotientSieve.row (p:=30803) (q:=977506555) (s:=31265) (rank:=49761280) (tiny:=3319) (pairs:=2368)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 977506555 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30803 : FinalSeventhSieve.rough 30110134441897 30803+199183381=FinalSeventhSieve.rough 30110134441897 30757 :=
  LargeQuotientSieve.combine to30781 row30803 rfl

set_option maxRecDepth 16000 in
private theorem row30809 :
    FinalSeventhSieve.rough 30110134441897 30809+49751084=FinalSeventhSieve.rough 30110134441897 30803 :=
  LargeQuotientSieve.row (p:=30809) (q:=977316188) (s:=31262) (rank:=49752155) (tiny:=3320) (pairs:=2248)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 977316188 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30809 : FinalSeventhSieve.rough 30110134441897 30809+248934465=FinalSeventhSieve.rough 30110134441897 30757 :=
  LargeQuotientSieve.combine to30803 row30809 rfl

set_option maxRecDepth 16000 in
private theorem row30817 :
    FinalSeventhSieve.rough 30110134441897 30817+49738631=FinalSeventhSieve.rough 30110134441897 30809 :=
  LargeQuotientSieve.row (p:=30817) (q:=977062479) (s:=31257) (rank:=49739827) (tiny:=3321) (pairs:=2124)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 977062479 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30817 : FinalSeventhSieve.rough 30110134441897 30817+298673096=FinalSeventhSieve.rough 30110134441897 30757 :=
  LargeQuotientSieve.combine to30809 row30817 rfl

set_option maxRecDepth 16000 in
private theorem row30829 :
    FinalSeventhSieve.rough 30110134441897 30829+49720062=FinalSeventhSieve.rough 30110134441897 30817 :=
  LargeQuotientSieve.row (p:=30829) (q:=976682164) (s:=31251) (rank:=49721407) (tiny:=3322) (pairs:=1976)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 976682164 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30829 : FinalSeventhSieve.rough 30110134441897 30829+348393158=FinalSeventhSieve.rough 30110134441897 30757 :=
  LargeQuotientSieve.combine to30817 row30829 rfl

set_option maxRecDepth 16000 in
private theorem row30839 :
    FinalSeventhSieve.rough 30110134441897 30839+49704624=FinalSeventhSieve.rough 30110134441897 30829 :=
  LargeQuotientSieve.row (p:=30839) (q:=976365460) (s:=31246) (rank:=49706100) (tiny:=3323) (pairs:=1846)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 976365460 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30839 : FinalSeventhSieve.rough 30110134441897 30839+398097782=FinalSeventhSieve.rough 30110134441897 30757 :=
  LargeQuotientSieve.combine to30829 row30839 rfl

set_option maxRecDepth 16000 in
private theorem row30841 :
    FinalSeventhSieve.rough 30110134441897 30841+49701434=FinalSeventhSieve.rough 30110134441897 30839 :=
  LargeQuotientSieve.row (p:=30841) (q:=976302144) (s:=31245) (rank:=49702999) (tiny:=3324) (pairs:=1758)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 976302144 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30841 : FinalSeventhSieve.rough 30110134441897 30841+447799216=FinalSeventhSieve.rough 30110134441897 30757 :=
  LargeQuotientSieve.combine to30839 row30841 rfl

set_option maxRecDepth 16000 in
private theorem row30851 :
    FinalSeventhSieve.rough 30110134441897 30851+49686063=FinalSeventhSieve.rough 30110134441897 30841 :=
  LargeQuotientSieve.row (p:=30851) (q:=975985687) (s:=31240) (rank:=49687745) (tiny:=3325) (pairs:=1642)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 975985687 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30851 : FinalSeventhSieve.rough 30110134441897 30851+497485279=FinalSeventhSieve.rough 30110134441897 30757 :=
  LargeQuotientSieve.combine to30841 row30851 rfl

set_option maxRecDepth 16000 in
private theorem row30853 :
    FinalSeventhSieve.rough 30110134441897 30853+49682980=FinalSeventhSieve.rough 30110134441897 30851 :=
  LargeQuotientSieve.row (p:=30853) (q:=975922420) (s:=31239) (rank:=49684752) (tiny:=3326) (pairs:=1553)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 975922420 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30853 : FinalSeventhSieve.rough 30110134441897 30853+547168259=FinalSeventhSieve.rough 30110134441897 30757 :=
  LargeQuotientSieve.combine to30851 row30853 rfl

set_option maxRecDepth 16000 in
private theorem row30859 :
    FinalSeventhSieve.rough 30110134441897 30859+49673723=FinalSeventhSieve.rough 30110134441897 30853 :=
  LargeQuotientSieve.row (p:=30859) (q:=975732669) (s:=31236) (rank:=49675593) (tiny:=3327) (pairs:=1456)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 975732669 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30859 : FinalSeventhSieve.rough 30110134441897 30859+596841982=FinalSeventhSieve.rough 30110134441897 30757 :=
  LargeQuotientSieve.combine to30853 row30859 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 30859+596841982=FinalSeventhSieve.rough 30110134441897 30757 := to30859

end Tail30110134441897From30757To30859

/- Exact changes for sieve primes 3329 through 3331. -/
open Finset
namespace Tail30110134441897From30859To30881

set_option maxRecDepth 16000 in
private theorem row30869 :
    FinalSeventhSieve.rough 30110134441897 30869+49658391=FinalSeventhSieve.rough 30110134441897 30859 :=
  LargeQuotientSieve.row (p:=30869) (q:=975416581) (s:=31231) (rank:=49660372) (tiny:=3328) (pairs:=1346)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 975416581 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row30871 :
    FinalSeventhSieve.rough 30110134441897 30871+49655234=FinalSeventhSieve.rough 30110134441897 30869 :=
  LargeQuotientSieve.row (p:=30871) (q:=975353388) (s:=31230) (rank:=49657290) (tiny:=3329) (pairs:=1272)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 975353388 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30871 : FinalSeventhSieve.rough 30110134441897 30871+99313625=FinalSeventhSieve.rough 30110134441897 30859 :=
  LargeQuotientSieve.combine row30869 row30871 rfl

set_option maxRecDepth 16000 in
private theorem row30881 :
    FinalSeventhSieve.rough 30110134441897 30881+49639948=FinalSeventhSieve.rough 30110134441897 30871 :=
  LargeQuotientSieve.row (p:=30881) (q:=975037545) (s:=31225) (rank:=49642117) (tiny:=3330) (pairs:=1160)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ975000000To1000000000.count_correct 975037545 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30881 : FinalSeventhSieve.rough 30110134441897 30881+148953573=FinalSeventhSieve.rough 30110134441897 30859 :=
  LargeQuotientSieve.combine to30871 row30881 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 30881+148953573=FinalSeventhSieve.rough 30110134441897 30859 := to30881

end Tail30110134441897From30859To30881

/- Exact changes for the consecutive sieve primes from 30,109 to 30,881. -/
namespace TailSeries30110134441897From30109To30881

private theorem to30341 : FinalSeventhSieve.rough 30110134441897 30341+1216329291=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine Tail30110134441897From30109To30211.change Tail30110134441897From30211To30341.change rfl

private theorem to30493 : FinalSeventhSieve.rough 30110134441897 30493+1820548792=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30341 Tail30110134441897From30341To30493.change rfl

private theorem to30637 : FinalSeventhSieve.rough 30110134441897 30637+2422265222=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30493 Tail30110134441897From30493To30637.change rfl

private theorem to30757 : FinalSeventhSieve.rough 30110134441897 30757+3021472412=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30637 Tail30110134441897From30637To30757.change rfl

private theorem to30859 : FinalSeventhSieve.rough 30110134441897 30859+3618314394=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30757 Tail30110134441897From30757To30859.change rfl

theorem change : FinalSeventhSieve.rough 30110134441897 30881+3767267967=FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine to30859 Tail30110134441897From30859To30881.change rfl

end TailSeries30110134441897From30109To30881

namespace EighthEndpointSieve

theorem final_ninety_four : FinalSeventhSieve.rough 30110134441897 31110 + 4706933946 =
    FinalSeventhSieve.rough 30110134441897 30109 :=
  LargeQuotientSieve.combine TailSeries30110134441897From30109To30881.change final_nineteen rfl

private theorem move_residue (a b : ℕ) (h : a+3767267967=b) : (a%5=2 ↔ b%5=4) := by omega

theorem residue_at_30109 :
    (Nat.primeCounting 30110134441897 % 5 = 3 ↔ FinalSeventhSieve.rough 30110134441897 30109 % 5 = 4) :=
  earlier_residue.trans (move_residue (FinalSeventhSieve.rough 30110134441897 30881)
    (FinalSeventhSieve.rough 30110134441897 30109) TailSeries30110134441897From30109To30881.change)

end EighthEndpointSieve
