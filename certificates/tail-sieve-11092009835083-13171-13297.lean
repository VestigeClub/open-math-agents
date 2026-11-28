import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-825000000-850000000»

/-! Exact changes for sieve primes 1568 through 1579. -/
open Finset
namespace Tail11092009835083From13171To13297

set_option maxRecDepth 16000 in
private theorem row13177 :
    FinalSeventhSieve.rough 11092009835083 13177+46407507=FinalSeventhSieve.rough 11092009835083 13171 :=
  LargeQuotientSieve.row (p:=13177) (q:=841770496) (s:=29013) (rank:=43181436) (tiny:=1567) (pairs:=3227637)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 841770496 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row13183 :
    FinalSeventhSieve.rough 11092009835083 13183+46381076=FinalSeventhSieve.rough 11092009835083 13177 :=
  LargeQuotientSieve.row (p:=13183) (q:=841387380) (s:=29006) (rank:=43162722) (tiny:=1568) (pairs:=3219921)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 841387380 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13183 : FinalSeventhSieve.rough 11092009835083 13183+92788583=FinalSeventhSieve.rough 11092009835083 13171 :=
  LargeQuotientSieve.combine row13177 row13183 rfl

set_option maxRecDepth 16000 in
private theorem row13187 :
    FinalSeventhSieve.rough 11092009835083 13187+46362045=FinalSeventhSieve.rough 11092009835083 13183 :=
  LargeQuotientSieve.row (p:=13187) (q:=841132163) (s:=29002) (rank:=43150492) (tiny:=1569) (pairs:=3213121)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 841132163 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13187 : FinalSeventhSieve.rough 11092009835083 13187+139150628=FinalSeventhSieve.rough 11092009835083 13171 :=
  LargeQuotientSieve.combine to13183 row13187 rfl

set_option maxRecDepth 16000 in
private theorem row13217 :
    FinalSeventhSieve.rough 11092009835083 13217+46250205=FinalSeventhSieve.rough 11092009835083 13187 :=
  LargeQuotientSieve.row (p:=13217) (q:=839222957) (s:=28969) (rank:=43057495) (tiny:=1570) (pairs:=3194279)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 839222957 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13217 : FinalSeventhSieve.rough 11092009835083 13217+185400833=FinalSeventhSieve.rough 11092009835083 13171 :=
  LargeQuotientSieve.combine to13187 row13217 rfl

set_option maxRecDepth 16000 in
private theorem row13219 :
    FinalSeventhSieve.rough 11092009835083 13219+46238287=FinalSeventhSieve.rough 11092009835083 13217 :=
  LargeQuotientSieve.row (p:=13219) (q:=839095985) (s:=28967) (rank:=43051294) (tiny:=1571) (pairs:=3188563)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 839095985 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13219 : FinalSeventhSieve.rough 11092009835083 13219+231639120=FinalSeventhSieve.rough 11092009835083 13171 :=
  LargeQuotientSieve.combine to13217 row13219 rfl

set_option maxRecDepth 16000 in
private theorem row13229 :
    FinalSeventhSieve.rough 11092009835083 13229+46198050=FinalSeventhSieve.rough 11092009835083 13219 :=
  LargeQuotientSieve.row (p:=13229) (q:=838461700) (s:=28956) (rank:=43020584) (tiny:=1572) (pairs:=3179037)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 838461700 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13229 : FinalSeventhSieve.rough 11092009835083 13229+277837170=FinalSeventhSieve.rough 11092009835083 13171 :=
  LargeQuotientSieve.combine to13219 row13229 rfl

set_option maxRecDepth 16000 in
private theorem row13241 :
    FinalSeventhSieve.rough 11092009835083 13241+46150506=FinalSeventhSieve.rough 11092009835083 13229 :=
  LargeQuotientSieve.row (p:=13241) (q:=837701822) (s:=28943) (rank:=42983370) (tiny:=1573) (pairs:=3168708)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 837701822 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13241 : FinalSeventhSieve.rough 11092009835083 13241+323987676=FinalSeventhSieve.rough 11092009835083 13171 :=
  LargeQuotientSieve.combine to13229 row13241 rfl

set_option maxRecDepth 16000 in
private theorem row13249 :
    FinalSeventhSieve.rough 11092009835083 13249+46117400=FinalSeventhSieve.rough 11092009835083 13241 :=
  LargeQuotientSieve.row (p:=13249) (q:=837196002) (s:=28934) (rank:=42958764) (tiny:=1574) (pairs:=3160209)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 837196002 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13249 : FinalSeventhSieve.rough 11092009835083 13249+370105076=FinalSeventhSieve.rough 11092009835083 13171 :=
  LargeQuotientSieve.combine to13241 row13249 rfl

set_option maxRecDepth 16000 in
private theorem row13259 :
    FinalSeventhSieve.rough 11092009835083 13259+46077284=FinalSeventhSieve.rough 11092009835083 13249 :=
  LargeQuotientSieve.row (p:=13259) (q:=836564585) (s:=28923) (rank:=42928036) (tiny:=1575) (pairs:=3150822)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 836564585 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13259 : FinalSeventhSieve.rough 11092009835083 13259+416182360=FinalSeventhSieve.rough 11092009835083 13171 :=
  LargeQuotientSieve.combine to13249 row13259 rfl

set_option maxRecDepth 16000 in
private theorem row13267 :
    FinalSeventhSieve.rough 11092009835083 13267+46044260=FinalSeventhSieve.rough 11092009835083 13259 :=
  LargeQuotientSieve.row (p:=13267) (q:=836060136) (s:=28914) (rank:=42903506) (tiny:=1576) (pairs:=3142329)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 836060136 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13267 : FinalSeventhSieve.rough 11092009835083 13267+462226620=FinalSeventhSieve.rough 11092009835083 13171 :=
  LargeQuotientSieve.combine to13259 row13267 rfl

set_option maxRecDepth 16000 in
private theorem row13291 :
    FinalSeventhSieve.rough 11092009835083 13291+45954939=FinalSeventhSieve.rough 11092009835083 13267 :=
  LargeQuotientSieve.row (p:=13291) (q:=834550435) (s:=28888) (rank:=42830054) (tiny:=1577) (pairs:=3126461)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 834550435 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13291 : FinalSeventhSieve.rough 11092009835083 13291+508181559=FinalSeventhSieve.rough 11092009835083 13171 :=
  LargeQuotientSieve.combine to13267 row13291 rfl

set_option maxRecDepth 16000 in
private theorem row13297 :
    FinalSeventhSieve.rough 11092009835083 13297+45929116=FinalSeventhSieve.rough 11092009835083 13291 :=
  LargeQuotientSieve.row (p:=13297) (q:=834173861) (s:=28882) (rank:=42811680) (tiny:=1578) (pairs:=3119013)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 834173861 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13297 : FinalSeventhSieve.rough 11092009835083 13297+554110675=FinalSeventhSieve.rough 11092009835083 13171 :=
  LargeQuotientSieve.combine to13291 row13297 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13297+554110675=FinalSeventhSieve.rough 11092009835083 13171 := to13297

end Tail11092009835083From13171To13297
