import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-825000000-850000000»

/-! Exact changes for sieve primes 1556 through 1567. -/
open Finset
namespace Tail11092009835083From13049To13171

set_option maxRecDepth 16000 in
private theorem row13063 :
    FinalSeventhSieve.rough 11092009835083 13063+46878558=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.row (p:=13063) (q:=849116576) (s:=29139) (rank:=43539003) (tiny:=1555) (pairs:=3341109)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 849116576 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row13093 :
    FinalSeventhSieve.rough 11092009835083 13093+46764240=FinalSeventhSieve.rough 11092009835083 13063 :=
  LargeQuotientSieve.row (p:=13093) (q:=847170994) (s:=29106) (rank:=43444183) (tiny:=1556) (pairs:=3321612)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 847170994 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13093 : FinalSeventhSieve.rough 11092009835083 13093+93642798=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine row13063 row13093 rfl

set_option maxRecDepth 16000 in
private theorem row13099 :
    FinalSeventhSieve.rough 11092009835083 13099+46737603=FinalSeventhSieve.rough 11092009835083 13093 :=
  LargeQuotientSieve.row (p:=13099) (q:=846782947) (s:=29099) (rank:=43425341) (tiny:=1557) (pairs:=3313818)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 846782947 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13099 : FinalSeventhSieve.rough 11092009835083 13099+140380401=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine to13093 row13099 rfl

set_option maxRecDepth 16000 in
private theorem row13103 :
    FinalSeventhSieve.rough 11092009835083 13103+46718198=FinalSeventhSieve.rough 11092009835083 13099 :=
  LargeQuotientSieve.row (p:=13103) (q:=846524447) (s:=29095) (rank:=43412868) (tiny:=1558) (pairs:=3306887)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 846524447 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13103 : FinalSeventhSieve.rough 11092009835083 13103+187098599=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine to13099 row13103 rfl

set_option maxRecDepth 16000 in
private theorem row13109 :
    FinalSeventhSieve.rough 11092009835083 13109+46691565=FinalSeventhSieve.rough 11092009835083 13103 :=
  LargeQuotientSieve.row (p:=13109) (q:=846136992) (s:=29088) (rank:=43394032) (tiny:=1559) (pairs:=3299091)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 846136992 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13109 : FinalSeventhSieve.rough 11092009835083 13109+233790164=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine to13103 row13109 rfl

set_option maxRecDepth 16000 in
private theorem row13121 :
    FinalSeventhSieve.rough 11092009835083 13121+46643178=FinalSeventhSieve.rough 11092009835083 13109 :=
  LargeQuotientSieve.row (p:=13121) (q:=845363145) (s:=29075) (rank:=43356390) (tiny:=1560) (pairs:=3288347)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 845363145 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13121 : FinalSeventhSieve.rough 11092009835083 13121+280433342=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine to13109 row13121 rfl

set_option maxRecDepth 16000 in
private theorem row13127 :
    FinalSeventhSieve.rough 11092009835083 13127+46616577=FinalSeventhSieve.rough 11092009835083 13121 :=
  LargeQuotientSieve.row (p:=13127) (q:=844976752) (s:=29068) (rank:=43337570) (tiny:=1561) (pairs:=3280567)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 844976752 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13127 : FinalSeventhSieve.rough 11092009835083 13127+327049919=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine to13121 row13127 rfl

set_option maxRecDepth 16000 in
private theorem row13147 :
    FinalSeventhSieve.rough 11092009835083 13147+46539751=FinalSeventhSieve.rough 11092009835083 13127 :=
  LargeQuotientSieve.row (p:=13147) (q:=843691323) (s:=29046) (rank:=43275216) (tiny:=1562) (pairs:=3266096)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 843691323 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13147 : FinalSeventhSieve.rough 11092009835083 13147+373589670=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine to13127 row13147 rfl

set_option maxRecDepth 16000 in
private theorem row13151 :
    FinalSeventhSieve.rough 11092009835083 13151+46520505=FinalSeventhSieve.rough 11092009835083 13147 :=
  LargeQuotientSieve.row (p:=13151) (q:=843434707) (s:=29041) (rank:=43262757) (tiny:=1563) (pairs:=3259310)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 843434707 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13151 : FinalSeventhSieve.rough 11092009835083 13151+420110175=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine to13147 row13151 rfl

set_option maxRecDepth 16000 in
private theorem row13159 :
    FinalSeventhSieve.rough 11092009835083 13159+46486770=FinalSeventhSieve.rough 11092009835083 13151 :=
  LargeQuotientSieve.row (p:=13159) (q:=842921942) (s:=29033) (rank:=43237710) (tiny:=1564) (pairs:=3250623)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 842921942 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13159 : FinalSeventhSieve.rough 11092009835083 13159+466596945=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine to13151 row13159 rfl

set_option maxRecDepth 16000 in
private theorem row13163 :
    FinalSeventhSieve.rough 11092009835083 13163+46467378=FinalSeventhSieve.rough 11092009835083 13159 :=
  LargeQuotientSieve.row (p:=13163) (q:=842665793) (s:=29028) (rank:=43225050) (tiny:=1565) (pairs:=3243892)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 842665793 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13163 : FinalSeventhSieve.rough 11092009835083 13163+513064323=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine to13159 row13163 rfl

set_option maxRecDepth 16000 in
private theorem row13171 :
    FinalSeventhSieve.rough 11092009835083 13171+46433949=FinalSeventhSieve.rough 11092009835083 13163 :=
  LargeQuotientSieve.row (p:=13171) (q:=842153962) (s:=29019) (rank:=43200244) (tiny:=1566) (pairs:=3235270)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 842153962 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13171 : FinalSeventhSieve.rough 11092009835083 13171+559498272=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine to13163 row13171 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13171+559498272=FinalSeventhSieve.rough 11092009835083 13049 := to13171

end Tail11092009835083From13049To13171
