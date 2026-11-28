import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1025000000-1050000000»

/-! Exact changes for sieve primes 3173 through 3184. -/
open Finset
namespace Tail30110134441897From29179To29303

set_option maxRecDepth 16000 in
private theorem row29191 :
    FinalSeventhSieve.rough 30110134441897 29191+52443568=FinalSeventhSieve.rough 30110134441897 29179 :=
  LargeQuotientSieve.row (p:=29191) (q:=1031486911) (s:=32116) (rank:=52365966) (tiny:=3172) (pairs:=80773)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1031486911 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row29201 :
    FinalSeventhSieve.rough 30110134441897 29201+52425707=FinalSeventhSieve.rough 30110134441897 29191 :=
  LargeQuotientSieve.row (p:=29201) (q:=1031133674) (s:=32111) (rank:=52349020) (tiny:=3173) (pairs:=79859)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1031133674 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29201 : FinalSeventhSieve.rough 30110134441897 29201+104869275=FinalSeventhSieve.rough 30110134441897 29179 :=
  LargeQuotientSieve.combine row29191 row29201 rfl

set_option maxRecDepth 16000 in
private theorem row29207 :
    FinalSeventhSieve.rough 30110134441897 29207+52414746=FinalSeventhSieve.rough 30110134441897 29201 :=
  LargeQuotientSieve.row (p:=29207) (q:=1030921848) (s:=32107) (rank:=52338846) (tiny:=3174) (pairs:=79073)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1030921848 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29207 : FinalSeventhSieve.rough 30110134441897 29207+157284021=FinalSeventhSieve.rough 30110134441897 29179 :=
  LargeQuotientSieve.combine to29201 row29207 rfl

set_option maxRecDepth 16000 in
private theorem row29209 :
    FinalSeventhSieve.rough 30110134441897 29209+52410659=FinalSeventhSieve.rough 30110134441897 29207 :=
  LargeQuotientSieve.row (p:=29209) (q:=1030851259) (s:=32106) (rank:=52335412) (tiny:=3175) (pairs:=78421)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1030851259 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29209 : FinalSeventhSieve.rough 30110134441897 29209+209694680=FinalSeventhSieve.rough 30110134441897 29179 :=
  LargeQuotientSieve.combine to29207 row29209 rfl

set_option maxRecDepth 16000 in
private theorem row29221 :
    FinalSeventhSieve.rough 30110134441897 29221+52389289=FinalSeventhSieve.rough 30110134441897 29209 :=
  LargeQuotientSieve.row (p:=29221) (q:=1030427926) (s:=32100) (rank:=52314986) (tiny:=3176) (pairs:=77478)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1030427926 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29221 : FinalSeventhSieve.rough 30110134441897 29221+262083969=FinalSeventhSieve.rough 30110134441897 29179 :=
  LargeQuotientSieve.combine to29209 row29221 rfl

set_option maxRecDepth 16000 in
private theorem row29231 :
    FinalSeventhSieve.rough 30110134441897 29231+52371375=FinalSeventhSieve.rough 30110134441897 29221 :=
  LargeQuotientSieve.row (p:=29231) (q:=1030075414) (s:=32094) (rank:=52297959) (tiny:=3177) (pairs:=76592)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1030075414 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29231 : FinalSeventhSieve.rough 30110134441897 29231+314455344=FinalSeventhSieve.rough 30110134441897 29179 :=
  LargeQuotientSieve.combine to29221 row29231 rfl

set_option maxRecDepth 16000 in
private theorem row29243 :
    FinalSeventhSieve.rough 30110134441897 29243+52350128=FinalSeventhSieve.rough 30110134441897 29231 :=
  LargeQuotientSieve.row (p:=29243) (q:=1029652718) (s:=32088) (rank:=52277656) (tiny:=3178) (pairs:=75649)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1029652718 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29243 : FinalSeventhSieve.rough 30110134441897 29243+366805472=FinalSeventhSieve.rough 30110134441897 29179 :=
  LargeQuotientSieve.combine to29231 row29243 rfl

set_option maxRecDepth 16000 in
private theorem row29251 :
    FinalSeventhSieve.rough 30110134441897 29251+52335707=FinalSeventhSieve.rough 30110134441897 29243 :=
  LargeQuotientSieve.row (p:=29251) (q:=1029371113) (s:=32083) (rank:=52264044) (tiny:=3179) (pairs:=74841)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1029371113 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29251 : FinalSeventhSieve.rough 30110134441897 29251+419141179=FinalSeventhSieve.rough 30110134441897 29179 :=
  LargeQuotientSieve.combine to29243 row29251 rfl

set_option maxRecDepth 16000 in
private theorem row29269 :
    FinalSeventhSieve.rough 30110134441897 29269+52303946=FinalSeventhSieve.rough 30110134441897 29251 :=
  LargeQuotientSieve.row (p:=29269) (q:=1028738065) (s:=32073) (rank:=52233401) (tiny:=3180) (pairs:=73724)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1028738065 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29269 : FinalSeventhSieve.rough 30110134441897 29269+471445125=FinalSeventhSieve.rough 30110134441897 29179 :=
  LargeQuotientSieve.combine to29251 row29269 rfl

set_option maxRecDepth 16000 in
private theorem row29287 :
    FinalSeventhSieve.rough 30110134441897 29287+52272323=FinalSeventhSieve.rough 30110134441897 29269 :=
  LargeQuotientSieve.row (p:=29287) (q:=1028105795) (s:=32064) (rank:=52202872) (tiny:=3181) (pairs:=72631)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1028105795 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29287 : FinalSeventhSieve.rough 30110134441897 29287+523717448=FinalSeventhSieve.rough 30110134441897 29179 :=
  LargeQuotientSieve.combine to29269 row29287 rfl

set_option maxRecDepth 16000 in
private theorem row29297 :
    FinalSeventhSieve.rough 30110134441897 29297+52254648=FinalSeventhSieve.rough 30110134441897 29287 :=
  LargeQuotientSieve.row (p:=29297) (q:=1027754870) (s:=32058) (rank:=52186058) (tiny:=3182) (pairs:=71771)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1027754870 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29297 : FinalSeventhSieve.rough 30110134441897 29297+575972096=FinalSeventhSieve.rough 30110134441897 29179 :=
  LargeQuotientSieve.combine to29287 row29297 rfl

set_option maxRecDepth 16000 in
private theorem row29303 :
    FinalSeventhSieve.rough 30110134441897 29303+52243802=FinalSeventhSieve.rough 30110134441897 29297 :=
  LargeQuotientSieve.row (p:=29303) (q:=1027544430) (s:=32055) (rank:=52175928) (tiny:=3183) (pairs:=71056)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1027544430 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29303 : FinalSeventhSieve.rough 30110134441897 29303+628215898=FinalSeventhSieve.rough 30110134441897 29179 :=
  LargeQuotientSieve.combine to29297 row29303 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 29303+628215898=FinalSeventhSieve.rough 30110134441897 29179 := to29303

end Tail30110134441897From29179To29303
