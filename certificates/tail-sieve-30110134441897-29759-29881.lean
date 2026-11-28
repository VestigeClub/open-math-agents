import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1000000000-1025000000»

/-! Exact changes for sieve primes 3227 through 3238. -/
open Finset
namespace Tail30110134441897From29759To29881

set_option maxRecDepth 16000 in
private theorem row29761 :
    FinalSeventhSieve.rough 30110134441897 29761+51448880=FinalSeventhSieve.rough 30110134441897 29759 :=
  LargeQuotientSieve.row (p:=29761) (q:=1011731273) (s:=31807) (rank:=51413426) (tiny:=3226) (pairs:=38679)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1011731273 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row29789 :
    FinalSeventhSieve.rough 30110134441897 29789+51401991=FinalSeventhSieve.rough 30110134441897 29761 :=
  LargeQuotientSieve.row (p:=29789) (q:=1010780302) (s:=31792) (rank:=51367553) (tiny:=3227) (pairs:=37664)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1010780302 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29789 : FinalSeventhSieve.rough 30110134441897 29789+102850871=FinalSeventhSieve.rough 30110134441897 29759 :=
  LargeQuotientSieve.combine row29761 row29789 rfl

set_option maxRecDepth 16000 in
private theorem row29803 :
    FinalSeventhSieve.rough 30110134441897 29803+51378387=FinalSeventhSieve.rough 30110134441897 29789 :=
  LargeQuotientSieve.row (p:=29803) (q:=1010305487) (s:=31785) (rank:=51344661) (tiny:=3228) (pairs:=36953)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1010305487 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29803 : FinalSeventhSieve.rough 30110134441897 29803+154229258=FinalSeventhSieve.rough 30110134441897 29759 :=
  LargeQuotientSieve.combine to29789 row29803 rfl

set_option maxRecDepth 16000 in
private theorem row29819 :
    FinalSeventhSieve.rough 30110134441897 29819+51351546=FinalSeventhSieve.rough 30110134441897 29803 :=
  LargeQuotientSieve.row (p:=29819) (q:=1009763387) (s:=31776) (rank:=51318552) (tiny:=3229) (pairs:=36222)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1009763387 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29819 : FinalSeventhSieve.rough 30110134441897 29819+205580804=FinalSeventhSieve.rough 30110134441897 29759 :=
  LargeQuotientSieve.combine to29803 row29819 rfl

set_option maxRecDepth 16000 in
private theorem row29833 :
    FinalSeventhSieve.rough 30110134441897 29833+51327936=FinalSeventhSieve.rough 30110134441897 29819 :=
  LargeQuotientSieve.row (p:=29833) (q:=1009289526) (s:=31769) (rank:=51295624) (tiny:=3230) (pairs:=35541)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1009289526 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29833 : FinalSeventhSieve.rough 30110134441897 29833+256908740=FinalSeventhSieve.rough 30110134441897 29759 :=
  LargeQuotientSieve.combine to29819 row29833 rfl

set_option maxRecDepth 16000 in
private theorem row29837 :
    FinalSeventhSieve.rough 30110134441897 29837+51320945=FinalSeventhSieve.rough 30110134441897 29833 :=
  LargeQuotientSieve.row (p:=29837) (q:=1009154219) (s:=31767) (rank:=51289114) (tiny:=3231) (pairs:=35061)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1009154219 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29837 : FinalSeventhSieve.rough 30110134441897 29837+308229685=FinalSeventhSieve.rough 30110134441897 29759 :=
  LargeQuotientSieve.combine to29833 row29837 rfl

set_option maxRecDepth 16000 in
private theorem row29851 :
    FinalSeventhSieve.rough 30110134441897 29851+51297474=FinalSeventhSieve.rough 30110134441897 29837 :=
  LargeQuotientSieve.row (p:=29851) (q:=1008680930) (s:=31759) (rank:=51266328) (tiny:=3232) (pairs:=34377)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1008680930 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29851 : FinalSeventhSieve.rough 30110134441897 29851+359527159=FinalSeventhSieve.rough 30110134441897 29759 :=
  LargeQuotientSieve.combine to29837 row29851 rfl

set_option maxRecDepth 16000 in
private theorem row29863 :
    FinalSeventhSieve.rough 30110134441897 29863+51277389=FinalSeventhSieve.rough 30110134441897 29851 :=
  LargeQuotientSieve.row (p:=29863) (q:=1008275606) (s:=31753) (rank:=51246864) (tiny:=3233) (pairs:=33757)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1008275606 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29863 : FinalSeventhSieve.rough 30110134441897 29863+410804548=FinalSeventhSieve.rough 30110134441897 29759 :=
  LargeQuotientSieve.combine to29851 row29863 rfl

set_option maxRecDepth 16000 in
private theorem row29867 :
    FinalSeventhSieve.rough 30110134441897 29867+51270361=FinalSeventhSieve.rough 30110134441897 29863 :=
  LargeQuotientSieve.row (p:=29867) (q:=1008140571) (s:=31751) (rank:=51240290) (tiny:=3234) (pairs:=33304)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1008140571 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29867 : FinalSeventhSieve.rough 30110134441897 29867+462074909=FinalSeventhSieve.rough 30110134441897 29759 :=
  LargeQuotientSieve.combine to29863 row29867 rfl

set_option maxRecDepth 16000 in
private theorem row29873 :
    FinalSeventhSieve.rough 30110134441897 29873+51260107=FinalSeventhSieve.rough 30110134441897 29867 :=
  LargeQuotientSieve.row (p:=29873) (q:=1007938085) (s:=31748) (rank:=51230533) (tiny:=3235) (pairs:=32808)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1007938085 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29873 : FinalSeventhSieve.rough 30110134441897 29873+513335016=FinalSeventhSieve.rough 30110134441897 29759 :=
  LargeQuotientSieve.combine to29867 row29873 rfl

set_option maxRecDepth 16000 in
private theorem row29879 :
    FinalSeventhSieve.rough 30110134441897 29879+51249940=FinalSeventhSieve.rough 30110134441897 29873 :=
  LargeQuotientSieve.row (p:=29879) (q:=1007735681) (s:=31744) (rank:=51220865) (tiny:=3236) (pairs:=32310)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1007735681 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29879 : FinalSeventhSieve.rough 30110134441897 29879+564584956=FinalSeventhSieve.rough 30110134441897 29759 :=
  LargeQuotientSieve.combine to29873 row29879 rfl

set_option maxRecDepth 16000 in
private theorem row29881 :
    FinalSeventhSieve.rough 30110134441897 29881+51246326=FinalSeventhSieve.rough 30110134441897 29879 :=
  LargeQuotientSieve.row (p:=29881) (q:=1007668232) (s:=31743) (rank:=51217669) (tiny:=3237) (pairs:=31893)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1007668232 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29881 : FinalSeventhSieve.rough 30110134441897 29881+615831282=FinalSeventhSieve.rough 30110134441897 29759 :=
  LargeQuotientSieve.combine to29879 row29881 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 29881+615831282=FinalSeventhSieve.rough 30110134441897 29759 := to29881

end Tail30110134441897From29759To29881
