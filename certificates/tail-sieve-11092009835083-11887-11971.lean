import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-925000000-950000000»

/-! Exact changes for sieve primes 1425 through 1436. -/
open Finset
namespace Tail11092009835083From11887To11971

set_option maxRecDepth 16000 in
private theorem row11897 :
    FinalSeventhSieve.rough 11092009835083 11897+52330421=FinalSeventhSieve.rough 11092009835083 11887 :=
  LargeQuotientSieve.row (p:=11897) (q:=932336709) (s:=30534) (rank:=47576612) (tiny:=1424) (pairs:=4755232)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 932336709 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row11903 :
    FinalSeventhSieve.rough 11092009835083 11903+52297282=FinalSeventhSieve.rough 11092009835083 11897 :=
  LargeQuotientSieve.row (p:=11903) (q:=931866742) (s:=30526) (rank:=47553941) (tiny:=1425) (pairs:=4744765)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 931866742 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11903 : FinalSeventhSieve.rough 11092009835083 11903+104627703=FinalSeventhSieve.rough 11092009835083 11887 :=
  LargeQuotientSieve.combine row11897 row11903 rfl

set_option maxRecDepth 16000 in
private theorem row11909 :
    FinalSeventhSieve.rough 11092009835083 11909+52264110=FinalSeventhSieve.rough 11092009835083 11903 :=
  LargeQuotientSieve.row (p:=11909) (q:=931397248) (s:=30518) (rank:=47531200) (tiny:=1426) (pairs:=4734335)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 931397248 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11909 : FinalSeventhSieve.rough 11092009835083 11909+156891813=FinalSeventhSieve.rough 11092009835083 11887 :=
  LargeQuotientSieve.combine to11903 row11909 rfl

set_option maxRecDepth 16000 in
private theorem row11923 :
    FinalSeventhSieve.rough 11092009835083 11923+52195217=FinalSeventhSieve.rough 11092009835083 11909 :=
  LargeQuotientSieve.row (p:=11923) (q:=930303601) (s:=30500) (rank:=47478146) (tiny:=1427) (pairs:=4718497)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 930303601 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11923 : FinalSeventhSieve.rough 11092009835083 11923+209087030=FinalSeventhSieve.rough 11092009835083 11887 :=
  LargeQuotientSieve.combine to11909 row11923 rfl

set_option maxRecDepth 16000 in
private theorem row11927 :
    FinalSeventhSieve.rough 11092009835083 11927+52171174=FinalSeventhSieve.rough 11092009835083 11923 :=
  LargeQuotientSieve.row (p:=11927) (q:=929991601) (s:=30495) (rank:=47463054) (tiny:=1428) (pairs:=4709547)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 929991601 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11927 : FinalSeventhSieve.rough 11092009835083 11927+261258204=FinalSeventhSieve.rough 11092009835083 11887 :=
  LargeQuotientSieve.combine to11923 row11927 rfl

set_option maxRecDepth 16000 in
private theorem row11933 :
    FinalSeventhSieve.rough 11092009835083 11933+52138169=FinalSeventhSieve.rough 11092009835083 11927 :=
  LargeQuotientSieve.row (p:=11933) (q:=929523995) (s:=30488) (rank:=47440444) (tiny:=1429) (pairs:=4699153)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 929523995 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11933 : FinalSeventhSieve.rough 11092009835083 11933+313396373=FinalSeventhSieve.rough 11092009835083 11887 :=
  LargeQuotientSieve.combine to11927 row11933 rfl

set_option maxRecDepth 16000 in
private theorem row11939 :
    FinalSeventhSieve.rough 11092009835083 11939+52105302=FinalSeventhSieve.rough 11092009835083 11933 :=
  LargeQuotientSieve.row (p:=11939) (q:=929056858) (s:=30480) (rank:=47417863) (tiny:=1430) (pairs:=4688868)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 929056858 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11939 : FinalSeventhSieve.rough 11092009835083 11939+365501675=FinalSeventhSieve.rough 11092009835083 11887 :=
  LargeQuotientSieve.combine to11933 row11939 rfl

set_option maxRecDepth 16000 in
private theorem row11941 :
    FinalSeventhSieve.rough 11092009835083 11941+52090248=FinalSeventhSieve.rough 11092009835083 11939 :=
  LargeQuotientSieve.row (p:=11941) (q:=928901250) (s:=30477) (rank:=47410401) (tiny:=1431) (pairs:=4681277)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 928901250 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11941 : FinalSeventhSieve.rough 11092009835083 11941+417591923=FinalSeventhSieve.rough 11092009835083 11887 :=
  LargeQuotientSieve.combine to11939 row11941 rfl

set_option maxRecDepth 16000 in
private theorem row11953 :
    FinalSeventhSieve.rough 11092009835083 11953+52030675=FinalSeventhSieve.rough 11092009835083 11941 :=
  LargeQuotientSieve.row (p:=11953) (q:=927968696) (s:=30462) (rank:=47365318) (tiny:=1432) (pairs:=4666788)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 927968696 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11953 : FinalSeventhSieve.rough 11092009835083 11953+469622598=FinalSeventhSieve.rough 11092009835083 11887 :=
  LargeQuotientSieve.combine to11941 row11953 rfl

set_option maxRecDepth 16000 in
private theorem row11959 :
    FinalSeventhSieve.rough 11092009835083 11959+51997999=FinalSeventhSieve.rough 11092009835083 11953 :=
  LargeQuotientSieve.row (p:=11959) (q:=927503121) (s:=30454) (rank:=47342930) (tiny:=1433) (pairs:=4656501)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 927503121 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11959 : FinalSeventhSieve.rough 11092009835083 11959+521620597=FinalSeventhSieve.rough 11092009835083 11887 :=
  LargeQuotientSieve.combine to11953 row11959 rfl

set_option maxRecDepth 16000 in
private theorem row11969 :
    FinalSeventhSieve.rough 11092009835083 11969+51947511=FinalSeventhSieve.rough 11092009835083 11959 :=
  LargeQuotientSieve.row (p:=11969) (q:=926728200) (s:=30442) (rank:=47305406) (tiny:=1434) (pairs:=4643538)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 926728200 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11969 : FinalSeventhSieve.rough 11092009835083 11969+573568108=FinalSeventhSieve.rough 11092009835083 11887 :=
  LargeQuotientSieve.combine to11959 row11969 rfl

set_option maxRecDepth 16000 in
private theorem row11971 :
    FinalSeventhSieve.rough 11092009835083 11971+51932533=FinalSeventhSieve.rough 11092009835083 11969 :=
  LargeQuotientSieve.row (p:=11971) (q:=926573371) (s:=30439) (rank:=47297954) (tiny:=1435) (pairs:=4636013)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ925000000To950000000.count_correct 926573371 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to11971 : FinalSeventhSieve.rough 11092009835083 11971+625500641=FinalSeventhSieve.rough 11092009835083 11887 :=
  LargeQuotientSieve.combine to11969 row11971 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 11971+625500641=FinalSeventhSieve.rough 11092009835083 11887 := to11971

end Tail11092009835083From11887To11971
