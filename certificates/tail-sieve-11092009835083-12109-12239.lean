import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-900000000-925000000»

/-! Exact changes for sieve primes 1451 through 1462. -/
open Finset
namespace Tail11092009835083From12109To12239

set_option maxRecDepth 16000 in
private theorem row12113 :
    FinalSeventhSieve.rough 11092009835083 12113+51220895=FinalSeventhSieve.rough 11092009835083 12109 :=
  LargeQuotientSieve.row (p:=12113) (q:=915711205) (s:=30260) (rank:=46771645) (tiny:=1450) (pairs:=4450699)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 915711205 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row12119 :
    FinalSeventhSieve.rough 11092009835083 12119+51189043=FinalSeventhSieve.rough 11092009835083 12113 :=
  LargeQuotientSieve.row (p:=12119) (q:=915257845) (s:=30253) (rank:=46749637) (tiny:=1451) (pairs:=4440856)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 915257845 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12119 : FinalSeventhSieve.rough 11092009835083 12119+102409938=FinalSeventhSieve.rough 11092009835083 12109 :=
  LargeQuotientSieve.combine row12113 row12119 rfl

set_option maxRecDepth 16000 in
private theorem row12143 :
    FinalSeventhSieve.rough 11092009835083 12143+51079796=FinalSeventhSieve.rough 11092009835083 12119 :=
  LargeQuotientSieve.row (p:=12143) (q:=913448887) (s:=30223) (rank:=46661846) (tiny:=1452) (pairs:=4419401)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 913448887 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12143 : FinalSeventhSieve.rough 11092009835083 12143+153489734=FinalSeventhSieve.rough 11092009835083 12109 :=
  LargeQuotientSieve.combine to12119 row12143 rfl

set_option maxRecDepth 16000 in
private theorem row12149 :
    FinalSeventhSieve.rough 11092009835083 12149+51048361=FinalSeventhSieve.rough 11092009835083 12143 :=
  LargeQuotientSieve.row (p:=12149) (q:=912997764) (s:=30215) (rank:=46640218) (tiny:=1453) (pairs:=4409595)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 912997764 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12149 : FinalSeventhSieve.rough 11092009835083 12149+204538095=FinalSeventhSieve.rough 11092009835083 12109 :=
  LargeQuotientSieve.combine to12143 row12149 rfl

set_option maxRecDepth 16000 in
private theorem row12157 :
    FinalSeventhSieve.rough 11092009835083 12157+51008040=FinalSeventhSieve.rough 11092009835083 12149 :=
  LargeQuotientSieve.row (p:=12157) (q:=912396959) (s:=30205) (rank:=46610917) (tiny:=1454) (pairs:=4398576)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 912396959 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12157 : FinalSeventhSieve.rough 11092009835083 12157+255546135=FinalSeventhSieve.rough 11092009835083 12109 :=
  LargeQuotientSieve.combine to12149 row12157 rfl

set_option maxRecDepth 16000 in
private theorem row12161 :
    FinalSeventhSieve.rough 11092009835083 12161+50984985=FinalSeventhSieve.rough 11092009835083 12157 :=
  LargeQuotientSieve.row (p:=12161) (q:=912096853) (s:=30200) (rank:=46596418) (tiny:=1455) (pairs:=4390021)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 912096853 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12161 : FinalSeventhSieve.rough 11092009835083 12161+306531120=FinalSeventhSieve.rough 11092009835083 12109 :=
  LargeQuotientSieve.combine to12157 row12161 rfl

set_option maxRecDepth 16000 in
private theorem row12163 :
    FinalSeventhSieve.rough 11092009835083 12163+50970445=FinalSeventhSieve.rough 11092009835083 12161 :=
  LargeQuotientSieve.row (p:=12163) (q:=911946874) (s:=30198) (rank:=46589070) (tiny:=1456) (pairs:=4382830)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 911946874 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12163 : FinalSeventhSieve.rough 11092009835083 12163+357501565=FinalSeventhSieve.rough 11092009835083 12109 :=
  LargeQuotientSieve.combine to12161 row12163 rfl

set_option maxRecDepth 16000 in
private theorem row12197 :
    FinalSeventhSieve.rough 11092009835083 12197+50819397=FinalSeventhSieve.rough 11092009835083 12163 :=
  LargeQuotientSieve.row (p:=12197) (q:=909404758) (s:=30156) (rank:=46465600) (tiny:=1457) (pairs:=4355253)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 909404758 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12197 : FinalSeventhSieve.rough 11092009835083 12197+408320962=FinalSeventhSieve.rough 11092009835083 12109 :=
  LargeQuotientSieve.combine to12163 row12197 rfl

set_option maxRecDepth 16000 in
private theorem row12203 :
    FinalSeventhSieve.rough 11092009835083 12203+50787815=FinalSeventhSieve.rough 11092009835083 12197 :=
  LargeQuotientSieve.row (p:=12203) (q:=908957619) (s:=30148) (rank:=46443665) (tiny:=1458) (pairs:=4345607)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 908957619 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12203 : FinalSeventhSieve.rough 11092009835083 12203+459108777=FinalSeventhSieve.rough 11092009835083 12109 :=
  LargeQuotientSieve.combine to12197 row12203 rfl

set_option maxRecDepth 16000 in
private theorem row12211 :
    FinalSeventhSieve.rough 11092009835083 12211+50748026=FinalSeventhSieve.rough 11092009835083 12203 :=
  LargeQuotientSieve.row (p:=12211) (q:=908362118) (s:=30139) (rank:=46414830) (tiny:=1459) (pairs:=4334654)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 908362118 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12211 : FinalSeventhSieve.rough 11092009835083 12211+509856803=FinalSeventhSieve.rough 11092009835083 12109 :=
  LargeQuotientSieve.combine to12203 row12211 rfl

set_option maxRecDepth 16000 in
private theorem row12227 :
    FinalSeventhSieve.rough 11092009835083 12227+50674515=FinalSeventhSieve.rough 11092009835083 12211 :=
  LargeQuotientSieve.row (p:=12227) (q:=907173455) (s:=30119) (rank:=46357255) (tiny:=1460) (pairs:=4318719)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 907173455 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12227 : FinalSeventhSieve.rough 11092009835083 12227+560531318=FinalSeventhSieve.rough 11092009835083 12109 :=
  LargeQuotientSieve.combine to12211 row12227 rfl

set_option maxRecDepth 16000 in
private theorem row12239 :
    FinalSeventhSieve.rough 11092009835083 12239+50617825=FinalSeventhSieve.rough 11092009835083 12227 :=
  LargeQuotientSieve.row (p:=12239) (q:=906283996) (s:=30104) (rank:=46313921) (tiny:=1461) (pairs:=4305364)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 906283996 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12239 : FinalSeventhSieve.rough 11092009835083 12239+611149143=FinalSeventhSieve.rough 11092009835083 12109 :=
  LargeQuotientSieve.combine to12227 row12239 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 12239+611149143=FinalSeventhSieve.rough 11092009835083 12109 := to12239

end Tail11092009835083From12109To12239
