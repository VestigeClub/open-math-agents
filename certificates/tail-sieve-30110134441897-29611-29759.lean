import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1000000000-1025000000»

/-! Exact changes for sieve primes 3215 through 3226. -/
open Finset
namespace Tail30110134441897From29611To29759

set_option maxRecDepth 16000 in
private theorem row29629 :
    FinalSeventhSieve.rough 30110134441897 29629+51674631=FinalSeventhSieve.rough 30110134441897 29611 :=
  LargeQuotientSieve.row (p:=29629) (q:=1016238632) (s:=31878) (rank:=51631048) (tiny:=3214) (pairs:=46796)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1016238632 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row29633 :
    FinalSeventhSieve.rough 30110134441897 29633+51667466=FinalSeventhSieve.rough 30110134441897 29629 :=
  LargeQuotientSieve.row (p:=29633) (q:=1016101455) (s:=31876) (rank:=51624427) (tiny:=3215) (pairs:=46253)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1016101455 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29633 : FinalSeventhSieve.rough 30110134441897 29633+103342097=FinalSeventhSieve.rough 30110134441897 29611 :=
  LargeQuotientSieve.combine row29629 row29633 rfl

set_option maxRecDepth 16000 in
private theorem row29641 :
    FinalSeventhSieve.rough 30110134441897 29641+51653578=FinalSeventhSieve.rough 30110134441897 29633 :=
  LargeQuotientSieve.row (p:=29641) (q:=1015827213) (s:=31872) (rank:=51611182) (tiny:=3216) (pairs:=45611)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1015827213 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29641 : FinalSeventhSieve.rough 30110134441897 29641+154995675=FinalSeventhSieve.rough 30110134441897 29611 :=
  LargeQuotientSieve.combine to29633 row29641 rfl

set_option maxRecDepth 16000 in
private theorem row29663 :
    FinalSeventhSieve.rough 30110134441897 29663+51616238=FinalSeventhSieve.rough 30110134441897 29641 :=
  LargeQuotientSieve.row (p:=29663) (q:=1015073810) (s:=31860) (rank:=51574800) (tiny:=3217) (pairs:=44654)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1015073810 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29663 : FinalSeventhSieve.rough 30110134441897 29663+206611913=FinalSeventhSieve.rough 30110134441897 29611 :=
  LargeQuotientSieve.combine to29641 row29663 rfl

set_option maxRecDepth 16000 in
private theorem row29669 :
    FinalSeventhSieve.rough 30110134441897 29669+51605724=FinalSeventhSieve.rough 30110134441897 29663 :=
  LargeQuotientSieve.row (p:=29669) (q:=1014868530) (s:=31857) (rank:=51564852) (tiny:=3218) (pairs:=44089)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1014868530 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29669 : FinalSeventhSieve.rough 30110134441897 29669+258217637=FinalSeventhSieve.rough 30110134441897 29611 :=
  LargeQuotientSieve.combine to29663 row29669 rfl

set_option maxRecDepth 16000 in
private theorem row29671 :
    FinalSeventhSieve.rough 30110134441897 29671+51601932=FinalSeventhSieve.rough 30110134441897 29669 :=
  LargeQuotientSieve.row (p:=29671) (q:=1014800122) (s:=31855) (rank:=51561542) (tiny:=3219) (pairs:=43608)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1014800122 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29671 : FinalSeventhSieve.rough 30110134441897 29671+309819569=FinalSeventhSieve.rough 30110134441897 29611 :=
  LargeQuotientSieve.combine to29669 row29671 rfl

set_option maxRecDepth 16000 in
private theorem row29683 :
    FinalSeventhSieve.rough 30110134441897 29683+51581350=FinalSeventhSieve.rough 30110134441897 29671 :=
  LargeQuotientSieve.row (p:=29683) (q:=1014389867) (s:=31849) (rank:=51541663) (tiny:=3220) (pairs:=42906)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1014389867 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29683 : FinalSeventhSieve.rough 30110134441897 29683+361400919=FinalSeventhSieve.rough 30110134441897 29611 :=
  LargeQuotientSieve.combine to29671 row29683 rfl

set_option maxRecDepth 16000 in
private theorem row29717 :
    FinalSeventhSieve.rough 30110134441897 29717+51524240=FinalSeventhSieve.rough 30110134441897 29683 :=
  LargeQuotientSieve.row (p:=29717) (q:=1013229277) (s:=31831) (rank:=51485714) (tiny:=3221) (pairs:=41746)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1013229277 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29717 : FinalSeventhSieve.rough 30110134441897 29717+412925159=FinalSeventhSieve.rough 30110134441897 29611 :=
  LargeQuotientSieve.combine to29683 row29717 rfl

set_option maxRecDepth 16000 in
private theorem row29723 :
    FinalSeventhSieve.rough 30110134441897 29723+51513927=FinalSeventhSieve.rough 30110134441897 29717 :=
  LargeQuotientSieve.row (p:=29723) (q:=1013024743) (s:=31828) (rank:=51475950) (tiny:=3222) (pairs:=41198)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1013024743 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29723 : FinalSeventhSieve.rough 30110134441897 29723+464439086=FinalSeventhSieve.rough 30110134441897 29611 :=
  LargeQuotientSieve.combine to29717 row29723 rfl

set_option maxRecDepth 16000 in
private theorem row29741 :
    FinalSeventhSieve.rough 30110134441897 29741+51483520=FinalSeventhSieve.rough 30110134441897 29723 :=
  LargeQuotientSieve.row (p:=29741) (q:=1012411635) (s:=31818) (rank:=51446364) (tiny:=3223) (pairs:=40378)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1012411635 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29741 : FinalSeventhSieve.rough 30110134441897 29741+515922606=FinalSeventhSieve.rough 30110134441897 29611 :=
  LargeQuotientSieve.combine to29723 row29741 rfl

set_option maxRecDepth 16000 in
private theorem row29753 :
    FinalSeventhSieve.rough 30110134441897 29753+51463173=FinalSeventhSieve.rough 30110134441897 29741 :=
  LargeQuotientSieve.row (p:=29753) (q:=1012003308) (s:=31811) (rank:=51426714) (tiny:=3224) (pairs:=39682)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1012003308 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29753 : FinalSeventhSieve.rough 30110134441897 29753+567385779=FinalSeventhSieve.rough 30110134441897 29611 :=
  LargeQuotientSieve.combine to29741 row29753 rfl

set_option maxRecDepth 16000 in
private theorem row29759 :
    FinalSeventhSieve.rough 30110134441897 29759+51452667=FinalSeventhSieve.rough 30110134441897 29753 :=
  LargeQuotientSieve.row (p:=29759) (q:=1011799268) (s:=31808) (rank:=51416760) (tiny:=3225) (pairs:=39131)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1000000000To1025000000.count_correct 1011799268 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to29759 : FinalSeventhSieve.rough 30110134441897 29759+618838446=FinalSeventhSieve.rough 30110134441897 29611 :=
  LargeQuotientSieve.combine to29753 row29759 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 29759+618838446=FinalSeventhSieve.rough 30110134441897 29611 := to29759

end Tail30110134441897From29611To29759
