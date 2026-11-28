import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-850000000-875000000»

/-! Exact changes for sieve primes 1527 through 1538. -/
open Finset
namespace Tail11092009835083From12799To12917

set_option maxRecDepth 16000 in
private theorem row12809 :
    FinalSeventhSieve.rough 11092009835083 12809+47973323=FinalSeventhSieve.rough 11092009835083 12799 :=
  LargeQuotientSieve.row (p:=12809) (q:=865954394) (s:=29427) (rank:=44357227) (tiny:=1526) (pairs:=3617621)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 865954394 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row12821 :
    FinalSeventhSieve.rough 11092009835083 12821+47922355=FinalSeventhSieve.rough 11092009835083 12809 :=
  LargeQuotientSieve.row (p:=12821) (q:=865143891) (s:=29413) (rank:=44317862) (tiny:=1527) (pairs:=3606019)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 865143891 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12821 : FinalSeventhSieve.rough 11092009835083 12821+95895678=FinalSeventhSieve.rough 11092009835083 12799 :=
  LargeQuotientSieve.combine row12809 row12821 rfl

set_option maxRecDepth 16000 in
private theorem row12823 :
    FinalSeventhSieve.rough 11092009835083 12823+47909531=FinalSeventhSieve.rough 11092009835083 12821 :=
  LargeQuotientSieve.row (p:=12823) (q:=865008955) (s:=29411) (rank:=44311261) (tiny:=1528) (pairs:=3599797)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 865008955 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12823 : FinalSeventhSieve.rough 11092009835083 12823+143805209=FinalSeventhSieve.rough 11092009835083 12799 :=
  LargeQuotientSieve.combine to12821 row12823 rfl

set_option maxRecDepth 16000 in
private theorem row12829 :
    FinalSeventhSieve.rough 11092009835083 12829+47881549=FinalSeventhSieve.rough 11092009835083 12823 :=
  LargeQuotientSieve.row (p:=12829) (q:=864604399) (s:=29404) (rank:=44291651) (tiny:=1529) (pairs:=3591426)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 864604399 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12829 : FinalSeventhSieve.rough 11092009835083 12829+191686758=FinalSeventhSieve.rough 11092009835083 12799 :=
  LargeQuotientSieve.combine to12823 row12829 rfl

set_option maxRecDepth 16000 in
private theorem row12841 :
    FinalSeventhSieve.rough 11092009835083 12841+47830615=FinalSeventhSieve.rough 11092009835083 12829 :=
  LargeQuotientSieve.row (p:=12841) (q:=863796420) (s:=29390) (rank:=44252207) (tiny:=1530) (pairs:=3579937)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 863796420 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12841 : FinalSeventhSieve.rough 11092009835083 12841+239517373=FinalSeventhSieve.rough 11092009835083 12799 :=
  LargeQuotientSieve.combine to12829 row12841 rfl

set_option maxRecDepth 16000 in
private theorem row12853 :
    FinalSeventhSieve.rough 11092009835083 12853+47780008=FinalSeventhSieve.rough 11092009835083 12841 :=
  LargeQuotientSieve.row (p:=12853) (q:=862989950) (s:=29376) (rank:=44213055) (tiny:=1531) (pairs:=3568483)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 862989950 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12853 : FinalSeventhSieve.rough 11092009835083 12853+287297381=FinalSeventhSieve.rough 11092009835083 12799 :=
  LargeQuotientSieve.combine to12841 row12853 rfl

set_option maxRecDepth 16000 in
private theorem row12889 :
    FinalSeventhSieve.rough 11092009835083 12889+47639112=FinalSeventhSieve.rough 11092009835083 12853 :=
  LargeQuotientSieve.row (p:=12889) (q:=860579551) (s:=29335) (rank:=44095998) (tiny:=1532) (pairs:=3544645)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 860579551 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12889 : FinalSeventhSieve.rough 11092009835083 12889+334936493=FinalSeventhSieve.rough 11092009835083 12799 :=
  LargeQuotientSieve.combine to12853 row12889 rfl

set_option maxRecDepth 16000 in
private theorem row12893 :
    FinalSeventhSieve.rough 11092009835083 12893+47618931=FinalSeventhSieve.rough 11092009835083 12889 :=
  LargeQuotientSieve.row (p:=12893) (q:=860312559) (s:=29331) (rank:=44082972) (tiny:=1533) (pairs:=3537491)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 860312559 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12893 : FinalSeventhSieve.rough 11092009835083 12893+382555424=FinalSeventhSieve.rough 11092009835083 12799 :=
  LargeQuotientSieve.combine to12889 row12893 rfl

set_option maxRecDepth 16000 in
private theorem row12899 :
    FinalSeventhSieve.rough 11092009835083 12899+47591317=FinalSeventhSieve.rough 11092009835083 12893 :=
  LargeQuotientSieve.row (p:=12899) (q:=859912383) (s:=29324) (rank:=44063594) (tiny:=1534) (pairs:=3529256)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 859912383 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12899 : FinalSeventhSieve.rough 11092009835083 12899+430146741=FinalSeventhSieve.rough 11092009835083 12799 :=
  LargeQuotientSieve.combine to12893 row12899 rfl

set_option maxRecDepth 16000 in
private theorem row12907 :
    FinalSeventhSieve.rough 11092009835083 12907+47556340=FinalSeventhSieve.rough 11092009835083 12899 :=
  LargeQuotientSieve.row (p:=12907) (q:=859379393) (s:=29315) (rank:=44037825) (tiny:=1535) (pairs:=3520049)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 859379393 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12907 : FinalSeventhSieve.rough 11092009835083 12907+477703081=FinalSeventhSieve.rough 11092009835083 12799 :=
  LargeQuotientSieve.combine to12899 row12907 rfl

set_option maxRecDepth 16000 in
private theorem row12911 :
    FinalSeventhSieve.rough 11092009835083 12911+47536267=FinalSeventhSieve.rough 11092009835083 12907 :=
  LargeQuotientSieve.row (p:=12911) (q:=859113146) (s:=29310) (rank:=44024935) (tiny:=1536) (pairs:=3512867)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 859113146 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12911 : FinalSeventhSieve.rough 11092009835083 12911+525239348=FinalSeventhSieve.rough 11092009835083 12799 :=
  LargeQuotientSieve.combine to12907 row12911 rfl

set_option maxRecDepth 16000 in
private theorem row12917 :
    FinalSeventhSieve.rough 11092009835083 12917+47508777=FinalSeventhSieve.rough 11092009835083 12911 :=
  LargeQuotientSieve.row (p:=12917) (q:=858714084) (s:=29303) (rank:=44005594) (tiny:=1537) (pairs:=3504719)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ850000000To875000000.count_correct 858714084 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12917 : FinalSeventhSieve.rough 11092009835083 12917+572748125=FinalSeventhSieve.rough 11092009835083 12799 :=
  LargeQuotientSieve.combine to12911 row12917 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 12917+572748125=FinalSeventhSieve.rough 11092009835083 12799 := to12917

end Tail11092009835083From12799To12917
