import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1075000000-1100000000»

/-! Exact changes for sieve primes 3030 through 3041. -/
open Finset
namespace Tail30110134441897From27763To27847

set_option maxRecDepth 16000 in
private theorem row27767 :
    FinalSeventhSieve.rough 30110134441897 27767+55174302=FinalSeventhSieve.rough 30110134441897 27763 :=
  LargeQuotientSieve.row (p:=27767) (q:=1084385581) (s:=32930) (rank:=54911837) (tiny:=3029) (pairs:=265493)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1084385581 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row27773 :
    FinalSeventhSieve.rough 30110134441897 27773+55161594=FinalSeventhSieve.rough 30110134441897 27767 :=
  LargeQuotientSieve.row (p:=27773) (q:=1084151313) (s:=32926) (rank:=54900582) (tiny:=3030) (pairs:=264041)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1084151313 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27773 : FinalSeventhSieve.rough 30110134441897 27773+110335896=FinalSeventhSieve.rough 30110134441897 27763 :=
  LargeQuotientSieve.combine row27767 row27773 rfl

set_option maxRecDepth 16000 in
private theorem row27779 :
    FinalSeventhSieve.rough 30110134441897 27779+55148830=FinalSeventhSieve.rough 30110134441897 27773 :=
  LargeQuotientSieve.row (p:=27779) (q:=1083917147) (s:=32922) (rank:=54889255) (tiny:=3031) (pairs:=262605)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1083917147 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27779 : FinalSeventhSieve.rough 30110134441897 27779+165484726=FinalSeventhSieve.rough 30110134441897 27763 :=
  LargeQuotientSieve.combine to27773 row27779 rfl

set_option maxRecDepth 16000 in
private theorem row27791 :
    FinalSeventhSieve.rough 30110134441897 27791+55124520=FinalSeventhSieve.rough 30110134441897 27779 :=
  LargeQuotientSieve.row (p:=27791) (q:=1083449118) (s:=32915) (rank:=54866773) (tiny:=3032) (pairs:=260778)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1083449118 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27791 : FinalSeventhSieve.rough 30110134441897 27791+220609246=FinalSeventhSieve.rough 30110134441897 27763 :=
  LargeQuotientSieve.combine to27779 row27791 rfl

set_option maxRecDepth 16000 in
private theorem row27793 :
    FinalSeventhSieve.rough 30110134441897 27793+55119590=FinalSeventhSieve.rough 30110134441897 27791 :=
  LargeQuotientSieve.row (p:=27793) (q:=1083371152) (s:=32914) (rank:=54863048) (tiny:=3033) (pairs:=259574)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1083371152 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27793 : FinalSeventhSieve.rough 30110134441897 27793+275728836=FinalSeventhSieve.rough 30110134441897 27763 :=
  LargeQuotientSieve.combine to27791 row27793 rfl

set_option maxRecDepth 16000 in
private theorem row27799 :
    FinalSeventhSieve.rough 30110134441897 27799+55106858=FinalSeventhSieve.rough 30110134441897 27793 :=
  LargeQuotientSieve.row (p:=27799) (q:=1083137322) (s:=32911) (rank:=54851738) (tiny:=3034) (pairs:=258153)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1083137322 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27799 : FinalSeventhSieve.rough 30110134441897 27799+330835694=FinalSeventhSieve.rough 30110134441897 27763 :=
  LargeQuotientSieve.combine to27793 row27799 rfl

set_option maxRecDepth 16000 in
private theorem row27803 :
    FinalSeventhSieve.rough 30110134441897 27803+55097969=FinalSeventhSieve.rough 30110134441897 27799 :=
  LargeQuotientSieve.row (p:=27803) (q:=1082981492) (s:=32908) (rank:=54844163) (tiny:=3035) (pairs:=256840)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1082981492 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27803 : FinalSeventhSieve.rough 30110134441897 27803+385933663=FinalSeventhSieve.rough 30110134441897 27763 :=
  LargeQuotientSieve.combine to27799 row27803 rfl

set_option maxRecDepth 16000 in
private theorem row27809 :
    FinalSeventhSieve.rough 30110134441897 27809+55085286=FinalSeventhSieve.rough 30110134441897 27803 :=
  LargeQuotientSieve.row (p:=27809) (q:=1082747831) (s:=32905) (rank:=54832922) (tiny:=3036) (pairs:=255399)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1082747831 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27809 : FinalSeventhSieve.rough 30110134441897 27809+441018949=FinalSeventhSieve.rough 30110134441897 27763 :=
  LargeQuotientSieve.combine to27803 row27809 rfl

set_option maxRecDepth 16000 in
private theorem row27817 :
    FinalSeventhSieve.rough 30110134441897 27817+55068817=FinalSeventhSieve.rough 30110134441897 27809 :=
  LargeQuotientSieve.row (p:=27817) (q:=1082436439) (s:=32900) (rank:=54817998) (tiny:=3037) (pairs:=253855)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1082436439 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27817 : FinalSeventhSieve.rough 30110134441897 27817+496087766=FinalSeventhSieve.rough 30110134441897 27763 :=
  LargeQuotientSieve.combine to27809 row27817 rfl

set_option maxRecDepth 16000 in
private theorem row27823 :
    FinalSeventhSieve.rough 30110134441897 27823+55056143=FinalSeventhSieve.rough 30110134441897 27817 :=
  LargeQuotientSieve.row (p:=27823) (q:=1082203013) (s:=32896) (rank:=54806743) (tiny:=3038) (pairs:=252437)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1082203013 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27823 : FinalSeventhSieve.rough 30110134441897 27823+551143909=FinalSeventhSieve.rough 30110134441897 27763 :=
  LargeQuotientSieve.combine to27817 row27823 rfl

set_option maxRecDepth 16000 in
private theorem row27827 :
    FinalSeventhSieve.rough 30110134441897 27827+55047350=FinalSeventhSieve.rough 30110134441897 27823 :=
  LargeQuotientSieve.row (p:=27827) (q:=1082047451) (s:=32894) (rank:=54799240) (tiny:=3039) (pairs:=251148)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1082047451 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27827 : FinalSeventhSieve.rough 30110134441897 27827+606191259=FinalSeventhSieve.rough 30110134441897 27763 :=
  LargeQuotientSieve.combine to27823 row27827 rfl

set_option maxRecDepth 16000 in
private theorem row27847 :
    FinalSeventhSieve.rough 30110134441897 27847+55007575=FinalSeventhSieve.rough 30110134441897 27827 :=
  LargeQuotientSieve.row (p:=27847) (q:=1081270314) (s:=32882) (rank:=54761740) (tiny:=3040) (pairs:=248874)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1075000000To1100000000.count_correct 1081270314 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to27847 : FinalSeventhSieve.rough 30110134441897 27847+661198834=FinalSeventhSieve.rough 30110134441897 27763 :=
  LargeQuotientSieve.combine to27827 row27847 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 27847+661198834=FinalSeventhSieve.rough 30110134441897 27763 := to27847

end Tail30110134441897From27763To27847
