import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 3057 through 3068. -/
open Finset
namespace Tail30110134441897From28001To28111

set_option maxRecDepth 16000 in
private theorem row28019 :
    FinalSeventhSieve.rough 30110134441897 28019+54662596=FinalSeventhSieve.rough 30110134441897 28001 :=
  LargeQuotientSieve.row (p:=28019) (q:=1074632729) (s:=32781) (rank:=54442908) (tiny:=3056) (pairs:=222743)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1074632729 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row28027 :
    FinalSeventhSieve.rough 30110134441897 28027+54646429=FinalSeventhSieve.rough 30110134441897 28019 :=
  LargeQuotientSieve.row (p:=28027) (q:=1074325987) (s:=32776) (rank:=54428198) (tiny:=3057) (pairs:=221287)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1074325987 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28027 : FinalSeventhSieve.rough 30110134441897 28027+109309025=FinalSeventhSieve.rough 30110134441897 28001 :=
  LargeQuotientSieve.combine row28019 row28027 rfl

set_option maxRecDepth 16000 in
private theorem row28031 :
    FinalSeventhSieve.rough 30110134441897 28031+54637741=FinalSeventhSieve.rough 30110134441897 28027 :=
  LargeQuotientSieve.row (p:=28031) (q:=1074172681) (s:=32774) (rank:=54420739) (tiny:=3058) (pairs:=220059)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1074172681 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28031 : FinalSeventhSieve.rough 30110134441897 28031+163946766=FinalSeventhSieve.rough 30110134441897 28001 :=
  LargeQuotientSieve.combine to28027 row28031 rfl

set_option maxRecDepth 16000 in
private theorem row28051 :
    FinalSeventhSieve.rough 30110134441897 28051+54598977=FinalSeventhSieve.rough 30110134441897 28031 :=
  LargeQuotientSieve.row (p:=28051) (q:=1073406810) (s:=32762) (rank:=54384019) (tiny:=3059) (pairs:=218016)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1073406810 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28051 : FinalSeventhSieve.rough 30110134441897 28051+218545743=FinalSeventhSieve.rough 30110134441897 28001 :=
  LargeQuotientSieve.combine to28031 row28051 rfl

set_option maxRecDepth 16000 in
private theorem row28057 :
    FinalSeventhSieve.rough 30110134441897 28057+54586615=FinalSeventhSieve.rough 30110134441897 28051 :=
  LargeQuotientSieve.row (p:=28057) (q:=1073177262) (s:=32759) (rank:=54372979) (tiny:=3060) (pairs:=216695)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1073177262 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28057 : FinalSeventhSieve.rough 30110134441897 28057+273132358=FinalSeventhSieve.rough 30110134441897 28001 :=
  LargeQuotientSieve.combine to28051 row28057 rfl

set_option maxRecDepth 16000 in
private theorem row28069 :
    FinalSeventhSieve.rough 30110134441897 28069+54562951=FinalSeventhSieve.rough 30110134441897 28057 :=
  LargeQuotientSieve.row (p:=28069) (q:=1072718459) (s:=32752) (rank:=54350908) (tiny:=3061) (pairs:=215103)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1072718459 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28069 : FinalSeventhSieve.rough 30110134441897 28069+327695309=FinalSeventhSieve.rough 30110134441897 28001 :=
  LargeQuotientSieve.combine to28057 row28069 rfl

set_option maxRecDepth 16000 in
private theorem row28081 :
    FinalSeventhSieve.rough 30110134441897 28081+54539311=FinalSeventhSieve.rough 30110134441897 28069 :=
  LargeQuotientSieve.row (p:=28081) (q:=1072260049) (s:=32745) (rank:=54328893) (tiny:=3062) (pairs:=213479)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1072260049 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28081 : FinalSeventhSieve.rough 30110134441897 28081+382234620=FinalSeventhSieve.rough 30110134441897 28001 :=
  LargeQuotientSieve.combine to28069 row28081 rfl

set_option maxRecDepth 16000 in
private theorem row28087 :
    FinalSeventhSieve.rough 30110134441897 28087+54526988=FinalSeventhSieve.rough 30110134441897 28081 :=
  LargeQuotientSieve.row (p:=28087) (q:=1072030990) (s:=32741) (rank:=54317852) (tiny:=3063) (pairs:=212198)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1072030990 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28087 : FinalSeventhSieve.rough 30110134441897 28087+436761608=FinalSeventhSieve.rough 30110134441897 28001 :=
  LargeQuotientSieve.combine to28081 row28087 rfl

set_option maxRecDepth 16000 in
private theorem row28097 :
    FinalSeventhSieve.rough 30110134441897 28097+54507089=FinalSeventhSieve.rough 30110134441897 28087 :=
  LargeQuotientSieve.row (p:=28097) (q:=1071649444) (s:=32736) (rank:=54299495) (tiny:=3064) (pairs:=210657)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1071649444 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28097 : FinalSeventhSieve.rough 30110134441897 28097+491268697=FinalSeventhSieve.rough 30110134441897 28001 :=
  LargeQuotientSieve.combine to28087 row28097 rfl

set_option maxRecDepth 16000 in
private theorem row28099 :
    FinalSeventhSieve.rough 30110134441897 28099+54502362=FinalSeventhSieve.rough 30110134441897 28097 :=
  LargeQuotientSieve.row (p:=28099) (q:=1071573167) (s:=32734) (rank:=54295839) (tiny:=3065) (pairs:=209587)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1071573167 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28099 : FinalSeventhSieve.rough 30110134441897 28099+545771059=FinalSeventhSieve.rough 30110134441897 28001 :=
  LargeQuotientSieve.combine to28097 row28099 rfl

set_option maxRecDepth 16000 in
private theorem row28109 :
    FinalSeventhSieve.rough 30110134441897 28109+54482536=FinalSeventhSieve.rough 30110134441897 28099 :=
  LargeQuotientSieve.row (p:=28109) (q:=1071191947) (s:=32729) (rank:=54277514) (tiny:=3066) (pairs:=208087)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1071191947 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28109 : FinalSeventhSieve.rough 30110134441897 28109+600253595=FinalSeventhSieve.rough 30110134441897 28001 :=
  LargeQuotientSieve.combine to28099 row28109 rfl

set_option maxRecDepth 16000 in
private theorem row28111 :
    FinalSeventhSieve.rough 30110134441897 28111+54477805=FinalSeventhSieve.rough 30110134441897 28109 :=
  LargeQuotientSieve.row (p:=28111) (q:=1071115735) (s:=32727) (rank:=54273851) (tiny:=3067) (pairs:=207020)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1071115735 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28111 : FinalSeventhSieve.rough 30110134441897 28111+654731400=FinalSeventhSieve.rough 30110134441897 28001 :=
  LargeQuotientSieve.combine to28109 row28111 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 28111+654731400=FinalSeventhSieve.rough 30110134441897 28001 := to28111

end Tail30110134441897From28001To28111
