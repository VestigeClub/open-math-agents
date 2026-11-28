import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1025000000-1050000000»

/-! Exact changes for sieve primes 3125 through 3136. -/
open Finset
namespace Tail30110134441897From28669To28793

set_option maxRecDepth 16000 in
private theorem row28687 :
    FinalSeventhSieve.rough 30110134441897 28687+53366615=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.row (p:=28687) (q:=1049609036) (s:=32397) (rank:=53238569) (tiny:=3124) (pairs:=131169)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1049609036 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row28697 :
    FinalSeventhSieve.rough 30110134441897 28697+53347795=FinalSeventhSieve.rough 30110134441897 28687 :=
  LargeQuotientSieve.row (p:=28697) (q:=1049243281) (s:=32392) (rank:=53220917) (tiny:=3125) (pairs:=130002)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1049243281 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28697 : FinalSeventhSieve.rough 30110134441897 28697+106714410=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine row28687 row28697 rfl

set_option maxRecDepth 16000 in
private theorem row28703 :
    FinalSeventhSieve.rough 30110134441897 28703+53336296=FinalSeventhSieve.rough 30110134441897 28697 :=
  LargeQuotientSieve.row (p:=28703) (q:=1049023950) (s:=32388) (rank:=53210405) (tiny:=3126) (pairs:=129016)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1049023950 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28703 : FinalSeventhSieve.rough 30110134441897 28703+160050706=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to28697 row28703 rfl

set_option maxRecDepth 16000 in
private theorem row28711 :
    FinalSeventhSieve.rough 30110134441897 28711+53321234=FinalSeventhSieve.rough 30110134441897 28703 :=
  LargeQuotientSieve.row (p:=28711) (q:=1048731651) (s:=32384) (rank:=53196427) (tiny:=3127) (pairs:=127933)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1048731651 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28711 : FinalSeventhSieve.rough 30110134441897 28711+213371940=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to28703 row28711 rfl

set_option maxRecDepth 16000 in
private theorem row28723 :
    FinalSeventhSieve.rough 30110134441897 28723+53299027=FinalSeventhSieve.rough 30110134441897 28711 :=
  LargeQuotientSieve.row (p:=28723) (q:=1048293508) (s:=32377) (rank:=53175432) (tiny:=3128) (pairs:=126722)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1048293508 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28723 : FinalSeventhSieve.rough 30110134441897 28723+266670967=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to28711 row28723 rfl

set_option maxRecDepth 16000 in
private theorem row28729 :
    FinalSeventhSieve.rough 30110134441897 28729+53287413=FinalSeventhSieve.rough 30110134441897 28723 :=
  LargeQuotientSieve.row (p:=28729) (q:=1048074574) (s:=32373) (rank:=53164808) (tiny:=3129) (pairs:=125733)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1048074574 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28729 : FinalSeventhSieve.rough 30110134441897 28729+319958380=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to28723 row28729 rfl

set_option maxRecDepth 16000 in
private theorem row28751 :
    FinalSeventhSieve.rough 30110134441897 28751+53247299=FinalSeventhSieve.rough 30110134441897 28729 :=
  LargeQuotientSieve.row (p:=28751) (q:=1047272597) (s:=32361) (rank:=53126270) (tiny:=3130) (pairs:=124158)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1047272597 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28751 : FinalSeventhSieve.rough 30110134441897 28751+373205679=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to28729 row28751 rfl

set_option maxRecDepth 16000 in
private theorem row28753 :
    FinalSeventhSieve.rough 30110134441897 28753+53243002=FinalSeventhSieve.rough 30110134441897 28751 :=
  LargeQuotientSieve.row (p:=28753) (q:=1047199751) (s:=32360) (rank:=53122791) (tiny:=3131) (pairs:=123341)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1047199751 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28753 : FinalSeventhSieve.rough 30110134441897 28753+426448681=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to28751 row28753 rfl

set_option maxRecDepth 16000 in
private theorem row28759 :
    FinalSeventhSieve.rough 30110134441897 28759+53231548=FinalSeventhSieve.rough 30110134441897 28753 :=
  LargeQuotientSieve.row (p:=28759) (q:=1046981273) (s:=32357) (rank:=53112293) (tiny:=3132) (pairs:=122386)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1046981273 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28759 : FinalSeventhSieve.rough 30110134441897 28759+479680229=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to28753 row28759 rfl

set_option maxRecDepth 16000 in
private theorem row28771 :
    FinalSeventhSieve.rough 30110134441897 28771+53209419=FinalSeventhSieve.rough 30110134441897 28759 :=
  LargeQuotientSieve.row (p:=28771) (q:=1046544591) (s:=32350) (rank:=53091385) (tiny:=3133) (pairs:=121166)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1046544591 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28771 : FinalSeventhSieve.rough 30110134441897 28771+532889648=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to28759 row28771 rfl

set_option maxRecDepth 16000 in
private theorem row28789 :
    FinalSeventhSieve.rough 30110134441897 28789+53176380=FinalSeventhSieve.rough 30110134441897 28771 :=
  LargeQuotientSieve.row (p:=28789) (q:=1045890251) (s:=32340) (rank:=53059760) (tiny:=3134) (pairs:=119753)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1045890251 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28789 : FinalSeventhSieve.rough 30110134441897 28789+586066028=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to28771 row28789 rfl

set_option maxRecDepth 16000 in
private theorem row28793 :
    FinalSeventhSieve.rough 30110134441897 28793+53168520=FinalSeventhSieve.rough 30110134441897 28789 :=
  LargeQuotientSieve.row (p:=28793) (q:=1045744953) (s:=32337) (rank:=53052804) (tiny:=3135) (pairs:=118850)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1045744953 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28793 : FinalSeventhSieve.rough 30110134441897 28793+639234548=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to28789 row28793 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 28793+639234548=FinalSeventhSieve.rough 30110134441897 28669 := to28793

end Tail30110134441897From28669To28793
