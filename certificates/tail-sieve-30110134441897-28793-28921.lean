import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1025000000-1050000000»

/-! Exact changes for sieve primes 3137 through 3148. -/
open Finset
namespace Tail30110134441897From28793To28921

set_option maxRecDepth 16000 in
private theorem row28807 :
    FinalSeventhSieve.rough 30110134441897 28807+53142807=FinalSeventhSieve.rough 30110134441897 28793 :=
  LargeQuotientSieve.row (p:=28807) (q:=1045236728) (s:=32330) (rank:=53028340) (tiny:=3136) (pairs:=117602)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1045236728 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row28813 :
    FinalSeventhSieve.rough 30110134441897 28813+53131415=FinalSeventhSieve.rough 30110134441897 28807 :=
  LargeQuotientSieve.row (p:=28813) (q:=1045019069) (s:=32326) (rank:=53017897) (tiny:=3137) (pairs:=116654)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1045019069 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28813 : FinalSeventhSieve.rough 30110134441897 28813+106274222=FinalSeventhSieve.rough 30110134441897 28793 :=
  LargeQuotientSieve.combine row28807 row28813 rfl

set_option maxRecDepth 16000 in
private theorem row28817 :
    FinalSeventhSieve.rough 30110134441897 28817+53123646=FinalSeventhSieve.rough 30110134441897 28813 :=
  LargeQuotientSieve.row (p:=28817) (q:=1044874013) (s:=32324) (rank:=53010978) (tiny:=3138) (pairs:=115805)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1044874013 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28817 : FinalSeventhSieve.rough 30110134441897 28817+159397868=FinalSeventhSieve.rough 30110134441897 28793 :=
  LargeQuotientSieve.combine to28813 row28817 rfl

set_option maxRecDepth 16000 in
private theorem row28837 :
    FinalSeventhSieve.rough 30110134441897 28837+53087315=FinalSeventhSieve.rough 30110134441897 28817 :=
  LargeQuotientSieve.row (p:=28837) (q:=1044149337) (s:=32313) (rank:=52976147) (tiny:=3139) (pairs:=114306)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1044149337 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28837 : FinalSeventhSieve.rough 30110134441897 28837+212485183=FinalSeventhSieve.rough 30110134441897 28793 :=
  LargeQuotientSieve.combine to28817 row28837 rfl

set_option maxRecDepth 16000 in
private theorem row28843 :
    FinalSeventhSieve.rough 30110134441897 28843+53075964=FinalSeventhSieve.rough 30110134441897 28837 :=
  LargeQuotientSieve.row (p:=28843) (q:=1043932130) (s:=32309) (rank:=52965720) (tiny:=3140) (pairs:=113383)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1043932130 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28843 : FinalSeventhSieve.rough 30110134441897 28843+265561147=FinalSeventhSieve.rough 30110134441897 28793 :=
  LargeQuotientSieve.combine to28837 row28843 rfl

set_option maxRecDepth 16000 in
private theorem row28859 :
    FinalSeventhSieve.rough 30110134441897 28859+53046699=FinalSeventhSieve.rough 30110134441897 28843 :=
  LargeQuotientSieve.row (p:=28859) (q:=1043353353) (s:=32300) (rank:=52937747) (tiny:=3141) (pairs:=112092)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1043353353 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28859 : FinalSeventhSieve.rough 30110134441897 28859+318607846=FinalSeventhSieve.rough 30110134441897 28793 :=
  LargeQuotientSieve.combine to28843 row28859 rfl

set_option maxRecDepth 16000 in
private theorem row28867 :
    FinalSeventhSieve.rough 30110134441897 28867+53031831=FinalSeventhSieve.rough 30110134441897 28859 :=
  LargeQuotientSieve.row (p:=28867) (q:=1043064206) (s:=32296) (rank:=52923888) (tiny:=3142) (pairs:=111084)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1043064206 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28867 : FinalSeventhSieve.rough 30110134441897 28867+371639677=FinalSeventhSieve.rough 30110134441897 28793 :=
  LargeQuotientSieve.combine to28859 row28867 rfl

set_option maxRecDepth 16000 in
private theorem row28871 :
    FinalSeventhSieve.rough 30110134441897 28871+53024133=FinalSeventhSieve.rough 30110134441897 28867 :=
  LargeQuotientSieve.row (p:=28871) (q:=1042919692) (s:=32294) (rank:=52917026) (tiny:=3143) (pairs:=110249)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1042919692 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28871 : FinalSeventhSieve.rough 30110134441897 28871+424663810=FinalSeventhSieve.rough 30110134441897 28793 :=
  LargeQuotientSieve.combine to28867 row28871 rfl

set_option maxRecDepth 16000 in
private theorem row28879 :
    FinalSeventhSieve.rough 30110134441897 28879+53009168=FinalSeventhSieve.rough 30110134441897 28871 :=
  LargeQuotientSieve.row (p:=28879) (q:=1042630785) (s:=32289) (rank:=52903046) (tiny:=3144) (pairs:=109265)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1042630785 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28879 : FinalSeventhSieve.rough 30110134441897 28879+477672978=FinalSeventhSieve.rough 30110134441897 28793 :=
  LargeQuotientSieve.combine to28871 row28879 rfl

set_option maxRecDepth 16000 in
private theorem row28901 :
    FinalSeventhSieve.rough 30110134441897 28901+52969413=FinalSeventhSieve.rough 30110134441897 28879 :=
  LargeQuotientSieve.row (p:=28901) (q:=1041837114) (s:=32277) (rank:=52864788) (tiny:=3145) (pairs:=107769)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1041837114 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28901 : FinalSeventhSieve.rough 30110134441897 28901+530642391=FinalSeventhSieve.rough 30110134441897 28793 :=
  LargeQuotientSieve.combine to28879 row28901 rfl

set_option maxRecDepth 16000 in
private theorem row28909 :
    FinalSeventhSieve.rough 30110134441897 28909+52954443=FinalSeventhSieve.rough 30110134441897 28901 :=
  LargeQuotientSieve.row (p:=28909) (q:=1041548806) (s:=32273) (rank:=52850797) (tiny:=3146) (pairs:=106791)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1041548806 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28909 : FinalSeventhSieve.rough 30110134441897 28909+583596834=FinalSeventhSieve.rough 30110134441897 28793 :=
  LargeQuotientSieve.combine to28901 row28909 rfl

set_option maxRecDepth 16000 in
private theorem row28921 :
    FinalSeventhSieve.rough 30110134441897 28921+52932484=FinalSeventhSieve.rough 30110134441897 28909 :=
  LargeQuotientSieve.row (p:=28921) (q:=1041116643) (s:=32266) (rank:=52829947) (tiny:=3147) (pairs:=105683)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1041116643 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to28921 : FinalSeventhSieve.rough 30110134441897 28921+636529318=FinalSeventhSieve.rough 30110134441897 28793 :=
  LargeQuotientSieve.combine to28909 row28921 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 28921+636529318=FinalSeventhSieve.rough 30110134441897 28793 := to28921

end Tail30110134441897From28793To28921
