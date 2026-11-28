import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1050000000-1075000000»

/-! Exact changes for sieve primes 1276 through 1276. -/
open Finset
namespace Tail11092009835083From10427To10429

private theorem split_pairs (n a b c : ℕ) (ab : a≤b) (bc : b≤c) :
    LargeQuotientSieve.pairSum n a c =
      LargeQuotientSieve.pairSum n a b + LargeQuotientSieve.pairSum n b c := by
  have partition : Icc (a+1) c = Icc (a+1) b ∪ Icc (b+1) c := by
    ext v
    simp only [mem_Icc,mem_union]
    omega
  have apart : Disjoint ((Icc (a+1) b).filter (fun r => FastDenseA26.prime r=true))
      ((Icc (b+1) c).filter (fun r => FastDenseA26.prime r=true)) := by
    refine disjoint_left.mpr ?_
    intro v hv hw
    have upper := (mem_Icc.mp (mem_filter.mp hv).1).2
    have lower := (mem_Icc.mp (mem_filter.mp hw).1).1
    omega
  unfold LargeQuotientSieve.pairSum
  rw [partition,filter_union,sum_union apart]

private theorem join_pairs {n a b c u v total : ℕ} (ab : a≤b) (bc : b≤c)
    (first : LargeQuotientSieve.pairSum n a b=u) (next : LargeQuotientSieve.pairSum n b c=v)
    (plus : u+v=total) : LargeQuotientSieve.pairSum n a c=total := by
  rw [split_pairs _ _ _ _ ab bc,first,next,plus]

set_option maxRecDepth 12000 in
private theorem pairs10427x10773 : LargeQuotientSieve.pairSum 1063573672 10427 10773=308151 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs10773x11120 : LargeQuotientSieve.pairSum 1063573672 10773 11120=288393 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs10427x11120 : LargeQuotientSieve.pairSum 1063573672 10427 11120=596544 := join_pairs (b:=10773) (by decide) (by decide) pairs10427x10773 pairs10773x11120 rfl

set_option maxRecDepth 12000 in
private theorem pairs11120x11466 : LargeQuotientSieve.pairSum 1063573672 11120 11466=254913 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs11466x11813 : LargeQuotientSieve.pairSum 1063573672 11466 11813=260372 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs11120x11813 : LargeQuotientSieve.pairSum 1063573672 11120 11813=515285 := join_pairs (b:=11466) (by decide) (by decide) pairs11120x11466 pairs11466x11813 rfl

set_option maxRecDepth 12000 in
private theorem pairs10427x11813 : LargeQuotientSieve.pairSum 1063573672 10427 11813=1111829 := join_pairs (b:=11120) (by decide) (by decide) pairs10427x11120 pairs11120x11813 rfl

set_option maxRecDepth 12000 in
private theorem pairs11813x12159 : LargeQuotientSieve.pairSum 1063573672 11813 12159=279522 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs12159x12506 : LargeQuotientSieve.pairSum 1063573672 12159 12506=262439 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs11813x12506 : LargeQuotientSieve.pairSum 1063573672 11813 12506=541961 := join_pairs (b:=12159) (by decide) (by decide) pairs11813x12159 pairs12159x12506 rfl

set_option maxRecDepth 12000 in
private theorem pairs12506x12853 : LargeQuotientSieve.pairSum 1063573672 12506 12853=260284 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs12853x13200 : LargeQuotientSieve.pairSum 1063573672 12853 13200=244422 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs12506x13200 : LargeQuotientSieve.pairSum 1063573672 12506 13200=504706 := join_pairs (b:=12853) (by decide) (by decide) pairs12506x12853 pairs12853x13200 rfl

set_option maxRecDepth 12000 in
private theorem pairs11813x13200 : LargeQuotientSieve.pairSum 1063573672 11813 13200=1046667 := join_pairs (b:=12506) (by decide) (by decide) pairs11813x12506 pairs12506x13200 rfl

set_option maxRecDepth 12000 in
private theorem pairs10427x13200 : LargeQuotientSieve.pairSum 1063573672 10427 13200=2158496 := join_pairs (b:=11813) (by decide) (by decide) pairs10427x11813 pairs11813x13200 rfl

set_option maxRecDepth 12000 in
private theorem pairs13200x13546 : LargeQuotientSieve.pairSum 1063573672 13200 13546=204815 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs13546x13893 : LargeQuotientSieve.pairSum 1063573672 13546 13893=227756 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs13200x13893 : LargeQuotientSieve.pairSum 1063573672 13200 13893=432571 := join_pairs (b:=13546) (by decide) (by decide) pairs13200x13546 pairs13546x13893 rfl

set_option maxRecDepth 12000 in
private theorem pairs13893x14239 : LargeQuotientSieve.pairSum 1063573672 13893 14239=179796 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs14239x14586 : LargeQuotientSieve.pairSum 1063573672 14239 14586=201356 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs13893x14586 : LargeQuotientSieve.pairSum 1063573672 13893 14586=381152 := join_pairs (b:=14239) (by decide) (by decide) pairs13893x14239 pairs14239x14586 rfl

set_option maxRecDepth 12000 in
private theorem pairs13200x14586 : LargeQuotientSieve.pairSum 1063573672 13200 14586=813723 := join_pairs (b:=13893) (by decide) (by decide) pairs13200x13893 pairs13893x14586 rfl

set_option maxRecDepth 12000 in
private theorem pairs14586x14932 : LargeQuotientSieve.pairSum 1063573672 14586 14932=216194 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs14932x15279 : LargeQuotientSieve.pairSum 1063573672 14932 15279=187365 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs14586x15279 : LargeQuotientSieve.pairSum 1063573672 14586 15279=403559 := join_pairs (b:=14932) (by decide) (by decide) pairs14586x14932 pairs14932x15279 rfl

set_option maxRecDepth 12000 in
private theorem pairs15279x15626 : LargeQuotientSieve.pairSum 1063573672 15279 15626=186592 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs15626x15973 : LargeQuotientSieve.pairSum 1063573672 15626 15973=194777 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs15279x15973 : LargeQuotientSieve.pairSum 1063573672 15279 15973=381369 := join_pairs (b:=15626) (by decide) (by decide) pairs15279x15626 pairs15626x15973 rfl

set_option maxRecDepth 12000 in
private theorem pairs14586x15973 : LargeQuotientSieve.pairSum 1063573672 14586 15973=784928 := join_pairs (b:=15279) (by decide) (by decide) pairs14586x15279 pairs15279x15973 rfl

set_option maxRecDepth 12000 in
private theorem pairs13200x15973 : LargeQuotientSieve.pairSum 1063573672 13200 15973=1598651 := join_pairs (b:=14586) (by decide) (by decide) pairs13200x14586 pairs14586x15973 rfl

set_option maxRecDepth 12000 in
private theorem pairs10427x15973 : LargeQuotientSieve.pairSum 1063573672 10427 15973=3757147 := join_pairs (b:=13200) (by decide) (by decide) pairs10427x13200 pairs13200x15973 rfl

set_option maxRecDepth 12000 in
private theorem pairs15973x16319 : LargeQuotientSieve.pairSum 1063573672 15973 16319=150420 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs16319x16666 : LargeQuotientSieve.pairSum 1063573672 16319 16666=158934 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs15973x16666 : LargeQuotientSieve.pairSum 1063573672 15973 16666=309354 := join_pairs (b:=16319) (by decide) (by decide) pairs15973x16319 pairs16319x16666 rfl

set_option maxRecDepth 12000 in
private theorem pairs16666x17012 : LargeQuotientSieve.pairSum 1063573672 16666 17012=144760 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs17012x17359 : LargeQuotientSieve.pairSum 1063573672 17012 17359=148536 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs16666x17359 : LargeQuotientSieve.pairSum 1063573672 16666 17359=293296 := join_pairs (b:=17012) (by decide) (by decide) pairs16666x17012 pairs17012x17359 rfl

set_option maxRecDepth 12000 in
private theorem pairs15973x17359 : LargeQuotientSieve.pairSum 1063573672 15973 17359=602650 := join_pairs (b:=16666) (by decide) (by decide) pairs15973x16666 pairs16666x17359 rfl

set_option maxRecDepth 12000 in
private theorem pairs17359x17705 : LargeQuotientSieve.pairSum 1063573672 17359 17705=147824 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs17705x18052 : LargeQuotientSieve.pairSum 1063573672 17705 18052=146526 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs17359x18052 : LargeQuotientSieve.pairSum 1063573672 17359 18052=294350 := join_pairs (b:=17705) (by decide) (by decide) pairs17359x17705 pairs17705x18052 rfl

set_option maxRecDepth 12000 in
private theorem pairs18052x18399 : LargeQuotientSieve.pairSum 1063573672 18052 18399=145157 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs18399x18746 : LargeQuotientSieve.pairSum 1063573672 18399 18746=117952 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs18052x18746 : LargeQuotientSieve.pairSum 1063573672 18052 18746=263109 := join_pairs (b:=18399) (by decide) (by decide) pairs18052x18399 pairs18399x18746 rfl

set_option maxRecDepth 12000 in
private theorem pairs17359x18746 : LargeQuotientSieve.pairSum 1063573672 17359 18746=557459 := join_pairs (b:=18052) (by decide) (by decide) pairs17359x18052 pairs18052x18746 rfl

set_option maxRecDepth 12000 in
private theorem pairs15973x18746 : LargeQuotientSieve.pairSum 1063573672 15973 18746=1160109 := join_pairs (b:=17359) (by decide) (by decide) pairs15973x17359 pairs17359x18746 rfl

set_option maxRecDepth 12000 in
private theorem pairs18746x19092 : LargeQuotientSieve.pairSum 1063573672 18746 19092=106360 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs19092x19439 : LargeQuotientSieve.pairSum 1063573672 19092 19439=116175 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs18746x19439 : LargeQuotientSieve.pairSum 1063573672 18746 19439=222535 := join_pairs (b:=19092) (by decide) (by decide) pairs18746x19092 pairs19092x19439 rfl

set_option maxRecDepth 12000 in
private theorem pairs19439x19785 : LargeQuotientSieve.pairSum 1063573672 19439 19785=118913 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs19785x20132 : LargeQuotientSieve.pairSum 1063573672 19785 20132=120613 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs19439x20132 : LargeQuotientSieve.pairSum 1063573672 19439 20132=239526 := join_pairs (b:=19785) (by decide) (by decide) pairs19439x19785 pairs19785x20132 rfl

set_option maxRecDepth 12000 in
private theorem pairs18746x20132 : LargeQuotientSieve.pairSum 1063573672 18746 20132=462061 := join_pairs (b:=19439) (by decide) (by decide) pairs18746x19439 pairs19439x20132 rfl

set_option maxRecDepth 12000 in
private theorem pairs20132x20478 : LargeQuotientSieve.pairSum 1063573672 20132 20478=104005 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs20478x20825 : LargeQuotientSieve.pairSum 1063573672 20478 20825=97085 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs20132x20825 : LargeQuotientSieve.pairSum 1063573672 20132 20825=201090 := join_pairs (b:=20478) (by decide) (by decide) pairs20132x20478 pairs20478x20825 rfl

set_option maxRecDepth 12000 in
private theorem pairs20825x21172 : LargeQuotientSieve.pairSum 1063573672 20825 21172=101831 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs21172x21519 : LargeQuotientSieve.pairSum 1063573672 21172 21519=92438 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs20825x21519 : LargeQuotientSieve.pairSum 1063573672 20825 21519=194269 := join_pairs (b:=21172) (by decide) (by decide) pairs20825x21172 pairs21172x21519 rfl

set_option maxRecDepth 12000 in
private theorem pairs20132x21519 : LargeQuotientSieve.pairSum 1063573672 20132 21519=395359 := join_pairs (b:=20825) (by decide) (by decide) pairs20132x20825 pairs20825x21519 rfl

set_option maxRecDepth 12000 in
private theorem pairs18746x21519 : LargeQuotientSieve.pairSum 1063573672 18746 21519=857420 := join_pairs (b:=20132) (by decide) (by decide) pairs18746x20132 pairs20132x21519 rfl

set_option maxRecDepth 12000 in
private theorem pairs15973x21519 : LargeQuotientSieve.pairSum 1063573672 15973 21519=2017529 := join_pairs (b:=18746) (by decide) (by decide) pairs15973x18746 pairs18746x21519 rfl

set_option maxRecDepth 12000 in
private theorem pairs10427x21519 : LargeQuotientSieve.pairSum 1063573672 10427 21519=5774676 := join_pairs (b:=15973) (by decide) (by decide) pairs10427x15973 pairs15973x21519 rfl

set_option maxRecDepth 12000 in
private theorem pairs21519x21865 : LargeQuotientSieve.pairSum 1063573672 21519 21865=101702 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs21865x22212 : LargeQuotientSieve.pairSum 1063573672 21865 22212=89823 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs21519x22212 : LargeQuotientSieve.pairSum 1063573672 21519 22212=191525 := join_pairs (b:=21865) (by decide) (by decide) pairs21519x21865 pairs21865x22212 rfl

set_option maxRecDepth 12000 in
private theorem pairs22212x22558 : LargeQuotientSieve.pairSum 1063573672 22212 22558=76588 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs22558x22905 : LargeQuotientSieve.pairSum 1063573672 22558 22905=80347 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs22212x22905 : LargeQuotientSieve.pairSum 1063573672 22212 22905=156935 := join_pairs (b:=22558) (by decide) (by decide) pairs22212x22558 pairs22558x22905 rfl

set_option maxRecDepth 12000 in
private theorem pairs21519x22905 : LargeQuotientSieve.pairSum 1063573672 21519 22905=348460 := join_pairs (b:=22212) (by decide) (by decide) pairs21519x22212 pairs22212x22905 rfl

set_option maxRecDepth 12000 in
private theorem pairs22905x23251 : LargeQuotientSieve.pairSum 1063573672 22905 23251=81238 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs23251x23598 : LargeQuotientSieve.pairSum 1063573672 23251 23598=65098 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs22905x23598 : LargeQuotientSieve.pairSum 1063573672 22905 23598=146336 := join_pairs (b:=23251) (by decide) (by decide) pairs22905x23251 pairs23251x23598 rfl

set_option maxRecDepth 12000 in
private theorem pairs23598x23945 : LargeQuotientSieve.pairSum 1063573672 23598 23945=78271 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs23945x24292 : LargeQuotientSieve.pairSum 1063573672 23945 24292=70690 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs23598x24292 : LargeQuotientSieve.pairSum 1063573672 23598 24292=148961 := join_pairs (b:=23945) (by decide) (by decide) pairs23598x23945 pairs23945x24292 rfl

set_option maxRecDepth 12000 in
private theorem pairs22905x24292 : LargeQuotientSieve.pairSum 1063573672 22905 24292=295297 := join_pairs (b:=23598) (by decide) (by decide) pairs22905x23598 pairs23598x24292 rfl

set_option maxRecDepth 12000 in
private theorem pairs21519x24292 : LargeQuotientSieve.pairSum 1063573672 21519 24292=643757 := join_pairs (b:=22905) (by decide) (by decide) pairs21519x22905 pairs22905x24292 rfl

set_option maxRecDepth 12000 in
private theorem pairs24292x24638 : LargeQuotientSieve.pairSum 1063573672 24292 24638=52713 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs24638x24985 : LargeQuotientSieve.pairSum 1063573672 24638 24985=55477 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs24292x24985 : LargeQuotientSieve.pairSum 1063573672 24292 24985=108190 := join_pairs (b:=24638) (by decide) (by decide) pairs24292x24638 pairs24638x24985 rfl

set_option maxRecDepth 12000 in
private theorem pairs24985x25331 : LargeQuotientSieve.pairSum 1063573672 24985 25331=52550 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs25331x25678 : LargeQuotientSieve.pairSum 1063573672 25331 25678=54238 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs24985x25678 : LargeQuotientSieve.pairSum 1063573672 24985 25678=106788 := join_pairs (b:=25331) (by decide) (by decide) pairs24985x25331 pairs25331x25678 rfl

set_option maxRecDepth 12000 in
private theorem pairs24292x25678 : LargeQuotientSieve.pairSum 1063573672 24292 25678=214978 := join_pairs (b:=24985) (by decide) (by decide) pairs24292x24985 pairs24985x25678 rfl

set_option maxRecDepth 12000 in
private theorem pairs25678x26024 : LargeQuotientSieve.pairSum 1063573672 25678 26024=51091 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs26024x26371 : LargeQuotientSieve.pairSum 1063573672 26024 26371=46690 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs25678x26371 : LargeQuotientSieve.pairSum 1063573672 25678 26371=97781 := join_pairs (b:=26024) (by decide) (by decide) pairs25678x26024 pairs26024x26371 rfl

set_option maxRecDepth 12000 in
private theorem pairs26371x26718 : LargeQuotientSieve.pairSum 1063573672 26371 26718=45255 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs26718x27065 : LargeQuotientSieve.pairSum 1063573672 26718 27065=42395 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs26371x27065 : LargeQuotientSieve.pairSum 1063573672 26371 27065=87650 := join_pairs (b:=26718) (by decide) (by decide) pairs26371x26718 pairs26718x27065 rfl

set_option maxRecDepth 12000 in
private theorem pairs25678x27065 : LargeQuotientSieve.pairSum 1063573672 25678 27065=185431 := join_pairs (b:=26371) (by decide) (by decide) pairs25678x26371 pairs26371x27065 rfl

set_option maxRecDepth 12000 in
private theorem pairs24292x27065 : LargeQuotientSieve.pairSum 1063573672 24292 27065=400409 := join_pairs (b:=25678) (by decide) (by decide) pairs24292x25678 pairs25678x27065 rfl

set_option maxRecDepth 12000 in
private theorem pairs21519x27065 : LargeQuotientSieve.pairSum 1063573672 21519 27065=1044166 := join_pairs (b:=24292) (by decide) (by decide) pairs21519x24292 pairs24292x27065 rfl

set_option maxRecDepth 12000 in
private theorem pairs27065x27411 : LargeQuotientSieve.pairSum 1063573672 27065 27411=32828 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs27411x27758 : LargeQuotientSieve.pairSum 1063573672 27411 27758=33656 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs27065x27758 : LargeQuotientSieve.pairSum 1063573672 27065 27758=66484 := join_pairs (b:=27411) (by decide) (by decide) pairs27065x27411 pairs27411x27758 rfl

set_option maxRecDepth 12000 in
private theorem pairs27758x28104 : LargeQuotientSieve.pairSum 1063573672 27758 28104=37103 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs28104x28451 : LargeQuotientSieve.pairSum 1063573672 28104 28451=26979 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs27758x28451 : LargeQuotientSieve.pairSum 1063573672 27758 28451=64082 := join_pairs (b:=28104) (by decide) (by decide) pairs27758x28104 pairs28104x28451 rfl

set_option maxRecDepth 12000 in
private theorem pairs27065x28451 : LargeQuotientSieve.pairSum 1063573672 27065 28451=130566 := join_pairs (b:=27758) (by decide) (by decide) pairs27065x27758 pairs27758x28451 rfl

set_option maxRecDepth 12000 in
private theorem pairs28451x28797 : LargeQuotientSieve.pairSum 1063573672 28451 28797=32849 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs28797x29144 : LargeQuotientSieve.pairSum 1063573672 28797 29144=22981 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs28451x29144 : LargeQuotientSieve.pairSum 1063573672 28451 29144=55830 := join_pairs (b:=28797) (by decide) (by decide) pairs28451x28797 pairs28797x29144 rfl

set_option maxRecDepth 12000 in
private theorem pairs29144x29491 : LargeQuotientSieve.pairSum 1063573672 29144 29491=23954 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs29491x29838 : LargeQuotientSieve.pairSum 1063573672 29491 29838=17170 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs29144x29838 : LargeQuotientSieve.pairSum 1063573672 29144 29838=41124 := join_pairs (b:=29491) (by decide) (by decide) pairs29144x29491 pairs29491x29838 rfl

set_option maxRecDepth 12000 in
private theorem pairs28451x29838 : LargeQuotientSieve.pairSum 1063573672 28451 29838=96954 := join_pairs (b:=29144) (by decide) (by decide) pairs28451x29144 pairs29144x29838 rfl

set_option maxRecDepth 12000 in
private theorem pairs27065x29838 : LargeQuotientSieve.pairSum 1063573672 27065 29838=227520 := join_pairs (b:=28451) (by decide) (by decide) pairs27065x28451 pairs28451x29838 rfl

set_option maxRecDepth 12000 in
private theorem pairs29838x30184 : LargeQuotientSieve.pairSum 1063573672 29838 30184=16809 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs30184x30531 : LargeQuotientSieve.pairSum 1063573672 30184 30531=14618 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs29838x30531 : LargeQuotientSieve.pairSum 1063573672 29838 30531=31427 := join_pairs (b:=30184) (by decide) (by decide) pairs29838x30184 pairs30184x30531 rfl

set_option maxRecDepth 12000 in
private theorem pairs30531x30878 : LargeQuotientSieve.pairSum 1063573672 30531 30878=13086 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs30878x31225 : LargeQuotientSieve.pairSum 1063573672 30878 31225=10588 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs30531x31225 : LargeQuotientSieve.pairSum 1063573672 30531 31225=23674 := join_pairs (b:=30878) (by decide) (by decide) pairs30531x30878 pairs30878x31225 rfl

set_option maxRecDepth 12000 in
private theorem pairs29838x31225 : LargeQuotientSieve.pairSum 1063573672 29838 31225=55101 := join_pairs (b:=30531) (by decide) (by decide) pairs29838x30531 pairs30531x31225 rfl

set_option maxRecDepth 12000 in
private theorem pairs31225x31571 : LargeQuotientSieve.pairSum 1063573672 31225 31571=8165 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs31571x31918 : LargeQuotientSieve.pairSum 1063573672 31571 31918=5303 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs31225x31918 : LargeQuotientSieve.pairSum 1063573672 31225 31918=13468 := join_pairs (b:=31571) (by decide) (by decide) pairs31225x31571 pairs31571x31918 rfl

set_option maxRecDepth 12000 in
private theorem pairs31918x32265 : LargeQuotientSieve.pairSum 1063573672 31918 32265=3610 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs32265x32612 : LargeQuotientSieve.pairSum 1063573672 32265 32612=1388 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem pairs31918x32612 : LargeQuotientSieve.pairSum 1063573672 31918 32612=4998 := join_pairs (b:=32265) (by decide) (by decide) pairs31918x32265 pairs32265x32612 rfl

set_option maxRecDepth 12000 in
private theorem pairs31225x32612 : LargeQuotientSieve.pairSum 1063573672 31225 32612=18466 := join_pairs (b:=31918) (by decide) (by decide) pairs31225x31918 pairs31918x32612 rfl

set_option maxRecDepth 12000 in
private theorem pairs29838x32612 : LargeQuotientSieve.pairSum 1063573672 29838 32612=73567 := join_pairs (b:=31225) (by decide) (by decide) pairs29838x31225 pairs31225x32612 rfl

set_option maxRecDepth 12000 in
private theorem pairs27065x32612 : LargeQuotientSieve.pairSum 1063573672 27065 32612=301087 := join_pairs (b:=29838) (by decide) (by decide) pairs27065x29838 pairs29838x32612 rfl

set_option maxRecDepth 12000 in
private theorem pairs21519x32612 : LargeQuotientSieve.pairSum 1063573672 21519 32612=1345253 := join_pairs (b:=27065) (by decide) (by decide) pairs21519x27065 pairs27065x32612 rfl

set_option maxRecDepth 12000 in
private theorem pairs10427x32612 : LargeQuotientSieve.pairSum 1063573672 10427 32612=7119929 := join_pairs (b:=21519) (by decide) (by decide) pairs10427x21519 pairs21519x32612 rfl

set_option maxRecDepth 16000 in
private theorem row10429 :
    FinalSeventhSieve.rough 11092009835083 10429+61028941=FinalSeventhSieve.rough 11092009835083 10427 :=
  LargeQuotientSieve.row (p:=10429) (q:=1063573672) (s:=32612) (rank:=53910286) (tiny:=1275) (pairs:=7119929)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1050000000To1075000000.count_correct 1063573672 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) pairs10427x32612 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10429+61028941=FinalSeventhSieve.rough 11092009835083 10427 := row10429

end Tail11092009835083From10427To10429
