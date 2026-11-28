import certificates.«semiprime-correction-555157672301-small»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 810,000 through 866,453

The sum covers 4,144 primes. Their quotient counts are checked by the
certified prime-counting table through 67,545,646.
-/
open Finset
namespace Correction30110134441897From810000To866453

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 810000 RangePrimeA26.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 810001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 810000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r810001 : blockSum term 810001 441 81633153 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r810442 : blockSum term 810442 441 68362689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r810883 : blockSum term 810883 441 72730598 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r811324 : blockSum term 811324 441 72687727 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r811765 : blockSum term 811765 441 66044998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r812206 : blockSum term 812206 441 81413376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r812647 : blockSum term 812647 441 54979066 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r813088 : blockSum term 813088 441 76930616 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r813529 : blockSum term 813529 441 59313690 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r813970 : blockSum term 813970 441 83434242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r814411 : blockSum term 814411 441 68024865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r814852 : blockSum term 814852 441 67989246 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r815293 : blockSum term 815293 441 76718290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r815734 : blockSum term 815734 441 65722243 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r816175 : blockSum term 816175 441 63502631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r816616 : blockSum term 816616 441 78786726 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r817057 : blockSum term 817057 441 69997819 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r817498 : blockSum term 817498 441 76515891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r817939 : blockSum term 817939 441 67734250 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r818380 : blockSum term 818380 441 50230734 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r818821 : blockSum term 818821 441 67663624 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r819262 : blockSum term 819262 441 89442465 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r819703 : blockSum term 819703 441 67591873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r820144 : blockSum term 820144 441 74094788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r820585 : blockSum term 820585 441 71877694 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r821026 : blockSum term 821026 441 71840893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r821467 : blockSum term 821467 441 69623336 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r821908 : blockSum term 821908 441 80458326 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r822349 : blockSum term 822349 441 78242425 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r822790 : blockSum term 822790 441 67342860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r823231 : blockSum term 823231 441 75988948 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r823672 : blockSum term 823672 442 80290623 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r824114 : blockSum term 824114 441 62894860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r824555 : blockSum term 824555 441 73699064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r824996 : blockSum term 824996 441 82327363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r825437 : blockSum term 825437 441 71457332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r825878 : blockSum term 825878 441 69254257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r826319 : blockSum term 826319 441 82193557 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r826760 : blockSum term 826760 441 62695720 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r827201 : blockSum term 827201 441 62661737 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r827642 : blockSum term 827642 441 79904969 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r828083 : blockSum term 828083 441 51804186 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r828524 : blockSum term 828524 441 75504973 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r828965 : blockSum term 828965 441 60373974 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r829406 : blockSum term 829406 441 68959247 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r829847 : blockSum term 829847 441 60308418 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r830288 : blockSum term 830288 441 79653211 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r830729 : blockSum term 830729 441 73153103 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r831170 : blockSum term 831170 441 64510438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r831611 : blockSum term 831611 441 79527895 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r832052 : blockSum term 832052 441 77333067 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r832493 : blockSum term 832493 441 83733771 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r832934 : blockSum term 832934 441 64378047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r833375 : blockSum term 833375 441 64343956 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r833816 : blockSum term 833816 441 60024253 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r834257 : blockSum term 834257 441 66418018 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r834698 : blockSum term 834698 441 66383440 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r835139 : blockSum term 835139 441 59927554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r835580 : blockSum term 835580 441 77009767 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r836021 : blockSum term 836021 441 66279161 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r836462 : blockSum term 836462 441 74789501 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r836903 : blockSum term 836903 441 55529905 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r837344 : blockSum term 837344 441 66174493 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r837785 : blockSum term 837785 442 66137728 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r838227 : blockSum term 838227 441 72498164 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r838668 : blockSum term 838668 441 68201375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r839109 : blockSum term 839109 441 61773767 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r839550 : blockSum term 839550 441 72389403 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r839991 : blockSum term 839991 441 59584439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r840432 : blockSum term 840432 441 70185944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r840873 : blockSum term 840873 441 82903513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r841314 : blockSum term 841314 441 55240574 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r841755 : blockSum term 841755 441 70073565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r842196 : blockSum term 842196 441 84895830 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r842637 : blockSum term 842637 441 55152384 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r843078 : blockSum term 843078 441 74206841 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r843519 : blockSum term 843519 441 65692941 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r843960 : blockSum term 843960 441 63540372 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r844401 : blockSum term 844401 441 80445647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r844842 : blockSum term 844842 441 67704150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r845283 : blockSum term 845283 441 54982705 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r845724 : blockSum term 845724 441 63407796 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r846165 : blockSum term 846165 441 65487756 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r846606 : blockSum term 846606 441 71785100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r847047 : blockSum term 847047 441 69642659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r847488 : blockSum term 847488 441 67496085 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r847929 : blockSum term 847929 441 61136122 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r848370 : blockSum term 848370 441 80064881 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r848811 : blockSum term 848811 441 73707511 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r849252 : blockSum term 849252 441 52621308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r849693 : blockSum term 849693 441 75735477 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r850134 : blockSum term 850134 441 75697205 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r850575 : blockSum term 850575 441 48334786 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r851016 : blockSum term 851016 441 81916967 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r851457 : blockSum term 851457 441 69278226 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r851898 : blockSum term 851898 442 62947088 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r852340 : blockSum term 852340 441 60817788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r852781 : blockSum term 852781 441 71269232 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r853222 : blockSum term 853222 441 46090950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r853663 : blockSum term 853663 441 81665746 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r854104 : blockSum term 854104 441 66971771 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r854545 : blockSum term 854545 441 56477658 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r854986 : blockSum term 854986 441 68992190 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r855427 : blockSum term 855427 441 66867296 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r855868 : blockSum term 855868 441 68922916 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r856309 : blockSum term 856309 441 73062448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r856750 : blockSum term 856750 441 73024826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r857191 : blockSum term 857191 441 64646116 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r857632 : blockSum term 857632 441 68781800 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r858073 : blockSum term 858073 441 68746079 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r858514 : blockSum term 858514 441 62461594 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r858955 : blockSum term 858955 442 64513134 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r859397 : blockSum term 859397 441 62400403 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r859838 : blockSum term 859838 441 62371412 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r860279 : blockSum term 860279 441 76884975 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r860720 : blockSum term 860720 441 78919985 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r861161 : blockSum term 861161 441 56044797 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r861602 : blockSum term 861602 441 74688808 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r862043 : blockSum term 862043 441 85018652 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r862484 : blockSum term 862484 441 66322533 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r862925 : blockSum term 862925 441 53860072 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r863366 : blockSum term 863366 441 53828881 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r863807 : blockSum term 863807 441 80703979 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r864248 : blockSum term 864248 441 70322636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r864689 : blockSum term 864689 441 66151576 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r865130 : blockSum term 865130 441 66120177 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r865571 : blockSum term 865571 441 82605828 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r866012 : blockSum term 866012 442 57794954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 810001 56453 8842639463 := (join_sums term (lo:=810001) (a:=28226) (b:=28227) (join_sums term (lo:=810001) (a:=14113) (b:=14113) (join_sums term (lo:=810001) (a:=7056) (b:=7057) (join_sums term (lo:=810001) (a:=3528) (b:=3528) (join_sums term (lo:=810001) (a:=1764) (b:=1764) (join_sums term (lo:=810001) (a:=882) (b:=882) (join_sums term (lo:=810001) (a:=441) (b:=441) r810001 r810442) (join_sums term (lo:=810883) (a:=441) (b:=441) r810883 r811324)) (join_sums term (lo:=811765) (a:=882) (b:=882) (join_sums term (lo:=811765) (a:=441) (b:=441) r811765 r812206) (join_sums term (lo:=812647) (a:=441) (b:=441) r812647 r813088))) (join_sums term (lo:=813529) (a:=1764) (b:=1764) (join_sums term (lo:=813529) (a:=882) (b:=882) (join_sums term (lo:=813529) (a:=441) (b:=441) r813529 r813970) (join_sums term (lo:=814411) (a:=441) (b:=441) r814411 r814852)) (join_sums term (lo:=815293) (a:=882) (b:=882) (join_sums term (lo:=815293) (a:=441) (b:=441) r815293 r815734) (join_sums term (lo:=816175) (a:=441) (b:=441) r816175 r816616)))) (join_sums term (lo:=817057) (a:=3528) (b:=3529) (join_sums term (lo:=817057) (a:=1764) (b:=1764) (join_sums term (lo:=817057) (a:=882) (b:=882) (join_sums term (lo:=817057) (a:=441) (b:=441) r817057 r817498) (join_sums term (lo:=817939) (a:=441) (b:=441) r817939 r818380)) (join_sums term (lo:=818821) (a:=882) (b:=882) (join_sums term (lo:=818821) (a:=441) (b:=441) r818821 r819262) (join_sums term (lo:=819703) (a:=441) (b:=441) r819703 r820144))) (join_sums term (lo:=820585) (a:=1764) (b:=1765) (join_sums term (lo:=820585) (a:=882) (b:=882) (join_sums term (lo:=820585) (a:=441) (b:=441) r820585 r821026) (join_sums term (lo:=821467) (a:=441) (b:=441) r821467 r821908)) (join_sums term (lo:=822349) (a:=882) (b:=883) (join_sums term (lo:=822349) (a:=441) (b:=441) r822349 r822790) (join_sums term (lo:=823231) (a:=441) (b:=442) r823231 r823672))))) (join_sums term (lo:=824114) (a:=7056) (b:=7057) (join_sums term (lo:=824114) (a:=3528) (b:=3528) (join_sums term (lo:=824114) (a:=1764) (b:=1764) (join_sums term (lo:=824114) (a:=882) (b:=882) (join_sums term (lo:=824114) (a:=441) (b:=441) r824114 r824555) (join_sums term (lo:=824996) (a:=441) (b:=441) r824996 r825437)) (join_sums term (lo:=825878) (a:=882) (b:=882) (join_sums term (lo:=825878) (a:=441) (b:=441) r825878 r826319) (join_sums term (lo:=826760) (a:=441) (b:=441) r826760 r827201))) (join_sums term (lo:=827642) (a:=1764) (b:=1764) (join_sums term (lo:=827642) (a:=882) (b:=882) (join_sums term (lo:=827642) (a:=441) (b:=441) r827642 r828083) (join_sums term (lo:=828524) (a:=441) (b:=441) r828524 r828965)) (join_sums term (lo:=829406) (a:=882) (b:=882) (join_sums term (lo:=829406) (a:=441) (b:=441) r829406 r829847) (join_sums term (lo:=830288) (a:=441) (b:=441) r830288 r830729)))) (join_sums term (lo:=831170) (a:=3528) (b:=3529) (join_sums term (lo:=831170) (a:=1764) (b:=1764) (join_sums term (lo:=831170) (a:=882) (b:=882) (join_sums term (lo:=831170) (a:=441) (b:=441) r831170 r831611) (join_sums term (lo:=832052) (a:=441) (b:=441) r832052 r832493)) (join_sums term (lo:=832934) (a:=882) (b:=882) (join_sums term (lo:=832934) (a:=441) (b:=441) r832934 r833375) (join_sums term (lo:=833816) (a:=441) (b:=441) r833816 r834257))) (join_sums term (lo:=834698) (a:=1764) (b:=1765) (join_sums term (lo:=834698) (a:=882) (b:=882) (join_sums term (lo:=834698) (a:=441) (b:=441) r834698 r835139) (join_sums term (lo:=835580) (a:=441) (b:=441) r835580 r836021)) (join_sums term (lo:=836462) (a:=882) (b:=883) (join_sums term (lo:=836462) (a:=441) (b:=441) r836462 r836903) (join_sums term (lo:=837344) (a:=441) (b:=442) r837344 r837785)))))) (join_sums term (lo:=838227) (a:=14113) (b:=14114) (join_sums term (lo:=838227) (a:=7056) (b:=7057) (join_sums term (lo:=838227) (a:=3528) (b:=3528) (join_sums term (lo:=838227) (a:=1764) (b:=1764) (join_sums term (lo:=838227) (a:=882) (b:=882) (join_sums term (lo:=838227) (a:=441) (b:=441) r838227 r838668) (join_sums term (lo:=839109) (a:=441) (b:=441) r839109 r839550)) (join_sums term (lo:=839991) (a:=882) (b:=882) (join_sums term (lo:=839991) (a:=441) (b:=441) r839991 r840432) (join_sums term (lo:=840873) (a:=441) (b:=441) r840873 r841314))) (join_sums term (lo:=841755) (a:=1764) (b:=1764) (join_sums term (lo:=841755) (a:=882) (b:=882) (join_sums term (lo:=841755) (a:=441) (b:=441) r841755 r842196) (join_sums term (lo:=842637) (a:=441) (b:=441) r842637 r843078)) (join_sums term (lo:=843519) (a:=882) (b:=882) (join_sums term (lo:=843519) (a:=441) (b:=441) r843519 r843960) (join_sums term (lo:=844401) (a:=441) (b:=441) r844401 r844842)))) (join_sums term (lo:=845283) (a:=3528) (b:=3529) (join_sums term (lo:=845283) (a:=1764) (b:=1764) (join_sums term (lo:=845283) (a:=882) (b:=882) (join_sums term (lo:=845283) (a:=441) (b:=441) r845283 r845724) (join_sums term (lo:=846165) (a:=441) (b:=441) r846165 r846606)) (join_sums term (lo:=847047) (a:=882) (b:=882) (join_sums term (lo:=847047) (a:=441) (b:=441) r847047 r847488) (join_sums term (lo:=847929) (a:=441) (b:=441) r847929 r848370))) (join_sums term (lo:=848811) (a:=1764) (b:=1765) (join_sums term (lo:=848811) (a:=882) (b:=882) (join_sums term (lo:=848811) (a:=441) (b:=441) r848811 r849252) (join_sums term (lo:=849693) (a:=441) (b:=441) r849693 r850134)) (join_sums term (lo:=850575) (a:=882) (b:=883) (join_sums term (lo:=850575) (a:=441) (b:=441) r850575 r851016) (join_sums term (lo:=851457) (a:=441) (b:=442) r851457 r851898))))) (join_sums term (lo:=852340) (a:=7057) (b:=7057) (join_sums term (lo:=852340) (a:=3528) (b:=3529) (join_sums term (lo:=852340) (a:=1764) (b:=1764) (join_sums term (lo:=852340) (a:=882) (b:=882) (join_sums term (lo:=852340) (a:=441) (b:=441) r852340 r852781) (join_sums term (lo:=853222) (a:=441) (b:=441) r853222 r853663)) (join_sums term (lo:=854104) (a:=882) (b:=882) (join_sums term (lo:=854104) (a:=441) (b:=441) r854104 r854545) (join_sums term (lo:=854986) (a:=441) (b:=441) r854986 r855427))) (join_sums term (lo:=855868) (a:=1764) (b:=1765) (join_sums term (lo:=855868) (a:=882) (b:=882) (join_sums term (lo:=855868) (a:=441) (b:=441) r855868 r856309) (join_sums term (lo:=856750) (a:=441) (b:=441) r856750 r857191)) (join_sums term (lo:=857632) (a:=882) (b:=883) (join_sums term (lo:=857632) (a:=441) (b:=441) r857632 r858073) (join_sums term (lo:=858514) (a:=441) (b:=442) r858514 r858955)))) (join_sums term (lo:=859397) (a:=3528) (b:=3529) (join_sums term (lo:=859397) (a:=1764) (b:=1764) (join_sums term (lo:=859397) (a:=882) (b:=882) (join_sums term (lo:=859397) (a:=441) (b:=441) r859397 r859838) (join_sums term (lo:=860279) (a:=441) (b:=441) r860279 r860720)) (join_sums term (lo:=861161) (a:=882) (b:=882) (join_sums term (lo:=861161) (a:=441) (b:=441) r861161 r861602) (join_sums term (lo:=862043) (a:=441) (b:=441) r862043 r862484))) (join_sums term (lo:=862925) (a:=1764) (b:=1765) (join_sums term (lo:=862925) (a:=882) (b:=882) (join_sums term (lo:=862925) (a:=441) (b:=441) r862925 r863366) (join_sums term (lo:=863807) (a:=441) (b:=441) r863807 r864248)) (join_sums term (lo:=864689) (a:=882) (b:=883) (join_sums term (lo:=864689) (a:=441) (b:=441) r864689 r865130) (join_sums term (lo:=865571) (a:=441) (b:=442) r865571 r866012)))))))

private theorem rows : blockSum term 0 866454 8842639463 :=
  join_sums term (lo:=0) (a:=810001) (b:=56453) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 866453).filter (810000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=8842639463 :=
  right_from_blocks (l:=34751024) (b:=67545646) (small:=4775000)
    RangePrimeA26.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (RangePrimeA26.fast_correct RankWheel34751.first_anchor)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From810000To866453
