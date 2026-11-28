import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 866,453 through 900,000

The sum covers 2,447 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From866453To900000

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


private abbrev term := contribution 30110134441897 866453 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 866454 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 866453 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r866454 : blockSum term 866454 524 76327380 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r866978 : blockSum term 866978 524 84529606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r867502 : blockSum term 867502 524 78300761 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r868026 : blockSum term 868026 524 86487618 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r868550 : blockSum term 868550 524 88492820 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r869074 : blockSum term 869074 524 82270159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r869598 : blockSum term 869598 524 73999117 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r870122 : blockSum term 870122 525 88336642 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r870647 : blockSum term 870647 524 73910723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r871171 : blockSum term 871171 524 65656892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r871695 : blockSum term 871695 524 75869188 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r872219 : blockSum term 872219 524 88124606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r872743 : blockSum term 872743 524 61443291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r873267 : blockSum term 873267 524 83920909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r873791 : blockSum term 873791 524 61365774 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r874315 : blockSum term 874315 525 85864615 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r874840 : blockSum term 874840 524 79681953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r875364 : blockSum term 875364 524 87805937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r875888 : blockSum term 875888 524 87753397 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r876412 : blockSum term 876412 524 77502134 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r876936 : blockSum term 876936 524 73378620 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r877460 : blockSum term 877460 524 65188074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r877984 : blockSum term 877984 524 79404382 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r878508 : blockSum term 878508 525 89527541 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r879033 : blockSum term 879033 524 73206874 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r879557 : blockSum term 879557 524 89422128 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r880081 : blockSum term 880081 524 81242813 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r880605 : blockSum term 880605 525 81195607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r881130 : blockSum term 881130 524 81150616 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r881654 : blockSum term 881654 524 68934235 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r882178 : blockSum term 882178 524 74974342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r882702 : blockSum term 882702 525 72904494 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r883227 : blockSum term 883227 524 87030064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r883751 : blockSum term 883751 524 72816140 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r884275 : blockSum term 884275 524 68734893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r884799 : blockSum term 884799 524 76772382 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r885323 : blockSum term 885323 524 74708890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r885847 : blockSum term 885847 524 86774213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r886371 : blockSum term 886371 524 78655996 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r886895 : blockSum term 886895 525 72562916 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r887420 : blockSum term 887420 524 84606698 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r887944 : blockSum term 887944 524 80528069 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r888468 : blockSum term 888468 524 78468577 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r888992 : blockSum term 888992 525 76412716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r889517 : blockSum term 889517 524 68326536 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r890041 : blockSum term 890041 524 66280276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r890565 : blockSum term 890565 524 76274022 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r891089 : blockSum term 891089 525 82247461 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r891614 : blockSum term 891614 524 86211100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r892138 : blockSum term 892138 524 74136265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r892662 : blockSum term 892662 524 80098654 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r893186 : blockSum term 893186 524 70047411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r893710 : blockSum term 893710 524 82002401 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r894234 : blockSum term 894234 524 77960667 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r894758 : blockSum term 894758 524 69921070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r895282 : blockSum term 895282 525 89847051 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r895807 : blockSum term 895807 524 65850633 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r896331 : blockSum term 896331 524 69802828 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r896855 : blockSum term 896855 524 79724642 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r897379 : blockSum term 897379 525 77686207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r897904 : blockSum term 897904 524 83611417 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r898428 : blockSum term 898428 524 73617046 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r898952 : blockSum term 898952 524 61642629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r899476 : blockSum term 899476 525 63593760 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 866454 33547 4955126878 := (join_sums term (lo:=866454) (a:=16773) (b:=16774) (join_sums term (lo:=866454) (a:=8386) (b:=8387) (join_sums term (lo:=866454) (a:=4193) (b:=4193) (join_sums term (lo:=866454) (a:=2096) (b:=2097) (join_sums term (lo:=866454) (a:=1048) (b:=1048) (join_sums term (lo:=866454) (a:=524) (b:=524) r866454 r866978) (join_sums term (lo:=867502) (a:=524) (b:=524) r867502 r868026)) (join_sums term (lo:=868550) (a:=1048) (b:=1049) (join_sums term (lo:=868550) (a:=524) (b:=524) r868550 r869074) (join_sums term (lo:=869598) (a:=524) (b:=525) r869598 r870122))) (join_sums term (lo:=870647) (a:=2096) (b:=2097) (join_sums term (lo:=870647) (a:=1048) (b:=1048) (join_sums term (lo:=870647) (a:=524) (b:=524) r870647 r871171) (join_sums term (lo:=871695) (a:=524) (b:=524) r871695 r872219)) (join_sums term (lo:=872743) (a:=1048) (b:=1049) (join_sums term (lo:=872743) (a:=524) (b:=524) r872743 r873267) (join_sums term (lo:=873791) (a:=524) (b:=525) r873791 r874315)))) (join_sums term (lo:=874840) (a:=4193) (b:=4194) (join_sums term (lo:=874840) (a:=2096) (b:=2097) (join_sums term (lo:=874840) (a:=1048) (b:=1048) (join_sums term (lo:=874840) (a:=524) (b:=524) r874840 r875364) (join_sums term (lo:=875888) (a:=524) (b:=524) r875888 r876412)) (join_sums term (lo:=876936) (a:=1048) (b:=1049) (join_sums term (lo:=876936) (a:=524) (b:=524) r876936 r877460) (join_sums term (lo:=877984) (a:=524) (b:=525) r877984 r878508))) (join_sums term (lo:=879033) (a:=2097) (b:=2097) (join_sums term (lo:=879033) (a:=1048) (b:=1049) (join_sums term (lo:=879033) (a:=524) (b:=524) r879033 r879557) (join_sums term (lo:=880081) (a:=524) (b:=525) r880081 r880605)) (join_sums term (lo:=881130) (a:=1048) (b:=1049) (join_sums term (lo:=881130) (a:=524) (b:=524) r881130 r881654) (join_sums term (lo:=882178) (a:=524) (b:=525) r882178 r882702))))) (join_sums term (lo:=883227) (a:=8387) (b:=8387) (join_sums term (lo:=883227) (a:=4193) (b:=4194) (join_sums term (lo:=883227) (a:=2096) (b:=2097) (join_sums term (lo:=883227) (a:=1048) (b:=1048) (join_sums term (lo:=883227) (a:=524) (b:=524) r883227 r883751) (join_sums term (lo:=884275) (a:=524) (b:=524) r884275 r884799)) (join_sums term (lo:=885323) (a:=1048) (b:=1049) (join_sums term (lo:=885323) (a:=524) (b:=524) r885323 r885847) (join_sums term (lo:=886371) (a:=524) (b:=525) r886371 r886895))) (join_sums term (lo:=887420) (a:=2097) (b:=2097) (join_sums term (lo:=887420) (a:=1048) (b:=1049) (join_sums term (lo:=887420) (a:=524) (b:=524) r887420 r887944) (join_sums term (lo:=888468) (a:=524) (b:=525) r888468 r888992)) (join_sums term (lo:=889517) (a:=1048) (b:=1049) (join_sums term (lo:=889517) (a:=524) (b:=524) r889517 r890041) (join_sums term (lo:=890565) (a:=524) (b:=525) r890565 r891089)))) (join_sums term (lo:=891614) (a:=4193) (b:=4194) (join_sums term (lo:=891614) (a:=2096) (b:=2097) (join_sums term (lo:=891614) (a:=1048) (b:=1048) (join_sums term (lo:=891614) (a:=524) (b:=524) r891614 r892138) (join_sums term (lo:=892662) (a:=524) (b:=524) r892662 r893186)) (join_sums term (lo:=893710) (a:=1048) (b:=1049) (join_sums term (lo:=893710) (a:=524) (b:=524) r893710 r894234) (join_sums term (lo:=894758) (a:=524) (b:=525) r894758 r895282))) (join_sums term (lo:=895807) (a:=2097) (b:=2097) (join_sums term (lo:=895807) (a:=1048) (b:=1049) (join_sums term (lo:=895807) (a:=524) (b:=524) r895807 r896331) (join_sums term (lo:=896855) (a:=524) (b:=525) r896855 r897379)) (join_sums term (lo:=897904) (a:=1048) (b:=1049) (join_sums term (lo:=897904) (a:=524) (b:=524) r897904 r898428) (join_sums term (lo:=898952) (a:=524) (b:=525) r898952 r899476))))))

private theorem rows : blockSum term 0 900001 4955126878 :=
  join_sums term (lo:=0) (a:=866454) (b:=33547) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 900000).filter (866453 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4955126878 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From866453To900000
