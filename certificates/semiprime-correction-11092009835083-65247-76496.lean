import certificates.«prime-table-145000000-170000000»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 65,247 through 76,496

The sum covers 1,007 primes. Their quotient counts are checked by the
certified prime-counting table through 170,000,000.
-/
open Finset
namespace Correction11092009835083From65247To76496

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


private abbrev term := contribution 11092009835083 65247 RangePrimeQ145000000To170000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 65248 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 65247 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r65248 : blockSum term 65248 703 633070627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r65951 : blockSum term 65951 703 561161721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r66654 : blockSum term 66654 703 592615264 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r67357 : blockSum term 67357 703 632773479 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r68060 : blockSum term 68060 703 508386913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r68763 : blockSum term 68763 703 548598427 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r69466 : blockSum term 69466 703 516467896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r70169 : blockSum term 70169 703 556063783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r70872 : blockSum term 70872 703 638132788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r71575 : blockSum term 71575 703 571404029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r72278 : blockSum term 72278 703 531820584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r72981 : blockSum term 72981 703 501563884 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r73684 : blockSum term 73684 703 530780284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r74387 : blockSum term 74387 703 517874167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r75090 : blockSum term 75090 703 546316633 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r75793 : blockSum term 75793 704 475938287 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 65248 11249 8862968766 := (join_sums term (lo:=65248) (a:=5624) (b:=5625) (join_sums term (lo:=65248) (a:=2812) (b:=2812) (join_sums term (lo:=65248) (a:=1406) (b:=1406) (join_sums term (lo:=65248) (a:=703) (b:=703) r65248 r65951) (join_sums term (lo:=66654) (a:=703) (b:=703) r66654 r67357)) (join_sums term (lo:=68060) (a:=1406) (b:=1406) (join_sums term (lo:=68060) (a:=703) (b:=703) r68060 r68763) (join_sums term (lo:=69466) (a:=703) (b:=703) r69466 r70169))) (join_sums term (lo:=70872) (a:=2812) (b:=2813) (join_sums term (lo:=70872) (a:=1406) (b:=1406) (join_sums term (lo:=70872) (a:=703) (b:=703) r70872 r71575) (join_sums term (lo:=72278) (a:=703) (b:=703) r72278 r72981)) (join_sums term (lo:=73684) (a:=1406) (b:=1407) (join_sums term (lo:=73684) (a:=703) (b:=703) r73684 r74387) (join_sums term (lo:=75090) (a:=703) (b:=704) r75090 r75793))))

private theorem rows : blockSum term 0 76497 8862968766 :=
  join_sums term (lo:=0) (a:=65248) (b:=11249) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 76496).filter (65247 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=8862968766 :=
  right_from_blocks (l:=145000000) (b:=170000000) (small:=745089)
    RangePrimeQ145000000To170000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ145000000To170000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From65247To76496
