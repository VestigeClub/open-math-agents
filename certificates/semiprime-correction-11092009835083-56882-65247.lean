import certificates.«prime-table-170000000-195000000»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 56,882 through 65,247

The sum covers 752 primes. Their quotient counts are checked by the
certified prime-counting table through 195,000,000.
-/
open Finset
namespace Correction11092009835083From56882To65247

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


private abbrev term := contribution 11092009835083 56882 RangePrimeQ170000000To195000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 56883 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 56882 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r56883 : blockSum term 56883 522 592173329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r57405 : blockSum term 57405 523 501410174 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r57928 : blockSum term 57928 523 529011950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r58451 : blockSum term 58451 523 440691410 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r58974 : blockSum term 58974 522 572371925 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r59496 : blockSum term 59496 523 454160344 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r60019 : blockSum term 60019 523 460627434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r60542 : blockSum term 60542 523 487235459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r61065 : blockSum term 61065 522 432798301 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r61587 : blockSum term 61587 523 469559997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r62110 : blockSum term 62110 523 445986602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r62633 : blockSum term 62633 523 442444929 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r63156 : blockSum term 63156 523 507079121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r63679 : blockSum term 63679 523 445431358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r64202 : blockSum term 64202 523 403369339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r64725 : blockSum term 64725 523 438400230 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 56883 8365 7622751902 := (join_sums term (lo:=56883) (a:=4182) (b:=4183) (join_sums term (lo:=56883) (a:=2091) (b:=2091) (join_sums term (lo:=56883) (a:=1045) (b:=1046) (join_sums term (lo:=56883) (a:=522) (b:=523) r56883 r57405) (join_sums term (lo:=57928) (a:=523) (b:=523) r57928 r58451)) (join_sums term (lo:=58974) (a:=1045) (b:=1046) (join_sums term (lo:=58974) (a:=522) (b:=523) r58974 r59496) (join_sums term (lo:=60019) (a:=523) (b:=523) r60019 r60542))) (join_sums term (lo:=61065) (a:=2091) (b:=2092) (join_sums term (lo:=61065) (a:=1045) (b:=1046) (join_sums term (lo:=61065) (a:=522) (b:=523) r61065 r61587) (join_sums term (lo:=62110) (a:=523) (b:=523) r62110 r62633)) (join_sums term (lo:=63156) (a:=1046) (b:=1046) (join_sums term (lo:=63156) (a:=523) (b:=523) r63156 r63679) (join_sums term (lo:=64202) (a:=523) (b:=523) r64202 r64725))))

private theorem rows : blockSum term 0 65248 7622751902 :=
  join_sums term (lo:=0) (a:=56883) (b:=8365) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 65247).filter (56882 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=7622751902 :=
  right_from_blocks (l:=170000000) (b:=195000000) (small:=745089)
    RangePrimeQ170000000To195000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ170000000To195000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From56882To65247
