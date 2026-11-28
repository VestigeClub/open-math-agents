import certificates.«prime-table-245000000-270000000»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 41,081 through 45,273

The sum covers 396 primes. Their quotient counts are checked by the
certified prime-counting table through 270,000,000.
-/
open Finset
namespace Correction11092009835083From41081To45273

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


private abbrev term := contribution 11092009835083 41081 RangePrimeQ245000000To270000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 41082 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 41081 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r41082 : blockSum term 41082 524 731024746 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r41606 : blockSum term 41606 524 765839074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r42130 : blockSum term 42130 524 785466439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r42654 : blockSum term 42654 524 720048870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r43178 : blockSum term 43178 524 599680946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r43702 : blockSum term 43702 524 703232167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r44226 : blockSum term 44226 524 640930770 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r44750 : blockSum term 44750 524 620731481 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 41082 4192 5566954493 := (join_sums term (lo:=41082) (a:=2096) (b:=2096) (join_sums term (lo:=41082) (a:=1048) (b:=1048) (join_sums term (lo:=41082) (a:=524) (b:=524) r41082 r41606) (join_sums term (lo:=42130) (a:=524) (b:=524) r42130 r42654)) (join_sums term (lo:=43178) (a:=1048) (b:=1048) (join_sums term (lo:=43178) (a:=524) (b:=524) r43178 r43702) (join_sums term (lo:=44226) (a:=524) (b:=524) r44226 r44750)))

private theorem rows : blockSum term 0 45274 5566954493 :=
  join_sums term (lo:=0) (a:=41082) (b:=4192) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 45273).filter (41081 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=5566954493 :=
  right_from_blocks (l:=245000000) (b:=270000000) (small:=745089)
    RangePrimeQ245000000To270000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ245000000To270000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From41081To45273
