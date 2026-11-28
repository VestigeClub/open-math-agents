import certificates.«prime-table-320000000-345000000»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 32,150 through 34,662

The sum covers 252 primes. Their quotient counts are checked by the
certified prime-counting table through 345,000,000.
-/
open Finset
namespace Correction11092009835083From32150To34662

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


private abbrev term := contribution 11092009835083 32150 RangePrimeQ320000000To345000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 32151 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 32150 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r32151 : blockSum term 32151 628 1176641504 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r32779 : blockSum term 32779 628 1155282770 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r33407 : blockSum term 33407 628 1135015375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r34035 : blockSum term 34035 628 1044877923 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 32151 2512 4511817572 := (join_sums term (lo:=32151) (a:=1256) (b:=1256) (join_sums term (lo:=32151) (a:=628) (b:=628) r32151 r32779) (join_sums term (lo:=33407) (a:=628) (b:=628) r33407 r34035))

private theorem rows : blockSum term 0 34663 4511817572 :=
  join_sums term (lo:=0) (a:=32151) (b:=2512) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 34662).filter (32150 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=4511817572 :=
  right_from_blocks (l:=320000000) (b:=345000000) (small:=745089)
    RangePrimeQ320000000To345000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ320000000To345000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From32150To34662
