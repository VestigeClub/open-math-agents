import FormalConjectures.OEIS.«247824»

/-!
# Prime counts measured from one endpoint

A table whose increments detect exactly the primes determines prime-count
differences even when its starting count is unknown. The last two lemmas use
those differences in a sum over a bounded prime interval.
-/
open Finset
namespace RelativeSemiprimeTable

theorem from_increments {table : ℕ → ℕ} {a b v : ℕ}
    (initial : table a = v)
    (step : ∀ n, a ≤ n → n + 1 ≤ b →
      table (n+1) = table n + (if (n+1).Prime then 1 else 0))
    (n : ℕ) (lo : a ≤ n) (hi : n ≤ b) :
    table n + Nat.primeCounting a = Nat.primeCounting n + v := by
  induction n with
  | zero =>
    have h : a=0 := by omega
    subst a
    rw [initial, Nat.add_comm]
  | succ n ih =>
    by_cases h : n+1=a
    · rw [h,initial,Nat.add_comm]
    · have past : a≤n := by omega
      have earlier := ih past (by omega)
      have prime_step : Nat.primeCounting (n+1) =
          Nat.primeCounting n + (if (n+1).Prime then 1 else 0) :=
        Nat.count_succ Nat.Prime (n+1)
      rw [step n past hi,prime_step]
      omega

theorem sum_from_differences {x y z a b v total : ℕ} (table : ℕ → ℕ)
    (ok : ∀ n, a≤n → n≤b → table n + Nat.primeCounting a = Nat.primeCounting n + v)
    (before : z≤v) (bottom : a≤x/z) (top : x/(y+1)≤b)
    (blocks : (∑ p ∈ (Nat.primesLE z).filter (y<·),
      (table (x/p) - Nat.primeCounting (p-1))) = total) :
    (∑ p ∈ (Nat.primesLE z).filter (y<·),
      ((Nat.primeCounting (x/p)-Nat.primeCounting a) + (v-Nat.primeCounting (p-1)))) = total := by
  rw [←blocks]
  apply Finset.sum_congr rfl
  intro p member
  obtain ⟨in_range, large⟩ := Finset.mem_filter.mp member
  obtain ⟨bound, prime⟩ := Nat.mem_primesLE.mp in_range
  have low := bottom.trans (Nat.div_le_div_left bound prime.pos)
  have high := (Nat.div_le_div_left (show y+1≤p by omega) (Nat.succ_pos y)).trans top
  have known := ok (x/p) low high
  have ordered := Nat.monotone_primeCounting low
  have prior : Nat.primeCounting (p-1)≤p-1+1 := Nat.count_le Nat.Prime
  omega

theorem absolute_from_differences {x y z a v total : ℕ}
    (initial : Nat.primeCounting a=v) (before : z≤v) (bottom : a≤x/z)
    (blocks : (∑ p ∈ (Nat.primesLE z).filter (y<·),
      ((Nat.primeCounting (x/p)-Nat.primeCounting a) + (v-Nat.primeCounting (p-1)))) = total) :
    (∑ p ∈ (Nat.primesLE z).filter (y<·),
      (Nat.primeCounting (x/p)-Nat.primeCounting (p-1))) = total := by
  rw [←blocks]
  apply Finset.sum_congr rfl
  intro p member
  obtain ⟨in_range, _⟩ := Finset.mem_filter.mp member
  obtain ⟨bound, prime⟩ := Nat.mem_primesLE.mp in_range
  have low := bottom.trans (Nat.div_le_div_left bound prime.pos)
  have ordered := Nat.monotone_primeCounting low
  have prior : Nat.primeCounting (p-1)≤p-1+1 := Nat.count_le Nat.Prime
  omega

end RelativeSemiprimeTable
