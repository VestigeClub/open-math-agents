import certificates.«sieve-change-11092009835083-0-53»
import certificates.«combined-semiprime-11092009835083-22301-3330466»

/-!
# The sieve remainder at 11,092,009,835,083

The exact semiprime correction leaves one count of survivors after sieving by
the primes through 22,301. For the candidate-index test this count is only
needed modulo 9.
-/
open Finset
namespace SeventhEndpointSieve

abbrev survivors : ℕ := ((Icc 1 11092009835083).filter
    (fun n => ∀ p ∈ Nat.primesLE 22301, ¬ p ∣ n)).card

private lemma partition_at {x y z : ℕ} (hx : 1 ≤ x) (hy : y ≤ x)
    (cube : x < (y+1)^3) (top : x < (z+1)^2) (bottom : z*z ≤ x) :
    ((Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card + (Nat.primesLE y).card =
      1 + Nat.primeCounting x + ∑ p ∈ (Nat.primesLE z).filter (y < ·),
        (Nat.primeCounting (x/p)-Nat.primeCounting (p-1)) := by
  have h := SieveA29From0To16.meissel hx hy cube top
  have row (p : ℕ) (hp : p ∈ (Nat.primesLE z).filter (y < ·)) := by
    have bound := Nat.le_of_mem_primesLE (mem_filter.mp hp).1
    have pos := (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1).pos
    exact SieveA29From0To16.prime_row pos
      ((Nat.le_div_iff_mul_le pos).mpr ((Nat.mul_le_mul bound bound).trans bottom))
  rw [sum_congr rfl row,Nat.primesLE_card_eq_primeCounting x] at h
  exact h

private lemma small_count : (Nat.primesLE 22301).card = 2498 := by
  rw [Nat.primesLE_card_eq_primeCounting,
    ← Sieve11092009835083From0To53.FastDenseControl.fast_correct 22301 (by decide)]
  decide +kernel

private lemma translate (r p : ℕ) (h : r + 2498 = 1+p+243665434375) :
    (p % 9 = 7 ↔ r % 9 = 1) ∧ (p = 382482495196 ↔ r = 626147927074) := by omega

def criterion (x y : ℕ) : Prop :=
    let r := ((Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card
    r+2498 = 1+Nat.primeCounting x+243665434375 ∧
      (Nat.primeCounting x % 9 = 7 ↔ r % 9 = 1) ∧
      (Nat.primeCounting x = 382482495196 ↔ r = 626147927074)

private lemma assemble {x y z : ℕ} (hx : 1 ≤ x) (hy : y ≤ x)
    (cube : x < (y+1)^3) (top : x < (z+1)^2) (bottom : z*z ≤ x)
    (sk : (Nat.primesLE y).card=2498)
    (sb : (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p)-Nat.primeCounting (p-1)))=243665434375) :
    criterion x y := by
  unfold criterion
  have h := partition_at hx hy cube top bottom
  rw [sk,sb] at h
  exact ⟨h,translate _ _ h⟩

theorem prime_count_and_residue : criterion 11092009835083 22301 :=
  assemble (x:=11092009835083) (y:=22301) (z:=3330466)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    small_count Combined11092009835083From22301To3330466.interval_sum

end SeventhEndpointSieve
