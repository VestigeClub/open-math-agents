import certificates.«sieve-change-11092009835083-0-53»
import certificates.«eighth-endpoint-semiprime-correction»

/-!
# The sieve remainder at 30,110,134,441,897

The full semiprime correction leaves the number of integers surviving division by the primes through 31,110. The candidate-index test uses that last number modulo 5.
-/
open Finset
namespace EighthEndpointSieve

abbrev survivors : ℕ := ((Icc 1 30110134441897).filter
    (fun n => ∀ p ∈ Nat.primesLE 31110, ¬ p ∣ n)).card

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

private lemma small_count : (Nat.primesLE 31110).card = 3350 := by
  rw [Nat.primesLE_card_eq_primeCounting,
    ← FastDenseA26.fast_correct 31110 (by decide)]
  decide +kernel

private lemma translate (r p : ℕ) (h : r + 3350 = 1+p+642072173249) :
    (p % 5 = 3 ↔ r % 5 = 3) ∧ (p = 1003670521508 ↔ r = 1645742691408) := by omega

def criterion (x y : ℕ) : Prop :=
    let r := ((Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card
    r+3350 = 1+Nat.primeCounting x+642072173249 ∧
      (Nat.primeCounting x % 5 = 3 ↔ r % 5 = 3) ∧
      (Nat.primeCounting x = 1003670521508 ↔ r = 1645742691408)

private lemma assemble {x y z : ℕ} (hx : 1 ≤ x) (hy : y ≤ x)
    (cube : x < (y+1)^3) (top : x < (z+1)^2) (bottom : z*z ≤ x)
    (sk : (Nat.primesLE y).card=3350)
    (sb : (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p)-Nat.primeCounting (p-1)))=642072173249) :
    criterion x y := by
  unfold criterion
  have h := partition_at hx hy cube top bottom
  rw [sk,sb] at h
  exact ⟨h,translate _ _ h⟩

theorem prime_count_and_residue : criterion 30110134441897 31110 :=
  assemble (x:=30110134441897) (y:=31110) (z:=5487270)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    small_count EighthSemiprimeCorrection.total

end EighthEndpointSieve
