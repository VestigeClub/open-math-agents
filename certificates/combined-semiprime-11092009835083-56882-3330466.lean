import certificates.«semiprime-correction-11092009835083-56882-65247»
import certificates.«combined-semiprime-11092009835083-65247-3330466»

/-!
# Semiprime correction from 56,882 through 3,330,466 at 11,092,009,835,083

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined11092009835083From56882To3330466

private theorem split_primes {y m z : ℕ} (ym : y ≤ m) (mz : m ≤ z) (f : ℕ → ℕ) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·), f p) =
    (∑ p ∈ (Nat.primesLE m).filter (y < ·), f p) +
    (∑ p ∈ (Nat.primesLE z).filter (m < ·), f p) := by
  have un : (Nat.primesLE z).filter (y < ·) =
      (Nat.primesLE m).filter (y < ·) ∪ (Nat.primesLE z).filter (m < ·) := by
    ext p
    simp only [Finset.mem_union,Finset.mem_filter,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨top,prime⟩,above⟩
      by_cases left : p ≤ m
      · exact Or.inl ⟨⟨left,prime⟩,above⟩
      · exact Or.inr ⟨⟨top,prime⟩,by omega⟩
    · rintro (⟨⟨top,prime⟩,above⟩ | ⟨⟨top,prime⟩,above⟩)
      · exact ⟨⟨top.trans mz,prime⟩,above⟩
      · exact ⟨⟨top,prime⟩,lt_of_le_of_lt ym above⟩
  have dis : Disjoint ((Nat.primesLE m).filter (y < ·)) ((Nat.primesLE z).filter (m < ·)) := by
    apply Finset.disjoint_left.mpr
    intro p lower upper
    exact (not_lt_of_ge (Nat.le_of_mem_primesLE (Finset.mem_filter.mp lower).1))
      (Finset.mem_filter.mp upper).2
  rw [un,Finset.sum_union dis]

private theorem join_value {y m z a b c : ℕ} (f : ℕ → ℕ) (ym : y ≤ m) (mz : m ≤ z)
    (left : (∑ p ∈ (Nat.primesLE m).filter (y < ·), f p)=a)
    (right : (∑ p ∈ (Nat.primesLE z).filter (m < ·), f p)=b) (total : a+b=c) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·), f p)=c := by
  rw [split_primes ym mz f,left,right,total]

theorem interval_sum : (∑ p ∈ (Nat.primesLE 3330466).filter (56882 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=190305333277 :=
  join_value (y:=56882) (m:=65247) (z:=3330466) (a:=7622751902) (b:=182682581375) (c:=190305333277)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction11092009835083From56882To65247.interval_sum Combined11092009835083From65247To3330466.interval_sum rfl

end Combined11092009835083From56882To3330466
