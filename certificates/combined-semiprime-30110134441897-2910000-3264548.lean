import certificates.«semiprime-correction-30110134441897-2910000-3030000»
import certificates.«semiprime-correction-30110134441897-3030000-3150000»
import certificates.«semiprime-correction-30110134441897-3150000-3264548»

/-!
# Semiprime correction from 2,910,000 through 3,264,548 at 30,110,134,441,897

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined30110134441897From2910000To3264548

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

private theorem until3150000 : (∑ p ∈ (Nat.primesLE 3150000).filter (2910000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=7095756451 :=
  join_value (y:=2910000) (m:=3030000) (z:=3150000) (a:=3675810397) (b:=3419946054) (c:=7095756451)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction30110134441897From2910000To3030000.interval_sum Correction30110134441897From3030000To3150000.interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 3264548).filter (2910000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=10149280080 :=
  join_value (y:=2910000) (m:=3150000) (z:=3264548) (a:=7095756451) (b:=3053523629) (c:=10149280080)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until3150000 Correction30110134441897From3150000To3264548.interval_sum rfl

end Combined30110134441897From2910000To3264548
