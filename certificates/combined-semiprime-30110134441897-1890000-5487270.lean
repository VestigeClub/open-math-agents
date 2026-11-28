import certificates.«semiprime-correction-30110134441897-1890000-1990000»
import certificates.«semiprime-correction-30110134441897-1990000-2090000»
import certificates.«semiprime-correction-30110134441897-2090000-2190000»
import certificates.«combined-semiprime-30110134441897-2190000-5487270»

/-!
# Semiprime correction from 1,890,000 through 5,487,270 at 30,110,134,441,897

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined30110134441897From1890000To5487270

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

private theorem until2090000 : (∑ p ∈ (Nat.primesLE 2090000).filter (1890000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=11464983008 :=
  join_value (y:=1890000) (m:=1990000) (z:=2090000) (a:=5901940495) (b:=5563042513) (c:=11464983008)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction30110134441897From1890000To1990000.interval_sum Correction30110134441897From1990000To2090000.interval_sum rfl

private theorem until2190000 : (∑ p ∈ (Nat.primesLE 2190000).filter (1890000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=16656042310 :=
  join_value (y:=1890000) (m:=2090000) (z:=2190000) (a:=11464983008) (b:=5191059302) (c:=16656042310)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until2090000 Correction30110134441897From2090000To2190000.interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 5487270).filter (1890000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=80815554708 :=
  join_value (y:=1890000) (m:=2190000) (z:=5487270) (a:=16656042310) (b:=64159512398) (c:=80815554708)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until2190000 Combined30110134441897From2190000To5487270.interval_sum rfl

end Combined30110134441897From1890000To5487270
