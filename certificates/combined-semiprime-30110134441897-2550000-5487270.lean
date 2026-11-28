import certificates.«semiprime-correction-30110134441897-2550000-2670000»
import certificates.«combined-semiprime-30110134441897-2670000-3264548»
import certificates.«semiprime-correction-30110134441897-3264548-4500000-shared»
import certificates.«semiprime-correction-30110134441897-4500000-5487270-shared»

/-!
# Semiprime correction from 2,550,000 through 5,487,270 at 30,110,134,441,897

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined30110134441897From2550000To5487270

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

private theorem until3264548 : (∑ p ∈ (Nat.primesLE 3264548).filter (2550000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=23061268149 :=
  join_value (y:=2550000) (m:=2670000) (z:=3264548) (a:=4639168756) (b:=18422099393) (c:=23061268149)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction30110134441897From2550000To2670000.interval_sum Combined30110134441897From2670000To3264548.interval_sum rfl

private theorem until4500000 : (∑ p ∈ (Nat.primesLE 4500000).filter (2550000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=43690931903 :=
  join_value (y:=2550000) (m:=3264548) (z:=4500000) (a:=23061268149) (b:=20629663754) (c:=43690931903)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until3264548 CorrectionNext30.exact_interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 5487270).filter (2550000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=48050288588 :=
  join_value (y:=2550000) (m:=4500000) (z:=5487270) (a:=43690931903) (b:=4359356685) (c:=48050288588)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until4500000 CorrectionHigh30.exact_upper_sum rfl

end Combined30110134441897From2550000To5487270
