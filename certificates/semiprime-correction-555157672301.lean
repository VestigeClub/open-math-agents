import certificates.«semiprime-correction-555157672301-small»
import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-555157672301-high»

/-!
# The full semiprime correction at 555,157,672,301

The primes above 8,218 through 745,089 are split at 15,975 and 116,263.
The three ranges contribute 2,387,377,753, 6,673,287,648 and 4,397,030,859.
-/
open Finset
namespace Correction555157

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


private theorem below_cut :
    (∑ p ∈ (Nat.primesLE 116263).filter (8218 < ·),
      (Nat.primeCounting (555157672301/p) - Nat.primeCounting (p-1)))=9060665401 :=
  join_value (y:=8218) (m:=15975) (z:=116263) (a:=2387377753) (b:=6673287648)
    (c:=9060665401) (fun p => Nat.primeCounting (555157672301/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) CorrectionSmall26.exact_sum CorrectionMiddle26.exact_sum rfl

theorem exact_sum : (∑ p ∈ (Nat.primesLE 745089).filter (8218 < ·),
    (Nat.primeCounting (555157672301/p) - Nat.primeCounting (p-1)))=13457696260 :=
  join_value (y:=8218) (m:=116263) (z:=745089) (a:=9060665401) (b:=4397030859)
    (c:=13457696260) (fun p => Nat.primeCounting (555157672301/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) below_cut CorrectionHigh26.exact_upper_sum rfl
end Correction555157
