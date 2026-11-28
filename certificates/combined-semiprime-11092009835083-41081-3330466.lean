import certificates.«semiprime-correction-11092009835083-41081-45273»
import certificates.«semiprime-correction-11092009835083-45273-50418»
import certificates.«combined-semiprime-11092009835083-50418-3330466»

/-!
# Semiprime correction from 41,081 through 3,330,466 at 11,092,009,835,083

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined11092009835083From41081To3330466

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

private theorem until50418 : (∑ p ∈ (Nat.primesLE 50418).filter (41081 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=11653521264 :=
  join_value (y:=41081) (m:=45273) (z:=50418) (a:=5566954493) (b:=6086566771) (c:=11653521264)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction11092009835083From41081To45273.interval_sum Correction11092009835083From45273To50418.interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 3330466).filter (41081 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=208726644868 :=
  join_value (y:=41081) (m:=50418) (z:=3330466) (a:=11653521264) (b:=197073123604) (c:=208726644868)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until50418 Combined11092009835083From50418To3330466.interval_sum rfl

end Combined11092009835083From41081To3330466
