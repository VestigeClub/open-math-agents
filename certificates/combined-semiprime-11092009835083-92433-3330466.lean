import certificates.«combined-semiprime-11092009835083-92433-1202598»
import certificates.«semiprime-correction-11092009835083-1202598-2322933-shared»
import certificates.«semiprime-correction-11092009835083-2322933-3330466-shared»

/-!
# Semiprime correction from 92,433 through 3,330,466 at 11,092,009,835,083

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined11092009835083From92433To3330466

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

private theorem until2322933 : (∑ p ∈ (Nat.primesLE 2322933).filter (92433 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=158173573458 :=
  join_value (y:=92433) (m:=1202598) (z:=2322933) (a:=133670572653) (b:=24503000805) (c:=158173573458)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Combined11092009835083From92433To1202598.interval_sum CorrectionNext29.exact_interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 3330466).filter (92433 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=163334952366 :=
  join_value (y:=92433) (m:=2322933) (z:=3330466) (a:=158173573458) (b:=5161378908) (c:=163334952366)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until2322933 CorrectionHigh29.exact_upper_sum rfl

end Combined11092009835083From92433To3330466
