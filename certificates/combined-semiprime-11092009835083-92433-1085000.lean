import certificates.«semiprime-correction-11092009835083-92433-117892»
import certificates.«combined-semiprime-11092009835083-117892-860000»
import certificates.«semiprime-correction-11092009835083-860000-975000»
import certificates.«semiprime-correction-11092009835083-975000-1085000»

/-!
# Semiprime correction from 92,433 through 1,085,000 at 11,092,009,835,083

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined11092009835083From92433To1085000

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

private theorem until860000 : (∑ p ∈ (Nat.primesLE 860000).filter (92433 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=117888385809 :=
  join_value (y:=92433) (m:=117892) (z:=860000) (a:=13344017255) (b:=104544368554) (c:=117888385809)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction11092009835083From92433To117892.interval_sum Combined11092009835083From117892To860000.interval_sum rfl

private theorem until975000 : (∑ p ∈ (Nat.primesLE 975000).filter (92433 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=123942567413 :=
  join_value (y:=92433) (m:=860000) (z:=975000) (a:=117888385809) (b:=6054181604) (c:=123942567413)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until860000 Correction11092009835083From860000To975000.interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 1085000).filter (92433 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=128942169063 :=
  join_value (y:=92433) (m:=975000) (z:=1085000) (a:=123942567413) (b:=4999601650) (c:=128942169063)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until975000 Correction11092009835083From975000To1085000.interval_sum rfl

end Combined11092009835083From92433To1085000
