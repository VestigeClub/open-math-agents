import certificates.«semiprime-correction-11092009835083-117892-164215»
import certificates.«combined-semiprime-11092009835083-164215-560000»
import certificates.«semiprime-correction-11092009835083-560000-745089»
import certificates.«semiprime-correction-11092009835083-745089-860000»

/-!
# Semiprime correction from 117,892 through 860,000 at 11,092,009,835,083

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined11092009835083From117892To860000

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

private theorem until560000 : (∑ p ∈ (Nat.primesLE 560000).filter (117892 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=83025206787 :=
  join_value (y:=117892) (m:=164215) (z:=560000) (a:=18070677898) (b:=64954528889) (c:=83025206787)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction11092009835083From117892To164215.interval_sum Combined11092009835083From164215To560000.interval_sum rfl

private theorem until745089 : (∑ p ∈ (Nat.primesLE 745089).filter (117892 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=97466456407 :=
  join_value (y:=117892) (m:=560000) (z:=745089) (a:=83025206787) (b:=14441249620) (c:=97466456407)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until560000 Correction11092009835083From560000To745089.interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 860000).filter (117892 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=104544368554 :=
  join_value (y:=117892) (m:=745089) (z:=860000) (a:=97466456407) (b:=7077912147) (c:=104544368554)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until745089 Correction11092009835083From745089To860000.interval_sum rfl

end Combined11092009835083From117892To860000
