import certificates.«semiprime-correction-11092009835083-164215-240000»
import certificates.«semiprime-correction-11092009835083-240000-319185»
import certificates.«semiprime-correction-11092009835083-319185-430000»
import certificates.«semiprime-correction-11092009835083-430000-560000»

/-!
# Semiprime correction from 164,215 through 560,000 at 11,092,009,835,083

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined11092009835083From164215To560000

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

private theorem until319185 : (∑ p ∈ (Nat.primesLE 319185).filter (164215 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=35606664142 :=
  join_value (y:=164215) (m:=240000) (z:=319185) (a:=20399199082) (b:=15207465060) (c:=35606664142)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction11092009835083From164215To240000.interval_sum Correction11092009835083From240000To319185.interval_sum rfl

private theorem until430000 : (∑ p ∈ (Nat.primesLE 430000).filter (164215 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=51273666232 :=
  join_value (y:=164215) (m:=319185) (z:=430000) (a:=35606664142) (b:=15667002090) (c:=51273666232)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until319185 Correction11092009835083From319185To430000.interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 560000).filter (164215 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=64954528889 :=
  join_value (y:=164215) (m:=430000) (z:=560000) (a:=51273666232) (b:=13680862657) (c:=64954528889)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until430000 Correction11092009835083From430000To560000.interval_sum rfl

end Combined11092009835083From164215To560000
