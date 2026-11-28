import certificates.«semiprime-correction-30110134441897-445774-530000»
import certificates.«semiprime-correction-30110134441897-530000-610000»
import certificates.«semiprime-correction-30110134441897-610000-690000»
import certificates.«semiprime-correction-30110134441897-690000-745089»
import certificates.«semiprime-correction-30110134441897-745089-810000»
import certificates.«semiprime-correction-30110134441897-810000-866453»
import certificates.«semiprime-correction-30110134441897-866453-900000»
import certificates.«combined-semiprime-30110134441897-900000-5487270»

/-!
# Semiprime correction from 445,774 through 5,487,270 at 30,110,134,441,897

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined30110134441897From445774To5487270

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

private theorem until610000 : (∑ p ∈ (Nat.primesLE 610000).filter (445774 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=42104328218 :=
  join_value (y:=445774) (m:=530000) (z:=610000) (a:=23287672387) (b:=18816655831) (c:=42104328218)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction30110134441897From445774To530000.interval_sum Correction30110134441897From530000To610000.interval_sum rfl

private theorem until690000 : (∑ p ∈ (Nat.primesLE 690000).filter (445774 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=58436945917 :=
  join_value (y:=445774) (m:=610000) (z:=690000) (a:=42104328218) (b:=16332617699) (c:=58436945917)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until610000 Correction30110134441897From610000To690000.interval_sum rfl

private theorem until745089 : (∑ p ∈ (Nat.primesLE 745089).filter (445774 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=68563041047 :=
  join_value (y:=445774) (m:=690000) (z:=745089) (a:=58436945917) (b:=10126095130) (c:=68563041047)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until690000 Correction30110134441897From690000To745089.interval_sum rfl

private theorem until810000 : (∑ p ∈ (Nat.primesLE 810000).filter (445774 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=79601581095 :=
  join_value (y:=445774) (m:=745089) (z:=810000) (a:=68563041047) (b:=11038540048) (c:=79601581095)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until745089 Correction30110134441897From745089To810000.interval_sum rfl

private theorem until866453 : (∑ p ∈ (Nat.primesLE 866453).filter (445774 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=88444220558 :=
  join_value (y:=445774) (m:=810000) (z:=866453) (a:=79601581095) (b:=8842639463) (c:=88444220558)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until810000 Correction30110134441897From810000To866453.interval_sum rfl

private theorem until900000 : (∑ p ∈ (Nat.primesLE 900000).filter (445774 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=93399347436 :=
  join_value (y:=445774) (m:=866453) (z:=900000) (a:=88444220558) (b:=4955126878) (c:=93399347436)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until866453 Correction30110134441897From866453To900000.interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 5487270).filter (445774 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=266604766056 :=
  join_value (y:=445774) (m:=900000) (z:=5487270) (a:=93399347436) (b:=173205418620) (c:=266604766056)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until900000 Combined30110134441897From900000To5487270.interval_sum rfl

end Combined30110134441897From445774To5487270
