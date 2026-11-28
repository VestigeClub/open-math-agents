import certificates.«semiprime-correction-30110134441897-900000-990000»
import certificates.«semiprime-correction-30110134441897-990000-1090000»
import certificates.«semiprime-correction-30110134441897-1090000-1190000»
import certificates.«semiprime-correction-30110134441897-1190000-1290000»
import certificates.«semiprime-correction-30110134441897-1290000-1390000»
import certificates.«semiprime-correction-30110134441897-1390000-1490000»
import certificates.«semiprime-correction-30110134441897-1490000-1590000»
import certificates.«semiprime-correction-30110134441897-1590000-1690000»
import certificates.«semiprime-correction-30110134441897-1690000-1790000»
import certificates.«semiprime-correction-30110134441897-1790000-1890000»
import certificates.«combined-semiprime-30110134441897-1890000-5487270»

/-!
# Semiprime correction from 900,000 through 5,487,270 at 30,110,134,441,897

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined30110134441897From900000To5487270

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

private theorem until1090000 : (∑ p ∈ (Nat.primesLE 1090000).filter (900000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=24674366117 :=
  join_value (y:=900000) (m:=990000) (z:=1090000) (a:=12311571924) (b:=12362794193) (c:=24674366117)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction30110134441897From900000To990000.interval_sum Correction30110134441897From990000To1090000.interval_sum rfl

private theorem until1190000 : (∑ p ∈ (Nat.primesLE 1190000).filter (900000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=35990611182 :=
  join_value (y:=900000) (m:=1090000) (z:=1190000) (a:=24674366117) (b:=11316245065) (c:=35990611182)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until1090000 Correction30110134441897From1090000To1190000.interval_sum rfl

private theorem until1290000 : (∑ p ∈ (Nat.primesLE 1290000).filter (900000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=46142751316 :=
  join_value (y:=900000) (m:=1190000) (z:=1290000) (a:=35990611182) (b:=10152140134) (c:=46142751316)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until1190000 Correction30110134441897From1190000To1290000.interval_sum rfl

private theorem until1390000 : (∑ p ∈ (Nat.primesLE 1390000).filter (900000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=55414689729 :=
  join_value (y:=900000) (m:=1290000) (z:=1390000) (a:=46142751316) (b:=9271938413) (c:=55414689729)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until1290000 Correction30110134441897From1290000To1390000.interval_sum rfl

private theorem until1490000 : (∑ p ∈ (Nat.primesLE 1490000).filter (900000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=64009617682 :=
  join_value (y:=900000) (m:=1390000) (z:=1490000) (a:=55414689729) (b:=8594927953) (c:=64009617682)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until1390000 Correction30110134441897From1390000To1490000.interval_sum rfl

private theorem until1590000 : (∑ p ∈ (Nat.primesLE 1590000).filter (900000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=71894378691 :=
  join_value (y:=900000) (m:=1490000) (z:=1590000) (a:=64009617682) (b:=7884761009) (c:=71894378691)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until1490000 Correction30110134441897From1490000To1590000.interval_sum rfl

private theorem until1690000 : (∑ p ∈ (Nat.primesLE 1690000).filter (900000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=79214863918 :=
  join_value (y:=900000) (m:=1590000) (z:=1690000) (a:=71894378691) (b:=7320485227) (c:=79214863918)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until1590000 Correction30110134441897From1590000To1690000.interval_sum rfl

private theorem until1790000 : (∑ p ∈ (Nat.primesLE 1790000).filter (900000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=86000912349 :=
  join_value (y:=900000) (m:=1690000) (z:=1790000) (a:=79214863918) (b:=6786048431) (c:=86000912349)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until1690000 Correction30110134441897From1690000To1790000.interval_sum rfl

private theorem until1890000 : (∑ p ∈ (Nat.primesLE 1890000).filter (900000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=92389863912 :=
  join_value (y:=900000) (m:=1790000) (z:=1890000) (a:=86000912349) (b:=6388951563) (c:=92389863912)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until1790000 Correction30110134441897From1790000To1890000.interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 5487270).filter (900000 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=173205418620 :=
  join_value (y:=900000) (m:=1890000) (z:=5487270) (a:=92389863912) (b:=80815554708) (c:=173205418620)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until1890000 Combined30110134441897From1890000To5487270.interval_sum rfl

end Combined30110134441897From900000To5487270
