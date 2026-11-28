import certificates.«semiprime-correction-11092009835083-22301-22408»
import certificates.«semiprime-correction-11092009835083-22408-23600»
import certificates.«semiprime-correction-11092009835083-23600-24925»
import certificates.«semiprime-correction-11092009835083-24925-26409»
import certificates.«semiprime-correction-11092009835083-26409-28081»
import certificates.«semiprime-correction-11092009835083-28081-29978»
import certificates.«semiprime-correction-11092009835083-29978-32150»
import certificates.«semiprime-correction-11092009835083-32150-34662»
import certificates.«combined-semiprime-11092009835083-34662-3330466»

/-!
# Semiprime correction from 22,301 through 3,330,466 at 11,092,009,835,083

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined11092009835083From22301To3330466

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

private theorem until23600 : (∑ p ∈ (Nat.primesLE 23600).filter (22301 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=3241216739 :=
  join_value (y:=22301) (m:=22408) (z:=23600) (a:=235449350) (b:=3005767389) (c:=3241216739)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction11092009835083From22301To22408.interval_sum Correction11092009835083From22408To23600.interval_sum rfl

private theorem until24925 : (∑ p ∈ (Nat.primesLE 24925).filter (22301 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=6393724838 :=
  join_value (y:=22301) (m:=23600) (z:=24925) (a:=3241216739) (b:=3152508099) (c:=6393724838)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until23600 Correction11092009835083From23600To24925.interval_sum rfl

private theorem until26409 : (∑ p ∈ (Nat.primesLE 26409).filter (22301 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=9743865830 :=
  join_value (y:=22301) (m:=24925) (z:=26409) (a:=6393724838) (b:=3350140992) (c:=9743865830)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until24925 Correction11092009835083From24925To26409.interval_sum rfl

private theorem until28081 : (∑ p ∈ (Nat.primesLE 28081).filter (22301 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=13258311870 :=
  join_value (y:=22301) (m:=26409) (z:=28081) (a:=9743865830) (b:=3514446040) (c:=13258311870)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until26409 Correction11092009835083From26409To28081.interval_sum rfl

private theorem until29978 : (∑ p ∈ (Nat.primesLE 29978).filter (22301 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=16939645625 :=
  join_value (y:=22301) (m:=28081) (z:=29978) (a:=13258311870) (b:=3681333755) (c:=16939645625)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until28081 Correction11092009835083From28081To29978.interval_sum rfl

private theorem until32150 : (∑ p ∈ (Nat.primesLE 32150).filter (22301 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=20889229858 :=
  join_value (y:=22301) (m:=29978) (z:=32150) (a:=16939645625) (b:=3949584233) (c:=20889229858)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until29978 Correction11092009835083From29978To32150.interval_sum rfl

private theorem until34662 : (∑ p ∈ (Nat.primesLE 34662).filter (22301 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=25401047430 :=
  join_value (y:=22301) (m:=32150) (z:=34662) (a:=20889229858) (b:=4511817572) (c:=25401047430)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until32150 Correction11092009835083From32150To34662.interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 3330466).filter (22301 < ·),
    (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=243665434375 :=
  join_value (y:=22301) (m:=34662) (z:=3330466) (a:=25401047430) (b:=218264386945) (c:=243665434375)
    (fun p => Nat.primeCounting (11092009835083/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until34662 Combined11092009835083From34662To3330466.interval_sum rfl

end Combined11092009835083From22301To3330466
