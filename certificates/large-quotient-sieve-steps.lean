import certificates.«seventh-sieve-last-primes»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Counting a prime removal with a smaller sieve

When a quotient is below the cube of the first permitted factor, each survivor
is one, a prime, or a product of two primes. The two-prime contribution uses
only prime counts up to 745,089.
-/
open Finset
namespace LargeQuotientSieve

private theorem window (y z : ℕ) : (Nat.primesLE z).filter (y < ·) = (Icc (y+1) z).filter Nat.Prime := by
  ext p
  simp only [mem_filter,Nat.mem_primesLE,mem_Icc]
  constructor
  · rintro ⟨⟨top,pr⟩,above⟩
    exact ⟨⟨by omega,top⟩,pr⟩
  · rintro ⟨⟨above,top⟩,pr⟩
    exact ⟨⟨top,pr⟩,by omega⟩

theorem prime_by_flag {p : ℕ} (cap : p≤745089)
    (flag : FastDenseA26.prime p=true) : p.Prime :=
  (FastDenseA26.prime_ok p cap).mp flag

theorem gap_by_flags {y z p : ℕ} (cap : z≤745089)
    (flags : ∀ r ∈ Icc (y+1) z, FastDenseA26.prime r=true → r=p) :
    ∀ r ∈ Icc (y+1) z, r.Prime → r=p := by
  intro r hr pr
  exact flags r hr ((FastDenseA26.prime_ok r ((mem_Icc.mp hr).2.trans cap)).mpr pr)

private abbrev small := FastDenseA26.fast

def pairSum (q y z : ℕ) : ℕ :=
  ∑ r ∈ (Icc (y+1) z).filter (fun r => FastDenseA26.prime r=true), (small (q/r)-small (r-1))

private theorem pair_values (q y z : ℕ) (high : z≤745089) (quot : q/(y+1)≤745089) :
    (∑ r ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (q/r)-Nat.primeCounting (r-1))) = pairSum q y z := by
  rw [window]
  unfold pairSum
  have flags : (Icc (y+1) z).filter Nat.Prime =
      (Icc (y+1) z).filter (fun r => FastDenseA26.prime r=true) := by
    ext r
    simp only [mem_filter]
    constructor
    · rintro ⟨hr,pr⟩
      exact ⟨hr,(FastDenseA26.prime_ok r ((mem_Icc.mp hr).2.trans high)).mpr pr⟩
    · rintro ⟨hr,fl⟩
      exact ⟨hr,prime_by_flag ((mem_Icc.mp hr).2.trans high) fl⟩
  rw [flags]
  apply sum_congr rfl
  intro r hr
  obtain ⟨low,top⟩ := mem_Icc.mp (mem_filter.mp hr).1
  have ub : q/r ≤ q/(y+1) := Nat.div_le_div_left low (by omega)
  unfold small
  rw [FastDenseA26.fast_correct _ (ub.trans quot),
    FastDenseA26.fast_correct _ (by omega : r-1≤745089)]

theorem quotient_survivors {q y z rank tiny pairs result : ℕ} (pos : 1≤q) (yq : y≤q)
    (cub : q<(y+1)^3) (sq : q<(z+1)^2) (bottom : z*z≤q)
    (high : z≤745089) (quot : q/(y+1)≤745089)
    (qrank : Nat.primeCounting q=rank) (yrank : Nat.primeCounting y=tiny)
    (twos : pairSum q y z=pairs) (sum : result+tiny=1+rank+pairs) :
    FinalSeventhSieve.rough q y=result := by
  have h := SieveA29From0To16.meissel pos yq cub sq
  have row (r : ℕ) (hr : r ∈ (Nat.primesLE z).filter (y < ·)) := by
    have rb := Nat.le_of_mem_primesLE (mem_filter.mp hr).1
    have rp := (Nat.prime_of_mem_primesLE (mem_filter.mp hr).1).pos
    exact SieveA29From0To16.prime_row rp
      ((Nat.le_div_iff_mul_le rp).mpr ((Nat.mul_le_mul rb rb).trans bottom))
  rw [sum_congr rfl row,pair_values q y z high quot,twos,Nat.primesLE_card_eq_primeCounting q,
    Nat.primesLE_card_eq_primeCounting y,qrank,yrank] at h
  change FinalSeventhSieve.rough q y+tiny = 1+rank+pairs at h
  omega

theorem row {x y z p q s rank tiny pairs amount : ℕ}
    (yp : y < p) (pz : p ≤ z) (top : z ≤ 745089)
    (prime : FastDenseA26.prime p=true)
    (gap : ∀ r ∈ Icc (y+1) z, FastDenseA26.prime r=true → r=p)
    (division : x/p=q) (positive : 1 ≤ q) (yq : y ≤ q)
    (cube : q < (y+1)^3) (root : q < (s+1)^2) (square : s*s ≤ q)
    (sbound : s ≤ 745089) (quot : q/(y+1) ≤ 745089)
    (qrank : Nat.primeCounting q=rank) (yrank : FastDenseA26.fast y=tiny)
    (twos : pairSum q y s=pairs) (sum : amount+tiny=1+rank+pairs) :
    FinalSeventhSieve.rough x z + amount = FinalSeventhSieve.rough x y :=
  FinalSeventhSieve.subtract_row yp pz (prime_by_flag (pz.trans top) prime)
    (gap_by_flags top gap) division (quotient_survivors positive yq cube root square sbound quot qrank
      ((FastDenseA26.fast_correct y (by omega)).symm.trans yrank) twos sum)

theorem combine {a b c v w total : ℕ} (first : b+v=a) (second : c+w=b)
    (add : v+w=total) : c+total=a := by omega

end LargeQuotientSieve
