import FormalConjectures.ErdosProblems.«1095»
import Mathlib

/-!
# A prime-power obstruction for the Erdős–Selfridge function

Suppose h is a power of a prime at most k, h ≥ k + 2 and k + 1 is
composite. For each admissible n, (h - k - 1) (n + 1) ≥ h (k + 1).
The bound is quadratic in k for fixed h - k. Its proof uses the
carry criterion for binomial coefficients and an adjacent binomial identity.
-/
open Finset

namespace ErdosSelfridgeGap

/-- Absence of a prime divisor forces domination of the lower base-p
digits after truncation at every power of p. -/
theorem truncated_residue {p n k : ℕ} (prime : p.Prime) (le : k ≤ n)
    (rough : ¬ p ∣ n.choose k) (a : ℕ) : k % p^a ≤ n % p^a := by
  by_cases az : a = 0
  · simp [az,Nat.mod_one]
  let b := Nat.log p n + a + 1
  have ord := Nat.factorization_choose prime le (show Nat.log p n < b by dsimp [b]; omega)
  rw [Nat.factorization_eq_zero_of_not_dvd rough] at ord
  have nocarry : k % p^a + (n-k) % p^a < p^a := by
    by_contra! carry
    have hit : a ∈ (Ico 1 b).filter (fun i => p^i ≤ k % p^i + (n-k) % p^i) := by
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by dsimp [b]; omega⟩,carry⟩
    have pos := Finset.card_pos.mpr ⟨a,hit⟩
    omega
  have sum : n % p^a = k % p^a + (n-k) % p^a := by
    calc
      n % p^a = (k+(n-k)) % p^a := congrArg (fun t => t % p^a) (by omega)
      _ = _ := (Nat.add_mod ..).trans (Nat.mod_eq_of_lt nocarry)
  rw [sum]
  exact Nat.le_add_right _ _

/-- Every prime divisor of a composite k+1 is at most k. Cancel the
coprime binomial coefficient in the adjacent binomial identity. -/
theorem next_divides {n k : ℕ} (composite : ¬(k+1).Prime)
    (rough : k < (n.choose k).minFac) : k+1 ∣ n+1 := by
  have cop : (k+1).Coprime (n.choose k) := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    by_contra different
    let p := ((k+1).gcd (n.choose k)).minFac
    have prime : p.Prime := Nat.minFac_prime different
    have divides := Nat.minFac_dvd ((k+1).gcd (n.choose k))
    have small : p ∣ k+1 := divides.trans (Nat.gcd_dvd_left _ _)
    have hle := Nat.le_of_dvd (Nat.zero_lt_succ k) small
    have ne : p ≠ k+1 := fun h => composite (h ▸ prime)
    have pc : p ∣ n.choose k := divides.trans (Nat.gcd_dvd_right _ _)
    have bound := Nat.minFac_le_of_dvd prime.two_le pc
    omega
  apply cop.dvd_of_dvd_mul_right
  rw [Nat.add_one_mul_choose_eq]
  exact Nat.dvd_mul_left _ _

private theorem gap_from_residue {h n k : ℕ} (past : k+1 < n) (above : k+2 ≤ h)
    (multiple : k+1 ∣ n+1) (residue : k ≤ n % h) :
    h*(k+1) ≤ (h-k-1)*(n+1) := by
  let s := h-k-1
  have hs : 0 < s := by dsimp [s]; omega
  have hm : k+1+s=h := by dsimp [s]; omega
  obtain ⟨q,hq⟩ := multiple
  have one : 1 < q := by
    by_contra! small
    interval_cases q <;> omega
  have far : h ≤ q*s := by
    by_contra! near
    let r := h-q*s-1
    have rem' : r+q*s+1=h := by dsimp [r]; omega
    have lt : r<h := by omega
    have sum : n+1+q*s=q*h := by
      calc
        n+1+q*s = q*(k+1)+q*s := by rw [hq]; ring
        _ = q*(k+1+s) := by ring
        _ = q*h := by rw [hm]
    have expand : h*(q-1)+h=q*h := by
      calc
        h*(q-1)+h = (q-1+1)*h := by ring
        _ = q*h := by rw [show q-1+1=q by omega]
    have eq : n=r+h*(q-1) := by omega
    rw [eq,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lt] at residue
    have gt : s < q*s := by simpa using Nat.mul_lt_mul_of_pos_right one hs
    omega
  calc
    h*(k+1) ≤ q*s*(k+1) := Nat.mul_le_mul_right _ far
    _ = s*(n+1) := by rw [hq]; ring

theorem admissible_gap {k n p a : ℕ} (prime : p.Prime) (small : p ≤ k)
    (composite : ¬(k+1).Prime) (past : k+1 < n) (rough : k < (n.choose k).minFac)
    (above : k+2 ≤ p^a) : p^a*(k+1) ≤ (p^a-k-1)*(n+1) := by
  have avoids : ¬ p ∣ n.choose k := fun d =>
    (not_lt_of_ge ((Nat.minFac_le_of_dvd prime.two_le d).trans small)) rough
  have residue := truncated_residue prime (show k ≤ n by omega) avoids a
  rw [Nat.mod_eq_of_lt (show k<p^a by omega)] at residue
  exact gap_from_residue past above (next_divides composite rough) residue

/-- Taking n=k+(k!)² gives a nonempty admissible set. The numerator
of the rising factorial is congruent to k! modulo (k!)². Cancelling
k! shows that the binomial coefficient is 1 modulo k!. -/
private theorem has_candidate (k : ℕ) (hk : 2 ≤ k) :
    {n : ℕ | k+1 < n ∧ k < (n.choose k).minFac}.Nonempty := by
  let f := k.factorial
  let L := f*f
  have fbig : 2 ≤ f := Nat.le_of_dvd (Nat.factorial_pos _) (Nat.dvd_factorial (by decide) hk)
  have big : 1 < L := by change 1 < f*f; nlinarith
  have zeroMod : L ≡ 0 [MOD L] := by
    show L%L = 0%L
    simp
  have lifts : (L+1).ascFactorial k ≡ (0+1).ascFactorial k [MOD L] := by
    rw [Nat.ascFactorial_eq_prod_range,Nat.ascFactorial_eq_prod_range]
    apply Nat.ModEq.prod
    intro i _
    simpa only [zero_add,Nat.add_assoc] using zeroMod.add (Nat.ModEq.refl (1+i))
  rw [Nat.ascFactorial_eq_factorial_mul_choose L k,
    Nat.ascFactorial_eq_factorial_mul_choose 0 k,zero_add,Nat.choose_self] at lifts
  have one : (L+k).choose k ≡ 1 [MOD f] :=
    Nat.ModEq.mul_left_cancel' (Nat.factorial_ne_zero k) lifts
  have nontriv : 1 < (L+k).choose k := by
    have h := Nat.choose_le_choose k (show k+1 ≤ L+k by omega)
    rw [Nat.choose_succ_self_right] at h
    omega
  refine ⟨L+k,by omega,?_⟩
  by_contra! small
  let p := ((L+k).choose k).minFac
  have prime : p.Prime := Nat.minFac_prime (by omega)
  have pf : p ∣ f := Nat.dvd_factorial prime.pos small
  have congr := one.of_dvd pf
  change ((L+k).choose k)%p = 1%p at congr
  rw [Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd _),Nat.mod_eq_of_lt prime.one_lt] at congr
  contradiction

/-- Apply the obstruction to the actual minimum in the problem statement. -/
theorem minimum_gap {k p a : ℕ} (prime : p.Prime) (small : p ≤ k)
    (composite : ¬(k+1).Prime) (above : k+2 ≤ p^a) :
    p^a*(k+1) ≤ (p^a-k-1)*(Erdos1095.g k+1) := by
  have mem : Erdos1095.g k ∈ {n : ℕ | k+1<n ∧ k < (n.choose k).minFac} :=
    Nat.sInf_mem (has_candidate k (prime.two_le.trans small))
  exact admissible_gap prime small composite mem.1 mem.2 above

/-- A fixed even offset below an odd prime power gives a quadratic
lower bound, with the factor t-1 explicit. -/
theorem even_offset {p a t : ℕ} (prime : p.Prime) (odd : Odd p) (even : Even t)
    (offset : 2 ≤ t) (large : p+t ≤ p^a) :
    p^a*(p^a-t+1) ≤ (t-1)*(Erdos1095.g (p^a-t)+1) := by
  let k := p^a-t
  have hk : k+t=p^a := by dsimp [k]; omega
  have small : p ≤ k := by omega
  have pthree : 3 ≤ p := by
    obtain ⟨v,hv⟩ := odd
    have := prime.two_le
    omega
  have oddK : Odd k := by
    obtain ⟨u,hu⟩ := odd.pow (n:=a)
    obtain ⟨v,hv⟩ := even
    exact ⟨u-v,by omega⟩
  obtain ⟨v,hv⟩ := oddK
  have two : 2 ∣ k+1 := ⟨v+1,by omega⟩
  have composite : ¬(k+1).Prime := by
    intro supposed
    rcases supposed.eq_one_or_self_of_dvd 2 two with h | h <;> omega
  have bound := minimum_gap prime small composite (show k+2≤p^a by omega)
  simpa only [show p^a-k-1=t-1 by omega] using bound

/-- In particular the offset two has no loss in the quadratic bound. -/
theorem quadratic_odd_prime_power {p a : ℕ} (prime : p.Prime) (odd : Odd p) (power : 2 ≤ a) :
    (p^a-1)*p^a ≤ Erdos1095.g (p^a-2)+1 := by
  have high : p^2 ≤ p^a := Nat.pow_le_pow_right prime.pos power
  have pbig := prime.two_le
  have large : p+2 ≤ p^a := by nlinarith
  have bound := even_offset prime odd (show Even 2 by decide) (le_refl 2) large
  have right : p^a-2+1=p^a-1 := by omega
  simpa only [right,show 2-1=1 by decide,one_mul,Nat.mul_comm] using bound

end ErdosSelfridgeGap
