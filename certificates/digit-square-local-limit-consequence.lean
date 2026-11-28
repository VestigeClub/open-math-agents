import certificates.«prime-digit-squares-through-1024»

/-!
# The prime digit-square sum on the central line

Martin, Mauduit and Rivat's local limit theorem (Theorem 1 with frequency zero)
applies to this digit function. The estimate takes a particularly simple form
when the target is the mean. This file proves the consequence of the normalized
estimate. The estimate itself is an explicit hypothesis.
https://www-lmpa.univ-littoral.fr/~martin/mmrp3-v7.pdf
-/
open Filter Finset
namespace DigitSquarePrimes.LocalLimit

theorem append_digit (n d : ℕ) (hd : d < 10) :
    squareSum (10*n+d) = squareSum n + d^2 := by
  by_cases z : 10*n+d=0
  · have hn : n=0 := by omega
    have he : d=0 := by omega
    simp [hn,he,squareSum]
  · have hpos : 0 < 10*n+d := Nat.pos_of_ne_zero z
    have last : (10*n+d)%10=d := by omega
    have rest : (10*n+d)/10=n := by omega
    unfold squareSum
    rw [Nat.digits_def' (by decide : 1 < 10) hpos,List.map_cons,List.sum_cons,last,rest,Nat.add_comm]

theorem digit_parameters :
    (∑ d ∈ range 10, (d:ℚ)^2)/10 = 57/2 ∧
    (∑ d ∈ range 10, ((d:ℚ)^2-57/2)^2)/10 = 14421/20 ∧
    ((List.range 9).map (fun i : ℕ => (i+1)^2)).foldl Nat.gcd 0 = 1 ∧
    ((List.range 8).map (fun i : ℕ => (i+2)^2-(i+2))).foldl Nat.gcd 9 = 1 := by
  decide +kernel

noncomputable def scale (n : ℕ) : ℝ := Real.exp (2 * (n : ℝ) * Real.log 10 / 57)
noncomputable def primes (n : ℕ) : Finset ℕ := Nat.primesLE ⌊scale n⌋₊
noncomputable def witnesses (n : ℕ) : Finset ℕ := (primes n).filter (fun p => squareSum p = n)
noncomputable def centralCoefficient : ℝ := Real.sqrt (57 / (4 * Real.pi * (14421 / 20)))

def Attained (n : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ squareSum p=n

/-- The normalized error estimate at the real cutoff where the digit mean equals n. -/
def DiagonalEstimate (K : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    |Real.sqrt n * ((witnesses n).card : ℝ) / ((primes n).card : ℝ) - centralCoefficient|
      ≤ K / Real.sqrt (Real.sqrt n)

theorem eventually_attained {K : ℝ} (hK : 0 ≤ K) (bound : DiagonalEstimate K) :
    ∀ᶠ n : ℕ in atTop, Attained n := by
  have hc : 0 < centralCoefficient := by unfold centralCoefficient; positivity
  have diverges : Tendsto (fun n : ℕ => Real.sqrt (Real.sqrt (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have large := diverges.eventually_gt_atTop (K / centralCoefficient)
  filter_upwards [bound,large] with n approximation threshold
  change K / centralCoefficient < Real.sqrt (Real.sqrt (n : ℝ)) at threshold
  have positive := lt_of_le_of_lt (div_nonneg hK hc.le) threshold
  have small : K / Real.sqrt (Real.sqrt (n : ℝ)) < centralCoefficient := by
    apply (div_lt_iff₀ positive).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp threshold
  have nonempty : (witnesses n).Nonempty := by
    by_contra empty
    have zero : witnesses n = ∅ := Finset.not_nonempty_iff_eq_empty.mp empty
    rw [zero] at approximation
    simp [abs_of_pos hc] at approximation
    linarith
  obtain ⟨p,hp⟩ := nonempty
  obtain ⟨pr,eq⟩ := mem_filter.mp hp
  exact ⟨p,Nat.prime_of_mem_primesLE pr,eq⟩

/-- Only finitely many target values can be missed if the diagonal estimate holds. -/
theorem finite_missing {K : ℝ} (hK : 0 ≤ K) (bound : DiagonalEstimate K) :
    {n : ℕ | ¬ Attained n}.Finite := by
  obtain ⟨N,large⟩ := Filter.eventually_atTop.mp (eventually_attained hK bound)
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  change ¬ Attained n at hn
  by_contra! high
  exact hn (large n high)

end DigitSquarePrimes.LocalLimit
