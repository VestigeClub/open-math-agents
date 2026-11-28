import OMAStatements.S_oeis_a144503

open MeasureTheory Polynomial Polynomial.Chebyshev Set

namespace GiftExchangeIntegral

/-- Exponential moments on the positive half-line. -/
noncomputable def moment (p : ℝ[X]) : ℝ :=
  ∫ x in Ioi (0 : ℝ), p.eval x * Real.exp (-x)

lemma integrablePower (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-x)) (Ioi 0) := by
  simpa [Real.rpow_natCast, mul_comm] using
    (Real.GammaIntegral_convergent (s := (k : ℝ) + 1) (by positivity))

lemma powerMoment (k : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ k * Real.exp (-x)) = (k.factorial : ℝ) := by
  have h := (Real.Gamma_eq_integral (s := (k : ℝ) + 1) (by positivity)).symm.trans
    (Real.Gamma_nat_eq_factorial k)
  simpa [Real.rpow_natCast, mul_comm] using h

lemma integrablePolynomial (p : ℝ[X]) :
    IntegrableOn (fun x : ℝ => p.eval x * Real.exp (-x)) (Ioi 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa [eval_add, add_mul, Pi.add_def] using hp.add hq
  | monomial k c =>
    simpa [IntegrableOn, eval_monomial, mul_assoc] using (integrablePower k).const_mul c

lemma addMoment (p q : ℝ[X]) : moment (p+q) = moment p + moment q := by
  simpa [moment, eval_add, add_mul, Pi.add_def] using
    (integral_add (integrablePolynomial p) (integrablePolynomial q))

lemma subMoment (p q : ℝ[X]) : moment (p-q) = moment p - moment q := by
  simpa [moment, eval_sub, sub_mul, Pi.sub_def] using
    (integral_sub (integrablePolynomial p) (integrablePolynomial q))

lemma scaleMoment (c : ℝ) (p : ℝ[X]) : moment (C c * p) = c * moment p := by
  simp only [moment, eval_mul, eval_C, mul_assoc]
  exact integral_const_mul c _

lemma monoMoment (k : ℕ) (c : ℝ) : moment (monomial k c) = c * k.factorial := by
  simp only [moment, eval_monomial, mul_assoc]
  rw [integral_const_mul, powerMoment]

lemma momentByParts (p : ℝ[X]) : moment p = p.eval 0 + moment p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [addMoment, eval_add, derivative_add, addMoment, hp, hq]
    ring
  | monomial k c =>
    cases k with
    | zero =>
      rw [monoMoment, eval_monomial, derivative_monomial, monoMoment]
      simp
    | succ k =>
      simp only [monoMoment, eval_monomial, zero_pow (Nat.succ_ne_zero _),
        mul_zero, zero_add, derivative_monomial_succ, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      ring

noncomputable def shifted (p : ℝ[X]) : ℝ[X] := p.comp (X+1)
noncomputable def uMoment (j : ℤ) : ℝ := moment (shifted (U ℝ j))

lemma twiceFirst (j : ℤ) : 2 * moment (shifted (T ℝ j)) =
    uMoment j - uMoment (j-2) := by
  have h := two_mul_T_eq_U_sub_U ℝ (j-2)
  rw [show j-2+2=j by omega] at h
  have hs := congrArg (fun p : ℝ[X] => moment (shifted p)) h
  unfold shifted at hs
  simp only [mul_comp, sub_comp, ofNat_comp] at hs
  rw [← C_eq_natCast (R := ℝ) 2, scaleMoment, subMoment] at hs
  exact hs

lemma derivativeFirst (j : ℤ) : moment (shifted (T ℝ j)) = 1 + (j : ℝ) * uMoment (j-1) := by
  have h := momentByParts (shifted (T ℝ j))
  unfold shifted at h
  simp only [eval_comp, eval_add, eval_X, eval_one, zero_add, T_eval_one, derivative_comp,
    derivative_add, derivative_X, derivative_one, add_zero, one_mul, T_derivative_eq_U,
    mul_comp, intCast_comp] at h
  rw [show (j : ℝ[X]) = C (j : ℝ) by simp, scaleMoment] at h
  exact h

lemma recurrence (k : ℕ) : uMoment ((k : ℤ)+1) =
    2 + 2 * ((k : ℝ)+1) * uMoment k + uMoment ((k : ℤ)-1) := by
  have h := twiceFirst ((k : ℤ)+1)
  rw [derivativeFirst] at h
  norm_num at h
  rw [show (k : ℤ)+1-2 = (k : ℤ)-1 by omega] at h
  linarith

lemma zeroMoment : uMoment 0 = 1 := by
  unfold uMoment shifted
  rw [U_zero, one_comp]
  simpa [moment] using powerMoment 0

lemma negOneMoment : uMoment (-1) = 0 := by
  simp [uMoment, shifted, U_neg_one, moment]

lemma giftMoment (n : ℕ) : (OMA.S_oeis_a144503.giftExchange n : ℝ) = 1+uMoment ((n : ℤ)-1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [OMA.S_oeis_a144503.giftExchange, negOneMoment]
  | one => norm_num [OMA.S_oeis_a144503.giftExchange, zeroMoment]
  | more k hk hk1 =>
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hk1
    simp only [OMA.S_oeis_a144503.giftExchange, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat, Int.cast_natCast, hk1, hk, Nat.cast_add, Nat.cast_ofNat]
    rw [show (k : ℤ)+2-1 = (k : ℤ)+1 by omega, recurrence]
    ring

end GiftExchangeIntegral

theorem OMA.solution : type_of% @OMA.S_oeis_a144503.main := by
  intro n
  have h := GiftExchangeIntegral.giftMoment n
  simpa [GiftExchangeIntegral.uMoment, GiftExchangeIntegral.shifted, GiftExchangeIntegral.moment,
    eval_comp, div_eq_mul_inv, Real.exp_neg] using h
