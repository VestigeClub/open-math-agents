import OMAStatements.S_oeis_a143412
import Mathlib

open Polynomial Polynomial.Chebyshev MeasureTheory ProbabilityTheory

namespace GaussianChebyshev

noncomputable def law : Measure ℝ := gaussianReal 0 1
noncomputable def powerMoment (k : ℕ) : ℝ := ∫ x : ℝ, x^k ∂law
noncomputable def expectation (p : ℝ[X]) : ℝ := ∫ x : ℝ, p.eval x ∂law
noncomputable def generating (t : ℝ) : ℝ := Real.exp (t^2/2)

lemma derivGenerating : deriv generating = fun t => t * generating t := by
  funext t
  unfold generating
  rw [_root_.deriv_exp (by fun_prop)]
  rw [deriv_div_const, deriv_fun_pow (by fun_prop)]
  simp
  ring

lemma powerDerivative (k : ℕ) : powerMoment k = iteratedDeriv k generating 0 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) k
  rw [mgf_fun_id_gaussianReal] at h
  change (∫ x : ℝ, x ^ k ∂gaussianReal 0 1) = iteratedDeriv k (fun t : ℝ => Real.exp (t^2/2)) 0
  simpa using h.symm

lemma powerRecurrence (k : ℕ) : powerMoment (k+2) = ((k:ℝ)+1) * powerMoment k := by
  rw [powerDerivative, powerDerivative, iteratedDeriv_succ', derivGenerating,
    iteratedDeriv_fun_mul (by fun_prop) (by unfold generating; fun_prop)]
  simp only [iteratedDeriv_fun_id_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

lemma integrablePower (k : ℕ) : Integrable (fun x : ℝ => x^k) law := by
  exact integrable_pow_of_mem_interior_integrableExpSet (X:=fun x : ℝ => x)
    (by simp [law]) k

lemma integrablePoly (p : ℝ[X]) : Integrable (fun x => p.eval x) law := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [eval_add, Pi.add_def] using hp.add hq
  | monomial k c => simpa only [eval_monomial] using (integrablePower k).const_mul c

lemma addExpectation (p q : ℝ[X]) : expectation (p+q) = expectation p + expectation q := by
  simpa only [expectation, eval_add, Pi.add_def] using integral_add (integrablePoly p) (integrablePoly q)

lemma subExpectation (p q : ℝ[X]) : expectation (p-q) = expectation p - expectation q := by
  simpa only [expectation, eval_sub, Pi.sub_def] using integral_sub (integrablePoly p) (integrablePoly q)

lemma scaleExpectation (c : ℝ) (p : ℝ[X]) : expectation (C c*p) = c*expectation p := by
  simp only [expectation, eval_mul, eval_C]
  exact integral_const_mul c _

lemma monoExpectation (k : ℕ) (c : ℝ) : expectation (monomial k c) = c*powerMoment k := by
  simp only [expectation, eval_monomial, powerMoment, integral_const_mul]

lemma xMonoExpectation (k : ℕ) (c : ℝ) : expectation (X*monomial k c) = c*powerMoment (k+1) := by
  unfold expectation powerMoment
  simp only [eval_mul, eval_X, eval_monomial, pow_succ]
  have h (x : ℝ) : x*(c*x^k) = c*(x^k*x) := by ring
  simp_rw [h, integral_const_mul]

lemma stein (p : ℝ[X]) : expectation (X*p) = expectation p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, derivative_add, addExpectation, addExpectation, hp, hq]
  | monomial k c =>
    cases k with
    | zero =>
      rw [xMonoExpectation, derivative_monomial, monoExpectation]
      simp [powerMoment, law]
    | succ k =>
      rw [xMonoExpectation, derivative_monomial_succ, monoExpectation, powerRecurrence]
      ring

lemma polyIdentity (j : ℤ) : U ℝ (j+2) - U ℝ (j-2) = C (4:ℝ)*(X*T ℝ (j+1)) := by
  have h := two_mul_T_eq_U_sub_U ℝ (j-2)
  rw [show j-2+2=j by omega] at h
  calc
    _ = (U ℝ (j+2)-U ℝ j)+(U ℝ j-U ℝ (j-2)) := by ring
    _ = 2*T ℝ (j+2) + 2*T ℝ j := by rw [←two_mul_T_eq_U_sub_U, ←h]
    _ = _ := by rw [T_add_two, C_ofNat]; ring

lemma uRec (j : ℤ) : expectation (U ℝ (j+2)) =
    4*((j:ℝ)+1)*expectation (U ℝ j) + expectation (U ℝ (j-2)) := by
  have h := congrArg expectation (polyIdentity j)
  rw [subExpectation, scaleExpectation, stein, T_derivative_eq_U] at h
  rw [show j+1-1=j by omega, show ((j+1 : ℤ) : ℝ[X])=C ((j:ℝ)+1) by simp, scaleExpectation] at h
  linarith

lemma standard (n : ℕ) : expectation (U ℝ (2*(n:ℤ))) = (OMA.S_oeis_a143412.a n : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [expectation,law,U_zero,OMA.S_oeis_a143412.a]
  | one =>
    have h := uRec 0
    norm_num [U_zero,U_neg_two,expectation,law,OMA.S_oeis_a143412.a] at h ⊢
    exact h
  | more k hk hk1 =>
    have h := uRec (2*((k:ℤ)+1))
    rw [show 2*((k:ℤ)+1)+2=2*((k:ℤ)+2) by ring,
      show 2*((k:ℤ)+1)-2=2*(k:ℤ) by ring] at h
    simp only [Nat.cast_add, Nat.cast_one] at hk1
    rw [hk1, hk] at h
    simp only [OMA.S_oeis_a143412.a, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    convert h using 1
    push_cast
    ring

end GaussianChebyshev

theorem OMA.solution : type_of% @OMA.S_oeis_a143412.main := by
  intro n
  exact GaussianChebyshev.standard n
