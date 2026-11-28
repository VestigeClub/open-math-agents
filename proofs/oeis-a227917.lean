import OMAStatements.S_oeis_a227917

open MeasureTheory Set Finset OMA.S_oeis_a227917

namespace TreeLaplace

def term (n k : ℕ) (x : ℝ) : ℝ := (Nat.stirlingFirst n k : ℝ)*x^k

lemma lastTerm (n : ℕ) (x : ℝ) : term n (n+1) x = 0 := by
  simp [term, Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n)]

lemma shiftedSum (n : ℕ) (x : ℝ) :
    (∑ k ∈ range (n+1), term n (k+1) x) + term n 0 x =
    ∑ k ∈ range (n+1), term n k x := by
  calc
    _ = ∑ k ∈ range (n+2), term n k x := (sum_range_succ' _ _).symm
    _ = _ := by rw [sum_range_succ, lastTerm, add_zero]

lemma firstWeighted (n : ℕ) (x : ℝ) : (n:ℝ)*term n 0 x = 0 := by
  cases n <;> simp [term]

lemma nextTerm (n k : ℕ) (x : ℝ) :
    term (n+1) (k+1) x = n*term n (k+1) x + x*term n k x := by
  rw [term, Nat.stirlingFirst_succ_succ, Nat.cast_add, Nat.cast_mul]
  unfold term
  ring

lemma expansion (x : ℝ) (n : ℕ) : rising x n = ∑ k ∈ range (n+1), term n k x := by
  induction n with
  | zero => simp [rising, term]
  | succ n ih =>
    change (∏ j ∈ range (n+1), (x+(j:ℝ))) = ∑ k ∈ range (n+2), term (n+1) k x
    rw [prod_range_succ]
    change rising x n * (x+(n:ℝ)) = _
    rw [ih, sum_range_succ' (fun k => term (n+1) k x) (n+1)]
    simp only [nextTerm, sum_add_distrib, ←mul_sum]
    rw [show term (n+1) 0 x = 0 by simp [term], add_zero]
    linear_combination -(n:ℝ)*shiftedSum n x + firstWeighted n x

lemma moment (k : ℕ) :
    (∫ x : ℝ in Ioi 0, x^k * Real.exp (-(2*x))) =
      (1/2:ℝ)^(k+1)*k.factorial := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=(k:ℝ)+1) (r:=2) (by positivity) (by norm_num)
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [←Nat.cast_succ, Real.rpow_natCast] at h
  exact h

lemma integrableMoment (k : ℕ) :
    IntegrableOn (fun x : ℝ => x^k * Real.exp (-(2*x))) (Ioi 0) := by
  by_contra hn
  have h := moment k
  have hz : (∫ x : ℝ in Ioi 0, x^k*Real.exp (-(2*x))) = 0 := integral_undef hn
  rw [hz] at h
  have hp : 0 < (1/2:ℝ)^(k+1)*(k.factorial:ℝ) := by positivity
  linarith

lemma termIntegrable (n k : ℕ) :
    IntegrableOn (fun x : ℝ => term n k x * Real.exp (-(2*x))) (Ioi 0) := by
  simpa only [IntegrableOn,term,mul_assoc] using (integrableMoment k).const_mul (Nat.stirlingFirst n k : ℝ)

lemma contribution (n k : ℕ) (hk : k ≤ n) :
    (2:ℝ)^(n+1)*(∫ x in Ioi (0:ℝ), term n k x * Real.exp (-(2*x))) =
      (Nat.stirlingFirst n k:ℝ)*k.factorial*2^(n-k) := by
  simp only [term,mul_assoc,integral_const_mul,moment,one_div_pow]
  have h : (2:ℝ)^(n+1) = 2^(n-k)*2^(k+1) := by
    rw [←pow_add]
    congr 1
    omega
  rw [h]
  field_simp

end TreeLaplace

theorem OMA.solution : type_of% @OMA.S_oeis_a227917.main := by
  intro n hn
  simp only [trees, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp_rw [TreeLaplace.expansion, div_eq_mul_inv, ←Real.exp_neg, Finset.sum_mul]
  rw [integral_finsetSum _ (fun k _ => TreeLaplace.termIntegrable n k), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact (TreeLaplace.contribution n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).symm
