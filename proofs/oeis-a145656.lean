import OMAStatements.S_oeis_a145656

open MeasureTheory Finset OMA.S_oeis_a145656

namespace GenusOne

noncomputable def ratio (x : ℝ) := x^2/(1+x^2)
noncomputable def kernel (k : ℕ) (x : ℝ) := x^(2*k+1)/(1+x^2)^(k+1)
noncomputable def moment (k : ℕ) := ∫ x in (0:ℝ)..1, kernel k x

lemma kernelAlt (k : ℕ) (x : ℝ) :
    kernel k x = x/(1+x^2) * ratio x ^ k := by
  simp only [kernel, ratio, div_pow, ←mul_div_mul_comm, pow_succ (1+x^2) k,
    pow_succ x (2*k), pow_mul x 2 k]
  congr 1 <;> ring

lemma continuousKernel (k : ℕ) : Continuous (kernel k) := by
  unfold kernel
  exact (continuous_id.pow _).div ((continuous_const.add (continuous_id.pow 2)).pow _)
    (fun x => by positivity)

lemma ratioDeriv (x : ℝ) : HasDerivAt ratio (2*x/(1+x^2)^2) x := by
  have h := (hasDerivAt_id x).pow 2
  have hx : (1:ℝ)+x^2 ≠ 0 := by positivity
  have hp := h.div ((hasDerivAt_const x (1:ℝ)).add h) hx
  apply hp.congr_deriv
  simp
  ring

lemma momentBase : moment 0 = Real.log 2/2 := by
  have h (x : ℝ) : HasDerivAt (fun t : ℝ => Real.log (1+t^2)/2) (kernel 0 x) x := by
    have hp := (hasDerivAt_const x (1:ℝ)).add ((hasDerivAt_id x).pow 2)
    have hx : (1:ℝ)+x^2 ≠ 0 := by positivity
    apply ((hp.log hx).div_const 2).congr_deriv
    simp [kernel]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
    (fun x _ => h x) ((continuousKernel 0).intervalIntegrable _ _)
  norm_num [moment] at hi ⊢
  exact hi

lemma primitiveDeriv (k : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => ratio t^(k+1)/(2*((k:ℝ)+1)))
      (kernel k x - kernel (k+1) x) x := by
  have h := ((ratioDeriv x).pow (k+1)).div_const (2*((k:ℝ)+1))
  apply h.congr_deriv
  rw [kernelAlt k x, kernelAlt (k+1) x, pow_succ (ratio x) k]
  simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
  generalize ratio x^k = R
  unfold ratio
  have hx : (1:ℝ)+x^2 ≠ 0 := by positivity
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

lemma momentStep (k : ℕ) : moment (k+1) =
    moment k - (1/2:ℝ)^(k+1)/(2*((k:ℝ)+1)) := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
    (fun x _ => primitiveDeriv k x)
    (((continuousKernel k).sub (continuousKernel (k+1))).intervalIntegrable _ _)
  rw [intervalIntegral.integral_sub ((continuousKernel k).intervalIntegrable _ _)
    ((continuousKernel (k+1)).intervalIntegrable _ _)] at hi
  change moment k - moment (k+1) = _ at hi
  norm_num [ratio] at hi
  linarith

lemma polynomialStep (k : ℕ) : polynomialValue (k+2) =
    2*polynomialValue (k+1)+2/((k:ℚ)+1) := by
  simp only [polynomialValue,show k+2-1=k+1 by omega,Nat.add_sub_cancel]
  rw [sum_range_succ, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro i hi
    have hit : i ≤ k := Nat.le_of_lt (mem_range.mp hi)
    rw [show k+1-i=k-i+1 by omega,pow_succ]
    ring
  · simp

lemma polynomialScale (k : ℕ) : polynomialValue (k+1) = (2:ℚ)^(k+1)*harmonicPart k := by
  simp only [polynomialValue,harmonicPart,Nat.add_sub_cancel,mul_sum]
  apply sum_congr rfl
  intro i hi
  have hit : i ≤ k := Nat.le_of_lt (mem_range.mp hi)
  have hp : (2:ℚ)^(k+1) = 2^(k-i)*2^(i+1) := by
    rw [←pow_add]; congr 1; omega
  rw [hp]
  field_simp

lemma expressionAt (k : ℕ) : expression (k+1) =
    (2:ℝ)^(k+1)*Real.log 2-2^(k+2)*moment k := by
  unfold expression moment kernel
  rw [show 2*(k+1)-1=2*k+1 by omega]

lemma expressionStep (k : ℕ) : expression (k+2)=2*expression (k+1)+2/((k:ℝ)+1) := by
  rw [expressionAt (k+1), expressionAt, momentStep]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  rw [one_div_pow]
  simp only [pow_succ]
  field_simp
  ring

lemma value (k : ℕ) : expression (k+1) = (polynomialValue (k+1):ℝ) := by
  induction k with
  | zero => rw [expressionAt, momentBase]; norm_num [polynomialValue]; ring
  | succ k hk =>
    rw [expressionStep, polynomialStep, hk]
    push_cast
    ring

lemma numDvdScale (q : ℚ) (m : ℕ) : q.num ∣ ((m:ℚ)*q).num := by
  have h := Rat.mul_num_den' (m:ℚ) q
  simp at h
  apply q.isCoprime_num_den.dvd_of_dvd_mul_right
  exact ⟨(m:ℤ)*((m:ℚ)*q).den, by linear_combination h⟩

end GenusOne

theorem OMA.solution : type_of% @OMA.S_oeis_a145656.main := by
  constructor
  · intro n hn
    obtain ⟨k,rfl⟩ : ∃ k, n=k+1 := ⟨n-1,by omega⟩
    exact ⟨polynomialValue (k+1), (GenusOne.value k).symm, rfl⟩
  · intro n hn
    obtain ⟨k,rfl⟩ : ∃ k, n=k+1 := ⟨n-1,by omega⟩
    rw [Nat.add_sub_cancel,GenusOne.polynomialScale]
    simpa using GenusOne.numDvdScale (harmonicPart k) (2^(k+1))
