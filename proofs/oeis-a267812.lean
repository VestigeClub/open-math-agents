import OMAStatements.S_oeis_a267812
import Mathlib

/-!
# Rule 217: stabilization, recurrence, and generating function

Credit: @VestigeClub.
Source: https://oeis.org/A267812.

After two updates, every site of the infinite line is on except the origin.
That configuration is fixed by Rule 217. Summing the finite binary readout
therefore gives `2^(2*n+1) - 2^n - 1` for every n at least two. Together with
the first two readouts, this proves the stated recurrence and generating function.
-/


namespace Rule217
open OMA.S_oeis_a267812

theorem cell_one (i : ℤ) : cell 217 1 i = decide (i ≠ -1 ∧ i ≠ 0) := by
  have hL : (i-1=0) ↔ i=1 := by omega
  have hR : (i+1=0) ↔ i= -1 := by omega
  by_cases h0 : i=0 <;> by_cases hm : i= -1 <;> by_cases hp : i=1 <;>
    norm_num [cell, ruleOut, hL, hR, h0, hm, hp] <;> first | omega | decide

theorem cell_two (i : ℤ) : cell 217 2 i = decide (i ≠ 0) := by
  change ruleOut 217 (cell 217 1 (i-1)) (cell 217 1 i) (cell 217 1 (i+1)) = _
  rw [cell_one, cell_one, cell_one]
  have hL1 : (i-1≠ -1) ↔ i≠0 := by omega
  have hL0 : (i-1≠0) ↔ i≠1 := by omega
  have hR1 : (i+1≠ -1) ↔ i≠ -2 := by omega
  have hR0 : (i+1≠0) ↔ i≠ -1 := by omega
  by_cases h0 : i=0 <;> by_cases hm1 : i= -1 <;> by_cases hm2 : i= -2 <;> by_cases hp1 : i=1 <;>
    norm_num [ruleOut, hL1, hL0, hR1, hR0, h0, hm1, hm2, hp1] <;> first | omega | decide

theorem fixed (i : ℤ) :
    ruleOut 217 (decide (i-1≠0)) (decide (i≠0)) (decide (i+1≠0)) = decide (i≠0) := by
  have hL : (i-1≠0) ↔ i≠1 := by omega
  have hR : (i+1≠0) ↔ i≠ -1 := by omega
  by_cases h0 : i=0 <;> by_cases hm : i= -1 <;> by_cases hp : i=1 <;>
    norm_num [ruleOut, hL, hR, h0, hm, hp] <;> first | omega | decide

theorem cell_stable (t : ℕ) (i : ℤ) : cell 217 (t+2) i = decide (i≠0) := by
  induction t generalizing i with
  | zero => exact cell_two i
  | succ t ih =>
    change ruleOut 217 (cell 217 (t+2) (i-1)) (cell 217 (t+2) i) (cell 217 (t+2) (i+1)) = _
    rw [ih, ih, ih]
    exact fixed i

end Rule217

namespace Rule217
open OMA.S_oeis_a267812

theorem sum_powers (k : ℕ) : (∑ j ∈ Finset.range k, (2:ℤ)^j) = 2^k-1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem a_formula (n : ℕ) (hn : 2≤n) : a n = (2:ℤ)^(2*n+1)-2^n-1 := by
  have hc (i : ℤ) : cell 217 n i = decide (i≠0) := by
    simpa only [show n-2+2=n by omega] using cell_stable (n-2) i
  have ht (j : ℕ) :
      (if cell 217 n ((j:ℤ)-n) then (2:ℤ)^(2*n-j) else 0) =
        (2:ℤ)^(2*n-j) - if j=n then (2:ℤ)^(2*n-j) else 0 := by
    rw [hc]
    by_cases hj : j=n
    · subst j; simp
    · have hneq : (j:ℤ)-(n:ℤ) ≠ 0 := by omega
      simp [hneq,hj]
  rw [a]
  simp_rw [ht]
  rw [Finset.sum_sub_distrib]
  have href := Finset.sum_range_reflect (fun j => (2:ℤ)^j) (2*n+1)
  simp only [Nat.add_sub_cancel] at href
  rw [href, sum_powers]
  simp [show n < 2*n+1 by omega]
  rw [show 2*n-n=n by omega]
  ring

theorem a_zero : a 0 = 1 := by norm_num [a, cell, ruleOut]
theorem a_one : a 1 = 1 := by
  norm_num [a, cell, ruleOut, Finset.sum_range_succ]
  decide

end Rule217

namespace Rule217
open OMA.S_oeis_a267812 PowerSeries

theorem recurrence_int (n : ℕ) (hn : 5≤n) :
    a n = 7*a (n-1)-14*a (n-2)+8*a (n-3) := by
  let k := n-5
  have he : n=k+5 := by dsimp [k]; omega
  rw [he, show k+5-1=k+4 by omega, show k+5-2=k+3 by omega, show k+5-3=k+2 by omega]
  rw [a_formula (k+5) (by omega), a_formula (k+4) (by omega),
    a_formula (k+3) (by omega), a_formula (k+2) (by omega)]
  norm_num [Nat.mul_add, pow_add, pow_mul]
  ring

theorem recurrence (n : ℕ) (hn : 5≤n) :
    (a n:ℚ) = 7*a (n-1)-14*a (n-2)+8*a (n-3) := by
  exact_mod_cast recurrence_int n hn

noncomputable def gen : PowerSeries ℚ := PowerSeries.mk (fun n => (a n:ℚ))

theorem generating_function :
    gen*((1-X)*(1-2*X)*(1-4*X)) = 1-6*X+34*X^2-64*X^3+32*X^4 := by
  have he : gen*((1-X)*(1-2*X)*(1-4*X)) =
      gen-(7:ℚ) • (X*gen)+(14:ℚ) • (X^2*gen)-(8:ℚ) • (X^3*gen) := by
    simp only [Algebra.smul_def, map_ofNat]
    ring
  have hr : (1-6*X+34*X^2-64*X^3+32*X^4 : PowerSeries ℚ) =
      1-(6:ℚ) • X+(34:ℚ) • X^2-(64:ℚ) • X^3+(32:ℚ) • X^4 := by
    simp only [Algebra.smul_def, map_ofNat]
  rw [he,hr]
  ext n
  have h2 := a_formula 2 (by omega)
  have h3 := a_formula 3 (by omega)
  have h4 := a_formula 4 (by omega)
  norm_num at h2 h3 h4
  by_cases hn : n≤4
  · interval_cases n <;>
      norm_num [gen, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow, PowerSeries.coeff_X,
        a_zero, a_one, h2,h3,h4]
  · have hn5 : 5≤n := by omega
    have h1n : 1≤n := by omega
    have h2n : 2≤n := by omega
    have h3n : 3≤n := by omega
    have hn0 : n≠0 := by omega
    have hn1 : n≠1 := by omega
    have hn2 : n≠2 := by omega
    have hn3 : n≠3 := by omega
    have hn4 : n≠4 := by omega
    have hX : coeff n (X*gen) = coeff (n-1) gen := by
      conv_lhs => rw [show n=(n-1)+1 by omega]
      exact coeff_succ_X_mul _ _
    simp only [map_sub, map_add, map_smul, smul_eq_mul]
    rw [hX]
    simp only [coeff_X_pow_mul',
      if_pos h1n, if_pos h2n, if_pos h3n, gen, coeff_mk,
      coeff_one, coeff_X, coeff_X_pow, hn0, hn1, hn2, hn3, hn4, if_false,
      mul_zero, add_zero, sub_zero]
    have h := recurrence n hn5
    linarith

end Rule217

theorem OMA.solution : type_of% @OMA.S_oeis_a267812.main := by
  constructor
  · exact Rule217.recurrence
  · exact Rule217.generating_function
