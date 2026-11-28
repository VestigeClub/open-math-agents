import OMAStatements.S_oeis_a267214

/-!
Proof of the Rule 109 recurrence and generating function in OEIS A267214.
The spatial pattern has three temporal phases and period twelve in the
interior. Only the two moving boundary cells require separate treatment.
Reflection and block counting give the white-cell recurrence; coefficient
extraction gives the generating function.

OEIS source: https://oeis.org/A267214
Conjectured formulas: Colin Barker.
-/

namespace Rule109
open OMA.S_oeis_a267214
def bits (t x : ℕ) : Bool :=
  (match t % 3 with | 0 => 1404 | 1 => 1989 | _ => 3159).testBit (x % 12)
def model (t x : ℕ) : Bool :=
  if t = 0 then decide (x = 0)
  else if t < x then decide (t % 2 = 1)
  else if x = t then decide (t % 2 = 0)
  else if x + 1 = t then true
  else bits t x

lemma bits_step (t x : ℕ) (hx : 0 < x) :
    bits (t+1) x = ruleOut 109 (bits t (x-1)) (bits t x) (bits t (x+1)) := by
  have hp : (t+1)%3 = (t%3+1)%3 := by omega
  have hl : (x-1)%12 = (x%12+11)%12 := by omega
  have hr : (x+1)%12 = (x%12+1)%12 := by omega
  unfold bits
  rw [hp,hl,hr]
  have ht : t%3 < 3 := Nat.mod_lt _ (by decide)
  have hi : x%12 < 12 := Nat.mod_lt _ (by decide)
  interval_cases ht' : t%3 <;> interval_cases hi' : x%12 <;> decide

lemma bits_center (t : ℕ) :
    bits (t+1) 0 = ruleOut 109 (bits t 1) (bits t 0) (bits t 1) := by
  have hp : (t+1)%3 = (t%3+1)%3 := by omega
  unfold bits
  rw [hp]
  have ht : t%3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases ht' : t%3 <;> decide

set_option maxHeartbeats 8000000 in
lemma model_step (t x : ℕ) (hx : 0 < x) :
    model (t+1) x = ruleOut 109 (model t (x-1)) (model t x) (model t (x+1)) := by
  by_cases h0 : t=0
  · subst t
    by_cases h1 : x=1
    · subst x; decide
    · have h2 : 2 ≤ x := by omega
      simp [model,show x ≠ 0 by omega,show x-1 ≠ 0 by omega,show x+1 ≠ 0 by omega,
        show ¬x=1 by omega,show ¬x+1=1 by omega,show 1<x by omega,ruleOut]
  · by_cases interior : x+2<t
    · have h1 : ¬t<x-1 := by omega
      have h2 : x-1≠t := by omega
      have h3 : x-1+1≠t := by omega
      have h4 : ¬t<x := by omega
      have h5 : x≠t := by omega
      have h6 : x+1≠t := by omega
      have h7 : ¬t<x+1 := by omega
      have h8 : x+1+1≠t := by omega
      have h9 : ¬t+1<x := by omega
      have h10 : x≠t+1 := by omega
      have h11 : x+1≠t+1 := by omega
      simp only [model, h0, h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
      exact bits_step t x hx
    · have ht : t%12<12 := Nat.mod_lt _ (by decide)
      have hi : x%12<12 := Nat.mod_lt _ (by decide)
      have ht3 : t%3=(t%12)%3 := by omega
      have ht3p : (t+1)%3=((t%12)%3+1)%3 := by omega
      have ht2 : t%2=(t%12)%2 := by omega
      have ht2p : (t+1)%2=((t%12)%2+1)%2 := by omega
      have hl : (x-1)%12=(x%12+11)%12 := by omega
      have hr : (x+1)%12=(x%12+1)%12 := by omega
      rcases (show x+2=t ∨ x+1=t ∨ x=t ∨ x=t+1 ∨ t+2≤x by omega) with
        hc | hc | hc | hc | hc
      all_goals
        simp (disch := omega) only [model, if_pos, if_neg]
        simp only [bits,ruleOut,ht3p,ht3,ht2p,ht2,hl,hr]

        interval_cases ht' : t%12 <;> interval_cases hi' : x%12
      all_goals first | omega | (norm_num at * <;> decide)

lemma model_center (t : ℕ) :
    model (t+1) 0 = ruleOut 109 (model t 1) (model t 0) (model t 1) := by
  by_cases ht : t < 3
  · interval_cases t <;> decide
  · simpa (disch := omega) only [model, if_neg, if_pos] using bits_center t

lemma rule_symm (l c r : Bool) : ruleOut 109 l c r = ruleOut 109 r c l := by
  cases l <;> cases c <;> cases r <;> decide

lemma cell_mirror (t : ℕ) (i : ℤ) : cell 109 t (-i) = cell 109 t i := by
  induction t generalizing i with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell]
    rw [show -i-1 = -(i+1) by ring,show -i+1 = -(i-1) by ring,ih,ih,ih]
    exact rule_symm _ _ _

lemma cell_nat (t x : ℕ) : cell 109 t (x : ℤ) = model t x := by
  induction t generalizing x with
  | zero => simp [cell,model]
  | succ t ih =>
    cases x with
    | zero =>
      simp only [cell]
      norm_num only [Nat.cast_zero,zero_sub,zero_add]
      have h1 : cell 109 t (1:ℤ) = model t 1 := by simpa only [Nat.cast_one] using ih 1
      have h0 : cell 109 t (0:ℤ) = model t 0 := by simpa only [Nat.cast_zero] using ih 0
      rw [show (-1 : ℤ) = -(1:ℤ) by rfl,cell_mirror,h1,h0]
      exact (model_center t).symm
    | succ x =>
      simp only [cell]
      rw [show ((x+1 : ℕ) : ℤ)-1 = (x:ℤ) by omega,
        show ((x+1 : ℕ) : ℤ)+1 = ((x+2 : ℕ):ℤ) by omega,ih,ih,ih]
      simpa only [Nat.add_sub_cancel] using (model_step t (x+1) (by omega)).symm

/-- Complete spatial pattern for the single-seed Rule 109 automaton. -/
theorem spatial_pattern (t : ℕ) (i : ℤ) : cell 109 t i = model t i.natAbs := by
  cases i with
  | ofNat x => exact cell_nat t x
  | negSucc x =>
    change cell 109 t (-((x+1:ℕ):ℤ)) = model t (x+1)
    rw [cell_mirror,cell_nat]


lemma bits_time_period (t x : ℕ) : bits (t+12) x = bits t x := by
  simp [bits, Nat.add_mod]

lemma bits_space_period (t x : ℕ) : bits t (x+12) = bits t x := by
  simp [bits, Nat.add_mod]

lemma white_block (t off : ℕ) :
    (∑ j ∈ Finset.range 12, if bits t (off+j) then 0 else 1 : ℕ) = 5 := by
  have hs (j : ℕ) : (off+j)%12=(off%12+j)%12 := by omega
  simp only [bits]
  simp_rw [hs]
  have ht : t%3<3 := Nat.mod_lt _ (by decide)
  have hx : off%12<12 := Nat.mod_lt _ (by decide)
  interval_cases ht' : t%3 <;> interval_cases hx' : off%12 <;> decide

def halfWhite (t : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (t-1), if bits t x then 0 else 1

lemma halfWhite_period (t : ℕ) (ht : 0<t) :
    halfWhite (t+12) = halfWhite t + 5 := by
  unfold halfWhite
  simp_rw [bits_time_period]
  rw [show t+12-1=t-1+12 by omega, Finset.sum_range_add, white_block]

end Rule109

namespace Rule109
open Finset OMA.S_oeis_a267214

lemma radial_sum (f : ℕ → ℤ) (t : ℕ) :
    (∑ j ∈ range (2*t+1), f ((j:ℤ)-t).natAbs) =
      2*(∑ j ∈ range (t+1), f j)-f 0 := by
  rw [show 2*t+1=(t+1)+t by omega,sum_range_add]
  have left : (∑ j ∈ range (t+1), f ((j:ℤ)-t).natAbs) =
      ∑ j ∈ range (t+1), f j := by
    calc _ = ∑ j ∈ range (t+1), f (t-j) := by
           apply sum_congr rfl
           intro j hj
           rw [Int.natAbs_natCast_sub_natCast_of_le (by have:=mem_range.mp hj;omega)]
         _ = _ := by simpa using sum_range_reflect f (t+1)
  have right : (∑ j ∈ range t, f (((t+1+j:ℕ):ℤ)-t).natAbs) =
      ∑ j ∈ range t, f (j+1) := by
    apply sum_congr rfl
    intro j hj
    rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega)]
    congr 1
    omega
  rw [left,right]
  have h := sum_range_succ' f t
  linarith

def fullWhite (t : ℕ) : ℤ :=
  ∑ j ∈ range (2*t+1), if cell 109 t ((j:ℤ)-t) then 0 else 1

lemma model_interior (t x : ℕ) (ht : 0<t) (hx : x<t-1) :
    model t x = bits t x := by
  simp (disch := omega) only [model,if_pos,if_neg,ite_true]

lemma model_penultimate (t : ℕ) (ht : 0<t) : model t (t-1) = true := by
  simp (disch := omega) only [model,if_pos,if_neg,ite_true]

lemma model_last (t : ℕ) (ht : 0<t) : model t t = decide (t%2=0) := by
  simp (disch := omega) only [model,if_pos,if_neg,ite_true]

lemma model_zero (t : ℕ) (ht : 0<t) : model t 0 = bits t 0 := by
  by_cases h1 : t=1
  · subst t; decide
  · exact model_interior t 0 ht (by omega)

lemma fullWhite_formula (t : ℕ) (ht : 0<t) :
    fullWhite t = 2*(halfWhite t:ℤ)+2*(t%2:ℕ)-
      (if t%3=0 then 1 else 0) := by
  unfold fullWhite
  simp_rw [spatial_pattern]
  rw [radial_sum (fun r => if model t r then (0:ℤ) else 1) t]
  have hs : (∑ j ∈ range (t+1), if model t j then (0:ℤ) else 1) =
      (halfWhite t:ℤ)+(t%2:ℕ) := by
    rw [show t+1=(t-1)+1+1 by omega,sum_range_succ,sum_range_succ]
    have h1 : t-1+1=t := by omega
    rw [h1,model_last t ht,model_penultimate t ht]
    have he : (if decide (t%2=0) then (0:ℤ) else 1) = (t%2:ℕ) := by
      have hm : t%2<2 := Nat.mod_lt _ (by decide)
      interval_cases h : t%2 <;> decide
    rw [he]
    simp only [Bool.true_eq,ite_true,add_zero]
    congr 1
    unfold halfWhite
    rw [Nat.cast_sum]
    apply sum_congr rfl
    intro j hj
    rw [model_interior t j ht (mem_range.mp hj)]
    split <;> simp
  rw [hs,model_zero t ht]
  have hb : (if bits t 0 then (0:ℤ) else 1) = if t%3=0 then 1 else 0 := by
    unfold bits
    have hm : t%3<3 := Nat.mod_lt _ (by decide)
    interval_cases h : t%3 <;> decide
  rw [hb]
  ring

theorem fullWhite_period (t : ℕ) (ht : 0<t) :
    fullWhite (t+12) = fullWhite t + 10 := by
  rw [fullWhite_formula (t+12) (by omega),fullWhite_formula t ht,
    halfWhite_period t ht]
  rw [show (t+12)%2=t%2 by omega,show (t+12)%3=t%3 by omega]
  push_cast
  ring

lemma fullWhite_eq (t : ℕ) :
    fullWhite t = ((2*t+1 : ℕ) : ℤ) - (onCount 109 t : ℤ) := by
  unfold fullWhite onCount
  rw [Nat.cast_sum]
  calc
    _ = (∑ j ∈ range (2*t+1), ((1:ℤ) -
      (if cell 109 t ((j:ℤ)-t) then (1:ℤ) else 0))) := by
      apply sum_congr rfl
      intro j hj
      split <;> simp_all
    _ = _ := by
      rw [sum_sub_distrib]
      simp

lemma a_succ (t : ℕ) : a (t+1) = a t + fullWhite (t+1) := by
  unfold a
  rw [sum_range_succ,fullWhite_eq]
  push_cast
  ring

end Rule109

namespace Rule109
open OMA.S_oeis_a267214

lemma white_four_base (t : Fin 12) :
    fullWhite (t.val+1+7) = fullWhite (t.val+1+4) + fullWhite (t.val+1+3) - fullWhite (t.val+1) := by
  fin_cases t <;> simp (disch := omega) only [fullWhite_formula] <;> decide

lemma white_four (t : ℕ) (ht : 0<t) :
    fullWhite (t+7) = fullWhite (t+4)+fullWhite (t+3)-fullWhite t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases small : t≤12
    · simpa only [show t-1+1=t by omega] using
        white_four_base ⟨t-1,by omega⟩
    · have hs : 0<t-12 := by omega
      have h := ih (t-12) (by omega) hs
      have w0 := fullWhite_period (t-12) hs
      have w3 := fullWhite_period (t-12+3) (by omega)
      have w4 := fullWhite_period (t-12+4) (by omega)
      have w7 := fullWhite_period (t-12+7) (by omega)
      simp only [show t-12+12=t by omega,
        show t-12+3+12=t+3 by omega,
        show t-12+4+12=t+4 by omega,
        show t-12+7+12=t+7 by omega] at w0 w3 w4 w7
      linarith

theorem recurrence_int (n : ℕ) (hn : 8≤n) :
    a n = a (n-1)+a (n-3)-a (n-5)-a (n-7)+a (n-8) := by
  have h0 := a_succ (n-1)
  have h3 := a_succ (n-4)
  have h4 := a_succ (n-5)
  have h7 := a_succ (n-8)
  simp only [show n-1+1=n by omega,show n-4+1=n-3 by omega,
    show n-5+1=n-4 by omega,show n-8+1=n-7 by omega] at h0 h3 h4 h7
  have hw := white_four (n-7) (by omega)
  simp only [show n-7+7=n by omega,show n-7+4=n-3 by omega,
    show n-7+3=n-4 by omega] at hw
  linarith

theorem recurrence (n : ℕ) (hn : 8≤n) :
    (a n : ℚ) = a (n-1)+a (n-3)-a (n-5)-a (n-7)+a (n-8) := by
  exact_mod_cast recurrence_int n hn
end Rule109

namespace Rule109
open OMA.S_oeis_a267214 PowerSeries

lemma initial : a 0=0 ∧ a 1=2 ∧ a 2=2 ∧ a 3=7 ∧ a 4=9 ∧ a 5=13 ∧ a 6=16 ∧ a 7=26 := by
  have h0 : a 0=0 := by norm_num [a,onCount,cell]
  have w1 : fullWhite 1=2 := by rw [fullWhite_formula 1 (by decide)]; decide
  have w2 : fullWhite 2=0 := by rw [fullWhite_formula 2 (by decide)]; decide
  have w3 : fullWhite 3=5 := by rw [fullWhite_formula 3 (by decide)]; decide
  have w4 : fullWhite 4=2 := by rw [fullWhite_formula 4 (by decide)]; decide
  have w5 : fullWhite 5=4 := by rw [fullWhite_formula 5 (by decide)]; decide
  have w6 : fullWhite 6=3 := by rw [fullWhite_formula 6 (by decide)]; decide
  have w7 : fullWhite 7=10 := by rw [fullWhite_formula 7 (by decide)]; decide
  have h1 := a_succ 0
  have h2 := a_succ 1
  have h3 := a_succ 2
  have h4 := a_succ 3
  have h5 := a_succ 4
  have h6 := a_succ 5
  have h7 := a_succ 6
  norm_num only at h1 h2 h3 h4 h5 h6 h7
  exact ⟨h0,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem generating_function :
    (PowerSeries.mk (fun n => (a n : ℚ))) *
      ((1-X)^3*(1+X)*(1+X^2)*(1+X+X^2):PowerSeries ℚ) =
      X*(2+5*X^2+2*X^4-2*X^5+3*X^6) := by
  let F := PowerSeries.mk (fun n => (a n : ℚ))
  change F * _ = _
  have he : F * ((1-X)^3*(1+X)*(1+X^2)*(1+X+X^2)) =
      F-F*X^1-F*X^3+F*X^5+F*X^7-F*X^8 := by ring
  have hp : (X*(2+5*X^2+2*X^4-2*X^5+3*X^6) : PowerSeries ℚ) =
      C 2 * X^1 + C 5 * X^3 + C 2 * X^5 - C 2 * X^6 + C 3 * X^7 := by
    simp only [map_ofNat]
    ring
  rw [he,hp]
  ext n
  simp only [map_sub,map_add,coeff_C_mul_X_pow,coeff_mul_X_pow',coeff_C,coeff_X_pow,coeff_mk,
    nsmul_eq_mul,F]
  by_cases hn : 8≤n
  · have h := recurrence n hn
    simp (disch := omega) only [if_pos,if_neg]
    linarith
  · obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := initial
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4,h5,h6,h7]

theorem solution : type_of% @OMA.S_oeis_a267214.main :=
  ⟨fun n hn => recurrence n hn, generating_function⟩
end Rule109

theorem OMA.solution : type_of% @OMA.S_oeis_a267214.main := Rule109.solution
