import OMAStatements.S_oeis_a115526
import Mathlib

/-!
# Inverse row sums and binary zero counts

Credit: @VestigeClub.
Source: https://oeis.org/A115526 (Paul Barry).

Each row of the original triangle has a signed diagonal entry and, except
for row zero, the opposite entry at one strictly earlier column. This makes
the matrix invertible and gives a recurrence for its action on a vector.
The binary zero counts satisfy that recurrence with right-hand side one.
Multiplying by the inverse identifies every inverse row sum.
-/


namespace InverseBinaryTriangle

def earlier (r : ℕ) : ℕ := if r % 2 = 0 then r/2 - 1 else r - 1

def earlierCol {n : ℕ} (i : Fin (n+1)) : Fin (n+1) :=
  ⟨earlier i.val, by have h := i.isLt; unfold earlier; split <;> omega⟩

def sign (r : ℕ) : ℚ := if r % 2 = 0 then 1 else -1

def corner (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  Matrix.of fun i j =>
    (if j = i then sign i.val else 0) -
    (if 0 < i.val then (if j = earlierCol i then sign i.val else 0) else 0)

def zeros (m : ℕ) : ℕ := ((2 : ℕ).digits m).count 0

theorem earlier_lt (r : ℕ) (hr : 0 < r) : earlier r < r := by
  unfold earlier
  split <;> omega

theorem sign_ne_zero (r : ℕ) : sign r ≠ 0 := by
  unfold sign
  split <;> norm_num

theorem mulVec_eq (n : ℕ) (v : Fin (n+1) → ℚ) (i : Fin (n+1)) :
    (corner n).mulVec v i = sign i.val *
      (v i - if 0 < i.val then v (earlierCol i) else 0) := by
  classical
  by_cases hz : i = 0
  · subst i
    simp [Matrix.mulVec, dotProduct, corner, sub_mul, ite_mul, Finset.sum_sub_distrib]
  · have hi : 0 < i.val := by
      have : i.val ≠ 0 := fun h => hz (Fin.ext h)
      omega
    simp [Matrix.mulVec, dotProduct, corner, sub_mul, ite_mul,
      Finset.sum_sub_distrib, hi, hz, mul_sub]

theorem corner_injective (n : ℕ) : Function.Injective (corner n).mulVec := by
  intro v w h
  have heq : ∀ r, (hr : r < n+1) → v ⟨r,hr⟩ = w ⟨r,hr⟩ := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr
      have hh := congrFun h (⟨r,hr⟩ : Fin (n+1))
      rw [mulVec_eq, mulVec_eq] at hh
      have hc := (mul_left_cancel₀ (sign_ne_zero r)) hh
      by_cases hz : 0 < r
      · have hprev := ih (earlier r) (earlier_lt r hz) (lt_trans (earlier_lt r hz) hr)
        simpa [hz, earlierCol, hprev] using hc
      · simpa [hz] using hc
  funext i
  exact heq i.val i.isLt

theorem corner_det_unit (n : ℕ) : IsUnit (corner n).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp (corner_injective n))

end InverseBinaryTriangle

namespace InverseBinaryTriangle

theorem zeros_even (m : ℕ) (hm : 0 < m) : zeros (2*m) = zeros m + 1 := by
  have hd := Nat.digits_add 2 (by decide) 0 m (by decide) (Or.inr (Nat.ne_of_gt hm))
  simp only [Nat.zero_add] at hd
  simp [zeros, hd]

theorem zeros_odd (m : ℕ) : zeros (2*m+1) = zeros m := by
  have hd := Nat.digits_add 2 (by decide) 1 m (by decide) (Or.inl (by decide))
  rw [Nat.add_comm] at hd
  change (Nat.digits 2 (2*m+1)).count 0 = (Nat.digits 2 m).count 0
  rw [hd]
  simp

theorem zeros_predecessor (r : ℕ) :
    (zeros (r+2) : ℚ) = sign r + if 0 < r then (zeros (earlier r+2) : ℚ) else 0 := by
  by_cases hz : r=0
  · subst r
    norm_num [sign, show zeros 2 = 1 from by decide]
  have hr : 0 < r := by omega
  rw [if_pos hr]
  by_cases he : r%2=0
  · have hq : 0 < r/2 := by omega
    have h1 : r+2 = 2*(r/2+1) := by omega
    have h2 : r/2-1+2 = r/2+1 := by omega
    rw [h1, zeros_even _ (by omega)]
    simp [sign, earlier, he, h2, add_comm]
  · have hmod : r%2=1 := by omega
    have h1 : r+2=2*(r/2+1)+1 := by omega
    have h2 : r-1+2=2*(r/2+1) := by omega
    rw [h1, zeros_odd]
    simp only [sign, earlier, if_neg he, h2, zeros_even _ (by omega : 0<r/2+1), Nat.cast_add, Nat.cast_one]
    ring

end InverseBinaryTriangle

namespace InverseBinaryTriangle

theorem sign_sq (r : ℕ) : sign r * sign r = 1 := by
  unfold sign
  split <;> norm_num

theorem zero_vector_solution (n : ℕ) :
    (corner n).mulVec (fun i => (zeros (i.val+2) : ℚ)) = fun _ => 1 := by
  funext i
  rw [mulVec_eq]
  have h := zeros_predecessor i.val
  have hs := sign_sq i.val
  by_cases hi : 0 < i.val
  · simp only [hi, if_true, earlierCol] at h ⊢
    rw [h]
    nlinarith
  · simp only [hi, if_false] at h ⊢
    rw [h]
    simpa using hs

theorem row_sum (n : ℕ) :
    (∑ j : Fin (n+1), (corner n)⁻¹ (Fin.last n) j) = (zeros (n+2) : ℚ) := by
  have h : ((corner n)⁻¹).mulVec (fun _ => (1 : ℚ)) = fun i => (zeros (i.val+2) : ℚ) := by
    rw [← zero_vector_solution n, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (corner_det_unit n)]
    simp
  simpa [Matrix.mulVec, dotProduct] using congrFun h (Fin.last n)

end InverseBinaryTriangle

theorem OMA.solution : type_of% @OMA.S_oeis_a115526.main := by
  intro n
  exact InverseBinaryTriangle.row_sum n
