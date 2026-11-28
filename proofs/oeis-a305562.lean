import OMAStatements.S_oeis_a305562

/-!
A305562 and the diagonal numerators of A386393.
The recurrence identity follows the known solution of Max Alekseyev:
https://mathoverflow.net/a/498031
OEIS identity proposed by Mikhail Kurkov; sequence by Michael Somos.

The binomial transform gives row n 0 = a n / 2^(n(n-1)/2).
Every a n is odd, so this fraction already has numerator a n.
-/

namespace A305562Proof
open OMA.S_oeis_a305562 Finset
def b (n : ℕ) : ℚ := row n 0
lemma row_formula (k n : ℕ) (hk : k ≤ n) :
    row n k = ∑ i ∈ range (k+1), (k.choose i : ℚ) * (1/2:ℚ)^(k-i) * b (n-i) := by
  induction k generalizing n with
  | zero => simp [b]
  | succ k ih =>
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [row, ih (m+1) (by omega), ih m (by omega)]
    have hs := Finset.sum_choose_succ_mul
      (R := ℚ) (fun i j => (1/2:ℚ)^j * b (m+1-i)) k
    simp only [mul_assoc] at *
    rw [hs]
    congr 1
    · rw [div_eq_mul_inv, sum_mul]
      apply sum_congr rfl
      intro i hi
      have hi' : i ≤ k := by simpa using (mem_range.mp hi)
      rw [show k+1-i = (k-i)+1 by omega, pow_succ]
      ring
    · apply sum_congr rfl
      intro i hi
      rw [show m+1-(i+1) = m-i by omega]

lemma b_recurrence (n : ℕ) :
    b (n+1) = ∑ j ∈ range (n+1), (n.choose j : ℚ) * (1/2:ℚ)^j * b j := by
  conv_lhs => simp only [b, row]
  rw [row_formula n n le_rfl, ← sum_range_reflect
    (fun i => (n.choose i : ℚ) * (1/2:ℚ)^(n-i) * b (n-i)) (n+1)]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ n := by simpa using mem_range.mp hj
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hj', Nat.choose_symm hj']

lemma tri_mono : Monotone tri := by
  apply monotone_nat_of_le_succ
  intro n
  simp [tri]

lemma b_normalized (n : ℕ) : b n = (a n : ℚ) / 2^(tri n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => norm_num [b, row, a, tri]
    | succ n =>
      rw [b_recurrence]
      simp only [a, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [Fin.sum_univ_eq_sum_range (fun j => (n.choose j : ℚ) * (a j : ℚ) * (2 : ℚ)^(tri (n+1)-tri (j+1))) (n+1), sum_div]
      apply sum_congr rfl
      intro j hj
      have jn : j < n+1 := mem_range.mp hj
      rw [ih j jn]
      have ht : tri (j+1) ≤ tri (n+1) := tri_mono (by omega)
      have hx : tri (n+1)-tri (j+1)+tri (j+1) = tri (n+1) := Nat.sub_add_cancel ht
      rw [one_div_pow]
      have hz : (2:ℚ) ^ tri (n+1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hzj : (2:ℚ) ^ tri j ≠ 0 := pow_ne_zero _ (by norm_num)
      have hzjp : (2:ℚ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
      have he : (2:ℚ)^tri (n+1) =
          2^(tri (n+1)-tri (j+1)) * (2^tri j * 2^j) := by
        rw [←pow_add, ←tri, ←pow_add, hx]
      rw [he]
      field_simp



lemma a_odd (n : ℕ) : Odd (a n) := by
  induction n with
  | zero => norm_num [a]
  | succ n ih =>
    rw [a, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.choose_self,
      Nat.sub_self, pow_zero, mul_one, one_mul]
    apply Even.add_odd _ ih
    apply Finset.even_sum
    intro i hi
    have hin : i.val < n := i.isLt
    have hm : tri (i.val+1) ≤ tri n := tri_mono (by omega)
    have hp : 0 < tri (n+1)-tri (i.val+1) := by
      rw [tri]
      omega
    refine ⟨n.choose i.val * a i.val * 2^(tri (n+1)-tri (i.val+1)-1), ?_⟩
    conv_lhs => rw [show tri (n+1)-tri (i.val+1) =
      (tri (n+1)-tri (i.val+1)-1)+1 by omega, pow_succ]
    ring

lemma solution (n : ℕ) (hn : 0 < n) :
    (a n : ℤ) = (row (n-1) (n-1)).num := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := b_normalized (m+1)
  simp only [b, row] at h
  simp only [Nat.succ_sub_one]
  rw [h]
  symm
  have hc : (a (m+1)).Coprime (2^tri (m+1)) :=
    (a_odd (m+1)).coprime_two_right.pow_right (tri (m+1))
  have hr := Rat.num_div_eq_of_coprime (a := (a (m+1) : ℤ))
    (b := ((2^tri (m+1) : ℕ) : ℤ)) (by positivity) (by simpa using hc)
  simpa only [Int.cast_natCast, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat, Nat.succ_eq_add_one] using hr

lemma small_values :
    [row 0 0, row 1 1, row 2 2, row 3 3] =
      [1,3/2,19/8,251/64] := by norm_num [row]
end A305562Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a305562.main :=
  A305562Proof.solution
