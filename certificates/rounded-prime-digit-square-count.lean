import certificates.«digit-square-mmr-local-limit»

/-!
# A lower bound at integer powers of ten

Theorem 1 of Martin, Mauduit and Rivat is used through its explicit
frequency-zero hypothesis UniformEstimate. Rounding the central digit
length down moves the target by less than 57/2. The Gaussian factor is
then at least exp(-1), which gives the displayed lower bound eventually.
-/

open Filter Finset
namespace DigitSquarePrimes.LocalLimit.Rounded
open DigitSquarePrimes.LocalLimit

private noncomputable def width : ℝ := Real.sqrt (2 * Real.pi * (14421/20))
private noncomputable def coeff : ℝ := Real.exp (-1)/(2*width)

private theorem width_pos : 0 < width := by unfold width; positivity
private theorem coeff_pos : 0 < coeff := by
  unfold coeff
  exact div_pos (Real.exp_pos _) (mul_pos (by norm_num) width_pos)

private lemma central_band (n k : ℕ) (hk : 1 ≤ k)
    (lo : 57*k ≤ 2*n) (hi : 2*n < 57*(k+1)) :
    2*coeff*((primesBelow ((10:ℝ)^k)).card:ℝ)/Real.sqrt (k:ℝ) ≤
      mainTerm ((10:ℝ)^k) n := by
  have kr : (1:ℝ) ≤ k := by exact_mod_cast hk
  have lg : Real.log ((10:ℝ)^k)/Real.log 10 = k := by
    rw [Real.log_pow]
    exact mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos (by norm_num)))
  have mean : meanAt ((10:ℝ)^k) = (57/2)*(k:ℝ) := by unfold meanAt; rw [lg]
  have variance : varianceAt ((10:ℝ)^k) = (14421/20)*(k:ℝ) := by unfold varianceAt; rw [lg]
  have lor : (57:ℝ)*k ≤ 2*n := by exact_mod_cast lo
  have hir : (2:ℝ)*n < 57*(k+1) := by exact_mod_cast hi
  have left : 0 ≤ (n:ℝ) - (57/2)*k := by linarith
  have right : (n:ℝ) - (57/2)*k ≤ 29 := by linarith
  have square : ((n:ℝ)-(57/2)*k)^2 ≤ 29^2 :=
    (sq_le_sq₀ left (by norm_num)).mpr right
  have vpos : 0 < 2*((14421/20:ℝ)*k) := by linarith
  have exponent : -1 ≤ -((n:ℝ)-(57/2)*k)^2/(2*((14421/20)*k)) := by
    apply (le_div_iff₀ vpos).mpr
    linarith
  have root : Real.sqrt (2*Real.pi*((14421/20)*(k:ℝ))) = width*Real.sqrt (k:ℝ) := by
    unfold width
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  unfold mainTerm
  rw [mean,variance,root]
  calc
    _ = (((primesBelow ((10:ℝ)^k)).card:ℝ)/(width*Real.sqrt (k:ℝ))) * Real.exp (-1) := by
      unfold coeff
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponent)
      (div_nonneg (by positivity) (mul_nonneg width_pos.le (Real.sqrt_nonneg _)))

private lemma error_small (C : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      C/(Real.log ((10:ℝ)^k))^(3/4:ℝ) ≤ coeff/Real.sqrt (k:ℝ) := by
  let d := (Real.log 10)^(3/4:ℝ)
  have ld : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have dp : 0 < d := Real.rpow_pos_of_pos ld _
  have grow := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (C/(coeff*d))
  filter_upwards [grow,eventually_ge_atTop 1] with k large hk
  change C/(coeff*d) ≤ (k:ℝ)^(1/4:ℝ) at large
  have kr : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have sr := Real.sqrt_pos.mpr kr
  have rootpower : Real.sqrt (k:ℝ) * (k:ℝ)^(1/4:ℝ) = (k:ℝ)^(3/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add kr]
    norm_num
  have denominator : (Real.log ((10:ℝ)^k))^(3/4:ℝ) =
      (Real.sqrt (k:ℝ) * (k:ℝ)^(1/4:ℝ))*d := by
    rw [rootpower,Real.log_pow,Real.mul_rpow kr.le ld.le]
  rw [denominator]
  apply (div_le_div_iff₀ (mul_pos (mul_pos sr (Real.rpow_pos_of_pos kr _)) dp) sr).mpr
  have c := (div_le_iff₀ (mul_pos coeff_pos dp)).mp large
  calc
    _ ≤ ((k:ℝ)^(1/4:ℝ)*(coeff*d)) * Real.sqrt (k:ℝ) := mul_le_mul_of_nonneg_right c sr.le
    _ = _ := by ring

private lemma root_small :
    ∀ᶠ k : ℕ in atTop, Real.sqrt (k:ℝ) ≤ 16*(k:ℝ)*coeff := by
  have grow := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (1/(16*coeff))
  filter_upwards [grow] with k large
  have p : (0:ℝ) < 16*coeff := mul_pos (by norm_num) coeff_pos
  change 1/(16*coeff) ≤ Real.sqrt (k:ℝ) at large
  have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ p).mp large) (Real.sqrt_nonneg (k:ℝ))
  rw [one_mul] at h
  calc
    _ ≤ _ := h
    _ = (16*coeff)*(Real.sqrt (k:ℝ))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity)]; ring

private lemma sizes_grow : Tendsto (fun n : ℕ => 2*n/57) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro m
  filter_upwards [eventually_ge_atTop (57*m)] with n bound
  change m ≤ 2*n/57
  omega

theorem eventually_central_count {C : ℝ} (estimate : UniformEstimate C) :
    ∀ᶠ n : ℕ in atTop,
      let P := Nat.primesLE (10 ^ (2*n/57))
      P.card ≤ (16*n) * (P.filter (fun p => squareSum p = n)).card := by
  have powers : Tendsto (fun k : ℕ => (10:ℝ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [(powers.comp sizes_grow).eventually estimate,
    sizes_grow.eventually (error_small C), sizes_grow.eventually root_small,
    sizes_grow.eventually_ge_atTop 1] with n bound err root hk
  let k := 2*n/57
  let x := (10:ℝ)^k
  let P : ℝ := (primesBelow x).card
  let H : ℝ := (hitsBelow x n).card
  have posk : (0:ℝ)<k := by exact_mod_cast (show 0<k by exact hk)
  have sr := Real.sqrt_pos.mpr posk
  have k_le : (k:ℝ) ≤ n := by exact_mod_cast (show k ≤ n by dsimp [k]; omega)
  have band : 2*coeff*P/Real.sqrt (k:ℝ) ≤ mainTerm x n :=
    central_band n k hk (by dsimp [k]; omega) (by dsimp [k]; omega)
  specialize bound n
  change |H-mainTerm x n| ≤ C*P/(Real.log x)^(3/4:ℝ) at bound
  change C/(Real.log x)^(3/4:ℝ) ≤ coeff/Real.sqrt (k:ℝ) at err
  have nonneg : 0 ≤ P := by dsimp [P]; positivity
  have many : coeff*P/Real.sqrt (k:ℝ) ≤ H := by
    have low := (abs_le.mp bound).1
    have e := mul_le_mul_of_nonneg_right err nonneg
    have aligned : C*P/(Real.log x)^(3/4:ℝ) ≤ coeff*P/Real.sqrt (k:ℝ) := calc
      _ = (C/(Real.log x)^(3/4:ℝ))*P := by ring
      _ ≤ _ := e
      _ = _ := by ring
    have twice : 2*(coeff*P/Real.sqrt (k:ℝ)) ≤ mainTerm x n := calc
      _ = 2*coeff*P/Real.sqrt (k:ℝ) := by ring
      _ ≤ _ := band
    linarith only [low,aligned,twice]
  have den : Real.sqrt (k:ℝ) ≤ (16*(n:ℝ))*coeff := calc
    _ ≤ 16*(k:ℝ)*coeff := root
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) coeff_pos.le
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have result : P ≤ (16*(n:ℝ))*H := by
    apply (mul_le_mul_iff_right₀ coeff_pos).mp
    calc
      coeff*P ≤ H*Real.sqrt (k:ℝ) := (div_le_iff₀ sr).mp many
      _ ≤ H*((16*(n:ℝ))*coeff) := mul_le_mul_of_nonneg_left den hH
      _ = _ := by ring
  have castPower : (((10:ℕ)^k : ℕ):ℝ) = x := by simp [x]
  have floorPower : ⌊x⌋₊ = (10:ℕ)^k := by rw [←castPower,Nat.floor_natCast]
  change ((primesBelow x).card:ℝ) ≤ (16*(n:ℝ))*((hitsBelow x n).card:ℝ) at result
  simp only [hitsBelow,primesBelow,floorPower] at result
  exact_mod_cast result

end DigitSquarePrimes.LocalLimit.Rounded
