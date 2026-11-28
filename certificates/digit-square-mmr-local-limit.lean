import certificates.«digit-square-local-limit-consequence»

/-!
# Finite exceptions from the uniform prime local limit theorem

This specializes Theorem 1 of Martin, Mauduit and Rivat to frequency zero,
digit weights 0² to 9², and error exponent three quarters. The analytic estimate
is an explicit hypothesis. All subsequent steps and the choice of cutoff are proved.
https://www-lmpa.univ-littoral.fr/~martin/mmrp3-v7.pdf
-/
open Filter Finset
namespace DigitSquarePrimes.LocalLimit

noncomputable def primesBelow (x : ℝ) := Nat.primesLE ⌊x⌋₊
noncomputable def hitsBelow (x : ℝ) (n : ℕ) :=
  (primesBelow x).filter (fun p => squareSum p=n)
noncomputable def meanAt (x : ℝ) : ℝ := (57/2) * (Real.log x / Real.log 10)
noncomputable def varianceAt (x : ℝ) : ℝ := (14421/20) * (Real.log x / Real.log 10)
noncomputable def mainTerm (x : ℝ) (n : ℕ) : ℝ :=
  ((primesBelow x).card : ℝ) / Real.sqrt (2*Real.pi*varianceAt x) *
    Real.exp (-((n : ℝ)-meanAt x)^2/(2*varianceAt x))

/-- The uniform counting estimate at frequency zero, with epsilon one quarter. -/
def UniformEstimate (C : ℝ) : Prop := ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
  |((hitsBelow x n).card : ℝ) - mainTerm x n|
    ≤ C * ((primesBelow x).card : ℝ) / (Real.log x)^(3/4 : ℝ)

private noncomputable def spread : ℝ := 2*Real.pi*(14421/20)/Real.log 10

private theorem spread_pos : 0<spread := by
  unfold spread
  positivity

private theorem log_scale_tends :
    Tendsto (fun n : ℕ => Real.log (scale n)) atTop atTop := by
  have t : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h : 0 < 2 * Real.log 10 / 57 := by positivity
  refine (t.atTop_mul_const h).congr ?_
  intro n
  simp only [scale,Real.log_exp]
  ring

private theorem scale_tends : Tendsto scale atTop atTop := by
  refine (Real.tendsto_exp_atTop.comp log_scale_tends).congr ?_
  intro n
  exact Real.exp_log (Real.exp_pos _)

private theorem select_mean (n : ℕ) : meanAt (scale n) = n := by
  have h : Real.log 10 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold meanAt scale
  rw [Real.log_exp]
  field_simp

private theorem pi_pos {x : ℝ} (hx : 2≤x) : 0 < ((primesBelow x).card : ℝ) := by
  have two : 2 ∈ primesBelow x :=
    Nat.mem_primesLE.mpr ⟨Nat.le_floor (by exact_mod_cast hx),Nat.prime_two⟩
  exact_mod_cast Finset.card_pos.mpr ⟨2,two⟩

private theorem error_smaller {C x : ℝ} (hx : 2≤x) (large : C * Real.sqrt spread < (Real.log x)^(1/4 : ℝ)) :
    C * ((primesBelow x).card : ℝ) / (Real.log x)^(3/4 : ℝ) <
      ((primesBelow x).card : ℝ) / Real.sqrt (2*Real.pi*varianceAt x) := by
  have positive : 0<Real.log x := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr positive
  have hd : 0 < Real.sqrt spread := Real.sqrt_pos.mpr spread_pos
  have hq := Real.rpow_pos_of_pos positive (1/4 : ℝ)
  have power : (Real.log x)^(3/4 : ℝ) =
      Real.sqrt (Real.log x) * (Real.log x)^(1/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add positive]
    norm_num
  have root : Real.sqrt (2*Real.pi*varianceAt x) =
      Real.sqrt spread * Real.sqrt (Real.log x) := by
    rw [←Real.sqrt_mul spread_pos.le]
    congr 1
    unfold spread varianceAt
    ring
  rw [power,root]
  apply (div_lt_div_iff₀ (mul_pos hs hq) (mul_pos hd hs)).mpr
  calc
    _ = (C*Real.sqrt spread) * (((primesBelow x).card : ℝ)*Real.sqrt (Real.log x)) := by ring
    _ < ((Real.log x)^(1/4 : ℝ)) * (((primesBelow x).card : ℝ)*Real.sqrt (Real.log x)) :=
      mul_lt_mul_of_pos_right large (mul_pos (pi_pos hx) hs)
    _ = _ := by ring

theorem covered_from_uniform {C : ℝ} (estimate : UniformEstimate C) :
    ∀ᶠ n : ℕ in atTop, Attained n := by
  have atScale := scale_tends.eventually estimate
  have high := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp log_scale_tends).eventually_gt_atTop
    (C * Real.sqrt spread)
  filter_upwards [atScale,high,scale_tends.eventually_ge_atTop 2] with n atN large hx
  specialize atN n
  change C * Real.sqrt spread < (Real.log (scale n))^(1/4 : ℝ) at large
  have small := error_smaller hx large
  have positive : 0 < ((primesBelow (scale n)).card : ℝ) / Real.sqrt (2*Real.pi*varianceAt (scale n)) := by
    have hlog : 0 < Real.log (scale n) := Real.log_pos (by linarith)
    have hv : 0 < varianceAt (scale n) := by unfold varianceAt; positivity
    exact div_pos (pi_pos hx) (Real.sqrt_pos.mpr (by positivity))
  have noneImpossible : (hitsBelow (scale n) n).Nonempty := by
    by_contra empty
    have zero := Finset.not_nonempty_iff_eq_empty.mp empty
    rw [zero] at atN
    simp only [Finset.card_empty,Nat.cast_zero,mainTerm,select_mean,sub_self,
      zero_pow (by decide : (2:ℕ)≠0),neg_zero,zero_div,Real.exp_zero,mul_one,
      zero_sub,abs_neg,abs_of_pos positive] at atN
    exact (not_le_of_gt small) atN
  obtain ⟨p,hp⟩ := noneImpossible
  obtain ⟨pr,eq⟩ := mem_filter.mp hp
  exact ⟨p,Nat.prime_of_mem_primesLE pr,eq⟩

theorem finitely_many_exceptions {C : ℝ} (estimate : UniformEstimate C) :
    {n : ℕ | ¬ Attained n}.Finite := by
  obtain ⟨N,ok⟩ := Filter.eventually_atTop.mp (covered_from_uniform estimate)
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  change ¬ Attained n at hn
  by_contra! h
  exact hn (ok n h)

end DigitSquarePrimes.LocalLimit
