import OMAStatements.S_oeis_a144636

namespace BalaParity
open PowerSeries

noncomputable def polynomial : ℤ⟦X⟧ := 6*X^3+3*X^2+X

theorem integral_inverse : ∃ B : ℤ⟦X⟧,
    constantCoeff B = 0 ∧ 6*B^3+3*B^2+B = X := by
  have h0 : constantCoeff polynomial = 0 := by simp [polynomial]
  have h1 : coeff 1 polynomial = 1 := by
    have e6 : (6 : ℤ⟦X⟧) = C 6 := by norm_num
    have e3 : (3 : ℤ⟦X⟧) = C 3 := by norm_num
    simp only [polynomial,map_add,e6,e3,coeff_C_mul,coeff_X_pow,coeff_X]
    norm_num
  have hu : IsUnit (coeff 1 polynomial) := h1 ▸ isUnit_one
  let B := polynomial.substInvOfIsUnit hu
  have hb : HasSubst B := HasSubst.substInvOfIsUnit polynomial hu
  have hx : (substAlgHom (R:=ℤ) hb) X = B := by
    rw [coe_substAlgHom]
    exact subst_X hb
  have h : (substAlgHom (R:=ℤ) hb) polynomial = X := by
    rw [coe_substAlgHom]
    exact subst_substInvOfIsUnit_right polynomial h0 hu
  refine ⟨B,constantCoeff_substInvOfIsUnit polynomial hu,?_⟩
  simpa only [polynomial,map_add,map_mul,map_pow,map_ofNat,hx] using h

lemma square_eq_expand (F : (ZMod 2)⟦X⟧) :
    F^2 = expand 2 (by decide) F := by
  have h := MvPowerSeries.map_frobenius_expand (R:=ZMod 2) (f:=F) 2 (by decide)
  have fid : frobenius (ZMod 2) 2 = RingHom.id _ := by
    ext z
    fin_cases z <;> decide
  change PowerSeries.map (frobenius (ZMod 2) 2) (expand 2 (by decide) F) = F^2 at h
  rw [fid] at h
  exact h.symm

theorem powers_characterize (F : (ZMod 2)⟦X⟧) (hF : F^2+F=X) (n : ℕ) (hn : 1≤n) :
    coeff n F = 1 ↔ ∃ k : ℕ, n=2^k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have point := congrArg (coeff n (R:=ZMod 2)) hF
    rw [map_add,square_eq_expand, coeff_expand, coeff_X] at point
    by_cases h1 : n=1
    · subst n
      norm_num at point
      exact ⟨fun _ => ⟨0,rfl⟩,fun _ => point⟩
    have hn2 : 2≤n := by omega
    by_cases hd : 2∣n
    · rw [if_pos hd, if_neg h1] at point
      have cancel : ∀ x y : ZMod 2, x+y=0 → y=x := by decide
      rw [cancel _ _ point, ih (n/2) (by omega) (by omega)]
      have eq : n = 2*(n/2) := (Nat.mul_div_cancel' hd).symm
      constructor
      · rintro ⟨j,hj⟩
        exact ⟨j+1,by rw [eq,hj,pow_succ]; ring⟩
      · rintro ⟨j,hj⟩
        cases j with
        | zero => simp at hj; contradiction
        | succ j =>
          refine ⟨j,?_⟩
          rw [pow_succ] at hj
          omega
    · rw [if_neg hd,if_neg h1,zero_add] at point
      constructor
      · intro hi
        rw [point] at hi
        exact False.elim ((by decide : (0 : ZMod 2) ≠ 1) hi)
      · rintro ⟨j,hj⟩
        cases j with
        | zero => simp at hj; contradiction
        | succ j =>
          rw [pow_succ] at hj
          exact (hd ⟨2^j,by omega⟩).elim

theorem scaled_eq (A : ℚ⟦X⟧) (hA0 : constantCoeff A=0)
    (hA : A^3+3*A^2+6*A=6*X) (B : ℤ⟦X⟧) (hB0 : constantCoeff B=0)
    (hB : 6*B^3+3*B^2+B=X) (n : ℕ) (hn : 1≤n) :
    (6 : ℚ)^(n-1)*coeff n A = ((coeff n (R:=ℤ) B : ℤ) : ℚ) := by
  let V : ℚ⟦X⟧ := C (1/6 : ℚ)*rescale 6 A
  let W := PowerSeries.map (Int.castRingHom ℚ) B
  have hV0 : constantCoeff V=0 := by
    rw [← coeff_zero_eq_constantCoeff_apply] at hA0 ⊢
    simp [V,coeff_C_mul,coeff_rescale,hA0]
  have hW0 : constantCoeff W=0 := by
    rw [← coeff_zero_eq_constantCoeff_apply] at hB0 ⊢
    simp [W,hB0]
  have six : (6 : ℚ⟦X⟧)=C (6 : ℚ) := by simp only [map_ofNat]
  have hs : rescale 6 A = 6*V := by
    rw [six]
    simp [V,← mul_assoc,← map_mul]
  have rr := congrArg (rescale (6 : ℚ)) hA
  simp only [map_pow,map_mul,map_add,map_ofNat,rescale_X,← six] at rr
  rw [hs] at rr
  have hh : (36 : ℚ⟦X⟧)*(6*V^3+3*V^2+V-X)=0 := by linear_combination rr
  have nz36 : (36 : ℚ⟦X⟧)≠0 := by
    intro h
    have q := congrArg (constantCoeff (R:=ℚ)) h
    norm_num only [map_ofNat,map_zero] at q
  have hV : 6*V^3+3*V^2+V=X := sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left nz36)
  have hW : 6*W^3+3*W^2+W=X := by
    simpa only [W,map_add,map_pow,map_mul,map_ofNat,PowerSeries.map_X] using congrArg (PowerSeries.map (Int.castRingHom ℚ)) hB
  have hnz : 6*(V^2+V*W+W^2)+3*(V+W)+1 ≠ 0 := by
    intro bad
    have h := congrArg (constantCoeff (R:=ℚ)) bad
    simp [hV0,hW0] at h
  have fac : (V-W)*(6*(V^2+V*W+W^2)+3*(V+W)+1)=0 := by linear_combination hV-hW
  have eq := sub_eq_zero.mp ((mul_eq_zero.mp fac).resolve_right hnz)
  have atn := congrArg (coeff n (R:=ℚ)) eq
  simp only [V,W,coeff_C_mul,coeff_rescale,coeff_map,Int.coe_castRingHom] at atn
  cases n with
  | zero => omega
  | succ n =>
    simp only [Nat.add_sub_cancel,pow_succ] at atn ⊢
    linear_combination atn

theorem odd_inverse (B : ℤ⟦X⟧) (hB : 6*B^3+3*B^2+B=X)
    (n : ℕ) (hn : 1≤n) : Odd (coeff n B) ↔ ∃ k : ℕ, n=2^k := by
  let F := PowerSeries.map (Int.castRingHom (ZMod 2)) B
  have six : (6 : (ZMod 2)⟦X⟧)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (C (R:=ZMod 2)) (show (6 : ZMod 2)=0 by decide)
  have three : (3 : (ZMod 2)⟦X⟧)=1 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (C (R:=ZMod 2)) (show (3 : ZMod 2)=1 by decide)
  have hf : F^2+F=X := by
    simpa only [F,map_add,map_mul,map_pow,map_ofNat,PowerSeries.map_X,six,three,zero_mul,one_mul,zero_add] using congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) hB
  rw [← ZMod.intCast_eq_one_iff_odd]
  exact powers_characterize F hf n hn

end BalaParity

theorem OMA.solution : type_of% @OMA.S_oeis_a144636.main := by
  intro A hA0 hA n hn
  obtain ⟨B,hB0,hB⟩ := BalaParity.integral_inverse
  have eq := BalaParity.scaled_eq A hA0 hA B hB0 hB n hn
  have nf : (n.factorial : ℚ) ≠ 0 := by positivity
  rw [show (6:ℚ)^(n-1)*((n.factorial:ℚ)*PowerSeries.coeff n A)/(n.factorial:ℚ)=
      ((PowerSeries.coeff n (R:=ℤ) B : ℤ) : ℚ) by rw [← eq]; field_simp]
  rw [← BalaParity.odd_inverse B hB n hn]
  constructor
  · rintro ⟨m,hm,he⟩
    have hi : PowerSeries.coeff n B = m := by exact_mod_cast he
    rwa [hi]
  · intro h
    exact ⟨_,h,rfl⟩
