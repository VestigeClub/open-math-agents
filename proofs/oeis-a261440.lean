import OMAStatements.S_oeis_a261440

/-!
Full proof of the path, coefficient and exponential conjectures in OEIS A261440.
The conjectures and implicit series are due to Werner Schulte (2015).
The walk argument uses the classical positive-slot encoding of ordered forests;
its independent prefix-height semantics are proved below. Formal coefficients
use Lagrange-Buermann inversion and the polynomial identity
1+X+X^2=(1+X)^2-X. The adapted inversion code retains its source attribution,
modification notice and Apache 2.0 license below.
-/

noncomputable section


/-! Algebraic ingredients for the implicit series P = 1 + X*P^n + X^2*P^(2*n). -/

open PowerSeries
namespace ForestAlgebra
abbrev Series := PowerSeries ℚ
def Native (n : ℕ) (P : Series) : Prop :=
  P = 1 + X * P ^ n + X ^ 2 * P ^ (2*n)
def Agree (k : ℕ) (P Q : Series) : Prop := ∀ j < k, coeff j P = coeff j Q
lemma agree_refl (k) (P : Series) : Agree k P P := by intro j hj; rfl
lemma agree_mono {k l} {P Q : Series} (h : Agree k P Q) (hl : l ≤ k) : Agree l P Q :=
  fun j hj => h j (lt_of_lt_of_le hj hl)
lemma agree_mul {k} {P Q R S : Series} (h : Agree k P Q) (g : Agree k R S) :
    Agree k (P*R) (Q*S) := by
  intro j hj
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hh : a.1 + a.2 = j := by simpa using ha
  rw [h a.1 (by omega), g a.2 (by omega)]
lemma agree_pow {k} {P Q : Series} (h : Agree k P Q) (e : ℕ) : Agree k (P^e) (Q^e) := by
  induction e with
  | zero => exact agree_refl _ _
  | succ e ih => simpa only [pow_succ] using agree_mul ih h

def step (n : ℕ) (P : Series) : Series := 1 + X * P^n + X^2 * P^(2*n)
lemma step_agree {k n} {P Q : Series} (h : Agree k P Q) :
    Agree (k+1) (step n P) (step n Q) := by
  intro j hj
  cases j with
  | zero => simp [step]
  | succ j =>
    simp only [step, map_add, coeff_one, Nat.succ_ne_zero, if_false, zero_add,
      coeff_succ_X_mul]
    congr 1
    · exact agree_pow h n j (by omega)
    · simp only [pow_two, mul_assoc, coeff_succ_X_mul]
      cases j with
      | zero => simp
      | succ j =>
        simp only [coeff_succ_X_mul]
        exact agree_pow h (2*n) j (by omega)

def approx (n : ℕ) : ℕ → Series
  | 0 => 0
  | k+1 => step n (approx n k)
lemma approx_adjacent (n k : ℕ) : Agree k (approx n (k+1)) (approx n k) := by
  induction k with
  | zero => intro j hj; omega
  | succ k ih => exact step_agree (n := n) ih
lemma approx_stable (n k l : ℕ) (hkl : k ≤ l) :
    Agree k (approx n l) (approx n k) := by
  induction l, hkl using Nat.le_induction with
  | base => exact agree_refl _ _
  | succ l hkl ih =>
    intro j hj
    exact (approx_adjacent n l j (by omega)).trans (ih j hj)
noncomputable def nativeSeries (n : ℕ) : Series := mk fun j => coeff j (approx n (j+1))
lemma native_approx (n k : ℕ) : Agree k (nativeSeries n) (approx n k) := by
  intro j hj
  simp only [nativeSeries, coeff_mk]
  exact (approx_stable n (j+1) k (by omega) j (by omega)).symm
lemma nativeSeries_native (n : ℕ) : Native n (nativeSeries n) := by
  apply PowerSeries.ext
  intro j
  change coeff j (nativeSeries n) = coeff j (step n (nativeSeries n))
  rw [native_approx n (j+1) j (by omega)]
  exact (step_agree (n := n) (native_approx n j) j (by omega)).symm
lemma native_unique (n : ℕ) (P Q : Series) (hp : Native n P) (hq : Native n Q) : P=Q := by
  have h : ∀ k, Agree k P Q := by
    intro k
    induction k with
    | zero => intro j hj; omega
    | succ k ih =>
      change P = step n P at hp
      change Q = step n Q at hq
      rw [hp, hq]
      exact step_agree (n := n) ih
  ext j
  exact h (j+1) j (by omega)
theorem existsUnique_native (n : ℕ) : ∃! P : Series, Native n P := by
  exact ⟨nativeSeries n, nativeSeries_native n, fun P hp => native_unique n P _ hp (nativeSeries_native n)⟩
end ForestAlgebra

open PowerSeries Finset
namespace ForestAlgebra
def signedSum (N k : ℕ) : ℚ := ∑ j ∈ range (k+1),
  (-1:ℚ)^j * (N.choose j : ℚ) * ((2*N-2*j).choose (k-j):ℚ)
lemma coeff_one_add_X_pow (N k : ℕ) :
  coeff k ((1+X:PowerSeries ℚ)^N) = (N.choose k : ℚ) := by
  calc
    _ = coeff k (((1+Polynomial.X)^N : Polynomial ℚ) : PowerSeries ℚ) := by simp
    _ = _ := by rw [Polynomial.coeff_coe]; exact Polynomial.coeff_one_add_X_pow ℚ N k
lemma term_coefficient (N k j : ℕ) (hj : j ≤ N) :
  coeff k ((-X:PowerSeries ℚ)^j * ((1+X)^2)^(N-j) * (N.choose j : PowerSeries ℚ)) =
   if j ≤ k then (-1:ℚ)^j * (N.choose j:ℚ) * ((2*N-2*j).choose (k-j):ℚ) else 0 := by
  rw [neg_pow, ← pow_mul]
  rw [show (-1:PowerSeries ℚ)^j = C ((-1:ℚ)^j) by simp]
  rw [show (N.choose j : PowerSeries ℚ) = C (N.choose j : ℚ) by simp]
  rw [show C ((-1:ℚ)^j) * X^j * (1+X)^(2*(N-j)) * C (N.choose j:ℚ) =
      C ((-1:ℚ)^j) * (((1+X)^(2*(N-j))) * X^j) * C (N.choose j:ℚ) by ring]
  rw [coeff_mul_C, coeff_C_mul, coeff_mul_X_pow']
  rw [coeff_one_add_X_pow]
  have h : 2*(N-j)=2*N-2*j := Nat.mul_sub_left_distrib 2 N j
  rw [h]
  split_ifs <;> ring
lemma coefficient_signedSum (N k : ℕ) :
  coeff k ((1+X+X^2 : PowerSeries ℚ)^N) = signedSum N k := by
  have hb : (1+X+X^2 : PowerSeries ℚ) = -X+(1+X)^2 := by ring
  rw [hb, add_pow, map_sum]
  have ht : ∀ j ∈ range (N+1), coeff k ((-X:PowerSeries ℚ)^j * ((1+X)^2)^(N-j) * (N.choose j : PowerSeries ℚ)) = if j ≤ k then (-1:ℚ)^j * (N.choose j:ℚ) * ((2*N-2*j).choose (k-j):ℚ) else 0 := by
    intro j hj
    exact term_coefficient N k j (by simpa only [mem_range, Nat.lt_succ_iff] using hj)
  rw [sum_congr rfl ht]
  unfold signedSum
  by_cases h : N ≤ k
  · calc
      _ = ∑ j ∈ range (N+1), (-1:ℚ)^j * (N.choose j:ℚ) * ((2*N-2*j).choose (k-j):ℚ) := by
        apply sum_congr rfl
        intro j hj
        rw [if_pos (by simp only [mem_range] at hj; omega)]
      _ = _ := by
        apply sum_subset (range_mono (by omega))
        intro j hj hnot
        simp only [mem_range] at hj hnot
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_mul]
  · have hkn : k ≤ N := by omega
    calc
      _ = ∑ j ∈ range (k+1), if j ≤ k then (-1:ℚ)^j * (N.choose j:ℚ) * ((2*N-2*j).choose (k-j):ℚ) else 0 := by
        symm
        apply sum_subset (range_mono (by omega))
        intro j hj hnot
        rw [if_neg (by simp only [mem_range] at hnot; omega)]
      _ = _ := by
        apply sum_congr rfl
        intro j hj
        rw [if_pos (by simp only [mem_range] at hj; omega)]
end ForestAlgebra

open PowerSeries
namespace ForestAlgebra
lemma subst_one {a : PowerSeries ℚ} (ha : HasSubst a) : (1:PowerSeries ℚ).subst a=1 := by
  rw [← coe_substAlgHom ha, map_one]
lemma log_derivative_mul :
    (1+X:PowerSeries ℚ) * derivative ℚ (log ℚ) = 1 := by
  rw [deriv_log, add_mul, one_mul]
  ext k
  cases k with
  | zero => simp
  | succ k =>
    simp only [map_add, coeff_mk, coeff_succ_X_mul, coeff_one, Nat.succ_ne_zero,
      if_false, pow_succ]
    simp
lemma exp_log_universal : (exp ℚ).subst (log ℚ) = (1+X:PowerSeries ℚ) := by
  let E : PowerSeries ℚ := (exp ℚ).subst (log ℚ)
  have hzero : constantCoeff E = 1 := by
    have hh := constantCoeff_subst_eq_zero (a := log ℚ) (by change constantCoeff (log ℚ)=0; exact constantCoeff_log) (exp ℚ-1) (by change constantCoeff (exp ℚ-1)=0; simp)
    rw [subst_sub (HasSubst.log)] at hh
    have hh' : constantCoeff ((exp ℚ).subst (log ℚ))-1=0 := by simpa [subst_one (HasSubst.log), ← PowerSeries.constantCoeff_eq] using hh
    exact sub_eq_zero.mp hh'
  have he : (1+X:PowerSeries ℚ) * derivative ℚ E = E := by
    dsimp [E]
    rw [derivative_subst (HasSubst.log), derivative_exp]
    calc
      _ = (exp ℚ).subst (log ℚ) * ((1+X)*derivative ℚ (log ℚ)) := by ring
      _ = _ := by rw [log_derivative_mul, mul_one]
  have hr (k : ℕ) :
      (k+1:ℚ)*coeff (k+1) E = (1-(k:ℚ))*coeff k E := by
    have h := congrArg (coeff k) he
    cases k with
    | zero =>
      have h' : coeff 0 (derivative ℚ E) = coeff 0 E := by simpa [add_mul] using h
      simpa only [coeff_derivative, Nat.cast_zero, zero_add, mul_one, one_mul, sub_zero] using h'
    | succ k =>
      simp only [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_derivative] at h
      push_cast at h ⊢
      linarith
  have hz (k : ℕ) (hk : 2 ≤ k) : coeff k E = 0 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have h := hr l
      by_cases hl : l=1
      · subst l; norm_num at h ⊢; linarith
      · rw [ih l (by omega) (by omega)] at h
        have : (l+1:ℚ) ≠ 0 := by positivity
        exact (mul_eq_zero.mp (by simpa using h)).resolve_left this
  ext k
  change coeff k E = _
  cases k with
  | zero => simpa using hzero
  | succ k =>
    cases k with
    | zero => simpa [← coeff_zero_eq_constantCoeff_apply, hzero] using hr 0
    | succ k => simp [hz (k+2) (by omega), coeff_X]
lemma exp_logOf {P : PowerSeries ℚ} (hP : constantCoeff P=1) :
    (exp ℚ).subst (logOf P) = P := by
  have hz : constantCoeff (P-1)=0 := by simp [hP]
  have hs : HasSubst (P-1) := HasSubst.of_constantCoeff_zero' hz
  rw [logOf_eq, ← subst_comp_subst_apply (HasSubst.log) hs, exp_log_universal]
  rw [subst_add hs]
  simp [subst_X hs, subst_one hs]
end ForestAlgebra

open PowerSeries
namespace ForestAlgebra
lemma native_constantCoeff {n : ℕ} {P : PowerSeries ℚ} (hp : Native n P) :
    constantCoeff P = 1 := by
  have h := congrArg constantCoeff hp
  simpa [Native] using h
lemma derivative_logOf_mul {P : PowerSeries ℚ} (hp : constantCoeff P=1) :
    derivative ℚ (logOf P) * P = derivative ℚ P := by
  have hz : constantCoeff (P-1)=0 := by simp [hp]
  have hs : HasSubst (P-1) := HasSubst.of_constantCoeff_zero' hz
  have hh := congrArg (fun f : PowerSeries ℚ => f.subst (P-1)) log_derivative_mul
  rw [subst_mul hs, subst_add hs, subst_X hs, subst_one hs] at hh
  have hi : P * (derivative ℚ (log ℚ)).subst (P-1) = 1 := by
    convert hh using 1 <;> ring
  rw [logOf_eq, derivative_subst hs]
  have hd : derivative ℚ (P-1) = derivative ℚ P := by simp
  rw [hd]
  calc
    _ = (P * (derivative ℚ (log ℚ)).subst (P-1)) * derivative ℚ P := by ring
    _ = _ := by rw [hi, one_mul]
noncomputable def logarithmicSeries (n : ℕ) : PowerSeries ℚ :=
  mk fun k => if k=0 then 0 else ((n*k:ℕ):ℚ)⁻¹ * signedSum (n*k) k
lemma logarithmicSeries_eq {n : ℕ} {P : PowerSeries ℚ} (hp : Native n P)
    (hc : ∀ k : ℕ, 0 < k → coeff k (logOf P) = ((n*k:ℕ):ℚ)⁻¹ * signedSum (n*k) k) :
    logarithmicSeries n = logOf P := by
  ext k
  by_cases hk : k=0
  · subst k
    simp only [logarithmicSeries, coeff_mk, if_true,
      coeff_zero_eq_constantCoeff, constantCoeff_logOf (native_constantCoeff hp)]
  · simp only [logarithmicSeries, coeff_mk, if_neg hk]
    exact (hc k (by omega)).symm
lemma exp_logarithmicSeries {n : ℕ} {P : PowerSeries ℚ} (hp : Native n P)
    (hc : ∀ k : ℕ, 0 < k → coeff k (logOf P) = ((n*k:ℕ):ℚ)⁻¹ * signedSum (n*k) k) :
    (exp ℚ).subst (logarithmicSeries n) = P := by
  rw [logarithmicSeries_eq hp hc]
  exact exp_logOf (native_constantCoeff hp)
end ForestAlgebra


/-
The general lagrange_coefficient proof below is adapted from The Omega
Institute's Apache-2.0 source. The full license is retained here because this
module is intended to be included in a standalone proof submission.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright 2026 The Omega Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

/-
Copyright 2026 The Omega Institute.
Licensed under the Apache License, Version 2.0.
https://www.apache.org/licenses/LICENSE-2.0

Adapted from the general Lagrange coefficient theorem in
https://github.com/the-omega-institute/trureturing/blob/2ff43f6275c756e3dad40449d2ce16c919b67b73/D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lean
The adaptation isolates the general power-series theorem from the
nonnesting application and uses it for the A261440 forest series.
-/
namespace ForestInversion
open PowerSeries
theorem lagrange_coefficient (root factor : PowerSeries ℚ) (zero : constantCoeff root = 0)
    (equation : root = X * subst root factor) :
    ∀ degree power : ℕ, 1 ≤ power → power ≤ degree →
      (degree : ℚ) * coeff degree (root ^ power) =
        (power : ℚ) * coeff (degree - power) (factor ^ degree) := by
  classical
  have substitution : HasSubst root := HasSubst.of_constantCoeff_zero' zero
  have vanishes (degree power : ℕ) (bound : degree < power) :
      coeff degree (root ^ power) = 0 := by
    apply coeff_of_lt_order
    exact (show (degree : ENat) < (power : ENat) by exact_mod_cast bound).trans_le
      (le_order_pow_of_constantCoeff_eq_zero power zero)
  have finiteSubstitution (source : PowerSeries ℚ) (degree : ℕ) :
      coeff degree (subst root source) =
        ∑ power ∈ Finset.range (degree + 1),
          coeff power source * coeff degree (root ^ power) := by
    rw [coeff_subst' substitution]
    simp only [smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro power supported
    apply Finset.mem_range.mpr
    by_contra unbounded
    have vanish := vanishes degree power (by omega)
    exact supported (by simp [vanish])
  have shifted (degree power : ℕ) (bound : power ≤ degree) :
      coeff degree (root ^ power) = coeff (degree - power) (subst root (factor ^ power)) := by
    have powers : root ^ power = X ^ power * subst root (factor ^ power) := by
      rw [subst_pow substitution, ← mul_pow, ← equation]
    rw [powers, coeff_X_pow_mul', if_pos bound]
  have derivativeCoefficients (source : PowerSeries ℚ) (degree : ℕ) :
      coeff degree (X * PowerSeries.derivative (R := ℚ) source) = (degree : ℚ) * coeff degree source := by
    cases degree with
    | zero => simp
    | succ degree =>
      rw [coeff_succ_X_mul, coeff_derivative]
      push_cast
      ring
  intro degree
  induction degree using Nat.strong_induction_on with
  | h degree inductionHypothesis =>
    intro power positive bounded
    by_cases equal : degree = power
    · subst degree
      rw [shifted power power le_rfl]
      simp only [Nat.sub_self]
      rw [finiteSubstitution]
      simp
    have differencePositive : 0 < degree - power := by omega
    have differenceSmaller : degree - power < degree := by omega
    have weighted : (degree - power : ℕ) * coeff degree (root ^ power) =
        coeff (degree - power)
          (X * PowerSeries.derivative (R := ℚ) (factor ^ power) * factor ^ (degree - power)) := by
      rw [shifted degree power bounded, finiteSubstitution, Finset.mul_sum]
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro index member
      have indexBound : index ≤ degree - power := by simpa using Finset.mem_range.mp member
      rw [derivativeCoefficients]
      by_cases indexZero : index = 0
      · subst index
        simp [coeff_one, Nat.ne_of_gt differencePositive]
      have inductionResult := inductionHypothesis (degree - power) differenceSmaller index
        (by omega) indexBound
      linear_combination coeff index (factor ^ power) * inductionResult
    have derivativeIdentity :
        (degree : PowerSeries ℚ) * (X * PowerSeries.derivative (R := ℚ) (factor ^ power) * factor ^ (degree - power)) =
          (power : PowerSeries ℚ) * (X * PowerSeries.derivative (R := ℚ) (factor ^ degree)) := by
      rw [derivative_pow, derivative_pow]
      have exponent : power - 1 + (degree - power) = degree - 1 := by omega
      rw [← exponent, pow_add]
      ring
    have coefficientIdentity := congrArg (coeff (degree - power)) derivativeIdentity
    simp only [← map_natCast C, coeff_C_mul, derivativeCoefficients] at coefficientIdentity
    have nonzero : (degree - power : ℕ) ≠ 0 := by omega
    apply mul_left_cancel₀ (show ((degree - power : ℕ) : ℚ) ≠ 0 by exact_mod_cast nonzero)
    linear_combination (degree : ℚ) * weighted + coefficientIdentity

end ForestInversion

namespace ForestInversion
open PowerSeries

lemma native_power_coefficient (n m k : ℕ) (hm : 0 < m)
    (P : PowerSeries ℚ) (hP : P=1+X*P^n+X^2*P^(2*n)) :
    ((n*k+m:ℕ):ℚ)*coeff k (P^m) =
      (m:ℚ)*coeff k ((1+X+X^2 : PowerSeries ℚ)^(n*k+m)) := by
  by_cases hn : n=0
  · subst n
    have he : P=1+X+X^2 := by simpa using hP
    rw [he]
    simp
  · let E := expand n hn P
    let U : PowerSeries ℚ := X*E
    let F : PowerSeries ℚ := 1+X^n+X^(2*n)
    have hU0 : constantCoeff U=0 := by simp [U]
    have hsub : HasSubst U := HasSubst.of_constantCoeff_zero' hU0
    have hE : E=1+X^n*E^n+X^(2*n)*E^(2*n) := by
      have h := congrArg (expand n hn) hP
      simpa only [map_add,map_mul,map_pow,map_one,expand_X,← pow_mul,
        show n*2=2*n by omega] using h
    have hUF : U=X*subst U F := by
      have hF : subst U F=1+U^n+U^(2*n) := by
        simp only [F,subst_add hsub,subst_pow hsub,subst_X hsub]
        rw [← coe_substAlgHom hsub,map_one]
      rw [hF]
      dsimp [U]
      conv_lhs => rw [hE]
      simp only [mul_pow]
    have hF : F=expand n hn (1+X+X^2 : PowerSeries ℚ) := by
      simp only [F,map_add,map_pow,map_one,expand_X,← pow_mul]
      rw [Nat.mul_comm n 2]
    have h := lagrange_coefficient U F hU0 hUF (n*k+m) m hm (by omega)
    rw [show n*k+m-m=n*k by omega,hF,← map_pow,coeff_expand_mul] at h
    have htransport : coeff (n*k+m) (U^m)=coeff k (P^m) := by
      dsimp [U,E]
      rw [mul_pow,← map_pow,coeff_X_pow_mul,coeff_expand_mul]
    rw [htransport] at h
    exact h

end ForestInversion

namespace ForestInversion
open PowerSeries

lemma composition_coefficient (root factor H : PowerSeries ℚ)
    (hzero : constantCoeff root=0) (heq : root=X*subst root factor)
    (k : ℕ) (hk : 0 < k) :
    (k:ℚ)*coeff k (subst root H) = coeff (k-1) (derivative ℚ H * factor^k) := by
  classical
  have hs : HasSubst root := HasSubst.of_constantCoeff_zero' hzero
  have hf : coeff k (subst root H) =
      ∑ j ∈ Finset.range (k+1), coeff j H * coeff k (root^j) := by
    rw [coeff_subst' hs]
    simp only [smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hn
    have hv : coeff k (root^j)=0 := by
      apply coeff_of_lt_order
      exact (show (k:ENat)<(j:ENat) by exact_mod_cast (show k<j by omega)).trans_le
        (le_order_pow_of_constantCoeff_eq_zero j hzero)
    exact hj (by simp [hv])
  rw [hf, Finset.sum_range_succ']
  simp only [Nat.zero_add, pow_zero, coeff_one, show k≠0 by omega, if_false,
    mul_zero, add_zero]
  rw [Finset.mul_sum, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hlen : k-1+1=k := by omega
  rw [show (k-1).succ=k by omega]
  apply Finset.sum_congr rfl
  intro j hj
  have hbound : j+1≤k := by have := Finset.mem_range.mp hj; omega
  have h := lagrange_coefficient root factor hzero heq k (j+1) (by omega) hbound
  rw [coeff_derivative]
  have he : k-1-j=k-(j+1) := by omega
  rw [he]
  push_cast at h ⊢
  linear_combination coeff (j+1) H * h

end ForestInversion

namespace ForestInversion
open PowerSeries

lemma logOf_subst (Q T : PowerSeries ℚ) (hQ : constantCoeff Q=1)
    (hT : constantCoeff T=0) : logOf (subst T Q)=subst T (logOf Q) := by
  have hs : HasSubst T := HasSubst.of_constantCoeff_zero' hT
  have hq : HasSubst (Q-1) := HasSubst.of_constantCoeff_zero' (by simpa [hQ])
  unfold logOf
  rw [subst_comp_subst_apply hq hs, subst_sub hs]
  have ho : subst T (1:PowerSeries ℚ)=1 := by rw [← coe_substAlgHom hs,map_one]
  rw [ho]

lemma log_coefficient (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (Q T : PowerSeries ℚ) (hQ : constantCoeff Q=1) (hT : constantCoeff T=0)
    (hroot : T=X*subst T (Q^n))
    (hD : derivative ℚ (logOf Q)*Q=derivative ℚ Q) :
    ((n*k:ℕ):ℚ)*coeff k (logOf (subst T Q))=coeff k (Q^(n*k)) := by
  have hc := composition_coefficient T (Q^n) (logOf Q) hT hroot k hk
  rw [← logOf_subst Q T hQ hT, ← pow_mul] at hc
  have hnk : 0<n*k := Nat.mul_pos hn hk
  have hp : n*k=(n*k-1)+1 := by omega
  have hd : (n*k : PowerSeries ℚ) * (derivative ℚ (logOf Q)*Q^(n*k)) =
      derivative ℚ (Q^(n*k)) := by
    rw [derivative_pow]
    conv_lhs => arg 2; arg 2; rw [hp,pow_succ']
    rw [← mul_assoc (derivative ℚ (logOf Q)) Q, hD]
    push_cast
    ring
  have hdcoeff := congrArg (coeff (k-1)) hd
  simp only [← map_natCast C, mul_assoc, coeff_C_mul, coeff_derivative] at hdcoeff
  have hki : ((k-1:ℕ):ℚ)+1=(k:ℚ) := by exact_mod_cast (show k-1+1=k by omega)
  rw [hki, show k-1+1=k by omega] at hdcoeff
  apply mul_left_cancel₀ (show (k:ℚ)≠0 by exact_mod_cast (Nat.ne_of_gt hk))
  push_cast at hc hdcoeff ⊢
  linear_combination (n:ℚ)*(k:ℚ)*hc + hdcoeff

end ForestInversion

namespace ForestInversion
open PowerSeries

lemma native_log_coefficient (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (P : PowerSeries ℚ) (hP : P=1+X*P^n+X^2*P^(2*n)) :
    ((n*k:ℕ):ℚ)*coeff k (logOf P) = coeff k ((1+X+X^2 : PowerSeries ℚ)^(n*k)) := by
  let Q : PowerSeries ℚ := 1+X+X^2
  let T : PowerSeries ℚ := X*P^n
  have hQ : constantCoeff Q=1 := by simp [Q]
  have hT : constantCoeff T=0 := by simp [T]
  have hs : HasSubst T := HasSubst.of_constantCoeff_zero' hT
  have hp : P=1+T+T^2 := by
    dsimp [T]
    rw [mul_pow,← pow_mul]
    simpa only [Nat.mul_comm n 2] using hP
  have hsubst : subst T Q=P := by
    dsimp [Q]
    rw [subst_add hs,subst_add hs,subst_pow hs,subst_X hs]
    have ho : subst T (1:PowerSeries ℚ)=1 := by rw [← coe_substAlgHom hs,map_one]
    rw [ho]
    exact hp.symm
  have hroot : T=X*subst T (Q^n) := by
    rw [subst_pow hs,hsubst]
  have hd := ForestAlgebra.derivative_logOf_mul hQ
  have h := log_coefficient n k hn hk Q T hQ hT hroot hd
  simpa only [hsubst,Q] using h

end ForestInversion

namespace MotzkinPath
open PowerSeries

def Native (n : ℕ) (P : PowerSeries ℚ) : Prop :=
  P = 1 + X * P ^ n + X ^ 2 * P ^ (2*n)

def prepend (a : ℕ) (s : Finset (List ℕ)) : Finset (List ℕ) :=
  s.image (List.cons a)

@[simp] theorem card_prefix (a : ℕ) (s : Finset (List ℕ)) :
    (prepend a s).card = s.card := by
  apply Finset.card_image_of_injective
  exact fun _ _ h => (List.cons.inj h).2

lemma prefix_disjoint {a b : ℕ} (h : a ≠ b) (s t : Finset (List ℕ)) :
    Disjoint (prepend a s) (prepend b t) := by
  apply Finset.disjoint_left.mpr
  intro l hl hr
  simp only [prepend, Finset.mem_image] at hl hr
  obtain ⟨u, _, rfl⟩ := hl
  obtain ⟨v, _, he⟩ := hr
  exact h (List.cons.inj he).1.symm

lemma card_three (s t u : Finset (List ℕ)) :
    ((prepend 0 s ∪ prepend 1 t) ∪ prepend 2 u).card = s.card+t.card+u.card := by
  have h01 := prefix_disjoint (show (0:ℕ) ≠ 1 by decide) s t
  have h02 := prefix_disjoint (show (0:ℕ) ≠ 2 by decide) s u
  have h12 := prefix_disjoint (show (1:ℕ) ≠ 2 by decide) t u
  have hU : Disjoint (prepend 0 s ∪ prepend 1 t) (prepend 2 u) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    rcases Finset.mem_union.mp ha with ha|ha
    · exact Finset.disjoint_left.mp h02 ha hb
    · exact Finset.disjoint_left.mp h12 ha hb
  rw [Finset.card_union_of_disjoint hU, Finset.card_union_of_disjoint h01]
  simp
/-- Direct enumeration by the first step: label r changes height by n*r-1. -/
def paths (n : ℕ) : ℕ → ℕ → Finset (List ℕ)
  | 0, h => if h=0 then {[]} else ∅
  | l+1, h =>
      (prepend 0 (if h=0 then ∅ else paths n l (h-1)) ∪
       prepend 1 (if h+n=0 then ∅ else paths n l (h+n-1))) ∪
       prepend 2 (if h+2*n=0 then ∅ else paths n l (h+2*n-1))

/-- Positive-slot words stop on their first visit to zero. -/
def forests (n : ℕ) : ℕ → ℕ → Finset (List ℕ)
  | 0, m => if m=0 then {[]} else ∅
  | _l+1, 0 => ∅
  | l+1, m+1 =>
      (prepend 0 (forests n l m) ∪ prepend 1 (forests n l (m+n))) ∪
       prepend 2 (forests n l (m+2*n))

@[simp] lemma forests_zero_slots (n l : ℕ) :
    (forests n l 0).card = if l=0 then 1 else 0 := by
  cases l <;> simp [forests]

lemma forests_succ (n l m : ℕ) :
    (forests n (l+1) (m+1)).card =
      (forests n l m).card + (forests n l (m+n)).card +
        (forests n l (m+2*n)).card := by
  exact card_three _ _ _

lemma paths_to_forests (n l h : ℕ) (hn : 0 < n) :
    (paths n l h).card = (forests n (l+1) (h+1)).card := by
  induction l generalizing h with
  | zero =>
      rw [forests_succ]
      simp only [paths, forests]
      split_ifs <;> simp_all
  | succ l ih =>
      rw [show (paths n (l+1) h).card =
          (if h=0 then ∅ else paths n l (h-1)).card +
          (if h+n=0 then ∅ else paths n l (h+n-1)).card +
          (if h+2*n=0 then ∅ else paths n l (h+2*n-1)).card from card_three _ _ _]
      rw [forests_succ]
      have aux (m : ℕ) :
          (if m=0 then ∅ else paths n l (m-1)).card =
            (forests n (l+1) m).card := by
        by_cases hm : m=0
        · simp [hm]
        · simp only [if_neg hm, ih]
          congr 2
          omega
      rw [aux, aux, aux]

lemma native_constant {n : ℕ} {P : PowerSeries ℚ} (hp : Native n P) :
    constantCoeff P = 1 := by
  unfold Native at hp
  apply_fun constantCoeff at hp
  simpa [Native] using hp

lemma lifted_native {n : ℕ} {P : PowerSeries ℚ} (hn : 0 < n) (hp : Native n P) :
    let U := X * expand n (by omega) P
    U = X * (1 + U^n + U^(2*n)) := by
  dsimp
  unfold Native at hp
  conv_lhs => rw [hp]
  simp only [map_add, map_one, map_mul, map_pow, expand_X]
  ring

lemma forests_coeff (n : ℕ) (U : PowerSeries ℚ)
    (hu : U = X * (1 + U^n + U^(2*n))) (l m : ℕ) :
    ((forests n l m).card : ℚ) = coeff l (U^m) := by
  have h0 : constantCoeff U = 0 := by
    rw [hu]
    simp
  induction l generalizing m with
  | zero =>
      cases m with
      | zero => simp [forests]
      | succ m => simp [forests, coeff_zero_eq_constantCoeff_apply, h0]
  | succ l ih =>
      cases m with
      | zero => simp [forests]
      | succ m =>
          rw [forests_succ, Nat.cast_add, Nat.cast_add, ih, ih, ih]
          have he : U^(m+1) = X*(U^m+U^(m+n)+U^(m+2*n)) := by
            calc
              U^(m+1) = U^m*U := pow_succ _ _
              _ = U^m*(X*(1+U^n+U^(2*n))) := by rw [←hu]
              _ = _ := by simp only [pow_add]; ring
          rw [he, coeff_succ_X_mul, map_add, map_add]

lemma lifted_coeff {n : ℕ} (hn : 0 < n) (P : PowerSeries ℚ) (m k : ℕ) :
    coeff (n*k+m) ((X * expand n (by omega) P)^m) = coeff k (P^m) := by
  rw [mul_pow, ← map_pow, coeff_X_pow_mul,
    coeff_expand_mul]

/-- Every coefficient counts all nonnegative paths with the prescribed endpoint. -/
theorem path_coeff {n : ℕ} {P : PowerSeries ℚ} (hn : 0 < n)
    (hp : Native n P) (m k : ℕ) (hm : 0 < m) :
    ((paths n (n*k+m-1) (m-1)).card : ℚ) = coeff k (P^m) := by
  rw [paths_to_forests _ _ _ hn,
    show n*k+m-1+1=n*k+m by omega, show m-1+1=m by omega]
  rw [forests_coeff n (X * expand n (by omega) P) (lifted_native hn hp), lifted_coeff hn]


/-- Local geometric semantics, independent of the generating series. -/
def IsPath (n : ℕ) : ℕ → List ℕ → Prop
  | h, [] => h=0
  | h, r::w => r ≤ 2 ∧ 0 < h+n*r ∧ IsPath n (h+n*r-1) w

@[simp] lemma mem_prepend_nil (a : ℕ) (s : Finset (List ℕ)) :
    [] ∉ prepend a s := by simp [prepend]

@[simp] lemma mem_prepend_cons (a b : ℕ) (w : List ℕ) (s : Finset (List ℕ)) :
    b::w ∈ prepend a s ↔ b=a ∧ w∈s := by
  simp [prepend, eq_comm, and_comm]

lemma paths_semantics (n l h : ℕ) (w : List ℕ) :
    w ∈ paths n l h ↔ w.length=l ∧ IsPath n h w := by
  induction l generalizing h w with
  | zero =>
      cases w <;> by_cases hh : h=0 <;> simp [paths, IsPath, hh]
  | succ l ih =>
      cases w with
      | nil => simp [paths, IsPath]
      | cons r w =>
          by_cases h0 : r=0
          · subst r
            by_cases hz : h=0
            · simp [paths, IsPath, hz]
            · simp [paths, IsPath, hz, ih, show 0 < h by omega]
          by_cases h1 : r=1
          · subst r
            by_cases hz : h+n=0
            · have hh : h=0 := by omega
              have hn : n=0 := by omega
              simp [paths, IsPath, hh, hn]
            · have hh : ¬(h=0 ∧ n=0) := by omega
              simp [paths, IsPath, hh, ih, show 0 < h+n by omega]
          by_cases h2 : r=2
          · subst r
            by_cases hz : h+2*n=0
            · have hh : h=0 := by omega
              have hn : n=0 := by omega
              simp [paths, IsPath, hh, hn]
            · have hh : ¬(h=0 ∧ n=0) := by omega
              have hp : 0 < h ∨ 0 < n := by omega
              simp [paths, IsPath, Nat.mul_comm, hh, ih, hp]
          · simp [paths, IsPath, h0,h1,h2, show ¬ r ≤ 2 by omega]


/-- Cardinality of the finite set of actual walks, specified geometrically. -/
noncomputable def pathCount (n l h : ℕ) : ℕ :=
  Nat.card {w : List ℕ // w.length=l ∧ IsPath n h w}

lemma pathCount_eq (n l h : ℕ) : pathCount n l h = (paths n l h).card := by
  let : Fintype {w : List ℕ // w.length=l ∧ IsPath n h w} := Fintype.ofFinset (paths n l h) (fun w => paths_semantics n l h w)
  unfold pathCount
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_ofFinset _ _

theorem path_count {n : ℕ} {P : PowerSeries ℚ} (hn : 0 < n)
    (hp : Native n P) (m k : ℕ) (hm : 0 < m) :
    (pathCount n (n*k+m-1) (m-1) : ℚ) = coeff k (P^m) := by
  rw [pathCount_eq]
  exact path_coeff hn hp m k hm


lemma IsPath.balance {n h : ℕ} {w : List ℕ} (hp : IsPath n h w) :
    h+n*w.sum=w.length := by
  induction w generalizing h with
  | nil => simpa [IsPath] using hp
  | cons r w ih =>
      obtain ⟨_, hpos, ht⟩ := hp
      have he := ih ht
      simp only [List.sum_cons, List.length_cons, mul_add]
      omega

lemma IsPath.prefix_bound {n h : ℕ} {w : List ℕ} (hp : IsPath n h w)
    (i : ℕ) : i ≤ w.length → i ≤ h+n*(w.take i).sum := by
  induction w generalizing h i with
  | nil => intro hi; simp at hi; subst i; simp
  | cons r w ih =>
      obtain ⟨_, hpos, ht⟩ := hp
      cases i with
      | zero => simp
      | succ i =>
          intro hi
          have he := ih ht i (by simpa using hi)
          simp only [List.take_succ_cons, List.sum_cons, mul_add]
          omega

lemma IsPath.labels {n h : ℕ} {w : List ℕ} (hp : IsPath n h w) :
    ∀ r∈w, r ≤ 2 := by
  induction w generalizing h with
  | nil => simp
  | cons r w ih =>
      obtain ⟨hr, _, ht⟩ := hp
      simpa using And.intro hr (ih ht)

/-- Equivalence with the endpoint and every-prefix height conditions. -/
theorem path_prefix_iff (n h : ℕ) (w : List ℕ) :
    IsPath n h w ↔
      (∀ r∈w, r ≤ 2) ∧ h+n*w.sum=w.length ∧
      (∀ i, i ≤ w.length → i ≤ h+n*(w.take i).sum) := by
  constructor
  · intro hp
    exact ⟨hp.labels, hp.balance, hp.prefix_bound⟩
  · induction w generalizing h with
    | nil => simp [IsPath]
    | cons r w ih =>
        rintro ⟨hr, hb, hf⟩
        have hpos := hf 1 (by simp)
        simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil,
          add_zero] at hpos
        refine ⟨hr r (by simp), by omega, ih (h+n*r-1) ?_⟩
        refine ⟨fun s hs => hr s (by simp [hs]), ?_, ?_⟩
        · simp only [List.sum_cons, List.length_cons, mul_add] at hb
          omega
        · intro i hi
          have hh := hf (i+1) (by simpa using hi)
          simp only [List.take_succ_cons, List.sum_cons, mul_add] at hh
          omega

end MotzkinPath

open OMA.S_oeis_a261440

lemma motzkin_semantics_bridge (n h : ℕ) (w : List ℕ) :
    MotzkinPath.IsPath n h w ↔ IsPath n h w := by
  induction w generalizing h with
  | nil => rfl
  | cons r w ih => simp only [MotzkinPath.IsPath, IsPath, ih]

lemma motzkin_count_bridge (n l h : ℕ) :
    MotzkinPath.pathCount n l h = pathCount n l h := by
  apply Nat.card_congr
    { toFun := fun w => ⟨w.1, w.2.1, (motzkin_semantics_bridge n h w.1).mp w.2.2⟩
      invFun := fun w => ⟨w.1, w.2.1, (motzkin_semantics_bridge n h w.1).mpr w.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem OMA.solution : type_of% @OMA.S_oeis_a261440.main := by
  constructor
  · intro n
    simpa only [ForestAlgebra.Native, Native] using ForestAlgebra.existsUnique_native n
  · intro n P hp
    have hpF : ForestAlgebra.Native n P := hp
    have hpM : MotzkinPath.Native n P := hp
    have hpower (m k : ℕ) (hm : 0 < m) : coeff k (P^m) =
        (m:ℚ) / ((n*k+m:ℕ):ℚ) * signedSum (n*k+m) k := by
      have he := ForestInversion.native_power_coefficient n m k hm P hp
      rw [ForestAlgebra.coefficient_signedSum] at he
      have hN : ((n*k+m:ℕ):ℚ) ≠ 0 := by
        exact_mod_cast (show n*k+m ≠ 0 by omega)
      calc
        coeff k (P^m) = ((m:ℚ)*signedSum (n*k+m) k) / ((n*k+m:ℕ):ℚ) :=
          (eq_div_iff hN).mpr (by
            simpa only [ForestAlgebra.signedSum, signedSum, mul_comm] using he)
        _ = _ := by ring
    constructor
    · intro k
      simpa only [pow_one, Nat.cast_one, one_div] using hpower 1 k (by omega)
    · intro hn
      have hlog (k : ℕ) (hk : 0 < k) : coeff k (logOf P) =
          (((n*k:ℕ):ℚ))⁻¹ * signedSum (n*k) k := by
        have he := ForestInversion.native_log_coefficient n k hn hk P hp
        rw [ForestAlgebra.coefficient_signedSum] at he
        have hN : ((n*k:ℕ):ℚ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hn hk))
        calc
          coeff k (logOf P) = signedSum (n*k) k / ((n*k:ℕ):ℚ) :=
            (eq_div_iff hN).mpr (by
              simpa only [ForestAlgebra.signedSum, signedSum, mul_comm] using he)
          _ = _ := by ring
      refine ⟨hpower, ?_, ?_, hlog, ?_⟩
      · intro k
        rw [←motzkin_count_bridge]
        simpa only [Nat.mul_one, Nat.add_sub_cancel, Nat.sub_self, pow_one] using
          MotzkinPath.path_count hn hpM 1 k (by omega)
      · intro m k hm
        rw [←motzkin_count_bridge]
        exact MotzkinPath.path_count hn hpM m k hm
      · exact ForestAlgebra.exp_logarithmicSeries hpF hlog
