import Mathlib

/-!
# Morton Brown's monotone union theorem

An increasing countable open cover by Euclidean d-cells is itself a Euclidean
d-cell. The geometric extension follows Brown's compact-engulfing argument as
presented in Steve Ferry's *Geometric topology*, Lemma 2.5 and Theorem 2.6.
A compactly supported radial homeomorphism compresses the previously fixed
ball. A second radial homeomorphism in a common chart enlarges its collar to
cover the next compact set. Conjugation preserves the fixed ball. Compatible
open embeddings then glue to a homeomorphism onto the whole space.

Morton Brown, Proc. Amer. Math. Soc. 12 (1961), 812–814.
https://doi.org/10.1090/S0002-9939-1961-0126835-6
https://www.math.rutgers.edu/~sferry/ps/geotop.pdf#page=4
-/
-- Credit: @VestigeClub

open Set Topology

namespace BrownOpenCells.Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def transform (h : ℝ ≃o ℝ) (a : ℝ) (x : E) : E :=
  (h (max a ‖x‖) / max a ‖x‖) • x

theorem symm_fixed (h : ℝ ≃o ℝ) {a : ℝ} (fixed : ∀ t, t≤a → h t=t)
    (t : ℝ) (ht : t≤a) : h.symm t=t := by
  apply h.injective
  rw [h.apply_symm_apply,fixed t ht]

theorem fixed_ball (h : ℝ ≃o ℝ) {a : ℝ} (positive : 0<a)
    (fixed : ∀ t, t≤a → h t=t) (x : E) (inside : ‖x‖≤a) : transform h a x=x := by
  simp only [transform,max_eq_left inside,fixed a le_rfl,div_self positive.ne',one_smul]

theorem norm_transform (h : ℝ ≃o ℝ) {a : ℝ} (positive : 0<a)
    (fixed : ∀ t, t≤a → h t=t) (x : E) : ‖transform h a x‖=h ‖x‖ := by
  rcases le_or_gt ‖x‖ a with small | big
  · rw [fixed_ball h positive fixed x small,fixed _ small]
  have hnorm : 0<h ‖x‖ := lt_of_lt_of_le positive (by simpa [fixed a le_rfl] using h.monotone big.le)
  have pn : 0<‖x‖ := positive.trans big
  rw [transform,max_eq_right big.le,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hnorm pn)]
  exact div_mul_cancel₀ _ pn.ne'

theorem continuous_transform (h : ℝ ≃o ℝ) {a : ℝ} (positive : 0<a) :
    Continuous (transform (E:=E) h a) := by
  have denom : Continuous (fun x : E => max a ‖x‖) := continuous_const.max continuous_norm
  exact ((h.continuous.comp denom).div denom
    (fun x => (positive.trans_le (le_max_left a ‖x‖)).ne')).smul continuous_id

theorem inverse (h : ℝ ≃o ℝ) {a : ℝ} (positive : 0<a)
    (fixed : ∀ t, t≤a → h t=t) (x : E) :
    transform h.symm a (transform h a x)=x := by
  rcases le_or_gt ‖x‖ a with small | big
  · rw [fixed_ball h positive fixed x small,fixed_ball h.symm positive (symm_fixed h fixed) x small]
  have ho : a<h ‖x‖ := by simpa only [fixed a le_rfl] using h.strictMono big
  have pn := (positive.trans big).ne'
  have ph := (positive.trans ho).ne'
  have cancel : ‖x‖/h ‖x‖*(h ‖x‖/‖x‖)=1 := by field_simp
  rw [transform,norm_transform h positive fixed,max_eq_right ho.le,h.symm_apply_apply,
    transform,max_eq_right big.le,smul_smul,cancel,one_smul]

noncomputable def homeo (h : ℝ ≃o ℝ) {a : ℝ} (positive : 0<a)
    (fixed : ∀ t, t≤a → h t=t) : E ≃ₜ E where
  toFun := transform h a
  invFun := transform h.symm a
  left_inv := inverse h positive fixed
  right_inv := inverse h.symm positive (symm_fixed h fixed)
  continuous_toFun := continuous_transform h positive
  continuous_invFun := continuous_transform h.symm positive

end BrownOpenCells.Radial

namespace BrownOpenCells.Radii

private noncomputable def bend (a k t : ℝ) :=
  if t ≤ a then t else a+k*(t-a)

private theorem left {a k t : ℝ} (le : t ≤ a) : bend a k t=t := if_pos le

private theorem right {a k t : ℝ} (le : a ≤ t) : bend a k t=a+k*(t-a) := by
  rcases le.eq_or_lt with rfl | lt
  · simp [bend]
  · exact if_neg lt.not_ge

private theorem monotone {a k : ℝ} (pos : 0 < k) : StrictMono (bend a k) := by
  intro x y xy
  by_cases hy : y ≤ a
  · simpa only [left (xy.le.trans hy),left hy] using xy
  by_cases hx : x ≤ a
  · rw [left hx,right (le_of_not_ge hy)]
    have := mul_pos pos (sub_pos.mpr (lt_of_not_ge hy))
    linarith
  · rw [right (le_of_not_ge hx),right (le_of_not_ge hy)]
    linarith [mul_lt_mul_of_pos_left (sub_lt_sub_right xy a) pos]

private theorem undo {a k : ℝ} (pos : 0 < k) (t : ℝ) :
    bend a k⁻¹ (bend a k t)=t := by
  rcases le_or_gt t a with small | big
  · rw [left small,left small]
  have hi : a ≤ a+k*(t-a) := by nlinarith [mul_pos pos (sub_pos.mpr big)]
  rw [right big.le,right hi]
  field_simp
  ring

private noncomputable def hinge (a k : ℝ) (pos : 0 < k) : ℝ ≃o ℝ where
  toFun := bend a k
  invFun := bend a k⁻¹
  left_inv := undo pos
  right_inv := by intro t; simpa only [inv_inv] using undo (a:=a) (inv_pos.mpr pos) t
  map_rel_iff' := (monotone pos).le_iff_le

theorem move {a r s b : ℝ} (ar : a < r) (rb : r < b) (aslt : a < s) (sb : s < b) :
    ∃ h : ℝ ≃o ℝ, (∀ t, t ≤ a → h t=t) ∧ h r=s ∧ ∀ t, b ≤ t → h t=t := by
  let k := (s-a)/(r-a)
  let m := (b-s)/(b-r)
  have kp : 0 < k := div_pos (sub_pos.mpr aslt) (sub_pos.mpr ar)
  have mp : 0 < m := div_pos (sub_pos.mpr sb) (sub_pos.mpr rb)
  have kr : k*(r-a)=s-a := div_mul_cancel₀ _ (sub_ne_zero.mpr ar.ne')
  have mr : m*(b-r)=b-s := div_mul_cancel₀ _ (sub_ne_zero.mpr rb.ne')
  let h := ((hinge a k kp).trans (hinge s (m/k) (div_pos mp kp))).trans
    (hinge b m⁻¹ (inv_pos.mpr mp))
  have eval (t : ℝ) : h t=bend b m⁻¹ (bend s (m/k) (bend a k t)) := rfl
  have middle (t : ℝ) (ht : r ≤ t) : bend s (m/k) (bend a k t)=s+m*(t-r) := by
    have one : bend a k t=s+k*(t-r) := by rw [right (ar.le.trans ht)]; nlinarith [kr]
    have hs : s ≤ s+k*(t-r) := by nlinarith [mul_nonneg kp.le (sub_nonneg.mpr ht)]
    rw [one,right hs]
    field_simp
    ring
  refine ⟨h,?_,?_,?_⟩
  · intro t ht
    rw [eval,left ht,left (ht.trans aslt.le),left (ht.trans (ar.trans rb).le)]
  · rw [eval,middle _ le_rfl,sub_self,mul_zero,add_zero,left sb.le]
  · intro t ht
    have hb : b ≤ s+m*(t-r) := by nlinarith [mul_nonneg mp.le (sub_nonneg.mpr ht),mr]
    rw [eval,middle t (rb.le.trans ht),right hb]
    field_simp
    nlinarith [mr]

end BrownOpenCells.Radii

open Set Topology

namespace BrownOpenCells.ChartTransport

private noncomputable def map {E X : Type*} (e : E → X) (h : E → E) (y : X) : X := by
  classical
  exact if hy : y∈range e then e (h hy.choose) else y

private theorem in_chart {E X : Type*} {e : E → X} (inj : Function.Injective e)
    (h : E → E) (x : E) : map e h (e x)=e (h x) := by
  classical
  have mem : e x∈range e := ⟨x,rfl⟩
  unfold map
  rw [dif_pos mem,inj mem.choose_spec]

private theorem out_chart {E X : Type*} {e : E → X} (h : E → E) {y : X} (hy : y∉range e) :
    map e h y=y := by classical exact dif_neg hy

private theorem outside {E X : Type*} {e : E → X} (inj : Function.Injective e)
    {h : E → E} {C : Set E} (fixed : ∀ x, x∉C → h x=x)
    {y : X} (out : y∉e '' C) : map e h y=y := by
  by_cases yes : y∈range e
  · obtain ⟨x,rfl⟩ := yes
    rw [in_chart inj,fixed x (fun hx => out ⟨x,hx,rfl⟩)]
  · exact out_chart h yes

private theorem continuous_map {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space X] {e : E → X} (emb : IsOpenEmbedding e) {h : E → E}
    (cont : Continuous h) {C : Set E} (compactC : IsCompact C)
    (fixed : ∀ x, x∉C → h x=x) : Continuous (map e h) := by
  apply continuous_def.mpr
  intro V op
  have pre : map e h ⁻¹' V=(e '' ((e ∘ h) ⁻¹' V)) ∪ (V \ (e '' C)) := by
    ext y
    constructor
    · intro hy
      by_cases mem : y∈range e
      · obtain ⟨x,rfl⟩ := mem
        exact Or.inl ⟨x,by simpa only [mem_preimage,in_chart emb.injective,Function.comp_apply] using hy,rfl⟩
      · have out : y∉e '' C := fun hy => mem (image_subset_range _ _ hy)
        exact Or.inr ⟨by simpa only [mem_preimage,outside emb.injective fixed out] using hy,out⟩
    · rintro (⟨x,hx,rfl⟩ | ⟨hy,out⟩)
      · simpa only [mem_preimage,in_chart emb.injective,Function.comp_apply] using hx
      · simpa only [mem_preimage,outside emb.injective fixed out] using hy
  rw [pre]
  exact (emb.isOpenMap _ (op.preimage (emb.continuous.comp cont))).union
    (op.sdiff (compactC.image emb.continuous).isClosed)

private theorem cancel {E X : Type*} {e : E → X} (inj : Function.Injective e) {h k : E → E}
    (inv : Function.LeftInverse k h) (y : X) : map e k (map e h y)=y := by
  by_cases hy : y∈range e
  · obtain ⟨x,rfl⟩ := hy
    rw [in_chart inj,in_chart inj,inv]
  · rw [out_chart h hy,out_chart k hy]

theorem extend {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {e : E → X} (emb : IsOpenEmbedding e) (h : E ≃ₜ E)
    {C : Set E} (compactC : IsCompact C) (fixed : ∀ x, x∉C → h x=x) :
    ∃ g : X ≃ₜ X, (∀ x, g (e x)=e (h x)) ∧ ∀ y, y∉e '' C → g y=y := by
  have fixInv (x : E) (hx : x∉C) : h.symm x=x := by
    apply h.injective
    rw [h.apply_symm_apply,fixed x hx]
  let g : X ≃ₜ X := {
    toFun := map e h
    invFun := map e h.symm
    left_inv := cancel emb.injective h.left_inv
    right_inv := cancel emb.injective h.right_inv
    continuous_toFun := continuous_map emb h.continuous compactC fixed
    continuous_invFun := continuous_map emb h.symm.continuous compactC fixInv }
  exact ⟨g,in_chart emb.injective h,fun _ hy => outside emb.injective fixed hy⟩

end BrownOpenCells.ChartTransport

open Set Topology Metric

namespace BrownOpenCells

/-- Move one coordinate ball to another while fixing an inner ball and the
exterior of an outer closed ball. -/
theorem stretch_chart {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
    {e : EuclideanSpace ℝ (Fin d) → X} (emb : IsOpenEmbedding e)
    {a r s b : ℝ} (positive : 0 < a) (ar : a < r) (rb : r < b)
    (aslt : a < s) (sb : s < b) :
    ∃ g : X ≃ₜ X, EqOn g id (e '' closedBall 0 a) ∧
      g '' (e '' ball 0 r)=e '' ball 0 s ∧
      g '' (e '' ball 0 b)=e '' ball 0 b ∧
      ∀ y, y∉e '' closedBall 0 b → g y=y := by
  let E := EuclideanSpace ℝ (Fin d)
  obtain ⟨h,low,moved,above⟩ := Radii.move ar rb aslt sb
  let R : E ≃ₜ E := Radial.homeo h positive low
  have norms (x : E) : ‖R x‖=h ‖x‖ := Radial.norm_transform h positive low x
  have support (x : E) (hx : x∉closedBall 0 b) : R x=x := by
    have hb : b < ‖x‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hx
    have ax := ((ar.trans rb).trans hb).le
    have normpos : 0 < ‖x‖ := positive.trans_le ax
    change (h (max a ‖x‖)/max a ‖x‖) • x=x
    rw [max_eq_right ax,above _ hb.le,div_self normpos.ne',one_smul]
  obtain ⟨g,chart,outside⟩ := ChartTransport.extend emb R (isCompact_closedBall (0 : E) b) support
  have moveBall (t : ℝ) : g '' (e '' ball 0 t)=e '' ball 0 (h t) := by
    ext y
    constructor
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      refine ⟨R x,?_,(chart x).symm⟩
      have lt : ‖x‖ < t := by simpa only [mem_ball,dist_zero_right] using hx
      simpa only [mem_ball,dist_zero_right,norms] using h.strictMono lt
    · rintro ⟨x,hx,rfl⟩
      refine ⟨_,⟨R.symm x,?_,rfl⟩,?_⟩
      · have lt : ‖x‖ < h t := by simpa only [mem_ball,dist_zero_right] using hx
        have bound : h ‖R.symm x‖ < h t := by simpa only [← norms,R.apply_symm_apply] using lt
        exact mem_ball.mpr (by simpa only [dist_zero_right] using h.strictMono.lt_iff_lt.mp bound)
      · rw [chart,R.apply_symm_apply]
  refine ⟨g,?_,by simpa only [moved] using moveBall r,by simpa only [above b le_rfl] using moveBall b,outside⟩
  rintro _ ⟨x,hx,rfl⟩
  have small : ‖x‖ ≤ a := by simpa only [mem_closedBall,dist_zero_right] using hx
  rw [chart]
  change e (Radial.transform h a x)=e x
  rw [Radial.fixed_ball h positive low x small]

end BrownOpenCells

open Set Topology Metric

namespace BrownOpenCells

private abbrev Euclid (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

private theorem neighborhood_ball {X : Type*} [TopologicalSpace X]
    (e : (Euclid d) → X) (cont : Continuous e) {U : Set X} (op : IsOpen U) (inside : e 0∈U) :
    ∃ r : ℝ, 0 < r ∧ e '' ball 0 r ⊆ U := by
  obtain ⟨r,pos,covers⟩ := Metric.isOpen_iff.mp (op.preimage cont) 0 inside
  exact ⟨r,pos,image_subset_iff.mpr covers⟩

private theorem center_chart {X : Type*} [TopologicalSpace X] (D : Set X) {p : X} (hp : p∈D)
    (chart : ∃ u : (Euclid d) → X, IsOpenEmbedding u ∧ D ⊆ range u) :
    ∃ g : (Euclid d) → X, IsOpenEmbedding g ∧ g 0=p ∧ D ⊆ range g := by
  obtain ⟨u,eu,inside⟩ := chart
  obtain ⟨c,hc⟩ := inside hp
  let move : (Euclid d) ≃ₜ (Euclid d) := Homeomorph.addRight c
  refine ⟨u ∘ move,eu.comp move.isOpenEmbedding,?_,?_⟩
  · change u (0+c)=p
    simpa only [zero_add] using hc
  · intro x hx
    obtain ⟨z,rfl⟩ := inside hx
    exact ⟨move.symm z,by simp⟩

theorem extend_cell {X : Type*} [TopologicalSpace X] [T2Space X]
    (engulf : ∀ K : Set X, IsCompact K → ∃ g : (Euclid d) → X, IsOpenEmbedding g ∧ K ⊆ range g)
    (f : (Euclid d) → X) (ef : IsOpenEmbedding f) (a b : ℝ) (apos : 0 < a) (ab : a < b)
    (K : Set X) (compactK : IsCompact K) :
    ∃ h : (Euclid d) → X, IsOpenEmbedding h ∧ EqOn h f (ball 0 a) ∧ K ⊆ h '' ball 0 b := by
  let D := K ∪ f '' closedBall 0 b
  have bpos := apos.trans ab
  have compactD : IsCompact D := compactK.union ((isCompact_closedBall 0 b).image ef.continuous)
  have base : f 0∈D := Or.inr ⟨0,mem_closedBall_self bpos.le,rfl⟩
  obtain ⟨g,eg,center,in_g⟩ := center_chart D base (engulf D compactD)
  have outercenter : g 0∈f '' ball 0 b := by rw [center]; exact ⟨0,mem_ball_self bpos,rfl⟩
  obtain ⟨r,rpos,small_g⟩ := neighborhood_ball g eg.continuous (ef.isOpenMap _ isOpen_ball) outercenter
  let c := r/2
  have cpos : 0 < c := by dsimp [c]; linarith
  have cr : c < r := by dsimp [c]; linarith
  have innercenter : f 0∈g '' ball 0 c := ⟨0,mem_ball_self cpos,center⟩
  obtain ⟨s0,spos0,small_f⟩ := neighborhood_ball f ef.continuous (eg.isOpenMap _ isOpen_ball) innercenter
  let s := min s0 (a/2)
  have sp : 0 < s := lt_min spos0 (by linarith)
  have sa : s < a := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hs : 0 < s/2 := by linarith
  have half : s/2 < s := by linarith
  obtain ⟨compress,_,shrink,preserve,off⟩ :=
    stretch_chart ef hs (half.trans sa) ab half (sa.trans ab)
  have small_image : compress '' (f '' ball 0 a) ⊆ g '' closedBall 0 c := by
    rw [shrink]
    exact ((image_mono (ball_subset_ball (min_le_left _ _))).trans small_f).trans
      (image_mono ball_subset_closedBall)
  have image_in_g : compress '' K ⊆ range g := by
    rintro _ ⟨x,hx,rfl⟩
    by_contra outside
    have untouched := off (compress x) (fun h => outside (in_g (Or.inr h)))
    have fixed : compress x=x := compress.injective untouched
    exact outside (fixed.symm ▸ in_g (Or.inl hx))
  have precompact := eg.isEmbedding.isInducing.isCompact_preimage'
    (compactK.image compress.continuous) image_in_g
  obtain ⟨R,rR,bound⟩ := precompact.isBounded.subset_ball_lt r (0 : (Euclid d))
  obtain ⟨expand,fix_core,grow,_,_⟩ :=
    stretch_chart eg cpos cr (show r < R+1 by linarith) (cr.trans rR) (show R < R+1 by linarith)
  let changeChart := (compress.trans expand).trans compress.symm
  refine ⟨changeChart ∘ f,changeChart.isOpenEmbedding.comp ef,?_,?_⟩
  · intro x hx
    have small := small_image ⟨f x,⟨x,hx,rfl⟩,rfl⟩
    change compress.symm (expand (compress (f x)))=f x
    rw [show expand (compress (f x))=compress (f x) from fix_core small,compress.symm_apply_apply]
  · intro y hy
    have moved : compress y∈compress '' K := ⟨y,hy,rfl⟩
    obtain ⟨z,hz⟩ := image_in_g moved
    have source : z∈g ⁻¹' (compress '' K) := by
      change g z∈compress '' K
      rw [hz]
      exact moved
    have in_ball : compress y∈g '' ball 0 R := ⟨z,bound source,hz⟩
    rw [← grow] at in_ball
    have in_large := (image_mono small_g) in_ball
    obtain ⟨t,ht,eq⟩ := in_large
    rw [← preserve] at ht
    obtain ⟨_,⟨x,hx,rfl⟩,rfl⟩ := ht
    refine ⟨x,hx,?_⟩
    change compress.symm (expand (compress (f x)))=y
    rw [eq,compress.symm_apply_apply]

end BrownOpenCells

open Set Topology

namespace BrownOpenCells

theorem assemble {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (U : ℕ → Set X) (op : ∀ n, IsOpen (U n)) (nested : Monotone U)
    (cover : (⋃ n, U n)=univ) (f : ℕ → X → Y) (emb : ∀ n, IsOpenEmbedding (f n))
    (compatible : ∀ n, EqOn (f (n+1)) (f n) (U n))
    (onto : ∀ y, ∃ n, y∈f n '' U n) : Nonempty (X ≃ₜ Y) := by
  classical
  have stage (x : X) : ∃ n, x∈U n := iUnion_eq_univ_iff.mp cover x
  let F (x : X) := f (stage x).choose x
  have after {m n : ℕ} (mn : m≤n) {x : X} (hx : x∈U m) : f n x=f m x := by
    induction n, mn using Nat.le_induction with
    | base => rfl
    | succ n h ih => exact (compatible n (nested h hx)).trans ih
  have here {n : ℕ} {x : X} (hx : x∈U n) : F x=f n x := by
    rcases le_total (stage x).choose n with h | h
    · exact (after h (stage x).choose_spec).symm
    · exact after h hx
  have inject : Function.Injective F := by
    intro x y eq
    let k := max (stage x).choose (stage y).choose
    have hx : x∈U k := nested (le_max_left _ _) (stage x).choose_spec
    have hy : y∈U k := nested (le_max_right _ _) (stage y).choose_spec
    exact (emb k).injective ((here hx).symm.trans (eq.trans (here hy)))
  have surject : Function.Surjective F := by
    intro y
    obtain ⟨n,x,hx,rfl⟩ := onto y
    exact ⟨x,here hx⟩
  have continuous : Continuous F := by
    apply continuous_def.mpr
    intro V hV
    have sets : F ⁻¹' V=⋃ n, U n ∩ f n ⁻¹' V := by
      ext x
      constructor
      · intro hx
        obtain ⟨n,hn⟩ := stage x
        exact mem_iUnion.mpr ⟨n,hn,by simpa only [mem_preimage,← here hn] using hx⟩
      · intro hx
        obtain ⟨n,hn,hxy⟩ := mem_iUnion.mp hx
        simpa only [mem_preimage,here hn] using hxy
    rw [sets]
    exact isOpen_iUnion fun n => (op n).inter (hV.preimage (emb n).continuous)
  have openMap : IsOpenMap F := by
    intro V hV
    have sets : F '' V=⋃ n, f n '' (V ∩ U n) := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨n,hn⟩ := stage x
        exact mem_iUnion.mpr ⟨n,x,⟨hx,hn⟩,(here hn).symm⟩
      · intro hy
        obtain ⟨n,x,⟨hx,hn⟩,rfl⟩ := mem_iUnion.mp hy
        exact ⟨x,hx,here hn⟩
    rw [sets]
    exact isOpen_iUnion fun n => (emb n).isOpenMap _ (hV.inter (op n))
  exact ⟨(Equiv.ofBijective F ⟨inject,surject⟩).toHomeomorphOfContinuousOpen continuous openMap⟩

end BrownOpenCells


namespace BrownOpenCells
open Set Topology Metric

variable {d : ℕ}

/-- If each embedding can be enlarged while fixing its previous ball, the
compatible enlarged embeddings give a homeomorphism onto the entire space. -/
theorem of_extensions {X : Type*} [TopologicalSpace X] [SigmaCompactSpace X]
    (start : ∃ f : (Euclid d) → X, IsOpenEmbedding f)
    (extend : ∀ (f : (Euclid d) → X), IsOpenEmbedding f → ∀ (a b : ℝ), 0<a → a<b →
      ∀ K : Set X, IsCompact K → ∃ g : (Euclid d) → X, IsOpenEmbedding g ∧
        EqOn g f (ball 0 a) ∧ K ⊆ g '' ball 0 b) : Nonempty (X ≃ₜ (Euclid d)) := by
  classical
  let U (n : ℕ) := ball (0 : (Euclid d)) ((n : ℝ)+1)
  obtain ⟨K,hK,covers⟩ := SigmaCompactSpace.exists_compact_covering (X:=X)
  let Chart := {f : (Euclid d) → X // IsOpenEmbedding f}
  have more (n : ℕ) (f : Chart) :
      ∃ g : Chart, EqOn g.val f.val (U n) ∧ K n ⊆ g.val '' U (n+1) := by
    have up : (n : ℝ)+1<((n+1 : ℕ) : ℝ)+1 := by push_cast; linarith
    obtain ⟨g,embedding,agree,wide⟩ := extend f.val f.property _ _ (by positivity) up _ (hK n)
    exact ⟨⟨g,embedding⟩,agree,wide⟩
  let seed : Chart := ⟨start.choose,start.choose_spec⟩
  let stages : ℕ → Chart := Nat.rec seed (fun n f => (more n f).choose)
  have step (n : ℕ) : EqOn (stages (n+1)).val (stages n).val (U n) ∧
      K n ⊆ (stages (n+1)).val '' U (n+1) := (more n (stages n)).choose_spec
  have increases : Monotone U := by
    intro i j ij
    apply ball_subset_ball
    have hij : (i : ℝ)≤(j : ℝ) := Nat.cast_le.mpr ij
    linarith
  have balls : (⋃ n, U n)=univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨n,hn⟩ := exists_nat_gt (dist x 0)
    exact ⟨n,show dist x 0 < (n : ℝ)+1 by linarith⟩
  obtain ⟨total⟩ := assemble U (fun _ => isOpen_ball) increases balls
    (fun n => (stages n).val) (fun n => (stages n).property) (fun n => (step n).1) (by
      intro y
      obtain ⟨n,hy⟩ := iUnion_eq_univ_iff.mp covers y
      exact ⟨n+1,(step n).2 hy⟩)
  exact ⟨total.symm⟩

end BrownOpenCells

open Set Topology Metric

namespace BrownOpenCells

/-- Morton Brown's monotone union theorem for open Euclidean cells. -/
theorem monotone_union (d : ℕ) {X : Type*} [TopologicalSpace X] [T2Space X] (U : ℕ → Set X)
    (op : ∀ n, IsOpen (U n)) (nested : Monotone U) (cover : (⋃ n, U n)=univ)
    (euclidean : ∀ n, Nonempty (U n ≃ₜ EuclideanSpace ℝ (Fin d))) :
    Nonempty (X ≃ₜ EuclideanSpace ℝ (Fin d)) := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  have in_chart (K : Set X) (compactK : IsCompact K) : ∃ n, K ⊆ U n :=
    compactK.elim_directed_cover U op (by rw [cover]; exact subset_univ _) fun i j =>
      ⟨max i j,nested (le_max_left _ _),nested (le_max_right _ _)⟩
  have engulf (K : Set X) (compactK : IsCompact K) : ∃ f : E → X, IsOpenEmbedding f ∧ K ⊆ range f := by
    obtain ⟨n,contains⟩ := in_chart K compactK
    obtain ⟨e⟩ := euclidean n
    refine ⟨(Subtype.val : U n → X) ∘ e.symm,
      (op n).isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding,?_⟩
    intro x hx
    refine ⟨e ⟨x,contains hx⟩,?_⟩
    simp
  have sigma (n : ℕ) : IsSigmaCompact (U n) := by
    obtain ⟨e⟩ := euclidean n
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr e.isClosedEmbedding.sigmaCompactSpace
  have : SigmaCompactSpace X := isSigmaCompact_univ_iff.mp (by
    rw [← cover]
    exact isSigmaCompact_iUnion U sigma)
  obtain ⟨f,ef,_⟩ := engulf ∅ isCompact_empty
  exact of_extensions ⟨f,ef⟩ (extend_cell engulf)

end BrownOpenCells
