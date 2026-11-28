import certificates.«brown-monotone-union»
import Mathlib

/-!
# A compact space covered by two Euclidean charts is a sphere

We follow Theorem 2.7 in Steve Ferry's *Geometric topology*. A puncture at a
point outside the second chart leaves a space in which every compact set fits
in a single chart. Brown's extension argument identifies that puncture with
Euclidean space. Taking its one-point compactification identifies the sphere.

https://www.math.rutgers.edu/~sferry/ps/geotop.pdf#page=4
-/

open Set Topology Metric

namespace TwoEuclideanCharts

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Each compact subset away from the center fits inside a moved copy of the
second chart. Its image still avoids the center. -/
theorem engulf_puncture {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] {f g : E d → X} (ef : IsOpenEmbedding f) (eg : IsOpenEmbedding g)
    (cover : range f ∪ range g = univ) {p : X} (center : f 0 = p) (outside : p ∉ range g)
    (K : Set (↥({p}ᶜ : Set X))) (compactK : IsCompact K) :
    ∃ h : E d → ↥({p}ᶜ : Set X), IsOpenEmbedding h ∧ K ⊆ range h := by
  classical
  let P := ({p}ᶜ : Set X)
  let D := (range g)ᶜ
  have inFirst : D ⊆ range f := by
    intro y hy
    have mem : y ∈ range f ∪ range g := cover.symm ▸ mem_univ y
    exact mem.resolve_right hy
  have compactD : IsCompact D := eg.isOpen_range.isClosed_compl.isCompact
  have bounded := ef.isEmbedding.isInducing.isCompact_preimage' compactD inFirst
  obtain ⟨R,oneR,bound⟩ := bounded.isBounded.subset_ball_lt 1 (0 : E d)
  have firstBall : D ⊆ f '' ball 0 R := by
    intro y hy
    obtain ⟨z,rfl⟩ := inFirst hy
    exact ⟨z,bound hy,rfl⟩
  let A := (Subtype.val : P → X) '' K
  have closedA : IsClosed A := (compactK.image continuous_subtype_val).isClosed
  have pOutside : p ∉ A := by
    rintro ⟨x,_,eq⟩
    exact x.property (mem_singleton_iff.mpr eq)
  have op : IsOpen (f ⁻¹' Aᶜ) := closedA.isOpen_compl.preimage ef.continuous
  obtain ⟨δ,δpos,small⟩ := Metric.isOpen_iff.mp op 0 (show f 0 ∉ A from center ▸ pOutside)
  let r := min δ (R/2)
  have rpos : 0 < r := lt_min δpos (by linarith)
  have rR : r < R := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have halfpos : 0 < r/2 := by linarith
  have half : r/2 < r := by linarith
  obtain ⟨H,fixCenter,stretch,_,_⟩ :=
    BrownOpenCells.stretch_chart ef halfpos half (show r < R+1 by linarith)
      (half.trans rR) (show R < R+1 by linarith)
  have fixed : H p = p := by
    apply fixCenter
    exact ⟨0,mem_closedBall_self halfpos.le,center⟩
  have misses {y : X} (hy : y ∈ A) : y ∉ f '' ball 0 r := by
    rintro ⟨z,hz,rfl⟩
    exact small (ball_subset_ball (min_le_left δ (R/2)) hz) hy
  have moved {y : X} (hy : y ∈ A) : H y ∈ range g := by
    by_contra no
    have inLarge := firstBall no
    rw [← stretch] at inLarge
    obtain ⟨z,hz,equal⟩ := inLarge
    exact misses hy (H.injective equal ▸ hz)
  have avoid (t : E d) : H.symm (g t) ∈ P := by
    intro eq
    have eq' : H.symm (g t)=p := mem_singleton_iff.mp eq
    exact outside ⟨t,(H.apply_symm_apply _).symm.trans ((congrArg H eq').trans fixed)⟩
  let h (t : E d) : P := ⟨H.symm (g t),avoid t⟩
  have opP : IsOpen P := isClosed_singleton.isOpen_compl
  refine ⟨h,IsOpenEmbedding.of_comp h opP.isOpenEmbedding_subtypeVal
    (H.symm.isOpenEmbedding.comp eg),?_⟩
  intro y hy
  obtain ⟨t,ht⟩ := moved (show y.val ∈ A from ⟨y,hy,rfl⟩)
  refine ⟨t,Subtype.ext ?_⟩
  change H.symm (g t) = y.val
  rw [ht,H.symm_apply_apply]

private theorem sigma_puncture {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
    {f g : E d → X} (ef : IsOpenEmbedding f) (eg : IsOpenEmbedding g)
    (cover : range f ∪ range g = univ) {p : X} (outside : p ∉ range g) :
    SigmaCompactSpace (↥({p}ᶜ : Set X)) := by
  let P := ({p}ᶜ : Set X)
  let C := f ⁻¹' P
  have opC : IsOpen C := isClosed_singleton.isOpen_compl.preimage ef.continuous
  let _ : LocallyCompactSpace C := opC.locallyCompactSpace
  have sigmaC : IsSigmaCompact C := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  have pieces : P = f '' C ∪ range g := by
    ext y
    constructor
    · intro hy
      have mem : y ∈ range f ∪ range g := cover.symm ▸ mem_univ y
      rcases mem with ⟨z,rfl⟩ | hg
      · exact Or.inl ⟨z,hy,rfl⟩
      · exact Or.inr hg
    · rintro (⟨z,hz,rfl⟩ | hg)
      · exact hz
      · intro eq
        exact outside (mem_singleton_iff.mp eq ▸ hg)
  apply isSigmaCompact_iff_sigmaCompactSpace.mp
  change IsSigmaCompact P
  rw [pieces]
  obtain ⟨A,hA,eqA⟩ := sigmaC.image ef.continuous
  obtain ⟨B,hB,eqB⟩ := isSigmaCompact_range eg.continuous
  refine ⟨fun k => A k ∪ B k,fun k => (hA k).union (hB k),?_⟩
  simp only [iUnion_union_distrib,eqA,eqB]

/-- Two Euclidean charts covering a compact Hausdorff space of positive
dimension suffice to recognize the topological sphere. -/
theorem sphere_of_two_charts (n : ℕ) {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] (f g : EuclideanSpace ℝ (Fin (n+1)) → X)
    (ef : IsOpenEmbedding f) (eg : IsOpenEmbedding g) (cover : range f ∪ range g = univ) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1) := by
  classical
  obtain ⟨p,outside⟩ : ∃ p : X, p ∉ range g := by
    by_contra! full
    have compact := eg.isEmbedding.isInducing.isCompact_preimage' (isCompact_univ (X:=X))
      (fun y _ => full y)
    exact noncompact_univ (E (n+1)) (by simpa only [preimage_univ] using compact)
  have mem : p ∈ range f ∪ range g := cover.symm ▸ mem_univ p
  obtain ⟨c,center⟩ := mem.resolve_right outside
  let move := Homeomorph.addRight c
  let u := f ∘ move
  have eu : IsOpenEmbedding u := ef.comp move.isOpenEmbedding
  have center' : u 0=p := by
    change f (0+c)=p
    simpa only [zero_add] using center
  have replacement : range u = range f := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨move t,rfl⟩
    · rintro ⟨t,rfl⟩
      exact ⟨move.symm t,by simp [u]⟩
  have covered : range u ∪ range g=univ := by rw [replacement,cover]
  let P := ({p}ᶜ : Set X)
  let _ : SigmaCompactSpace P := sigma_puncture eu eg covered outside
  have charts := engulf_puncture eu eg covered center' outside
  obtain ⟨seed,eseed,_⟩ := charts ∅ isCompact_empty
  obtain ⟨e⟩ := BrownOpenCells.of_extensions ⟨seed,eseed⟩ (BrownOpenCells.extend_cell charts)
  let compactification := OnePoint.equivOfIsEmbeddingOfRangeEq p (Subtype.val : P → X)
    Topology.IsEmbedding.subtypeVal Subtype.range_val
  exact ⟨compactification.symm.trans (e.onePointCongr.trans (onePointEquivSphereOfFinrankEq (by simp)))⟩

/-- A compact Hausdorff space covered by two open Euclidean cells of the same
positive dimension is homeomorphic to the sphere of that dimension. -/
theorem sphere_of_two_cells (n : ℕ) {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] (U V : Set X) (openU : IsOpen U) (openV : IsOpen V) (cover : U ∪ V = univ)
    (hU : Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin (n+1))))
    (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin (n+1)))) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1) := by
  obtain ⟨u⟩ := hU
  obtain ⟨v⟩ := hV
  apply sphere_of_two_charts n (Subtype.val ∘ u.symm) (Subtype.val ∘ v.symm)
    (openU.isOpenEmbedding_subtypeVal.comp u.symm.isOpenEmbedding)
    (openV.isOpenEmbedding_subtypeVal.comp v.symm.isOpenEmbedding)
  simpa only [range_comp,u.symm.surjective.range_eq,v.symm.surjective.range_eq,
    image_univ,Subtype.range_val] using cover

end TwoEuclideanCharts
