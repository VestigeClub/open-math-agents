import FormalConjectures.ErdosProblems.«774»
import Mathlib

/-!
# The weighted extraction proportion of the Grow–Whicher example

The finite set in Grow and Whicher, *Finite unions of quasi-independent
sets* (1984), has unweighted extraction proportion at least one half.
For arbitrary nonnegative weights the best proportion is exactly 13/27.
-/

open Finset

namespace GrowWhicher

private def represents (bits : ℕ) (P : Finset ℕ) : Prop :=
  ∀ t, bits.testBit t = true → ∃ S ⊆ P, (∑ n ∈ S, n) = t

private theorem start_bits : represents 1 ∅ := by
  intro t h
  exact ⟨∅, Subset.rfl, by simp [Nat.testBit_one_eq_true_iff_self_eq_zero.mp h]⟩

private theorem shift_witness {a t bits : ℕ} {P : Finset ℕ}
    (rep : represents bits P) (h : (bits <<< a).testBit t = true) :
    ∃ S ⊆ P, a + (∑ n ∈ S, n) = t := by
  have step := Bool.and_eq_true_iff.mp ((Nat.testBit_shiftLeft bits).symm ▸ h)
  obtain ⟨S,sub,eq⟩ := rep _ step.2
  exact ⟨S,sub,by have := of_decide_eq_true step.1; omega⟩

private theorem insert_bits {a bits : ℕ} {P : Finset ℕ}
    (outside : a ∉ P) (rep : represents bits P) :
    represents (bits ||| (bits <<< a)) (insert a P) := by
  intro t h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with old | shifted
  · obtain ⟨S,sub,eq⟩ := rep _ old
    exact ⟨S,sub.trans (subset_insert _ _),eq⟩
  · obtain ⟨S,sub,eq⟩ := shift_witness rep shifted
    have absent : a ∉ S := fun h => outside (sub h)
    exact ⟨insert a S, insert_subset_insert _ sub, by simpa [Finset.sum_insert,absent] using eq⟩

private theorem no_overlap {a bits : ℕ} {P U : Finset ℕ} (rep : represents bits P)
    (outside : a ∉ P) (sub : P ⊆ U) (ha : a ∈ U) (indep : Set.IsDissociated (↑U : Set ℕ)) :
    bits &&& (bits <<< a) = 0 := by
  by_contra wrong
  obtain ⟨t,h⟩ := Nat.exists_testBit_of_ne_zero wrong
  rw [Nat.testBit_and, Bool.and_eq_true] at h
  obtain ⟨S,small,hs⟩ := rep _ h.1
  obtain ⟨T,small',ht⟩ := shift_witness rep h.2
  have absent : a ∉ T := fun h => outside (small' h)
  have inc : insert a T ⊆ U := Finset.insert_subset ha (small'.trans sub)
  have equal : (∑ n ∈ S, n) = ∑ n ∈ insert a T, n := by
    rw [Finset.sum_insert absent]
    exact hs.trans ht.symm
  have ident : S = insert a T := indep (small.trans sub) inc equal
  have exists_a : a ∈ S := ident ▸ Finset.mem_insert_self a T
  exact outside (small exists_a)

/-- Maximize the weight over candidate selections. The bit at t represents
a subset of the already selected elements with sum t. A repeated sum rules
out taking the next element in a dissociated set. -/
private def best (w : ℕ → ℕ) (bits : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: rest =>
    let skip := best w bits rest
    if bits &&& (bits <<< a) = 0 then
      max skip (w a + best w (bits ||| (bits <<< a)) rest)
    else skip

private theorem best_bound (w : ℕ → ℕ) (U : Finset ℕ) (indep : Set.IsDissociated (↑U : Set ℕ))
    (rest : List ℕ) (nodup : rest.Nodup) (bits : ℕ) (P W : Finset ℕ)
    (rep : represents bits P) (subP : P ⊆ U) (subW : W ⊆ U)
    (outside : ∀ n ∈ rest, n ∉ P) (within : W ⊆ rest.toFinset) :
    (∑ n ∈ W, w n) ≤ best w bits rest := by
  induction rest generalizing bits P W with
  | nil =>
    have no : W = ∅ := le_antisymm (by simpa using within) (empty_subset _)
    simp [no,best]
  | cons a rest ih =>
    have tail := (List.nodup_cons.mp nodup).2
    have fresh := outside a (List.mem_cons_self ..)
    have out (n) (hn : n ∈ rest) := outside n (List.mem_cons_of_mem a hn)
    by_cases ha : a ∈ W
    · have compatible := no_overlap rep fresh subP (subW ha) indep
      have smaller : W.erase a ⊆ rest.toFinset := by
        intro n hn
        have memAll : n ∈ a :: rest := List.mem_toFinset.mp (within (mem_erase.mp hn).2)
        exact List.mem_toFinset.mpr ((List.mem_cons.mp memAll).resolve_left (mem_erase.mp hn).1)
      have outside' (n) (hn : n ∈ rest) : n ∉ insert a P := by
        intro h
        rcases Finset.mem_insert.mp h with rfl | p
        · exact (List.nodup_cons.mp nodup).1 hn
        · exact out n hn p
      have bound := ih tail _ _ _ (insert_bits fresh rep)
        (Finset.insert_subset (subW ha) subP) ((Finset.erase_subset _ _).trans subW) outside' smaller
      rw [best, if_pos compatible, ← Finset.add_sum_erase W w ha]
      exact (Nat.add_le_add_left bound _).trans (le_max_right _ _)
    · have smaller : W ⊆ rest.toFinset := by
        intro n hn
        have old := List.mem_cons.mp (List.mem_toFinset.mp (within hn))
        exact List.mem_toFinset.mpr (old.resolve_left (fun e => ha (e ▸ hn)))
      have bound := ih tail _ _ _ rep subP subW out smaller
      rw [best]
      split
      · exact bound.trans (le_max_left _ _)
      · exact bound

private def numbers : List ℕ := [3,4,5,9,11,13,27,30,33,81,85,89,243,248,253]
def exampleSet : Finset ℕ := numbers.toFinset

/-- Dual weights witnessing the upper bound on the extraction proportion. -/
def dualWeight (n : ℕ) : ℕ := if n < 243 then 2 else 1

private theorem maximal_weight : best dualWeight 1 numbers = 13 := by decide +kernel

theorem weighted_upper (U : Finset ℕ) (sub : U ⊆ exampleSet)
    (indep : Set.IsDissociated (↑U : Set ℕ)) : (∑ n ∈ U, dualWeight n) ≤ 13 := by
  rw [← maximal_weight]
  exact best_bound dualWeight U indep numbers (by decide) 1 ∅ U start_bits
    (empty_subset _) Subset.rfl (by simp) sub


/-- A finite set is dissociated when its distinct subsets have distinct sums. -/
private theorem independent_of_card (F : Finset ℕ)
    (hc : (F.powerset.image (fun A => ∑ n ∈ A, n)).card = F.powerset.card) :
    Set.IsDissociated (↑F : Set ℕ) := by
  intro S inside T small eq
  exact Finset.card_image_iff.mp hc (Finset.mem_powerset.mpr inside)
    (Finset.mem_powerset.mpr small) eq

private def pieces : Fin 13 → Finset ℕ :=
  ![{4,5,11,13,27,81,243},
    {3,4,11,13,30,85,243},
    {5,9,11,13,30,85,243},
    {3,4,5,11,33,85,243},
    {3,5,11,27,81,85,243},
    {3,4,5,11,27,89,243},
    {3,5,9,13,33,85,248},
    {9,13,27,30,33,89,248},
    {9,27,30,33,85,89,248},
    {3,5,9,13,33,81,253},
    {3,4,5,13,30,85,253},
    {4,11,27,81,89,243,248,253},
    {4,11,30,81,89,243,248,253}]

private def allocation : Fin 27 → Fin 13 :=
  ![0,1,1,2,3,4,5,6,7,8,8,8,8,8,9,9,9,9,9,10,10,11,11,11,11,12,12]

private def cover (i : Fin 27) := pieces (allocation i)

private theorem good_pieces (j : Fin 13) : Set.IsDissociated (↑(pieces j) : Set ℕ) := by
  apply independent_of_card
  fin_cases j <;> decide +kernel

private theorem inside : ∀ i, cover i ⊆ exampleSet := by decide +kernel

private theorem times : ∀ n ∈ exampleSet,
    (univ.filter (fun i : Fin 27 => n ∈ cover i)).card = 13 := by decide +kernel

/-- Twenty-seven sets counted with multiplicity cover each point exactly
thirteen times. At least one of them carries its share of any given weight. -/
theorem weighted_lower (w : ℕ → ℝ) :
    ∃ U ⊆ exampleSet, Set.IsDissociated (↑U : Set ℕ) ∧
      (13/27 : ℝ) * (∑ n ∈ exampleSet, w n) ≤ ∑ n ∈ U, w n := by
  let mass (i : Fin 27) := ∑ n ∈ cover i, w n
  have row (i : Fin 27) : mass i = ∑ n ∈ exampleSet, if n ∈ cover i then w n else 0 := by
    rw [← Finset.sum_filter]
    have same : exampleSet.filter (· ∈ cover i) = cover i := by
      ext n
      exact Finset.mem_filter.trans ⟨And.right, fun h => ⟨inside i h,h⟩⟩
    rw [same]
  have col (n : ℕ) (hn : n ∈ exampleSet) :
      (∑ i : Fin 27, if n ∈ cover i then w n else 0) = 13 * w n := by
    rw [← Finset.sum_filter, Finset.sum_const, times n hn]
    simp [nsmul_eq_mul]
  have total : (∑ i, mass i) = 13 * ∑ n ∈ exampleSet, w n := by
    calc
      (∑ i, mass i) = ∑ i : Fin 27, ∑ n ∈ exampleSet, if n ∈ cover i then w n else 0 :=
        Finset.sum_congr rfl (fun i _ => row i)
      _ = ∑ n ∈ exampleSet, ∑ i : Fin 27, if n ∈ cover i then w n else 0 := Finset.sum_comm
      _ = ∑ n ∈ exampleSet, 13 * w n := Finset.sum_congr rfl col
      _ = 13 * ∑ n ∈ exampleSet, w n := (Finset.mul_sum ..).symm
  have heavy : ∃ i : Fin 27, (13/27 : ℝ) * (∑ n ∈ exampleSet, w n) ≤ mass i := by
    by_contra! light
    have strict := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α:=Fin 27))
      (fun i _ => light i)
    rw [total] at strict
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] at strict
    linarith
  obtain ⟨i,hi⟩ := heavy
  exact ⟨cover i,inside i,good_pieces (allocation i),hi⟩


/-- For the fifteen-element example, uniform weighted extraction holds with
proportion c precisely up to 13/27. The explicit dual weights sum to 27. -/
theorem optimal_proportion (c : ℝ) :
    (∀ w : ℕ → ℝ, (∀ n ∈ exampleSet, 0 ≤ w n) →
      ∃ U ⊆ exampleSet, Set.IsDissociated (↑U : Set ℕ) ∧
        c * (∑ n ∈ exampleSet, w n) ≤ ∑ n ∈ U, w n) ↔ c ≤ 13/27 := by
  constructor
  · intro extract
    let w (n : ℕ) : ℝ := dualWeight n
    obtain ⟨U,sub,indep,heavy⟩ := extract w (fun _ _ => Nat.cast_nonneg _)
    have natural : (∑ n ∈ exampleSet, dualWeight n) = 27 := by decide
    have total : (∑ n ∈ exampleSet, w n) = 27 := by
      change (∑ n ∈ exampleSet, (dualWeight n : ℝ)) = 27
      exact_mod_cast natural
    have bound : (∑ n ∈ U, w n) ≤ 13 := by
      change (∑ n ∈ U, (dualWeight n : ℝ)) ≤ 13
      exact_mod_cast weighted_upper U sub indep
    rw [total] at heavy
    linarith
  · intro hc w positive
    obtain ⟨U,sub,indep,heavy⟩ := weighted_lower w
    exact ⟨U,sub,indep,(mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg positive)).trans heavy⟩

end GrowWhicher
