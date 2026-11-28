import Mathlib

/-!
# Simultaneous permutation bounds for colour conflicts

For a family of maps on a q-colour palette, relabel all colours by one permutation.
If there are fewer than k! maps, there is a relabelling for which each map
agrees with the inverse permutation in fewer than k places. Prescribing k matches
admits at most (q-k)! permutations, even if a map repeats values. Applied to
a fixed proper edge colouring and a proper vertex colouring, this bounds the
number of rejected edges incident to each vertex. The bound depends on the
order of the graph or its connected components.

For the reject graph in total colouring, see M. Molloy and B. Reed,
*A bound on the total chromatic number*, Combinatorica 18 (1998), 241–280.
https://doi.org/10.1007/PL00009820
-/

open Finset Equiv

namespace ColourRelabelling

private noncomputable def extensions {C : Type*} [Fintype C] [DecidableEq C]
    (f : C → C) (A : Finset C) : Finset (Perm C) := by
  classical
  exact univ.filter fun σ => ∀ t ∈ A, σ (f t)=t

private theorem mem_extensions {C : Type*} [Fintype C] [DecidableEq C]
    {f : C → C} {A : Finset C} {σ : Perm C} :
    σ ∈ extensions f A ↔ ∀ t ∈ A, σ (f t)=t := by
  classical
  simp [extensions]

private theorem card_extensions {C : Type*} [Fintype C] [DecidableEq C]
    (f : C → C) (A : Finset C) :
    (extensions f A).card ≤ (Fintype.card C - A.card).factorial := by
  classical
  rcases (extensions f A).eq_empty_or_nonempty with e | ⟨ρ,hρ⟩
  · simp [e]
  have count : (extensions f A).card ≤ (permsOfFinset Aᶜ).card := by
    apply card_le_card_of_injOn (fun σ : Perm C => σ * ρ⁻¹)
    · intro σ hσ
      apply mem_perms_of_finset_iff.mpr
      intro t differs
      apply Finset.mem_compl.mpr
      intro ht
      have one := (mem_extensions.mp hρ) t ht
      have two := (mem_extensions.mp hσ) t ht
      have back : ρ.symm t = f t := ρ.symm_apply_eq.mpr one.symm
      apply differs
      change σ (ρ.symm t) = t
      rw [back,two]
    · intro x _ y _ hxy
      exact mul_right_cancel hxy
  simpa only [card_perms_of_finset,card_compl] using count

/-- A single relabelling avoids k simultaneous matches for every member
of a family of fewer than k! maps on the palette. -/
private theorem simultaneous_of_le {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]
    (f : V → C → C) {k : ℕ} (hk : k ≤ Fintype.card C) (few : Fintype.card V < k.factorial) :
    ∃ σ : Perm C, ∀ v, (univ.filter fun t => σ (f v t)=t).card < k := by
  classical
  let q := Fintype.card C
  let family := (univ : Finset C).powersetCard k
  let bad (v : V) := family.biUnion fun A => extensions (f v) A
  have bound (v : V) : (bad v).card ≤ q.choose k * (q-k).factorial := by
    calc
      (bad v).card ≤ ∑ A ∈ family, (extensions (f v) A).card := card_biUnion_le
      _ ≤ ∑ _A ∈ family, (q-k).factorial := by
        apply sum_le_sum
        intro A hA
        have size : A.card=k := (mem_powersetCard.mp hA).2
        simpa only [size] using card_extensions (f v) A
      _ = q.choose k * (q-k).factorial := by simp [family,q]
  by_contra! fails
  have swept : (univ : Finset (Perm C)) ⊆ univ.biUnion bad := by
    intro σ _
    obtain ⟨v,hv⟩ := fails σ
    obtain ⟨A,sub,hcard⟩ := exists_subset_card_eq hv
    apply mem_biUnion.mpr
    refine ⟨v,mem_univ _,mem_biUnion.mpr ⟨A,mem_powersetCard.mpr ⟨subset_univ _,hcard⟩,?_⟩⟩
    exact mem_extensions.mpr fun t ht => (mem_filter.mp (sub ht)).2
  have upper : q.factorial ≤ Fintype.card V * (q.choose k * (q-k).factorial) := by
    calc
      q.factorial = (univ : Finset (Perm C)).card := by simp [q,Fintype.card_perm]
      _ ≤ (univ.biUnion bad).card := card_le_card swept
      _ ≤ ∑ v, (bad v).card := card_biUnion_le
      _ ≤ ∑ _v : V, q.choose k * (q-k).factorial := sum_le_sum fun v _ => bound v
      _ = _ := by simp
  have pos : 0 < q.choose k * (q-k).factorial := Nat.mul_pos (Nat.choose_pos hk) (Nat.factorial_pos _)
  have smaller := Nat.mul_lt_mul_of_pos_right few pos
  have identity : k.factorial * (q.choose k * (q-k).factorial) = q.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hk]
    ac_rfl
  rw [identity] at smaller
  exact (not_lt_of_ge upper) smaller

/-- If there are fewer than k! constraints, one permutation has fewer than k
matches in every constraint. This also covers palettes with fewer than k colours. -/
theorem simultaneous {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]
    (f : V → C → C) {k : ℕ} (few : Fintype.card V < k.factorial) :
    ∃ σ : Perm C, ∀ v, (univ.filter fun t => σ (f v t)=t).card < k := by
  classical
  by_cases hk : k ≤ Fintype.card C
  · exact simultaneous_of_le f hk few
  · refine ⟨1,fun v => ?_⟩
    have size := card_filter_le (univ : Finset C) (fun t => (1 : Perm C) (f v t)=t)
    rw [card_univ] at size
    omega

end ColourRelabelling

namespace ColourRelabelling

open SimpleGraph Finset Equiv

/-- For a fixed proper edge colouring, a separate permutation of the vertex colours
in each part of a partition with no crossing edges keeps reject degrees bounded. -/
theorem bounded_rejects_of_parts {V C I : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] [DecidableEq C] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : G.edgeSet → C)
    (properEdge : ∀ a b : G.edgeSet, a ≠ b →
      (∃ u, u ∈ (a : Sym2 V) ∧ u ∈ (b : Sym2 V)) → e a ≠ e b)
    (c : V → C) (properVertex : ∀ u v, G.Adj u v → c u ≠ c v)
    (part : V → I) (closed : ∀ {u v}, G.Adj u v → part u=part v)
    {k : ℕ} (few : ∀ i, Nat.card {v // part v=i} < k.factorial) :
    ∃ σ : I → Perm C, (∀ u v, G.Adj u v → σ (part u) (c u) ≠ σ (part v) (c v)) ∧ ∀ u,
      {a : Sym2 V | u ∈ a ∧ ∃ ha : a ∈ G.edgeSet, ∃ v ∈ a, σ (part v) (c v) = e ⟨a,ha⟩}.ncard ≤ k := by
  classical
  have unique {u : V} {a b : G.edgeSet} (ha : u ∈ (a : Sym2 V))
      (hb : u ∈ (b : Sym2 V)) (same : e a=e b) : a=b := by
    by_contra ne
    exact properEdge a b ne ⟨u,ha,hb⟩ same
  let source (u : V) (t : C) : C :=
    if h : ∃ a : G.edgeSet, u ∈ (a : Sym2 V) ∧ e a=t
    then c (Sym2.Mem.other h.choose_spec.1) else t
  have atEdge {u : V} {a : G.edgeSet} (ha : u ∈ (a : Sym2 V)) :
      source u (e a)=c (Sym2.Mem.other ha) := by
    have existsEdge : ∃ b : G.edgeSet, u ∈ (b : Sym2 V) ∧ e b=e a := ⟨a,ha,rfl⟩
    dsimp only [source]
    rw [dif_pos existsEdge]
    have eq := unique existsEdge.choose_spec.1 ha existsEdge.choose_spec.2
    congr 1
    exact Sym2.congr_right.mp ((Sym2.other_spec _).trans ((congrArg Subtype.val eq).trans
      (Sym2.other_spec _).symm))
  have inside (i : I) := simultaneous (fun x : {v // part v=i} => source x.val)
    (show Fintype.card {v // part v=i} < k.factorial by simpa only [Nat.card_eq_fintype_card] using few i)
  choose σ low using inside
  refine ⟨σ,?_,?_⟩
  · intro u v huv
    rw [closed huv]
    exact (σ (part v)).injective.ne (properVertex u v huv)
  intro u
  let M := univ.filter fun t => σ (part u) (source u t)=t
  let bad := univ.filter fun a : G.edgeSet =>
    u ∈ (a : Sym2 V) ∧ ∃ v ∈ (a : Sym2 V), σ (part v) (c v)=e a
  have inject : (bad : Set G.edgeSet).InjOn e := by
    intro a ha b hb eq
    exact unique (mem_filter.mp ha).2.1 (mem_filter.mp hb).2.1 eq
  have maps : Set.MapsTo e (bad : Set G.edgeSet) (insert (σ (part u) (c u)) M : Finset C) := by
    intro a ha
    obtain ⟨hu,v,hv,agree⟩ := (mem_filter.mp ha).2
    have which : v=u ∨ v=Sym2.Mem.other hu := by
      exact Sym2.mem_iff.mp ((Sym2.other_spec hu).symm ▸ hv)
    rcases which with rfl | rfl
    · exact mem_insert.mpr (Or.inl agree.symm)
    · have adj : G.Adj u (Sym2.Mem.other hu) := by
        apply G.mem_edgeSet.mp
        rw [Sym2.other_spec hu]
        exact a.property
      have samePart := closed adj
      rw [← samePart] at agree
      exact mem_insert.mpr (Or.inr (mem_filter.mpr
        ⟨mem_univ _,(congrArg (σ (part u)) (atEdge hu)).trans agree⟩))
  have small : bad.card ≤ k := by
    have hmap := card_le_card_of_injOn e maps inject
    have atMost := Finset.card_insert_le (σ (part u) (c u)) M
    have strict : M.card < k := low (part u) ⟨u,rfl⟩
    omega
  let reject := {a : Sym2 V | u ∈ a ∧ ∃ ha : a ∈ G.edgeSet, ∃ v ∈ a, σ (part v) (c v)=e ⟨a,ha⟩}
  have asImage : reject = (Subtype.val : G.edgeSet → Sym2 V) '' (bad : Set G.edgeSet) := by
    ext a
    constructor
    · rintro ⟨hu,ha,v,hv,agree⟩
      exact ⟨⟨a,ha⟩,mem_filter.mpr ⟨mem_univ _,hu,v,hv,agree⟩,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨hu,v,hv,agree⟩ := (mem_filter.mp ha).2
      exact ⟨hu,a.property,v,hv,agree⟩
  change reject.ncard ≤ k
  rw [asImage]
  calc
    _ ≤ (bad : Set G.edgeSet).ncard := Set.ncard_image_le
    _ = bad.card := Set.ncard_coe_finset bad
    _ ≤ k := small

/-- On a graph of order less than k!, the same permutation can be used
on every vertex. Matching colours bound the conflicts from neighbours. Only the
vertex's own colour can add a further conflict. -/
theorem bounded_rejects_of_order {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] [DecidableEq C] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : G.edgeSet → C)
    (properEdge : ∀ a b : G.edgeSet, a ≠ b →
      (∃ u, u ∈ (a : Sym2 V) ∧ u ∈ (b : Sym2 V)) → e a ≠ e b)
    (c : V → C) (properVertex : ∀ u v, G.Adj u v → c u ≠ c v)
    {k : ℕ} (few : Fintype.card V < k.factorial) :
    ∃ σ : Perm C, (∀ u v, G.Adj u v → σ (c u) ≠ σ (c v)) ∧ ∀ u,
      {a : Sym2 V | u ∈ a ∧ ∃ ha : a ∈ G.edgeSet, ∃ v ∈ a, σ (c v) = e ⟨a,ha⟩}.ncard ≤ k := by
  classical
  have sizes (i : Unit) : Nat.card { _v : V // ()=i } < k.factorial := by
    cases i
    simpa using few
  obtain ⟨σ,proper,bound⟩ := bounded_rejects_of_parts G e properEdge c properVertex
    (fun _ => ()) (fun _ => rfl) sizes
  exact ⟨σ (),proper,bound⟩

end ColourRelabelling
