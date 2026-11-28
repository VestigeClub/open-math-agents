import Mathlib
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.TotalColouring

/-!
# Total colouring of finite bipartite graphs

Every finite bipartite simple graph of maximum degree Δ admits a total
colouring with Δ + 2 colours. König's edge-colouring theorem gives Δ edge
colours. Two fresh colours distinguish the two vertex classes.

For the edge colouring, pad the adjacency matrix on its diagonal until all
row and column sums equal Δ. Hall's marriage theorem gives a positive
permutation diagonal. Subtract one such diagonal at a time to express the
matrix as a sum of permutation matrices. Orient each edge from the first
class to the second and use a covering permutation as its colour.
-/

open Finset Equiv

namespace BipartiteEdgeColours

private theorem positive_permutation {V : Type*} [Fintype V] [DecidableEq V]
    {d : ℕ} (positive : 0 < d) (m : V → V → ℕ)
    (row : ∀ i, ∑ j, m i j = d) (col : ∀ j, ∑ i, m i j = d) :
    ∃ p : Perm V, ∀ i, 0 < m i (p i) := by
  classical
  let supports (i : V) := univ.filter fun j => 0 < m i j
  have hall (S : Finset V) : S.card ≤ (S.biUnion supports).card := by
    let T := S.biUnion supports
    have whole (i : V) (hi : i∈S) : ∑ j ∈ T, m i j = d := by
      calc
        ∑ j ∈ T, m i j = ∑ j, m i j := by
          apply sum_subset (subset_univ _)
          intro j _ hj
          by_contra! pos
          exact hj (mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨mem_univ _,Nat.pos_of_ne_zero pos⟩⟩)
        _ = _ := row i
    have inside (j : V) : ∑ i ∈ S, m i j ≤ d := by
      rw [← col j]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => Nat.zero_le _
    have bound : S.card * d ≤ T.card * d := calc
      S.card*d = ∑ _i ∈ S, d := by simp
      _ = ∑ i ∈ S, ∑ j ∈ T, m i j := (sum_congr rfl whole).symm
      _ = ∑ j ∈ T, ∑ i ∈ S, m i j := sum_comm
      _ ≤ ∑ _j ∈ T, d := sum_le_sum fun j _ => inside j
      _ = T.card*d := by simp
    exact Nat.le_of_mul_le_mul_right bound positive
  obtain ⟨f,hf,allowed⟩ := (all_card_le_biUnion_card_iff_exists_injective supports).mp hall
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf),fun i => (mem_filter.mp (allowed i)).2⟩

/-- An integral doubly stochastic matrix scaled by d is the sum of exactly
d permutation matrices. The statement includes d = 0 and an empty index set. -/
theorem permutation_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    (d : ℕ) (m : V → V → ℕ) (row : ∀ i, ∑ j, m i j=d) (col : ∀ j, ∑ i, m i j=d) :
    ∃ p : Fin d → Perm V,
      ∀ i j, (∑ k : Fin d, if p k i=j then 1 else 0) = m i j := by
  classical
  induction d generalizing m with
  | zero =>
    refine ⟨Fin.elim0,?_⟩
    intro i j
    have le := single_le_sum (f:=fun t => m i t) (fun t _ => Nat.zero_le _) (mem_univ j)
    rw [row i] at le
    simp [Nat.eq_zero_of_le_zero le]
  | succ d ih =>
    obtain ⟨p,positive⟩ := positive_permutation (Nat.zero_lt_succ d) m row col
    let entry (i j : V) : ℕ := if p i=j then 1 else 0
    let rest (i j : V) := m i j-entry i j
    have add (i j : V) : rest i j + entry i j = m i j := by
      apply Nat.sub_add_cancel
      by_cases same : p i=j
      · subst j
        simp only [entry,if_pos rfl]
        have := positive i
        omega
      · simp [entry,same]
    have oneRow (i : V) : ∑ j, entry i j=1 := by simp [entry]
    have oneCol (j : V) : ∑ i, entry i j=1 := by
      have eq (i : V) : p i=j ↔ i=p.symm j := by
        constructor
        · intro h
          exact p.injective (h.trans (p.apply_symm_apply j).symm)
        · rintro rfl
          exact p.apply_symm_apply _
      simp [entry,eq]
    have rows (i : V) : ∑ j, rest i j=d := by
      have h : (∑ j, rest i j)+(∑ j,entry i j)=d+1 := by
        rw [← sum_add_distrib]
        simpa only [add] using row i
      rw [oneRow] at h
      omega
    have cols (j : V) : ∑ i, rest i j=d := by
      have h : (∑ i,rest i j)+(∑ i,entry i j)=d+1 := by
        rw [← sum_add_distrib]
        simpa only [add] using col j
      rw [oneCol] at h
      omega
    obtain ⟨q,dec⟩ := ih rest rows cols
    let all : Fin (d+1) → Perm V := Fin.cases p q
    refine ⟨all,?_⟩
    intro i j
    rw [Fin.sum_univ_succ]
    simp only [all,Fin.cases_zero,Fin.cases_succ]
    exact (congrArg (fun z : ℕ => entry i j + z) (dec i j)).trans
      ((Nat.add_comm (entry i j) (rest i j)).trans (add i j))

end BipartiteEdgeColours

namespace BipartiteEdgeColours

open Finset Equiv SimpleGraph

/-- The bipartite double cover of any finite simple graph decomposes into
matchings using at most its maximum degree colours. A diagonal entry makes
up each vertex's degree deficit and leaves every off-diagonal edge intact. -/
theorem permutations_cover_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ p : Fin G.maxDegree → Perm V, ∀ u v, G.Adj u v → ∃ k, p k u=v := by
  classical
  let d := G.maxDegree
  let m (i j : V) : ℕ := (if G.Adj i j then 1 else 0) + (if i=j then d-G.degree i else 0)
  have adjSum (i : V) : (∑ j : V, if G.Adj i j then 1 else 0) = G.degree i := by
    rw [← G.card_neighborFinset_eq_degree]
    have neighbors : univ.filter (G.Adj i)=G.neighborFinset i := by ext j; simp
    simp [Finset.sum_boole,neighbors]
  have rows (i : V) : ∑ j, m i j=d := by
    simp only [m,sum_add_distrib,adjSum]
    simp [d,G.degree_le_maxDegree i]
  have symmetric (i j : V) : m i j=m j i := by
    by_cases eq : i=j
    · subst j; rfl
    · simp [m,eq,Ne.symm eq,G.adj_comm i j]
  have cols (j : V) : ∑ i, m i j=d :=
    (sum_congr rfl (fun i _ => symmetric i j)).trans (rows j)
  obtain ⟨p,counts⟩ := permutation_decomposition d m rows cols
  refine ⟨p,?_⟩
  intro u v huv
  by_contra! misses
  have proof := counts u v
  simp [misses,m,huv,G.ne_of_adj huv] at proof

/-- König's line-colouring theorem for finite simple bipartite graphs.
Two edges incident to a vertex receive distinct colours. -/
theorem bipartite_edge_coloring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : G.Coloring (Fin 2)) :
    ∃ e : G.edgeSet → Fin G.maxDegree, ∀ a a' : G.edgeSet, a ≠ a' →
      (∃ v, v ∈ (a : Sym2 V) ∧ v ∈ (a' : Sym2 V)) → e a ≠ e a' := by
  classical
  have two : ∀ x y : Fin 2, x ≠ y → (x=0 ∧ y=1) ∨ (y=0 ∧ x=1) := by decide
  have ordered (a : G.edgeSet) :
      ∃ u v : V, b u=0 ∧ b v=1 ∧ s(u,v)=(a : Sym2 V) := by
    rcases a with ⟨a,ha⟩
    revert ha
    refine Sym2.inductionOn a ?_
    intro u v h
    obtain ⟨hu,hv⟩ | ⟨hv,hu⟩ := two _ _ (b.valid (G.mem_edgeSet.mp h))
    · exact ⟨u,v,hu,hv,rfl⟩
    · exact ⟨v,u,hv,hu,Sym2.eq_swap⟩
  choose L R leftCol rightCol pair using ordered
  obtain ⟨p,hp⟩ := permutations_cover_edges G
  have edgeAdj (a : G.edgeSet) : G.Adj (L a) (R a) := by
    apply G.mem_edgeSet.mp
    rw [pair]
    exact a.property
  choose e correct using fun a => hp (L a) (R a) (edgeAdj a)
  refine ⟨e,?_⟩
  intro a a' ne common same
  obtain ⟨v,ha,ha'⟩ := common
  have endpoint (z : G.edgeSet) (hz : v ∈ (z : Sym2 V)) : v=L z ∨ v=R z :=
    Sym2.mem_iff.mp ((pair z).symm ▸ hz)
  have sides : (L a=L a') ∨ (R a=R a') := by
    rcases endpoint a ha with l | r <;> rcases endpoint a' ha' with l' | r'
    · exact Or.inl (l.symm.trans l')
    · have different : (0 : Fin 2) ≠ 1 := by decide
      exact (different ((leftCol a).symm.trans ((congrArg b (l.symm.trans r')).trans (rightCol a')))).elim
    · have different : (0 : Fin 2) ≠ 1 := by decide
      exact (different ((leftCol a').symm.trans ((congrArg b (l'.symm.trans r)).trans (rightCol a)))).elim
    · exact Or.inr (r.symm.trans r')
  have correspondence : L a=L a' ↔ R a=R a' := by
    rw [← correct a,← correct a',same]
    exact (p (e a')).injective.eq_iff.symm
  obtain ⟨hl,hr⟩ : L a=L a' ∧ R a=R a' :=
    sides.elim (fun h => ⟨h,correspondence.mp h⟩) (fun h => ⟨correspondence.mpr h,h⟩)
  apply ne
  apply Subtype.ext
  rw [← pair a,← pair a',hl,hr]

/-- The total colouring conjecture holds for all finite bipartite simple
graphs. Use the two parts as vertex colours and the matching indices as a
disjoint palette for the edges. -/
theorem bipartite_total_chromatic_number {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (bipartite : G.IsBipartite) :
    G.totalChromaticNumber ≤ G.maxDegree+2 := by
  classical
  obtain ⟨b⟩ := bipartite
  obtain ⟨e,proper⟩ := bipartite_edge_coloring G b
  let d := G.maxDegree
  let vertex (v : V) : Fin (d+2) := ⟨d+(b v).val,by have := (b v).isLt; omega⟩
  let edge (a : G.edgeSet) : Fin (d+2) := ⟨(e a).val,by have := (e a).isLt; dsimp [d]; omega⟩
  apply Nat.sInf_le
  refine ⟨Sum.elim vertex edge,?_,?_,?_⟩
  · intro u v huv eq
    apply b.valid huv
    apply Fin.ext
    exact Nat.add_left_cancel (show d+(b u).val=d+(b v).val from congrArg Fin.val eq)
  · intro a a' ne common eq
    have same : (e a).val=(e a').val := congrArg (fun z : Fin (d+2) => z.val) eq
    exact proper a a' ne common (Fin.ext same)
  · intro v a _ eq
    have hv : d+(b v).val=(e a).val := congrArg Fin.val eq
    have he : (e a).val<d := (e a).isLt
    omega

end BipartiteEdgeColours
