import certificates.«fifteen-cell-pentomino-pair-search»

open Finset OMA.S_oeis_a380455 PrimePolyFactor
namespace HalfGeometry

theorem boundary_cell {P S : Shape} (poly : polyomino P) (sub : S⊆P)
    (ne : S.Nonempty) (strict : S≠P) :
    ∃ a∈S, ∃ b∈P, b∉S ∧ adjacent a b := by
  classical
  obtain ⟨a,ha⟩ := ne
  by_contra blocked
  apply strict
  apply Subset.antisymm sub
  intro v hv
  have inside (q : P) (path : Relation.ReflTransGen
      (fun x y : P => adjacent x.val y.val) (⟨a,sub ha⟩ : P) q) : q.val∈S := by
    induction path with
    | refl => exact ha
    | @tail b c prev edge ih =>
      by_contra outside
      exact blocked ⟨b.val,ih,c.val,c.property,outside,edge⟩
  exact inside ⟨v,hv⟩ (poly.2 _ _)

theorem two_parts {f b : Shape} (tiling : tiles f b) (positive : 0<f.card)
    (area : b.card=2*f.card) :
    ∃ p q : Shape, p≠q ∧ b=p∪q ∧ congruent f p ∧ congruent f q ∧ Disjoint p q := by
  obtain ⟨t⟩:=existsRealTiling tiling
  have count : t.parts.card=2 := by have := t.area; nlinarith
  obtain ⟨p,q,ne,pair⟩:=Finset.card_eq_two.mp count
  have hp : p∈t.parts := pair ▸ mem_insert_self p {q}
  have hq : q∈t.parts := pair ▸ mem_insert_of_mem (mem_singleton_self q)
  refine ⟨p,q,ne,?_,t.same p hp,t.same q hq,t.separate p hp q hq ne⟩
  rw [←t.cover,pair]
  simp

theorem pair_model {f b model : Shape} (tiling : tiles f b) (positive : 0<f.card)
    (area : b.card=2*f.card) (known : congruent f model) :
    ∃ g : Orientation, ∃ offset : Cell,
      congruent b (model ∪ model.image (move g offset)) ∧
      Disjoint model (model.image (move g offset)) := by
  classical
  obtain ⟨p,q,ne,cover,fp,fq,apart⟩:=two_parts tiling positive area
  obtain ⟨h,o,pm⟩:=(congruent_iff _ _).mp (motion_trans (motion_symm fp) known)
  let q' := q.image (move h o)
  have qq' : congruent q q' := (congruent_iff _ _).mpr ⟨h,o,rfl⟩
  have mq' := motion_trans (motion_symm known) (motion_trans fq qq')
  obtain ⟨g,offset,eq⟩:=(congruent_iff _ _).mp mq'
  refine ⟨g,offset,?_,?_⟩
  · apply (congruent_iff _ _).mpr
    refine ⟨h,o,?_⟩
    rw [cover,image_union,←pm,←eq]
  · rw [←eq,pm]
    change Disjoint (p.image (move h o)) (q.image (move h o))
    refine disjoint_left.mpr ?_
    intro c hc hd
    obtain ⟨v,hv,rfl⟩:=mem_image.mp hc
    obtain ⟨u,hu,same⟩:=mem_image.mp hd
    exact disjoint_left.mp apart hv (move_injective h o same ▸ hu)

theorem pair_adjacent_offset {model b : Shape} (poly : polyomino b)
    (positive : model.Nonempty) {g : Orientation} {offset : Cell}
    (board : congruent b (model ∪ model.image (move g offset)))
    (apart : Disjoint model (model.image (move g offset))) :
    ∃ u∈model, ∃ v∈model, ∃ n∈neighbors u, offset=n-turn g v := by
  let second := model.image (move g offset)
  have connected := poly_motion poly board
  have strict : model≠model∪second := by
    intro eq
    obtain ⟨v,hv⟩:=positive
    have inside : move g offset v∈model := eq.symm ▸ mem_union_right model (mem_image_of_mem _ hv)
    exact disjoint_left.mp apart inside (mem_image_of_mem _ hv)
  obtain ⟨u,hu,n,hn,out,edge⟩:=boundary_cell connected subset_union_left positive strict
  have inSecond : n∈second := (mem_union.mp hn).resolve_left out
  obtain ⟨v,hv,rfl⟩:=mem_image.mp inSecond
  refine ⟨u,hu,v,hv,move g offset v,?_,?_⟩
  · have spec (a b : Cell) : adjacent a b ↔ b∈neighbors a := by
      obtain ⟨x,y⟩:=a
      obtain ⟨u,v⟩:=b
      simp [neighbors,adjacent,Prod.ext_iff]
      omega
    exact (spec _ _).mp edge
  · simp [move]

end HalfGeometry
