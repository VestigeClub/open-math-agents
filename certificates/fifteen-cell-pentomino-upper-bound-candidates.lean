import certificates.«prime-polyomino-factor-witnesses-14-17»

/-!
# Restrictions on a counterexample at area fifteen

Four distinct prime factors would require two different pentomino factors.
Each of the twenty boards below is checked against every possible proper
factor model. The proof establishes their individual upper bounds without
assuming that the list exhausts all common pentomino boards.
-/

open Finset OMA.S_oeis_a380455
namespace PrimePolyFactor

def neighbors (p : Cell) : Finset Cell :=
  {(p.1+1,p.2), (p.1-1,p.2), (p.1,p.2+1), (p.1,p.2-1)}

private theorem neighborhood (a b : Cell) : b ∈ neighbors a ↔ adjacent a b := by
  obtain ⟨x,y⟩:=a
  obtain ⟨u,v⟩:=b
  simp [neighbors,adjacent,Prod.ext_iff]
  omega

def animals : ℕ → Finset Shape
  | 0 => {{(0,0)}}
  | k+1 => (animals k).biUnion fun s =>
      s.biUnion fun a => ((neighbors a).filter (fun b => b∉s)).image (fun b => insert b s)

private theorem boundary_cell {P S : Shape} (poly : polyomino P) (sub : S⊆P)
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

private theorem grow_through {P : Shape} (poly : polyomino P) {o : Cell} (start : o∈P)
    (k : ℕ) (enough : k+1≤P.card) :
    ∃ S∈animals k, S.card=k+1 ∧ S.image (fun z => o+z) ⊆ P := by
  induction k with
  | zero =>
    refine ⟨{(0,0)},by simp [animals],by simp,?_⟩
    simpa only [Finset.image_singleton, show ((0,0) : Cell) = 0 from rfl, add_zero, Finset.singleton_subset_iff] using start
  | succ k ih =>
    obtain ⟨S,hs,sz,sub⟩ := ih (by omega)
    let placed := S.image (fun z => o+z)
    have pc : placed.card=S.card := card_image_of_injective _ (fun _ _ h => add_left_cancel h)
    have ne : placed.Nonempty := card_pos.mp (by omega)
    obtain ⟨a,ha,b,hb,outside,edge⟩ := boundary_cell poly sub ne (by
      intro e
      change placed=P at e
      rw [e] at pc
      omega)
    obtain ⟨v,hv,av⟩ := mem_image.mp ha
    let z : Cell := b-o
    have vz : adjacent v z := by
      rw [← av] at edge
      simp [adjacent,z] at edge ⊢
      omega
    have oz : o+z=b := by dsimp [z]; abel_nf
    have fresh : z∉S := by
      intro h
      exact outside (oz ▸ mem_image_of_mem _ h)
    refine ⟨insert z S,?_,?_,?_⟩
    · apply mem_biUnion.mpr
      refine ⟨S,hs,mem_biUnion.mpr ⟨v,hv,?_⟩⟩
      exact mem_image.mpr ⟨z,mem_filter.mpr ⟨(neighborhood _ _).mpr vz,fresh⟩,rfl⟩
    · rw [card_insert_of_notMem fresh,sz]
    · intro c hc
      obtain ⟨j,hj,rfl⟩:=mem_image.mp hc
      rcases mem_insert.mp hj with rfl|rest
      · simpa only [oz] using hb
      · exact sub (mem_image_of_mem _ rest)

theorem rooted_model {P : Shape} (poly : polyomino P) (k : ℕ) (size : P.card=k+1) :
    ∃ A∈animals k, congruent P A := by
  obtain ⟨o,ho⟩ := poly.1
  obtain ⟨A,ha,sz,sub⟩ := grow_through poly ho k size.ge
  have ct : (A.image (fun v => o+v)).card=A.card :=
    card_image_of_injective _ (fun _ _ h => add_left_cancel h)
  have eq : A.image (fun v => o+v)=P :=
    eq_of_subset_of_card_le sub (by omega)
  refine ⟨A,ha,motion_symm ((congruent_iff _ _).mpr ⟨⟨false,false,false⟩,o,?_⟩)⟩
  have same : move ⟨false,false,false⟩ o = fun v => o+v := by
    funext v
    simp [move,turn,sign]
  rw [same]
  exact eq.symm

def extensions (P : Shape) : Finset Shape :=
  P.biUnion fun p => ((neighbors p).filter (fun q => q∉P)).image (fun q => insert q P)

structure Rule where
  child : Shape
  model : Shape
  turnBy : Orientation
  offset : Cell

def goodRule (next : Finset Shape) (r : Rule) : Bool :=
  decide (r.model ∈ next ∧ r.model = r.child.image (move r.turnBy r.offset))

def closedLevel (here next : Finset Shape) (rules : List Rule) : Bool :=
  decide (here.biUnion extensions ⊆ (rules.map Rule.child).toFinset) && rules.all (goodRule next)

theorem level_step {here next : Finset Shape} {rules : List Rule}
    (ok : closedLevel here next rules=true) {r P : Shape} (hr : r∈here) (hP : P∈extensions r) :
    ∃ t∈next, congruent P t := by
  simp only [closedLevel,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨row,hm,e⟩ := List.mem_map.mp (List.mem_toFinset.mp
    (ok.1 (mem_biUnion.mpr ⟨r,hr,hP⟩)))
  have good : row.model ∈ next ∧ row.model=row.child.image (move row.turnBy row.offset) :=
    of_decide_eq_true (List.all_eq_true.mp ok.2 _ hm)
  refine ⟨row.model,good.1,(congruent_iff _ _).mpr ⟨row.turnBy,row.offset,?_⟩⟩
  simpa only [e] using good.2

def level0 : Finset Shape := {{(0,0)}}

def level1 : Finset Shape := {{(0,0),(0,1)}}

def level2 : Finset Shape := {{(0,0),(0,1),(0,2)},
  {(0,0),(0,1),(1,0)}}

def level3 : Finset Shape := {{(0,0),(0,1),(0,2),(0,3)},
  {(0,0),(0,1),(0,2),(1,0)},
  {(0,0),(0,1),(0,2),(1,1)},
  {(0,0),(0,1),(1,0),(1,1)},
  {(0,0),(0,1),(1,1),(1,2)}}

def level4 : Finset Shape := {{(0,0),(0,1),(0,2),(0,3),(0,4)},
  {(0,0),(0,1),(0,2),(0,3),(1,0)},
  {(0,0),(0,1),(0,2),(0,3),(1,1)},
  {(0,0),(0,1),(0,2),(1,0),(1,1)},
  {(0,0),(0,1),(0,2),(1,0),(1,2)},
  {(0,0),(0,1),(0,2),(1,0),(2,0)},
  {(0,0),(0,1),(0,2),(1,1),(2,1)},
  {(0,0),(0,1),(0,2),(1,2),(1,3)},
  {(0,0),(0,1),(1,1),(1,2),(2,1)},
  {(0,0),(0,1),(1,1),(1,2),(2,2)},
  {(0,0),(0,1),(1,1),(2,1),(2,2)},
  {(0,0),(1,-1),(1,0),(1,1),(2,0)}}

def models : ℕ → Finset Shape
  | 0 => level0
  | 1 => level1
  | 2 => level2
  | 3 => level3
  | 4 => level4
  | _ => ∅

private def rules0 : List Rule := [
  ⟨{(-1,0),(0,0)},{(0,0),(0,1)},⟨true,false,false⟩,(0,1)⟩,
  ⟨{(0,-1),(0,0)},{(0,0),(0,1)},⟨false,false,false⟩,(0,1)⟩,
  ⟨{(0,0),(0,1)},{(0,0),(0,1)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(1,0)},{(0,0),(0,1)},⟨true,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
private theorem complete0 : closedLevel level0 level1 rules0=true := by decide +kernel

private def rules1 : List Rule := [
  ⟨{(-1,0),(0,0),(0,1)},{(0,0),(0,1),(1,0)},⟨false,true,false⟩,(0,0)⟩,
  ⟨{(-1,1),(0,0),(0,1)},{(0,0),(0,1),(1,0)},⟨false,true,true⟩,(0,1)⟩,
  ⟨{(0,-1),(0,0),(0,1)},{(0,0),(0,1),(0,2)},⟨false,false,false⟩,(0,1)⟩,
  ⟨{(0,0),(0,1),(0,2)},{(0,0),(0,1),(0,2)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(1,0)},{(0,0),(0,1),(1,0)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(1,1)},{(0,0),(0,1),(1,0)},⟨false,false,true⟩,(0,1)⟩]

set_option maxRecDepth 20000 in
private theorem complete1 : closedLevel level1 level2 rules1=true := by decide +kernel

private def rules2 : List Rule := [
  ⟨{(-1,0),(0,0),(0,1),(0,2)},{(0,0),(0,1),(0,2),(1,0)},⟨false,true,false⟩,(0,0)⟩,
  ⟨{(-1,0),(0,0),(0,1),(1,0)},{(0,0),(0,1),(0,2),(1,1)},⟨true,false,false⟩,(0,1)⟩,
  ⟨{(-1,1),(0,0),(0,1),(0,2)},{(0,0),(0,1),(0,2),(1,1)},⟨false,true,false⟩,(0,0)⟩,
  ⟨{(-1,1),(0,0),(0,1),(1,0)},{(0,0),(0,1),(1,1),(1,2)},⟨true,false,true⟩,(0,1)⟩,
  ⟨{(-1,2),(0,0),(0,1),(0,2)},{(0,0),(0,1),(0,2),(1,0)},⟨false,true,true⟩,(0,2)⟩,
  ⟨{(0,-1),(0,0),(0,1),(0,2)},{(0,0),(0,1),(0,2),(0,3)},⟨false,false,false⟩,(0,1)⟩,
  ⟨{(0,-1),(0,0),(0,1),(1,0)},{(0,0),(0,1),(0,2),(1,1)},⟨false,false,false⟩,(0,1)⟩,
  ⟨{(0,0),(0,1),(0,2),(0,3)},{(0,0),(0,1),(0,2),(0,3)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(0,2),(1,0)},{(0,0),(0,1),(0,2),(1,0)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(0,2),(1,1)},{(0,0),(0,1),(0,2),(1,1)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(0,2),(1,2)},{(0,0),(0,1),(0,2),(1,0)},⟨false,false,true⟩,(0,2)⟩,
  ⟨{(0,0),(0,1),(1,-1),(1,0)},{(0,0),(0,1),(1,1),(1,2)},⟨false,false,true⟩,(0,1)⟩,
  ⟨{(0,0),(0,1),(1,0),(1,1)},{(0,0),(0,1),(1,0),(1,1)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(1,0),(2,0)},{(0,0),(0,1),(0,2),(1,0)},⟨true,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
private theorem complete2 : closedLevel level2 level3 rules2=true := by decide +kernel

private def rules3 : List Rule := [
  ⟨{(-1,0),(0,0),(0,1),(0,2),(0,3)},{(0,0),(0,1),(0,2),(0,3),(1,0)},⟨false,true,false⟩,(0,0)⟩,
  ⟨{(-1,0),(0,0),(0,1),(0,2),(1,0)},{(0,0),(0,1),(0,2),(1,1),(2,1)},⟨true,false,false⟩,(0,1)⟩,
  ⟨{(-1,0),(0,0),(0,1),(0,2),(1,1)},{(0,0),(0,1),(1,1),(1,2),(2,1)},⟨true,false,false⟩,(0,1)⟩,
  ⟨{(-1,0),(0,0),(0,1),(1,0),(1,1)},{(0,0),(0,1),(0,2),(1,0),(1,1)},⟨true,false,true⟩,(0,1)⟩,
  ⟨{(-1,0),(0,0),(0,1),(1,1),(1,2)},{(0,0),(0,1),(1,1),(1,2),(2,2)},⟨false,true,true⟩,(1,2)⟩,
  ⟨{(-1,1),(0,0),(0,1),(0,2),(0,3)},{(0,0),(0,1),(0,2),(0,3),(1,1)},⟨false,true,false⟩,(0,0)⟩,
  ⟨{(-1,1),(0,0),(0,1),(0,2),(1,0)},{(0,0),(0,1),(1,1),(1,2),(2,1)},⟨true,false,true⟩,(0,1)⟩,
  ⟨{(-1,1),(0,0),(0,1),(0,2),(1,1)},{(0,0),(1,-1),(1,0),(1,1),(2,0)},⟨false,false,false⟩,(1,-1)⟩,
  ⟨{(-1,1),(0,0),(0,1),(1,0),(1,1)},{(0,0),(0,1),(0,2),(1,0),(1,1)},⟨true,true,true⟩,(1,1)⟩,
  ⟨{(-1,1),(0,0),(0,1),(1,1),(1,2)},{(0,0),(0,1),(1,1),(1,2),(2,1)},⟨false,true,true⟩,(1,2)⟩,
  ⟨{(-1,2),(0,0),(0,1),(0,2),(0,3)},{(0,0),(0,1),(0,2),(0,3),(1,1)},⟨false,true,true⟩,(0,3)⟩,
  ⟨{(-1,2),(0,0),(0,1),(0,2),(1,0)},{(0,0),(0,1),(1,1),(2,1),(2,2)},⟨true,false,true⟩,(0,1)⟩,
  ⟨{(-1,2),(0,0),(0,1),(0,2),(1,1)},{(0,0),(0,1),(1,1),(1,2),(2,1)},⟨true,true,false⟩,(2,1)⟩,
  ⟨{(-1,3),(0,0),(0,1),(0,2),(0,3)},{(0,0),(0,1),(0,2),(0,3),(1,0)},⟨false,true,true⟩,(0,3)⟩,
  ⟨{(0,-1),(0,0),(0,1),(0,2),(0,3)},{(0,0),(0,1),(0,2),(0,3),(0,4)},⟨false,false,false⟩,(0,1)⟩,
  ⟨{(0,-1),(0,0),(0,1),(0,2),(1,0)},{(0,0),(0,1),(0,2),(0,3),(1,1)},⟨false,false,false⟩,(0,1)⟩,
  ⟨{(0,-1),(0,0),(0,1),(0,2),(1,1)},{(0,0),(0,1),(0,2),(0,3),(1,1)},⟨false,false,true⟩,(0,2)⟩,
  ⟨{(0,-1),(0,0),(0,1),(1,0),(1,1)},{(0,0),(0,1),(0,2),(1,0),(1,1)},⟨false,false,true⟩,(0,1)⟩,
  ⟨{(0,-1),(0,0),(0,1),(1,1),(1,2)},{(0,0),(0,1),(0,2),(1,2),(1,3)},⟨false,false,false⟩,(0,1)⟩,
  ⟨{(0,0),(0,1),(0,2),(0,3),(0,4)},{(0,0),(0,1),(0,2),(0,3),(0,4)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(0,2),(0,3),(1,0)},{(0,0),(0,1),(0,2),(0,3),(1,0)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(0,2),(0,3),(1,1)},{(0,0),(0,1),(0,2),(0,3),(1,1)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(0,2),(0,3),(1,2)},{(0,0),(0,1),(0,2),(0,3),(1,1)},⟨false,false,true⟩,(0,3)⟩,
  ⟨{(0,0),(0,1),(0,2),(0,3),(1,3)},{(0,0),(0,1),(0,2),(0,3),(1,0)},⟨false,false,true⟩,(0,3)⟩,
  ⟨{(0,0),(0,1),(0,2),(1,-1),(1,0)},{(0,0),(0,1),(0,2),(1,2),(1,3)},⟨false,false,true⟩,(0,2)⟩,
  ⟨{(0,0),(0,1),(0,2),(1,0),(1,1)},{(0,0),(0,1),(0,2),(1,0),(1,1)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(0,2),(1,0),(1,2)},{(0,0),(0,1),(0,2),(1,0),(1,2)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(0,2),(1,0),(2,0)},{(0,0),(0,1),(0,2),(1,0),(2,0)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(0,2),(1,1),(1,2)},{(0,0),(0,1),(0,2),(1,0),(1,1)},⟨false,false,true⟩,(0,2)⟩,
  ⟨{(0,0),(0,1),(0,2),(1,1),(2,1)},{(0,0),(0,1),(0,2),(1,1),(2,1)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(1,-1),(1,0),(1,1)},{(0,0),(0,1),(0,2),(1,0),(1,1)},⟨false,true,true⟩,(1,1)⟩,
  ⟨{(0,0),(0,1),(1,0),(1,1),(1,2)},{(0,0),(0,1),(0,2),(1,0),(1,1)},⟨false,true,false⟩,(1,0)⟩,
  ⟨{(0,0),(0,1),(1,0),(1,1),(2,0)},{(0,0),(0,1),(0,2),(1,0),(1,1)},⟨true,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(1,0),(1,1),(2,1)},{(0,0),(0,1),(0,2),(1,0),(1,1)},⟨true,true,false⟩,(1,0)⟩,
  ⟨{(0,0),(0,1),(1,1),(1,2),(1,3)},{(0,0),(0,1),(0,2),(1,2),(1,3)},⟨false,true,true⟩,(1,3)⟩,
  ⟨{(0,0),(0,1),(1,1),(1,2),(2,1)},{(0,0),(0,1),(1,1),(1,2),(2,1)},⟨false,false,false⟩,(0,0)⟩,
  ⟨{(0,0),(0,1),(1,1),(1,2),(2,2)},{(0,0),(0,1),(1,1),(1,2),(2,2)},⟨false,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
private theorem complete3 : closedLevel level3 level4 rules3=true := by decide +kernel

theorem all_steps (k : ℕ) (bound : k<4) {R P : Shape} (r : R∈models k) (p : P∈extensions R) :
    ∃ t∈models (k+1), congruent P t := by
  interval_cases k
  · exact level_step complete0 r p
  · exact level_step complete1 r p
  · exact level_step complete2 r p
  · exact level_step complete3 r p

def inventory : Finset Shape := level0 ∪ level1 ∪ level2 ∪ level3 ∪ level4

theorem levels_in (k : ℕ) (bound : k≤4) : models k ⊆ inventory := by
  interval_cases k <;> simp only [models,inventory,subset_iff,mem_union] <;> tauto

private theorem adjacency_move (g : Orientation) (o a b : Cell) (e : adjacent a b) :
    adjacent (move g o a) (move g o b) := by
  obtain ⟨s,x,y⟩:=g
  cases s <;> cases x <;> cases y <;> simp [adjacent,move,turn,sign] at e ⊢ <;> omega

private theorem moved_injective (g : Orientation) (o : Cell) : Function.Injective (move g o) := by
  intro p q h
  have e : turn g p=turn g q := add_left_cancel (show o+turn g p=o+turn g q from h)
  simpa only [turn_inv] using congrArg (turn (inverse g)) e

private theorem animal_model (k : ℕ) (limit : k≤4) (A : Shape) (ha : A∈animals k) :
    ∃ t∈models k, congruent A t := by
  induction k generalizing A with
  | zero =>
    have e : A={(0,0)} := by simpa [animals] using ha
    subst A
    refine ⟨{(0,0)},by decide,(congruent_iff _ _).mpr ⟨⟨false,false,false⟩,0,?_⟩⟩
    decide +kernel
  | succ k ih =>
    obtain ⟨S,hs,rest⟩ := mem_biUnion.mp ha
    obtain ⟨a,hasa,rest⟩ := mem_biUnion.mp rest
    obtain ⟨b,hb,rfl⟩ := mem_image.mp rest
    obtain ⟨nb,fresh⟩ := mem_filter.mp hb
    obtain ⟨R,hr,geo⟩ := ih (by omega) S hs
    obtain ⟨g,o,eq⟩ := (congruent_iff _ _).mp geo
    let f := move g o
    have inj := moved_injective g o
    have ar : f a ∈ R := eq ▸ mem_image_of_mem _ hasa
    have br : f b ∉ R := by
      rw [eq]
      intro h
      obtain ⟨v,hv,same⟩:=mem_image.mp h
      exact fresh ((inj same) ▸ hv)
    have adj : f b ∈ neighbors (f a) :=
      (neighborhood _ _).mpr (adjacency_move _ _ _ _ ((neighborhood _ _).mp nb))
    have ext : insert (f b) R∈extensions R :=
      mem_biUnion.mpr ⟨f a,ar,mem_image.mpr ⟨f b,mem_filter.mpr ⟨adj,br⟩,rfl⟩⟩
    obtain ⟨model,hm,c⟩ := all_steps k (by omega) hr ext
    exact ⟨model,hm,motion_trans ((congruent_iff _ _).mpr ⟨g,o,by simp [eq,f]⟩) c⟩

theorem representative {s : Shape} (poly : polyomino s) (k : ℕ) (small : k≤4)
    (size : s.card=k+1) : ∃ r∈models k, congruent s r := by
  obtain ⟨a,ha,pa⟩ := rooted_model poly k size
  obtain ⟨r,hr,ar⟩ := animal_model k small a ha
  exact ⟨r,hr,motion_trans pa ar⟩

theorem transport_tiles {f a b : Shape} (h : tiles f a) (moveBoard : congruent a b) :
    tiles f b := by
  classical
  obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp moveBoard
  obtain ⟨parts,hs,cover,classes,disj⟩ := h
  let shift := fun z : Shape => z.image (move g o)
  refine ⟨parts.image shift,hs.image _,?_,?_,?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨t,ht,mem⟩ := mem_biUnion.mp hx
      obtain ⟨s,hs,rfl⟩ := mem_image.mp ht
      obtain ⟨q,hq,rfl⟩ := mem_image.mp mem
      exact mem_image_of_mem _ (cover ▸ mem_biUnion.mpr ⟨s,hs,hq⟩)
    · intro hx
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
      rw [←cover] at hz
      obtain ⟨s,hs,hz⟩ := mem_biUnion.mp hz
      exact mem_biUnion.mpr ⟨shift s,mem_image_of_mem _ hs,mem_image_of_mem _ hz⟩
  · intro t ht
    obtain ⟨s,hs,rfl⟩ := mem_image.mp ht
    exact motion_trans (classes s hs) ((congruent_iff _ _).mpr ⟨g,o,rfl⟩)
  · intro s hs t ht ne
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hs
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ht
    refine disjoint_left.mpr ?_
    intro x hx hy
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
    obtain ⟨v,hv,e⟩ := mem_image.mp hy
    have same : v=u := move_injective g o e
    exact disjoint_left.mp (disj a ha b hb (fun e => ne (congrArg shift e))) hu (same ▸ hv)

theorem represented_card {family catalog : Finset Shape}
    (distinct : ∀ a∈family, ∀ b∈family, congruent a b → a=b)
    (cover : ∀ a∈family, ∃ r∈catalog, congruent a r) : family.card ≤ catalog.card := by
  classical
  choose pick member related using (fun a : family => cover a a.property)
  let f : family → catalog := fun a => ⟨pick a, member a⟩
  have injective : Function.Injective f := by
    intro a b same
    have e : pick a = pick b := congrArg Subtype.val same
    apply Subtype.ext
    have left := related a
    rw [e] at left
    exact distinct a a.property b b.property (motion_trans left (motion_symm (related b)))
  simpa using Fintype.card_le_of_injective f injective

theorem bounds_when_whole {b : Shape} {fs : Finset Shape}
    (factor : ∀ t∈fs, primeShape t ∧ tiles t b)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q)
    (whole : ∃ p∈fs, p.card=b.card) : fs.card≤1 := by
  obtain ⟨p,hp,size⟩ := whole
  have wholeMove := single_tile (factor p hp).2 size
  have all (t : Shape) (ht : t∈fs) : congruent t b := by
    obtain ⟨prime,tiling⟩ := factor t ht
    have divider := transport_tiles tiling (motion_symm wholeMove)
    exact single_tile tiling (((factor p hp).1.2.2 t prime.1 prime.2.1 divider).trans size)
  apply card_le_one.mpr
  intro t ht u hu
  exact different t ht u hu (motion_trans (all t ht) (motion_symm (all u hu)))

private lemma proper_divisor_fifteen (v : ℕ) (lo : 1<v) (hi : v≤15) (ne : v≠15)
    (dvd : v∣15) : v=3 ∨ v=5 := by
  interval_cases v <;> omega

theorem two_pentominoes_of_four {b : Shape} {fs : Finset Shape}
    (size : b.card=15) (large : 4≤fs.card)
    (factor : ∀ t∈fs, primeShape t ∧ tiles t b)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q) :
    ∃ p∈fs, ∃ q∈fs, p.card=5 ∧ q.card=5 ∧ ¬congruent p q := by
  classical
  have proper : ¬ ∃ p∈fs, p.card=b.card :=
    fun h => (by omega : ¬fs.card≤1) (bounds_when_whole factor different h)
  have options (t : Shape) (ht : t∈fs) : t.card=3 ∨ t.card=5 := by
    have dvd : t.card∣15 := size ▸ tile_area (factor t ht).2
    have least := (factor t ht).1.2.1
    have le := Nat.le_of_dvd (by decide : 0<15) dvd
    have ne : t.card≠15 := fun e => proper ⟨t,ht,e.trans size.symm⟩
    exact proper_divisor_fifteen _ least le ne dvd
  let small := fs.filter (fun t => t.card=3)
  let big := fs.filter (fun t => t.card=5)
  have smallBound : small.card≤2 := by
    have two : (models 2).card=2 := by decide +kernel
    rw [←two]
    apply represented_card
    · intro p hp q hq
      exact different p (mem_filter.mp hp).1 q (mem_filter.mp hq).1
    · intro t ht
      exact representative (factor t (mem_filter.mp ht).1).1.1 2 (by decide) (mem_filter.mp ht).2
  have unionEq : small ∪ big = fs := by
    ext t
    simp only [small,big,mem_union,mem_filter]
    constructor
    · rintro (h|h) <;> exact h.1
    · intro ht
      rcases options t ht with a|a
      · exact Or.inl ⟨ht,a⟩
      · exact Or.inr ⟨ht,a⟩
  have total := card_union_le small big
  rw [unionEq] at total
  have enough : 1<big.card := by omega
  obtain ⟨p,hp,q,hq,ne⟩ := one_lt_card.mp enough
  exact ⟨p,(mem_filter.mp hp).1,q,(mem_filter.mp hq).1,(mem_filter.mp hp).2,(mem_filter.mp hq).2,
    fun eq => ne (different p (mem_filter.mp hp).1 q (mem_filter.mp hq).1 eq)⟩

end PrimePolyFactor


open Finset OMA.S_oeis_a380455
namespace PrimePolyFactor

def directions : List Orientation :=
  [⟨false,false,false⟩,⟨false,false,true⟩,⟨false,true,false⟩,⟨false,true,true⟩,
   ⟨true,false,false⟩,⟨true,false,true⟩,⟨true,true,false⟩,⟨true,true,true⟩]

theorem direction_mem (g : Orientation) : g∈directions := by
  obtain ⟨a,b,c⟩ := g
  cases a <;> cases b <;> cases c <;> decide

def through (model : List Cell) (p : Cell) : List Shape :=
  directions.flatMap fun g =>
    model.map fun q => model.toFinset.image (move g (p-turn g q))

theorem through_complete {m : List Cell} {s : Shape} {p : Cell}
    (shape : congruent m.toFinset s) (inTile : p∈s) : s∈through m p := by
  obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp shape
  obtain ⟨q,hq,rfl⟩ := mem_image.mp inTile
  apply List.mem_flatMap.mpr
  refine ⟨g,direction_mem _,List.mem_map.mpr ⟨q,List.mem_toFinset.mp hq,?_⟩⟩
  simp [move]

def occupied : List Cell → Shape → Option Cell
  | [],_ => none
  | p::rest,b => if p∈b then some p else occupied rest b

theorem occupied_mem {p : Cell} {b : Shape} (l : List Cell) (h : occupied l b=some p) : p∈b := by
  induction l with
  | nil => simp [occupied] at h
  | cons q rest ih =>
    by_cases inB : q∈b
    · simp [occupied,inB] at h
      exact h ▸ inB
    · exact ih (by simpa [occupied,inB] using h)

def fits : ℕ → List Cell → List Cell → Shape → Bool
  | 0,_,_,b => decide (b=∅)
  | k+1,m,pool,b =>
    match occupied pool b with
    | none => true
    | some p => (through m p).any fun s => decide (s⊆b) && fits k m pool (b\s)

theorem fits_complete (k : ℕ) (m pool : List Cell) {b : Shape} {parts : Finset Shape}
    (cover : parts.biUnion id=b) (types : ∀ s∈parts, congruent m.toFinset s)
    (apart : ∀ p∈parts, ∀ q∈parts, p≠q → Disjoint p q)
    (bound : parts.card≤k) : fits k m pool b=true := by
  induction k generalizing b parts with
  | zero =>
    have empty := card_eq_zero.mp (by omega : parts.card=0)
    simpa [fits,empty] using cover.symm
  | succ k ih =>
    cases pick : occupied pool b with
    | none => simp [fits,pick]
    | some v =>
      simp only [fits,pick,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
      have inB := occupied_mem pool pick
      rw [←cover] at inB
      obtain ⟨p,hp,hit⟩ := mem_biUnion.mp inB
      have sub : p⊆b := by
        rw [←cover]
        exact fun x hx => mem_biUnion.mpr ⟨p,hp,hx⟩
      refine ⟨p,through_complete (types p hp) hit,sub,ih (parts:=parts.erase p) ?_
        (fun s hs => types s (mem_of_mem_erase hs))
        (fun s hs t ht ne => apart s (mem_of_mem_erase hs) t (mem_of_mem_erase ht) ne) ?_⟩
      · ext i
        constructor
        · intro h
          obtain ⟨q,hq,iq⟩:=mem_biUnion.mp h
          obtain ⟨ne,inAll⟩:=mem_erase.mp hq
          exact mem_sdiff.mpr ⟨cover ▸ mem_biUnion.mpr ⟨q,inAll,iq⟩,
            fun inside => disjoint_left.mp (apart q inAll p hp ne) iq inside⟩
        · intro h
          obtain ⟨inside,outside⟩:=mem_sdiff.mp h
          rw [←cover] at inside
          obtain ⟨q,hq,iq⟩:=mem_biUnion.mp inside
          exact mem_biUnion.mpr ⟨q,mem_erase.mpr ⟨fun e => outside (e ▸ iq),hq⟩,iq⟩
      · rw [card_erase_of_mem hp]
        omega

theorem tile_detected {t : Shape} {m pool : List Cell} (change : congruent t m.toFinset)
    (h : tiles t pool.toFinset) (pos : 0<t.card) :
    fits pool.toFinset.card m pool pool.toFinset=true := by
  obtain ⟨parts,_,cover,kind,apart⟩:=h
  apply fits_complete _ _ _ cover (fun q hq => motion_trans (motion_symm change) (kind q hq)) apart
  have total : pool.toFinset.card = ∑ s∈parts,s.card := by
    rw [←cover,card_biUnion (by intro p hp q hq ne; exact apart p hp q hq ne)]
    rfl
  rw [total]
  calc
    _ = ∑ _s∈parts,1 := by simp
    _ ≤ _ := sum_le_sum fun s hs => by rw [←motion_card (kind s hs)]; omega

def triPentaModels : List (List Cell) := [[(0,0),(0,1),(0,2)],
  [(0,0),(0,1),(1,0)],
  [(0,0),(0,1),(0,2),(0,3),(0,4)],
  [(0,0),(0,1),(0,2),(0,3),(1,0)],
  [(0,0),(0,1),(0,2),(0,3),(1,1)],
  [(0,0),(0,1),(0,2),(1,0),(1,1)],
  [(0,0),(0,1),(0,2),(1,0),(1,2)],
  [(0,0),(0,1),(0,2),(1,0),(2,0)],
  [(0,0),(0,1),(0,2),(1,1),(2,1)],
  [(0,0),(0,1),(0,2),(1,2),(1,3)],
  [(0,0),(0,1),(1,1),(1,2),(2,1)],
  [(0,0),(0,1),(1,1),(1,2),(2,2)],
  [(0,0),(0,1),(1,1),(2,1),(2,2)],
  [(0,0),(1,-1),(1,0),(1,1),(2,0)]]

theorem modelLists : models 2 ∪ models 4 = (triPentaModels.map List.toFinset).toFinset := by
  decide +kernel

def detected (b : List Cell) : Finset Shape :=
  ((triPentaModels.filter (fun m => fits b.toFinset.card m b b.toFinset)).map List.toFinset).toFinset

theorem board_upper (pool : List Cell) (area : pool.toFinset.card=15) (cap : (detected pool).card≤3)
    {fs : Finset Shape} (factor : ∀ t∈fs, primeShape t ∧ tiles t pool.toFinset)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q) : fs.card≤3 := by
  by_cases whole : ∃ p∈fs, p.card=pool.toFinset.card
  · exact (bounds_when_whole factor different whole).trans (by decide)
  refine (represented_card different ?_).trans cap
  intro t ht
  obtain ⟨prime,tiling⟩ := factor t ht
  have dvd : t.card∣15 := area ▸ tile_area tiling
  have le := Nat.le_of_dvd (by decide : 0<15) dvd
  have least := prime.2.1
  have ne : t.card≠15 := fun e => whole ⟨t,ht,e.trans area.symm⟩
  have options (v : ℕ) (h : v∣15) (lo : 1<v) (hi : v≤15) (ex : v≠15) :
      v=3 ∨ v=5 := by interval_cases v <;> omega
  obtain ⟨s,hs,rel⟩ : ∃ s∈models 2 ∪ models 4, congruent t s := by
    rcases options _ dvd least le ne with three|five
    · obtain ⟨s,hs,r⟩:=representative prime.1 2 (by decide) three
      exact ⟨s,mem_union_left _ hs,r⟩
    · obtain ⟨s,hs,r⟩:=representative prime.1 4 (by decide) five
      exact ⟨s,mem_union_right _ hs,r⟩
  rw [modelLists] at hs
  obtain ⟨m,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hs)
  refine ⟨m.toFinset,List.mem_toFinset.mpr (List.mem_map.mpr ⟨m,?_,rfl⟩),rel⟩
  exact List.mem_filter.mpr ⟨hm,tile_detected rel tiling (by omega)⟩

end PrimePolyFactor

open Finset OMA.S_oeis_a380455
namespace PrimePolyFactor

def sharedExamples : List (List Cell) :=
  [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],
   [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5)],
   [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],
   [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(2,5),(2,6)],
   [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(3,2),(4,2)],
   [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5),(2,6),(2,7)],
   [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],
   [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3),(4,4)],
   [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],
   [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2),(4,1)],
   [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3),(4,4)],
   [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],
   [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],
   [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(4,1)],
   [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3),(3,4),(3,5),(4,5)],
   [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4),(4,5),(4,6)],
   [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],
   [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],
   [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],
   [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3),(3,4),(4,2)]]

def boundedBoard (b : List Cell) : Bool :=
  decide (b.toFinset.card=15 ∧ (detected b).card≤3)

set_option maxRecDepth 20000 in
private theorem limited0 : boundedBoard ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited1 : boundedBoard ([(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited2 : boundedBoard ([(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited3 : boundedBoard ([(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(2,5),(2,6)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited4 : boundedBoard ([(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(3,2),(4,2)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited5 : boundedBoard ([(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5),(2,6),(2,7)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited6 : boundedBoard ([(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited7 : boundedBoard ([(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3),(4,4)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited8 : boundedBoard ([(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited9 : boundedBoard ([(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2),(4,1)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited10 : boundedBoard ([(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3),(4,4)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited11 : boundedBoard ([(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited12 : boundedBoard ([(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited13 : boundedBoard ([(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(4,1)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited14 : boundedBoard ([(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3),(3,4),(3,5),(4,5)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited15 : boundedBoard ([(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4),(4,5),(4,6)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited16 : boundedBoard ([(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited17 : boundedBoard ([(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited18 : boundedBoard ([(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)] : List Cell) = true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem limited19 : boundedBoard ([(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3),(3,4),(4,2)] : List Cell) = true := by decide +kernel

private theorem allLimited : sharedExamples.all boundedBoard = true := by
  simp only [sharedExamples,List.all_cons,limited0,limited1,limited2,limited3,limited4,limited5,limited6,limited7,limited8,limited9,limited10,limited11,limited12,limited13,limited14,limited15,limited16,limited17,limited18,limited19,Bool.true_and,List.all_nil]

theorem upper_on_twenty {b : Shape} {pool : List Cell} (inList : pool∈sharedExamples)
    (matchBoard : congruent b pool.toFinset) {fs : Finset Shape}
    (factor : ∀ t∈fs, primeShape t ∧ tiles t b)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q) : fs.card≤3 := by
  have good : pool.toFinset.card=15 ∧ (detected pool).card≤3 :=
    of_decide_eq_true (List.all_eq_true.mp allLimited pool inList)
  exact board_upper pool good.1 good.2
    (fun t ht => ⟨(factor t ht).1,transport_tiles (factor t ht).2 matchBoard⟩) different

end PrimePolyFactor

open OMA.S_oeis_a380455
namespace PrimePolyFactor

theorem fifteen_restriction {b : Shape} {fs : Finset Shape} (area : b.card=15)
    (large : 4≤fs.card) (factor : ∀ t∈fs, primeShape t ∧ tiles t b)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q) :
    (∃ p∈fs, ∃ q∈fs, p.card=5 ∧ q.card=5 ∧ ¬congruent p q) ∧
    ∀ pool∈sharedExamples, ¬congruent b pool.toFinset := by
  refine ⟨two_pentominoes_of_four area large factor different,?_⟩
  intro pool found eq
  have cap := upper_on_twenty found eq factor different
  omega

end PrimePolyFactor
