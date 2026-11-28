import OMAStatements.S_oeis_a144876
import Mathlib

/-!
# Three exact values for square dissections into distinct polyominoes

For Charlie Neder's conjecture in OEIS A144876, the maxima for sides 15, 16
and 17 are respectively 43, 48 and 54. Small shapes are classified by
growing one edge-adjacent cell at a time, up to rotations, reflections and
translations. At threshold six their combined area deficit is 37. Each
displayed dissection is checked against the upstream definition.
-/

open Finset OMA.S_oeis_a144876
namespace DistinctSquare

structure Orientation where
  swap : Bool
  flipX : Bool
  flipY : Bool
deriving DecidableEq, Fintype

def sign (b : Bool) : ℤ := if b then -1 else 1

def turn (g : Orientation) (p : Cell) : Cell :=
  let q := if g.swap then (p.2,p.1) else p
  (sign g.flipX * q.1,sign g.flipY * q.2)

def move (g : Orientation) (o p : Cell) : Cell := o + turn g p

private theorem sign_ok (b : Bool) : sign b=1 ∨ sign b = -1 := by cases b <;> decide

private theorem sign_exists {x : ℤ} (h : x=1 ∨ x= -1) : ∃ b, x=sign b := by
  rcases h with rfl|rfl
  · exact ⟨false,rfl⟩
  · exact ⟨true,rfl⟩

theorem congruent_iff (A B : Shape) :
    congruent A B ↔ ∃ (g : Orientation) (o : Cell), B=A.image (move g o) := by
  constructor
  · rintro ⟨sw,sx,sy,o,hx,hy,rfl⟩
    obtain ⟨a,rfl⟩ := sign_exists hx
    obtain ⟨b,rfl⟩ := sign_exists hy
    exact ⟨⟨sw,a,b⟩,o,rfl⟩
  · rintro ⟨⟨sw,a,b⟩,o,rfl⟩
    exact ⟨sw,sign a,sign b,o,sign_ok a,sign_ok b,rfl⟩

def inverse (g : Orientation) : Orientation :=
  if g.swap then ⟨true,g.flipY,g.flipX⟩ else g

def compose (g h : Orientation) : Orientation :=
  ⟨g.swap ^^ h.swap,(if h.swap then g.flipY else g.flipX) ^^ h.flipX,
    (if h.swap then g.flipX else g.flipY) ^^ h.flipY⟩

theorem turn_inv (g : Orientation) (p : Cell) : turn (inverse g) (turn g p)=p := by
  obtain ⟨s,a,b⟩ := g
  cases s <;> cases a <;> cases b <;> simp [turn,inverse,sign]

theorem turn_comp (g h : Orientation) (p : Cell) : turn (compose g h) p=turn h (turn g p) := by
  obtain ⟨s,a,b⟩ := g
  obtain ⟨t,c,d⟩ := h
  cases s <;> cases t <;> cases a <;> cases b <;> cases c <;> cases d <;> simp [turn,compose,sign]

theorem turn_add (g : Orientation) (p q : Cell) : turn g (p+q)=turn g p+turn g q := by
  obtain ⟨s,a,b⟩:=g
  cases s <;> ext <;> simp [turn,mul_add]

theorem motion_card {A B : Shape} (h : congruent A B) : A.card=B.card := by
  obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp h
  symm
  apply card_image_of_injective
  intro p q eq
  have e : turn g p = turn g q := add_left_cancel (show o+turn g p=o+turn g q from eq)
  simpa only [turn_inv] using congrArg (turn (inverse g)) e

theorem motion_symm {A B : Shape} (h : congruent A B) : congruent B A := by
  obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp h
  apply (congruent_iff _ _).mpr
  refine ⟨inverse g,-turn (inverse g) o,?_⟩
  rw [image_image]
  have e : move (inverse g) (-turn (inverse g) o) ∘ move g o = id := by
    funext p
    simp [move,turn_add,turn_inv]
  simp only [e,image_id]

theorem motion_trans {A B C : Shape} (h : congruent A B) (k : congruent B C) : congruent A C := by
  obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp h
  obtain ⟨f,p,rfl⟩ := (congruent_iff _ _).mp k
  apply (congruent_iff _ _).mpr
  refine ⟨compose g f,p+turn f o,?_⟩
  rw [image_image]
  apply Finset.image_congr
  intro v hv
  simp [move,turn_add,turn_comp,add_assoc]

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

theorem inventory_deficit : (∑ r ∈ inventory, (6-r.card))=37 := by decide +kernel

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

theorem has_small_model {P : Shape} (poly : polyomino P) (small : P.card≤5) :
    ∃ r∈inventory, congruent P r := by
  have pos := Finset.card_pos.mpr poly.1
  let k := P.card-1
  have size : P.card=k+1 := by dsimp [k]; omega
  obtain ⟨a,ha,pa⟩ := rooted_model poly k size
  obtain ⟨r,hr,ar⟩ := animal_model k (by omega) a ha
  exact ⟨r,levels_in k (by omega) hr,motion_trans pa ar⟩

theorem catalogue_bound (t : ℕ) (catalogue pieces : Finset Shape)
    (distinct : distinctPolyominoes pieces)
    (cover : ∀ a∈pieces, a.card<t → ∃ r∈catalogue, congruent a r) :
    t*pieces.card ≤ (∑ a∈pieces,a.card) + ∑ r∈catalogue,(t-r.card) := by
  classical
  let small := pieces.filter (fun a => a.card < t)
  let available (a : Shape) := ∃ r∈catalogue, congruent a r
  let pick (a : Shape) := if h : available a then h.choose else ∅
  have selected {a : Shape} (ha : a∈small) : pick a ∈ catalogue ∧ congruent a (pick a) := by
    have h : available a := cover _ (mem_filter.mp ha).1 (mem_filter.mp ha).2
    simpa only [pick,dif_pos h] using h.choose_spec
  have injective : Set.InjOn pick ↑small := by
    intro a ha b hb e
    have left := (selected ha).2
    rw [e] at left
    exact distinct.2 a (mem_filter.mp ha).1 b (mem_filter.mp hb).1
      (motion_trans left (motion_symm (selected hb).2))
  have bound : (∑ a∈small,(t-a.card)) ≤ ∑ r∈catalogue,(t-r.card) := by
    calc
      _ = ∑ r ∈ small.image pick,(t-r.card) := by
        rw [sum_image injective]
        exact sum_congr rfl (fun a ha => by rw [motion_card (selected ha).2])
      _ ≤ ∑ r ∈ catalogue,(t-r.card) := by
        apply sum_le_sum_of_subset_of_nonneg _ (by intros; omega)
        intro r hr
        obtain ⟨a,ha,rfl⟩:=mem_image.mp hr
        exact (selected ha).1
  have unused : (∑ a∈pieces,(t-a.card))=(∑ a∈small,(t-a.card)) := by
    dsimp [small]
    rw [sum_filter]
    apply sum_congr rfl
    intro a ha
    split <;> omega
  have estimate : (∑ _a∈pieces, t) ≤ ∑ a∈pieces,(a.card+(t-a.card)) :=
    sum_le_sum (fun a ha => by omega)
  have cost : (∑ _a∈pieces,t) = t*pieces.card := by simp [Nat.mul_comm]
  rw [cost,sum_add_distrib,unused] at estimate
  exact estimate.trans (Nat.add_le_add_left bound _)

theorem area_bound (pieces : Finset Shape) (distinct : distinctPolyominoes pieces) :
    6*pieces.card ≤ (∑ a∈pieces,a.card)+37 := by
  have h := catalogue_bound 6 inventory pieces distinct (fun a ha small =>
    has_small_model (distinct.1 a ha) (by omega))
  simpa only [inventory_deficit] using h

def pairWeight (p q : Cell) : ℕ :=
  let a := (p.1-q.1).natAbs
  let b := (p.2-q.2).natAbs
  64 ^ (5*max a b + min a b)

def signature (s : Shape) : ℕ :=
  ∑ p ∈ s, (∑ q ∈ s, pairWeight p q)^2

private theorem sign_delta (b : Bool) (x y : ℤ) :
    (sign b*x-sign b*y).natAbs=(x-y).natAbs := by
  rw [← mul_sub,Int.natAbs_mul]
  cases b <;> simp [sign]

private theorem weight_move (g : Orientation) (o p q : Cell) :
    pairWeight (move g o p) (move g o q)=pairWeight p q := by
  obtain ⟨s,x,y⟩:=g
  cases s <;> simp [pairWeight,move,turn,sign_delta,max_comm,min_comm]

theorem signature_invariant {A B : Shape} (eq : congruent A B) : signature A=signature B := by
  obtain ⟨g,o,rfl⟩ := (congruent_iff A B).mp eq
  have inj : Function.Injective (move g o) := by
    intro p q h
    have e : turn g p=turn g q := add_left_cancel (show o+turn g p=o+turn g q from h)
    simpa only [turn_inv] using congrArg (turn (inverse g)) e
  unfold signature
  rw [sum_image inj.injOn]
  apply sum_congr rfl
  intro p hp
  rw [sum_image inj.injOn]
  simp only [weight_move]

private theorem reverse_adj {a b : Cell} (h : adjacent a b) : adjacent b a := by
  rcases h with ⟨e,f|f⟩|⟨e,f|f⟩
  · exact Or.inl ⟨e.symm, Or.inr f⟩
  · exact Or.inl ⟨e.symm, Or.inl f⟩
  · exact Or.inr ⟨e.symm, Or.inr f⟩
  · exact Or.inr ⟨e.symm, Or.inl f⟩

private theorem add_cell {s : Shape} (h : polyomino s) (p q : Cell) (mem : q∈s)
    (edge : adjacent p q) : polyomino (insert p s) := by
  let lift (z : s) : ↥(insert p s) := ⟨z.val,mem_insert_of_mem z.property⟩
  let R (a b : ↥(insert p s)) := adjacent a.val b.val
  have within (a b : s) : Relation.ReflTransGen R (lift a) (lift b) :=
    Relation.ReflTransGen.lift lift (fun _ _ e => e) a b (h.2 a b)
  have both (a : ↥(insert p s)) :
      Relation.ReflTransGen R a (lift ⟨q,mem⟩) ∧ Relation.ReflTransGen R (lift ⟨q,mem⟩) a := by
    obtain ⟨v,hv⟩:=a
    rcases mem_insert.mp hv with rfl|hv
    · exact ⟨.single edge,.single (reverse_adj edge)⟩
    · exact ⟨within ⟨v,hv⟩ _,within _ ⟨v,hv⟩⟩
  exact ⟨insert_nonempty _ _,fun a b => (both a).1.trans (both b).2⟩

def neighborFlag (a b : Cell) : Bool :=
  decide ((a.1=b.1 ∧ (a.2+1=b.2 ∨ b.2+1=a.2)) ∨
    (a.2=b.2 ∧ (a.1+1=b.1 ∨ b.1+1=a.1)))

private theorem neighborFlag_spec (p q : Cell) : neighborFlag p q=true ↔ adjacent p q :=
  decide_eq_true_iff

def building : List Cell → Bool
  | [] => false
  | [_] => true
  | p::q::rest => building (q::rest) && (q::rest).any (neighborFlag p)

theorem poly_of_building : ∀ l : List Cell, building l=true → polyomino l.toFinset
  | [],h => by simp [building] at h
  | [p],_ => by
    refine ⟨by simp,?_⟩
    rintro ⟨a,ha⟩ ⟨b,hb⟩
    simp at ha hb
    subst a
    subst b
    rfl
  | p::q::rest,h => by
    have hb : building (q::rest)=true ∧ (q::rest).any (neighborFlag p)=true := by
      simpa only [building,Bool.and_eq_true] using h
    obtain ⟨v,hv,edge⟩ := List.any_eq_true.mp hb.2
    simpa only [List.toFinset_cons] using add_cell (poly_of_building _ hb.1) p v (List.mem_toFinset.mpr hv) ((neighborFlag_spec _ _).mp edge)

def regions (data : List (List Cell)) : Finset Shape := (data.map List.toFinset).toFinset

theorem distinct_from_data (data : List (List Cell)) (ok : data.all building=true)
    (unique : ((regions data).image signature).card=(regions data).card) :
    distinctPolyominoes (regions data) := by
  refine ⟨?_,fun a ha b hb eq => card_image_iff.mp unique ha hb (signature_invariant eq)⟩
  intro a ha
  obtain ⟨cells,hc,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact poly_of_building _ (List.all_eq_true.mp ok _ hc)

private theorem disjoint_cells {data : List (List Cell)} (pair : data.Pairwise List.Disjoint)
    {u v : List Cell} (hu : u∈data) (hv : v∈data) (ne : u≠v) : u.Disjoint v := by
  induction data with
  | nil => simp at hu
  | cons a rest ih =>
    obtain ⟨head,tail⟩:=List.pairwise_cons.mp pair
    rcases List.mem_cons.mp hu with e|hu <;> rcases List.mem_cons.mp hv with f|hv
    · exact False.elim (ne (e.trans f.symm))
    · exact e ▸ head v hv
    · exact f ▸ (head u hu).symm
    · exact ih tail hu hv

def flatCheck (n : ℕ) (data : List (List Cell)) : Bool :=
  decide (data.flatten.Nodup ∧ data.flatten.toFinset=square n)

theorem dissection_from_flat {n : ℕ} {data : List (List Cell)} (check : flatCheck n data=true) :
    dissects n (regions data) := by
  have hh : data.flatten.Nodup ∧ data.flatten.toFinset=square n := of_decide_eq_true check
  have union : (regions data).biUnion id=data.flatten.toFinset := by
    ext p
    simp [regions,List.mem_flatten]
  refine ⟨union.trans hh.2,?_⟩
  intro a ha b hb ne
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
  have sep := disjoint_cells (List.nodup_flatten.mp hh.1).2 hu hv
    (fun e => ne (congrArg List.toFinset e))
  apply Finset.disjoint_left.mpr
  intro c hc hd
  exact List.disjoint_left.mp sep (List.mem_toFinset.mp hc) (List.mem_toFinset.mp hd)

def boardFifteen : List (List Cell) := [
  [(5,3),(4,4),(4,2),(4,3),(3,3)],
  [(6,5),(5,4),(5,5),(4,5),(3,5)],
  [(2,2),(3,4),(2,3),(2,4),(1,4)],
  [(2,5),(1,5),(0,5),(0,4),(0,3)],
  [(1,3),(1,2),(0,2),(0,1),(0,0)],
  [(3,2),(3,1),(2,1),(1,1),(1,0)],
  [(6,0),(5,0),(4,0),(3,0),(2,0)],
  [(6,2),(6,1),(5,2),(5,1),(4,1)],
  [(9,1),(9,0),(8,0),(7,1),(7,0)],
  [(8,1),(8,2),(7,2),(7,3),(6,3)],
  [(9,2),(9,3),(9,4),(9,5),(8,5)],
  [(8,3),(8,4),(7,5),(7,4),(6,4)],
  [(13,10),(13,9),(12,10),(12,9)],
  [(13,6),(12,6),(11,6),(10,6)],
  [(11,9),(11,8),(11,7)],
  [(10,8),(10,7)],
  [(14,9),(14,7),(14,8),(13,8)],
  [(14,6)],
  [(13,7),(12,8),(12,7)],
  [(11,11),(11,10),(10,10),(10,9)],
  [(13,11),(12,11),(12,12),(11,12),(10,12),(10,11)],
  [(14,10),(14,11),(14,12),(13,12)],
  [(11,2),(11,1),(10,2),(11,0),(10,1),(10,0)],
  [(14,2),(14,1),(14,0),(13,1),(13,0),(12,0)],
  [(12,1),(12,2),(12,4),(12,3),(11,4),(11,3)],
  [(13,5),(12,5),(11,5),(10,5),(10,4),(10,3)],
  [(14,5),(14,4),(14,3),(13,4),(13,3),(13,2)],
  [(4,6),(3,6),(2,6),(1,6),(0,7),(0,6)],
  [(9,11),(9,10),(9,9),(9,8),(9,7),(9,6)],
  [(9,14),(9,13),(9,12),(8,12),(7,12),(7,11)],
  [(8,14),(8,13),(7,13),(6,12),(6,13),(5,13)],
  [(7,14),(6,14),(5,14),(4,13),(4,14),(3,14)],
  [(8,11),(8,9),(8,10),(7,9),(7,10),(6,10)],
  [(7,8),(8,8),(8,7),(8,6),(7,6),(6,6)],
  [(7,7),(6,7),(5,6),(5,7),(4,8),(4,7)],
  [(6,8),(6,9),(5,8),(5,9),(4,10),(4,9)],
  [(6,11),(5,10),(5,11),(5,12),(4,12),(3,12)],
  [(4,11),(3,11),(3,10),(3,9),(3,8),(2,8)],
  [(3,7),(2,7),(1,7),(1,8),(0,9),(0,8)],
  [(2,9),(2,10),(1,11),(1,9),(1,10),(0,10)],
  [(1,14),(0,14),(1,12),(0,13),(0,12),(0,11)],
  [(2,11),(3,13),(2,14),(2,12),(2,13),(1,13)],
  [(14,14),(14,13),(13,14),(13,13),(12,14),(12,13),(11,14),(11,13),(10,14),(10,13)]]

def tilingFifteen := regions boardFifteen

set_option maxRecDepth 20000 in
private theorem build15 : boardFifteen.all building=true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem count15 : tilingFifteen.card=43 := by decide +kernel

set_option maxRecDepth 20000 in
private theorem signatures15 : (tilingFifteen.image signature).card=43 := by decide +kernel

set_option maxRecDepth 20000 in
private theorem board15 : flatCheck 15 boardFifteen=true := by decide +kernel

theorem lower_15 :
    ∃ tiles : Finset Shape, tiles.card=43 ∧ distinctPolyominoes tiles ∧ dissects 15 tiles :=
  ⟨tilingFifteen,count15,distinct_from_data _ build15 (signatures15.trans count15.symm),
    dissection_from_flat board15⟩

def boardSixteen : List (List Cell) := [
  [(4,2),(3,3),(3,1),(3,2),(2,2)],
  [(1,3),(0,3),(0,2),(0,1),(0,0)],
  [(2,1),(1,2),(2,0),(1,1),(1,0)],
  [(6,0),(5,0),(4,1),(4,0),(3,0)],
  [(2,3),(2,4),(1,4),(0,5),(0,4)],
  [(5,5),(4,5),(3,5),(2,5),(1,5)],
  [(5,2),(5,3),(4,3),(4,4),(3,4)],
  [(7,2),(6,3),(6,2),(6,1),(5,1)],
  [(8,5),(7,5),(6,5),(6,4),(5,4)],
  [(9,5),(9,3),(9,4),(8,4),(7,4)],
  [(9,2),(9,1),(9,0),(8,0),(7,0)],
  [(7,3),(8,3),(8,2),(8,1),(7,1)],
  [(7,12)],
  [(6,14),(6,13),(5,14),(5,13)],
  [(6,12),(5,12)],
  [(6,15),(5,15),(4,15),(4,14)],
  [(4,12),(3,12),(2,12),(1,12)],
  [(1,13),(0,14),(0,13),(0,12)],
  [(4,13),(3,13),(2,13)],
  [(2,14),(1,14),(1,15),(0,15)],
  [(3,14),(3,15),(2,15)],
  [(7,15),(9,15),(7,14),(9,14),(8,15),(7,13),(9,13),(8,14),(9,12),(8,13),(8,12)],
  [(15,0),(14,0),(13,0),(12,0),(11,0),(10,0)],
  [(12,2),(12,1),(11,2),(11,1),(10,2),(10,1)],
  [(12,4),(11,4),(10,5),(11,3),(10,4),(10,3)],
  [(12,3),(13,3),(13,4),(13,5),(12,5),(11,5)],
  [(15,4),(15,3),(15,2),(15,1),(14,1),(13,1)],
  [(15,5),(14,5),(14,4),(14,3),(14,2),(13,2)],
  [(1,9),(0,10),(0,9),(0,8),(0,7),(0,6)],
  [(3,10),(2,9),(2,10),(1,10),(1,11),(0,11)],
  [(5,9),(4,9),(4,10),(4,11),(3,11),(2,11)],
  [(5,7),(4,7),(3,7),(2,7),(2,6),(1,6)],
  [(7,7),(7,6),(6,6),(5,6),(4,6),(3,6)],
  [(4,8),(3,9),(3,8),(2,8),(1,8),(1,7)],
  [(8,9),(9,9),(9,8),(9,7),(9,6),(8,6)],
  [(8,7),(8,8),(7,8),(6,7),(6,8),(5,8)],
  [(9,11),(9,10),(8,10),(7,10),(7,9),(6,9)],
  [(8,11),(7,11),(6,11),(6,10),(5,11),(5,10)],
  [(12,9),(12,8),(12,7),(11,7),(11,6),(10,6)],
  [(11,10),(11,9),(11,8),(10,9),(10,8),(10,7)],
  [(13,9),(14,7),(13,8),(13,7),(13,6),(12,6)],
  [(14,9),(14,8),(15,8),(15,7),(15,6),(14,6)],
  [(15,11),(15,9),(15,10),(14,10),(13,10),(12,10)],
  [(12,11),(10,13),(11,11),(10,12),(10,11),(10,10)],
  [(14,15),(13,15),(12,14),(12,15),(11,15),(10,15)],
  [(12,12),(12,13),(11,12),(11,13),(11,14),(10,14)],
  [(15,15),(15,13),(15,14),(14,14),(13,14),(13,13)],
  [(15,12),(14,13),(14,12),(14,11),(13,12),(13,11)]]

def tilingSixteen := regions boardSixteen

set_option maxRecDepth 20000 in
private theorem build16 : boardSixteen.all building=true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem count16 : tilingSixteen.card=48 := by decide +kernel

set_option maxRecDepth 20000 in
private theorem signatures16 : (tilingSixteen.image signature).card=48 := by decide +kernel

set_option maxRecDepth 20000 in
private theorem board16 : flatCheck 16 boardSixteen=true := by decide +kernel

theorem lower_16 :
    ∃ tiles : Finset Shape, tiles.card=48 ∧ distinctPolyominoes tiles ∧ dissects 16 tiles :=
  ⟨tilingSixteen,count16,distinct_from_data _ build16 (signatures16.trans count16.symm),
    dissection_from_flat board16⟩

def boardSeventeen : List (List Cell) := [
  [(4,2),(3,3),(3,1),(3,2),(2,2)],
  [(1,3),(0,3),(0,2),(0,1),(0,0)],
  [(2,1),(1,2),(2,0),(1,1),(1,0)],
  [(6,0),(5,0),(4,1),(4,0),(3,0)],
  [(2,3),(2,4),(1,4),(0,5),(0,4)],
  [(5,5),(4,5),(3,5),(2,5),(1,5)],
  [(5,2),(5,3),(4,3),(4,4),(3,4)],
  [(7,2),(6,3),(6,2),(6,1),(5,1)],
  [(8,5),(7,5),(6,5),(6,4),(5,4)],
  [(9,5),(9,3),(9,4),(8,4),(7,4)],
  [(9,2),(9,1),(9,0),(8,0),(7,0)],
  [(7,3),(8,3),(8,2),(8,1),(7,1)],
  [(15,8),(15,7),(14,8),(14,7)],
  [(14,6),(13,6),(12,6),(11,6)],
  [(15,6)],
  [(16,8),(16,7),(16,6)],
  [(13,9),(12,10),(12,9),(11,9)],
  [(11,10),(12,8),(10,10),(11,8),(10,9),(10,8)],
  [(15,9),(14,9),(14,10),(13,10)],
  [(12,7),(11,7),(10,7),(10,6)],
  [(16,9),(16,10),(15,10)],
  [(13,8),(13,7)],
  [(12,2),(12,1),(11,2),(11,1),(10,1),(10,0)],
  [(14,2),(14,1),(13,1),(13,0),(12,0),(11,0)],
  [(15,3),(15,2),(16,0),(15,1),(15,0),(14,0)],
  [(16,1),(16,2),(16,3),(16,4),(16,5),(15,5)],
  [(12,4),(11,4),(10,5),(10,4),(10,3),(10,2)],
  [(15,4),(14,4),(14,5),(13,5),(12,5),(11,5)],
  [(14,3),(13,4),(13,2),(13,3),(12,3),(11,3)],
  [(13,13),(13,12),(12,12),(11,12),(10,12),(10,11)],
  [(14,13),(14,12),(14,11),(13,11),(12,11),(11,11)],
  [(16,16),(16,15),(16,14),(16,13),(16,12),(16,11)],
  [(15,11),(15,12),(15,15),(15,13),(15,14),(14,14)],
  [(15,16),(14,16),(14,15),(13,16),(13,15),(13,14)],
  [(11,15),(10,16),(11,14),(10,15),(10,14),(10,13)],
  [(11,16),(12,16),(12,15),(12,14),(12,13),(11,13)],
  [(9,6),(8,6),(8,7),(7,6),(7,7),(6,7)],
  [(6,8),(5,8),(6,6),(5,7),(5,6),(4,6)],
  [(9,7),(9,8),(8,8),(8,9),(8,10),(7,10)],
  [(9,9),(9,10),(9,11),(8,11),(7,12),(7,11)],
  [(7,8),(7,9),(6,10),(6,9),(5,9),(4,9)],
  [(4,7),(4,8),(3,10),(3,8),(3,9),(2,9)],
  [(1,10),(2,8),(1,9),(1,8),(0,9),(0,8)],
  [(2,10),(2,11),(1,12),(1,11),(0,11),(0,10)],
  [(3,13),(2,14),(2,13),(1,13),(0,13),(0,12)],
  [(1,16),(1,15),(0,16),(1,14),(0,15),(0,14)],
  [(5,10),(4,10),(4,11),(3,11),(3,12),(2,12)],
  [(5,16),(4,16),(3,16),(3,15),(2,16),(2,15)],
  [(9,16),(9,12),(9,15),(9,13),(9,14),(8,14)],
  [(8,15),(8,12),(7,15),(8,13),(7,14),(7,13)],
  [(8,16),(7,16),(6,16),(6,15),(5,15),(4,15)],
  [(6,13),(6,14),(5,14),(4,13),(4,14),(3,14)],
  [(6,11),(6,12),(5,13),(5,11),(5,12),(4,12)],
  [(3,7),(3,6),(2,7),(2,6),(1,7),(1,6),(0,7),(0,6)]]

def tilingSeventeen := regions boardSeventeen

set_option maxRecDepth 20000 in
private theorem build17 : boardSeventeen.all building=true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem count17 : tilingSeventeen.card=54 := by decide +kernel

set_option maxRecDepth 20000 in
private theorem signatures17 : (tilingSeventeen.image signature).card=54 := by decide +kernel

set_option maxRecDepth 20000 in
private theorem board17 : flatCheck 17 boardSeventeen=true := by decide +kernel

theorem lower_17 :
    ∃ tiles : Finset Shape, tiles.card=54 ∧ distinctPolyominoes tiles ∧ dissects 17 tiles :=
  ⟨tilingSeventeen,count17,distinct_from_data _ build17 (signatures17.trans count17.symm),
    dissection_from_flat board17⟩

/-- A dissection by k pieces, together with an upper bound for all unrestricted
collections of distinct free polyominoes having the same total area. -/
def maximumAt (n k : ℕ) : Prop :=
  (∃ tiles : Finset Shape, tiles.card=k ∧ distinctPolyominoes tiles ∧ dissects n tiles) ∧
  ∀ shapes : Finset Shape, distinctPolyominoes shapes →
    (∑ a∈shapes,a.card)=n^2 → shapes.card≤k

private theorem exact_of_six {n k : ℕ}
    (construction : ∃ tiles : Finset Shape,
      tiles.card=k ∧ distinctPolyominoes tiles ∧ dissects n tiles)
    (next : n^2+37 < 6*(k+1)) : maximumAt n k := by
  refine ⟨construction,?_⟩
  intro shapes distinct area
  have b := area_bound shapes distinct
  rw [area] at b
  omega

theorem exact_three : maximumAt 15 43 ∧ maximumAt 16 48 ∧ maximumAt 17 54 :=
  ⟨exact_of_six lower_15 (by decide), exact_of_six lower_16 (by decide),
    exact_of_six lower_17 (by decide)⟩

end DistinctSquare
