import certificates.«pp-catalog-models»

open Finset OMA.S_oeis_a380455 PrimePolyFactor
namespace HalfCatalogue

def extensionComplete (area id : ℕ) : Prop :=
  ∀ child ∈ extensions (shape area id), ∃ j < count (area+1), congruent child (shape (area+1) j)

structure Assignment where
  child : Shape
  id : ℕ
  turnBy : Orientation
  offset : Cell

def assignmentGood (area : ℕ) (r : Assignment) : Bool :=
  decide (r.id < count (area+1) ∧
    shape (area+1) r.id = r.child.image (move r.turnBy r.offset))

def transitionCheck (area id : ℕ) (rows : List Assignment) : Bool :=
  decide (extensions (shape area id) ⊆ (rows.map Assignment.child).toFinset) &&
    rows.all (assignmentGood area)

theorem transition_of_check {area id : ℕ} {rows : List Assignment}
    (checked : transitionCheck area id rows=true) : extensionComplete area id := by
  simp only [transitionCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
  intro child member
  obtain ⟨r,hr,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp (checked.1 member))
  have good : r.id < count (area+1) ∧
      shape (area+1) r.id = r.child.image (move r.turnBy r.offset) :=
    of_decide_eq_true (List.all_eq_true.mp checked.2 _ hr)
  refine ⟨r.id,good.1,(congruent_iff _ _).mpr ⟨r.turnBy,r.offset,?_⟩⟩
  simpa only [eq] using good.2

private theorem neighbor_spec (a b : Cell) : b ∈ neighbors a ↔ adjacent a b := by
  obtain ⟨x,y⟩ := a
  obtain ⟨u,v⟩ := b
  simp [neighbors,adjacent,Prod.ext_iff]
  omega

private theorem adjacency_transform (g : Orientation) (o a b : Cell)
    (edge : adjacent a b) : adjacent (move g o a) (move g o b) := by
  obtain ⟨s,x,y⟩ := g
  cases s <;> cases x <;> cases y <;> simp [adjacent,move,turn,sign] at edge ⊢ <;> omega

private theorem move_inj (g : Orientation) (o : Cell) : Function.Injective (move g o) := by
  intro p q eq
  have e : turn g p=turn g q := add_left_cancel (show o+turn g p=o+turn g q from eq)
  simpa only [turn_inv] using congrArg (turn (inverse g)) e

def completeGrowth : Prop :=
  ∀ area, 1 ≤ area → area < 8 → ∀ id, id < count area → extensionComplete area id

theorem animal_represented (steps : completeGrowth) (k : ℕ) (limit : k<8)
    {A : Shape} (ha : A∈animals k) :
    ∃ id < count (k+1), congruent A (shape (k+1) id) := by
  induction k generalizing A with
  | zero =>
    have eq : A={(0,0)} := by simpa [animals] using ha
    subst A
    refine ⟨0,by decide,(congruent_iff _ _).mpr ⟨⟨false,false,false⟩,0,?_⟩⟩
    decide +kernel
  | succ k ih =>
    obtain ⟨S,hs,rest⟩ := mem_biUnion.mp ha
    obtain ⟨a,hasa,rest⟩ := mem_biUnion.mp rest
    obtain ⟨b,hb,rfl⟩ := mem_image.mp rest
    obtain ⟨nb,fresh⟩ := mem_filter.mp hb
    obtain ⟨i,hi,geo⟩ := ih (by omega) hs
    obtain ⟨g,o,eq⟩ := (congruent_iff _ _).mp geo
    let f := move g o
    have inj := move_inj g o
    have ar : f a ∈ shape (k+1) i := eq ▸ mem_image_of_mem _ hasa
    have br : f b ∉ shape (k+1) i := by
      rw [eq]
      intro h
      obtain ⟨v,hv,same⟩ := mem_image.mp h
      exact fresh ((inj same) ▸ hv)
    have adj : f b ∈ neighbors (f a) :=
      (neighbor_spec _ _).mpr (adjacency_transform _ _ _ _ ((neighbor_spec _ _).mp nb))
    have ext : insert (f b) (shape (k+1) i) ∈ extensions (shape (k+1) i) :=
      mem_biUnion.mpr ⟨f a,ar,mem_image.mpr ⟨f b,mem_filter.mpr ⟨adj,br⟩,rfl⟩⟩
    obtain ⟨j,hj,next⟩ := steps (k+1) (by omega) (by omega) i hi _ ext
    exact ⟨j,hj,motion_trans ((congruent_iff _ _).mpr ⟨g,o,by simp [eq,f]⟩) next⟩

theorem represented_of_growth (steps : completeGrowth) {f : Shape} (poly : polyomino f)
    (area : ℕ) (positive : 0<area) (bound : area≤8) (size : f.card=area) :
    ∃ id < count area, congruent f (shapeCells area id).toFinset := by
  have size' : f.card=(area-1)+1 := by omega
  obtain ⟨A,ha,rel⟩ := rooted_model poly (area-1) size'
  obtain ⟨id,hi,eq⟩ := animal_represented steps (area-1) (by omega) ha
  have amount : area-1+1=area := by omega
  rw [amount] at hi eq
  exact ⟨id,hi,motion_trans rel eq⟩

end HalfCatalogue
