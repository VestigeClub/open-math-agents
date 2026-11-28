import certificates.«pp-geometry-two-pieces-b»

open Finset OMA.S_oeis_a380455 PrimePolyFactor FactorMaskCheck
namespace HalfGeometry

def least (s : Shape) : ℤ :=
  if h : s.Nonempty then (s.image flat).min' (h.image flat) else 0

def normCells (s : Shape) : Finset ℕ := s.image fun p => (flat p-least s).toNat

def view (s : Shape) : ℤ × ℕ := (least s,Finset.equivBitIndices.symm (normCells s))
def views (s : Shape) (d : Orientation) : ℤ × ℕ := view (s.image (turn d))

def minimum (f : Orientation → ℕ) : ℕ :=
  (Finset.univ.image f).min' ⟨f ⟨false,false,false⟩,mem_image_of_mem f (mem_univ _)⟩

def boardKey (s : Shape) : ℕ := minimum fun d => (views s d).2

def joinWord (a b : ℤ × ℕ) (shift : ℤ) : ℕ :=
  let z := min a.1 (shift+b.1)
  (a.2 <<< (a.1-z).toNat) ||| (b.2 <<< (shift+b.1-z).toNat)

def fastKey (cache : Orientation → ℤ × ℕ) (g : Orientation) (o : Cell) : ℕ :=
  minimum fun d => joinWord (cache d) (cache (compose g d)) (flat (turn d o))

theorem least_le {s : Shape} {p : Cell} (hp : p∈s) : least s≤flat p := by
  unfold least
  rw [dif_pos ⟨p,hp⟩]
  exact Finset.min'_le _ _ (mem_image_of_mem _ hp)

theorem least_attained {s : Shape} (hs : s.Nonempty) : ∃ p∈s, flat p=least s := by
  unfold least
  rw [dif_pos hs]
  exact mem_image.mp (Finset.min'_mem _ _)

theorem flat_add (p q : Cell) : flat (p+q)=flat p+flat q := by
  simp [flat]
  ring

theorem least_translate {s : Shape} (hs : s.Nonempty) (o : Cell) :
    least (s.image (fun p => o+p))=flat o+least s := by
  obtain ⟨p,hp,eqp⟩:=least_attained hs
  obtain ⟨q,hq,eqq⟩:=least_attained (hs.image (fun p => o+p))
  obtain ⟨v,hv,rfl⟩:=mem_image.mp hq
  have l:=least_le (mem_image_of_mem (fun p => o+p) hp)
  have r:=least_le hv
  rw [flat_add,eqp] at l
  rw [flat_add] at eqq
  omega

theorem norm_translate (s : Shape) (o : Cell) :
    normCells (s.image (fun p => o+p))=normCells s := by
  by_cases hs : s.Nonempty
  · unfold normCells
    rw [image_image]
    apply Finset.image_congr
    intro p hp
    dsimp only [Function.comp_apply]
    rw [least_translate hs,flat_add]
    congr 1
    ring
  · have empty : s=∅ := not_nonempty_iff_eq_empty.mp hs
    simp [empty,normCells]

theorem word_translate (s : Shape) (o : Cell) :
    (view (s.image (fun p => o+p))).2=(view s).2 := by
  simp only [view,norm_translate]

theorem turned_move (s : Shape) (g d : Orientation) (o : Cell) :
    (s.image (move g o)).image (turn d)=
      (s.image (turn (compose g d))).image (fun p => turn d o+p) := by
  simp only [image_image]
  congr 1
  funext p
  simp [move,turn_add,turn_comp]

theorem views_move (s : Shape) (g d : Orientation) (o : Cell) :
    (views (s.image (move g o)) d).2=(views s (compose g d)).2 := by
  unfold views
  rw [turned_move,word_translate]

theorem compose_surjective (g : Orientation) : Function.Surjective (compose g) := by
  intro d
  refine ⟨compose (inverse g) d,?_⟩
  obtain ⟨a,b,c⟩:=g
  obtain ⟨x,y,z⟩:=d
  cases a <;> cases b <;> cases c <;> cases x <;> cases y <;> cases z <;>
    decide

theorem minimum_compose (f : Orientation → ℕ) (g : Orientation) :
    minimum (fun d => f (compose g d))=minimum f := by
  have eq : Finset.univ.image (fun d => f (compose g d))=Finset.univ.image f := by
    ext k
    simp only [mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨d,rfl⟩
      exact ⟨compose g d,rfl⟩
    · rintro ⟨d,rfl⟩
      obtain ⟨e,he⟩:=compose_surjective g d
      exact ⟨e,congrArg f he⟩
  unfold minimum
  simp only [eq]

theorem boardKey_motion (s : Shape) (g : Orientation) (o : Cell) :
    boardKey (s.image (move g o))=boardKey s := by
  unfold boardKey
  simp only [views_move]
  exact minimum_compose (fun d => (views s d).2) g

theorem boardKey_invariant {a b : Shape} (h : congruent a b) : boardKey a=boardKey b := by
  obtain ⟨g,o,rfl⟩:=(congruent_iff _ _).mp h
  exact (boardKey_motion a g o).symm

end HalfGeometry
