import certificates.«pp-geometry-key-c»

open Finset OMA.S_oeis_a380455 PrimePolyFactor FactorMaskCheck
namespace HalfGeometry

theorem least_union {s t : Shape} (hs : s.Nonempty) (ht : t.Nonempty) :
    least (s∪t)=min (least s) (least t) := by
  obtain ⟨p,hp,eqp⟩:=least_attained hs
  obtain ⟨q,hq,eqq⟩:=least_attained ht
  obtain ⟨r,hr,eqr⟩:=least_attained (show (s∪t).Nonempty from hs.mono subset_union_left)
  have lp : least (s∪t)≤flat p := least_le (mem_union_left t hp)
  have lq : least (s∪t)≤flat q := least_le (mem_union_right s hq)
  rw [eqp] at lp
  rw [eqq] at lq
  rcases mem_union.mp hr with ins|int
  · have r:=least_le ins
    rw [eqr] at r
    omega
  · have r:=least_le int
    rw [eqr] at r
    omega

theorem cells_view (s : Shape) : cells (view s).2=normCells s :=
  Finset.equivBitIndices.apply_symm_apply _

theorem norm_union {s t : Shape} (hs : s.Nonempty) (ht : t.Nonempty) :
    normCells (s∪t)=
      (normCells s).image (·+(least s-least (s∪t)).toNat) ∪
      (normCells t).image (·+(least t-least (s∪t)).toNat) := by
  unfold normCells
  rw [image_union,image_image,image_image]
  congr 1
  · apply Finset.image_congr
    intro p hp
    dsimp only [Function.comp_apply]
    have lp:=least_le hp
    have order : least (s∪t)≤least s := by rw [least_union hs ht]; exact min_le_left _ _
    omega
  · apply Finset.image_congr
    intro p hp
    dsimp only [Function.comp_apply]
    have lp:=least_le hp
    have order : least (s∪t)≤least t := by rw [least_union hs ht]; exact min_le_right _ _
    omega

theorem view_union_word {s t : Shape} (hs : s.Nonempty) (ht : t.Nonempty) :
    (view (s∪t)).2 =
      ((view s).2 <<< (least s-min (least s) (least t)).toNat) |||
      ((view t).2 <<< (least t-min (least s) (least t)).toNat) := by
  apply cells_injective
  rw [cells_or,shifted_cells,shifted_cells,cells_view,cells_view,cells_view,
    norm_union hs ht,least_union hs ht]

theorem word_union_translate {s t : Shape} (hs : s.Nonempty) (ht : t.Nonempty) (o : Cell) :
    (view (s∪t.image (fun p => o+p))).2=joinWord (view s) (view t) (flat o) := by
  rw [view_union_word hs (ht.image _),word_translate,least_translate ht]
  rfl

theorem pair_fastKey {s : Shape} (hs : s.Nonempty) (g : Orientation) (o : Cell) :
    boardKey (s∪s.image (move g o))=fastKey (views s) g o := by
  unfold boardKey fastKey
  congr 1
  funext d
  unfold views
  rw [image_union,turned_move]
  exact word_union_translate (hs.image _) (hs.image _) (turn d o)

end HalfGeometry
