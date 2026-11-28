import certificates.«pp-geometry-two-pieces-b»
import certificates.«pp-primes-exception-data»

open Finset OMA.S_oeis_a380455 PrimePolyFactor HalfPrimes
namespace HalfIncidence

def offsetIndex (o : Cell) : ℕ := (o.1+16).toNat + 32*(o.2+16).toNat

def offsetAt (k : ℕ) : Cell := ((↑(k%32) : ℤ)-16,(↑(k/32) : ℤ)-16)

def adjacentList (p : Cell) : List Cell :=
  [(p.1+1,p.2),(p.1-1,p.2),(p.1,p.2+1),(p.1,p.2-1)]

theorem adjacentListed {p q : Cell} (h : q∈neighbors p) : q∈adjacentList p := by
  simpa only [neighbors,adjacentList,mem_insert,mem_singleton,List.mem_cons,List.not_mem_nil,or_false] using h

def overlapFlag (m : List Cell) (g : Orientation) (o : Cell) : Bool :=
  m.any fun q => decide (move g o q∈m)

def located (mask : ℕ) (o : Cell) : Bool :=
  decide (offsetAt (offsetIndex o)=o) && mask.testBit (offsetIndex o)

def coverage (m : List Cell) (g : Orientation) (mask : ℕ) : Bool :=
  m.all fun a => m.all fun b => (adjacentList a).all fun n =>
    let o := n-turn g b
    located mask o || overlapFlag m g o

theorem proposed_captured {m : List Cell} {g : Orientation} {o : Cell} {mask : ℕ}
    (ok : coverage m g mask=true)
    (edge : ∃ u∈m.toFinset, ∃ v∈m.toFinset, ∃ n∈neighbors u, o=n-turn g v)
    (apart : Disjoint m.toFinset (m.toFinset.image (move g o))) :
    ∃ k∈mask.bitIndices, offsetAt k=o := by
  obtain ⟨u,hu,v,hv,n,hn,off⟩:=edge
  have a:=List.all_eq_true.mp ok u (List.mem_toFinset.mp hu)
  have b:=List.all_eq_true.mp a v (List.mem_toFinset.mp hv)
  have c:=List.all_eq_true.mp b n (adjacentListed hn)
  change (located mask (n-turn g v) || overlapFlag m g (n-turn g v))=true at c
  rw [←off] at c
  have alternatives : located mask o=true ∨ overlapFlag m g o=true := by simpa using c
  rcases alternatives with yes|clash
  · have loc : offsetAt (offsetIndex o)=o ∧ mask.testBit (offsetIndex o)=true := by simpa [located] using yes
    exact ⟨offsetIndex o, (Nat.mem_bitIndices).mpr loc.2, loc.1⟩
  · obtain ⟨q,hq,used⟩:=List.any_eq_true.mp clash
    exact (disjoint_left.mp apart (List.mem_toFinset.mpr (of_decide_eq_true used))
      (mem_image_of_mem _ (List.mem_toFinset.mpr hq))).elim

def joined (m : List Cell) (g : Orientation) (o : Cell) : Shape :=
  m.toFinset ∪ m.toFinset.image (move g o)

def isExceptionalShape (m : List Cell) (g : Orientation) (o : Cell) : Bool :=
  directions.any fun h => exceptionCells.any fun q =>
    decide (exceptionShape = (joined m g o).image (move h (q-turn h (m.headD (0,0)))))

theorem exceptional_of_check {m : List Cell} {g : Orientation} {o : Cell}
    (yes : isExceptionalShape m g o=true) : congruent (joined m g o) exceptionShape := by
  obtain ⟨h,_,rest⟩:=List.any_eq_true.mp yes
  obtain ⟨q,_,same⟩:=List.any_eq_true.mp rest
  exact (congruent_iff _ _).mpr ⟨h,q-turn h (m.headD (0,0)),of_decide_eq_true same⟩

end HalfIncidence
