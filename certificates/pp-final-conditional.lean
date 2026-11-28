import certificates.«pp-incidence-rows-core»
import certificates.«pp-primes-assemble-b»
import certificates.«pp-primes-representatives-b»
import certificates.«maximum-prime-factors-fifteen-cells»

open Finset OMA.S_oeis_a380455 PrimePolyFactor
namespace HalfFinal

def AllRows : Prop :=
  ∀ half id : ℕ, (half=7 ∨ half=8) → id<HalfCatalogue.count half →
    HalfPrimes.allowed half id=true → ∀ g : Orientation, HalfIncidence.RowFact half id g

theorem factor_info (rows : AllRows) {b f : Shape} (half : ℕ)
    (supported : half=7 ∨ half=8) (poly : polyomino b)
    (area : b.card=2*half) (prime : primeShape f) (tiling : tiles f b)
    (size : f.card=half) :
    ∃ id<HalfCatalogue.count half,
      congruent f (HalfCatalogue.shape half id) ∧
      HalfIndex.offered half (HalfGeometry.boardKey b) id=true ∧
      (half=8 → HalfGeometry.boardKey b=HalfIndex.exceptionKey →
        congruent b HalfPrimes.exceptionShape) := by
  have inList : half∈([2,4,7,8] : List ℕ) := by rcases supported with rfl|rfl <;> decide
  obtain ⟨id,valid,allowed,known⟩:=HalfPrimes.representative half inList prime size
  have positive : 0<f.card := lt_trans (by decide : 0<1) prime.2.1
  have exactArea : b.card=2*f.card := by omega
  obtain ⟨g,o,related,apart⟩:=HalfGeometry.pair_model tiling positive exactArea known
  have nonempty : (HalfCatalogue.shape half id).Nonempty := card_pos.mp (by
    have := motion_card known
    omega)
  obtain ⟨u,hu,v,hv,n,hn,offset⟩:=
    HalfGeometry.pair_adjacent_offset poly nonempty related apart
  have proposal : ∃ u∈HalfCatalogue.shape half id, ∃ v∈HalfCatalogue.shape half id,
      ∃ n∈neighbors u, o=n-turn g v := ⟨u,hu,v,hv,n,hn,offset⟩
  have tested := rows half id supported valid allowed g o proposal apart
  have key : HalfGeometry.boardKey b =
      HalfGeometry.fastKey (HalfGeometry.views (HalfCatalogue.shape half id)) g o :=
    (HalfGeometry.boardKey_invariant related).trans (HalfGeometry.pair_fastKey nonempty g o)
  refine ⟨id,valid,known,?_,?_⟩
  · rw [key]
    exact tested.1
  · intro eight exception
    have geo := tested.2 eight (key.symm.trans exception)
    exact motion_trans related geo

theorem large_bound (rows : AllRows) {b : Shape} {fs : Finset Shape} (half : ℕ)
    (supported : half=7 ∨ half=8) (poly : polyomino b) (area : b.card=2*half)
    (factors : ∀ f∈fs, primeShape f ∧ tiles f b)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q) :
    (fs.filter (fun f => f.card=half)).card≤HalfIndex.capacity half (HalfGeometry.boardKey b) := by
  apply HalfPrimes.large_family_bound different
    (catalog:=HalfIndex.palette half (HalfGeometry.boardKey b))
  · intro f hf size
    obtain ⟨id,_,known,offered,_⟩:=factor_info rows half supported poly area
      (factors f hf).1 (factors f hf).2 size
    exact ⟨HalfCatalogue.shape half id,HalfIndex.in_palette offered,known⟩
  · exact HalfIndex.palette_card _ _

theorem fourteen_upper (rows : AllRows) {b : Shape} {fs : Finset Shape}
    (poly : polyomino b) (area : b.card=14)
    (factors : ∀ f∈fs, primeShape f ∧ tiles f b)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q) : fs.card≤10 := by
  apply HalfPrimes.fourteen_upper_of_large area factors different
  have bound:=large_bound rows 7 (Or.inl rfl) poly area factors different
  simpa only [HalfIndex.capacity,ite_true] using bound

theorem sixteen_upper (rows : AllRows) {b : Shape} {fs : Finset Shape}
    (poly : polyomino b) (area : b.card=16)
    (factors : ∀ f∈fs, primeShape f ∧ tiles f b)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q) : fs.card≤12 := by
  classical
  have bound:=large_bound rows 8 (Or.inr rfl) poly area factors different
  by_cases exception : HalfGeometry.boardKey b=HalfIndex.exceptionKey
  · by_cases existsBig : ∃ f∈fs, f.card=8
    · obtain ⟨f,hf,size⟩:=existsBig
      obtain ⟨_,_,_,_,geo⟩:=factor_info rows 8 (Or.inr rfl) poly area
        (factors f hf).1 (factors f hf).2 size
      apply HalfPrimes.sixteen_exceptional_upper area (geo rfl exception) factors different
      simpa only [HalfIndex.capacity,show (8 : ℕ)≠7 by decide,ite_false,exception,ite_true] using bound
    · apply HalfPrimes.sixteen_upper_of_large area factors different
      have empty : fs.filter (fun f => f.card=8)=∅ := by
        apply filter_eq_empty_iff.mpr
        intro f hf size
        exact existsBig ⟨f,hf,size⟩
      simp [empty]
  · apply HalfPrimes.sixteen_upper_of_large area factors different
    simpa only [HalfIndex.capacity,show (8 : ℕ)≠7 by decide,ite_false,exception] using bound

theorem exact_fourteen (rows : AllRows) : maximum 14 10 := by
  refine ⟨achieves_14,?_⟩
  rintro j ⟨b,fs,poly,area,size,factors,different⟩
  rw [←size]
  exact fourteen_upper rows poly area factors different

theorem exact_sixteen (rows : AllRows) : maximum 16 12 := by
  refine ⟨achieves_16,?_⟩
  rintro j ⟨b,fs,poly,area,size,factors,different⟩
  rw [←size]
  exact sixteen_upper rows poly area factors different

theorem all_four (rows : AllRows) :
    maximum 14 10 ∧ maximum 15 3 ∧ maximum 16 12 ∧ maximum 17 1 :=
  ⟨exact_fourteen rows,exact_fifteen,exact_sixteen rows,exact_seventeen⟩

end HalfFinal
