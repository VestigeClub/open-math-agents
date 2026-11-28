import certificates.«pp-primes-candidates-b»
import certificates.«pp-primes-exception-data»

open Finset OMA.S_oeis_a380455 PrimePolyFactor
namespace HalfPrimes

private theorem small_catalogue_agrees :
    models 1 = {HalfCatalogue.shape 2 0} ∧
    models 3 ⊆ ((List.range 5).map (HalfCatalogue.shape 4)).toFinset := by decide +kernel

theorem domino_representative {f : Shape} (poly : polyomino f) (size : f.card=2) :
    congruent f (HalfCatalogue.shape 2 0) := by
  obtain ⟨s,hs,rel⟩ := representative poly 1 (by decide) size
  rw [small_catalogue_agrees.1] at hs
  exact (mem_singleton.mp hs) ▸ rel

theorem tetromino_representative {f : Shape} (prime : primeShape f) (size : f.card=4) :
    congruent f (HalfCatalogue.shape 4 2) := by
  obtain ⟨s,hs,rel⟩ := representative prime.1 3 (by decide) size
  have mem := small_catalogue_agrees.2 hs
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp mem)
  have bound : i<5 := List.mem_range.mp hi
  have con : congruent f (HalfCatalogue.shape 4 i) := eq ▸ rel
  have valid : i<HalfCatalogue.count 4 := bound
  have keep := allowed_of_prime (by simp) valid size prime con
  have law : ∀ j : Fin 5, allowed 4 j=true → j.val=2 := by decide +kernel
  have which : i=2 := law ⟨i,bound⟩ keep
  exact which ▸ con

def smallCatalogue : Finset Shape := {HalfCatalogue.shape 2 0,HalfCatalogue.shape 4 2}

theorem small_representative {f : Shape} (prime : primeShape f) (size : f.card=2 ∨ f.card=4) :
    ∃ r∈smallCatalogue, congruent f r := by
  rcases size with two|four
  · exact ⟨HalfCatalogue.shape 2 0,by simp [smallCatalogue],domino_representative prime.1 two⟩
  · exact ⟨HalfCatalogue.shape 4 2,by simp [smallCatalogue],tetromino_representative prime four⟩

theorem small_family_fourteen {fs : Finset Shape} (primes : ∀ f∈fs, primeShape f)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q) :
    (fs.filter (fun f => f.card=2)).card≤1 := by
  have bound : ({HalfCatalogue.shape 2 0} : Finset Shape).card=1 := by simp
  rw [←bound]
  apply represented_card
  · intro p hp q hq
    exact different p (mem_filter.mp hp).1 q (mem_filter.mp hq).1
  · intro t ht
    exact ⟨HalfCatalogue.shape 2 0,by simp,
      domino_representative (primes t (mem_filter.mp ht).1).1 (mem_filter.mp ht).2⟩

theorem small_family_sixteen {fs : Finset Shape} (primes : ∀ f∈fs, primeShape f)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q) :
    (fs.filter (fun f => f.card=2 ∨ f.card=4)).card≤2 := by
  have cap : smallCatalogue.card≤2 := by decide +kernel
  refine (represented_card (family:=fs.filter (fun f => f.card=2 ∨ f.card=4)) (catalog:=smallCatalogue) ?_ ?_).trans cap
  · intro p hp q hq
    exact different p (mem_filter.mp hp).1 q (mem_filter.mp hq).1
  · intro f hf
    exact small_representative (primes f (mem_filter.mp hf).1) (mem_filter.mp hf).2

set_option maxRecDepth 20000 in
private theorem rejects_small :
    fits 16 (HalfCatalogue.shapeCells 2 0) exceptionCells exceptionShape=false ∧
    fits 16 (HalfCatalogue.shapeCells 4 2) exceptionCells exceptionShape=false := by decide +kernel

theorem no_small_exceptional {f b : Shape} (geo : congruent b exceptionShape)
    (prime : primeShape f) (size : f.card=2 ∨ f.card=4) : ¬tiles f b := by
  intro tiling
  have moved := transport_tiles tiling geo
  have area : exceptionShape.card=16 := by decide +kernel
  rcases size with two|four
  · have rel := domino_representative prime.1 two
    have det := tile_detected rel moved (by omega : 0<f.card)
    change fits exceptionShape.card (HalfCatalogue.shapeCells 2 0) exceptionCells exceptionShape=true at det
    rw [area,rejects_small.1] at det
    contradiction
  · have rel := tetromino_representative prime four
    have det := tile_detected rel moved (by omega : 0<f.card)
    change fits exceptionShape.card (HalfCatalogue.shapeCells 4 2) exceptionCells exceptionShape=true at det
    rw [area,rejects_small.2] at det
    contradiction

end HalfPrimes
