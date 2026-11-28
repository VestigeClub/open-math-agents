import certificates.«pp-primes-small-c»

open Finset OMA.S_oeis_a380455 PrimePolyFactor
namespace HalfPrimes

theorem proper_area_fourteen {b f : Shape} (size : b.card=14)
    (prime : primeShape f) (tiling : tiles f b) (proper : f.card≠b.card) : f.card=2 ∨ f.card=7 := by
  have dvd : f.card∣14 := size ▸ tile_area tiling
  have bound := Nat.le_of_dvd (by decide : 0<14) dvd
  have low := prime.2.1
  have ne : f.card≠14 := by simpa [size] using proper
  interval_cases h : f.card <;> first | omega | norm_num at dvd

theorem proper_area_sixteen {b f : Shape} (size : b.card=16)
    (prime : primeShape f) (tiling : tiles f b) (proper : f.card≠b.card) :
    f.card=2 ∨ f.card=4 ∨ f.card=8 := by
  have dvd : f.card∣16 := size ▸ tile_area tiling
  have bound := Nat.le_of_dvd (by decide : 0<16) dvd
  have low := prime.2.1
  have ne : f.card≠16 := by simpa [size] using proper
  interval_cases h : f.card <;> first | omega | norm_num at dvd

theorem large_family_bound {fs catalog : Finset Shape} {area cap : ℕ}
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q)
    (cover : ∀ f∈fs, f.card=area → ∃ r∈catalog, congruent f r)
    (bound : catalog.card≤cap) : (fs.filter (fun f => f.card=area)).card≤cap := by
  refine (represented_card (family:=fs.filter (fun f => f.card=area)) (catalog:=catalog) ?_ ?_).trans bound
  · intro p hp q hq
    exact different p (mem_filter.mp hp).1 q (mem_filter.mp hq).1
  · intro f hf
    exact cover f (mem_filter.mp hf).1 (mem_filter.mp hf).2

theorem fourteen_upper_of_large {b : Shape} {fs : Finset Shape} (size : b.card=14)
    (factors : ∀ f∈fs, primeShape f ∧ tiles f b)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q)
    (large : (fs.filter (fun f => f.card=7)).card≤9) : fs.card≤10 := by
  by_cases whole : ∃ p∈fs, p.card=b.card
  · exact (bounds_when_whole factors different whole).trans (by decide)
  have options (f : Shape) (hf : f∈fs) : f.card=2 ∨ f.card=7 :=
    proper_area_fourteen size (factors f hf).1 (factors f hf).2 (fun eq => whole ⟨f,hf,eq⟩)
  let small := fs.filter (fun f => f.card=2)
  let big := fs.filter (fun f => f.card=7)
  have union : small ∪ big=fs := by
    ext f
    simp only [small,big,mem_union,mem_filter]
    constructor
    · rintro (h|h) <;> exact h.1
    · intro hf
      rcases options f hf with a|a
      · exact Or.inl ⟨hf,a⟩
      · exact Or.inr ⟨hf,a⟩
  have smallBound := small_family_fourteen (fun f hf => (factors f hf).1) different
  have total := card_union_le small big
  rw [union] at total
  change small.card≤1 at smallBound
  change big.card≤9 at large
  omega

theorem sixteen_upper_of_large {b : Shape} {fs : Finset Shape} (size : b.card=16)
    (factors : ∀ f∈fs, primeShape f ∧ tiles f b)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q)
    (large : (fs.filter (fun f => f.card=8)).card≤10) : fs.card≤12 := by
  by_cases whole : ∃ p∈fs, p.card=b.card
  · exact (bounds_when_whole factors different whole).trans (by decide)
  have options (f : Shape) (hf : f∈fs) : f.card=2 ∨ f.card=4 ∨ f.card=8 :=
    proper_area_sixteen size (factors f hf).1 (factors f hf).2 (fun eq => whole ⟨f,hf,eq⟩)
  let small := fs.filter (fun f => f.card=2 ∨ f.card=4)
  let big := fs.filter (fun f => f.card=8)
  have union : small ∪ big=fs := by
    ext f
    simp only [small,big,mem_union,mem_filter]
    constructor
    · rintro (h|h) <;> exact h.1
    · intro hf
      rcases options f hf with a|a|a
      · exact Or.inl ⟨hf,Or.inl a⟩
      · exact Or.inl ⟨hf,Or.inr a⟩
      · exact Or.inr ⟨hf,a⟩
  have smallBound := small_family_sixteen (fun f hf => (factors f hf).1) different
  have total := card_union_le small big
  rw [union] at total
  change small.card≤2 at smallBound
  change big.card≤10 at large
  omega

theorem sixteen_exceptional_upper {b : Shape} {fs : Finset Shape} (size : b.card=16)
    (geo : congruent b exceptionShape)
    (factors : ∀ f∈fs, primeShape f ∧ tiles f b)
    (different : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q)
    (large : (fs.filter (fun f => f.card=8)).card≤12) : fs.card≤12 := by
  by_cases whole : ∃ p∈fs, p.card=b.card
  · exact (bounds_when_whole factors different whole).trans (by decide)
  have all (f : Shape) (hf : f∈fs) : f.card=8 := by
    have opts := proper_area_sixteen size (factors f hf).1 (factors f hf).2 (fun eq => whole ⟨f,hf,eq⟩)
    rcases opts with two|four|eight
    · exact (no_small_exceptional geo (factors f hf).1 (Or.inl two) (factors f hf).2).elim
    · exact (no_small_exceptional geo (factors f hf).1 (Or.inr four) (factors f hf).2).elim
    · exact eight
  have eq : fs.filter (fun f => f.card=8)=fs := filter_eq_self.mpr all
  simpa only [eq] using large

end HalfPrimes
