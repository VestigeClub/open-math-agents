import certificates.«pp-primes-candidates-b»
import certificates.«pp-catalog-complete»

open Finset OMA.S_oeis_a380455 PrimePolyFactor
namespace HalfPrimes

theorem representative {f : Shape} (area : ℕ) (supported : area∈([2,4,7,8] : List ℕ))
    (prime : primeShape f) (size : f.card=area) :
    ∃ id<HalfCatalogue.count area,
      allowed area id=true ∧ congruent f (HalfCatalogue.shape area id) := by
  have positive : 0<area := by simpa only [←size] using (Nat.lt_trans (by decide : 0<1) prime.2.1)
  have bounded : area≤8 := by
    have h : area=2 ∨ area=4 ∨ area=7 ∨ area=8 := by simpa using supported
    omega
  obtain ⟨id,valid,rel⟩ := HalfCatalogue.representative prime.1 area positive bounded size
  exact ⟨id,valid,allowed_of_prime supported valid size prime rel,rel⟩

end HalfPrimes
