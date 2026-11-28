import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-rows-core»

/-! Catalogue positions from 368 through 368. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x23 (j : ℕ) (lo : (368 : ℕ) ≤ j) (hi : j < 369)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 368 := by omega
  rcases options with rfl
  · exact ((by decide +kernel : ¬allowed 8 368=true) eligible).elim

end HalfIndexRows
