import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-5»
import certificates.«pp-incidence-8-group-6»

/-! Catalogue positions from 48 through 63. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x3 (j : ℕ) (lo : (48 : ℕ) ≤ j) (hi : j < 64)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 48 ∨ j = 49 ∨ j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨ j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 ∨ j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 48=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 49=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 50=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 51=true) eligible).elim
  · exact checked8x52
  · exact ((by decide +kernel : ¬allowed 8 53=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 54=true) eligible).elim
  · exact checked8x55
  · exact ((by decide +kernel : ¬allowed 8 56=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 57=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 58=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 59=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 60=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 61=true) eligible).elim
  · exact checked8x62
  · exact checked8x63

end HalfIndexRows
