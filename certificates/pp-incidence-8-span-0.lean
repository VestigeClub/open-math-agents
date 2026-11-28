import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-0»
import certificates.«pp-incidence-8-group-1»

/-! Catalogue positions from 0 through 15. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x0 (j : ℕ) (lo : (0 : ℕ) ≤ j) (hi : j < 16)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 0=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 1=true) eligible).elim
  · exact checked8x2
  · exact ((by decide +kernel : ¬allowed 8 3=true) eligible).elim
  · exact checked8x4
  · exact ((by decide +kernel : ¬allowed 8 5=true) eligible).elim
  · exact checked8x6
  · exact ((by decide +kernel : ¬allowed 8 7=true) eligible).elim
  · exact checked8x8
  · exact ((by decide +kernel : ¬allowed 8 9=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 10=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 11=true) eligible).elim
  · exact checked8x12
  · exact ((by decide +kernel : ¬allowed 8 13=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 14=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 15=true) eligible).elim

end HalfIndexRows
