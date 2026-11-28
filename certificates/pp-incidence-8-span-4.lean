import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-6»
import certificates.«pp-incidence-8-group-7»

/-! Catalogue positions from 64 through 79. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x4 (j : ℕ) (lo : (64 : ℕ) ≤ j) (hi : j < 80)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 64 ∨ j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 ∨ j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨ j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 64=true) eligible).elim
  · exact checked8x65
  · exact checked8x66
  · exact checked8x67
  · exact checked8x68
  · exact ((by decide +kernel : ¬allowed 8 69=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 70=true) eligible).elim
  · exact checked8x71
  · exact ((by decide +kernel : ¬allowed 8 72=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 73=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 74=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 75=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 76=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 77=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 78=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 79=true) eligible).elim

end HalfIndexRows
