import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-9»

/-! Catalogue positions from 96 through 111. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x6 (j : ℕ) (lo : (96 : ℕ) ≤ j) (hi : j < 112)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 96 ∨ j = 97 ∨ j = 98 ∨ j = 99 ∨ j = 100 ∨ j = 101 ∨ j = 102 ∨ j = 103 ∨ j = 104 ∨ j = 105 ∨ j = 106 ∨ j = 107 ∨ j = 108 ∨ j = 109 ∨ j = 110 ∨ j = 111 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 96=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 97=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 98=true) eligible).elim
  · exact checked8x99
  · exact ((by decide +kernel : ¬allowed 8 100=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 101=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 102=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 103=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 104=true) eligible).elim
  · exact checked8x105
  · exact ((by decide +kernel : ¬allowed 8 106=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 107=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 108=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 109=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 110=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 111=true) eligible).elim

end HalfIndexRows
