import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-11»

/-! Catalogue positions from 128 through 143. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x8 (j : ℕ) (lo : (128 : ℕ) ≤ j) (hi : j < 144)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 128 ∨ j = 129 ∨ j = 130 ∨ j = 131 ∨ j = 132 ∨ j = 133 ∨ j = 134 ∨ j = 135 ∨ j = 136 ∨ j = 137 ∨ j = 138 ∨ j = 139 ∨ j = 140 ∨ j = 141 ∨ j = 142 ∨ j = 143 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 128=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 129=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 130=true) eligible).elim
  · exact checked8x131
  · exact ((by decide +kernel : ¬allowed 8 132=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 133=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 134=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 135=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 136=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 137=true) eligible).elim
  · exact checked8x138
  · exact ((by decide +kernel : ¬allowed 8 139=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 140=true) eligible).elim
  · exact checked8x141
  · exact ((by decide +kernel : ¬allowed 8 142=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 143=true) eligible).elim

end HalfIndexRows
