import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-21»
import certificates.«pp-incidence-8-group-22»

/-! Catalogue positions from 224 through 239. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x14 (j : ℕ) (lo : (224 : ℕ) ≤ j) (hi : j < 240)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 224 ∨ j = 225 ∨ j = 226 ∨ j = 227 ∨ j = 228 ∨ j = 229 ∨ j = 230 ∨ j = 231 ∨ j = 232 ∨ j = 233 ∨ j = 234 ∨ j = 235 ∨ j = 236 ∨ j = 237 ∨ j = 238 ∨ j = 239 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 224=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 225=true) eligible).elim
  · exact checked8x226
  · exact checked8x227
  · exact ((by decide +kernel : ¬allowed 8 228=true) eligible).elim
  · exact checked8x229
  · exact checked8x230
  · exact checked8x231
  · exact ((by decide +kernel : ¬allowed 8 232=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 233=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 234=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 235=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 236=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 237=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 238=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 239=true) eligible).elim

end HalfIndexRows
