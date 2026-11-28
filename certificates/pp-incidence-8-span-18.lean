import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-26»
import certificates.«pp-incidence-8-group-27»

/-! Catalogue positions from 288 through 303. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x18 (j : ℕ) (lo : (288 : ℕ) ≤ j) (hi : j < 304)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 288 ∨ j = 289 ∨ j = 290 ∨ j = 291 ∨ j = 292 ∨ j = 293 ∨ j = 294 ∨ j = 295 ∨ j = 296 ∨ j = 297 ∨ j = 298 ∨ j = 299 ∨ j = 300 ∨ j = 301 ∨ j = 302 ∨ j = 303 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked8x288
  · exact ((by decide +kernel : ¬allowed 8 289=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 290=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 291=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 292=true) eligible).elim
  · exact checked8x293
  · exact checked8x294
  · exact ((by decide +kernel : ¬allowed 8 295=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 296=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 297=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 298=true) eligible).elim
  · exact checked8x299
  · exact ((by decide +kernel : ¬allowed 8 300=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 301=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 302=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 303=true) eligible).elim

end HalfIndexRows
