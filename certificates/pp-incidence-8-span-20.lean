import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-30»
import certificates.«pp-incidence-8-group-31»
import certificates.«pp-incidence-8-group-32»

/-! Catalogue positions from 320 through 335. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x20 (j : ℕ) (lo : (320 : ℕ) ≤ j) (hi : j < 336)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 320 ∨ j = 321 ∨ j = 322 ∨ j = 323 ∨ j = 324 ∨ j = 325 ∨ j = 326 ∨ j = 327 ∨ j = 328 ∨ j = 329 ∨ j = 330 ∨ j = 331 ∨ j = 332 ∨ j = 333 ∨ j = 334 ∨ j = 335 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 320=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 321=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 322=true) eligible).elim
  · exact checked8x323
  · exact ((by decide +kernel : ¬allowed 8 324=true) eligible).elim
  · exact checked8x325
  · exact checked8x326
  · exact checked8x327
  · exact ((by decide +kernel : ¬allowed 8 328=true) eligible).elim
  · exact checked8x329
  · exact ((by decide +kernel : ¬allowed 8 330=true) eligible).elim
  · exact checked8x331
  · exact ((by decide +kernel : ¬allowed 8 332=true) eligible).elim
  · exact checked8x333
  · exact ((by decide +kernel : ¬allowed 8 334=true) eligible).elim
  · exact checked8x335

end HalfIndexRows
