import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-32»
import certificates.«pp-incidence-8-group-33»
import certificates.«pp-incidence-8-group-34»

/-! Catalogue positions from 336 through 351. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x21 (j : ℕ) (lo : (336 : ℕ) ≤ j) (hi : j < 352)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 336 ∨ j = 337 ∨ j = 338 ∨ j = 339 ∨ j = 340 ∨ j = 341 ∨ j = 342 ∨ j = 343 ∨ j = 344 ∨ j = 345 ∨ j = 346 ∨ j = 347 ∨ j = 348 ∨ j = 349 ∨ j = 350 ∨ j = 351 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked8x336
  · exact ((by decide +kernel : ¬allowed 8 337=true) eligible).elim
  · exact checked8x338
  · exact ((by decide +kernel : ¬allowed 8 339=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 340=true) eligible).elim
  · exact checked8x341
  · exact ((by decide +kernel : ¬allowed 8 342=true) eligible).elim
  · exact checked8x343
  · exact checked8x344
  · exact checked8x345
  · exact ((by decide +kernel : ¬allowed 8 346=true) eligible).elim
  · exact checked8x347
  · exact checked8x348
  · exact checked8x349
  · exact checked8x350
  · exact ((by decide +kernel : ¬allowed 8 351=true) eligible).elim

end HalfIndexRows
