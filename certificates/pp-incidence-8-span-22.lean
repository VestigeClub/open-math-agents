import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-34»
import certificates.«pp-incidence-8-group-35»
import certificates.«pp-incidence-8-group-36»

/-! Catalogue positions from 352 through 367. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x22 (j : ℕ) (lo : (352 : ℕ) ≤ j) (hi : j < 368)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 352 ∨ j = 353 ∨ j = 354 ∨ j = 355 ∨ j = 356 ∨ j = 357 ∨ j = 358 ∨ j = 359 ∨ j = 360 ∨ j = 361 ∨ j = 362 ∨ j = 363 ∨ j = 364 ∨ j = 365 ∨ j = 366 ∨ j = 367 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked8x352
  · exact checked8x353
  · exact checked8x354
  · exact checked8x355
  · exact checked8x356
  · exact checked8x357
  · exact ((by decide +kernel : ¬allowed 8 358=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 359=true) eligible).elim
  · exact checked8x360
  · exact ((by decide +kernel : ¬allowed 8 361=true) eligible).elim
  · exact checked8x362
  · exact ((by decide +kernel : ¬allowed 8 363=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 364=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 365=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 366=true) eligible).elim
  · exact checked8x367

end HalfIndexRows
