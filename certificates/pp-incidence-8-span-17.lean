import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-25»
import certificates.«pp-incidence-8-group-26»

/-! Catalogue positions from 272 through 287. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x17 (j : ℕ) (lo : (272 : ℕ) ≤ j) (hi : j < 288)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 272 ∨ j = 273 ∨ j = 274 ∨ j = 275 ∨ j = 276 ∨ j = 277 ∨ j = 278 ∨ j = 279 ∨ j = 280 ∨ j = 281 ∨ j = 282 ∨ j = 283 ∨ j = 284 ∨ j = 285 ∨ j = 286 ∨ j = 287 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 272=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 273=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 274=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 275=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 276=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 277=true) eligible).elim
  · exact checked8x278
  · exact checked8x279
  · exact checked8x280
  · exact checked8x281
  · exact ((by decide +kernel : ¬allowed 8 282=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 283=true) eligible).elim
  · exact checked8x284
  · exact ((by decide +kernel : ¬allowed 8 285=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 286=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 287=true) eligible).elim

end HalfIndexRows
