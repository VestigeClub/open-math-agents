import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-27»
import certificates.«pp-incidence-8-group-28»
import certificates.«pp-incidence-8-group-29»
import certificates.«pp-incidence-8-group-30»

/-! Catalogue positions from 304 through 319. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x19 (j : ℕ) (lo : (304 : ℕ) ≤ j) (hi : j < 320)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 304 ∨ j = 305 ∨ j = 306 ∨ j = 307 ∨ j = 308 ∨ j = 309 ∨ j = 310 ∨ j = 311 ∨ j = 312 ∨ j = 313 ∨ j = 314 ∨ j = 315 ∨ j = 316 ∨ j = 317 ∨ j = 318 ∨ j = 319 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 304=true) eligible).elim
  · exact checked8x305
  · exact ((by decide +kernel : ¬allowed 8 306=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 307=true) eligible).elim
  · exact checked8x308
  · exact ((by decide +kernel : ¬allowed 8 309=true) eligible).elim
  · exact checked8x310
  · exact checked8x311
  · exact checked8x312
  · exact checked8x313
  · exact checked8x314
  · exact checked8x315
  · exact checked8x316
  · exact ((by decide +kernel : ¬allowed 8 317=true) eligible).elim
  · exact checked8x318
  · exact ((by decide +kernel : ¬allowed 8 319=true) eligible).elim

end HalfIndexRows
