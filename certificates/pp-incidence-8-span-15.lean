import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-22»
import certificates.«pp-incidence-8-group-23»

/-! Catalogue positions from 240 through 255. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x15 (j : ℕ) (lo : (240 : ℕ) ≤ j) (hi : j < 256)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 240 ∨ j = 241 ∨ j = 242 ∨ j = 243 ∨ j = 244 ∨ j = 245 ∨ j = 246 ∨ j = 247 ∨ j = 248 ∨ j = 249 ∨ j = 250 ∨ j = 251 ∨ j = 252 ∨ j = 253 ∨ j = 254 ∨ j = 255 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked8x240
  · exact ((by decide +kernel : ¬allowed 8 241=true) eligible).elim
  · exact checked8x242
  · exact ((by decide +kernel : ¬allowed 8 243=true) eligible).elim
  · exact checked8x244
  · exact ((by decide +kernel : ¬allowed 8 245=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 246=true) eligible).elim
  · exact checked8x247
  · exact ((by decide +kernel : ¬allowed 8 248=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 249=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 250=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 251=true) eligible).elim
  · exact checked8x252
  · exact ((by decide +kernel : ¬allowed 8 253=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 254=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 255=true) eligible).elim

end HalfIndexRows
