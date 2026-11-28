import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-24»
import certificates.«pp-incidence-8-group-25»

/-! Catalogue positions from 256 through 271. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x16 (j : ℕ) (lo : (256 : ℕ) ≤ j) (hi : j < 272)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 256 ∨ j = 257 ∨ j = 258 ∨ j = 259 ∨ j = 260 ∨ j = 261 ∨ j = 262 ∨ j = 263 ∨ j = 264 ∨ j = 265 ∨ j = 266 ∨ j = 267 ∨ j = 268 ∨ j = 269 ∨ j = 270 ∨ j = 271 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked8x256
  · exact ((by decide +kernel : ¬allowed 8 257=true) eligible).elim
  · exact checked8x258
  · exact ((by decide +kernel : ¬allowed 8 259=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 260=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 261=true) eligible).elim
  · exact checked8x262
  · exact ((by decide +kernel : ¬allowed 8 263=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 264=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 265=true) eligible).elim
  · exact checked8x266
  · exact ((by decide +kernel : ¬allowed 8 267=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 268=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 269=true) eligible).elim
  · exact checked8x270
  · exact checked8x271

end HalfIndexRows
