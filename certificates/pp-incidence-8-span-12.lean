import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-18»
import certificates.«pp-incidence-8-group-19»
import certificates.«pp-incidence-8-group-20»

/-! Catalogue positions from 192 through 207. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x12 (j : ℕ) (lo : (192 : ℕ) ≤ j) (hi : j < 208)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 192 ∨ j = 193 ∨ j = 194 ∨ j = 195 ∨ j = 196 ∨ j = 197 ∨ j = 198 ∨ j = 199 ∨ j = 200 ∨ j = 201 ∨ j = 202 ∨ j = 203 ∨ j = 204 ∨ j = 205 ∨ j = 206 ∨ j = 207 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 192=true) eligible).elim
  · exact checked8x193
  · exact ((by decide +kernel : ¬allowed 8 194=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 195=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 196=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 197=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 198=true) eligible).elim
  · exact checked8x199
  · exact checked8x200
  · exact checked8x201
  · exact ((by decide +kernel : ¬allowed 8 202=true) eligible).elim
  · exact checked8x203
  · exact checked8x204
  · exact checked8x205
  · exact ((by decide +kernel : ¬allowed 8 206=true) eligible).elim
  · exact checked8x207

end HalfIndexRows
