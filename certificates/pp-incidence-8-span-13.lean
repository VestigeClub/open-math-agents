import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-20»
import certificates.«pp-incidence-8-group-21»

/-! Catalogue positions from 208 through 223. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x13 (j : ℕ) (lo : (208 : ℕ) ≤ j) (hi : j < 224)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 208 ∨ j = 209 ∨ j = 210 ∨ j = 211 ∨ j = 212 ∨ j = 213 ∨ j = 214 ∨ j = 215 ∨ j = 216 ∨ j = 217 ∨ j = 218 ∨ j = 219 ∨ j = 220 ∨ j = 221 ∨ j = 222 ∨ j = 223 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 208=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 209=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 210=true) eligible).elim
  · exact checked8x211
  · exact ((by decide +kernel : ¬allowed 8 212=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 213=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 214=true) eligible).elim
  · exact checked8x215
  · exact ((by decide +kernel : ¬allowed 8 216=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 217=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 218=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 219=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 220=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 221=true) eligible).elim
  · exact checked8x222
  · exact ((by decide +kernel : ¬allowed 8 223=true) eligible).elim

end HalfIndexRows
