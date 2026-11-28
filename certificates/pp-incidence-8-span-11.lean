import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-16»
import certificates.«pp-incidence-8-group-17»
import certificates.«pp-incidence-8-group-18»

/-! Catalogue positions from 176 through 191. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x11 (j : ℕ) (lo : (176 : ℕ) ≤ j) (hi : j < 192)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 176 ∨ j = 177 ∨ j = 178 ∨ j = 179 ∨ j = 180 ∨ j = 181 ∨ j = 182 ∨ j = 183 ∨ j = 184 ∨ j = 185 ∨ j = 186 ∨ j = 187 ∨ j = 188 ∨ j = 189 ∨ j = 190 ∨ j = 191 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked8x176
  · exact checked8x177
  · exact ((by decide +kernel : ¬allowed 8 178=true) eligible).elim
  · exact checked8x179
  · exact checked8x180
  · exact ((by decide +kernel : ¬allowed 8 181=true) eligible).elim
  · exact checked8x182
  · exact ((by decide +kernel : ¬allowed 8 183=true) eligible).elim
  · exact checked8x184
  · exact checked8x185
  · exact checked8x186
  · exact checked8x187
  · exact ((by decide +kernel : ¬allowed 8 188=true) eligible).elim
  · exact checked8x189
  · exact ((by decide +kernel : ¬allowed 8 190=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 191=true) eligible).elim

end HalfIndexRows
