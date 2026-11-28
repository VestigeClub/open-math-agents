import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-13»
import certificates.«pp-incidence-8-group-14»
import certificates.«pp-incidence-8-group-15»
import certificates.«pp-incidence-8-group-16»

/-! Catalogue positions from 160 through 175. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x10 (j : ℕ) (lo : (160 : ℕ) ≤ j) (hi : j < 176)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 160 ∨ j = 161 ∨ j = 162 ∨ j = 163 ∨ j = 164 ∨ j = 165 ∨ j = 166 ∨ j = 167 ∨ j = 168 ∨ j = 169 ∨ j = 170 ∨ j = 171 ∨ j = 172 ∨ j = 173 ∨ j = 174 ∨ j = 175 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked8x160
  · exact ((by decide +kernel : ¬allowed 8 161=true) eligible).elim
  · exact checked8x162
  · exact checked8x163
  · exact checked8x164
  · exact checked8x165
  · exact checked8x166
  · exact ((by decide +kernel : ¬allowed 8 167=true) eligible).elim
  · exact checked8x168
  · exact ((by decide +kernel : ¬allowed 8 169=true) eligible).elim
  · exact checked8x170
  · exact checked8x171
  · exact checked8x172
  · exact ((by decide +kernel : ¬allowed 8 173=true) eligible).elim
  · exact checked8x174
  · exact checked8x175

end HalfIndexRows
