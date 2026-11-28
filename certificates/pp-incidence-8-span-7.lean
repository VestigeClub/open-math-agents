import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-9»
import certificates.«pp-incidence-8-group-10»
import certificates.«pp-incidence-8-group-11»

/-! Catalogue positions from 112 through 127. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x7 (j : ℕ) (lo : (112 : ℕ) ≤ j) (hi : j < 128)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 112 ∨ j = 113 ∨ j = 114 ∨ j = 115 ∨ j = 116 ∨ j = 117 ∨ j = 118 ∨ j = 119 ∨ j = 120 ∨ j = 121 ∨ j = 122 ∨ j = 123 ∨ j = 124 ∨ j = 125 ∨ j = 126 ∨ j = 127 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked8x112
  · exact ((by decide +kernel : ¬allowed 8 113=true) eligible).elim
  · exact checked8x114
  · exact ((by decide +kernel : ¬allowed 8 115=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 116=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 117=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 118=true) eligible).elim
  · exact checked8x119
  · exact ((by decide +kernel : ¬allowed 8 120=true) eligible).elim
  · exact checked8x121
  · exact checked8x122
  · exact ((by decide +kernel : ¬allowed 8 123=true) eligible).elim
  · exact checked8x124
  · exact ((by decide +kernel : ¬allowed 8 125=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 126=true) eligible).elim
  · exact checked8x127

end HalfIndexRows
