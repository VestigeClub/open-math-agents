import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-7»
import certificates.«pp-incidence-8-group-8»

/-! Catalogue positions from 80 through 95. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x5 (j : ℕ) (lo : (80 : ℕ) ≤ j) (hi : j < 96)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨ j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 ∨ j = 89 ∨ j = 90 ∨ j = 91 ∨ j = 92 ∨ j = 93 ∨ j = 94 ∨ j = 95 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 80=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 81=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 82=true) eligible).elim
  · exact checked8x83
  · exact ((by decide +kernel : ¬allowed 8 84=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 85=true) eligible).elim
  · exact checked8x86
  · exact checked8x87
  · exact checked8x88
  · exact ((by decide +kernel : ¬allowed 8 89=true) eligible).elim
  · exact checked8x90
  · exact ((by decide +kernel : ¬allowed 8 91=true) eligible).elim
  · exact checked8x92
  · exact ((by decide +kernel : ¬allowed 8 93=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 94=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 95=true) eligible).elim

end HalfIndexRows
