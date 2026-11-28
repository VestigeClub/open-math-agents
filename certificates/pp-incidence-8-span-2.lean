import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-3»
import certificates.«pp-incidence-8-group-4»
import certificates.«pp-incidence-8-group-5»

/-! Catalogue positions from 32 through 47. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x2 (j : ℕ) (lo : (32 : ℕ) ≤ j) (hi : j < 48)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 32 ∨ j = 33 ∨ j = 34 ∨ j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 ∨ j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨ j = 45 ∨ j = 46 ∨ j = 47 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 32=true) eligible).elim
  · exact checked8x33
  · exact ((by decide +kernel : ¬allowed 8 34=true) eligible).elim
  · exact checked8x35
  · exact checked8x36
  · exact checked8x37
  · exact checked8x38
  · exact checked8x39
  · exact checked8x40
  · exact ((by decide +kernel : ¬allowed 8 41=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 42=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 43=true) eligible).elim
  · exact checked8x44
  · exact ((by decide +kernel : ¬allowed 8 45=true) eligible).elim
  · exact checked8x46
  · exact ((by decide +kernel : ¬allowed 8 47=true) eligible).elim

end HalfIndexRows
