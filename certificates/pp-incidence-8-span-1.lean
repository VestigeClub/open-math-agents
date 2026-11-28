import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-2»

/-! Catalogue positions from 16 through 31. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x1 (j : ℕ) (lo : (16 : ℕ) ≤ j) (hi : j < 32)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 16=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 17=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 18=true) eligible).elim
  · exact checked8x19
  · exact ((by decide +kernel : ¬allowed 8 20=true) eligible).elim
  · exact checked8x21
  · exact ((by decide +kernel : ¬allowed 8 22=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 23=true) eligible).elim
  · exact checked8x24
  · exact ((by decide +kernel : ¬allowed 8 25=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 26=true) eligible).elim
  · exact checked8x27
  · exact ((by decide +kernel : ¬allowed 8 28=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 29=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 30=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 31=true) eligible).elim

end HalfIndexRows
