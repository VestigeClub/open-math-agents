import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-7-group-0»
import certificates.«pp-incidence-7-group-1»
import certificates.«pp-incidence-7-group-2»
import certificates.«pp-incidence-7-group-3»
import certificates.«pp-incidence-7-group-4»

/-! Catalogue positions from 0 through 15. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block7x0 (j : ℕ) (lo : (0 : ℕ) ≤ j) (hi : j < 16)
    (eligible : allowed 7 j = true) : ∀ g, RowFact 7 j g := by
  have options : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked7x0
  · exact checked7x1
  · exact checked7x2
  · exact checked7x3
  · exact checked7x4
  · exact checked7x5
  · exact checked7x6
  · exact checked7x7
  · exact checked7x8
  · exact checked7x9
  · exact checked7x10
  · exact checked7x11
  · exact checked7x12
  · exact checked7x13
  · exact checked7x14
  · exact checked7x15

end HalfIndexRows
