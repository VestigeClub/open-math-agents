import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-7-group-24»
import certificates.«pp-incidence-7-group-25»
import certificates.«pp-incidence-7-group-26»
import certificates.«pp-incidence-7-group-27»

/-! Catalogue positions from 96 through 107. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block7x6 (j : ℕ) (lo : (96 : ℕ) ≤ j) (hi : j < 108)
    (eligible : allowed 7 j = true) : ∀ g, RowFact 7 j g := by
  have options : j = 96 ∨ j = 97 ∨ j = 98 ∨ j = 99 ∨ j = 100 ∨ j = 101 ∨ j = 102 ∨ j = 103 ∨ j = 104 ∨ j = 105 ∨ j = 106 ∨ j = 107 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked7x96
  · exact checked7x97
  · exact checked7x98
  · exact checked7x99
  · exact checked7x100
  · exact checked7x101
  · exact checked7x102
  · exact checked7x103
  · exact checked7x104
  · exact checked7x105
  · exact checked7x106
  · exact checked7x107

end HalfIndexRows
