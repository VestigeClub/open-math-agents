import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-7-group-20»
import certificates.«pp-incidence-7-group-21»
import certificates.«pp-incidence-7-group-22»
import certificates.«pp-incidence-7-group-23»
import certificates.«pp-incidence-7-group-24»

/-! Catalogue positions from 80 through 95. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block7x5 (j : ℕ) (lo : (80 : ℕ) ≤ j) (hi : j < 96)
    (eligible : allowed 7 j = true) : ∀ g, RowFact 7 j g := by
  have options : j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨ j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 ∨ j = 89 ∨ j = 90 ∨ j = 91 ∨ j = 92 ∨ j = 93 ∨ j = 94 ∨ j = 95 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked7x80
  · exact checked7x81
  · exact checked7x82
  · exact checked7x83
  · exact checked7x84
  · exact checked7x85
  · exact checked7x86
  · exact checked7x87
  · exact checked7x88
  · exact checked7x89
  · exact checked7x90
  · exact checked7x91
  · exact checked7x92
  · exact checked7x93
  · exact checked7x94
  · exact checked7x95

end HalfIndexRows
