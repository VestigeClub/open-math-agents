import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-7-group-16»
import certificates.«pp-incidence-7-group-17»
import certificates.«pp-incidence-7-group-18»
import certificates.«pp-incidence-7-group-19»
import certificates.«pp-incidence-7-group-20»

/-! Catalogue positions from 64 through 79. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block7x4 (j : ℕ) (lo : (64 : ℕ) ≤ j) (hi : j < 80)
    (eligible : allowed 7 j = true) : ∀ g, RowFact 7 j g := by
  have options : j = 64 ∨ j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 ∨ j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨ j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked7x64
  · exact checked7x65
  · exact checked7x66
  · exact checked7x67
  · exact checked7x68
  · exact checked7x69
  · exact checked7x70
  · exact checked7x71
  · exact checked7x72
  · exact checked7x73
  · exact checked7x74
  · exact checked7x75
  · exact checked7x76
  · exact checked7x77
  · exact checked7x78
  · exact checked7x79

end HalfIndexRows
