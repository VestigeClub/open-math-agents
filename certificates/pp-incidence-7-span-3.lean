import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-7-group-12»
import certificates.«pp-incidence-7-group-13»
import certificates.«pp-incidence-7-group-14»
import certificates.«pp-incidence-7-group-15»
import certificates.«pp-incidence-7-group-16»

/-! Catalogue positions from 48 through 63. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block7x3 (j : ℕ) (lo : (48 : ℕ) ≤ j) (hi : j < 64)
    (eligible : allowed 7 j = true) : ∀ g, RowFact 7 j g := by
  have options : j = 48 ∨ j = 49 ∨ j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨ j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 ∨ j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked7x48
  · exact checked7x49
  · exact checked7x50
  · exact checked7x51
  · exact checked7x52
  · exact checked7x53
  · exact checked7x54
  · exact checked7x55
  · exact checked7x56
  · exact checked7x57
  · exact checked7x58
  · exact checked7x59
  · exact checked7x60
  · exact checked7x61
  · exact checked7x62
  · exact checked7x63

end HalfIndexRows
