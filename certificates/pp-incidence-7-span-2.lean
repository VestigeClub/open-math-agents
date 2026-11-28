import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-7-group-8»
import certificates.«pp-incidence-7-group-9»
import certificates.«pp-incidence-7-group-10»
import certificates.«pp-incidence-7-group-11»
import certificates.«pp-incidence-7-group-12»

/-! Catalogue positions from 32 through 47. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block7x2 (j : ℕ) (lo : (32 : ℕ) ≤ j) (hi : j < 48)
    (eligible : allowed 7 j = true) : ∀ g, RowFact 7 j g := by
  have options : j = 32 ∨ j = 33 ∨ j = 34 ∨ j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 ∨ j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨ j = 45 ∨ j = 46 ∨ j = 47 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked7x32
  · exact checked7x33
  · exact checked7x34
  · exact checked7x35
  · exact checked7x36
  · exact checked7x37
  · exact checked7x38
  · exact checked7x39
  · exact checked7x40
  · exact checked7x41
  · exact checked7x42
  · exact checked7x43
  · exact checked7x44
  · exact checked7x45
  · exact checked7x46
  · exact checked7x47

end HalfIndexRows
