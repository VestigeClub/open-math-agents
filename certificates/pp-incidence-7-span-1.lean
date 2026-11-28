import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-7-group-4»
import certificates.«pp-incidence-7-group-5»
import certificates.«pp-incidence-7-group-6»
import certificates.«pp-incidence-7-group-7»
import certificates.«pp-incidence-7-group-8»

/-! Catalogue positions from 16 through 31. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block7x1 (j : ℕ) (lo : (16 : ℕ) ≤ j) (hi : j < 32)
    (eligible : allowed 7 j = true) : ∀ g, RowFact 7 j g := by
  have options : j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked7x16
  · exact checked7x17
  · exact checked7x18
  · exact checked7x19
  · exact checked7x20
  · exact checked7x21
  · exact checked7x22
  · exact checked7x23
  · exact checked7x24
  · exact checked7x25
  · exact checked7x26
  · exact checked7x27
  · exact checked7x28
  · exact checked7x29
  · exact checked7x30
  · exact checked7x31

end HalfIndexRows
