import certificates.«pp-primes-candidates-b»
import certificates.«pp-incidence-8-group-12»
import certificates.«pp-incidence-8-group-13»

/-! Catalogue positions from 144 through 159. -/

open PrimePolyFactor HalfCatalogue HalfIncidence HalfPrimes

namespace HalfIndexRows

theorem block8x9 (j : ℕ) (lo : (144 : ℕ) ≤ j) (hi : j < 160)
    (eligible : allowed 8 j = true) : ∀ g, RowFact 8 j g := by
  have options : j = 144 ∨ j = 145 ∨ j = 146 ∨ j = 147 ∨ j = 148 ∨ j = 149 ∨ j = 150 ∨ j = 151 ∨ j = 152 ∨ j = 153 ∨ j = 154 ∨ j = 155 ∨ j = 156 ∨ j = 157 ∨ j = 158 ∨ j = 159 := by omega
  rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ((by decide +kernel : ¬allowed 8 144=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 145=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 146=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 147=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 148=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 149=true) eligible).elim
  · exact checked8x150
  · exact ((by decide +kernel : ¬allowed 8 151=true) eligible).elim
  · exact checked8x152
  · exact ((by decide +kernel : ¬allowed 8 153=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 154=true) eligible).elim
  · exact ((by decide +kernel : ¬allowed 8 155=true) eligible).elim
  · exact checked8x156
  · exact ((by decide +kernel : ¬allowed 8 157=true) eligible).elim
  · exact checked8x158
  · exact checked8x159

end HalfIndexRows
