import certificates.«pp-final-conditional»
import certificates.«pp-incidence-7-span-0»
import certificates.«pp-incidence-7-span-1»
import certificates.«pp-incidence-7-span-2»
import certificates.«pp-incidence-7-span-3»
import certificates.«pp-incidence-7-span-4»
import certificates.«pp-incidence-7-span-5»
import certificates.«pp-incidence-7-span-6»
import certificates.«pp-incidence-8-span-0»
import certificates.«pp-incidence-8-span-1»
import certificates.«pp-incidence-8-span-2»
import certificates.«pp-incidence-8-span-3»
import certificates.«pp-incidence-8-span-4»
import certificates.«pp-incidence-8-span-5»
import certificates.«pp-incidence-8-span-6»
import certificates.«pp-incidence-8-span-7»
import certificates.«pp-incidence-8-span-8»
import certificates.«pp-incidence-8-span-9»
import certificates.«pp-incidence-8-span-10»
import certificates.«pp-incidence-8-span-11»
import certificates.«pp-incidence-8-span-12»
import certificates.«pp-incidence-8-span-13»
import certificates.«pp-incidence-8-span-14»
import certificates.«pp-incidence-8-span-15»
import certificates.«pp-incidence-8-span-16»
import certificates.«pp-incidence-8-span-17»
import certificates.«pp-incidence-8-span-18»
import certificates.«pp-incidence-8-span-19»
import certificates.«pp-incidence-8-span-20»
import certificates.«pp-incidence-8-span-21»
import certificates.«pp-incidence-8-span-22»
import certificates.«pp-incidence-8-span-23»

/-!
# Prime factors of boards with fourteen through seventeen cells

For a fourteen-cell board the only proper prime factor areas are two and seven.
A seven-cell factor tiles in two copies. Connectivity makes those copies touch,
so anchoring one of them leaves a finite list of placements for the other.
The verified catalogue puts the seven-cell factors of each board in a list of
length nine. The domino supplies at most one additional factor.

For sixteen cells the smaller prime factors are the domino and the T tetromino.
For every possible placement of two copies of a prime octomino, the catalogue
gives at most ten possible octominoes, except at one canonical board key. At
that key the placement is proved congruent to a specific board, its list has
length twelve, and neither of the smaller prime factors can tile it.

Explicit boards attain the bounds. The fifteen- and seventeen-cell maxima are
proved in the imported development using the same definitions of factor and
congruence. Rotations and reflections are allowed.
-/

open OMA.S_oeis_a380455
namespace PrimePolyFactor

private theorem size7 (j : ℕ) (bound : j < HalfCatalogue.count 7)
    (eligible : HalfPrimes.allowed 7 j = true) : ∀ g, HalfIncidence.RowFact 7 j g := by
  change j < 108 at bound
  by_cases h0 : j < 16
  · exact HalfIndexRows.block7x0 j (by omega) h0 eligible
  by_cases h1 : j < 32
  · exact HalfIndexRows.block7x1 j (by omega) h1 eligible
  by_cases h2 : j < 48
  · exact HalfIndexRows.block7x2 j (by omega) h2 eligible
  by_cases h3 : j < 64
  · exact HalfIndexRows.block7x3 j (by omega) h3 eligible
  by_cases h4 : j < 80
  · exact HalfIndexRows.block7x4 j (by omega) h4 eligible
  by_cases h5 : j < 96
  · exact HalfIndexRows.block7x5 j (by omega) h5 eligible
  exact HalfIndexRows.block7x6 j (by omega) bound eligible

private theorem size8 (j : ℕ) (bound : j < HalfCatalogue.count 8)
    (eligible : HalfPrimes.allowed 8 j = true) : ∀ g, HalfIncidence.RowFact 8 j g := by
  change j < 369 at bound
  by_cases h0 : j < 16
  · exact HalfIndexRows.block8x0 j (by omega) h0 eligible
  by_cases h1 : j < 32
  · exact HalfIndexRows.block8x1 j (by omega) h1 eligible
  by_cases h2 : j < 48
  · exact HalfIndexRows.block8x2 j (by omega) h2 eligible
  by_cases h3 : j < 64
  · exact HalfIndexRows.block8x3 j (by omega) h3 eligible
  by_cases h4 : j < 80
  · exact HalfIndexRows.block8x4 j (by omega) h4 eligible
  by_cases h5 : j < 96
  · exact HalfIndexRows.block8x5 j (by omega) h5 eligible
  by_cases h6 : j < 112
  · exact HalfIndexRows.block8x6 j (by omega) h6 eligible
  by_cases h7 : j < 128
  · exact HalfIndexRows.block8x7 j (by omega) h7 eligible
  by_cases h8 : j < 144
  · exact HalfIndexRows.block8x8 j (by omega) h8 eligible
  by_cases h9 : j < 160
  · exact HalfIndexRows.block8x9 j (by omega) h9 eligible
  by_cases h10 : j < 176
  · exact HalfIndexRows.block8x10 j (by omega) h10 eligible
  by_cases h11 : j < 192
  · exact HalfIndexRows.block8x11 j (by omega) h11 eligible
  by_cases h12 : j < 208
  · exact HalfIndexRows.block8x12 j (by omega) h12 eligible
  by_cases h13 : j < 224
  · exact HalfIndexRows.block8x13 j (by omega) h13 eligible
  by_cases h14 : j < 240
  · exact HalfIndexRows.block8x14 j (by omega) h14 eligible
  by_cases h15 : j < 256
  · exact HalfIndexRows.block8x15 j (by omega) h15 eligible
  by_cases h16 : j < 272
  · exact HalfIndexRows.block8x16 j (by omega) h16 eligible
  by_cases h17 : j < 288
  · exact HalfIndexRows.block8x17 j (by omega) h17 eligible
  by_cases h18 : j < 304
  · exact HalfIndexRows.block8x18 j (by omega) h18 eligible
  by_cases h19 : j < 320
  · exact HalfIndexRows.block8x19 j (by omega) h19 eligible
  by_cases h20 : j < 336
  · exact HalfIndexRows.block8x20 j (by omega) h20 eligible
  by_cases h21 : j < 352
  · exact HalfIndexRows.block8x21 j (by omega) h21 eligible
  by_cases h22 : j < 368
  · exact HalfIndexRows.block8x22 j (by omega) h22 eligible
  exact HalfIndexRows.block8x23 j (by omega) bound eligible

theorem all_half_area_placements : HalfFinal.AllRows := by
  intro half id sizes bound eligible
  rcases sizes with rfl|rfl
  · exact size7 id bound eligible
  · exact size8 id bound eligible

theorem exact_fourteen_cells : maximum 14 10 :=
  HalfFinal.exact_fourteen all_half_area_placements

theorem exact_sixteen_cells : maximum 16 12 :=
  HalfFinal.exact_sixteen all_half_area_placements

theorem a380455_four_maxima :
    maximum 14 10 ∧ maximum 15 3 ∧ maximum 16 12 ∧ maximum 17 1 :=
  HalfFinal.all_four all_half_area_placements

end PrimePolyFactor
