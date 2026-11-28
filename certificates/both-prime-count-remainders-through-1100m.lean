import certificates.«eighth-final-ninety-four-sieve-steps»
import certificates.«seventh-prime-count-sieve-criterion»
import certificates.«seventh-sieve-final-1154-prime-steps»
import certificates.«tail-series-11092009835083-10079-10313»
import certificates.«tail-series-11092009835083-10313-10559»
import certificates.«tail-series-11092009835083-10559-10799»
import certificates.«tail-series-11092009835083-10799-11087»
import certificates.«tail-series-30110134441897-27367-28001»
import certificates.«tail-series-30110134441897-28001-28669»
import certificates.«tail-series-30110134441897-28669-29363»
import certificates.«tail-series-30110134441897-29363-30109»

/-! Exact removals and reduced survivor residues for the two remaining prime counts in the A247824 exclusion. -/

namespace RankSieveRanges
open FinalSeventhSieve

private theorem first_rank_residue {x y : ℕ} (h : SeventhEndpointSieve.criterion x y) :
    Nat.primeCounting x % 9=7 ↔ rough x y % 9=1 := by
  unfold SeventhEndpointSieve.criterion at h
  exact h.2.1

private theorem from11092009835083at10079to10559 : rough 11092009835083 10559+3218331335=rough 11092009835083 10079 :=
  LargeQuotientSieve.combine TailSeries11092009835083From10079To10313.change TailSeries11092009835083From10313To10559.change rfl

private theorem from11092009835083at10079to10799 : rough 11092009835083 10799+4761202072=rough 11092009835083 10079 :=
  LargeQuotientSieve.combine from11092009835083at10079to10559 TailSeries11092009835083From10559To10799.change rfl

private theorem from11092009835083at10079to11087 : rough 11092009835083 11087+6432375437=rough 11092009835083 10079 :=
  LargeQuotientSieve.combine from11092009835083at10079to10799 TailSeries11092009835083From10799To11087.change rfl

theorem removed_seventh : rough 11092009835083 22301+49690371951=rough 11092009835083 10079 :=
  LargeQuotientSieve.combine from11092009835083at10079to11087 FinalSeventhSieve.last_1154_by_intervals rfl

theorem residue_11092009835083 : Nat.primeCounting 11092009835083 % 9 = 7 ↔ rough 11092009835083 10079 % 9 = 1 := by
  have base : Nat.primeCounting 11092009835083 % 9 = 7 ↔ rough 11092009835083 22301 % 9 = 1 := first_rank_residue SeventhEndpointSieve.prime_count_and_residue
  have change := removed_seventh
  exact base.trans (by omega)

private theorem from30110134441897at27367to28669 : rough 30110134441897 28669+7153180692=rough 30110134441897 27367 :=
  LargeQuotientSieve.combine TailSeries30110134441897From27367To28001.change TailSeries30110134441897From28001To28669.change rfl

private theorem from30110134441897at27367to29363 : rough 30110134441897 29363+10634447982=rough 30110134441897 27367 :=
  LargeQuotientSieve.combine from30110134441897at27367to28669 TailSeries30110134441897From28669To29363.change rfl

private theorem from30110134441897at27367to30109 : rough 30110134441897 30109+14033472518=rough 30110134441897 27367 :=
  LargeQuotientSieve.combine from30110134441897at27367to29363 TailSeries30110134441897From29363To30109.change rfl

theorem removed_eighth : rough 30110134441897 31110+18740406464=rough 30110134441897 27367 :=
  LargeQuotientSieve.combine from30110134441897at27367to30109 EighthEndpointSieve.final_ninety_four rfl

theorem residue_30110134441897 : Nat.primeCounting 30110134441897 % 5 = 3 ↔ rough 30110134441897 27367 % 5 = 2 := by
  have base : Nat.primeCounting 30110134441897 % 5 = 3 ↔ rough 30110134441897 30109 % 5 = 4 := EighthEndpointSieve.residue_at_30109
  have change := from30110134441897at27367to30109
  exact base.trans (by omega)

theorem both_residues :
    (Nat.primeCounting 11092009835083 % 9 = 7 ↔ rough 11092009835083 10079 % 9 = 1) ∧
    (Nat.primeCounting 30110134441897 % 5 = 3 ↔ rough 30110134441897 27367 % 5 = 2) :=
  ⟨residue_11092009835083,residue_30110134441897⟩

end RankSieveRanges
