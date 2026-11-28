import certificates.«prime-table-67545646-94085731-conditional»
import certificates.«semiprime-correction-555157672301-small»

/-!
# Prime counts from 67,545,646 through 94,085,731

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ67545646To94085731

theorem lower_count : Nat.primeCounting 67545646=3982129 := by
  calc
    Nat.primeCounting 67545646 = RangePrimeA26.fast 67545646 :=
      (RangePrimeA26.fast_correct RankWheel34751.first_anchor _ (by decide) (by decide)).symm
    _ = 3982129 := by decide +kernel

theorem count_correct (n : ℕ) (low : 67545646≤n) (high : n≤94085731) :
    RangePrimeQ67545646To94085731.fast n=Nat.primeCounting n :=
  RangePrimeQ67545646To94085731.fast_correct lower_count n low high

end QuotientQ67545646To94085731
