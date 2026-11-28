import certificates.«prime-table-245000000-270000000-conditional»
import certificates.«prime-table-220000000-245000000»

/-!
# Prime counts from 245,000,000 through 270,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ245000000To270000000

theorem lower_count : Nat.primeCounting 245000000=13420660 := by
  calc
    Nat.primeCounting 245000000 = RangePrimeQ220000000To245000000.fast 245000000 :=
      (QuotientQ220000000To245000000.count_correct _ (by decide) (by decide)).symm
    _ = 13420660 := by decide +kernel

theorem count_correct (n : ℕ) (low : 245000000≤n) (high : n≤270000000) :
    RangePrimeQ245000000To270000000.fast n=Nat.primeCounting n :=
  RangePrimeQ245000000To270000000.fast_correct lower_count n low high

end QuotientQ245000000To270000000
