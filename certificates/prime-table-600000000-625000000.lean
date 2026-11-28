import certificates.«prime-table-600000000-625000000-conditional»
import certificates.«prime-table-575000000-600000000»

/-!
# Prime counts from 600,000,000 through 625,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ600000000To625000000

theorem lower_count : Nat.primeCounting 600000000=31324703 := by
  calc
    Nat.primeCounting 600000000 = RangePrimeQ575000000To600000000.fast 600000000 :=
      (QuotientQ575000000To600000000.count_correct _ (by decide) (by decide)).symm
    _ = 31324703 := by decide +kernel

theorem count_correct (n : ℕ) (low : 600000000≤n) (high : n≤625000000) :
    RangePrimeQ600000000To625000000.fast n=Nat.primeCounting n :=
  RangePrimeQ600000000To625000000.fast_correct lower_count n low high

end QuotientQ600000000To625000000
