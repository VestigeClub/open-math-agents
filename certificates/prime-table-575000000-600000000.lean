import certificates.«prime-table-575000000-600000000-conditional»
import certificates.«prime-table-550000000-575000000»

/-!
# Prime counts from 575,000,000 through 600,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ575000000To600000000

theorem lower_count : Nat.primeCounting 575000000=30086302 := by
  calc
    Nat.primeCounting 575000000 = RangePrimeQ550000000To575000000.fast 575000000 :=
      (QuotientQ550000000To575000000.count_correct _ (by decide) (by decide)).symm
    _ = 30086302 := by decide +kernel

theorem count_correct (n : ℕ) (low : 575000000≤n) (high : n≤600000000) :
    RangePrimeQ575000000To600000000.fast n=Nat.primeCounting n :=
  RangePrimeQ575000000To600000000.fast_correct lower_count n low high

end QuotientQ575000000To600000000
