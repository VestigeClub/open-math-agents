import certificates.«prime-table-975000000-1000000000-conditional»
import certificates.«prime-table-950000000-975000000»

/-!
# Prime counts from 975,000,000 through 1,000,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ975000000To1000000000

theorem lower_count : Nat.primeCounting 975000000=49640342 := by
  calc
    Nat.primeCounting 975000000 = RangePrimeQ950000000To975000000.fast 975000000 :=
      (QuotientQ950000000To975000000.count_correct _ (by decide) (by decide)).symm
    _ = 49640342 := by decide +kernel

theorem count_correct (n : ℕ) (low : 975000000≤n) (high : n≤1000000000) :
    RangePrimeQ975000000To1000000000.fast n=Nat.primeCounting n :=
  RangePrimeQ975000000To1000000000.fast_correct lower_count n low high

end QuotientQ975000000To1000000000
