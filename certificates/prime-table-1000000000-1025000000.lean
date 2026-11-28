import certificates.«prime-table-1000000000-1025000000-conditional»
import certificates.«prime-table-975000000-1000000000»

/-!
# Prime counts from 1,000,000,000 through 1,025,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ1000000000To1025000000

theorem lower_count : Nat.primeCounting 1000000000=50847534 := by
  calc
    Nat.primeCounting 1000000000 = RangePrimeQ975000000To1000000000.fast 1000000000 :=
      (QuotientQ975000000To1000000000.count_correct _ (by decide) (by decide)).symm
    _ = 50847534 := by decide +kernel

theorem count_correct (n : ℕ) (low : 1000000000≤n) (high : n≤1025000000) :
    RangePrimeQ1000000000To1025000000.fast n=Nat.primeCounting n :=
  RangePrimeQ1000000000To1025000000.fast_correct lower_count n low high

end QuotientQ1000000000To1025000000
