import certificates.«prime-table-800000000-825000000-conditional»
import certificates.«prime-table-775000000-800000000»

/-!
# Prime counts from 800,000,000 through 825,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ800000000To825000000

theorem lower_count : Nat.primeCounting 800000000=41146179 := by
  calc
    Nat.primeCounting 800000000 = RangePrimeQ775000000To800000000.fast 800000000 :=
      (QuotientQ775000000To800000000.count_correct _ (by decide) (by decide)).symm
    _ = 41146179 := by decide +kernel

theorem count_correct (n : ℕ) (low : 800000000≤n) (high : n≤825000000) :
    RangePrimeQ800000000To825000000.fast n=Nat.primeCounting n :=
  RangePrimeQ800000000To825000000.fast_correct lower_count n low high

end QuotientQ800000000To825000000
