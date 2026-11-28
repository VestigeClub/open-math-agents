import certificates.«prime-table-825000000-850000000-conditional»
import certificates.«prime-table-800000000-825000000»

/-!
# Prime counts from 825,000,000 through 850,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ825000000To850000000

theorem lower_count : Nat.primeCounting 825000000=42364890 := by
  calc
    Nat.primeCounting 825000000 = RangePrimeQ800000000To825000000.fast 825000000 :=
      (QuotientQ800000000To825000000.count_correct _ (by decide) (by decide)).symm
    _ = 42364890 := by decide +kernel

theorem count_correct (n : ℕ) (low : 825000000≤n) (high : n≤850000000) :
    RangePrimeQ825000000To850000000.fast n=Nat.primeCounting n :=
  RangePrimeQ825000000To850000000.fast_correct lower_count n low high

end QuotientQ825000000To850000000
