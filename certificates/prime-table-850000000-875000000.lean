import certificates.«prime-table-850000000-875000000-conditional»
import certificates.«prime-table-825000000-850000000»

/-!
# Prime counts from 850,000,000 through 875,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ850000000To875000000

theorem lower_count : Nat.primeCounting 850000000=43581966 := by
  calc
    Nat.primeCounting 850000000 = RangePrimeQ825000000To850000000.fast 850000000 :=
      (QuotientQ825000000To850000000.count_correct _ (by decide) (by decide)).symm
    _ = 43581966 := by decide +kernel

theorem count_correct (n : ℕ) (low : 850000000≤n) (high : n≤875000000) :
    RangePrimeQ850000000To875000000.fast n=Nat.primeCounting n :=
  RangePrimeQ850000000To875000000.fast_correct lower_count n low high

end QuotientQ850000000To875000000
