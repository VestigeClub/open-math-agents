import certificates.«prime-table-950000000-975000000-conditional»
import certificates.«prime-table-925000000-950000000»

/-!
# Prime counts from 950,000,000 through 975,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ950000000To975000000

theorem lower_count : Nat.primeCounting 950000000=48431471 := by
  calc
    Nat.primeCounting 950000000 = RangePrimeQ925000000To950000000.fast 950000000 :=
      (QuotientQ925000000To950000000.count_correct _ (by decide) (by decide)).symm
    _ = 48431471 := by decide +kernel

theorem count_correct (n : ℕ) (low : 950000000≤n) (high : n≤975000000) :
    RangePrimeQ950000000To975000000.fast n=Nat.primeCounting n :=
  RangePrimeQ950000000To975000000.fast_correct lower_count n low high

end QuotientQ950000000To975000000
