import certificates.«prime-table-700000000-725000000-conditional»
import certificates.«prime-table-675000000-700000000»

/-!
# Prime counts from 700,000,000 through 725,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ700000000To725000000

theorem lower_count : Nat.primeCounting 700000000=36252931 := by
  calc
    Nat.primeCounting 700000000 = RangePrimeQ675000000To700000000.fast 700000000 :=
      (QuotientQ675000000To700000000.count_correct _ (by decide) (by decide)).symm
    _ = 36252931 := by decide +kernel

theorem count_correct (n : ℕ) (low : 700000000≤n) (high : n≤725000000) :
    RangePrimeQ700000000To725000000.fast n=Nat.primeCounting n :=
  RangePrimeQ700000000To725000000.fast_correct lower_count n low high

end QuotientQ700000000To725000000
