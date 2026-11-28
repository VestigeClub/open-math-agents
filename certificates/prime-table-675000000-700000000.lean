import certificates.«prime-table-675000000-700000000-conditional»
import certificates.«prime-table-650000000-675000000»

/-!
# Prime counts from 675,000,000 through 700,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ675000000To700000000

theorem lower_count : Nat.primeCounting 675000000=35024348 := by
  calc
    Nat.primeCounting 675000000 = RangePrimeQ650000000To675000000.fast 675000000 :=
      (QuotientQ650000000To675000000.count_correct _ (by decide) (by decide)).symm
    _ = 35024348 := by decide +kernel

theorem count_correct (n : ℕ) (low : 675000000≤n) (high : n≤700000000) :
    RangePrimeQ675000000To700000000.fast n=Nat.primeCounting n :=
  RangePrimeQ675000000To700000000.fast_correct lower_count n low high

end QuotientQ675000000To700000000
