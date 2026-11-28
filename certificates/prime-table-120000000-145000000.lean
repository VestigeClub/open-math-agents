import certificates.«prime-table-120000000-145000000-conditional»
import certificates.«prime-table-94085731-120000000»

/-!
# Prime counts from 120,000,000 through 145,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ120000000To145000000

theorem lower_count : Nat.primeCounting 120000000=6841648 := by
  calc
    Nat.primeCounting 120000000 = RangePrimeQ94085731To120000000.fast 120000000 :=
      (QuotientQ94085731To120000000.count_correct _ (by decide) (by decide)).symm
    _ = 6841648 := by decide +kernel

theorem count_correct (n : ℕ) (low : 120000000≤n) (high : n≤145000000) :
    RangePrimeQ120000000To145000000.fast n=Nat.primeCounting n :=
  RangePrimeQ120000000To145000000.fast_correct lower_count n low high

end QuotientQ120000000To145000000
