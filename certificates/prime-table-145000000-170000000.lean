import certificates.«prime-table-145000000-170000000-conditional»
import certificates.«prime-table-120000000-145000000»

/-!
# Prime counts from 145,000,000 through 170,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ145000000To170000000

theorem lower_count : Nat.primeCounting 145000000=8178593 := by
  calc
    Nat.primeCounting 145000000 = RangePrimeQ120000000To145000000.fast 145000000 :=
      (QuotientQ120000000To145000000.count_correct _ (by decide) (by decide)).symm
    _ = 8178593 := by decide +kernel

theorem count_correct (n : ℕ) (low : 145000000≤n) (high : n≤170000000) :
    RangePrimeQ145000000To170000000.fast n=Nat.primeCounting n :=
  RangePrimeQ145000000To170000000.fast_correct lower_count n low high

end QuotientQ145000000To170000000
