import certificates.«prime-table-750000000-775000000-conditional»
import certificates.«prime-table-725000000-750000000»

/-!
# Prime counts from 750,000,000 through 775,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ750000000To775000000

theorem lower_count : Nat.primeCounting 750000000=38703181 := by
  calc
    Nat.primeCounting 750000000 = RangePrimeQ725000000To750000000.fast 750000000 :=
      (QuotientQ725000000To750000000.count_correct _ (by decide) (by decide)).symm
    _ = 38703181 := by decide +kernel

theorem count_correct (n : ℕ) (low : 750000000≤n) (high : n≤775000000) :
    RangePrimeQ750000000To775000000.fast n=Nat.primeCounting n :=
  RangePrimeQ750000000To775000000.fast_correct lower_count n low high

end QuotientQ750000000To775000000
