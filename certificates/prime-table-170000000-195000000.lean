import certificates.«prime-table-170000000-195000000-conditional»
import certificates.«prime-table-145000000-170000000»

/-!
# Prime counts from 170,000,000 through 195,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ170000000To195000000

theorem lower_count : Nat.primeCounting 170000000=9503083 := by
  calc
    Nat.primeCounting 170000000 = RangePrimeQ145000000To170000000.fast 170000000 :=
      (QuotientQ145000000To170000000.count_correct _ (by decide) (by decide)).symm
    _ = 9503083 := by decide +kernel

theorem count_correct (n : ℕ) (low : 170000000≤n) (high : n≤195000000) :
    RangePrimeQ170000000To195000000.fast n=Nat.primeCounting n :=
  RangePrimeQ170000000To195000000.fast_correct lower_count n low high

end QuotientQ170000000To195000000
