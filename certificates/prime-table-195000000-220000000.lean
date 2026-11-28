import certificates.«prime-table-195000000-220000000-conditional»
import certificates.«prime-table-170000000-195000000»

/-!
# Prime counts from 195,000,000 through 220,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ195000000To220000000

theorem lower_count : Nat.primeCounting 195000000=10817577 := by
  calc
    Nat.primeCounting 195000000 = RangePrimeQ170000000To195000000.fast 195000000 :=
      (QuotientQ170000000To195000000.count_correct _ (by decide) (by decide)).symm
    _ = 10817577 := by decide +kernel

theorem count_correct (n : ℕ) (low : 195000000≤n) (high : n≤220000000) :
    RangePrimeQ195000000To220000000.fast n=Nat.primeCounting n :=
  RangePrimeQ195000000To220000000.fast_correct lower_count n low high

end QuotientQ195000000To220000000
