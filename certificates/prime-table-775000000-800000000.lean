import certificates.«prime-table-775000000-800000000-conditional»
import certificates.«prime-table-750000000-775000000»

/-!
# Prime counts from 775,000,000 through 800,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ775000000To800000000

theorem lower_count : Nat.primeCounting 775000000=39925351 := by
  calc
    Nat.primeCounting 775000000 = RangePrimeQ750000000To775000000.fast 775000000 :=
      (QuotientQ750000000To775000000.count_correct _ (by decide) (by decide)).symm
    _ = 39925351 := by decide +kernel

theorem count_correct (n : ℕ) (low : 775000000≤n) (high : n≤800000000) :
    RangePrimeQ775000000To800000000.fast n=Nat.primeCounting n :=
  RangePrimeQ775000000To800000000.fast_correct lower_count n low high

end QuotientQ775000000To800000000
