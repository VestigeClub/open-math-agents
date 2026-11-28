import certificates.«prime-table-625000000-650000000-conditional»
import certificates.«prime-table-600000000-625000000»

/-!
# Prime counts from 625,000,000 through 650,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ625000000To650000000

theorem lower_count : Nat.primeCounting 625000000=32560335 := by
  calc
    Nat.primeCounting 625000000 = RangePrimeQ600000000To625000000.fast 625000000 :=
      (QuotientQ600000000To625000000.count_correct _ (by decide) (by decide)).symm
    _ = 32560335 := by decide +kernel

theorem count_correct (n : ℕ) (low : 625000000≤n) (high : n≤650000000) :
    RangePrimeQ625000000To650000000.fast n=Nat.primeCounting n :=
  RangePrimeQ625000000To650000000.fast_correct lower_count n low high

end QuotientQ625000000To650000000
