import certificates.«prime-table-650000000-675000000-conditional»
import certificates.«prime-table-625000000-650000000»

/-!
# Prime counts from 650,000,000 through 675,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ650000000To675000000

theorem lower_count : Nat.primeCounting 650000000=33793395 := by
  calc
    Nat.primeCounting 650000000 = RangePrimeQ625000000To650000000.fast 650000000 :=
      (QuotientQ625000000To650000000.count_correct _ (by decide) (by decide)).symm
    _ = 33793395 := by decide +kernel

theorem count_correct (n : ℕ) (low : 650000000≤n) (high : n≤675000000) :
    RangePrimeQ650000000To675000000.fast n=Nat.primeCounting n :=
  RangePrimeQ650000000To675000000.fast_correct lower_count n low high

end QuotientQ650000000To675000000
