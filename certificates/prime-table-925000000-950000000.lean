import certificates.«prime-table-925000000-950000000-conditional»
import certificates.«prime-table-900000000-925000000»

/-!
# Prime counts from 925,000,000 through 950,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ925000000To950000000

theorem lower_count : Nat.primeCounting 925000000=47221646 := by
  calc
    Nat.primeCounting 925000000 = RangePrimeQ900000000To925000000.fast 925000000 :=
      (QuotientQ900000000To925000000.count_correct _ (by decide) (by decide)).symm
    _ = 47221646 := by decide +kernel

theorem count_correct (n : ℕ) (low : 925000000≤n) (high : n≤950000000) :
    RangePrimeQ925000000To950000000.fast n=Nat.primeCounting n :=
  RangePrimeQ925000000To950000000.fast_correct lower_count n low high

end QuotientQ925000000To950000000
