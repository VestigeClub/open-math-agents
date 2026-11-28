import certificates.«prime-table-900000000-925000000-conditional»
import certificates.«prime-table-875000000-900000000»

/-!
# Prime counts from 900,000,000 through 925,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ900000000To925000000

theorem lower_count : Nat.primeCounting 900000000=46009215 := by
  calc
    Nat.primeCounting 900000000 = RangePrimeQ875000000To900000000.fast 900000000 :=
      (QuotientQ875000000To900000000.count_correct _ (by decide) (by decide)).symm
    _ = 46009215 := by decide +kernel

theorem count_correct (n : ℕ) (low : 900000000≤n) (high : n≤925000000) :
    RangePrimeQ900000000To925000000.fast n=Nat.primeCounting n :=
  RangePrimeQ900000000To925000000.fast_correct lower_count n low high

end QuotientQ900000000To925000000
