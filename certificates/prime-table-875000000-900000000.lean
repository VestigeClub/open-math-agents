import certificates.«prime-table-875000000-900000000-conditional»
import certificates.«prime-table-850000000-875000000»

/-!
# Prime counts from 875,000,000 through 900,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ875000000To900000000

theorem lower_count : Nat.primeCounting 875000000=44796869 := by
  calc
    Nat.primeCounting 875000000 = RangePrimeQ850000000To875000000.fast 875000000 :=
      (QuotientQ850000000To875000000.count_correct _ (by decide) (by decide)).symm
    _ = 44796869 := by decide +kernel

theorem count_correct (n : ℕ) (low : 875000000≤n) (high : n≤900000000) :
    RangePrimeQ875000000To900000000.fast n=Nat.primeCounting n :=
  RangePrimeQ875000000To900000000.fast_correct lower_count n low high

end QuotientQ875000000To900000000
