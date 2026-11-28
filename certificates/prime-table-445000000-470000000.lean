import certificates.«prime-table-445000000-470000000-conditional»
import certificates.«prime-table-420000000-445000000»

/-!
# Prime counts from 445,000,000 through 470,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ445000000To470000000

theorem lower_count : Nat.primeCounting 445000000=23602035 := by
  calc
    Nat.primeCounting 445000000 = RangePrimeQ420000000To445000000.fast 445000000 :=
      (QuotientQ420000000To445000000.count_correct _ (by decide) (by decide)).symm
    _ = 23602035 := by decide +kernel

theorem count_correct (n : ℕ) (low : 445000000≤n) (high : n≤470000000) :
    RangePrimeQ445000000To470000000.fast n=Nat.primeCounting n :=
  RangePrimeQ445000000To470000000.fast_correct lower_count n low high

end QuotientQ445000000To470000000
