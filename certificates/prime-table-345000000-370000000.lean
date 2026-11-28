import certificates.«prime-table-345000000-370000000-conditional»
import certificates.«prime-table-320000000-345000000»

/-!
# Prime counts from 345,000,000 through 370,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ345000000To370000000

theorem lower_count : Nat.primeCounting 345000000=18549341 := by
  calc
    Nat.primeCounting 345000000 = RangePrimeQ320000000To345000000.fast 345000000 :=
      (QuotientQ320000000To345000000.count_correct _ (by decide) (by decide)).symm
    _ = 18549341 := by decide +kernel

theorem count_correct (n : ℕ) (low : 345000000≤n) (high : n≤370000000) :
    RangePrimeQ345000000To370000000.fast n=Nat.primeCounting n :=
  RangePrimeQ345000000To370000000.fast_correct lower_count n low high

end QuotientQ345000000To370000000
