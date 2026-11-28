import certificates.«prime-table-320000000-345000000-conditional»
import certificates.«prime-table-295000000-320000000»

/-!
# Prime counts from 320,000,000 through 345,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ320000000To345000000

theorem lower_count : Nat.primeCounting 320000000=17275206 := by
  calc
    Nat.primeCounting 320000000 = RangePrimeQ295000000To320000000.fast 320000000 :=
      (QuotientQ295000000To320000000.count_correct _ (by decide) (by decide)).symm
    _ = 17275206 := by decide +kernel

theorem count_correct (n : ℕ) (low : 320000000≤n) (high : n≤345000000) :
    RangePrimeQ320000000To345000000.fast n=Nat.primeCounting n :=
  RangePrimeQ320000000To345000000.fast_correct lower_count n low high

end QuotientQ320000000To345000000
