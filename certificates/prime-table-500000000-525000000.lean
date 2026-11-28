import certificates.«prime-table-500000000-525000000-conditional»
import certificates.«prime-table-495000000-500000000»

/-!
# Prime counts from 500,000,000 through 525,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ500000000To525000000

theorem lower_count : Nat.primeCounting 500000000=26355867 := by
  calc
    Nat.primeCounting 500000000 = RangePrimeQ495000000To500000000.fast 500000000 :=
      (QuotientQ495000000To500000000.count_correct _ (by decide) (by decide)).symm
    _ = 26355867 := by decide +kernel

theorem count_correct (n : ℕ) (low : 500000000≤n) (high : n≤525000000) :
    RangePrimeQ500000000To525000000.fast n=Nat.primeCounting n :=
  RangePrimeQ500000000To525000000.fast_correct lower_count n low high

end QuotientQ500000000To525000000
