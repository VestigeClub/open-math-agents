import certificates.«prime-table-525000000-550000000-conditional»
import certificates.«prime-table-500000000-525000000»

/-!
# Prime counts from 525,000,000 through 550,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ525000000To550000000

theorem lower_count : Nat.primeCounting 525000000=27601606 := by
  calc
    Nat.primeCounting 525000000 = RangePrimeQ500000000To525000000.fast 525000000 :=
      (QuotientQ500000000To525000000.count_correct _ (by decide) (by decide)).symm
    _ = 27601606 := by decide +kernel

theorem count_correct (n : ℕ) (low : 525000000≤n) (high : n≤550000000) :
    RangePrimeQ525000000To550000000.fast n=Nat.primeCounting n :=
  RangePrimeQ525000000To550000000.fast_correct lower_count n low high

end QuotientQ525000000To550000000
