import certificates.«prime-table-550000000-575000000-conditional»
import certificates.«prime-table-525000000-550000000»

/-!
# Prime counts from 550,000,000 through 575,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ550000000To575000000

theorem lower_count : Nat.primeCounting 550000000=28845356 := by
  calc
    Nat.primeCounting 550000000 = RangePrimeQ525000000To550000000.fast 550000000 :=
      (QuotientQ525000000To550000000.count_correct _ (by decide) (by decide)).symm
    _ = 28845356 := by decide +kernel

theorem count_correct (n : ℕ) (low : 550000000≤n) (high : n≤575000000) :
    RangePrimeQ550000000To575000000.fast n=Nat.primeCounting n :=
  RangePrimeQ550000000To575000000.fast_correct lower_count n low high

end QuotientQ550000000To575000000
