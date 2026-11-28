import certificates.«prime-table-370000000-395000000-conditional»
import certificates.«prime-table-345000000-370000000»

/-!
# Prime counts from 370,000,000 through 395,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ370000000To395000000

theorem lower_count : Nat.primeCounting 370000000=19818405 := by
  calc
    Nat.primeCounting 370000000 = RangePrimeQ345000000To370000000.fast 370000000 :=
      (QuotientQ345000000To370000000.count_correct _ (by decide) (by decide)).symm
    _ = 19818405 := by decide +kernel

theorem count_correct (n : ℕ) (low : 370000000≤n) (high : n≤395000000) :
    RangePrimeQ370000000To395000000.fast n=Nat.primeCounting n :=
  RangePrimeQ370000000To395000000.fast_correct lower_count n low high

end QuotientQ370000000To395000000
