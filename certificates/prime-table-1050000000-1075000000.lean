import certificates.«prime-table-1050000000-1075000000-conditional»
import certificates.«prime-table-1025000000-1050000000»

/-!
# Prime counts from 1,050,000,000 through 1,075,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ1050000000To1075000000

theorem lower_count : Nat.primeCounting 1050000000=53257350 := by
  calc
    Nat.primeCounting 1050000000 = RangePrimeQ1025000000To1050000000.fast 1050000000 :=
      (QuotientQ1025000000To1050000000.count_correct _ (by decide) (by decide)).symm
    _ = 53257350 := by decide +kernel

theorem count_correct (n : ℕ) (low : 1050000000≤n) (high : n≤1075000000) :
    RangePrimeQ1050000000To1075000000.fast n=Nat.primeCounting n :=
  RangePrimeQ1050000000To1075000000.fast_correct lower_count n low high

end QuotientQ1050000000To1075000000
