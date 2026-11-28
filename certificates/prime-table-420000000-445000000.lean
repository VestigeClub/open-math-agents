import certificates.«prime-table-420000000-445000000-conditional»
import certificates.«prime-table-395000000-420000000»

/-!
# Prime counts from 420,000,000 through 445,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ420000000To445000000

theorem lower_count : Nat.primeCounting 420000000=22344479 := by
  calc
    Nat.primeCounting 420000000 = RangePrimeQ395000000To420000000.fast 420000000 :=
      (QuotientQ395000000To420000000.count_correct _ (by decide) (by decide)).symm
    _ = 22344479 := by decide +kernel

theorem count_correct (n : ℕ) (low : 420000000≤n) (high : n≤445000000) :
    RangePrimeQ420000000To445000000.fast n=Nat.primeCounting n :=
  RangePrimeQ420000000To445000000.fast_correct lower_count n low high

end QuotientQ420000000To445000000
