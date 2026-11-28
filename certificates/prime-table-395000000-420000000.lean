import certificates.«prime-table-395000000-420000000-conditional»
import certificates.«prime-table-370000000-395000000»

/-!
# Prime counts from 395,000,000 through 420,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ395000000To420000000

theorem lower_count : Nat.primeCounting 395000000=21083785 := by
  calc
    Nat.primeCounting 395000000 = RangePrimeQ370000000To395000000.fast 395000000 :=
      (QuotientQ370000000To395000000.count_correct _ (by decide) (by decide)).symm
    _ = 21083785 := by decide +kernel

theorem count_correct (n : ℕ) (low : 395000000≤n) (high : n≤420000000) :
    RangePrimeQ395000000To420000000.fast n=Nat.primeCounting n :=
  RangePrimeQ395000000To420000000.fast_correct lower_count n low high

end QuotientQ395000000To420000000
