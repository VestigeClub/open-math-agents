import certificates.«prime-table-725000000-750000000-conditional»
import certificates.«prime-table-700000000-725000000»

/-!
# Prime counts from 725,000,000 through 750,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ725000000To750000000

theorem lower_count : Nat.primeCounting 725000000=37479513 := by
  calc
    Nat.primeCounting 725000000 = RangePrimeQ700000000To725000000.fast 725000000 :=
      (QuotientQ700000000To725000000.count_correct _ (by decide) (by decide)).symm
    _ = 37479513 := by decide +kernel

theorem count_correct (n : ℕ) (low : 725000000≤n) (high : n≤750000000) :
    RangePrimeQ725000000To750000000.fast n=Nat.primeCounting n :=
  RangePrimeQ725000000To750000000.fast_correct lower_count n low high

end QuotientQ725000000To750000000
