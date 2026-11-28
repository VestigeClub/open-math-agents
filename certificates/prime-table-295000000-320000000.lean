import certificates.«prime-table-295000000-320000000-conditional»
import certificates.«prime-table-270000000-295000000»

/-!
# Prime counts from 295,000,000 through 320,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ295000000To320000000

theorem lower_count : Nat.primeCounting 295000000=15996202 := by
  calc
    Nat.primeCounting 295000000 = RangePrimeQ270000000To295000000.fast 295000000 :=
      (QuotientQ270000000To295000000.count_correct _ (by decide) (by decide)).symm
    _ = 15996202 := by decide +kernel

theorem count_correct (n : ℕ) (low : 295000000≤n) (high : n≤320000000) :
    RangePrimeQ295000000To320000000.fast n=Nat.primeCounting n :=
  RangePrimeQ295000000To320000000.fast_correct lower_count n low high

end QuotientQ295000000To320000000
