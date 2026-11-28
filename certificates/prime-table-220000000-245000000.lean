import certificates.«prime-table-220000000-245000000-conditional»
import certificates.«prime-table-195000000-220000000»

/-!
# Prime counts from 220,000,000 through 245,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ220000000To245000000

theorem lower_count : Nat.primeCounting 220000000=12122540 := by
  calc
    Nat.primeCounting 220000000 = RangePrimeQ195000000To220000000.fast 220000000 :=
      (QuotientQ195000000To220000000.count_correct _ (by decide) (by decide)).symm
    _ = 12122540 := by decide +kernel

theorem count_correct (n : ℕ) (low : 220000000≤n) (high : n≤245000000) :
    RangePrimeQ220000000To245000000.fast n=Nat.primeCounting n :=
  RangePrimeQ220000000To245000000.fast_correct lower_count n low high

end QuotientQ220000000To245000000
