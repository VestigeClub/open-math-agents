import certificates.«prime-table-270000000-295000000-conditional»
import certificates.«prime-table-245000000-270000000»

/-!
# Prime counts from 270,000,000 through 295,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ270000000To295000000

theorem lower_count : Nat.primeCounting 270000000=14711384 := by
  calc
    Nat.primeCounting 270000000 = RangePrimeQ245000000To270000000.fast 270000000 :=
      (QuotientQ245000000To270000000.count_correct _ (by decide) (by decide)).symm
    _ = 14711384 := by decide +kernel

theorem count_correct (n : ℕ) (low : 270000000≤n) (high : n≤295000000) :
    RangePrimeQ270000000To295000000.fast n=Nat.primeCounting n :=
  RangePrimeQ270000000To295000000.fast_correct lower_count n low high

end QuotientQ270000000To295000000
