import certificates.«prime-table-94085731-120000000-conditional»
import certificates.«prime-table-67545646-94085731»

/-!
# Prime counts from 94,085,731 through 120,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ94085731To120000000

theorem lower_count : Nat.primeCounting 94085731=5439846 := by
  calc
    Nat.primeCounting 94085731 = RangePrimeQ67545646To94085731.fast 94085731 :=
      (QuotientQ67545646To94085731.count_correct _ (by decide) (by decide)).symm
    _ = 5439846 := by decide +kernel

theorem count_correct (n : ℕ) (low : 94085731≤n) (high : n≤120000000) :
    RangePrimeQ94085731To120000000.fast n=Nat.primeCounting n :=
  RangePrimeQ94085731To120000000.fast_correct lower_count n low high

end QuotientQ94085731To120000000
