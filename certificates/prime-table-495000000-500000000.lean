import certificates.«prime-table-495000000-500000000-conditional»
import certificates.«prime-table-470000000-495000000»

/-!
# Prime counts from 495,000,000 through 500,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ495000000To500000000

theorem lower_count : Nat.primeCounting 495000000=26106107 := by
  calc
    Nat.primeCounting 495000000 = RangePrimeQ470000000To495000000.fast 495000000 :=
      (QuotientQ470000000To495000000.count_correct _ (by decide) (by decide)).symm
    _ = 26106107 := by decide +kernel

theorem count_correct (n : ℕ) (low : 495000000≤n) (high : n≤500000000) :
    RangePrimeQ495000000To500000000.fast n=Nat.primeCounting n :=
  RangePrimeQ495000000To500000000.fast_correct lower_count n low high

end QuotientQ495000000To500000000
