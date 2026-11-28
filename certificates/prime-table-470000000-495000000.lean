import certificates.«prime-table-470000000-495000000-conditional»
import certificates.«prime-table-445000000-470000000»

/-!
# Prime counts from 470,000,000 through 495,000,000

The lower endpoint follows from the preceding verified interval. Each subsequent
count follows from the wheel table and its proof that it counts exactly the primes.
-/
namespace QuotientQ470000000To495000000

theorem lower_count : Nat.primeCounting 470000000=24855718 := by
  calc
    Nat.primeCounting 470000000 = RangePrimeQ445000000To470000000.fast 470000000 :=
      (QuotientQ445000000To470000000.count_correct _ (by decide) (by decide)).symm
    _ = 24855718 := by decide +kernel

theorem count_correct (n : ℕ) (low : 470000000≤n) (high : n≤495000000) :
    RangePrimeQ470000000To495000000.fast n=Nat.primeCounting n :=
  RangePrimeQ470000000To495000000.fast_correct lower_count n low high

end QuotientQ470000000To495000000
