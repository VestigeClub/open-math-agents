import certificates.«sieve-change-204778727327-0-131»
import certificates.«joint-semiprime-correction-204778727327»

/-!
# Prime counting from the last sieve total at 204,778,727,327

The semiprime correction is 5,125,265,886. The theorem derives the prime
count from the number of survivors after sieving by all primes through 5,894.
-/
open Finset
namespace JointPrimeRank204778727327

private theorem count_segment {b : ℕ} (f : ℕ → Bool)
    (ok : ∀ n, n≤b → (f n=true ↔ n.Prime)) (a n : ℕ) (h : a+n≤b) :
    Nat.primeCounting (a+n) = Nat.primeCounting a + (List.range' (a+1) n).countP f := by
  induction n with
  | zero => simp
  | succ n ih =>
    have previous := ih (by omega)
    have step : Nat.primeCounting (a+n+1) = Nat.primeCounting (a+n) +
        (if (a+n+1).Prime then 1 else 0) := Nat.count_succ Nat.Prime (a+n+1)
    have cnt : (List.range' (a+1) (n+1)).countP f = (List.range' (a+1) n).countP f +
        (if f (a+n+1) then 1 else 0) := by
      rw [← List.range'_append_1,List.countP_append]
      simp [Nat.add_right_comm]
    rw [show a+(n+1)=a+n+1 by omega,step,previous,cnt]
    by_cases hp : (a+n+1).Prime
    · rw [if_pos hp,if_pos ((ok _ (by omega)).mpr hp),Nat.add_assoc]
    · have no : f (a+n+1)=false := Bool.eq_false_iff.mpr (mt (ok _ (by omega)).mp hp)
      rw [if_neg hp,no]
      simp

private theorem join_counts (f : ℕ → Bool) {lo a b x y : ℕ}
    (h : (List.range' lo a).countP f=x) (k : (List.range' (lo+a) b).countP f=y) :
    (List.range' lo (a+b)).countP f=x+y := by
  rw [← List.range'_append_1,List.countP_append,h,k]

private theorem count_from_intervals {b v : ℕ} (f : ℕ → Bool)
    (ok : ∀ n, n≤b → (f n=true ↔ n.Prime)) (values : (List.range' 1 b).countP f=v) :
    (Nat.primesLE b).card=v := by
  rw [Nat.primesLE_card_eq_primeCounting]
  have base := count_segment (b:=b) f ok 0 b (by omega)
  rw [show Nat.primeCounting 0=0 by decide] at base
  simp only [Nat.zero_add] at base
  exact base.trans values

private theorem prime_test (n : ℕ) (hn : n≤5894) :
    (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) n=true ↔ n.Prime := by
  dsimp only
  split_ifs with small
  · simp
  · have fac : Nat.factorial 76 = 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have lim : n.minFac ≤ 76 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) lim)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private theorem range1 : (List.range' 1 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 24 := by decide +kernel

private theorem range93 : (List.range' 93 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 18 := by decide +kernel

private theorem range185 : (List.range' 185 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 16 := by decide +kernel

private theorem range277 : (List.range' 277 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 15 := by decide +kernel

private theorem range369 : (List.range' 369 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 15 := by decide +kernel

private theorem range461 : (List.range' 461 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 13 := by decide +kernel

private theorem range553 : (List.range' 553 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 16 := by decide +kernel

private theorem range645 : (List.range' 645 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 13 := by decide +kernel

private theorem range737 : (List.range' 737 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 14 := by decide +kernel

private theorem range829 : (List.range' 829 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 13 := by decide +kernel

private theorem range921 : (List.range' 921 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 12 := by decide +kernel

private theorem range1013 : (List.range' 1013 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 16 := by decide +kernel

private theorem range1105 : (List.range' 1105 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range1197 : (List.range' 1197 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 12 := by decide +kernel

private theorem range1289 : (List.range' 1289 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 12 := by decide +kernel

private theorem range1381 : (List.range' 1381 93).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 13 := by decide +kernel

private theorem range1474 : (List.range' 1474 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 13 := by decide +kernel

private theorem range1566 : (List.range' 1566 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 14 := by decide +kernel

private theorem range1658 : (List.range' 1658 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 12 := by decide +kernel

private theorem range1750 : (List.range' 1750 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 10 := by decide +kernel

private theorem range1842 : (List.range' 1842 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 13 := by decide +kernel

private theorem range1934 : (List.range' 1934 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range2026 : (List.range' 2026 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 13 := by decide +kernel

private theorem range2118 : (List.range' 2118 93).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 10 := by decide +kernel

private theorem range2211 : (List.range' 2211 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 13 := by decide +kernel

private theorem range2303 : (List.range' 2303 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 14 := by decide +kernel

private theorem range2395 : (List.range' 2395 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range2487 : (List.range' 2487 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 8 := by decide +kernel

private theorem range2579 : (List.range' 2579 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range2671 : (List.range' 2671 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 16 := by decide +kernel

private theorem range2763 : (List.range' 2763 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 12 := by decide +kernel

private theorem range2855 : (List.range' 2855 93).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 10 := by decide +kernel

private theorem range2948 : (List.range' 2948 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range3040 : (List.range' 3040 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 10 := by decide +kernel

private theorem range3132 : (List.range' 3132 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range3224 : (List.range' 3224 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 10 := by decide +kernel

private theorem range3316 : (List.range' 3316 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 13 := by decide +kernel

private theorem range3408 : (List.range' 3408 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 10 := by decide +kernel

private theorem range3500 : (List.range' 3500 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 13 := by decide +kernel

private theorem range3592 : (List.range' 3592 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 12 := by decide +kernel

private theorem range3684 : (List.range' 3684 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range3776 : (List.range' 3776 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range3868 : (List.range' 3868 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 12 := by decide +kernel

private theorem range3960 : (List.range' 3960 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range4052 : (List.range' 4052 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range4144 : (List.range' 4144 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 10 := by decide +kernel

private theorem range4236 : (List.range' 4236 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range4328 : (List.range' 4328 93).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 9 := by decide +kernel

private theorem range4421 : (List.range' 4421 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range4513 : (List.range' 4513 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 12 := by decide +kernel

private theorem range4605 : (List.range' 4605 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range4697 : (List.range' 4697 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 9 := by decide +kernel

private theorem range4789 : (List.range' 4789 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 10 := by decide +kernel

private theorem range4881 : (List.range' 4881 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 12 := by decide +kernel

private theorem range4973 : (List.range' 4973 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 12 := by decide +kernel

private theorem range5065 : (List.range' 5065 93).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 10 := by decide +kernel

private theorem range5158 : (List.range' 5158 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 10 := by decide +kernel

private theorem range5250 : (List.range' 5250 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 9 := by decide +kernel

private theorem range5342 : (List.range' 5342 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 11 := by decide +kernel

private theorem range5434 : (List.range' 5434 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 13 := by decide +kernel

private theorem range5526 : (List.range' 5526 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 8 := by decide +kernel

private theorem range5618 : (List.range' 5618 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 13 := by decide +kernel

private theorem range5710 : (List.range' 5710 92).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 10 := by decide +kernel

private theorem range5802 : (List.range' 5802 93).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) = 14 := by decide +kernel

set_option maxRecDepth 16000 in
private theorem all_intervals : (List.range' 1 5894).countP (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1)=775 := (join_counts _ (lo:=1) (a:=2947) (b:=2947) (join_counts _ (lo:=1) (a:=1473) (b:=1474) (join_counts _ (lo:=1) (a:=736) (b:=737) (join_counts _ (lo:=1) (a:=368) (b:=368) (join_counts _ (lo:=1) (a:=184) (b:=184) (join_counts _ (lo:=1) (a:=92) (b:=92) range1 range93) (join_counts _ (lo:=185) (a:=92) (b:=92) range185 range277)) (join_counts _ (lo:=369) (a:=184) (b:=184) (join_counts _ (lo:=369) (a:=92) (b:=92) range369 range461) (join_counts _ (lo:=553) (a:=92) (b:=92) range553 range645))) (join_counts _ (lo:=737) (a:=368) (b:=369) (join_counts _ (lo:=737) (a:=184) (b:=184) (join_counts _ (lo:=737) (a:=92) (b:=92) range737 range829) (join_counts _ (lo:=921) (a:=92) (b:=92) range921 range1013)) (join_counts _ (lo:=1105) (a:=184) (b:=185) (join_counts _ (lo:=1105) (a:=92) (b:=92) range1105 range1197) (join_counts _ (lo:=1289) (a:=92) (b:=93) range1289 range1381)))) (join_counts _ (lo:=1474) (a:=737) (b:=737) (join_counts _ (lo:=1474) (a:=368) (b:=369) (join_counts _ (lo:=1474) (a:=184) (b:=184) (join_counts _ (lo:=1474) (a:=92) (b:=92) range1474 range1566) (join_counts _ (lo:=1658) (a:=92) (b:=92) range1658 range1750)) (join_counts _ (lo:=1842) (a:=184) (b:=185) (join_counts _ (lo:=1842) (a:=92) (b:=92) range1842 range1934) (join_counts _ (lo:=2026) (a:=92) (b:=93) range2026 range2118))) (join_counts _ (lo:=2211) (a:=368) (b:=369) (join_counts _ (lo:=2211) (a:=184) (b:=184) (join_counts _ (lo:=2211) (a:=92) (b:=92) range2211 range2303) (join_counts _ (lo:=2395) (a:=92) (b:=92) range2395 range2487)) (join_counts _ (lo:=2579) (a:=184) (b:=185) (join_counts _ (lo:=2579) (a:=92) (b:=92) range2579 range2671) (join_counts _ (lo:=2763) (a:=92) (b:=93) range2763 range2855))))) (join_counts _ (lo:=2948) (a:=1473) (b:=1474) (join_counts _ (lo:=2948) (a:=736) (b:=737) (join_counts _ (lo:=2948) (a:=368) (b:=368) (join_counts _ (lo:=2948) (a:=184) (b:=184) (join_counts _ (lo:=2948) (a:=92) (b:=92) range2948 range3040) (join_counts _ (lo:=3132) (a:=92) (b:=92) range3132 range3224)) (join_counts _ (lo:=3316) (a:=184) (b:=184) (join_counts _ (lo:=3316) (a:=92) (b:=92) range3316 range3408) (join_counts _ (lo:=3500) (a:=92) (b:=92) range3500 range3592))) (join_counts _ (lo:=3684) (a:=368) (b:=369) (join_counts _ (lo:=3684) (a:=184) (b:=184) (join_counts _ (lo:=3684) (a:=92) (b:=92) range3684 range3776) (join_counts _ (lo:=3868) (a:=92) (b:=92) range3868 range3960)) (join_counts _ (lo:=4052) (a:=184) (b:=185) (join_counts _ (lo:=4052) (a:=92) (b:=92) range4052 range4144) (join_counts _ (lo:=4236) (a:=92) (b:=93) range4236 range4328)))) (join_counts _ (lo:=4421) (a:=737) (b:=737) (join_counts _ (lo:=4421) (a:=368) (b:=369) (join_counts _ (lo:=4421) (a:=184) (b:=184) (join_counts _ (lo:=4421) (a:=92) (b:=92) range4421 range4513) (join_counts _ (lo:=4605) (a:=92) (b:=92) range4605 range4697)) (join_counts _ (lo:=4789) (a:=184) (b:=185) (join_counts _ (lo:=4789) (a:=92) (b:=92) range4789 range4881) (join_counts _ (lo:=4973) (a:=92) (b:=93) range4973 range5065))) (join_counts _ (lo:=5158) (a:=368) (b:=369) (join_counts _ (lo:=5158) (a:=184) (b:=184) (join_counts _ (lo:=5158) (a:=92) (b:=92) range5158 range5250) (join_counts _ (lo:=5342) (a:=92) (b:=92) range5342 range5434)) (join_counts _ (lo:=5526) (a:=184) (b:=185) (join_counts _ (lo:=5526) (a:=92) (b:=92) range5526 range5618) (join_counts _ (lo:=5710) (a:=92) (b:=93) range5710 range5802))))))

private theorem count_to_5894 : (Nat.primesLE 5894).card=775 :=
  count_from_intervals (b:=5894) (v:=775) (fun n : ℕ => if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1) prime_test all_intervals

theorem from_sieve
    (survivors : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 5894, ¬ p ∣ n)).card=13315926782) :
    Nat.primeCounting 204778727327=8190661670 := by
  apply IndexedSlicedSieveA25From0To32.rank_of_parts (y:=5894) (z:=452524) (a:=13315927557) (b:=5125265886)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [IndexedSlicedSieveA25From0To32.legendre_range,survivors,count_to_5894]
  · exact JointCorrection204778.exact_sum
  · rfl

end JointPrimeRank204778727327
