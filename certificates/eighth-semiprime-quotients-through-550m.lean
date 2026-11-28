import certificates.«combined-semiprime-30110134441897-445774-5487270»
import certificates.«prime-table-120000000-145000000»
import certificates.«prime-table-145000000-170000000»
import certificates.«prime-table-170000000-195000000»
import certificates.«prime-table-195000000-220000000»
import certificates.«prime-table-220000000-245000000»
import certificates.«prime-table-245000000-270000000»
import certificates.«prime-table-270000000-295000000»
import certificates.«prime-table-295000000-320000000»
import certificates.«prime-table-320000000-345000000»
import certificates.«prime-table-345000000-370000000»
import certificates.«prime-table-370000000-395000000»
import certificates.«prime-table-395000000-420000000»
import certificates.«prime-table-420000000-445000000»
import certificates.«prime-table-445000000-470000000»
import certificates.«prime-table-470000000-495000000»
import certificates.«prime-table-495000000-500000000»
import certificates.«prime-table-500000000-525000000»
import certificates.«prime-table-525000000-550000000»
import certificates.«prime-table-67545646-94085731»
import certificates.«prime-table-94085731-120000000»
import certificates.«semiprime-correction-555157672301-middle»

/-! Eighth-endpoint semiprime correction from 54,745 to 5,487,270. -/

/-
# Semiprime terms at 30,110,134,441,897 for primes above 54,745 through 57,352

The sum covers 247 primes. Their quotient counts are checked by the
certified prime-counting table through 550,000,000.
-/
open Finset
namespace Correction30110134441897From54745To57352

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 54745 RangePrimeQ525000000To550000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 54746 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 54745 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r54746 : blockSum term 54746 651 1605938776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r55397 : blockSum term 55397 652 1757974531 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r56049 : blockSum term 56049 652 1710853520 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r56701 : blockSum term 56701 652 1886838787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 54746 2607 6961605614 := (join_sums term (lo:=54746) (a:=1303) (b:=1304) (join_sums term (lo:=54746) (a:=651) (b:=652) r54746 r55397) (join_sums term (lo:=56049) (a:=652) (b:=652) r56049 r56701))

private theorem rows : blockSum term 0 57353 6961605614 :=
  join_sums term (lo:=0) (a:=54746) (b:=2607) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 57352).filter (54745 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=6961605614 :=
  right_from_blocks (l:=525000000) (b:=550000000) (small:=745089)
    RangePrimeQ525000000To550000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ525000000To550000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From54745To57352

/-
# Semiprime terms at 30,110,134,441,897 for primes above 57,352 through 60,220

The sum covers 262 primes. Their quotient counts are checked by the
certified prime-counting table through 525,000,000.
-/
open Finset
namespace Correction30110134441897From57352To60220

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 57352 RangePrimeQ500000000To525000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 57353 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 57352 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r57353 : blockSum term 57353 717 1782593604 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r58070 : blockSum term 58070 717 1762685412 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r58787 : blockSum term 58787 717 1875621357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r59504 : blockSum term 59504 717 1642964427 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 57353 2868 7063864800 := (join_sums term (lo:=57353) (a:=1434) (b:=1434) (join_sums term (lo:=57353) (a:=717) (b:=717) r57353 r58070) (join_sums term (lo:=58787) (a:=717) (b:=717) r58787 r59504))

private theorem rows : blockSum term 0 60221 7063864800 :=
  join_sums term (lo:=0) (a:=57353) (b:=2868) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 60220).filter (57352 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=7063864800 :=
  right_from_blocks (l:=500000000) (b:=525000000) (small:=745089)
    RangePrimeQ500000000To525000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ500000000To525000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From57352To60220

/-
# Semiprime terms at 30,110,134,441,897 for primes above 60,220 through 60,828

The sum covers 53 primes. Their quotient counts are checked by the
certified prime-counting table through 500,000,000.
-/
open Finset
namespace Correction30110134441897From60220To60828

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 60220 RangePrimeQ495000000To500000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 60221 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 60220 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r60221 : blockSum term 60221 608 1389518940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 60221 608 1389518940 := r60221

private theorem rows : blockSum term 0 60829 1389518940 :=
  join_sums term (lo:=0) (a:=60221) (b:=608) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 60828).filter (60220 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=1389518940 :=
  right_from_blocks (l:=495000000) (b:=500000000) (small:=745089)
    RangePrimeQ495000000To500000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ495000000To500000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From60220To60828

/-
# Semiprime terms at 30,110,134,441,897 for primes above 60,828 through 64,064

The sum covers 288 primes. Their quotient counts are checked by the
certified prime-counting table through 495,000,000.
-/
open Finset
namespace Correction30110134441897From60828To64064

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 60828 RangePrimeQ470000000To495000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 60829 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 60828 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r60829 : blockSum term 60829 404 832691792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r61233 : blockSum term 61233 405 982196916 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r61638 : blockSum term 61638 404 899343329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r62042 : blockSum term 62042 405 843032453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r62447 : blockSum term 62447 404 888594576 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r62851 : blockSum term 62851 405 857941850 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r63256 : blockSum term 63256 404 1103121778 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r63660 : blockSum term 63660 405 922482201 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 60829 3236 7329404895 := (join_sums term (lo:=60829) (a:=1618) (b:=1618) (join_sums term (lo:=60829) (a:=809) (b:=809) (join_sums term (lo:=60829) (a:=404) (b:=405) r60829 r61233) (join_sums term (lo:=61638) (a:=404) (b:=405) r61638 r62042)) (join_sums term (lo:=62447) (a:=809) (b:=809) (join_sums term (lo:=62447) (a:=404) (b:=405) r62447 r62851) (join_sums term (lo:=63256) (a:=404) (b:=405) r63256 r63660)))

private theorem rows : blockSum term 0 64065 7329404895 :=
  join_sums term (lo:=0) (a:=60829) (b:=3236) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 64064).filter (60828 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=7329404895 :=
  right_from_blocks (l:=470000000) (b:=495000000) (small:=745089)
    RangePrimeQ470000000To495000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ470000000To495000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From60828To64064

/-
# Semiprime terms at 30,110,134,441,897 for primes above 64,064 through 67,663

The sum covers 321 primes. Their quotient counts are checked by the
certified prime-counting table through 470,000,000.
-/
open Finset
namespace Correction30110134441897From64064To67663

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 64064 RangePrimeQ445000000To470000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 64065 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 64064 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r64065 : blockSum term 64065 449 866847508 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r64514 : blockSum term 64514 450 910240116 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r64964 : blockSum term 64964 450 1026630199 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r65414 : blockSum term 65414 450 1117027264 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r65864 : blockSum term 65864 450 820561814 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r66314 : blockSum term 66314 450 1006784329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r66764 : blockSum term 66764 450 1000191693 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r67214 : blockSum term 67214 450 1017751107 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 64065 3599 7766034030 := (join_sums term (lo:=64065) (a:=1799) (b:=1800) (join_sums term (lo:=64065) (a:=899) (b:=900) (join_sums term (lo:=64065) (a:=449) (b:=450) r64065 r64514) (join_sums term (lo:=64964) (a:=450) (b:=450) r64964 r65414)) (join_sums term (lo:=65864) (a:=900) (b:=900) (join_sums term (lo:=65864) (a:=450) (b:=450) r65864 r66314) (join_sums term (lo:=66764) (a:=450) (b:=450) r66764 r67214)))

private theorem rows : blockSum term 0 67664 7766034030 :=
  join_sums term (lo:=0) (a:=64065) (b:=3599) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 67663).filter (64064 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=7766034030 :=
  right_from_blocks (l:=445000000) (b:=470000000) (small:=745089)
    RangePrimeQ445000000To470000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ445000000To470000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From64064To67663

/-
# Semiprime terms at 30,110,134,441,897 for primes above 67,663 through 71,690

The sum covers 355 primes. Their quotient counts are checked by the
certified prime-counting table through 445,000,000.
-/
open Finset
namespace Correction30110134441897From67663To71690

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 67663 RangePrimeQ420000000To445000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 67664 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 67663 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r67664 : blockSum term 67664 503 1081676544 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r68167 : blockSum term 68167 503 910449647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r68670 : blockSum term 68670 503 1020353654 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r69173 : blockSum term 69173 504 898448549 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r69677 : blockSum term 69677 503 1051923000 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r70180 : blockSum term 70180 504 1090486880 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r70684 : blockSum term 70684 503 1037726043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r71187 : blockSum term 71187 504 1053681618 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 67664 4027 8144745935 := (join_sums term (lo:=67664) (a:=2013) (b:=2014) (join_sums term (lo:=67664) (a:=1006) (b:=1007) (join_sums term (lo:=67664) (a:=503) (b:=503) r67664 r68167) (join_sums term (lo:=68670) (a:=503) (b:=504) r68670 r69173)) (join_sums term (lo:=69677) (a:=1007) (b:=1007) (join_sums term (lo:=69677) (a:=503) (b:=504) r69677 r70180) (join_sums term (lo:=70684) (a:=503) (b:=504) r70684 r71187)))

private theorem rows : blockSum term 0 71691 8144745935 :=
  join_sums term (lo:=0) (a:=67664) (b:=4027) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 71690).filter (67663 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=8144745935 :=
  right_from_blocks (l:=420000000) (b:=445000000) (small:=745089)
    RangePrimeQ420000000To445000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ420000000To445000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From67663To71690

/-
# Semiprime terms at 30,110,134,441,897 for primes above 71,690 through 76,228

The sum covers 406 primes. Their quotient counts are checked by the
certified prime-counting table through 420,000,000.
-/
open Finset
namespace Correction30110134441897From71690To76228

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 71690 RangePrimeQ395000000To420000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 71691 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 71690 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r71691 : blockSum term 71691 567 1268553433 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r72258 : blockSum term 72258 567 1060199762 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r72825 : blockSum term 72825 567 1074601920 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r73392 : blockSum term 73392 568 1066612343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r73960 : blockSum term 73960 567 1123679941 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r74527 : blockSum term 74527 567 1094356048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r75094 : blockSum term 75094 567 1128795598 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r75661 : blockSum term 75661 568 994252311 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 71691 4538 8811051356 := (join_sums term (lo:=71691) (a:=2269) (b:=2269) (join_sums term (lo:=71691) (a:=1134) (b:=1135) (join_sums term (lo:=71691) (a:=567) (b:=567) r71691 r72258) (join_sums term (lo:=72825) (a:=567) (b:=568) r72825 r73392)) (join_sums term (lo:=73960) (a:=1134) (b:=1135) (join_sums term (lo:=73960) (a:=567) (b:=567) r73960 r74527) (join_sums term (lo:=75094) (a:=567) (b:=568) r75094 r75661)))

private theorem rows : blockSum term 0 76229 8811051356 :=
  join_sums term (lo:=0) (a:=71691) (b:=4538) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 76228).filter (71690 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=8811051356 :=
  right_from_blocks (l:=395000000) (b:=420000000) (small:=745089)
    RangePrimeQ395000000To420000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ395000000To420000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From71690To76228

/-
# Semiprime terms at 30,110,134,441,897 for primes above 76,228 through 81,378

The sum covers 463 primes. Their quotient counts are checked by the
certified prime-counting table through 395,000,000.
-/
open Finset
namespace Correction30110134441897From76228To81378

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 76228 RangePrimeQ370000000To395000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 76229 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 76228 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r76229 : blockSum term 76229 643 1175654629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r76872 : blockSum term 76872 644 1207731295 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r77516 : blockSum term 77516 644 1219659932 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r78160 : blockSum term 78160 644 1148173370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r78804 : blockSum term 78804 643 1139029229 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r79447 : blockSum term 79447 644 1130507200 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r80091 : blockSum term 80091 644 1162105232 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r80735 : blockSum term 80735 644 1272751844 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 76229 5150 9455612731 := (join_sums term (lo:=76229) (a:=2575) (b:=2575) (join_sums term (lo:=76229) (a:=1287) (b:=1288) (join_sums term (lo:=76229) (a:=643) (b:=644) r76229 r76872) (join_sums term (lo:=77516) (a:=644) (b:=644) r77516 r78160)) (join_sums term (lo:=78804) (a:=1287) (b:=1288) (join_sums term (lo:=78804) (a:=643) (b:=644) r78804 r79447) (join_sums term (lo:=80091) (a:=644) (b:=644) r80091 r80735)))

private theorem rows : blockSum term 0 81379 9455612731 :=
  join_sums term (lo:=0) (a:=76229) (b:=5150) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 81378).filter (76228 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=9455612731 :=
  right_from_blocks (l:=370000000) (b:=395000000) (small:=745089)
    RangePrimeQ370000000To395000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ370000000To395000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From76228To81378

/-
# Semiprime terms at 30,110,134,441,897 for primes above 81,378 through 87,275

The sum covers 509 primes. Their quotient counts are checked by the
certified prime-counting table through 370,000,000.
-/
open Finset
namespace Correction30110134441897From81378To87275

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 81378 RangePrimeQ345000000To370000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 81379 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 81378 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r81379 : blockSum term 81379 737 1262262081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r82116 : blockSum term 82116 737 1349680204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r82853 : blockSum term 82853 737 1163488096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r83590 : blockSum term 83590 737 1211597827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r84327 : blockSum term 84327 737 1201869341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r85064 : blockSum term 85064 737 1210974179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r85801 : blockSum term 85801 737 1275804628 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r86538 : blockSum term 86538 738 1079535168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 81379 5897 9755211524 := (join_sums term (lo:=81379) (a:=2948) (b:=2949) (join_sums term (lo:=81379) (a:=1474) (b:=1474) (join_sums term (lo:=81379) (a:=737) (b:=737) r81379 r82116) (join_sums term (lo:=82853) (a:=737) (b:=737) r82853 r83590)) (join_sums term (lo:=84327) (a:=1474) (b:=1475) (join_sums term (lo:=84327) (a:=737) (b:=737) r84327 r85064) (join_sums term (lo:=85801) (a:=737) (b:=738) r85801 r86538)))

private theorem rows : blockSum term 0 87276 9755211524 :=
  join_sums term (lo:=0) (a:=81379) (b:=5897) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 87275).filter (81378 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=9755211524 :=
  right_from_blocks (l:=345000000) (b:=370000000) (small:=745089)
    RangePrimeQ345000000To370000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ345000000To370000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From81378To87275

/-
# Semiprime terms at 30,110,134,441,897 for primes above 87,275 through 94,094

The sum covers 604 primes. Their quotient counts are checked by the
certified prime-counting table through 345,000,000.
-/
open Finset
namespace Correction30110134441897From87275To94094

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 87275 RangePrimeQ320000000To345000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 87276 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 87275 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r87276 : blockSum term 87276 426 832247806 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r87702 : blockSum term 87702 426 626100379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r88128 : blockSum term 88128 426 513154538 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r88554 : blockSum term 88554 426 675016273 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r88980 : blockSum term 88980 426 726621866 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r89406 : blockSum term 89406 426 723321224 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r89832 : blockSum term 89832 426 792029000 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r90258 : blockSum term 90258 427 645079756 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r90685 : blockSum term 90685 426 570887063 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r91111 : blockSum term 91111 426 728337713 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r91537 : blockSum term 91537 426 601158875 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r91963 : blockSum term 91963 427 721665426 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r92390 : blockSum term 92390 426 736123022 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r92816 : blockSum term 92816 426 663223656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r93242 : blockSum term 93242 426 643109391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r93668 : blockSum term 93668 427 605522744 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 87276 6819 10803598732 := (join_sums term (lo:=87276) (a:=3409) (b:=3410) (join_sums term (lo:=87276) (a:=1704) (b:=1705) (join_sums term (lo:=87276) (a:=852) (b:=852) (join_sums term (lo:=87276) (a:=426) (b:=426) r87276 r87702) (join_sums term (lo:=88128) (a:=426) (b:=426) r88128 r88554)) (join_sums term (lo:=88980) (a:=852) (b:=853) (join_sums term (lo:=88980) (a:=426) (b:=426) r88980 r89406) (join_sums term (lo:=89832) (a:=426) (b:=427) r89832 r90258))) (join_sums term (lo:=90685) (a:=1705) (b:=1705) (join_sums term (lo:=90685) (a:=852) (b:=853) (join_sums term (lo:=90685) (a:=426) (b:=426) r90685 r91111) (join_sums term (lo:=91537) (a:=426) (b:=427) r91537 r91963)) (join_sums term (lo:=92390) (a:=852) (b:=853) (join_sums term (lo:=92390) (a:=426) (b:=426) r92390 r92816) (join_sums term (lo:=93242) (a:=426) (b:=427) r93242 r93668))))

private theorem rows : blockSum term 0 94095 10803598732 :=
  join_sums term (lo:=0) (a:=87276) (b:=6819) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 94094).filter (87275 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=10803598732 :=
  right_from_blocks (l:=320000000) (b:=345000000) (small:=745089)
    RangePrimeQ320000000To345000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ320000000To345000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From87275To94094

/-
# Semiprime terms at 30,110,134,441,897 for primes above 94,094 through 102,068

The sum covers 697 primes. Their quotient counts are checked by the
certified prime-counting table through 320,000,000.
-/
open Finset
namespace Correction30110134441897From94094To102068

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 94094 RangePrimeQ295000000To320000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 94095 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 94094 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r94095 : blockSum term 94095 498 792174821 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r94593 : blockSum term 94593 498 736847492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r95091 : blockSum term 95091 498 818571289 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r95589 : blockSum term 95589 499 763612180 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r96088 : blockSum term 96088 498 692264612 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r96586 : blockSum term 96586 499 722534089 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r97085 : blockSum term 97085 498 702165426 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r97583 : blockSum term 97583 499 665546080 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r98082 : blockSum term 98082 498 678806272 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r98580 : blockSum term 98580 498 725133551 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r99078 : blockSum term 99078 498 721869042 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r99576 : blockSum term 99576 499 718405184 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r100075 : blockSum term 100075 498 698554906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r100573 : blockSum term 100573 499 598368396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r101072 : blockSum term 101072 498 788837794 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r101570 : blockSum term 101570 499 753034152 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 94095 7974 11576725286 := (join_sums term (lo:=94095) (a:=3987) (b:=3987) (join_sums term (lo:=94095) (a:=1993) (b:=1994) (join_sums term (lo:=94095) (a:=996) (b:=997) (join_sums term (lo:=94095) (a:=498) (b:=498) r94095 r94593) (join_sums term (lo:=95091) (a:=498) (b:=499) r95091 r95589)) (join_sums term (lo:=96088) (a:=997) (b:=997) (join_sums term (lo:=96088) (a:=498) (b:=499) r96088 r96586) (join_sums term (lo:=97085) (a:=498) (b:=499) r97085 r97583))) (join_sums term (lo:=98082) (a:=1993) (b:=1994) (join_sums term (lo:=98082) (a:=996) (b:=997) (join_sums term (lo:=98082) (a:=498) (b:=498) r98082 r98580) (join_sums term (lo:=99078) (a:=498) (b:=499) r99078 r99576)) (join_sums term (lo:=100075) (a:=997) (b:=997) (join_sums term (lo:=100075) (a:=498) (b:=499) r100075 r100573) (join_sums term (lo:=101072) (a:=498) (b:=499) r101072 r101570))))

private theorem rows : blockSum term 0 102069 11576725286 :=
  join_sums term (lo:=0) (a:=94095) (b:=7974) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 102068).filter (94094 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=11576725286 :=
  right_from_blocks (l:=295000000) (b:=320000000) (small:=745089)
    RangePrimeQ295000000To320000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ295000000To320000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From94094To102068

/-
# Semiprime terms at 30,110,134,441,897 for primes above 102,068 through 111,519

The sum covers 803 primes. Their quotient counts are checked by the
certified prime-counting table through 295,000,000.
-/
open Finset
namespace Correction30110134441897From102068To111519

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 102068 RangePrimeQ270000000To295000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 102069 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 102068 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r102069 : blockSum term 102069 590 876925320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r102659 : blockSum term 102659 591 681815949 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r103250 : blockSum term 103250 590 709641494 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r103840 : blockSum term 103840 591 847101903 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r104431 : blockSum term 104431 590 842486220 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r105021 : blockSum term 105021 591 775814754 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r105612 : blockSum term 105612 591 694703401 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r106203 : blockSum term 106203 591 921381214 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r106794 : blockSum term 106794 590 748544294 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r107384 : blockSum term 107384 591 653218831 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r107975 : blockSum term 107975 591 816397471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r108566 : blockSum term 108566 591 796947964 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r109157 : blockSum term 109157 590 763184890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r109747 : blockSum term 109747 591 699804703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r110338 : blockSum term 110338 591 770083399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r110929 : blockSum term 110929 591 707425666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 102069 9451 12305477473 := (join_sums term (lo:=102069) (a:=4725) (b:=4726) (join_sums term (lo:=102069) (a:=2362) (b:=2363) (join_sums term (lo:=102069) (a:=1181) (b:=1181) (join_sums term (lo:=102069) (a:=590) (b:=591) r102069 r102659) (join_sums term (lo:=103250) (a:=590) (b:=591) r103250 r103840)) (join_sums term (lo:=104431) (a:=1181) (b:=1182) (join_sums term (lo:=104431) (a:=590) (b:=591) r104431 r105021) (join_sums term (lo:=105612) (a:=591) (b:=591) r105612 r106203))) (join_sums term (lo:=106794) (a:=2363) (b:=2363) (join_sums term (lo:=106794) (a:=1181) (b:=1182) (join_sums term (lo:=106794) (a:=590) (b:=591) r106794 r107384) (join_sums term (lo:=107975) (a:=591) (b:=591) r107975 r108566)) (join_sums term (lo:=109157) (a:=1181) (b:=1182) (join_sums term (lo:=109157) (a:=590) (b:=591) r109157 r109747) (join_sums term (lo:=110338) (a:=591) (b:=591) r110338 r110929))))

private theorem rows : blockSum term 0 111520 12305477473 :=
  join_sums term (lo:=0) (a:=102069) (b:=9451) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 111519).filter (102068 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=12305477473 :=
  right_from_blocks (l:=270000000) (b:=295000000) (small:=745089)
    RangePrimeQ270000000To295000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ270000000To295000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From102068To111519

/-
# Semiprime terms at 30,110,134,441,897 for primes above 111,519 through 122,898

The sum covers 979 primes. Their quotient counts are checked by the
certified prime-counting table through 270,000,000.
-/
open Finset
namespace Correction30110134441897From111519To122898

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 111519 RangePrimeQ245000000To270000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 111520 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 111519 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r111520 : blockSum term 111520 711 908710084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r112231 : blockSum term 112231 711 845129823 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r112942 : blockSum term 112942 711 912741299 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r113653 : blockSum term 113653 711 863801306 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r114364 : blockSum term 114364 711 830075160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r115075 : blockSum term 115075 711 896282368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r115786 : blockSum term 115786 711 891365078 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r116497 : blockSum term 116497 712 815655095 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r117209 : blockSum term 117209 711 922817053 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r117920 : blockSum term 117920 711 764758863 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r118631 : blockSum term 118631 711 843414647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r119342 : blockSum term 119342 712 852189757 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r120054 : blockSum term 120054 711 806513171 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r120765 : blockSum term 120765 711 910935771 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r121476 : blockSum term 121476 711 824745274 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r122187 : blockSum term 122187 712 847146319 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 111520 11379 13736281068 := (join_sums term (lo:=111520) (a:=5689) (b:=5690) (join_sums term (lo:=111520) (a:=2844) (b:=2845) (join_sums term (lo:=111520) (a:=1422) (b:=1422) (join_sums term (lo:=111520) (a:=711) (b:=711) r111520 r112231) (join_sums term (lo:=112942) (a:=711) (b:=711) r112942 r113653)) (join_sums term (lo:=114364) (a:=1422) (b:=1423) (join_sums term (lo:=114364) (a:=711) (b:=711) r114364 r115075) (join_sums term (lo:=115786) (a:=711) (b:=712) r115786 r116497))) (join_sums term (lo:=117209) (a:=2845) (b:=2845) (join_sums term (lo:=117209) (a:=1422) (b:=1423) (join_sums term (lo:=117209) (a:=711) (b:=711) r117209 r117920) (join_sums term (lo:=118631) (a:=711) (b:=712) r118631 r119342)) (join_sums term (lo:=120054) (a:=1422) (b:=1423) (join_sums term (lo:=120054) (a:=711) (b:=711) r120054 r120765) (join_sums term (lo:=121476) (a:=711) (b:=712) r121476 r122187))))

private theorem rows : blockSum term 0 122899 13736281068 :=
  join_sums term (lo:=0) (a:=111520) (b:=11379) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 122898).filter (111519 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=13736281068 :=
  right_from_blocks (l:=245000000) (b:=270000000) (small:=745089)
    RangePrimeQ245000000To270000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ245000000To270000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From111519To122898

/-
# Semiprime terms at 30,110,134,441,897 for primes above 122,898 through 136,864

The sum covers 1,191 primes. Their quotient counts are checked by the
certified prime-counting table through 245,000,000.
-/
open Finset
namespace Correction30110134441897From122898To136864

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 122898 RangePrimeQ220000000To245000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 122899 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 122898 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r122899 : blockSum term 122899 436 441760383 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r123335 : blockSum term 123335 436 560354266 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r123771 : blockSum term 123771 436 478673745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r124207 : blockSum term 124207 437 477149440 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r124644 : blockSum term 124644 436 475614370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r125080 : blockSum term 125080 437 513511356 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r125517 : blockSum term 125517 436 498638954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r125953 : blockSum term 125953 437 483982212 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r126390 : blockSum term 126390 436 469349286 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r126826 : blockSum term 126826 437 415775031 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r127263 : blockSum term 127263 436 505076314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r127699 : blockSum term 127699 437 451958953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r128136 : blockSum term 128136 436 553333069 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r128572 : blockSum term 128572 437 500190332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r129009 : blockSum term 129009 436 460316567 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r129445 : blockSum term 129445 437 458979819 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r129882 : blockSum term 129882 436 482811057 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r130318 : blockSum term 130318 436 506639573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r130754 : blockSum term 130754 436 391385388 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r131190 : blockSum term 131190 437 453085631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r131627 : blockSum term 131627 436 476772498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r132063 : blockSum term 132063 437 437713124 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r132500 : blockSum term 132500 436 498764615 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r132936 : blockSum term 132936 437 497171099 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r133373 : blockSum term 133373 436 421294334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r133809 : blockSum term 133809 437 444655464 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r134246 : blockSum term 134246 436 431063433 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r134682 : blockSum term 134682 437 417398240 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r135119 : blockSum term 135119 436 477342373 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r135555 : blockSum term 135555 437 488180026 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r135992 : blockSum term 135992 436 498663265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r136428 : blockSum term 136428 437 497287531 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 122899 13966 15164891748 := (join_sums term (lo:=122899) (a:=6983) (b:=6983) (join_sums term (lo:=122899) (a:=3491) (b:=3492) (join_sums term (lo:=122899) (a:=1745) (b:=1746) (join_sums term (lo:=122899) (a:=872) (b:=873) (join_sums term (lo:=122899) (a:=436) (b:=436) r122899 r123335) (join_sums term (lo:=123771) (a:=436) (b:=437) r123771 r124207)) (join_sums term (lo:=124644) (a:=873) (b:=873) (join_sums term (lo:=124644) (a:=436) (b:=437) r124644 r125080) (join_sums term (lo:=125517) (a:=436) (b:=437) r125517 r125953))) (join_sums term (lo:=126390) (a:=1746) (b:=1746) (join_sums term (lo:=126390) (a:=873) (b:=873) (join_sums term (lo:=126390) (a:=436) (b:=437) r126390 r126826) (join_sums term (lo:=127263) (a:=436) (b:=437) r127263 r127699)) (join_sums term (lo:=128136) (a:=873) (b:=873) (join_sums term (lo:=128136) (a:=436) (b:=437) r128136 r128572) (join_sums term (lo:=129009) (a:=436) (b:=437) r129009 r129445)))) (join_sums term (lo:=129882) (a:=3491) (b:=3492) (join_sums term (lo:=129882) (a:=1745) (b:=1746) (join_sums term (lo:=129882) (a:=872) (b:=873) (join_sums term (lo:=129882) (a:=436) (b:=436) r129882 r130318) (join_sums term (lo:=130754) (a:=436) (b:=437) r130754 r131190)) (join_sums term (lo:=131627) (a:=873) (b:=873) (join_sums term (lo:=131627) (a:=436) (b:=437) r131627 r132063) (join_sums term (lo:=132500) (a:=436) (b:=437) r132500 r132936))) (join_sums term (lo:=133373) (a:=1746) (b:=1746) (join_sums term (lo:=133373) (a:=873) (b:=873) (join_sums term (lo:=133373) (a:=436) (b:=437) r133373 r133809) (join_sums term (lo:=134246) (a:=436) (b:=437) r134246 r134682)) (join_sums term (lo:=135119) (a:=873) (b:=873) (join_sums term (lo:=135119) (a:=436) (b:=437) r135119 r135555) (join_sums term (lo:=135992) (a:=436) (b:=437) r135992 r136428)))))

private theorem rows : blockSum term 0 136865 15164891748 :=
  join_sums term (lo:=0) (a:=122899) (b:=13966) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 136864).filter (122898 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=15164891748 :=
  right_from_blocks (l:=220000000) (b:=245000000) (small:=745089)
    RangePrimeQ220000000To245000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ220000000To245000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From122898To136864

/-
# Semiprime terms at 30,110,134,441,897 for primes above 136,864 through 154,410

The sum covers 1,478 primes. Their quotient counts are checked by the
certified prime-counting table through 220,000,000.
-/
open Finset
namespace Correction30110134441897From136864To154410

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 136864 RangePrimeQ195000000To220000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 136865 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 136864 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r136865 : blockSum term 136865 548 568036075 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r137413 : blockSum term 137413 548 529802866 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r137961 : blockSum term 137961 548 563787231 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r138509 : blockSum term 138509 549 514025020 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r139058 : blockSum term 139058 548 559585538 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r139606 : blockSum term 139606 548 510153367 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r140154 : blockSum term 140154 548 626391448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r140702 : blockSum term 140702 549 541674540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r141251 : blockSum term 141251 548 586563674 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r141799 : blockSum term 141799 548 526075929 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r142347 : blockSum term 142347 548 500819357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r142895 : blockSum term 142895 549 452604183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r143444 : blockSum term 143444 548 555091777 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r143992 : blockSum term 143992 549 483850045 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r144541 : blockSum term 144541 548 528079441 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r145089 : blockSum term 145089 549 526094670 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r145638 : blockSum term 145638 548 535724588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r146186 : blockSum term 146186 548 511138194 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r146734 : blockSum term 146734 548 509294505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r147282 : blockSum term 147282 549 586443325 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r147831 : blockSum term 147831 548 415762826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r148379 : blockSum term 148379 548 526366756 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r148927 : blockSum term 148927 548 602688023 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r149475 : blockSum term 149475 549 522726304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r150024 : blockSum term 150024 548 531991236 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r150572 : blockSum term 150572 548 474913886 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r151120 : blockSum term 151120 548 594331482 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r151668 : blockSum term 151668 549 515579178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r152217 : blockSum term 152217 548 481025696 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r152765 : blockSum term 152765 549 501256903 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r153314 : blockSum term 153314 548 467009065 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r153862 : blockSum term 153862 549 541093787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 136865 17546 16889980915 := (join_sums term (lo:=136865) (a:=8773) (b:=8773) (join_sums term (lo:=136865) (a:=4386) (b:=4387) (join_sums term (lo:=136865) (a:=2193) (b:=2193) (join_sums term (lo:=136865) (a:=1096) (b:=1097) (join_sums term (lo:=136865) (a:=548) (b:=548) r136865 r137413) (join_sums term (lo:=137961) (a:=548) (b:=549) r137961 r138509)) (join_sums term (lo:=139058) (a:=1096) (b:=1097) (join_sums term (lo:=139058) (a:=548) (b:=548) r139058 r139606) (join_sums term (lo:=140154) (a:=548) (b:=549) r140154 r140702))) (join_sums term (lo:=141251) (a:=2193) (b:=2194) (join_sums term (lo:=141251) (a:=1096) (b:=1097) (join_sums term (lo:=141251) (a:=548) (b:=548) r141251 r141799) (join_sums term (lo:=142347) (a:=548) (b:=549) r142347 r142895)) (join_sums term (lo:=143444) (a:=1097) (b:=1097) (join_sums term (lo:=143444) (a:=548) (b:=549) r143444 r143992) (join_sums term (lo:=144541) (a:=548) (b:=549) r144541 r145089)))) (join_sums term (lo:=145638) (a:=4386) (b:=4387) (join_sums term (lo:=145638) (a:=2193) (b:=2193) (join_sums term (lo:=145638) (a:=1096) (b:=1097) (join_sums term (lo:=145638) (a:=548) (b:=548) r145638 r146186) (join_sums term (lo:=146734) (a:=548) (b:=549) r146734 r147282)) (join_sums term (lo:=147831) (a:=1096) (b:=1097) (join_sums term (lo:=147831) (a:=548) (b:=548) r147831 r148379) (join_sums term (lo:=148927) (a:=548) (b:=549) r148927 r149475))) (join_sums term (lo:=150024) (a:=2193) (b:=2194) (join_sums term (lo:=150024) (a:=1096) (b:=1097) (join_sums term (lo:=150024) (a:=548) (b:=548) r150024 r150572) (join_sums term (lo:=151120) (a:=548) (b:=549) r151120 r151668)) (join_sums term (lo:=152217) (a:=1097) (b:=1097) (join_sums term (lo:=152217) (a:=548) (b:=549) r152217 r152765) (join_sums term (lo:=153314) (a:=548) (b:=549) r153314 r153862)))))

private theorem rows : blockSum term 0 154411 16889980915 :=
  join_sums term (lo:=0) (a:=136865) (b:=17546) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 154410).filter (136864 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=16889980915 :=
  right_from_blocks (l:=195000000) (b:=220000000) (small:=745089)
    RangePrimeQ195000000To220000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ195000000To220000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From136864To154410

/-
# Semiprime terms at 30,110,134,441,897 for primes above 154,410 through 177,118

The sum covers 1,870 primes. Their quotient counts are checked by the
certified prime-counting table through 195,000,000.
-/
open Finset
namespace Correction30110134441897From154410To177118

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 154410 RangePrimeQ170000000To195000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 154411 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 154410 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r154411 : blockSum term 154411 709 614433112 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r155120 : blockSum term 155120 710 708298442 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r155830 : blockSum term 155830 709 512981157 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r156539 : blockSum term 156539 710 670321682 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r157249 : blockSum term 157249 709 635800435 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r157958 : blockSum term 157958 710 601298127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r158668 : blockSum term 158668 710 535777388 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r159378 : blockSum term 159378 710 690528015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r160088 : blockSum term 160088 709 614591887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r160797 : blockSum term 160797 710 570672899 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r161507 : blockSum term 161507 709 578745096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r162216 : blockSum term 162216 710 658442912 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r162926 : blockSum term 162926 709 584049004 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r163635 : blockSum term 163635 710 622462002 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r164345 : blockSum term 164345 710 538706020 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r165055 : blockSum term 165055 710 597120638 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r165765 : blockSum term 165765 709 534248543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r166474 : blockSum term 166474 710 652532326 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r167184 : blockSum term 167184 709 560017747 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r167893 : blockSum term 167893 710 507950843 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r168603 : blockSum term 168603 709 535707492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r169312 : blockSum term 169312 710 622524552 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r170022 : blockSum term 170022 710 600416543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r170732 : blockSum term 170732 710 558917303 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r171442 : blockSum term 171442 709 585987222 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r172151 : blockSum term 172151 710 642031876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r172861 : blockSum term 172861 709 503868759 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r173570 : blockSum term 173570 710 598453510 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r174280 : blockSum term 174280 709 548087915 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r174989 : blockSum term 174989 710 469307872 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r175699 : blockSum term 175699 710 648784433 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r176409 : blockSum term 176409 710 608409299 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 154411 22708 18911475051 := (join_sums term (lo:=154411) (a:=11354) (b:=11354) (join_sums term (lo:=154411) (a:=5677) (b:=5677) (join_sums term (lo:=154411) (a:=2838) (b:=2839) (join_sums term (lo:=154411) (a:=1419) (b:=1419) (join_sums term (lo:=154411) (a:=709) (b:=710) r154411 r155120) (join_sums term (lo:=155830) (a:=709) (b:=710) r155830 r156539)) (join_sums term (lo:=157249) (a:=1419) (b:=1420) (join_sums term (lo:=157249) (a:=709) (b:=710) r157249 r157958) (join_sums term (lo:=158668) (a:=710) (b:=710) r158668 r159378))) (join_sums term (lo:=160088) (a:=2838) (b:=2839) (join_sums term (lo:=160088) (a:=1419) (b:=1419) (join_sums term (lo:=160088) (a:=709) (b:=710) r160088 r160797) (join_sums term (lo:=161507) (a:=709) (b:=710) r161507 r162216)) (join_sums term (lo:=162926) (a:=1419) (b:=1420) (join_sums term (lo:=162926) (a:=709) (b:=710) r162926 r163635) (join_sums term (lo:=164345) (a:=710) (b:=710) r164345 r165055)))) (join_sums term (lo:=165765) (a:=5677) (b:=5677) (join_sums term (lo:=165765) (a:=2838) (b:=2839) (join_sums term (lo:=165765) (a:=1419) (b:=1419) (join_sums term (lo:=165765) (a:=709) (b:=710) r165765 r166474) (join_sums term (lo:=167184) (a:=709) (b:=710) r167184 r167893)) (join_sums term (lo:=168603) (a:=1419) (b:=1420) (join_sums term (lo:=168603) (a:=709) (b:=710) r168603 r169312) (join_sums term (lo:=170022) (a:=710) (b:=710) r170022 r170732))) (join_sums term (lo:=171442) (a:=2838) (b:=2839) (join_sums term (lo:=171442) (a:=1419) (b:=1419) (join_sums term (lo:=171442) (a:=709) (b:=710) r171442 r172151) (join_sums term (lo:=172861) (a:=709) (b:=710) r172861 r173570)) (join_sums term (lo:=174280) (a:=1419) (b:=1420) (join_sums term (lo:=174280) (a:=709) (b:=710) r174280 r174989) (join_sums term (lo:=175699) (a:=710) (b:=710) r175699 r176409)))))

private theorem rows : blockSum term 0 177119 18911475051 :=
  join_sums term (lo:=0) (a:=154411) (b:=22708) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 177118).filter (154410 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=18911475051 :=
  right_from_blocks (l:=170000000) (b:=195000000) (small:=745089)
    RangePrimeQ170000000To195000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ170000000To195000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From154410To177118

/-
# Semiprime terms at 30,110,134,441,897 for primes above 177,118 through 207,656

The sum covers 2,512 primes. Their quotient counts are checked by the
certified prime-counting table through 170,000,000.
-/
open Finset
namespace Correction30110134441897From177118To207656

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 177118 RangePrimeQ145000000To170000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 177119 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 177118 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r177119 : blockSum term 177119 477 322147906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r177596 : blockSum term 177596 477 340187138 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r178073 : blockSum term 178073 477 377064719 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r178550 : blockSum term 178550 477 413755507 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r179027 : blockSum term 179027 477 412679516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r179504 : blockSum term 179504 477 430350037 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r179981 : blockSum term 179981 477 373296993 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r180458 : blockSum term 180458 478 297931652 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r180936 : blockSum term 180936 477 315687849 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r181413 : blockSum term 181413 477 333427504 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r181890 : blockSum term 181890 477 415817106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r182367 : blockSum term 182367 477 387106284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r182844 : blockSum term 182844 477 349377755 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r183321 : blockSum term 183321 477 376071002 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r183798 : blockSum term 183798 477 365929692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r184275 : blockSum term 184275 478 355896913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r184753 : blockSum term 184753 477 364123950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r185230 : blockSum term 185230 477 363248809 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r185707 : blockSum term 185707 477 425830446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r186184 : blockSum term 186184 477 334423007 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r186661 : blockSum term 186661 477 360640050 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r187138 : blockSum term 187138 477 368811227 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r187615 : blockSum term 187615 477 314078672 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r188092 : blockSum term 188092 478 340131403 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r188570 : blockSum term 188570 477 383948559 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r189047 : blockSum term 189047 477 365158656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r189524 : blockSum term 189524 477 373226313 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r190001 : blockSum term 190001 478 274834592 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r190479 : blockSum term 190479 477 371486772 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r190956 : blockSum term 190956 477 273583881 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r191433 : blockSum term 191433 477 405010914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r191910 : blockSum term 191910 478 368841064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r192388 : blockSum term 192388 477 350448159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r192865 : blockSum term 192865 477 332212046 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r193342 : blockSum term 193342 477 374995893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r193819 : blockSum term 193819 477 330655473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r194296 : blockSum term 194296 477 295079968 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r194773 : blockSum term 194773 477 346401495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r195250 : blockSum term 195250 477 302459723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r195727 : blockSum term 195727 478 405159772 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r196205 : blockSum term 196205 477 283775604 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r196682 : blockSum term 196682 477 326065499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r197159 : blockSum term 197159 477 351023838 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r197636 : blockSum term 197636 477 358743546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r198113 : blockSum term 198113 477 332353203 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r198590 : blockSum term 198590 477 357109631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r199067 : blockSum term 199067 477 288402160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r199544 : blockSum term 199544 478 347031704 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r200022 : blockSum term 200022 477 320920332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r200499 : blockSum term 200499 477 278046629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r200976 : blockSum term 200976 477 311083338 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r201453 : blockSum term 201453 477 385841107 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r201930 : blockSum term 201930 477 326427389 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r202407 : blockSum term 202407 477 292260698 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r202884 : blockSum term 202884 477 324947530 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r203361 : blockSum term 203361 478 291008235 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r203839 : blockSum term 203839 477 298681129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r204316 : blockSum term 204316 477 331131036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r204793 : blockSum term 204793 477 330347586 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r205270 : blockSum term 205270 478 329643104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r205748 : blockSum term 205748 477 328873606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r206225 : blockSum term 206225 477 336429262 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r206702 : blockSum term 206702 477 278334296 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r207179 : blockSum term 207179 478 383931917 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 177119 30538 22083930796 := (join_sums term (lo:=177119) (a:=15269) (b:=15269) (join_sums term (lo:=177119) (a:=7634) (b:=7635) (join_sums term (lo:=177119) (a:=3817) (b:=3817) (join_sums term (lo:=177119) (a:=1908) (b:=1909) (join_sums term (lo:=177119) (a:=954) (b:=954) (join_sums term (lo:=177119) (a:=477) (b:=477) r177119 r177596) (join_sums term (lo:=178073) (a:=477) (b:=477) r178073 r178550)) (join_sums term (lo:=179027) (a:=954) (b:=955) (join_sums term (lo:=179027) (a:=477) (b:=477) r179027 r179504) (join_sums term (lo:=179981) (a:=477) (b:=478) r179981 r180458))) (join_sums term (lo:=180936) (a:=1908) (b:=1909) (join_sums term (lo:=180936) (a:=954) (b:=954) (join_sums term (lo:=180936) (a:=477) (b:=477) r180936 r181413) (join_sums term (lo:=181890) (a:=477) (b:=477) r181890 r182367)) (join_sums term (lo:=182844) (a:=954) (b:=955) (join_sums term (lo:=182844) (a:=477) (b:=477) r182844 r183321) (join_sums term (lo:=183798) (a:=477) (b:=478) r183798 r184275)))) (join_sums term (lo:=184753) (a:=3817) (b:=3818) (join_sums term (lo:=184753) (a:=1908) (b:=1909) (join_sums term (lo:=184753) (a:=954) (b:=954) (join_sums term (lo:=184753) (a:=477) (b:=477) r184753 r185230) (join_sums term (lo:=185707) (a:=477) (b:=477) r185707 r186184)) (join_sums term (lo:=186661) (a:=954) (b:=955) (join_sums term (lo:=186661) (a:=477) (b:=477) r186661 r187138) (join_sums term (lo:=187615) (a:=477) (b:=478) r187615 r188092))) (join_sums term (lo:=188570) (a:=1909) (b:=1909) (join_sums term (lo:=188570) (a:=954) (b:=955) (join_sums term (lo:=188570) (a:=477) (b:=477) r188570 r189047) (join_sums term (lo:=189524) (a:=477) (b:=478) r189524 r190001)) (join_sums term (lo:=190479) (a:=954) (b:=955) (join_sums term (lo:=190479) (a:=477) (b:=477) r190479 r190956) (join_sums term (lo:=191433) (a:=477) (b:=478) r191433 r191910))))) (join_sums term (lo:=192388) (a:=7634) (b:=7635) (join_sums term (lo:=192388) (a:=3817) (b:=3817) (join_sums term (lo:=192388) (a:=1908) (b:=1909) (join_sums term (lo:=192388) (a:=954) (b:=954) (join_sums term (lo:=192388) (a:=477) (b:=477) r192388 r192865) (join_sums term (lo:=193342) (a:=477) (b:=477) r193342 r193819)) (join_sums term (lo:=194296) (a:=954) (b:=955) (join_sums term (lo:=194296) (a:=477) (b:=477) r194296 r194773) (join_sums term (lo:=195250) (a:=477) (b:=478) r195250 r195727))) (join_sums term (lo:=196205) (a:=1908) (b:=1909) (join_sums term (lo:=196205) (a:=954) (b:=954) (join_sums term (lo:=196205) (a:=477) (b:=477) r196205 r196682) (join_sums term (lo:=197159) (a:=477) (b:=477) r197159 r197636)) (join_sums term (lo:=198113) (a:=954) (b:=955) (join_sums term (lo:=198113) (a:=477) (b:=477) r198113 r198590) (join_sums term (lo:=199067) (a:=477) (b:=478) r199067 r199544)))) (join_sums term (lo:=200022) (a:=3817) (b:=3818) (join_sums term (lo:=200022) (a:=1908) (b:=1909) (join_sums term (lo:=200022) (a:=954) (b:=954) (join_sums term (lo:=200022) (a:=477) (b:=477) r200022 r200499) (join_sums term (lo:=200976) (a:=477) (b:=477) r200976 r201453)) (join_sums term (lo:=201930) (a:=954) (b:=955) (join_sums term (lo:=201930) (a:=477) (b:=477) r201930 r202407) (join_sums term (lo:=202884) (a:=477) (b:=478) r202884 r203361))) (join_sums term (lo:=203839) (a:=1909) (b:=1909) (join_sums term (lo:=203839) (a:=954) (b:=955) (join_sums term (lo:=203839) (a:=477) (b:=477) r203839 r204316) (join_sums term (lo:=204793) (a:=477) (b:=478) r204793 r205270)) (join_sums term (lo:=205748) (a:=954) (b:=955) (join_sums term (lo:=205748) (a:=477) (b:=477) r205748 r206225) (join_sums term (lo:=206702) (a:=477) (b:=478) r206702 r207179))))))

private theorem rows : blockSum term 0 207657 22083930796 :=
  join_sums term (lo:=0) (a:=177119) (b:=30538) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 207656).filter (177118 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=22083930796 :=
  right_from_blocks (l:=145000000) (b:=170000000) (small:=745089)
    RangePrimeQ145000000To170000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ145000000To170000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From177118To207656

/-
# Semiprime terms at 30,110,134,441,897 for primes above 207,656 through 250,917

The sum covers 3,500 primes. Their quotient counts are checked by the
certified prime-counting table through 145,000,000.
-/
open Finset
namespace Correction30110134441897From207656To250917

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 207656 RangePrimeQ120000000To145000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 207657 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 207656 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r207657 : blockSum term 207657 675 456243663 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r208332 : blockSum term 208332 676 454905119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r209008 : blockSum term 209008 676 477732130 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r209684 : blockSum term 209684 676 516641398 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r210360 : blockSum term 210360 676 402433411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r211036 : blockSum term 211036 676 481455749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r211712 : blockSum term 211712 676 392019677 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r212388 : blockSum term 212388 676 390789518 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r213064 : blockSum term 213064 676 453265621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r213740 : blockSum term 213740 676 428104512 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r214416 : blockSum term 214416 676 442698460 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r215092 : blockSum term 215092 676 401912311 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r215768 : blockSum term 215768 676 400726488 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r216444 : blockSum term 216444 676 415186753 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r217120 : blockSum term 217120 676 460844941 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r217796 : blockSum term 217796 676 381564092 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r218472 : blockSum term 218472 675 481423997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r219147 : blockSum term 219147 676 433502171 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r219823 : blockSum term 219823 676 424656505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r220499 : blockSum term 220499 676 431073988 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r221175 : blockSum term 221175 676 437476546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r221851 : blockSum term 221851 676 405628693 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r222527 : blockSum term 222527 676 396837701 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r223203 : blockSum term 223203 676 449030419 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r223879 : blockSum term 223879 676 402132725 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r224555 : blockSum term 224555 676 431243108 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r225231 : blockSum term 225231 676 414960540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r225907 : blockSum term 225907 676 398742832 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r226583 : blockSum term 226583 676 405094291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r227259 : blockSum term 227259 676 396531283 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r227935 : blockSum term 227935 676 432620315 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r228611 : blockSum term 228611 676 453753810 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r229287 : blockSum term 229287 675 445056284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r229962 : blockSum term 229962 676 421682052 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r230638 : blockSum term 230638 676 376249713 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r231314 : blockSum term 231314 676 419359398 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r231990 : blockSum term 231990 676 366810207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r232666 : blockSum term 232666 676 373110647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r233342 : blockSum term 233342 676 342912852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r234018 : blockSum term 234018 676 414740283 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r234694 : blockSum term 234694 676 413643144 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r235370 : blockSum term 235370 676 340106412 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r236046 : blockSum term 236046 676 368053729 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r236722 : blockSum term 236722 676 403054586 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r237398 : blockSum term 237398 676 330128441 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r238074 : blockSum term 238074 676 436706512 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r238750 : blockSum term 238750 676 371241126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r239426 : blockSum term 239426 676 412955038 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r240102 : blockSum term 240102 676 369250461 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r240778 : blockSum term 240778 676 396590023 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r241454 : blockSum term 241454 676 430874781 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r242130 : blockSum term 242130 676 380398207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r242806 : blockSum term 242806 676 351284290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r243482 : blockSum term 243482 676 371417054 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r244158 : blockSum term 244158 676 426359516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r244834 : blockSum term 244834 676 355540123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r245510 : blockSum term 245510 676 382440041 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r246186 : blockSum term 246186 676 409148662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r246862 : blockSum term 246862 676 352759898 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r247538 : blockSum term 247538 676 427712998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r248214 : blockSum term 248214 676 412824807 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r248890 : blockSum term 248890 676 370575695 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r249566 : blockSum term 249566 676 342302101 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r250242 : blockSum term 250242 676 314065242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 207657 43261 26080587090 := (join_sums term (lo:=207657) (a:=21630) (b:=21631) (join_sums term (lo:=207657) (a:=10815) (b:=10815) (join_sums term (lo:=207657) (a:=5407) (b:=5408) (join_sums term (lo:=207657) (a:=2703) (b:=2704) (join_sums term (lo:=207657) (a:=1351) (b:=1352) (join_sums term (lo:=207657) (a:=675) (b:=676) r207657 r208332) (join_sums term (lo:=209008) (a:=676) (b:=676) r209008 r209684)) (join_sums term (lo:=210360) (a:=1352) (b:=1352) (join_sums term (lo:=210360) (a:=676) (b:=676) r210360 r211036) (join_sums term (lo:=211712) (a:=676) (b:=676) r211712 r212388))) (join_sums term (lo:=213064) (a:=2704) (b:=2704) (join_sums term (lo:=213064) (a:=1352) (b:=1352) (join_sums term (lo:=213064) (a:=676) (b:=676) r213064 r213740) (join_sums term (lo:=214416) (a:=676) (b:=676) r214416 r215092)) (join_sums term (lo:=215768) (a:=1352) (b:=1352) (join_sums term (lo:=215768) (a:=676) (b:=676) r215768 r216444) (join_sums term (lo:=217120) (a:=676) (b:=676) r217120 r217796)))) (join_sums term (lo:=218472) (a:=5407) (b:=5408) (join_sums term (lo:=218472) (a:=2703) (b:=2704) (join_sums term (lo:=218472) (a:=1351) (b:=1352) (join_sums term (lo:=218472) (a:=675) (b:=676) r218472 r219147) (join_sums term (lo:=219823) (a:=676) (b:=676) r219823 r220499)) (join_sums term (lo:=221175) (a:=1352) (b:=1352) (join_sums term (lo:=221175) (a:=676) (b:=676) r221175 r221851) (join_sums term (lo:=222527) (a:=676) (b:=676) r222527 r223203))) (join_sums term (lo:=223879) (a:=2704) (b:=2704) (join_sums term (lo:=223879) (a:=1352) (b:=1352) (join_sums term (lo:=223879) (a:=676) (b:=676) r223879 r224555) (join_sums term (lo:=225231) (a:=676) (b:=676) r225231 r225907)) (join_sums term (lo:=226583) (a:=1352) (b:=1352) (join_sums term (lo:=226583) (a:=676) (b:=676) r226583 r227259) (join_sums term (lo:=227935) (a:=676) (b:=676) r227935 r228611))))) (join_sums term (lo:=229287) (a:=10815) (b:=10816) (join_sums term (lo:=229287) (a:=5407) (b:=5408) (join_sums term (lo:=229287) (a:=2703) (b:=2704) (join_sums term (lo:=229287) (a:=1351) (b:=1352) (join_sums term (lo:=229287) (a:=675) (b:=676) r229287 r229962) (join_sums term (lo:=230638) (a:=676) (b:=676) r230638 r231314)) (join_sums term (lo:=231990) (a:=1352) (b:=1352) (join_sums term (lo:=231990) (a:=676) (b:=676) r231990 r232666) (join_sums term (lo:=233342) (a:=676) (b:=676) r233342 r234018))) (join_sums term (lo:=234694) (a:=2704) (b:=2704) (join_sums term (lo:=234694) (a:=1352) (b:=1352) (join_sums term (lo:=234694) (a:=676) (b:=676) r234694 r235370) (join_sums term (lo:=236046) (a:=676) (b:=676) r236046 r236722)) (join_sums term (lo:=237398) (a:=1352) (b:=1352) (join_sums term (lo:=237398) (a:=676) (b:=676) r237398 r238074) (join_sums term (lo:=238750) (a:=676) (b:=676) r238750 r239426)))) (join_sums term (lo:=240102) (a:=5408) (b:=5408) (join_sums term (lo:=240102) (a:=2704) (b:=2704) (join_sums term (lo:=240102) (a:=1352) (b:=1352) (join_sums term (lo:=240102) (a:=676) (b:=676) r240102 r240778) (join_sums term (lo:=241454) (a:=676) (b:=676) r241454 r242130)) (join_sums term (lo:=242806) (a:=1352) (b:=1352) (join_sums term (lo:=242806) (a:=676) (b:=676) r242806 r243482) (join_sums term (lo:=244158) (a:=676) (b:=676) r244158 r244834))) (join_sums term (lo:=245510) (a:=2704) (b:=2704) (join_sums term (lo:=245510) (a:=1352) (b:=1352) (join_sums term (lo:=245510) (a:=676) (b:=676) r245510 r246186) (join_sums term (lo:=246862) (a:=676) (b:=676) r246862 r247538)) (join_sums term (lo:=248214) (a:=1352) (b:=1352) (join_sums term (lo:=248214) (a:=676) (b:=676) r248214 r248890) (join_sums term (lo:=249566) (a:=676) (b:=676) r249566 r250242))))))

private theorem rows : blockSum term 0 250918 26080587090 :=
  join_sums term (lo:=0) (a:=207657) (b:=43261) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 250917).filter (207656 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=26080587090 :=
  right_from_blocks (l:=120000000) (b:=145000000) (small:=745089)
    RangePrimeQ120000000To145000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ120000000To145000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From207656To250917

/-
# Semiprime terms at 30,110,134,441,897 for primes above 250,917 through 320,028

The sum covers 5,504 primes. Their quotient counts are checked by the
certified prime-counting table through 120,000,000.
-/
open Finset
namespace Correction30110134441897From250917To320028

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 250917 RangePrimeQ94085731To120000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 250918 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 250917 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r250918 : blockSum term 250918 539 340635666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r251457 : blockSum term 251457 540 312752065 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r251997 : blockSum term 251997 540 284963715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r252537 : blockSum term 252537 540 270845088 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r253077 : blockSum term 253077 540 277020269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r253617 : blockSum term 253617 540 323724410 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r254157 : blockSum term 254157 540 222124269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r254697 : blockSum term 254697 540 369428152 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r255237 : blockSum term 255237 539 294935650 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r255776 : blockSum term 255776 540 294362269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r256316 : blockSum term 256316 540 247045083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r256856 : blockSum term 256856 540 273183410 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r257396 : blockSum term 257396 540 272662729 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r257936 : blockSum term 257936 540 305294475 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r258476 : blockSum term 258476 540 317950591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r259016 : blockSum term 259016 540 251191757 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r259556 : blockSum term 259556 539 290302269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r260095 : blockSum term 260095 540 263363352 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r260635 : blockSum term 260635 540 282576819 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r261175 : blockSum term 261175 540 268884268 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r261715 : blockSum term 261715 540 261818204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r262255 : blockSum term 262255 540 293985678 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r262795 : blockSum term 262795 540 267315520 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r263335 : blockSum term 263335 540 286340191 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r263875 : blockSum term 263875 540 292296206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r264415 : blockSum term 264415 540 265764847 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r264955 : blockSum term 264955 540 291164786 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r265495 : blockSum term 265495 540 277682238 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r266035 : blockSum term 266035 540 270740256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r266575 : blockSum term 266575 540 283069640 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r267115 : blockSum term 267115 540 365943992 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r267655 : blockSum term 267655 540 288416132 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r268195 : blockSum term 268195 539 217463617 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r268734 : blockSum term 268734 540 338357403 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r269274 : blockSum term 269274 540 273984851 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r269814 : blockSum term 269814 540 273429269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r270354 : blockSum term 270354 540 272954189 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r270894 : blockSum term 270894 540 272446141 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r271434 : blockSum term 271434 540 271911209 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r271974 : blockSum term 271974 540 296639990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r272514 : blockSum term 272514 540 258285191 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r273054 : blockSum term 273054 540 226408922 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r273594 : blockSum term 273594 540 263600140 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r274134 : blockSum term 274134 540 238084937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r274674 : blockSum term 274674 540 306403114 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r275214 : blockSum term 275214 540 280846098 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r275754 : blockSum term 275754 540 286553105 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r276294 : blockSum term 276294 540 273593154 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r276834 : blockSum term 276834 539 254477124 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r277373 : blockSum term 277373 540 260181464 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r277913 : blockSum term 277913 540 228791118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r278453 : blockSum term 278453 540 296282797 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r278993 : blockSum term 278993 540 221801353 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r279533 : blockSum term 279533 540 270600424 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r280073 : blockSum term 280073 540 270072328 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r280613 : blockSum term 280613 540 269606599 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r281153 : blockSum term 281153 540 293559087 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r281693 : blockSum term 281693 540 280837907 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r282233 : blockSum term 282233 540 255939423 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r282773 : blockSum term 282773 540 261561431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r283313 : blockSum term 283313 540 230692407 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r283853 : blockSum term 283853 540 260600259 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r284393 : blockSum term 284393 540 320632572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r284933 : blockSum term 284933 540 223437832 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r285473 : blockSum term 285473 539 271276709 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r286012 : blockSum term 286012 540 228620909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r286552 : blockSum term 286552 540 216253977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r287092 : blockSum term 287092 540 257855075 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r287632 : blockSum term 287632 540 191537210 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r288172 : blockSum term 288172 540 268865841 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r288712 : blockSum term 288712 540 298172542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r289252 : blockSum term 289252 540 250040135 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r289792 : blockSum term 289792 540 249603638 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r290332 : blockSum term 290332 540 290683531 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r290872 : blockSum term 290872 540 248708540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r291412 : blockSum term 291412 540 236461271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r291952 : blockSum term 291952 540 247833100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r292492 : blockSum term 292492 540 241528729 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r293032 : blockSum term 293032 540 217590519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r293572 : blockSum term 293572 540 228938803 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r294112 : blockSum term 294112 539 269577460 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r294651 : blockSum term 294651 540 251535448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r295191 : blockSum term 295191 540 210237259 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r295731 : blockSum term 295731 540 273981045 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r296271 : blockSum term 296271 540 267660069 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r296811 : blockSum term 296811 540 209146738 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r297351 : blockSum term 297351 540 249367627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r297891 : blockSum term 297891 540 254715364 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r298431 : blockSum term 298431 540 208044834 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r298971 : blockSum term 298971 540 248072770 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r299511 : blockSum term 299511 540 236131890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r300051 : blockSum term 300051 540 247221685 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r300591 : blockSum term 300591 540 269779638 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r301131 : blockSum term 301131 540 257843582 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r301671 : blockSum term 301671 540 223098637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r302211 : blockSum term 302211 540 211289258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r302751 : blockSum term 302751 539 267954944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r303290 : blockSum term 303290 540 290264172 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r303830 : blockSum term 303830 540 232944732 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r304370 : blockSum term 304370 540 289271943 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r304910 : blockSum term 304910 540 254806353 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r305450 : blockSum term 305450 540 231788369 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r305990 : blockSum term 305990 540 259587371 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r306530 : blockSum term 306530 540 236626584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r307070 : blockSum term 307070 540 247500175 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r307610 : blockSum term 307610 540 213376976 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r308150 : blockSum term 308150 540 224228184 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r308690 : blockSum term 308690 540 235049039 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r309230 : blockSum term 309230 540 251440276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r309770 : blockSum term 309770 540 211967630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r310310 : blockSum term 310310 540 250592404 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r310850 : blockSum term 310850 540 216825870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r311390 : blockSum term 311390 539 205371365 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r311929 : blockSum term 311929 540 260439446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r312469 : blockSum term 312469 540 243414878 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r313009 : blockSum term 313009 540 215414928 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r313549 : blockSum term 313549 540 281240165 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r314089 : blockSum term 314089 540 253234637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r314629 : blockSum term 314629 540 197867307 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r315169 : blockSum term 315169 540 257884089 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r315709 : blockSum term 315709 540 224591173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r316249 : blockSum term 316249 540 240645656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r316789 : blockSum term 316789 540 240271773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r317329 : blockSum term 317329 540 256222344 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r317869 : blockSum term 317869 540 250352446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r318409 : blockSum term 318409 540 239085600 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r318949 : blockSum term 318949 540 249549718 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r319489 : blockSum term 319489 540 243746041 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 250918 69111 33363049872 := (join_sums term (lo:=250918) (a:=34555) (b:=34556) (join_sums term (lo:=250918) (a:=17277) (b:=17278) (join_sums term (lo:=250918) (a:=8638) (b:=8639) (join_sums term (lo:=250918) (a:=4319) (b:=4319) (join_sums term (lo:=250918) (a:=2159) (b:=2160) (join_sums term (lo:=250918) (a:=1079) (b:=1080) (join_sums term (lo:=250918) (a:=539) (b:=540) r250918 r251457) (join_sums term (lo:=251997) (a:=540) (b:=540) r251997 r252537)) (join_sums term (lo:=253077) (a:=1080) (b:=1080) (join_sums term (lo:=253077) (a:=540) (b:=540) r253077 r253617) (join_sums term (lo:=254157) (a:=540) (b:=540) r254157 r254697))) (join_sums term (lo:=255237) (a:=2159) (b:=2160) (join_sums term (lo:=255237) (a:=1079) (b:=1080) (join_sums term (lo:=255237) (a:=539) (b:=540) r255237 r255776) (join_sums term (lo:=256316) (a:=540) (b:=540) r256316 r256856)) (join_sums term (lo:=257396) (a:=1080) (b:=1080) (join_sums term (lo:=257396) (a:=540) (b:=540) r257396 r257936) (join_sums term (lo:=258476) (a:=540) (b:=540) r258476 r259016)))) (join_sums term (lo:=259556) (a:=4319) (b:=4320) (join_sums term (lo:=259556) (a:=2159) (b:=2160) (join_sums term (lo:=259556) (a:=1079) (b:=1080) (join_sums term (lo:=259556) (a:=539) (b:=540) r259556 r260095) (join_sums term (lo:=260635) (a:=540) (b:=540) r260635 r261175)) (join_sums term (lo:=261715) (a:=1080) (b:=1080) (join_sums term (lo:=261715) (a:=540) (b:=540) r261715 r262255) (join_sums term (lo:=262795) (a:=540) (b:=540) r262795 r263335))) (join_sums term (lo:=263875) (a:=2160) (b:=2160) (join_sums term (lo:=263875) (a:=1080) (b:=1080) (join_sums term (lo:=263875) (a:=540) (b:=540) r263875 r264415) (join_sums term (lo:=264955) (a:=540) (b:=540) r264955 r265495)) (join_sums term (lo:=266035) (a:=1080) (b:=1080) (join_sums term (lo:=266035) (a:=540) (b:=540) r266035 r266575) (join_sums term (lo:=267115) (a:=540) (b:=540) r267115 r267655))))) (join_sums term (lo:=268195) (a:=8639) (b:=8639) (join_sums term (lo:=268195) (a:=4319) (b:=4320) (join_sums term (lo:=268195) (a:=2159) (b:=2160) (join_sums term (lo:=268195) (a:=1079) (b:=1080) (join_sums term (lo:=268195) (a:=539) (b:=540) r268195 r268734) (join_sums term (lo:=269274) (a:=540) (b:=540) r269274 r269814)) (join_sums term (lo:=270354) (a:=1080) (b:=1080) (join_sums term (lo:=270354) (a:=540) (b:=540) r270354 r270894) (join_sums term (lo:=271434) (a:=540) (b:=540) r271434 r271974))) (join_sums term (lo:=272514) (a:=2160) (b:=2160) (join_sums term (lo:=272514) (a:=1080) (b:=1080) (join_sums term (lo:=272514) (a:=540) (b:=540) r272514 r273054) (join_sums term (lo:=273594) (a:=540) (b:=540) r273594 r274134)) (join_sums term (lo:=274674) (a:=1080) (b:=1080) (join_sums term (lo:=274674) (a:=540) (b:=540) r274674 r275214) (join_sums term (lo:=275754) (a:=540) (b:=540) r275754 r276294)))) (join_sums term (lo:=276834) (a:=4319) (b:=4320) (join_sums term (lo:=276834) (a:=2159) (b:=2160) (join_sums term (lo:=276834) (a:=1079) (b:=1080) (join_sums term (lo:=276834) (a:=539) (b:=540) r276834 r277373) (join_sums term (lo:=277913) (a:=540) (b:=540) r277913 r278453)) (join_sums term (lo:=278993) (a:=1080) (b:=1080) (join_sums term (lo:=278993) (a:=540) (b:=540) r278993 r279533) (join_sums term (lo:=280073) (a:=540) (b:=540) r280073 r280613))) (join_sums term (lo:=281153) (a:=2160) (b:=2160) (join_sums term (lo:=281153) (a:=1080) (b:=1080) (join_sums term (lo:=281153) (a:=540) (b:=540) r281153 r281693) (join_sums term (lo:=282233) (a:=540) (b:=540) r282233 r282773)) (join_sums term (lo:=283313) (a:=1080) (b:=1080) (join_sums term (lo:=283313) (a:=540) (b:=540) r283313 r283853) (join_sums term (lo:=284393) (a:=540) (b:=540) r284393 r284933)))))) (join_sums term (lo:=285473) (a:=17278) (b:=17278) (join_sums term (lo:=285473) (a:=8639) (b:=8639) (join_sums term (lo:=285473) (a:=4319) (b:=4320) (join_sums term (lo:=285473) (a:=2159) (b:=2160) (join_sums term (lo:=285473) (a:=1079) (b:=1080) (join_sums term (lo:=285473) (a:=539) (b:=540) r285473 r286012) (join_sums term (lo:=286552) (a:=540) (b:=540) r286552 r287092)) (join_sums term (lo:=287632) (a:=1080) (b:=1080) (join_sums term (lo:=287632) (a:=540) (b:=540) r287632 r288172) (join_sums term (lo:=288712) (a:=540) (b:=540) r288712 r289252))) (join_sums term (lo:=289792) (a:=2160) (b:=2160) (join_sums term (lo:=289792) (a:=1080) (b:=1080) (join_sums term (lo:=289792) (a:=540) (b:=540) r289792 r290332) (join_sums term (lo:=290872) (a:=540) (b:=540) r290872 r291412)) (join_sums term (lo:=291952) (a:=1080) (b:=1080) (join_sums term (lo:=291952) (a:=540) (b:=540) r291952 r292492) (join_sums term (lo:=293032) (a:=540) (b:=540) r293032 r293572)))) (join_sums term (lo:=294112) (a:=4319) (b:=4320) (join_sums term (lo:=294112) (a:=2159) (b:=2160) (join_sums term (lo:=294112) (a:=1079) (b:=1080) (join_sums term (lo:=294112) (a:=539) (b:=540) r294112 r294651) (join_sums term (lo:=295191) (a:=540) (b:=540) r295191 r295731)) (join_sums term (lo:=296271) (a:=1080) (b:=1080) (join_sums term (lo:=296271) (a:=540) (b:=540) r296271 r296811) (join_sums term (lo:=297351) (a:=540) (b:=540) r297351 r297891))) (join_sums term (lo:=298431) (a:=2160) (b:=2160) (join_sums term (lo:=298431) (a:=1080) (b:=1080) (join_sums term (lo:=298431) (a:=540) (b:=540) r298431 r298971) (join_sums term (lo:=299511) (a:=540) (b:=540) r299511 r300051)) (join_sums term (lo:=300591) (a:=1080) (b:=1080) (join_sums term (lo:=300591) (a:=540) (b:=540) r300591 r301131) (join_sums term (lo:=301671) (a:=540) (b:=540) r301671 r302211))))) (join_sums term (lo:=302751) (a:=8639) (b:=8639) (join_sums term (lo:=302751) (a:=4319) (b:=4320) (join_sums term (lo:=302751) (a:=2159) (b:=2160) (join_sums term (lo:=302751) (a:=1079) (b:=1080) (join_sums term (lo:=302751) (a:=539) (b:=540) r302751 r303290) (join_sums term (lo:=303830) (a:=540) (b:=540) r303830 r304370)) (join_sums term (lo:=304910) (a:=1080) (b:=1080) (join_sums term (lo:=304910) (a:=540) (b:=540) r304910 r305450) (join_sums term (lo:=305990) (a:=540) (b:=540) r305990 r306530))) (join_sums term (lo:=307070) (a:=2160) (b:=2160) (join_sums term (lo:=307070) (a:=1080) (b:=1080) (join_sums term (lo:=307070) (a:=540) (b:=540) r307070 r307610) (join_sums term (lo:=308150) (a:=540) (b:=540) r308150 r308690)) (join_sums term (lo:=309230) (a:=1080) (b:=1080) (join_sums term (lo:=309230) (a:=540) (b:=540) r309230 r309770) (join_sums term (lo:=310310) (a:=540) (b:=540) r310310 r310850)))) (join_sums term (lo:=311390) (a:=4319) (b:=4320) (join_sums term (lo:=311390) (a:=2159) (b:=2160) (join_sums term (lo:=311390) (a:=1079) (b:=1080) (join_sums term (lo:=311390) (a:=539) (b:=540) r311390 r311929) (join_sums term (lo:=312469) (a:=540) (b:=540) r312469 r313009)) (join_sums term (lo:=313549) (a:=1080) (b:=1080) (join_sums term (lo:=313549) (a:=540) (b:=540) r313549 r314089) (join_sums term (lo:=314629) (a:=540) (b:=540) r314629 r315169))) (join_sums term (lo:=315709) (a:=2160) (b:=2160) (join_sums term (lo:=315709) (a:=1080) (b:=1080) (join_sums term (lo:=315709) (a:=540) (b:=540) r315709 r316249) (join_sums term (lo:=316789) (a:=540) (b:=540) r316789 r317329)) (join_sums term (lo:=317869) (a:=1080) (b:=1080) (join_sums term (lo:=317869) (a:=540) (b:=540) r317869 r318409) (join_sums term (lo:=318949) (a:=540) (b:=540) r318949 r319489)))))))

private theorem rows : blockSum term 0 320029 33363049872 :=
  join_sums term (lo:=0) (a:=250918) (b:=69111) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 320028).filter (250917 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=33363049872 :=
  right_from_blocks (l:=94085731) (b:=120000000) (small:=745089)
    RangePrimeQ94085731To120000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ94085731To120000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From250917To320028

/-
# Semiprime terms at 30,110,134,441,897 for primes above 320,028 through 445,774

The sum covers 9,789 primes. Their quotient counts are checked by the
certified prime-counting table through 94,085,731.
-/
open Finset
namespace Correction30110134441897From320028To445774

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 320028 RangePrimeQ67545646To94085731.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 320029 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 320028 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r320029 : blockSum term 320029 491 221754879 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r320520 : blockSum term 320520 491 194420257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r321011 : blockSum term 321011 491 221091239 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r321502 : blockSum term 321502 491 204617853 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r321993 : blockSum term 321993 491 209710780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r322484 : blockSum term 322484 491 214769396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r322975 : blockSum term 322975 491 187646826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r323466 : blockSum term 323466 492 198086363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r323958 : blockSum term 323958 491 203132444 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r324449 : blockSum term 324449 491 224214849 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r324940 : blockSum term 324940 491 223904968 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r325431 : blockSum term 325431 492 234205511 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r325923 : blockSum term 325923 491 175421183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r326414 : blockSum term 326414 491 207004875 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r326905 : blockSum term 326905 491 196107928 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r327396 : blockSum term 327396 492 259340878 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r327888 : blockSum term 327888 491 195543866 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r328379 : blockSum term 328379 491 184712341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r328870 : blockSum term 328870 491 210787979 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r329361 : blockSum term 329361 491 194711443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r329852 : blockSum term 329852 491 225965264 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r330343 : blockSum term 330343 491 199400867 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r330834 : blockSum term 330834 491 199122495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r331325 : blockSum term 331325 492 204085999 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r331817 : blockSum term 331817 491 219467333 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r332308 : blockSum term 332308 491 172194971 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r332799 : blockSum term 332799 491 198000272 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r333290 : blockSum term 333290 492 218543441 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r333782 : blockSum term 333782 491 176667840 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r334273 : blockSum term 334273 491 212733358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r334764 : blockSum term 334764 491 207257648 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r335255 : blockSum term 335255 492 191444381 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r335747 : blockSum term 335747 491 191177292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r336238 : blockSum term 336238 491 206393293 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r336729 : blockSum term 336729 491 206125414 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r337220 : blockSum term 337220 491 205832108 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r337711 : blockSum term 337711 491 190130662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r338202 : blockSum term 338202 491 225812954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r338693 : blockSum term 338693 491 174227938 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r339184 : blockSum term 339184 492 173978567 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r339676 : blockSum term 339676 491 183965307 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r340167 : blockSum term 340167 491 193917863 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r340658 : blockSum term 340658 491 203857467 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r341149 : blockSum term 341149 492 198483940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r341641 : blockSum term 341641 491 198209253 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r342132 : blockSum term 342132 491 203019155 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r342623 : blockSum term 342623 491 167263375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r343114 : blockSum term 343114 492 222703629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r343606 : blockSum term 343606 491 171864457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r344097 : blockSum term 344097 491 201934349 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r344588 : blockSum term 344588 491 211719889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r345079 : blockSum term 345079 491 151020493 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r345570 : blockSum term 345570 491 216195189 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r346061 : blockSum term 346061 491 220902261 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r346552 : blockSum term 346552 491 175494673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r347043 : blockSum term 347043 492 200301328 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r347535 : blockSum term 347535 491 209999986 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r348026 : blockSum term 348026 491 189747069 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r348517 : blockSum term 348517 491 184515819 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r349008 : blockSum term 349008 492 204173370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r349500 : blockSum term 349500 491 198924866 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r349991 : blockSum term 349991 491 163899562 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r350482 : blockSum term 350482 491 188482321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r350973 : blockSum term 350973 492 217964516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r351465 : blockSum term 351465 491 183037344 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r351956 : blockSum term 351956 491 212429359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r352447 : blockSum term 352447 491 182556968 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r352938 : blockSum term 352938 491 172464151 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r353429 : blockSum term 353429 491 206672001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r353920 : blockSum term 353920 491 216221928 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r354411 : blockSum term 354411 491 191403196 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r354902 : blockSum term 354902 492 186265884 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r355394 : blockSum term 355394 491 195802366 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r355885 : blockSum term 355885 491 161328162 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r356376 : blockSum term 356376 491 146472698 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r356867 : blockSum term 356867 492 195029565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r357359 : blockSum term 357359 491 219105454 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r357850 : blockSum term 357850 491 170186336 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r358341 : blockSum term 358341 491 189404160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r358832 : blockSum term 358832 492 213416162 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r359324 : blockSum term 359324 491 174386300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r359815 : blockSum term 359815 491 154789075 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r360306 : blockSum term 360306 491 120792320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r360797 : blockSum term 360797 491 183365395 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r361288 : blockSum term 361288 491 192766449 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r361779 : blockSum term 361779 491 197328595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r362270 : blockSum term 362270 491 192272075 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r362761 : blockSum term 362761 492 158405302 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r363253 : blockSum term 363253 491 206161305 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r363744 : blockSum term 363744 491 181950406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r364235 : blockSum term 364235 491 196055930 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r364726 : blockSum term 364726 492 181471359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r365218 : blockSum term 365218 491 205086732 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r365709 : blockSum term 365709 491 171469828 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r366200 : blockSum term 366200 491 180797061 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r366691 : blockSum term 366691 492 204312497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r367183 : blockSum term 367183 491 189808352 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r367674 : blockSum term 367674 491 184826901 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r368165 : blockSum term 368165 491 175122295 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r368656 : blockSum term 368656 491 155988038 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r369147 : blockSum term 369147 491 127482384 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r369638 : blockSum term 369638 491 183887543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r370129 : blockSum term 370129 491 178939476 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r370620 : blockSum term 370620 492 136396193 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r371112 : blockSum term 371112 491 187903124 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r371603 : blockSum term 371603 491 164189004 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r372094 : blockSum term 372094 491 168681226 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r372585 : blockSum term 372585 492 205903398 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r373077 : blockSum term 373077 491 182268935 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r373568 : blockSum term 373568 491 154024627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r374059 : blockSum term 374059 491 172502749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r374550 : blockSum term 374550 492 200203847 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r375042 : blockSum term 375042 491 218566458 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r375533 : blockSum term 375533 491 181129766 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r376024 : blockSum term 376024 491 148434166 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r376515 : blockSum term 376515 492 203851304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r377007 : blockSum term 377007 491 157322844 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r377498 : blockSum term 377498 491 166384564 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r377989 : blockSum term 377989 491 166168978 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r378480 : blockSum term 378480 492 184399540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r378972 : blockSum term 378972 491 188770542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r379463 : blockSum term 379463 491 179339636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r379954 : blockSum term 379954 491 174527446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r380445 : blockSum term 380445 492 155964163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r380937 : blockSum term 380937 491 178676834 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r381428 : blockSum term 381428 491 164743187 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r381919 : blockSum term 381919 491 146258011 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r382410 : blockSum term 382410 492 191714606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r382902 : blockSum term 382902 491 159578431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r383393 : blockSum term 383393 491 191249845 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r383884 : blockSum term 383884 491 195564716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r384375 : blockSum term 384375 491 172613495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r384866 : blockSum term 384866 491 167866274 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r385357 : blockSum term 385357 491 176730127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r385848 : blockSum term 385848 491 181036080 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r386339 : blockSum term 386339 492 171792385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r386831 : blockSum term 386831 491 162536605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r387322 : blockSum term 387322 491 148809360 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r387813 : blockSum term 387813 491 162138179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r388304 : blockSum term 388304 492 157451246 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r388796 : blockSum term 388796 491 175240543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r389287 : blockSum term 389287 491 175026101 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r389778 : blockSum term 389778 491 188269334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r390269 : blockSum term 390269 492 188044666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r390761 : blockSum term 390761 491 178866481 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r391252 : blockSum term 391252 491 160787752 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r391743 : blockSum term 391743 491 187356921 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r392234 : blockSum term 392234 491 178242420 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r392725 : blockSum term 392725 491 209165703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r393216 : blockSum term 393216 491 182240793 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r393707 : blockSum term 393707 491 164281580 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r394198 : blockSum term 394198 492 155211359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r394690 : blockSum term 394690 491 190462030 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r395181 : blockSum term 395181 491 159272202 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r395672 : blockSum term 395672 491 141404385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r396163 : blockSum term 396163 492 185369929 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r396655 : blockSum term 396655 491 136654136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r397146 : blockSum term 397146 491 171725052 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r397637 : blockSum term 397637 491 171514666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r398128 : blockSum term 398128 492 188885398 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r398620 : blockSum term 398620 491 157947815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r399111 : blockSum term 399111 491 175293043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r399602 : blockSum term 399602 491 166337284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r400093 : blockSum term 400093 491 148660600 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r400584 : blockSum term 400584 491 152845994 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r401075 : blockSum term 401075 491 148305555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r401566 : blockSum term 401566 491 161191314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r402057 : blockSum term 402057 492 161009201 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r402549 : blockSum term 402549 491 156482291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r403040 : blockSum term 403040 491 147624349 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r403531 : blockSum term 403531 491 182131143 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r404022 : blockSum term 404022 492 173249723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r404514 : blockSum term 404514 491 116807854 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r405005 : blockSum term 405005 491 159894178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r405496 : blockSum term 405496 491 181297204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r405987 : blockSum term 405987 492 137973756 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r406479 : blockSum term 406479 491 155053086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r406970 : blockSum term 406970 491 154854276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r407461 : blockSum term 407461 491 180462409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r407952 : blockSum term 407952 491 180248496 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r408443 : blockSum term 408443 491 154324454 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r408934 : blockSum term 408934 491 158431981 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r409425 : blockSum term 409425 491 183902490 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r409916 : blockSum term 409916 492 166604279 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r410408 : blockSum term 410408 491 153624047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r410899 : blockSum term 410899 491 161969707 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r411390 : blockSum term 411390 491 174556121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r411881 : blockSum term 411881 492 182867037 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r412373 : blockSum term 412373 491 131681889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r412864 : blockSum term 412864 491 156988532 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r413355 : blockSum term 413355 491 127137028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r413846 : blockSum term 413846 492 169329394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r414338 : blockSum term 414338 491 194504673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r414829 : blockSum term 414829 491 164728304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r415320 : blockSum term 415320 491 164529082 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r415811 : blockSum term 415811 491 151710208 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r416302 : blockSum term 416302 491 143133817 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r416793 : blockSum term 416793 491 155566662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r417284 : blockSum term 417284 491 172187871 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r417775 : blockSum term 417775 492 159413874 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r418267 : blockSum term 418267 491 155054413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r418758 : blockSum term 418758 491 175814798 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r419249 : blockSum term 419249 491 171424850 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r419740 : blockSum term 419740 492 133653076 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r420232 : blockSum term 420232 491 166884931 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r420723 : blockSum term 420723 491 170850118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r421214 : blockSum term 421214 491 149836835 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r421705 : blockSum term 421705 492 145516123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r422197 : blockSum term 422197 491 141215125 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r422688 : blockSum term 422688 491 174237929 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r423179 : blockSum term 423179 491 174049997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r423670 : blockSum term 423670 491 169704342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r424161 : blockSum term 424161 491 144718889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r424652 : blockSum term 424652 491 165210701 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r425143 : blockSum term 425143 491 156774925 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r425634 : blockSum term 425634 492 140112256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r426126 : blockSum term 426126 491 123497719 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r426617 : blockSum term 426617 491 176816880 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r427108 : blockSum term 427108 491 160184284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r427599 : blockSum term 427599 492 151795277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r428091 : blockSum term 428091 491 151637021 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r428582 : blockSum term 428582 491 118729176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r429073 : blockSum term 429073 491 184016005 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r429564 : blockSum term 429564 492 183819647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r430056 : blockSum term 430056 491 122413187 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r430547 : blockSum term 430547 491 183417557 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r431038 : blockSum term 431038 491 154725949 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r431529 : blockSum term 431529 491 162684720 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r432020 : blockSum term 432020 491 182826047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r432511 : blockSum term 432511 491 150160671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r433002 : blockSum term 433002 491 174318434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r433493 : blockSum term 433493 492 149829896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r433985 : blockSum term 433985 491 165836429 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r434476 : blockSum term 434476 491 165652158 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r434967 : blockSum term 434967 491 161444680 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r435458 : blockSum term 435458 492 169339053 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r435950 : blockSum term 435950 491 132911122 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r436441 : blockSum term 436441 491 144843891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r436932 : blockSum term 436932 491 152721073 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r437423 : blockSum term 437423 492 136498880 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r437915 : blockSum term 437915 491 128328032 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r438406 : blockSum term 438406 491 152231409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r438897 : blockSum term 438897 491 132061542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r439388 : blockSum term 439388 492 167892231 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r439880 : blockSum term 439880 491 147748359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r440371 : blockSum term 440371 491 163552823 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r440862 : blockSum term 440862 491 155406990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r441353 : blockSum term 441353 492 143291388 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r441845 : blockSum term 441845 491 159042693 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r442336 : blockSum term 442336 491 150928872 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r442827 : blockSum term 442827 491 182515966 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r443318 : blockSum term 443318 492 158543118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r443810 : blockSum term 443810 491 166293006 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r444301 : blockSum term 444301 491 146344966 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r444792 : blockSum term 444792 491 158049082 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r445283 : blockSum term 445283 492 130240950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 320029 125746 45053794298 := (join_sums term (lo:=320029) (a:=62873) (b:=62873) (join_sums term (lo:=320029) (a:=31436) (b:=31437) (join_sums term (lo:=320029) (a:=15718) (b:=15718) (join_sums term (lo:=320029) (a:=7859) (b:=7859) (join_sums term (lo:=320029) (a:=3929) (b:=3930) (join_sums term (lo:=320029) (a:=1964) (b:=1965) (join_sums term (lo:=320029) (a:=982) (b:=982) (join_sums term (lo:=320029) (a:=491) (b:=491) r320029 r320520) (join_sums term (lo:=321011) (a:=491) (b:=491) r321011 r321502)) (join_sums term (lo:=321993) (a:=982) (b:=983) (join_sums term (lo:=321993) (a:=491) (b:=491) r321993 r322484) (join_sums term (lo:=322975) (a:=491) (b:=492) r322975 r323466))) (join_sums term (lo:=323958) (a:=1965) (b:=1965) (join_sums term (lo:=323958) (a:=982) (b:=983) (join_sums term (lo:=323958) (a:=491) (b:=491) r323958 r324449) (join_sums term (lo:=324940) (a:=491) (b:=492) r324940 r325431)) (join_sums term (lo:=325923) (a:=982) (b:=983) (join_sums term (lo:=325923) (a:=491) (b:=491) r325923 r326414) (join_sums term (lo:=326905) (a:=491) (b:=492) r326905 r327396)))) (join_sums term (lo:=327888) (a:=3929) (b:=3930) (join_sums term (lo:=327888) (a:=1964) (b:=1965) (join_sums term (lo:=327888) (a:=982) (b:=982) (join_sums term (lo:=327888) (a:=491) (b:=491) r327888 r328379) (join_sums term (lo:=328870) (a:=491) (b:=491) r328870 r329361)) (join_sums term (lo:=329852) (a:=982) (b:=983) (join_sums term (lo:=329852) (a:=491) (b:=491) r329852 r330343) (join_sums term (lo:=330834) (a:=491) (b:=492) r330834 r331325))) (join_sums term (lo:=331817) (a:=1965) (b:=1965) (join_sums term (lo:=331817) (a:=982) (b:=983) (join_sums term (lo:=331817) (a:=491) (b:=491) r331817 r332308) (join_sums term (lo:=332799) (a:=491) (b:=492) r332799 r333290)) (join_sums term (lo:=333782) (a:=982) (b:=983) (join_sums term (lo:=333782) (a:=491) (b:=491) r333782 r334273) (join_sums term (lo:=334764) (a:=491) (b:=492) r334764 r335255))))) (join_sums term (lo:=335747) (a:=7859) (b:=7859) (join_sums term (lo:=335747) (a:=3929) (b:=3930) (join_sums term (lo:=335747) (a:=1964) (b:=1965) (join_sums term (lo:=335747) (a:=982) (b:=982) (join_sums term (lo:=335747) (a:=491) (b:=491) r335747 r336238) (join_sums term (lo:=336729) (a:=491) (b:=491) r336729 r337220)) (join_sums term (lo:=337711) (a:=982) (b:=983) (join_sums term (lo:=337711) (a:=491) (b:=491) r337711 r338202) (join_sums term (lo:=338693) (a:=491) (b:=492) r338693 r339184))) (join_sums term (lo:=339676) (a:=1965) (b:=1965) (join_sums term (lo:=339676) (a:=982) (b:=983) (join_sums term (lo:=339676) (a:=491) (b:=491) r339676 r340167) (join_sums term (lo:=340658) (a:=491) (b:=492) r340658 r341149)) (join_sums term (lo:=341641) (a:=982) (b:=983) (join_sums term (lo:=341641) (a:=491) (b:=491) r341641 r342132) (join_sums term (lo:=342623) (a:=491) (b:=492) r342623 r343114)))) (join_sums term (lo:=343606) (a:=3929) (b:=3930) (join_sums term (lo:=343606) (a:=1964) (b:=1965) (join_sums term (lo:=343606) (a:=982) (b:=982) (join_sums term (lo:=343606) (a:=491) (b:=491) r343606 r344097) (join_sums term (lo:=344588) (a:=491) (b:=491) r344588 r345079)) (join_sums term (lo:=345570) (a:=982) (b:=983) (join_sums term (lo:=345570) (a:=491) (b:=491) r345570 r346061) (join_sums term (lo:=346552) (a:=491) (b:=492) r346552 r347043))) (join_sums term (lo:=347535) (a:=1965) (b:=1965) (join_sums term (lo:=347535) (a:=982) (b:=983) (join_sums term (lo:=347535) (a:=491) (b:=491) r347535 r348026) (join_sums term (lo:=348517) (a:=491) (b:=492) r348517 r349008)) (join_sums term (lo:=349500) (a:=982) (b:=983) (join_sums term (lo:=349500) (a:=491) (b:=491) r349500 r349991) (join_sums term (lo:=350482) (a:=491) (b:=492) r350482 r350973)))))) (join_sums term (lo:=351465) (a:=15718) (b:=15719) (join_sums term (lo:=351465) (a:=7859) (b:=7859) (join_sums term (lo:=351465) (a:=3929) (b:=3930) (join_sums term (lo:=351465) (a:=1964) (b:=1965) (join_sums term (lo:=351465) (a:=982) (b:=982) (join_sums term (lo:=351465) (a:=491) (b:=491) r351465 r351956) (join_sums term (lo:=352447) (a:=491) (b:=491) r352447 r352938)) (join_sums term (lo:=353429) (a:=982) (b:=983) (join_sums term (lo:=353429) (a:=491) (b:=491) r353429 r353920) (join_sums term (lo:=354411) (a:=491) (b:=492) r354411 r354902))) (join_sums term (lo:=355394) (a:=1965) (b:=1965) (join_sums term (lo:=355394) (a:=982) (b:=983) (join_sums term (lo:=355394) (a:=491) (b:=491) r355394 r355885) (join_sums term (lo:=356376) (a:=491) (b:=492) r356376 r356867)) (join_sums term (lo:=357359) (a:=982) (b:=983) (join_sums term (lo:=357359) (a:=491) (b:=491) r357359 r357850) (join_sums term (lo:=358341) (a:=491) (b:=492) r358341 r358832)))) (join_sums term (lo:=359324) (a:=3929) (b:=3930) (join_sums term (lo:=359324) (a:=1964) (b:=1965) (join_sums term (lo:=359324) (a:=982) (b:=982) (join_sums term (lo:=359324) (a:=491) (b:=491) r359324 r359815) (join_sums term (lo:=360306) (a:=491) (b:=491) r360306 r360797)) (join_sums term (lo:=361288) (a:=982) (b:=983) (join_sums term (lo:=361288) (a:=491) (b:=491) r361288 r361779) (join_sums term (lo:=362270) (a:=491) (b:=492) r362270 r362761))) (join_sums term (lo:=363253) (a:=1965) (b:=1965) (join_sums term (lo:=363253) (a:=982) (b:=983) (join_sums term (lo:=363253) (a:=491) (b:=491) r363253 r363744) (join_sums term (lo:=364235) (a:=491) (b:=492) r364235 r364726)) (join_sums term (lo:=365218) (a:=982) (b:=983) (join_sums term (lo:=365218) (a:=491) (b:=491) r365218 r365709) (join_sums term (lo:=366200) (a:=491) (b:=492) r366200 r366691))))) (join_sums term (lo:=367183) (a:=7859) (b:=7860) (join_sums term (lo:=367183) (a:=3929) (b:=3930) (join_sums term (lo:=367183) (a:=1964) (b:=1965) (join_sums term (lo:=367183) (a:=982) (b:=982) (join_sums term (lo:=367183) (a:=491) (b:=491) r367183 r367674) (join_sums term (lo:=368165) (a:=491) (b:=491) r368165 r368656)) (join_sums term (lo:=369147) (a:=982) (b:=983) (join_sums term (lo:=369147) (a:=491) (b:=491) r369147 r369638) (join_sums term (lo:=370129) (a:=491) (b:=492) r370129 r370620))) (join_sums term (lo:=371112) (a:=1965) (b:=1965) (join_sums term (lo:=371112) (a:=982) (b:=983) (join_sums term (lo:=371112) (a:=491) (b:=491) r371112 r371603) (join_sums term (lo:=372094) (a:=491) (b:=492) r372094 r372585)) (join_sums term (lo:=373077) (a:=982) (b:=983) (join_sums term (lo:=373077) (a:=491) (b:=491) r373077 r373568) (join_sums term (lo:=374059) (a:=491) (b:=492) r374059 r374550)))) (join_sums term (lo:=375042) (a:=3930) (b:=3930) (join_sums term (lo:=375042) (a:=1965) (b:=1965) (join_sums term (lo:=375042) (a:=982) (b:=983) (join_sums term (lo:=375042) (a:=491) (b:=491) r375042 r375533) (join_sums term (lo:=376024) (a:=491) (b:=492) r376024 r376515)) (join_sums term (lo:=377007) (a:=982) (b:=983) (join_sums term (lo:=377007) (a:=491) (b:=491) r377007 r377498) (join_sums term (lo:=377989) (a:=491) (b:=492) r377989 r378480))) (join_sums term (lo:=378972) (a:=1965) (b:=1965) (join_sums term (lo:=378972) (a:=982) (b:=983) (join_sums term (lo:=378972) (a:=491) (b:=491) r378972 r379463) (join_sums term (lo:=379954) (a:=491) (b:=492) r379954 r380445)) (join_sums term (lo:=380937) (a:=982) (b:=983) (join_sums term (lo:=380937) (a:=491) (b:=491) r380937 r381428) (join_sums term (lo:=381919) (a:=491) (b:=492) r381919 r382410))))))) (join_sums term (lo:=382902) (a:=31436) (b:=31437) (join_sums term (lo:=382902) (a:=15718) (b:=15718) (join_sums term (lo:=382902) (a:=7859) (b:=7859) (join_sums term (lo:=382902) (a:=3929) (b:=3930) (join_sums term (lo:=382902) (a:=1964) (b:=1965) (join_sums term (lo:=382902) (a:=982) (b:=982) (join_sums term (lo:=382902) (a:=491) (b:=491) r382902 r383393) (join_sums term (lo:=383884) (a:=491) (b:=491) r383884 r384375)) (join_sums term (lo:=384866) (a:=982) (b:=983) (join_sums term (lo:=384866) (a:=491) (b:=491) r384866 r385357) (join_sums term (lo:=385848) (a:=491) (b:=492) r385848 r386339))) (join_sums term (lo:=386831) (a:=1965) (b:=1965) (join_sums term (lo:=386831) (a:=982) (b:=983) (join_sums term (lo:=386831) (a:=491) (b:=491) r386831 r387322) (join_sums term (lo:=387813) (a:=491) (b:=492) r387813 r388304)) (join_sums term (lo:=388796) (a:=982) (b:=983) (join_sums term (lo:=388796) (a:=491) (b:=491) r388796 r389287) (join_sums term (lo:=389778) (a:=491) (b:=492) r389778 r390269)))) (join_sums term (lo:=390761) (a:=3929) (b:=3930) (join_sums term (lo:=390761) (a:=1964) (b:=1965) (join_sums term (lo:=390761) (a:=982) (b:=982) (join_sums term (lo:=390761) (a:=491) (b:=491) r390761 r391252) (join_sums term (lo:=391743) (a:=491) (b:=491) r391743 r392234)) (join_sums term (lo:=392725) (a:=982) (b:=983) (join_sums term (lo:=392725) (a:=491) (b:=491) r392725 r393216) (join_sums term (lo:=393707) (a:=491) (b:=492) r393707 r394198))) (join_sums term (lo:=394690) (a:=1965) (b:=1965) (join_sums term (lo:=394690) (a:=982) (b:=983) (join_sums term (lo:=394690) (a:=491) (b:=491) r394690 r395181) (join_sums term (lo:=395672) (a:=491) (b:=492) r395672 r396163)) (join_sums term (lo:=396655) (a:=982) (b:=983) (join_sums term (lo:=396655) (a:=491) (b:=491) r396655 r397146) (join_sums term (lo:=397637) (a:=491) (b:=492) r397637 r398128))))) (join_sums term (lo:=398620) (a:=7859) (b:=7859) (join_sums term (lo:=398620) (a:=3929) (b:=3930) (join_sums term (lo:=398620) (a:=1964) (b:=1965) (join_sums term (lo:=398620) (a:=982) (b:=982) (join_sums term (lo:=398620) (a:=491) (b:=491) r398620 r399111) (join_sums term (lo:=399602) (a:=491) (b:=491) r399602 r400093)) (join_sums term (lo:=400584) (a:=982) (b:=983) (join_sums term (lo:=400584) (a:=491) (b:=491) r400584 r401075) (join_sums term (lo:=401566) (a:=491) (b:=492) r401566 r402057))) (join_sums term (lo:=402549) (a:=1965) (b:=1965) (join_sums term (lo:=402549) (a:=982) (b:=983) (join_sums term (lo:=402549) (a:=491) (b:=491) r402549 r403040) (join_sums term (lo:=403531) (a:=491) (b:=492) r403531 r404022)) (join_sums term (lo:=404514) (a:=982) (b:=983) (join_sums term (lo:=404514) (a:=491) (b:=491) r404514 r405005) (join_sums term (lo:=405496) (a:=491) (b:=492) r405496 r405987)))) (join_sums term (lo:=406479) (a:=3929) (b:=3930) (join_sums term (lo:=406479) (a:=1964) (b:=1965) (join_sums term (lo:=406479) (a:=982) (b:=982) (join_sums term (lo:=406479) (a:=491) (b:=491) r406479 r406970) (join_sums term (lo:=407461) (a:=491) (b:=491) r407461 r407952)) (join_sums term (lo:=408443) (a:=982) (b:=983) (join_sums term (lo:=408443) (a:=491) (b:=491) r408443 r408934) (join_sums term (lo:=409425) (a:=491) (b:=492) r409425 r409916))) (join_sums term (lo:=410408) (a:=1965) (b:=1965) (join_sums term (lo:=410408) (a:=982) (b:=983) (join_sums term (lo:=410408) (a:=491) (b:=491) r410408 r410899) (join_sums term (lo:=411390) (a:=491) (b:=492) r411390 r411881)) (join_sums term (lo:=412373) (a:=982) (b:=983) (join_sums term (lo:=412373) (a:=491) (b:=491) r412373 r412864) (join_sums term (lo:=413355) (a:=491) (b:=492) r413355 r413846)))))) (join_sums term (lo:=414338) (a:=15718) (b:=15719) (join_sums term (lo:=414338) (a:=7859) (b:=7859) (join_sums term (lo:=414338) (a:=3929) (b:=3930) (join_sums term (lo:=414338) (a:=1964) (b:=1965) (join_sums term (lo:=414338) (a:=982) (b:=982) (join_sums term (lo:=414338) (a:=491) (b:=491) r414338 r414829) (join_sums term (lo:=415320) (a:=491) (b:=491) r415320 r415811)) (join_sums term (lo:=416302) (a:=982) (b:=983) (join_sums term (lo:=416302) (a:=491) (b:=491) r416302 r416793) (join_sums term (lo:=417284) (a:=491) (b:=492) r417284 r417775))) (join_sums term (lo:=418267) (a:=1965) (b:=1965) (join_sums term (lo:=418267) (a:=982) (b:=983) (join_sums term (lo:=418267) (a:=491) (b:=491) r418267 r418758) (join_sums term (lo:=419249) (a:=491) (b:=492) r419249 r419740)) (join_sums term (lo:=420232) (a:=982) (b:=983) (join_sums term (lo:=420232) (a:=491) (b:=491) r420232 r420723) (join_sums term (lo:=421214) (a:=491) (b:=492) r421214 r421705)))) (join_sums term (lo:=422197) (a:=3929) (b:=3930) (join_sums term (lo:=422197) (a:=1964) (b:=1965) (join_sums term (lo:=422197) (a:=982) (b:=982) (join_sums term (lo:=422197) (a:=491) (b:=491) r422197 r422688) (join_sums term (lo:=423179) (a:=491) (b:=491) r423179 r423670)) (join_sums term (lo:=424161) (a:=982) (b:=983) (join_sums term (lo:=424161) (a:=491) (b:=491) r424161 r424652) (join_sums term (lo:=425143) (a:=491) (b:=492) r425143 r425634))) (join_sums term (lo:=426126) (a:=1965) (b:=1965) (join_sums term (lo:=426126) (a:=982) (b:=983) (join_sums term (lo:=426126) (a:=491) (b:=491) r426126 r426617) (join_sums term (lo:=427108) (a:=491) (b:=492) r427108 r427599)) (join_sums term (lo:=428091) (a:=982) (b:=983) (join_sums term (lo:=428091) (a:=491) (b:=491) r428091 r428582) (join_sums term (lo:=429073) (a:=491) (b:=492) r429073 r429564))))) (join_sums term (lo:=430056) (a:=7859) (b:=7860) (join_sums term (lo:=430056) (a:=3929) (b:=3930) (join_sums term (lo:=430056) (a:=1964) (b:=1965) (join_sums term (lo:=430056) (a:=982) (b:=982) (join_sums term (lo:=430056) (a:=491) (b:=491) r430056 r430547) (join_sums term (lo:=431038) (a:=491) (b:=491) r431038 r431529)) (join_sums term (lo:=432020) (a:=982) (b:=983) (join_sums term (lo:=432020) (a:=491) (b:=491) r432020 r432511) (join_sums term (lo:=433002) (a:=491) (b:=492) r433002 r433493))) (join_sums term (lo:=433985) (a:=1965) (b:=1965) (join_sums term (lo:=433985) (a:=982) (b:=983) (join_sums term (lo:=433985) (a:=491) (b:=491) r433985 r434476) (join_sums term (lo:=434967) (a:=491) (b:=492) r434967 r435458)) (join_sums term (lo:=435950) (a:=982) (b:=983) (join_sums term (lo:=435950) (a:=491) (b:=491) r435950 r436441) (join_sums term (lo:=436932) (a:=491) (b:=492) r436932 r437423)))) (join_sums term (lo:=437915) (a:=3930) (b:=3930) (join_sums term (lo:=437915) (a:=1965) (b:=1965) (join_sums term (lo:=437915) (a:=982) (b:=983) (join_sums term (lo:=437915) (a:=491) (b:=491) r437915 r438406) (join_sums term (lo:=438897) (a:=491) (b:=492) r438897 r439388)) (join_sums term (lo:=439880) (a:=982) (b:=983) (join_sums term (lo:=439880) (a:=491) (b:=491) r439880 r440371) (join_sums term (lo:=440862) (a:=491) (b:=492) r440862 r441353))) (join_sums term (lo:=441845) (a:=1965) (b:=1965) (join_sums term (lo:=441845) (a:=982) (b:=983) (join_sums term (lo:=441845) (a:=491) (b:=491) r441845 r442336) (join_sums term (lo:=442827) (a:=491) (b:=492) r442827 r443318)) (join_sums term (lo:=443810) (a:=982) (b:=983) (join_sums term (lo:=443810) (a:=491) (b:=491) r443810 r444301) (join_sums term (lo:=444792) (a:=491) (b:=492) r444792 r445283))))))))

private theorem rows : blockSum term 0 445775 45053794298 :=
  join_sums term (lo:=0) (a:=320029) (b:=125746) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 445774).filter (320028 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=45053794298 :=
  right_from_blocks (l:=67545646) (b:=94085731) (small:=745089)
    RangePrimeQ67545646To94085731.fast FastDenseA26.fast FastDenseA26.prime QuotientQ67545646To94085731.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From320028To445774

/-
# Semiprime correction from 54,745 through 445,774 at 30,110,134,441,897

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined30110134441897From54745To445774

private theorem split_primes {y m z : ℕ} (ym : y ≤ m) (mz : m ≤ z) (f : ℕ → ℕ) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·), f p) =
    (∑ p ∈ (Nat.primesLE m).filter (y < ·), f p) +
    (∑ p ∈ (Nat.primesLE z).filter (m < ·), f p) := by
  have un : (Nat.primesLE z).filter (y < ·) =
      (Nat.primesLE m).filter (y < ·) ∪ (Nat.primesLE z).filter (m < ·) := by
    ext p
    simp only [Finset.mem_union,Finset.mem_filter,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨top,prime⟩,above⟩
      by_cases left : p ≤ m
      · exact Or.inl ⟨⟨left,prime⟩,above⟩
      · exact Or.inr ⟨⟨top,prime⟩,by omega⟩
    · rintro (⟨⟨top,prime⟩,above⟩ | ⟨⟨top,prime⟩,above⟩)
      · exact ⟨⟨top.trans mz,prime⟩,above⟩
      · exact ⟨⟨top,prime⟩,lt_of_le_of_lt ym above⟩
  have dis : Disjoint ((Nat.primesLE m).filter (y < ·)) ((Nat.primesLE z).filter (m < ·)) := by
    apply Finset.disjoint_left.mpr
    intro p lower upper
    exact (not_lt_of_ge (Nat.le_of_mem_primesLE (Finset.mem_filter.mp lower).1))
      (Finset.mem_filter.mp upper).2
  rw [un,Finset.sum_union dis]

private theorem join_value {y m z a b c : ℕ} (f : ℕ → ℕ) (ym : y ≤ m) (mz : m ≤ z)
    (left : (∑ p ∈ (Nat.primesLE m).filter (y < ·), f p)=a)
    (right : (∑ p ∈ (Nat.primesLE z).filter (m < ·), f p)=b) (total : a+b=c) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·), f p)=c := by
  rw [split_primes ym mz f,left,right,total]

private theorem until60220 : (∑ p ∈ (Nat.primesLE 60220).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=14025470414 :=
  join_value (y:=54745) (m:=57352) (z:=60220) (a:=6961605614) (b:=7063864800) (c:=14025470414)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction30110134441897From54745To57352.interval_sum Correction30110134441897From57352To60220.interval_sum rfl

private theorem until60828 : (∑ p ∈ (Nat.primesLE 60828).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=15414989354 :=
  join_value (y:=54745) (m:=60220) (z:=60828) (a:=14025470414) (b:=1389518940) (c:=15414989354)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until60220 Correction30110134441897From60220To60828.interval_sum rfl

private theorem until64064 : (∑ p ∈ (Nat.primesLE 64064).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=22744394249 :=
  join_value (y:=54745) (m:=60828) (z:=64064) (a:=15414989354) (b:=7329404895) (c:=22744394249)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until60828 Correction30110134441897From60828To64064.interval_sum rfl

private theorem until67663 : (∑ p ∈ (Nat.primesLE 67663).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=30510428279 :=
  join_value (y:=54745) (m:=64064) (z:=67663) (a:=22744394249) (b:=7766034030) (c:=30510428279)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until64064 Correction30110134441897From64064To67663.interval_sum rfl

private theorem until71690 : (∑ p ∈ (Nat.primesLE 71690).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=38655174214 :=
  join_value (y:=54745) (m:=67663) (z:=71690) (a:=30510428279) (b:=8144745935) (c:=38655174214)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until67663 Correction30110134441897From67663To71690.interval_sum rfl

private theorem until76228 : (∑ p ∈ (Nat.primesLE 76228).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=47466225570 :=
  join_value (y:=54745) (m:=71690) (z:=76228) (a:=38655174214) (b:=8811051356) (c:=47466225570)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until71690 Correction30110134441897From71690To76228.interval_sum rfl

private theorem until81378 : (∑ p ∈ (Nat.primesLE 81378).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=56921838301 :=
  join_value (y:=54745) (m:=76228) (z:=81378) (a:=47466225570) (b:=9455612731) (c:=56921838301)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until76228 Correction30110134441897From76228To81378.interval_sum rfl

private theorem until87275 : (∑ p ∈ (Nat.primesLE 87275).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=66677049825 :=
  join_value (y:=54745) (m:=81378) (z:=87275) (a:=56921838301) (b:=9755211524) (c:=66677049825)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until81378 Correction30110134441897From81378To87275.interval_sum rfl

private theorem until94094 : (∑ p ∈ (Nat.primesLE 94094).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=77480648557 :=
  join_value (y:=54745) (m:=87275) (z:=94094) (a:=66677049825) (b:=10803598732) (c:=77480648557)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until87275 Correction30110134441897From87275To94094.interval_sum rfl

private theorem until102068 : (∑ p ∈ (Nat.primesLE 102068).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=89057373843 :=
  join_value (y:=54745) (m:=94094) (z:=102068) (a:=77480648557) (b:=11576725286) (c:=89057373843)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until94094 Correction30110134441897From94094To102068.interval_sum rfl

private theorem until111519 : (∑ p ∈ (Nat.primesLE 111519).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=101362851316 :=
  join_value (y:=54745) (m:=102068) (z:=111519) (a:=89057373843) (b:=12305477473) (c:=101362851316)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until102068 Correction30110134441897From102068To111519.interval_sum rfl

private theorem until122898 : (∑ p ∈ (Nat.primesLE 122898).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=115099132384 :=
  join_value (y:=54745) (m:=111519) (z:=122898) (a:=101362851316) (b:=13736281068) (c:=115099132384)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until111519 Correction30110134441897From111519To122898.interval_sum rfl

private theorem until136864 : (∑ p ∈ (Nat.primesLE 136864).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=130264024132 :=
  join_value (y:=54745) (m:=122898) (z:=136864) (a:=115099132384) (b:=15164891748) (c:=130264024132)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until122898 Correction30110134441897From122898To136864.interval_sum rfl

private theorem until154410 : (∑ p ∈ (Nat.primesLE 154410).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=147154005047 :=
  join_value (y:=54745) (m:=136864) (z:=154410) (a:=130264024132) (b:=16889980915) (c:=147154005047)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until136864 Correction30110134441897From136864To154410.interval_sum rfl

private theorem until177118 : (∑ p ∈ (Nat.primesLE 177118).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=166065480098 :=
  join_value (y:=54745) (m:=154410) (z:=177118) (a:=147154005047) (b:=18911475051) (c:=166065480098)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until154410 Correction30110134441897From154410To177118.interval_sum rfl

private theorem until207656 : (∑ p ∈ (Nat.primesLE 207656).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=188149410894 :=
  join_value (y:=54745) (m:=177118) (z:=207656) (a:=166065480098) (b:=22083930796) (c:=188149410894)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until177118 Correction30110134441897From177118To207656.interval_sum rfl

private theorem until250917 : (∑ p ∈ (Nat.primesLE 250917).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=214229997984 :=
  join_value (y:=54745) (m:=207656) (z:=250917) (a:=188149410894) (b:=26080587090) (c:=214229997984)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until207656 Correction30110134441897From207656To250917.interval_sum rfl

private theorem until320028 : (∑ p ∈ (Nat.primesLE 320028).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=247593047856 :=
  join_value (y:=54745) (m:=250917) (z:=320028) (a:=214229997984) (b:=33363049872) (c:=247593047856)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until250917 Correction30110134441897From250917To320028.interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 445774).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=292646842154 :=
  join_value (y:=54745) (m:=320028) (z:=445774) (a:=247593047856) (b:=45053794298) (c:=292646842154)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until320028 Correction30110134441897From320028To445774.interval_sum rfl

end Combined30110134441897From54745To445774

open Finset
namespace EighthQuotientsThrough550m

private theorem split_primes {y m z : ℕ} (ym : y ≤ m) (mz : m ≤ z) (f : ℕ → ℕ) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·), f p) =
    (∑ p ∈ (Nat.primesLE m).filter (y < ·), f p) +
    (∑ p ∈ (Nat.primesLE z).filter (m < ·), f p) := by
  have un : (Nat.primesLE z).filter (y < ·) =
      (Nat.primesLE m).filter (y < ·) ∪ (Nat.primesLE z).filter (m < ·) := by
    ext p
    simp only [Finset.mem_union,Finset.mem_filter,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨top,prime⟩,above⟩
      by_cases left : p ≤ m
      · exact Or.inl ⟨⟨left,prime⟩,above⟩
      · exact Or.inr ⟨⟨top,prime⟩,by omega⟩
    · rintro (⟨⟨top,prime⟩,above⟩ | ⟨⟨top,prime⟩,above⟩)
      · exact ⟨⟨top.trans mz,prime⟩,above⟩
      · exact ⟨⟨top,prime⟩,lt_of_le_of_lt ym above⟩
  have dis : Disjoint ((Nat.primesLE m).filter (y < ·)) ((Nat.primesLE z).filter (m < ·)) := by
    apply Finset.disjoint_left.mpr
    intro p lower upper
    exact (not_lt_of_ge (Nat.le_of_mem_primesLE (Finset.mem_filter.mp lower).1))
      (Finset.mem_filter.mp upper).2
  rw [un,Finset.sum_union dis]

private theorem join_value {y m z a b c : ℕ} (f : ℕ → ℕ) (ym : y ≤ m) (mz : m ≤ z)
    (left : (∑ p ∈ (Nat.primesLE m).filter (y < ·), f p)=a)
    (right : (∑ p ∈ (Nat.primesLE z).filter (m < ·), f p)=b) (total : a+b=c) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·), f p)=c := by
  rw [split_primes ym mz f,left,right,total]


theorem checked_sum : (∑ p ∈ (Nat.primesLE 5487270).filter (54745 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=559251608210 :=
  join_value (y:=54745) (m:=445774) (z:=5487270) (a:=292646842154) (b:=266604766056) (c:=559251608210)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Combined30110134441897From54745To445774.interval_sum Combined30110134441897From445774To5487270.interval_sum rfl

end EighthQuotientsThrough550m
