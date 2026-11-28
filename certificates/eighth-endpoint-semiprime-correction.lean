import certificates.«eighth-semiprime-quotients-through-550m»
import certificates.«prime-table-550000000-575000000»
import certificates.«prime-table-575000000-600000000»
import certificates.«prime-table-600000000-625000000»
import certificates.«prime-table-625000000-650000000»
import certificates.«prime-table-650000000-675000000»
import certificates.«prime-table-675000000-700000000»
import certificates.«prime-table-700000000-725000000»
import certificates.«prime-table-725000000-750000000»
import certificates.«prime-table-750000000-775000000»
import certificates.«prime-table-775000000-800000000»
import certificates.«prime-table-800000000-825000000»
import certificates.«prime-table-825000000-850000000»
import certificates.«prime-table-850000000-875000000»
import certificates.«prime-table-875000000-900000000»
import certificates.«prime-table-900000000-925000000»
import certificates.«prime-table-925000000-950000000»
import certificates.«prime-table-950000000-975000000»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Complete semiprime correction for the eighth endpoint

At 30,110,134,441,897, the 376,624 summands between its integer cube and square roots total 642,072,173,249.
-/

/-
# Semiprime terms at 30,110,134,441,897 for primes above 31,110 through 31,694

The sum covers 58 primes. Their quotient counts are checked by the
certified prime-counting table through 975,000,000.
-/
open Finset
namespace Correction30110134441897From31110To31694

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


private abbrev term := contribution 30110134441897 31110 RangePrimeQ950000000To975000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 31111 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 31110 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r31111 : blockSum term 31111 584 2835659022 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 31111 584 2835659022 := r31111

private theorem rows : blockSum term 0 31695 2835659022 :=
  join_sums term (lo:=0) (a:=31111) (b:=584) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 31694).filter (31110 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=2835659022 :=
  right_from_blocks (l:=950000000) (b:=975000000) (small:=745089)
    RangePrimeQ950000000To975000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ950000000To975000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From31110To31694

/-
# Semiprime terms at 30,110,134,441,897 for primes above 31,694 through 32,551

The sum covers 84 primes. Their quotient counts are checked by the
certified prime-counting table through 950,000,000.
-/
open Finset
namespace Correction30110134441897From31694To32551

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


private abbrev term := contribution 30110134441897 31694 RangePrimeQ925000000To950000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 31695 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 31694 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r31695 : blockSum term 31695 428 1875959675 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r32123 : blockSum term 32123 429 2137833554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 31695 857 4013793229 := (join_sums term (lo:=31695) (a:=428) (b:=429) r31695 r32123)

private theorem rows : blockSum term 0 32552 4013793229 :=
  join_sums term (lo:=0) (a:=31695) (b:=857) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 32551).filter (31694 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4013793229 :=
  right_from_blocks (l:=925000000) (b:=950000000) (small:=745089)
    RangePrimeQ925000000To950000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ925000000To950000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From31694To32551

/-
# Semiprime terms at 30,110,134,441,897 for primes above 32,551 through 33,455

The sum covers 88 primes. Their quotient counts are checked by the
certified prime-counting table through 925,000,000.
-/
open Finset
namespace Correction30110134441897From32551To33455

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


private abbrev term := contribution 30110134441897 32551 RangePrimeQ900000000To925000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 32552 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 32551 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r32552 : blockSum term 32552 452 2157773448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r33004 : blockSum term 33004 452 1945209560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 32552 904 4102983008 := (join_sums term (lo:=32552) (a:=452) (b:=452) r32552 r33004)

private theorem rows : blockSum term 0 33456 4102983008 :=
  join_sums term (lo:=0) (a:=32552) (b:=904) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 33455).filter (32551 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4102983008 :=
  right_from_blocks (l:=900000000) (b:=925000000) (small:=745089)
    RangePrimeQ900000000To925000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ900000000To925000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From32551To33455

/-
# Semiprime terms at 30,110,134,441,897 for primes above 33,455 through 34,411

The sum covers 96 primes. Their quotient counts are checked by the
certified prime-counting table through 900,000,000.
-/
open Finset
namespace Correction30110134441897From33455To34411

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


private abbrev term := contribution 30110134441897 33455 RangePrimeQ875000000To900000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 33456 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 33455 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r33456 : blockSum term 33456 478 2422803679 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r33934 : blockSum term 33934 478 1937824178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 33456 956 4360627857 := (join_sums term (lo:=33456) (a:=478) (b:=478) r33456 r33934)

private theorem rows : blockSum term 0 34412 4360627857 :=
  join_sums term (lo:=0) (a:=33456) (b:=956) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 34411).filter (33455 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4360627857 :=
  right_from_blocks (l:=875000000) (b:=900000000) (small:=745089)
    RangePrimeQ875000000To900000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ875000000To900000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From33455To34411

/-
# Semiprime terms at 30,110,134,441,897 for primes above 34,411 through 35,423

The sum covers 97 primes. Their quotient counts are checked by the
certified prime-counting table through 875,000,000.
-/
open Finset
namespace Correction30110134441897From34411To35423

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


private abbrev term := contribution 30110134441897 34411 RangePrimeQ850000000To875000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 34412 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 34411 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r34412 : blockSum term 34412 506 2224586149 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r34918 : blockSum term 34918 506 2061474525 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 34412 1012 4286060674 := (join_sums term (lo:=34412) (a:=506) (b:=506) r34412 r34918)

private theorem rows : blockSum term 0 35424 4286060674 :=
  join_sums term (lo:=0) (a:=34412) (b:=1012) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 35423).filter (34411 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4286060674 :=
  right_from_blocks (l:=850000000) (b:=875000000) (small:=745089)
    RangePrimeQ850000000To875000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ850000000To875000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From34411To35423

/-
# Semiprime terms at 30,110,134,441,897 for primes above 35,423 through 36,497

The sum covers 97 primes. Their quotient counts are checked by the
certified prime-counting table through 850,000,000.
-/
open Finset
namespace Correction30110134441897From35423To36497

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


private abbrev term := contribution 30110134441897 35423 RangePrimeQ825000000To850000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 35424 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 35423 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r35424 : blockSum term 35424 537 1947030057 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r35961 : blockSum term 35961 537 2218837201 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 35424 1074 4165867258 := (join_sums term (lo:=35424) (a:=537) (b:=537) r35424 r35961)

private theorem rows : blockSum term 0 36498 4165867258 :=
  join_sums term (lo:=0) (a:=35424) (b:=1074) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 36497).filter (35423 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4165867258 :=
  right_from_blocks (l:=825000000) (b:=850000000) (small:=745089)
    RangePrimeQ825000000To850000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ825000000To850000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From35423To36497

/-
# Semiprime terms at 30,110,134,441,897 for primes above 36,497 through 37,637

The sum covers 116 primes. Their quotient counts are checked by the
certified prime-counting table through 825,000,000.
-/
open Finset
namespace Correction30110134441897From36497To37637

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


private abbrev term := contribution 30110134441897 36497 RangePrimeQ800000000To825000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 36498 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 36497 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r36498 : blockSum term 36498 570 2564625186 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r37068 : blockSum term 37068 570 2277519554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 36498 1140 4842144740 := (join_sums term (lo:=36498) (a:=570) (b:=570) r36498 r37068)

private theorem rows : blockSum term 0 37638 4842144740 :=
  join_sums term (lo:=0) (a:=36498) (b:=1140) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 37637).filter (36497 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4842144740 :=
  right_from_blocks (l:=800000000) (b:=825000000) (small:=745089)
    RangePrimeQ800000000To825000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ800000000To825000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From36497To37637

/-
# Semiprime terms at 30,110,134,441,897 for primes above 37,637 through 38,851

The sum covers 107 primes. Their quotient counts are checked by the
certified prime-counting table through 800,000,000.
-/
open Finset
namespace Correction30110134441897From37637To38851

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


private abbrev term := contribution 30110134441897 37637 RangePrimeQ775000000To800000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 37638 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 37637 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r37638 : blockSum term 37638 607 2081694128 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r38245 : blockSum term 38245 607 2251518935 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 37638 1214 4333213063 := (join_sums term (lo:=37638) (a:=607) (b:=607) r37638 r38245)

private theorem rows : blockSum term 0 38852 4333213063 :=
  join_sums term (lo:=0) (a:=37638) (b:=1214) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 38851).filter (37637 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4333213063 :=
  right_from_blocks (l:=775000000) (b:=800000000) (small:=745089)
    RangePrimeQ775000000To800000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ775000000To800000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From37637To38851

/-
# Semiprime terms at 30,110,134,441,897 for primes above 38,851 through 40,146

The sum covers 123 primes. Their quotient counts are checked by the
certified prime-counting table through 775,000,000.
-/
open Finset
namespace Correction30110134441897From38851To40146

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


private abbrev term := contribution 30110134441897 38851 RangePrimeQ750000000To775000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 38852 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 38851 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r38852 : blockSum term 38852 647 2416731486 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r39499 : blockSum term 39499 648 2418290993 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 38852 1295 4835022479 := (join_sums term (lo:=38852) (a:=647) (b:=648) r38852 r39499)

private theorem rows : blockSum term 0 40147 4835022479 :=
  join_sums term (lo:=0) (a:=38852) (b:=1295) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 40146).filter (38851 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4835022479 :=
  right_from_blocks (l:=750000000) (b:=775000000) (small:=745089)
    RangePrimeQ750000000To775000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ750000000To775000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From38851To40146

/-
# Semiprime terms at 30,110,134,441,897 for primes above 40,146 through 41,531

The sum covers 127 primes. Their quotient counts are checked by the
certified prime-counting table through 750,000,000.
-/
open Finset
namespace Correction30110134441897From40146To41531

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


private abbrev term := contribution 30110134441897 40146 RangePrimeQ725000000To750000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 40147 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 40146 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r40147 : blockSum term 40147 692 2264761170 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r40839 : blockSum term 40839 693 2569268547 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 40147 1385 4834029717 := (join_sums term (lo:=40147) (a:=692) (b:=693) r40147 r40839)

private theorem rows : blockSum term 0 41532 4834029717 :=
  join_sums term (lo:=0) (a:=40147) (b:=1385) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 41531).filter (40146 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4834029717 :=
  right_from_blocks (l:=725000000) (b:=750000000) (small:=745089)
    RangePrimeQ725000000To750000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ725000000To750000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From40146To41531

/-
# Semiprime terms at 30,110,134,441,897 for primes above 41,531 through 43,014

The sum covers 153 primes. Their quotient counts are checked by the
certified prime-counting table through 725,000,000.
-/
open Finset
namespace Correction30110134441897From41531To43014

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


private abbrev term := contribution 30110134441897 41531 RangePrimeQ700000000To725000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 41532 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 41531 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r41532 : blockSum term 41532 741 2787397342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r42273 : blockSum term 42273 742 2851454100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 41532 1483 5638851442 := (join_sums term (lo:=41532) (a:=741) (b:=742) r41532 r42273)

private theorem rows : blockSum term 0 43015 5638851442 :=
  join_sums term (lo:=0) (a:=41532) (b:=1483) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 43014).filter (41531 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=5638851442 :=
  right_from_blocks (l:=700000000) (b:=725000000) (small:=745089)
    RangePrimeQ700000000To725000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ700000000To725000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From41531To43014

/-
# Semiprime terms at 30,110,134,441,897 for primes above 43,014 through 44,607

The sum covers 139 primes. Their quotient counts are checked by the
certified prime-counting table through 700,000,000.
-/
open Finset
namespace Correction30110134441897From43014To44607

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


private abbrev term := contribution 30110134441897 43014 RangePrimeQ675000000To700000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 43015 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 43014 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r43015 : blockSum term 43015 398 1118765014 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r43413 : blockSum term 43413 398 1323226582 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r43811 : blockSum term 43811 398 1346939093 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r44209 : blockSum term 44209 399 1160457125 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 43015 1593 4949387814 := (join_sums term (lo:=43015) (a:=796) (b:=797) (join_sums term (lo:=43015) (a:=398) (b:=398) r43015 r43413) (join_sums term (lo:=43811) (a:=398) (b:=399) r43811 r44209))

private theorem rows : blockSum term 0 44608 4949387814 :=
  join_sums term (lo:=0) (a:=43015) (b:=1593) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 44607).filter (43014 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4949387814 :=
  right_from_blocks (l:=675000000) (b:=700000000) (small:=745089)
    RangePrimeQ675000000To700000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ675000000To700000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From43014To44607

/-
# Semiprime terms at 30,110,134,441,897 for primes above 44,607 through 46,323

The sum covers 155 primes. Their quotient counts are checked by the
certified prime-counting table through 675,000,000.
-/
open Finset
namespace Correction30110134441897From44607To46323

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


private abbrev term := contribution 30110134441897 44607 RangePrimeQ650000000To675000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 44608 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 44607 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r44608 : blockSum term 44608 429 1464615436 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r45037 : blockSum term 45037 429 1278216780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r45466 : blockSum term 45466 429 1369343423 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r45895 : blockSum term 45895 429 1221292937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 44608 1716 5333468576 := (join_sums term (lo:=44608) (a:=858) (b:=858) (join_sums term (lo:=44608) (a:=429) (b:=429) r44608 r45037) (join_sums term (lo:=45466) (a:=429) (b:=429) r45466 r45895))

private theorem rows : blockSum term 0 46324 5333468576 :=
  join_sums term (lo:=0) (a:=44608) (b:=1716) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 46323).filter (44607 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=5333468576 :=
  right_from_blocks (l:=650000000) (b:=675000000) (small:=745089)
    RangePrimeQ650000000To675000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ650000000To675000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From44607To46323

/-
# Semiprime terms at 30,110,134,441,897 for primes above 46,323 through 48,176

The sum covers 169 primes. Their quotient counts are checked by the
certified prime-counting table through 650,000,000.
-/
open Finset
namespace Correction30110134441897From46323To48176

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


private abbrev term := contribution 30110134441897 46323 RangePrimeQ625000000To650000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 46324 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 46323 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r46324 : blockSum term 46324 463 1479411882 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r46787 : blockSum term 46787 463 1232824827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r47250 : blockSum term 47250 463 1551388614 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r47713 : blockSum term 47713 464 1341320403 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 46324 1853 5604945726 := (join_sums term (lo:=46324) (a:=926) (b:=927) (join_sums term (lo:=46324) (a:=463) (b:=463) r46324 r46787) (join_sums term (lo:=47250) (a:=463) (b:=464) r47250 r47713))

private theorem rows : blockSum term 0 48177 5604945726 :=
  join_sums term (lo:=0) (a:=46324) (b:=1853) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 48176).filter (46323 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=5604945726 :=
  right_from_blocks (l:=625000000) (b:=650000000) (small:=745089)
    RangePrimeQ625000000To650000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ625000000To650000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From46323To48176

/-
# Semiprime terms at 30,110,134,441,897 for primes above 48,176 through 50,183

The sum covers 194 primes. Their quotient counts are checked by the
certified prime-counting table through 625,000,000.
-/
open Finset
namespace Correction30110134441897From48176To50183

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


private abbrev term := contribution 30110134441897 48176 RangePrimeQ600000000To625000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 48177 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 48176 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r48177 : blockSum term 48177 501 1554673260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r48678 : blockSum term 48678 502 1539501065 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r49180 : blockSum term 49180 502 1524926805 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r49682 : blockSum term 49682 502 1573052453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 48177 2007 6192153583 := (join_sums term (lo:=48177) (a:=1003) (b:=1004) (join_sums term (lo:=48177) (a:=501) (b:=502) r48177 r48678) (join_sums term (lo:=49180) (a:=502) (b:=502) r49180 r49682))

private theorem rows : blockSum term 0 50184 6192153583 :=
  join_sums term (lo:=0) (a:=48177) (b:=2007) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 50183).filter (48176 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=6192153583 :=
  right_from_blocks (l:=600000000) (b:=625000000) (small:=745089)
    RangePrimeQ600000000To625000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ600000000To625000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From48176To50183

/-
# Semiprime terms at 30,110,134,441,897 for primes above 50,183 through 52,365

The sum covers 198 primes. Their quotient counts are checked by the
certified prime-counting table through 600,000,000.
-/
open Finset
namespace Correction30110134441897From50183To52365

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


private abbrev term := contribution 30110134441897 50183 RangePrimeQ575000000To600000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 50184 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 50183 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r50184 : blockSum term 50184 545 1402334371 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r50729 : blockSum term 50729 546 1480260297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r51275 : blockSum term 51275 545 1679533177 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r51820 : blockSum term 51820 546 1511793183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 50184 2182 6073921028 := (join_sums term (lo:=50184) (a:=1091) (b:=1091) (join_sums term (lo:=50184) (a:=545) (b:=546) r50184 r50729) (join_sums term (lo:=51275) (a:=545) (b:=546) r51275 r51820))

private theorem rows : blockSum term 0 52366 6073921028 :=
  join_sums term (lo:=0) (a:=50184) (b:=2182) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 52365).filter (50183 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=6073921028 :=
  right_from_blocks (l:=575000000) (b:=600000000) (small:=745089)
    RangePrimeQ575000000To600000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ575000000To600000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From50183To52365

/-
# Semiprime terms at 30,110,134,441,897 for primes above 52,365 through 54,745

The sum covers 218 primes. Their quotient counts are checked by the
certified prime-counting table through 575,000,000.
-/
open Finset
namespace Correction30110134441897From52365To54745

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


private abbrev term := contribution 30110134441897 52365 RangePrimeQ550000000To575000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 52366 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 52365 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r52366 : blockSum term 52366 595 1555552302 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r52961 : blockSum term 52961 595 1599130531 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r53556 : blockSum term 53556 595 1611562168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r54151 : blockSum term 54151 595 1652190822 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 52366 2380 6418435823 := (join_sums term (lo:=52366) (a:=1190) (b:=1190) (join_sums term (lo:=52366) (a:=595) (b:=595) r52366 r52961) (join_sums term (lo:=53556) (a:=595) (b:=595) r53556 r54151))

private theorem rows : blockSum term 0 54746 6418435823 :=
  join_sums term (lo:=0) (a:=52366) (b:=2380) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 54745).filter (52365 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=6418435823 :=
  right_from_blocks (l:=550000000) (b:=575000000) (small:=745089)
    RangePrimeQ550000000To575000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ550000000To575000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From52365To54745

/-
# Semiprime correction from 31,110 through 54,745 at 30,110,134,441,897

The imported intervals meet at consecutive cutoffs and add without overlap.
-/
open Finset
namespace Combined30110134441897From31110To54745

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

private theorem until32551 : (∑ p ∈ (Nat.primesLE 32551).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=6849452251 :=
  join_value (y:=31110) (m:=31694) (z:=32551) (a:=2835659022) (b:=4013793229) (c:=6849452251)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Correction30110134441897From31110To31694.interval_sum Correction30110134441897From31694To32551.interval_sum rfl

private theorem until33455 : (∑ p ∈ (Nat.primesLE 33455).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=10952435259 :=
  join_value (y:=31110) (m:=32551) (z:=33455) (a:=6849452251) (b:=4102983008) (c:=10952435259)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until32551 Correction30110134441897From32551To33455.interval_sum rfl

private theorem until34411 : (∑ p ∈ (Nat.primesLE 34411).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=15313063116 :=
  join_value (y:=31110) (m:=33455) (z:=34411) (a:=10952435259) (b:=4360627857) (c:=15313063116)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until33455 Correction30110134441897From33455To34411.interval_sum rfl

private theorem until35423 : (∑ p ∈ (Nat.primesLE 35423).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=19599123790 :=
  join_value (y:=31110) (m:=34411) (z:=35423) (a:=15313063116) (b:=4286060674) (c:=19599123790)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until34411 Correction30110134441897From34411To35423.interval_sum rfl

private theorem until36497 : (∑ p ∈ (Nat.primesLE 36497).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=23764991048 :=
  join_value (y:=31110) (m:=35423) (z:=36497) (a:=19599123790) (b:=4165867258) (c:=23764991048)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until35423 Correction30110134441897From35423To36497.interval_sum rfl

private theorem until37637 : (∑ p ∈ (Nat.primesLE 37637).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=28607135788 :=
  join_value (y:=31110) (m:=36497) (z:=37637) (a:=23764991048) (b:=4842144740) (c:=28607135788)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until36497 Correction30110134441897From36497To37637.interval_sum rfl

private theorem until38851 : (∑ p ∈ (Nat.primesLE 38851).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=32940348851 :=
  join_value (y:=31110) (m:=37637) (z:=38851) (a:=28607135788) (b:=4333213063) (c:=32940348851)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until37637 Correction30110134441897From37637To38851.interval_sum rfl

private theorem until40146 : (∑ p ∈ (Nat.primesLE 40146).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=37775371330 :=
  join_value (y:=31110) (m:=38851) (z:=40146) (a:=32940348851) (b:=4835022479) (c:=37775371330)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until38851 Correction30110134441897From38851To40146.interval_sum rfl

private theorem until41531 : (∑ p ∈ (Nat.primesLE 41531).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=42609401047 :=
  join_value (y:=31110) (m:=40146) (z:=41531) (a:=37775371330) (b:=4834029717) (c:=42609401047)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until40146 Correction30110134441897From40146To41531.interval_sum rfl

private theorem until43014 : (∑ p ∈ (Nat.primesLE 43014).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=48248252489 :=
  join_value (y:=31110) (m:=41531) (z:=43014) (a:=42609401047) (b:=5638851442) (c:=48248252489)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until41531 Correction30110134441897From41531To43014.interval_sum rfl

private theorem until44607 : (∑ p ∈ (Nat.primesLE 44607).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=53197640303 :=
  join_value (y:=31110) (m:=43014) (z:=44607) (a:=48248252489) (b:=4949387814) (c:=53197640303)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until43014 Correction30110134441897From43014To44607.interval_sum rfl

private theorem until46323 : (∑ p ∈ (Nat.primesLE 46323).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=58531108879 :=
  join_value (y:=31110) (m:=44607) (z:=46323) (a:=53197640303) (b:=5333468576) (c:=58531108879)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until44607 Correction30110134441897From44607To46323.interval_sum rfl

private theorem until48176 : (∑ p ∈ (Nat.primesLE 48176).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=64136054605 :=
  join_value (y:=31110) (m:=46323) (z:=48176) (a:=58531108879) (b:=5604945726) (c:=64136054605)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until46323 Correction30110134441897From46323To48176.interval_sum rfl

private theorem until50183 : (∑ p ∈ (Nat.primesLE 50183).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=70328208188 :=
  join_value (y:=31110) (m:=48176) (z:=50183) (a:=64136054605) (b:=6192153583) (c:=70328208188)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until48176 Correction30110134441897From48176To50183.interval_sum rfl

private theorem until52365 : (∑ p ∈ (Nat.primesLE 52365).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=76402129216 :=
  join_value (y:=31110) (m:=50183) (z:=52365) (a:=70328208188) (b:=6073921028) (c:=76402129216)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until50183 Correction30110134441897From50183To52365.interval_sum rfl

theorem interval_sum : (∑ p ∈ (Nat.primesLE 54745).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=82820565039 :=
  join_value (y:=31110) (m:=52365) (z:=54745) (a:=76402129216) (b:=6418435823) (c:=82820565039)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) until52365 Correction30110134441897From52365To54745.interval_sum rfl

end Combined30110134441897From31110To54745

open Finset
namespace EighthSemiprimeCorrection

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


theorem total : (∑ p ∈ (Nat.primesLE 5487270).filter (31110 < ·),
    (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=642072173249 :=
  join_value (y:=31110) (m:=54745) (z:=5487270) (a:=82820565039) (b:=559251608210) (c:=642072173249)
    (fun p => Nat.primeCounting (30110134441897/p)-Nat.primeCounting (p-1))
    (by decide) (by decide) Combined30110134441897From31110To54745.interval_sum EighthQuotientsThrough550m.checked_sum rfl

end EighthSemiprimeCorrection
