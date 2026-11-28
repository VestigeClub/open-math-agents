import certificates.«prime-table-195000000-220000000»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 50,418 through 56,882

The sum covers 592 primes. Their quotient counts are checked by the
certified prime-counting table through 220,000,000.
-/
open Finset
namespace Correction11092009835083From50418To56882

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


private abbrev term := contribution 11092009835083 50418 RangePrimeQ195000000To220000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 50419 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 50418 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r50419 : blockSum term 50419 404 374255708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r50823 : blockSum term 50823 404 431346887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r51227 : blockSum term 51227 404 499469292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r51631 : blockSum term 51631 404 460419792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r52035 : blockSum term 52035 404 398486043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r52439 : blockSum term 52439 404 418788576 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r52843 : blockSum term 52843 404 461956394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r53247 : blockSum term 53247 404 412718386 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r53651 : blockSum term 53651 404 421252574 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r54055 : blockSum term 54055 404 406830930 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r54459 : blockSum term 54459 404 415503072 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r54863 : blockSum term 54863 404 412470798 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r55267 : blockSum term 55267 404 376306913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r55671 : blockSum term 55671 404 428958429 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r56075 : blockSum term 56075 404 415029213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r56479 : blockSum term 56479 404 433997320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 50419 6464 6767790327 := (join_sums term (lo:=50419) (a:=3232) (b:=3232) (join_sums term (lo:=50419) (a:=1616) (b:=1616) (join_sums term (lo:=50419) (a:=808) (b:=808) (join_sums term (lo:=50419) (a:=404) (b:=404) r50419 r50823) (join_sums term (lo:=51227) (a:=404) (b:=404) r51227 r51631)) (join_sums term (lo:=52035) (a:=808) (b:=808) (join_sums term (lo:=52035) (a:=404) (b:=404) r52035 r52439) (join_sums term (lo:=52843) (a:=404) (b:=404) r52843 r53247))) (join_sums term (lo:=53651) (a:=1616) (b:=1616) (join_sums term (lo:=53651) (a:=808) (b:=808) (join_sums term (lo:=53651) (a:=404) (b:=404) r53651 r54055) (join_sums term (lo:=54459) (a:=404) (b:=404) r54459 r54863)) (join_sums term (lo:=55267) (a:=808) (b:=808) (join_sums term (lo:=55267) (a:=404) (b:=404) r55267 r55671) (join_sums term (lo:=56075) (a:=404) (b:=404) r56075 r56479))))

private theorem rows : blockSum term 0 56883 6767790327 :=
  join_sums term (lo:=0) (a:=50419) (b:=6464) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 56882).filter (50418 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=6767790327 :=
  right_from_blocks (l:=195000000) (b:=220000000) (small:=745089)
    RangePrimeQ195000000To220000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ195000000To220000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From50418To56882
