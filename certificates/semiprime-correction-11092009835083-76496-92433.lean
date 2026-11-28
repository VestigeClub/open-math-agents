import certificates.«prime-table-120000000-145000000»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 76,496 through 92,433

The sum covers 1,405 primes. Their quotient counts are checked by the
certified prime-counting table through 145,000,000.
-/
open Finset
namespace Correction11092009835083From76496To92433

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


private abbrev term := contribution 11092009835083 76496 RangePrimeQ120000000To145000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 76497 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 76496 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r76497 : blockSum term 76497 498 342150650 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r76995 : blockSum term 76995 498 372379865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r77493 : blockSum term 77493 498 386378616 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r77991 : blockSum term 77991 498 319988974 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r78489 : blockSum term 78489 498 349871695 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r78987 : blockSum term 78987 498 339801764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r79485 : blockSum term 79485 498 361375984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r79983 : blockSum term 79983 498 335877314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r80481 : blockSum term 80481 498 364967280 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r80979 : blockSum term 80979 498 355233802 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r81477 : blockSum term 81477 498 360712607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r81975 : blockSum term 81975 498 335830958 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r82473 : blockSum term 82473 498 326396485 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r82971 : blockSum term 82971 498 339499820 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r83469 : blockSum term 83469 498 285140598 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r83967 : blockSum term 83967 498 350629233 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r84465 : blockSum term 84465 498 289418894 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r84963 : blockSum term 84963 498 339444925 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r85461 : blockSum term 85461 498 300903384 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r85959 : blockSum term 85959 498 342945999 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r86457 : blockSum term 86457 498 283106973 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r86955 : blockSum term 86955 498 310439218 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r87453 : blockSum term 87453 498 351914642 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r87951 : blockSum term 87951 498 242890277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r88449 : blockSum term 88449 498 305431824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r88947 : blockSum term 88947 498 325093396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r89445 : blockSum term 89445 498 330409419 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r89943 : blockSum term 89943 498 342695810 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r90441 : blockSum term 90441 498 278247193 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r90939 : blockSum term 90939 498 311390510 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r91437 : blockSum term 91437 498 254778168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r91935 : blockSum term 91935 499 349313966 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 76497 15937 10484660243 := (join_sums term (lo:=76497) (a:=7968) (b:=7969) (join_sums term (lo:=76497) (a:=3984) (b:=3984) (join_sums term (lo:=76497) (a:=1992) (b:=1992) (join_sums term (lo:=76497) (a:=996) (b:=996) (join_sums term (lo:=76497) (a:=498) (b:=498) r76497 r76995) (join_sums term (lo:=77493) (a:=498) (b:=498) r77493 r77991)) (join_sums term (lo:=78489) (a:=996) (b:=996) (join_sums term (lo:=78489) (a:=498) (b:=498) r78489 r78987) (join_sums term (lo:=79485) (a:=498) (b:=498) r79485 r79983))) (join_sums term (lo:=80481) (a:=1992) (b:=1992) (join_sums term (lo:=80481) (a:=996) (b:=996) (join_sums term (lo:=80481) (a:=498) (b:=498) r80481 r80979) (join_sums term (lo:=81477) (a:=498) (b:=498) r81477 r81975)) (join_sums term (lo:=82473) (a:=996) (b:=996) (join_sums term (lo:=82473) (a:=498) (b:=498) r82473 r82971) (join_sums term (lo:=83469) (a:=498) (b:=498) r83469 r83967)))) (join_sums term (lo:=84465) (a:=3984) (b:=3985) (join_sums term (lo:=84465) (a:=1992) (b:=1992) (join_sums term (lo:=84465) (a:=996) (b:=996) (join_sums term (lo:=84465) (a:=498) (b:=498) r84465 r84963) (join_sums term (lo:=85461) (a:=498) (b:=498) r85461 r85959)) (join_sums term (lo:=86457) (a:=996) (b:=996) (join_sums term (lo:=86457) (a:=498) (b:=498) r86457 r86955) (join_sums term (lo:=87453) (a:=498) (b:=498) r87453 r87951))) (join_sums term (lo:=88449) (a:=1992) (b:=1993) (join_sums term (lo:=88449) (a:=996) (b:=996) (join_sums term (lo:=88449) (a:=498) (b:=498) r88449 r88947) (join_sums term (lo:=89445) (a:=498) (b:=498) r89445 r89943)) (join_sums term (lo:=90441) (a:=996) (b:=997) (join_sums term (lo:=90441) (a:=498) (b:=498) r90441 r90939) (join_sums term (lo:=91437) (a:=498) (b:=499) r91437 r91935)))))

private theorem rows : blockSum term 0 92434 10484660243 :=
  join_sums term (lo:=0) (a:=76497) (b:=15937) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 92433).filter (76496 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=10484660243 :=
  right_from_blocks (l:=120000000) (b:=145000000) (small:=745089)
    RangePrimeQ120000000To145000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ120000000To145000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From76496To92433
