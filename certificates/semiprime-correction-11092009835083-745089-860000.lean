import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 745,089 through 860,000

The sum covers 8,459 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction11092009835083From745089To860000

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


private abbrev term := contribution 11092009835083 745089 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 745090 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 745089 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r745090 : blockSum term 745090 448 24401169 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r745538 : blockSum term 745538 449 27998632 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r745987 : blockSum term 745987 449 33397118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r746436 : blockSum term 746436 449 27962440 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r746885 : blockSum term 746885 448 26143019 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r747333 : blockSum term 747333 449 30630493 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r747782 : blockSum term 747782 449 29710605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r748231 : blockSum term 748231 449 28791229 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r748680 : blockSum term 748680 448 32371519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r749128 : blockSum term 749128 449 32350992 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r749577 : blockSum term 749577 449 26940411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r750026 : blockSum term 750026 449 27822125 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r750475 : blockSum term 750475 449 27803562 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r750924 : blockSum term 750924 449 37643196 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r751373 : blockSum term 751373 449 29558046 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r751822 : blockSum term 751822 449 31330632 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r752271 : blockSum term 752271 448 29521721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r752719 : blockSum term 752719 449 28608786 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r753168 : blockSum term 753168 449 25016137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r753617 : blockSum term 753617 449 32144919 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r754066 : blockSum term 754066 449 37478308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r754515 : blockSum term 754515 449 25860728 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r754964 : blockSum term 754964 449 34757179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r755413 : blockSum term 755413 449 26718888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r755862 : blockSum term 755862 448 26701303 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r756310 : blockSum term 756310 449 27573606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r756759 : blockSum term 756759 449 21334414 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r757208 : blockSum term 757208 449 30205867 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r757657 : blockSum term 757657 449 27523070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r758106 : blockSum term 758106 449 31055268 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r758555 : blockSum term 758555 449 32809371 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r759004 : blockSum term 759004 449 26586183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r759453 : blockSum term 759453 448 33656147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r759901 : blockSum term 759901 449 31862814 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r760350 : blockSum term 760350 449 28305484 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r760799 : blockSum term 760799 449 30938924 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r761248 : blockSum term 761248 449 37103034 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r761697 : blockSum term 761697 449 26485289 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r762146 : blockSum term 762146 449 27349996 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r762595 : blockSum term 762595 449 29095888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r763044 : blockSum term 763044 448 27316055 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r763492 : blockSum term 763492 449 33463550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r763941 : blockSum term 763941 449 29923126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r764390 : blockSum term 764390 449 23747667 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r764839 : blockSum term 764839 449 37796300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r765288 : blockSum term 765288 449 27232624 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r765737 : blockSum term 765737 449 31605169 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r766186 : blockSum term 766186 449 32462559 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r766635 : blockSum term 766635 448 28058006 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r767083 : blockSum term 767083 449 27164134 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r767532 : blockSum term 767532 449 28899499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r767981 : blockSum term 767981 449 33255235 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r768430 : blockSum term 768430 449 27987891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r768879 : blockSum term 768879 449 28844505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r769328 : blockSum term 769328 449 27953412 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r769777 : blockSum term 769777 449 30554769 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r770226 : blockSum term 770226 448 31408020 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r770674 : blockSum term 770674 449 28772347 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r771123 : blockSum term 771123 449 28754187 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r771572 : blockSum term 771572 449 29607510 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r772021 : blockSum term 772021 449 26977958 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r772470 : blockSum term 772470 449 26961424 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r772919 : blockSum term 772919 449 26944336 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r773368 : blockSum term 773368 449 28664973 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r773817 : blockSum term 773817 448 34723295 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r774265 : blockSum term 774265 449 25158066 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r774714 : blockSum term 774714 449 28611249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r775163 : blockSum term 775163 449 23394675 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r775612 : blockSum term 775612 449 27710421 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r776061 : blockSum term 776061 449 27693558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r776510 : blockSum term 776510 449 25081571 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r776959 : blockSum term 776959 449 32844709 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r777408 : blockSum term 777408 448 26778206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r777856 : blockSum term 777856 449 29351389 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r778305 : blockSum term 778305 449 32783532 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r778754 : blockSum term 778754 449 29314901 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r779203 : blockSum term 779203 449 25848598 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r779652 : blockSum term 779652 449 28417659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r780101 : blockSum term 780101 449 24096984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r780550 : blockSum term 780550 449 30961841 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r780999 : blockSum term 780999 448 33521256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r781447 : blockSum term 781447 449 28347728 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r781896 : blockSum term 781896 449 33481887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r782345 : blockSum term 782345 449 24023369 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r782794 : blockSum term 782794 449 24865637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r783243 : blockSum term 783243 449 29135807 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r783692 : blockSum term 783692 449 28263106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r784141 : blockSum term 784141 449 35091051 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r784590 : blockSum term 784590 448 23094422 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r785038 : blockSum term 785038 449 32483349 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r785487 : blockSum term 785487 449 28192555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r785936 : blockSum term 785936 449 26467368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r786385 : blockSum term 786385 449 24743773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r786834 : blockSum term 786834 449 27287789 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r787283 : blockSum term 787283 449 27271332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r787732 : blockSum term 787732 449 32364204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r788181 : blockSum term 788181 448 31492390 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r788629 : blockSum term 788629 449 28069856 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r789078 : blockSum term 789078 449 23803769 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r789527 : blockSum term 789527 449 27188530 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r789976 : blockSum term 789976 449 29718584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r790425 : blockSum term 790425 449 29700241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r790874 : blockSum term 790874 449 30529646 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r791323 : blockSum term 791323 449 20341758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r791772 : blockSum term 791772 448 31341005 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r792220 : blockSum term 792220 449 34707352 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r792669 : blockSum term 792669 449 24535016 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r793118 : blockSum term 793118 449 27055656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r793567 : blockSum term 793567 449 31264571 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r794016 : blockSum term 794016 449 29558595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r794465 : blockSum term 794465 449 25321230 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r794914 : blockSum term 794914 449 30365405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r795363 : blockSum term 795363 448 29502681 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r795811 : blockSum term 795811 449 26116548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r796260 : blockSum term 796260 449 28627148 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r796709 : blockSum term 796709 449 33658700 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r797158 : blockSum term 797158 449 26908677 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r797607 : blockSum term 797607 449 23532439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r798056 : blockSum term 798056 449 31917435 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r798505 : blockSum term 798505 449 25181856 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r798954 : blockSum term 798954 448 21810402 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r799402 : blockSum term 799402 449 29343142 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r799851 : blockSum term 799851 449 30162747 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r800300 : blockSum term 800300 449 36005015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r800749 : blockSum term 800749 449 26778505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r801198 : blockSum term 801198 449 25924992 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r801647 : blockSum term 801647 449 21731321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r802096 : blockSum term 802096 449 25895998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r802545 : blockSum term 802545 448 27549392 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r802993 : blockSum term 802993 449 23360742 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r803442 : blockSum term 803442 449 25849675 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r803891 : blockSum term 803891 449 30833753 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r804340 : blockSum term 804340 449 27482572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r804789 : blockSum term 804789 449 32459200 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r805238 : blockSum term 805238 449 29113972 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r805687 : blockSum term 805687 449 29926588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r806136 : blockSum term 806136 448 26586037 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r806584 : blockSum term 806584 449 20756572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r807033 : blockSum term 807033 449 27383324 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r807482 : blockSum term 807482 449 24050785 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r807931 : blockSum term 807931 449 26522011 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r808380 : blockSum term 808380 449 27334691 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r808829 : blockSum term 808829 449 26489448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r809278 : blockSum term 809278 449 25647919 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r809727 : blockSum term 809727 448 30594489 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r810175 : blockSum term 810175 449 33879914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r810624 : blockSum term 810624 449 23123658 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r811073 : blockSum term 811073 449 27237008 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r811522 : blockSum term 811522 449 27219836 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r811971 : blockSum term 811971 449 30500052 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r812420 : blockSum term 812420 449 24715777 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r812869 : blockSum term 812869 449 27992909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r813318 : blockSum term 813318 448 22217766 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r813766 : blockSum term 813766 449 31249405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r814215 : blockSum term 814215 449 25478153 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r814664 : blockSum term 814664 449 24642630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r815113 : blockSum term 815113 449 27909936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r815562 : blockSum term 815562 449 24612363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r816011 : blockSum term 816011 449 27877938 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r816460 : blockSum term 816460 449 27039859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r816909 : blockSum term 816909 448 30300710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r817357 : blockSum term 817357 449 24552272 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r817806 : blockSum term 817806 449 26175090 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r818255 : blockSum term 818255 449 24525056 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r818704 : blockSum term 818704 449 22058400 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r819153 : blockSum term 819153 449 32660738 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r819602 : blockSum term 819602 449 26930158 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r820051 : blockSum term 820051 449 30990875 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r820500 : blockSum term 820500 448 26081764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r820948 : blockSum term 820948 449 26882157 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r821397 : blockSum term 821397 449 25237342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r821846 : blockSum term 821846 449 29290505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r822295 : blockSum term 822295 449 32525431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r822744 : blockSum term 822744 449 26005715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r823193 : blockSum term 823193 449 27614087 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r823642 : blockSum term 823642 449 31656896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r824091 : blockSum term 824091 448 23525058 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r824539 : blockSum term 824539 449 28375767 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r824988 : blockSum term 824988 449 30790903 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r825437 : blockSum term 825437 449 27533671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r825886 : blockSum term 825886 449 25898530 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r826335 : blockSum term 826335 449 30735939 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r826784 : blockSum term 826784 449 25059906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r827233 : blockSum term 827233 449 22621409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r827682 : blockSum term 827682 448 31489953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r828130 : blockSum term 828130 449 18560013 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r828579 : blockSum term 828579 449 29033826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r829028 : blockSum term 829028 449 22569159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r829477 : blockSum term 829477 449 26582917 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r829926 : blockSum term 829926 449 26566198 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r830375 : blockSum term 830375 449 26552082 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r830824 : blockSum term 830824 449 26536565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r831273 : blockSum term 831273 448 31340910 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r831721 : blockSum term 831721 449 28110663 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r832170 : blockSum term 832170 449 25685707 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r832619 : blockSum term 832619 449 33694573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r833068 : blockSum term 833068 449 24051758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r833517 : blockSum term 833517 449 24838950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r833966 : blockSum term 833966 449 20820931 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r834415 : blockSum term 834415 449 27211435 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r834864 : blockSum term 834864 448 20797448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r835312 : blockSum term 835312 449 27979516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r835761 : blockSum term 835761 449 28761173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r836210 : blockSum term 836210 449 23155841 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r836659 : blockSum term 836659 449 28729096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r837108 : blockSum term 837108 449 22330977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r837557 : blockSum term 837557 449 22318745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r838006 : blockSum term 838006 449 26288946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r838455 : blockSum term 838455 448 27070352 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r838903 : blockSum term 838903 449 23872248 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r839352 : blockSum term 839352 449 27038597 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r839801 : blockSum term 839801 449 27022573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r840250 : blockSum term 840250 449 21446894 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r840699 : blockSum term 840699 449 30166472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r841148 : blockSum term 841148 449 25389100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r841597 : blockSum term 841597 449 22201322 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r842046 : blockSum term 842046 448 34866922 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r842494 : blockSum term 842494 449 22967723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r842943 : blockSum term 842943 449 27703315 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r843392 : blockSum term 843392 449 26105199 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r843841 : blockSum term 843841 449 25299040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r844290 : blockSum term 844290 449 29235586 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r844739 : blockSum term 844739 449 23690474 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r845188 : blockSum term 845188 449 22099379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r845637 : blockSum term 845637 448 25240886 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r846085 : blockSum term 846085 449 25225776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r846534 : blockSum term 846534 449 24422537 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r846983 : blockSum term 846983 449 29134993 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r847432 : blockSum term 847432 449 24396477 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r847881 : blockSum term 847881 449 23596178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r848330 : blockSum term 848330 449 26726183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r848779 : blockSum term 848779 449 31425107 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r849228 : blockSum term 849228 448 19629710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r849676 : blockSum term 849676 449 28250721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r850125 : blockSum term 850125 449 29018865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r850574 : blockSum term 850574 449 18811467 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r851023 : blockSum term 851023 449 30552023 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r851472 : blockSum term 851472 449 25837246 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r851921 : blockSum term 851921 449 24256547 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r852370 : blockSum term 852370 449 23460713 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r852819 : blockSum term 852819 448 25011906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r853267 : blockSum term 853267 449 21090273 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r853716 : blockSum term 853716 449 30445815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r854165 : blockSum term 854165 449 23406329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r854614 : blockSum term 854614 449 21833936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r855063 : blockSum term 855063 449 26497780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r855512 : blockSum term 855512 449 25703510 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r855961 : blockSum term 855961 449 26467605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r856410 : blockSum term 856410 448 28786239 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r856858 : blockSum term 856858 449 25659836 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r857307 : blockSum term 857307 449 27975835 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r857756 : blockSum term 857756 449 22523524 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r858205 : blockSum term 858205 449 23288326 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r858654 : blockSum term 858654 449 27928557 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r859103 : blockSum term 859103 449 20159555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r859552 : blockSum term 859552 449 27898096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 745090 114911 7077912147 := (join_sums term (lo:=745090) (a:=57455) (b:=57456) (join_sums term (lo:=745090) (a:=28727) (b:=28728) (join_sums term (lo:=745090) (a:=14363) (b:=14364) (join_sums term (lo:=745090) (a:=7181) (b:=7182) (join_sums term (lo:=745090) (a:=3590) (b:=3591) (join_sums term (lo:=745090) (a:=1795) (b:=1795) (join_sums term (lo:=745090) (a:=897) (b:=898) (join_sums term (lo:=745090) (a:=448) (b:=449) r745090 r745538) (join_sums term (lo:=745987) (a:=449) (b:=449) r745987 r746436)) (join_sums term (lo:=746885) (a:=897) (b:=898) (join_sums term (lo:=746885) (a:=448) (b:=449) r746885 r747333) (join_sums term (lo:=747782) (a:=449) (b:=449) r747782 r748231))) (join_sums term (lo:=748680) (a:=1795) (b:=1796) (join_sums term (lo:=748680) (a:=897) (b:=898) (join_sums term (lo:=748680) (a:=448) (b:=449) r748680 r749128) (join_sums term (lo:=749577) (a:=449) (b:=449) r749577 r750026)) (join_sums term (lo:=750475) (a:=898) (b:=898) (join_sums term (lo:=750475) (a:=449) (b:=449) r750475 r750924) (join_sums term (lo:=751373) (a:=449) (b:=449) r751373 r751822)))) (join_sums term (lo:=752271) (a:=3591) (b:=3591) (join_sums term (lo:=752271) (a:=1795) (b:=1796) (join_sums term (lo:=752271) (a:=897) (b:=898) (join_sums term (lo:=752271) (a:=448) (b:=449) r752271 r752719) (join_sums term (lo:=753168) (a:=449) (b:=449) r753168 r753617)) (join_sums term (lo:=754066) (a:=898) (b:=898) (join_sums term (lo:=754066) (a:=449) (b:=449) r754066 r754515) (join_sums term (lo:=754964) (a:=449) (b:=449) r754964 r755413))) (join_sums term (lo:=755862) (a:=1795) (b:=1796) (join_sums term (lo:=755862) (a:=897) (b:=898) (join_sums term (lo:=755862) (a:=448) (b:=449) r755862 r756310) (join_sums term (lo:=756759) (a:=449) (b:=449) r756759 r757208)) (join_sums term (lo:=757657) (a:=898) (b:=898) (join_sums term (lo:=757657) (a:=449) (b:=449) r757657 r758106) (join_sums term (lo:=758555) (a:=449) (b:=449) r758555 r759004))))) (join_sums term (lo:=759453) (a:=7182) (b:=7182) (join_sums term (lo:=759453) (a:=3591) (b:=3591) (join_sums term (lo:=759453) (a:=1795) (b:=1796) (join_sums term (lo:=759453) (a:=897) (b:=898) (join_sums term (lo:=759453) (a:=448) (b:=449) r759453 r759901) (join_sums term (lo:=760350) (a:=449) (b:=449) r760350 r760799)) (join_sums term (lo:=761248) (a:=898) (b:=898) (join_sums term (lo:=761248) (a:=449) (b:=449) r761248 r761697) (join_sums term (lo:=762146) (a:=449) (b:=449) r762146 r762595))) (join_sums term (lo:=763044) (a:=1795) (b:=1796) (join_sums term (lo:=763044) (a:=897) (b:=898) (join_sums term (lo:=763044) (a:=448) (b:=449) r763044 r763492) (join_sums term (lo:=763941) (a:=449) (b:=449) r763941 r764390)) (join_sums term (lo:=764839) (a:=898) (b:=898) (join_sums term (lo:=764839) (a:=449) (b:=449) r764839 r765288) (join_sums term (lo:=765737) (a:=449) (b:=449) r765737 r766186)))) (join_sums term (lo:=766635) (a:=3591) (b:=3591) (join_sums term (lo:=766635) (a:=1795) (b:=1796) (join_sums term (lo:=766635) (a:=897) (b:=898) (join_sums term (lo:=766635) (a:=448) (b:=449) r766635 r767083) (join_sums term (lo:=767532) (a:=449) (b:=449) r767532 r767981)) (join_sums term (lo:=768430) (a:=898) (b:=898) (join_sums term (lo:=768430) (a:=449) (b:=449) r768430 r768879) (join_sums term (lo:=769328) (a:=449) (b:=449) r769328 r769777))) (join_sums term (lo:=770226) (a:=1795) (b:=1796) (join_sums term (lo:=770226) (a:=897) (b:=898) (join_sums term (lo:=770226) (a:=448) (b:=449) r770226 r770674) (join_sums term (lo:=771123) (a:=449) (b:=449) r771123 r771572)) (join_sums term (lo:=772021) (a:=898) (b:=898) (join_sums term (lo:=772021) (a:=449) (b:=449) r772021 r772470) (join_sums term (lo:=772919) (a:=449) (b:=449) r772919 r773368)))))) (join_sums term (lo:=773817) (a:=14364) (b:=14364) (join_sums term (lo:=773817) (a:=7182) (b:=7182) (join_sums term (lo:=773817) (a:=3591) (b:=3591) (join_sums term (lo:=773817) (a:=1795) (b:=1796) (join_sums term (lo:=773817) (a:=897) (b:=898) (join_sums term (lo:=773817) (a:=448) (b:=449) r773817 r774265) (join_sums term (lo:=774714) (a:=449) (b:=449) r774714 r775163)) (join_sums term (lo:=775612) (a:=898) (b:=898) (join_sums term (lo:=775612) (a:=449) (b:=449) r775612 r776061) (join_sums term (lo:=776510) (a:=449) (b:=449) r776510 r776959))) (join_sums term (lo:=777408) (a:=1795) (b:=1796) (join_sums term (lo:=777408) (a:=897) (b:=898) (join_sums term (lo:=777408) (a:=448) (b:=449) r777408 r777856) (join_sums term (lo:=778305) (a:=449) (b:=449) r778305 r778754)) (join_sums term (lo:=779203) (a:=898) (b:=898) (join_sums term (lo:=779203) (a:=449) (b:=449) r779203 r779652) (join_sums term (lo:=780101) (a:=449) (b:=449) r780101 r780550)))) (join_sums term (lo:=780999) (a:=3591) (b:=3591) (join_sums term (lo:=780999) (a:=1795) (b:=1796) (join_sums term (lo:=780999) (a:=897) (b:=898) (join_sums term (lo:=780999) (a:=448) (b:=449) r780999 r781447) (join_sums term (lo:=781896) (a:=449) (b:=449) r781896 r782345)) (join_sums term (lo:=782794) (a:=898) (b:=898) (join_sums term (lo:=782794) (a:=449) (b:=449) r782794 r783243) (join_sums term (lo:=783692) (a:=449) (b:=449) r783692 r784141))) (join_sums term (lo:=784590) (a:=1795) (b:=1796) (join_sums term (lo:=784590) (a:=897) (b:=898) (join_sums term (lo:=784590) (a:=448) (b:=449) r784590 r785038) (join_sums term (lo:=785487) (a:=449) (b:=449) r785487 r785936)) (join_sums term (lo:=786385) (a:=898) (b:=898) (join_sums term (lo:=786385) (a:=449) (b:=449) r786385 r786834) (join_sums term (lo:=787283) (a:=449) (b:=449) r787283 r787732))))) (join_sums term (lo:=788181) (a:=7182) (b:=7182) (join_sums term (lo:=788181) (a:=3591) (b:=3591) (join_sums term (lo:=788181) (a:=1795) (b:=1796) (join_sums term (lo:=788181) (a:=897) (b:=898) (join_sums term (lo:=788181) (a:=448) (b:=449) r788181 r788629) (join_sums term (lo:=789078) (a:=449) (b:=449) r789078 r789527)) (join_sums term (lo:=789976) (a:=898) (b:=898) (join_sums term (lo:=789976) (a:=449) (b:=449) r789976 r790425) (join_sums term (lo:=790874) (a:=449) (b:=449) r790874 r791323))) (join_sums term (lo:=791772) (a:=1795) (b:=1796) (join_sums term (lo:=791772) (a:=897) (b:=898) (join_sums term (lo:=791772) (a:=448) (b:=449) r791772 r792220) (join_sums term (lo:=792669) (a:=449) (b:=449) r792669 r793118)) (join_sums term (lo:=793567) (a:=898) (b:=898) (join_sums term (lo:=793567) (a:=449) (b:=449) r793567 r794016) (join_sums term (lo:=794465) (a:=449) (b:=449) r794465 r794914)))) (join_sums term (lo:=795363) (a:=3591) (b:=3591) (join_sums term (lo:=795363) (a:=1795) (b:=1796) (join_sums term (lo:=795363) (a:=897) (b:=898) (join_sums term (lo:=795363) (a:=448) (b:=449) r795363 r795811) (join_sums term (lo:=796260) (a:=449) (b:=449) r796260 r796709)) (join_sums term (lo:=797158) (a:=898) (b:=898) (join_sums term (lo:=797158) (a:=449) (b:=449) r797158 r797607) (join_sums term (lo:=798056) (a:=449) (b:=449) r798056 r798505))) (join_sums term (lo:=798954) (a:=1795) (b:=1796) (join_sums term (lo:=798954) (a:=897) (b:=898) (join_sums term (lo:=798954) (a:=448) (b:=449) r798954 r799402) (join_sums term (lo:=799851) (a:=449) (b:=449) r799851 r800300)) (join_sums term (lo:=800749) (a:=898) (b:=898) (join_sums term (lo:=800749) (a:=449) (b:=449) r800749 r801198) (join_sums term (lo:=801647) (a:=449) (b:=449) r801647 r802096))))))) (join_sums term (lo:=802545) (a:=28728) (b:=28728) (join_sums term (lo:=802545) (a:=14364) (b:=14364) (join_sums term (lo:=802545) (a:=7182) (b:=7182) (join_sums term (lo:=802545) (a:=3591) (b:=3591) (join_sums term (lo:=802545) (a:=1795) (b:=1796) (join_sums term (lo:=802545) (a:=897) (b:=898) (join_sums term (lo:=802545) (a:=448) (b:=449) r802545 r802993) (join_sums term (lo:=803442) (a:=449) (b:=449) r803442 r803891)) (join_sums term (lo:=804340) (a:=898) (b:=898) (join_sums term (lo:=804340) (a:=449) (b:=449) r804340 r804789) (join_sums term (lo:=805238) (a:=449) (b:=449) r805238 r805687))) (join_sums term (lo:=806136) (a:=1795) (b:=1796) (join_sums term (lo:=806136) (a:=897) (b:=898) (join_sums term (lo:=806136) (a:=448) (b:=449) r806136 r806584) (join_sums term (lo:=807033) (a:=449) (b:=449) r807033 r807482)) (join_sums term (lo:=807931) (a:=898) (b:=898) (join_sums term (lo:=807931) (a:=449) (b:=449) r807931 r808380) (join_sums term (lo:=808829) (a:=449) (b:=449) r808829 r809278)))) (join_sums term (lo:=809727) (a:=3591) (b:=3591) (join_sums term (lo:=809727) (a:=1795) (b:=1796) (join_sums term (lo:=809727) (a:=897) (b:=898) (join_sums term (lo:=809727) (a:=448) (b:=449) r809727 r810175) (join_sums term (lo:=810624) (a:=449) (b:=449) r810624 r811073)) (join_sums term (lo:=811522) (a:=898) (b:=898) (join_sums term (lo:=811522) (a:=449) (b:=449) r811522 r811971) (join_sums term (lo:=812420) (a:=449) (b:=449) r812420 r812869))) (join_sums term (lo:=813318) (a:=1795) (b:=1796) (join_sums term (lo:=813318) (a:=897) (b:=898) (join_sums term (lo:=813318) (a:=448) (b:=449) r813318 r813766) (join_sums term (lo:=814215) (a:=449) (b:=449) r814215 r814664)) (join_sums term (lo:=815113) (a:=898) (b:=898) (join_sums term (lo:=815113) (a:=449) (b:=449) r815113 r815562) (join_sums term (lo:=816011) (a:=449) (b:=449) r816011 r816460))))) (join_sums term (lo:=816909) (a:=7182) (b:=7182) (join_sums term (lo:=816909) (a:=3591) (b:=3591) (join_sums term (lo:=816909) (a:=1795) (b:=1796) (join_sums term (lo:=816909) (a:=897) (b:=898) (join_sums term (lo:=816909) (a:=448) (b:=449) r816909 r817357) (join_sums term (lo:=817806) (a:=449) (b:=449) r817806 r818255)) (join_sums term (lo:=818704) (a:=898) (b:=898) (join_sums term (lo:=818704) (a:=449) (b:=449) r818704 r819153) (join_sums term (lo:=819602) (a:=449) (b:=449) r819602 r820051))) (join_sums term (lo:=820500) (a:=1795) (b:=1796) (join_sums term (lo:=820500) (a:=897) (b:=898) (join_sums term (lo:=820500) (a:=448) (b:=449) r820500 r820948) (join_sums term (lo:=821397) (a:=449) (b:=449) r821397 r821846)) (join_sums term (lo:=822295) (a:=898) (b:=898) (join_sums term (lo:=822295) (a:=449) (b:=449) r822295 r822744) (join_sums term (lo:=823193) (a:=449) (b:=449) r823193 r823642)))) (join_sums term (lo:=824091) (a:=3591) (b:=3591) (join_sums term (lo:=824091) (a:=1795) (b:=1796) (join_sums term (lo:=824091) (a:=897) (b:=898) (join_sums term (lo:=824091) (a:=448) (b:=449) r824091 r824539) (join_sums term (lo:=824988) (a:=449) (b:=449) r824988 r825437)) (join_sums term (lo:=825886) (a:=898) (b:=898) (join_sums term (lo:=825886) (a:=449) (b:=449) r825886 r826335) (join_sums term (lo:=826784) (a:=449) (b:=449) r826784 r827233))) (join_sums term (lo:=827682) (a:=1795) (b:=1796) (join_sums term (lo:=827682) (a:=897) (b:=898) (join_sums term (lo:=827682) (a:=448) (b:=449) r827682 r828130) (join_sums term (lo:=828579) (a:=449) (b:=449) r828579 r829028)) (join_sums term (lo:=829477) (a:=898) (b:=898) (join_sums term (lo:=829477) (a:=449) (b:=449) r829477 r829926) (join_sums term (lo:=830375) (a:=449) (b:=449) r830375 r830824)))))) (join_sums term (lo:=831273) (a:=14364) (b:=14364) (join_sums term (lo:=831273) (a:=7182) (b:=7182) (join_sums term (lo:=831273) (a:=3591) (b:=3591) (join_sums term (lo:=831273) (a:=1795) (b:=1796) (join_sums term (lo:=831273) (a:=897) (b:=898) (join_sums term (lo:=831273) (a:=448) (b:=449) r831273 r831721) (join_sums term (lo:=832170) (a:=449) (b:=449) r832170 r832619)) (join_sums term (lo:=833068) (a:=898) (b:=898) (join_sums term (lo:=833068) (a:=449) (b:=449) r833068 r833517) (join_sums term (lo:=833966) (a:=449) (b:=449) r833966 r834415))) (join_sums term (lo:=834864) (a:=1795) (b:=1796) (join_sums term (lo:=834864) (a:=897) (b:=898) (join_sums term (lo:=834864) (a:=448) (b:=449) r834864 r835312) (join_sums term (lo:=835761) (a:=449) (b:=449) r835761 r836210)) (join_sums term (lo:=836659) (a:=898) (b:=898) (join_sums term (lo:=836659) (a:=449) (b:=449) r836659 r837108) (join_sums term (lo:=837557) (a:=449) (b:=449) r837557 r838006)))) (join_sums term (lo:=838455) (a:=3591) (b:=3591) (join_sums term (lo:=838455) (a:=1795) (b:=1796) (join_sums term (lo:=838455) (a:=897) (b:=898) (join_sums term (lo:=838455) (a:=448) (b:=449) r838455 r838903) (join_sums term (lo:=839352) (a:=449) (b:=449) r839352 r839801)) (join_sums term (lo:=840250) (a:=898) (b:=898) (join_sums term (lo:=840250) (a:=449) (b:=449) r840250 r840699) (join_sums term (lo:=841148) (a:=449) (b:=449) r841148 r841597))) (join_sums term (lo:=842046) (a:=1795) (b:=1796) (join_sums term (lo:=842046) (a:=897) (b:=898) (join_sums term (lo:=842046) (a:=448) (b:=449) r842046 r842494) (join_sums term (lo:=842943) (a:=449) (b:=449) r842943 r843392)) (join_sums term (lo:=843841) (a:=898) (b:=898) (join_sums term (lo:=843841) (a:=449) (b:=449) r843841 r844290) (join_sums term (lo:=844739) (a:=449) (b:=449) r844739 r845188))))) (join_sums term (lo:=845637) (a:=7182) (b:=7182) (join_sums term (lo:=845637) (a:=3591) (b:=3591) (join_sums term (lo:=845637) (a:=1795) (b:=1796) (join_sums term (lo:=845637) (a:=897) (b:=898) (join_sums term (lo:=845637) (a:=448) (b:=449) r845637 r846085) (join_sums term (lo:=846534) (a:=449) (b:=449) r846534 r846983)) (join_sums term (lo:=847432) (a:=898) (b:=898) (join_sums term (lo:=847432) (a:=449) (b:=449) r847432 r847881) (join_sums term (lo:=848330) (a:=449) (b:=449) r848330 r848779))) (join_sums term (lo:=849228) (a:=1795) (b:=1796) (join_sums term (lo:=849228) (a:=897) (b:=898) (join_sums term (lo:=849228) (a:=448) (b:=449) r849228 r849676) (join_sums term (lo:=850125) (a:=449) (b:=449) r850125 r850574)) (join_sums term (lo:=851023) (a:=898) (b:=898) (join_sums term (lo:=851023) (a:=449) (b:=449) r851023 r851472) (join_sums term (lo:=851921) (a:=449) (b:=449) r851921 r852370)))) (join_sums term (lo:=852819) (a:=3591) (b:=3591) (join_sums term (lo:=852819) (a:=1795) (b:=1796) (join_sums term (lo:=852819) (a:=897) (b:=898) (join_sums term (lo:=852819) (a:=448) (b:=449) r852819 r853267) (join_sums term (lo:=853716) (a:=449) (b:=449) r853716 r854165)) (join_sums term (lo:=854614) (a:=898) (b:=898) (join_sums term (lo:=854614) (a:=449) (b:=449) r854614 r855063) (join_sums term (lo:=855512) (a:=449) (b:=449) r855512 r855961))) (join_sums term (lo:=856410) (a:=1795) (b:=1796) (join_sums term (lo:=856410) (a:=897) (b:=898) (join_sums term (lo:=856410) (a:=448) (b:=449) r856410 r856858) (join_sums term (lo:=857307) (a:=449) (b:=449) r857307 r857756)) (join_sums term (lo:=858205) (a:=898) (b:=898) (join_sums term (lo:=858205) (a:=449) (b:=449) r858205 r858654) (join_sums term (lo:=859103) (a:=449) (b:=449) r859103 r859552))))))))

private theorem rows : blockSum term 0 860001 7077912147 :=
  join_sums term (lo:=0) (a:=745090) (b:=114911) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 860000).filter (745089 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=7077912147 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From745089To860000
