import certificates.«semiprime-correction-555157672301-small»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 690,000 through 745,089

The sum covers 4,068 primes. Their quotient counts are checked by the
certified prime-counting table through 67,545,646.
-/
open Finset
namespace Correction30110134441897From690000To745089

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


private abbrev term := contribution 30110134441897 690000 RangePrimeA26.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 690001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 690000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r690001 : blockSum term 690001 430 64604079 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r690431 : blockSum term 690431 430 69735164 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r690861 : blockSum term 690861 430 74852089 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r691291 : blockSum term 691291 431 79964368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r691722 : blockSum term 691722 430 100541318 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r692152 : blockSum term 692152 431 92747164 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r692583 : blockSum term 692583 430 74669470 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r693013 : blockSum term 693013 431 79768579 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r693444 : blockSum term 693444 430 92576219 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r693874 : blockSum term 693874 430 66820779 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r694304 : blockSum term 694304 430 95039762 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r694734 : blockSum term 694734 431 84707281 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r695165 : blockSum term 695165 430 84656927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r695595 : blockSum term 695595 431 79481706 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r696026 : blockSum term 696026 430 76868095 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r696456 : blockSum term 696456 431 84505699 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r696887 : blockSum term 696887 430 87014991 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r697317 : blockSum term 697317 430 94632629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r697747 : blockSum term 697747 430 66458947 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r698177 : blockSum term 698177 431 86854150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r698608 : blockSum term 698608 430 56164868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r699038 : blockSum term 699038 431 91851580 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r699469 : blockSum term 699469 430 68850626 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r699899 : blockSum term 699899 431 78999059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r700330 : blockSum term 700330 430 81501210 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r700760 : blockSum term 700760 430 73817040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r701190 : blockSum term 701190 430 91576009 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r701620 : blockSum term 701620 431 68645257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r702051 : blockSum term 702051 430 94008885 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r702481 : blockSum term 702481 431 93954792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r702912 : blockSum term 702912 430 76130202 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r703342 : blockSum term 703342 431 76086552 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r703773 : blockSum term 703773 430 86178300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r704203 : blockSum term 704203 430 88662347 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r704633 : blockSum term 704633 430 98735912 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r705063 : blockSum term 705063 431 78437267 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r705494 : blockSum term 705494 430 65742484 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r705924 : blockSum term 705924 431 93504445 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r706355 : blockSum term 706355 430 80818352 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r706785 : blockSum term 706785 431 83297029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r707216 : blockSum term 707216 430 60544026 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r707646 : blockSum term 707646 430 113450306 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r708076 : blockSum term 708076 430 85667561 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r708506 : blockSum term 708506 431 65471812 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r708937 : blockSum term 708937 430 78014535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r709367 : blockSum term 709367 431 82997843 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r709798 : blockSum term 709798 430 80440261 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r710228 : blockSum term 710228 431 95459970 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r710659 : blockSum term 710659 430 85359779 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r711089 : blockSum term 711089 430 75275179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r711519 : blockSum term 711519 430 90274472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r711949 : blockSum term 711949 431 70171871 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r712380 : blockSum term 712380 430 77645752 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r712810 : blockSum term 712810 431 87609467 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r713241 : blockSum term 713241 430 82556432 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r713671 : blockSum term 713671 431 65004665 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r714102 : blockSum term 714102 430 67463710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r714532 : blockSum term 714532 430 82404035 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r714962 : blockSum term 714962 430 79862472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r715392 : blockSum term 715392 431 82309628 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r715823 : blockSum term 715823 430 79773657 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r716253 : blockSum term 716253 431 79720704 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r716684 : blockSum term 716684 430 82165199 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r717114 : blockSum term 717114 431 72162526 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r717545 : blockSum term 717545 430 64661687 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r717975 : blockSum term 717975 430 72078029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r718405 : blockSum term 718405 430 72039961 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r718835 : blockSum term 718835 431 81925472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r719266 : blockSum term 719266 430 69471255 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r719696 : blockSum term 719696 431 79352768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r720127 : blockSum term 720127 430 84262572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r720557 : blockSum term 720557 431 84208283 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r720988 : blockSum term 720988 430 106438123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r721418 : blockSum term 721418 430 61846140 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r721848 : blockSum term 721848 430 79116608 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r722278 : blockSum term 722278 431 79073800 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r722709 : blockSum term 722709 430 86428346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r723139 : blockSum term 723139 431 93785433 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r723570 : blockSum term 723570 430 81395640 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r724000 : blockSum term 724000 431 59166496 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r724431 : blockSum term 724431 430 103482059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r724861 : blockSum term 724861 430 64021919 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r725291 : blockSum term 725291 430 76292609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r725721 : blockSum term 725721 431 83621135 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r726152 : blockSum term 726152 430 71283906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r726582 : blockSum term 726582 431 88438736 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r727013 : blockSum term 727013 430 78566389 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r727443 : blockSum term 727443 431 80973962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r727874 : blockSum term 727874 430 66213368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r728304 : blockSum term 728304 430 75975454 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r728734 : blockSum term 728734 430 83285872 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r729164 : blockSum term 729164 431 85681290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r729595 : blockSum term 729595 430 83187319 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r730025 : blockSum term 730025 431 56240698 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r730456 : blockSum term 730456 430 85533304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r730886 : blockSum term 730886 431 80599351 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r731317 : blockSum term 731317 430 75669553 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r731747 : blockSum term 731747 430 78069311 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r732177 : blockSum term 732177 430 78027039 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r732607 : blockSum term 732607 431 73103363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r733038 : blockSum term 733038 430 85235671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r733468 : blockSum term 733468 431 70582403 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r733899 : blockSum term 733899 430 77842963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r734329 : blockSum term 734329 431 80227702 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r734760 : blockSum term 734760 430 87468495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r735190 : blockSum term 735190 430 82565276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r735620 : blockSum term 735620 430 77661214 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r736050 : blockSum term 736050 431 84894700 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r736481 : blockSum term 736481 430 50905729 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r736911 : blockSum term 736911 431 87222350 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r737342 : blockSum term 737342 430 79905666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r737772 : blockSum term 737772 431 72602483 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r738203 : blockSum term 738203 430 74978509 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r738633 : blockSum term 738633 430 77349149 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r739063 : blockSum term 739063 430 91802155 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r739493 : blockSum term 739493 431 74848442 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r739924 : blockSum term 739924 430 74804055 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r740354 : blockSum term 740354 431 74760335 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r740785 : blockSum term 740785 430 72305338 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r741215 : blockSum term 741215 431 69857886 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r741646 : blockSum term 741646 430 77040892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r742076 : blockSum term 742076 431 69780627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r742507 : blockSum term 742507 430 74553462 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r742937 : blockSum term 742937 431 88928179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r743368 : blockSum term 743368 430 52843716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r743798 : blockSum term 743798 431 67221109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r744229 : blockSum term 744229 430 64782694 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r744659 : blockSum term 744659 431 74339186 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 690001 55089 10126095130 := (join_sums term (lo:=690001) (a:=27544) (b:=27545) (join_sums term (lo:=690001) (a:=13772) (b:=13772) (join_sums term (lo:=690001) (a:=6886) (b:=6886) (join_sums term (lo:=690001) (a:=3443) (b:=3443) (join_sums term (lo:=690001) (a:=1721) (b:=1722) (join_sums term (lo:=690001) (a:=860) (b:=861) (join_sums term (lo:=690001) (a:=430) (b:=430) r690001 r690431) (join_sums term (lo:=690861) (a:=430) (b:=431) r690861 r691291)) (join_sums term (lo:=691722) (a:=861) (b:=861) (join_sums term (lo:=691722) (a:=430) (b:=431) r691722 r692152) (join_sums term (lo:=692583) (a:=430) (b:=431) r692583 r693013))) (join_sums term (lo:=693444) (a:=1721) (b:=1722) (join_sums term (lo:=693444) (a:=860) (b:=861) (join_sums term (lo:=693444) (a:=430) (b:=430) r693444 r693874) (join_sums term (lo:=694304) (a:=430) (b:=431) r694304 r694734)) (join_sums term (lo:=695165) (a:=861) (b:=861) (join_sums term (lo:=695165) (a:=430) (b:=431) r695165 r695595) (join_sums term (lo:=696026) (a:=430) (b:=431) r696026 r696456)))) (join_sums term (lo:=696887) (a:=3443) (b:=3443) (join_sums term (lo:=696887) (a:=1721) (b:=1722) (join_sums term (lo:=696887) (a:=860) (b:=861) (join_sums term (lo:=696887) (a:=430) (b:=430) r696887 r697317) (join_sums term (lo:=697747) (a:=430) (b:=431) r697747 r698177)) (join_sums term (lo:=698608) (a:=861) (b:=861) (join_sums term (lo:=698608) (a:=430) (b:=431) r698608 r699038) (join_sums term (lo:=699469) (a:=430) (b:=431) r699469 r699899))) (join_sums term (lo:=700330) (a:=1721) (b:=1722) (join_sums term (lo:=700330) (a:=860) (b:=861) (join_sums term (lo:=700330) (a:=430) (b:=430) r700330 r700760) (join_sums term (lo:=701190) (a:=430) (b:=431) r701190 r701620)) (join_sums term (lo:=702051) (a:=861) (b:=861) (join_sums term (lo:=702051) (a:=430) (b:=431) r702051 r702481) (join_sums term (lo:=702912) (a:=430) (b:=431) r702912 r703342))))) (join_sums term (lo:=703773) (a:=6886) (b:=6886) (join_sums term (lo:=703773) (a:=3443) (b:=3443) (join_sums term (lo:=703773) (a:=1721) (b:=1722) (join_sums term (lo:=703773) (a:=860) (b:=861) (join_sums term (lo:=703773) (a:=430) (b:=430) r703773 r704203) (join_sums term (lo:=704633) (a:=430) (b:=431) r704633 r705063)) (join_sums term (lo:=705494) (a:=861) (b:=861) (join_sums term (lo:=705494) (a:=430) (b:=431) r705494 r705924) (join_sums term (lo:=706355) (a:=430) (b:=431) r706355 r706785))) (join_sums term (lo:=707216) (a:=1721) (b:=1722) (join_sums term (lo:=707216) (a:=860) (b:=861) (join_sums term (lo:=707216) (a:=430) (b:=430) r707216 r707646) (join_sums term (lo:=708076) (a:=430) (b:=431) r708076 r708506)) (join_sums term (lo:=708937) (a:=861) (b:=861) (join_sums term (lo:=708937) (a:=430) (b:=431) r708937 r709367) (join_sums term (lo:=709798) (a:=430) (b:=431) r709798 r710228)))) (join_sums term (lo:=710659) (a:=3443) (b:=3443) (join_sums term (lo:=710659) (a:=1721) (b:=1722) (join_sums term (lo:=710659) (a:=860) (b:=861) (join_sums term (lo:=710659) (a:=430) (b:=430) r710659 r711089) (join_sums term (lo:=711519) (a:=430) (b:=431) r711519 r711949)) (join_sums term (lo:=712380) (a:=861) (b:=861) (join_sums term (lo:=712380) (a:=430) (b:=431) r712380 r712810) (join_sums term (lo:=713241) (a:=430) (b:=431) r713241 r713671))) (join_sums term (lo:=714102) (a:=1721) (b:=1722) (join_sums term (lo:=714102) (a:=860) (b:=861) (join_sums term (lo:=714102) (a:=430) (b:=430) r714102 r714532) (join_sums term (lo:=714962) (a:=430) (b:=431) r714962 r715392)) (join_sums term (lo:=715823) (a:=861) (b:=861) (join_sums term (lo:=715823) (a:=430) (b:=431) r715823 r716253) (join_sums term (lo:=716684) (a:=430) (b:=431) r716684 r717114)))))) (join_sums term (lo:=717545) (a:=13772) (b:=13773) (join_sums term (lo:=717545) (a:=6886) (b:=6886) (join_sums term (lo:=717545) (a:=3443) (b:=3443) (join_sums term (lo:=717545) (a:=1721) (b:=1722) (join_sums term (lo:=717545) (a:=860) (b:=861) (join_sums term (lo:=717545) (a:=430) (b:=430) r717545 r717975) (join_sums term (lo:=718405) (a:=430) (b:=431) r718405 r718835)) (join_sums term (lo:=719266) (a:=861) (b:=861) (join_sums term (lo:=719266) (a:=430) (b:=431) r719266 r719696) (join_sums term (lo:=720127) (a:=430) (b:=431) r720127 r720557))) (join_sums term (lo:=720988) (a:=1721) (b:=1722) (join_sums term (lo:=720988) (a:=860) (b:=861) (join_sums term (lo:=720988) (a:=430) (b:=430) r720988 r721418) (join_sums term (lo:=721848) (a:=430) (b:=431) r721848 r722278)) (join_sums term (lo:=722709) (a:=861) (b:=861) (join_sums term (lo:=722709) (a:=430) (b:=431) r722709 r723139) (join_sums term (lo:=723570) (a:=430) (b:=431) r723570 r724000)))) (join_sums term (lo:=724431) (a:=3443) (b:=3443) (join_sums term (lo:=724431) (a:=1721) (b:=1722) (join_sums term (lo:=724431) (a:=860) (b:=861) (join_sums term (lo:=724431) (a:=430) (b:=430) r724431 r724861) (join_sums term (lo:=725291) (a:=430) (b:=431) r725291 r725721)) (join_sums term (lo:=726152) (a:=861) (b:=861) (join_sums term (lo:=726152) (a:=430) (b:=431) r726152 r726582) (join_sums term (lo:=727013) (a:=430) (b:=431) r727013 r727443))) (join_sums term (lo:=727874) (a:=1721) (b:=1722) (join_sums term (lo:=727874) (a:=860) (b:=861) (join_sums term (lo:=727874) (a:=430) (b:=430) r727874 r728304) (join_sums term (lo:=728734) (a:=430) (b:=431) r728734 r729164)) (join_sums term (lo:=729595) (a:=861) (b:=861) (join_sums term (lo:=729595) (a:=430) (b:=431) r729595 r730025) (join_sums term (lo:=730456) (a:=430) (b:=431) r730456 r730886))))) (join_sums term (lo:=731317) (a:=6886) (b:=6887) (join_sums term (lo:=731317) (a:=3443) (b:=3443) (join_sums term (lo:=731317) (a:=1721) (b:=1722) (join_sums term (lo:=731317) (a:=860) (b:=861) (join_sums term (lo:=731317) (a:=430) (b:=430) r731317 r731747) (join_sums term (lo:=732177) (a:=430) (b:=431) r732177 r732607)) (join_sums term (lo:=733038) (a:=861) (b:=861) (join_sums term (lo:=733038) (a:=430) (b:=431) r733038 r733468) (join_sums term (lo:=733899) (a:=430) (b:=431) r733899 r734329))) (join_sums term (lo:=734760) (a:=1721) (b:=1722) (join_sums term (lo:=734760) (a:=860) (b:=861) (join_sums term (lo:=734760) (a:=430) (b:=430) r734760 r735190) (join_sums term (lo:=735620) (a:=430) (b:=431) r735620 r736050)) (join_sums term (lo:=736481) (a:=861) (b:=861) (join_sums term (lo:=736481) (a:=430) (b:=431) r736481 r736911) (join_sums term (lo:=737342) (a:=430) (b:=431) r737342 r737772)))) (join_sums term (lo:=738203) (a:=3443) (b:=3444) (join_sums term (lo:=738203) (a:=1721) (b:=1722) (join_sums term (lo:=738203) (a:=860) (b:=861) (join_sums term (lo:=738203) (a:=430) (b:=430) r738203 r738633) (join_sums term (lo:=739063) (a:=430) (b:=431) r739063 r739493)) (join_sums term (lo:=739924) (a:=861) (b:=861) (join_sums term (lo:=739924) (a:=430) (b:=431) r739924 r740354) (join_sums term (lo:=740785) (a:=430) (b:=431) r740785 r741215))) (join_sums term (lo:=741646) (a:=1722) (b:=1722) (join_sums term (lo:=741646) (a:=861) (b:=861) (join_sums term (lo:=741646) (a:=430) (b:=431) r741646 r742076) (join_sums term (lo:=742507) (a:=430) (b:=431) r742507 r742937)) (join_sums term (lo:=743368) (a:=861) (b:=861) (join_sums term (lo:=743368) (a:=430) (b:=431) r743368 r743798) (join_sums term (lo:=744229) (a:=430) (b:=431) r744229 r744659)))))))

private theorem rows : blockSum term 0 745090 10126095130 :=
  join_sums term (lo:=0) (a:=690001) (b:=55089) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 745089).filter (690000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=10126095130 :=
  right_from_blocks (l:=34751024) (b:=67545646) (small:=745089)
    RangePrimeA26.fast FastDenseA26.fast FastDenseA26.prime (RangePrimeA26.fast_correct RankWheel34751.first_anchor)
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From690000To745089
