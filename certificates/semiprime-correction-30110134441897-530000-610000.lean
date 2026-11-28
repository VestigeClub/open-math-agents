import certificates.«semiprime-correction-555157672301-small»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 530,000 through 610,000

The sum covers 6,036 primes. Their quotient counts are checked by the
certified prime-counting table through 67,545,646.
-/
open Finset
namespace Correction30110134441897From530000To610000

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


private abbrev term := contribution 30110134441897 530000 RangePrimeA26.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 530001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 530000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r530001 : blockSum term 530001 625 166908144 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r530626 : blockSum term 530626 625 156719439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r531251 : blockSum term 531251 625 143207413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r531876 : blockSum term 531876 625 156351636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r532501 : blockSum term 532501 625 166152252 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r533126 : blockSum term 533126 625 146049292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r533751 : blockSum term 533751 625 169089464 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r534376 : blockSum term 534376 625 135782484 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r535001 : blockSum term 535001 625 138939407 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r535626 : blockSum term 535626 625 165215043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r536251 : blockSum term 536251 625 181530909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r536876 : blockSum term 536876 625 151667244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r537501 : blockSum term 537501 625 138308010 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r538126 : blockSum term 538126 625 161185473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r538751 : blockSum term 538751 625 167574357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r539376 : blockSum term 539376 625 128002687 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r540001 : blockSum term 540001 625 160635459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r540626 : blockSum term 540626 625 137539117 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r541251 : blockSum term 541251 625 163553488 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r541876 : blockSum term 541876 625 160107601 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r542501 : blockSum term 542501 625 143612731 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r543126 : blockSum term 543126 625 169541406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r543751 : blockSum term 543751 625 153073339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r544376 : blockSum term 544376 625 143125373 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r545001 : blockSum term 545001 625 139720668 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r545626 : blockSum term 545626 625 155794990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r546251 : blockSum term 546251 625 136176790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r546876 : blockSum term 546876 625 152209053 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r547501 : blockSum term 547501 625 152051149 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r548126 : blockSum term 548126 625 151875049 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r548751 : blockSum term 548751 625 161405173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r549376 : blockSum term 549376 625 158001582 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r550001 : blockSum term 550001 625 148162799 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r550626 : blockSum term 550626 625 167308815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r551251 : blockSum term 551251 625 151044842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r551876 : blockSum term 551876 625 144465950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r552501 : blockSum term 552501 625 150712573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r553126 : blockSum term 553126 625 160158636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r553751 : blockSum term 553751 625 140795554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r554376 : blockSum term 554376 625 163008499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r555001 : blockSum term 555001 625 124528216 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r555626 : blockSum term 555626 625 127579603 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r556251 : blockSum term 556251 625 191153781 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r556876 : blockSum term 556876 625 133670123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r557501 : blockSum term 557501 625 146240449 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r558126 : blockSum term 558126 625 142904914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r558751 : blockSum term 558751 625 149091413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r559376 : blockSum term 559376 625 155270723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r560001 : blockSum term 560001 625 177267818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r560626 : blockSum term 560626 625 151778311 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r561251 : blockSum term 561251 625 104235820 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r561876 : blockSum term 561876 625 151443165 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r562501 : blockSum term 562501 625 182802868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r563126 : blockSum term 563126 625 116493790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r563751 : blockSum term 563751 625 157247082 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r564376 : blockSum term 564376 625 138236812 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r565001 : blockSum term 565001 625 172599818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r565626 : blockSum term 565626 625 131663915 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r566251 : blockSum term 566251 625 137788437 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r566876 : blockSum term 566876 625 131388080 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r567501 : blockSum term 567501 625 146871282 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r568126 : blockSum term 568126 625 140482022 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r568751 : blockSum term 568751 625 152799434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r569376 : blockSum term 569376 625 152632991 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r570001 : blockSum term 570001 625 168034896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r570626 : blockSum term 570626 625 155423276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r571251 : blockSum term 571251 625 145930862 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r571876 : blockSum term 571876 625 145779240 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r572501 : blockSum term 572501 625 158031160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r573126 : blockSum term 573126 625 133096911 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r573751 : blockSum term 573751 625 151514121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r574376 : blockSum term 574376 625 132819128 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r575001 : blockSum term 575001 625 148103955 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r575626 : blockSum term 575626 625 157194400 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r576251 : blockSum term 576251 625 147795887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r576876 : blockSum term 576876 625 141489185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r577501 : blockSum term 577501 625 144418331 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r578126 : blockSum term 578126 625 153467053 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r578751 : blockSum term 578751 625 128783952 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r579376 : blockSum term 579376 625 162342984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r580001 : blockSum term 580001 625 119333310 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r580626 : blockSum term 580626 625 165062712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r581251 : blockSum term 581251 625 155722341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r581876 : blockSum term 581876 625 131159185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r582501 : blockSum term 582501 625 137119656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r583126 : blockSum term 583126 625 158289505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r583751 : blockSum term 583751 625 121635882 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r584376 : blockSum term 584376 625 154914004 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r585001 : blockSum term 585001 625 145655505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r585626 : blockSum term 585626 625 151569957 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r586251 : blockSum term 586251 625 151404087 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r586876 : blockSum term 586876 625 160329203 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r587501 : blockSum term 587501 625 172248223 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r588126 : blockSum term 588126 625 135843343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r588751 : blockSum term 588751 625 132686747 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r589376 : blockSum term 589376 625 123514906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r590001 : blockSum term 590001 625 132422999 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r590626 : blockSum term 590626 625 129280422 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r591251 : blockSum term 591251 625 132150468 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r591876 : blockSum term 591876 625 141010124 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r592501 : blockSum term 592501 625 149863015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r593126 : blockSum term 593126 625 155701768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r593751 : blockSum term 593751 625 128610782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r594376 : blockSum term 594376 625 149404722 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r595001 : blockSum term 595001 625 158214671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r595626 : blockSum term 595626 625 131199724 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r596251 : blockSum term 596251 625 142983877 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r596876 : blockSum term 596876 625 133912453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r597501 : blockSum term 597501 625 139730784 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r598126 : blockSum term 598126 625 130672867 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r598751 : blockSum term 598751 625 133507893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r599376 : blockSum term 599376 625 142265074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r600001 : blockSum term 600001 625 139159529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r600626 : blockSum term 600626 625 144932546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r601251 : blockSum term 601251 625 130015446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r601876 : blockSum term 601876 625 153499522 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r602501 : blockSum term 602501 625 141551829 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r603126 : blockSum term 603126 625 123729435 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r603751 : blockSum term 603751 625 150100122 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r604376 : blockSum term 604376 625 141120334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r605001 : blockSum term 605001 625 143914816 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r605626 : blockSum term 605626 625 129100137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r606251 : blockSum term 606251 625 128971287 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r606876 : blockSum term 606876 625 152276840 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r607501 : blockSum term 607501 625 125785368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r608126 : blockSum term 608126 625 143197356 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r608751 : blockSum term 608751 625 148890231 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r609376 : blockSum term 609376 625 145830726 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 530001 80000 18816655831 := (join_sums term (lo:=530001) (a:=40000) (b:=40000) (join_sums term (lo:=530001) (a:=20000) (b:=20000) (join_sums term (lo:=530001) (a:=10000) (b:=10000) (join_sums term (lo:=530001) (a:=5000) (b:=5000) (join_sums term (lo:=530001) (a:=2500) (b:=2500) (join_sums term (lo:=530001) (a:=1250) (b:=1250) (join_sums term (lo:=530001) (a:=625) (b:=625) r530001 r530626) (join_sums term (lo:=531251) (a:=625) (b:=625) r531251 r531876)) (join_sums term (lo:=532501) (a:=1250) (b:=1250) (join_sums term (lo:=532501) (a:=625) (b:=625) r532501 r533126) (join_sums term (lo:=533751) (a:=625) (b:=625) r533751 r534376))) (join_sums term (lo:=535001) (a:=2500) (b:=2500) (join_sums term (lo:=535001) (a:=1250) (b:=1250) (join_sums term (lo:=535001) (a:=625) (b:=625) r535001 r535626) (join_sums term (lo:=536251) (a:=625) (b:=625) r536251 r536876)) (join_sums term (lo:=537501) (a:=1250) (b:=1250) (join_sums term (lo:=537501) (a:=625) (b:=625) r537501 r538126) (join_sums term (lo:=538751) (a:=625) (b:=625) r538751 r539376)))) (join_sums term (lo:=540001) (a:=5000) (b:=5000) (join_sums term (lo:=540001) (a:=2500) (b:=2500) (join_sums term (lo:=540001) (a:=1250) (b:=1250) (join_sums term (lo:=540001) (a:=625) (b:=625) r540001 r540626) (join_sums term (lo:=541251) (a:=625) (b:=625) r541251 r541876)) (join_sums term (lo:=542501) (a:=1250) (b:=1250) (join_sums term (lo:=542501) (a:=625) (b:=625) r542501 r543126) (join_sums term (lo:=543751) (a:=625) (b:=625) r543751 r544376))) (join_sums term (lo:=545001) (a:=2500) (b:=2500) (join_sums term (lo:=545001) (a:=1250) (b:=1250) (join_sums term (lo:=545001) (a:=625) (b:=625) r545001 r545626) (join_sums term (lo:=546251) (a:=625) (b:=625) r546251 r546876)) (join_sums term (lo:=547501) (a:=1250) (b:=1250) (join_sums term (lo:=547501) (a:=625) (b:=625) r547501 r548126) (join_sums term (lo:=548751) (a:=625) (b:=625) r548751 r549376))))) (join_sums term (lo:=550001) (a:=10000) (b:=10000) (join_sums term (lo:=550001) (a:=5000) (b:=5000) (join_sums term (lo:=550001) (a:=2500) (b:=2500) (join_sums term (lo:=550001) (a:=1250) (b:=1250) (join_sums term (lo:=550001) (a:=625) (b:=625) r550001 r550626) (join_sums term (lo:=551251) (a:=625) (b:=625) r551251 r551876)) (join_sums term (lo:=552501) (a:=1250) (b:=1250) (join_sums term (lo:=552501) (a:=625) (b:=625) r552501 r553126) (join_sums term (lo:=553751) (a:=625) (b:=625) r553751 r554376))) (join_sums term (lo:=555001) (a:=2500) (b:=2500) (join_sums term (lo:=555001) (a:=1250) (b:=1250) (join_sums term (lo:=555001) (a:=625) (b:=625) r555001 r555626) (join_sums term (lo:=556251) (a:=625) (b:=625) r556251 r556876)) (join_sums term (lo:=557501) (a:=1250) (b:=1250) (join_sums term (lo:=557501) (a:=625) (b:=625) r557501 r558126) (join_sums term (lo:=558751) (a:=625) (b:=625) r558751 r559376)))) (join_sums term (lo:=560001) (a:=5000) (b:=5000) (join_sums term (lo:=560001) (a:=2500) (b:=2500) (join_sums term (lo:=560001) (a:=1250) (b:=1250) (join_sums term (lo:=560001) (a:=625) (b:=625) r560001 r560626) (join_sums term (lo:=561251) (a:=625) (b:=625) r561251 r561876)) (join_sums term (lo:=562501) (a:=1250) (b:=1250) (join_sums term (lo:=562501) (a:=625) (b:=625) r562501 r563126) (join_sums term (lo:=563751) (a:=625) (b:=625) r563751 r564376))) (join_sums term (lo:=565001) (a:=2500) (b:=2500) (join_sums term (lo:=565001) (a:=1250) (b:=1250) (join_sums term (lo:=565001) (a:=625) (b:=625) r565001 r565626) (join_sums term (lo:=566251) (a:=625) (b:=625) r566251 r566876)) (join_sums term (lo:=567501) (a:=1250) (b:=1250) (join_sums term (lo:=567501) (a:=625) (b:=625) r567501 r568126) (join_sums term (lo:=568751) (a:=625) (b:=625) r568751 r569376)))))) (join_sums term (lo:=570001) (a:=20000) (b:=20000) (join_sums term (lo:=570001) (a:=10000) (b:=10000) (join_sums term (lo:=570001) (a:=5000) (b:=5000) (join_sums term (lo:=570001) (a:=2500) (b:=2500) (join_sums term (lo:=570001) (a:=1250) (b:=1250) (join_sums term (lo:=570001) (a:=625) (b:=625) r570001 r570626) (join_sums term (lo:=571251) (a:=625) (b:=625) r571251 r571876)) (join_sums term (lo:=572501) (a:=1250) (b:=1250) (join_sums term (lo:=572501) (a:=625) (b:=625) r572501 r573126) (join_sums term (lo:=573751) (a:=625) (b:=625) r573751 r574376))) (join_sums term (lo:=575001) (a:=2500) (b:=2500) (join_sums term (lo:=575001) (a:=1250) (b:=1250) (join_sums term (lo:=575001) (a:=625) (b:=625) r575001 r575626) (join_sums term (lo:=576251) (a:=625) (b:=625) r576251 r576876)) (join_sums term (lo:=577501) (a:=1250) (b:=1250) (join_sums term (lo:=577501) (a:=625) (b:=625) r577501 r578126) (join_sums term (lo:=578751) (a:=625) (b:=625) r578751 r579376)))) (join_sums term (lo:=580001) (a:=5000) (b:=5000) (join_sums term (lo:=580001) (a:=2500) (b:=2500) (join_sums term (lo:=580001) (a:=1250) (b:=1250) (join_sums term (lo:=580001) (a:=625) (b:=625) r580001 r580626) (join_sums term (lo:=581251) (a:=625) (b:=625) r581251 r581876)) (join_sums term (lo:=582501) (a:=1250) (b:=1250) (join_sums term (lo:=582501) (a:=625) (b:=625) r582501 r583126) (join_sums term (lo:=583751) (a:=625) (b:=625) r583751 r584376))) (join_sums term (lo:=585001) (a:=2500) (b:=2500) (join_sums term (lo:=585001) (a:=1250) (b:=1250) (join_sums term (lo:=585001) (a:=625) (b:=625) r585001 r585626) (join_sums term (lo:=586251) (a:=625) (b:=625) r586251 r586876)) (join_sums term (lo:=587501) (a:=1250) (b:=1250) (join_sums term (lo:=587501) (a:=625) (b:=625) r587501 r588126) (join_sums term (lo:=588751) (a:=625) (b:=625) r588751 r589376))))) (join_sums term (lo:=590001) (a:=10000) (b:=10000) (join_sums term (lo:=590001) (a:=5000) (b:=5000) (join_sums term (lo:=590001) (a:=2500) (b:=2500) (join_sums term (lo:=590001) (a:=1250) (b:=1250) (join_sums term (lo:=590001) (a:=625) (b:=625) r590001 r590626) (join_sums term (lo:=591251) (a:=625) (b:=625) r591251 r591876)) (join_sums term (lo:=592501) (a:=1250) (b:=1250) (join_sums term (lo:=592501) (a:=625) (b:=625) r592501 r593126) (join_sums term (lo:=593751) (a:=625) (b:=625) r593751 r594376))) (join_sums term (lo:=595001) (a:=2500) (b:=2500) (join_sums term (lo:=595001) (a:=1250) (b:=1250) (join_sums term (lo:=595001) (a:=625) (b:=625) r595001 r595626) (join_sums term (lo:=596251) (a:=625) (b:=625) r596251 r596876)) (join_sums term (lo:=597501) (a:=1250) (b:=1250) (join_sums term (lo:=597501) (a:=625) (b:=625) r597501 r598126) (join_sums term (lo:=598751) (a:=625) (b:=625) r598751 r599376)))) (join_sums term (lo:=600001) (a:=5000) (b:=5000) (join_sums term (lo:=600001) (a:=2500) (b:=2500) (join_sums term (lo:=600001) (a:=1250) (b:=1250) (join_sums term (lo:=600001) (a:=625) (b:=625) r600001 r600626) (join_sums term (lo:=601251) (a:=625) (b:=625) r601251 r601876)) (join_sums term (lo:=602501) (a:=1250) (b:=1250) (join_sums term (lo:=602501) (a:=625) (b:=625) r602501 r603126) (join_sums term (lo:=603751) (a:=625) (b:=625) r603751 r604376))) (join_sums term (lo:=605001) (a:=2500) (b:=2500) (join_sums term (lo:=605001) (a:=1250) (b:=1250) (join_sums term (lo:=605001) (a:=625) (b:=625) r605001 r605626) (join_sums term (lo:=606251) (a:=625) (b:=625) r606251 r606876)) (join_sums term (lo:=607501) (a:=1250) (b:=1250) (join_sums term (lo:=607501) (a:=625) (b:=625) r607501 r608126) (join_sums term (lo:=608751) (a:=625) (b:=625) r608751 r609376)))))))

private theorem rows : blockSum term 0 610001 18816655831 :=
  join_sums term (lo:=0) (a:=530001) (b:=80000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 610000).filter (530000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=18816655831 :=
  right_from_blocks (l:=34751024) (b:=67545646) (small:=745089)
    RangePrimeA26.fast FastDenseA26.fast FastDenseA26.prime (RangePrimeA26.fast_correct RankWheel34751.first_anchor)
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From530000To610000
