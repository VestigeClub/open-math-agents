import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 560,000 through 745,089

The sum covers 13,811 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction11092009835083From560000To745089

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


private abbrev term := contribution 11092009835083 560000 SparsePrimeA204.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 560001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 560000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r560001 : blockSum term 560001 723 77586326 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r560724 : blockSum term 560724 723 65376497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r561447 : blockSum term 561447 723 45941727 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r562170 : blockSum term 562170 723 74867449 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r562893 : blockSum term 562893 723 67536519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r563616 : blockSum term 563616 723 61418199 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r564339 : blockSum term 564339 723 63751530 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r565062 : blockSum term 565062 723 70876350 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r565785 : blockSum term 565785 723 57587288 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r566508 : blockSum term 566508 723 64706250 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r567231 : blockSum term 567231 723 63420875 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r567954 : blockSum term 567954 723 62151682 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r568677 : blockSum term 568677 723 64458540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r569400 : blockSum term 569400 723 76294396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r570123 : blockSum term 570123 723 67863223 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r570846 : blockSum term 570846 723 59458543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r571569 : blockSum term 571569 723 67692584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r572292 : blockSum term 572292 723 75905718 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r573015 : blockSum term 573015 723 56854793 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r573738 : blockSum term 573738 723 65067684 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r574461 : blockSum term 574461 723 62617722 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r575184 : blockSum term 575184 723 64898133 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r575907 : blockSum term 575907 723 67173582 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r576630 : blockSum term 576630 723 65913184 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r577353 : blockSum term 577353 723 63478297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r578076 : blockSum term 578076 723 65743955 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r578799 : blockSum term 578799 723 59800311 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r579522 : blockSum term 579522 723 65584407 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r580245 : blockSum term 580245 723 64326234 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r580968 : blockSum term 580968 723 67752387 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r581691 : blockSum term 581691 723 60669997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r582414 : blockSum term 582414 723 61757616 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r583137 : blockSum term 583137 723 69827750 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r583860 : blockSum term 583860 723 52304677 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r584583 : blockSum term 584583 723 70815069 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r585306 : blockSum term 585306 723 67243474 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r586029 : blockSum term 586029 723 63685069 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r586752 : blockSum term 586752 723 72859609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r587475 : blockSum term 587475 723 73923778 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r588198 : blockSum term 588198 723 57680018 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r588921 : blockSum term 588921 723 59911604 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r589644 : blockSum term 589644 723 58685534 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r590367 : blockSum term 590367 723 55167614 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r591090 : blockSum term 591090 723 57395481 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r591813 : blockSum term 591813 723 61906658 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r592536 : blockSum term 592536 723 68701662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r593259 : blockSum term 593259 723 59473028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r593982 : blockSum term 593982 723 65108374 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r594705 : blockSum term 594705 723 73010877 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r595428 : blockSum term 595428 723 56965994 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r596151 : blockSum term 596151 723 61449021 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r596874 : blockSum term 596874 723 61372770 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r597597 : blockSum term 597597 723 57896353 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r598320 : blockSum term 598320 723 62355727 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r599043 : blockSum term 599043 723 58881970 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r599766 : blockSum term 599766 723 64465173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r600489 : blockSum term 600489 723 58740743 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r601212 : blockSum term 601212 723 58672926 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r601935 : blockSum term 601935 723 67616792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r602658 : blockSum term 602658 723 56280874 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r603381 : blockSum term 603381 723 69697317 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r604104 : blockSum term 604104 723 58383133 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r604827 : blockSum term 604827 723 60560570 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r605550 : blockSum term 605550 723 59365987 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r606273 : blockSum term 606273 723 57054742 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r606996 : blockSum term 606996 723 62579011 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r607719 : blockSum term 607719 723 64725741 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r608442 : blockSum term 608442 723 60187318 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r609165 : blockSum term 609165 723 66797764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r609888 : blockSum term 609888 723 51147756 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r610611 : blockSum term 610611 723 65529524 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r611334 : blockSum term 611334 723 59896693 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r612057 : blockSum term 612057 723 57616335 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r612780 : blockSum term 612780 723 66395314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r613503 : blockSum term 613503 723 58580962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r614226 : blockSum term 614226 723 57404780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r614949 : blockSum term 614949 723 56235629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r615672 : blockSum term 615672 723 68285435 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r616395 : blockSum term 616395 723 64904167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r617118 : blockSum term 617118 723 67022525 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r617841 : blockSum term 617841 723 52673442 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r618564 : blockSum term 618564 723 59184922 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r619287 : blockSum term 619287 723 54734550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r620010 : blockSum term 620010 723 61231297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r620733 : blockSum term 620733 723 58975235 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r621456 : blockSum term 621456 723 57811880 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r622179 : blockSum term 622179 723 55568383 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r622902 : blockSum term 622902 723 51149830 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r623625 : blockSum term 623625 723 69566129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r624348 : blockSum term 624348 723 56455624 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r625071 : blockSum term 625071 723 54222953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r625794 : blockSum term 625794 723 48744655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r626517 : blockSum term 626517 723 62751736 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r627240 : blockSum term 627240 723 55110519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r627963 : blockSum term 627963 723 50731680 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r628686 : blockSum term 628686 723 53908529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r629409 : blockSum term 629409 723 62456683 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r630132 : blockSum term 630132 723 51628326 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r630855 : blockSum term 630855 723 61233262 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r631578 : blockSum term 631578 723 63309150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r632301 : blockSum term 632301 723 58948953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r633024 : blockSum term 633024 723 50316194 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r633747 : blockSum term 633747 723 60950531 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r634470 : blockSum term 634470 723 58744688 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r635193 : blockSum term 635193 723 64007067 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r635916 : blockSum term 635916 723 58603999 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r636639 : blockSum term 636639 723 57468410 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r637362 : blockSum term 637362 723 56340215 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r638085 : blockSum term 638085 723 43532617 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r638808 : blockSum term 638808 723 50905493 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r639531 : blockSum term 639531 723 63559030 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r640254 : blockSum term 640254 723 55015950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r640977 : blockSum term 640977 723 48613148 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r641700 : blockSum term 641700 723 58059022 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r642423 : blockSum term 642423 723 54823449 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r643146 : blockSum term 643146 723 48444269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r643869 : blockSum term 643869 723 64168079 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r644592 : blockSum term 644592 723 58845008 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r645315 : blockSum term 645315 723 60873849 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r646038 : blockSum term 646038 723 52419299 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r646761 : blockSum term 646761 723 60736009 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r647484 : blockSum term 647484 723 62758605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r648207 : blockSum term 648207 723 51195823 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r648930 : blockSum term 648930 723 62612185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r649653 : blockSum term 649653 723 53163375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r650376 : blockSum term 650376 723 48934412 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r651099 : blockSum term 651099 723 56161024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r651822 : blockSum term 651822 723 57132685 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r652545 : blockSum term 652545 723 59146906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r653268 : blockSum term 653268 723 55963450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r653991 : blockSum term 653991 723 59007687 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r654714 : blockSum term 654714 723 57904704 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r655437 : blockSum term 655437 723 50610358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r656160 : blockSum term 656160 723 53645272 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r656883 : blockSum term 656883 723 56676086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r657606 : blockSum term 657606 723 53521547 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r658329 : blockSum term 658329 723 55520064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r659052 : blockSum term 659052 723 55456828 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r659775 : blockSum term 659775 723 56422084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r660498 : blockSum term 660498 723 64554837 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r661221 : blockSum term 661221 723 47080385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r661944 : blockSum term 661944 723 54184759 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r662667 : blockSum term 662667 723 55144407 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r663390 : blockSum term 663390 723 58139325 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r664113 : blockSum term 664113 723 60113397 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r664836 : blockSum term 664836 723 56993256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r665559 : blockSum term 665559 723 54895708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r666282 : blockSum term 666282 723 50770377 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r667005 : blockSum term 667005 723 54770834 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r667728 : blockSum term 667728 723 43570179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r668451 : blockSum term 668451 723 56672417 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r669174 : blockSum term 669174 723 52564565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r669897 : blockSum term 669897 723 58566260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r670620 : blockSum term 670620 723 53457919 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r671343 : blockSum term 671343 723 54406203 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r672066 : blockSum term 672066 723 52337143 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r672789 : blockSum term 672789 723 63332132 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r673512 : blockSum term 673512 723 49204376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r674235 : blockSum term 674235 723 55166165 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r674958 : blockSum term 674958 723 54104165 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r675681 : blockSum term 675681 723 54043415 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r676404 : blockSum term 676404 723 53980453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r677127 : blockSum term 677127 723 44936784 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r677850 : blockSum term 677850 723 49872543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r678573 : blockSum term 678573 723 59787713 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r679296 : blockSum term 679296 723 62704905 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r680019 : blockSum term 680019 723 54685414 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r680742 : blockSum term 680742 723 55615590 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r681465 : blockSum term 681465 723 52579586 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r682188 : blockSum term 682188 723 49550771 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r682911 : blockSum term 682911 723 46522660 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r683634 : blockSum term 683634 723 59329195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r684357 : blockSum term 684357 723 54320990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r685080 : blockSum term 685080 723 55247509 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r685803 : blockSum term 685803 723 51245314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r686526 : blockSum term 686526 723 53157859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r687249 : blockSum term 687249 723 58020233 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r687972 : blockSum term 687972 723 51078684 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r688695 : blockSum term 688695 723 54948214 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r689418 : blockSum term 689418 723 52927489 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r690141 : blockSum term 690141 723 43079501 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r690864 : blockSum term 690864 723 46946184 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r691587 : blockSum term 691587 723 61550792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r692310 : blockSum term 692310 723 52701560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r693033 : blockSum term 693033 723 54590018 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r693756 : blockSum term 693756 723 51610137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r694479 : blockSum term 694479 723 52529431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r695202 : blockSum term 695202 723 57330231 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r695925 : blockSum term 695925 723 47559532 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r696648 : blockSum term 696648 723 52359233 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r697371 : blockSum term 697371 723 57146334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r698094 : blockSum term 698094 723 43538325 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r698817 : blockSum term 698817 723 54119034 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r699540 : blockSum term 699540 723 44406376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r700263 : blockSum term 700263 723 52074419 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r700986 : blockSum term 700986 723 53941337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r701709 : blockSum term 701709 723 50034255 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r702432 : blockSum term 702432 723 52869987 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r703155 : blockSum term 703155 723 49932074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r703878 : blockSum term 703878 723 58510436 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r704601 : blockSum term 704601 723 60363367 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r705324 : blockSum term 705324 723 44024555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r706047 : blockSum term 706047 723 55453434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r706770 : blockSum term 706770 723 46800398 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r707493 : blockSum term 707493 723 60104685 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r708216 : blockSum term 708216 723 48606041 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r708939 : blockSum term 708939 723 48552446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r709662 : blockSum term 709662 723 54208895 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r710385 : blockSum term 710385 723 57948672 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r711108 : blockSum term 711108 723 50293887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r711831 : blockSum term 711831 723 50241453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r712554 : blockSum term 712554 723 52080549 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r713277 : blockSum term 713277 723 49188576 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r714000 : blockSum term 714000 723 39685615 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r714723 : blockSum term 714723 723 55690391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r715446 : blockSum term 715446 723 53743720 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r716169 : blockSum term 716169 723 48033943 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r716892 : blockSum term 716892 723 47984903 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r717615 : blockSum term 717615 723 40414978 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r718338 : blockSum term 718338 723 48824761 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r719061 : blockSum term 719061 723 50647405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r719784 : blockSum term 719784 723 51531364 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r720507 : blockSum term 720507 723 58962339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r721230 : blockSum term 721230 723 44882126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r721953 : blockSum term 721953 723 53241481 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r722676 : blockSum term 722676 723 53181415 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r723399 : blockSum term 723399 723 54060402 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r724122 : blockSum term 724122 723 51207317 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r724845 : blockSum term 724845 723 46506150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r725568 : blockSum term 725568 723 47386197 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r726291 : blockSum term 726291 723 52905092 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r727014 : blockSum term 727014 723 50067715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r727737 : blockSum term 727737 723 42606654 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r728460 : blockSum term 728460 723 53664528 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r729183 : blockSum term 729183 723 51759864 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r729906 : blockSum term 729906 723 44319795 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r730629 : blockSum term 730629 723 52575790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r731352 : blockSum term 731352 723 49754759 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r732075 : blockSum term 732075 723 46944797 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r732798 : blockSum term 732798 723 53329097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r733521 : blockSum term 733521 723 46842610 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r734244 : blockSum term 734244 723 50465683 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r734967 : blockSum term 734967 723 53165002 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r735690 : blockSum term 735690 723 51276982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r736413 : blockSum term 736413 723 42989703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r737136 : blockSum term 737136 723 51171578 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r737859 : blockSum term 737859 723 46554749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r738582 : blockSum term 738582 723 51064083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r739305 : blockSum term 739305 723 51926167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r740028 : blockSum term 740028 723 48228880 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r740751 : blockSum term 740751 723 43634148 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r741474 : blockSum term 741474 723 44501965 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r742197 : blockSum term 742197 723 48992898 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r742920 : blockSum term 742920 723 43505400 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r743643 : blockSum term 743643 723 41649436 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r744366 : blockSum term 744366 724 46128975 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 560001 185089 14441249620 := (join_sums term (lo:=560001) (a:=92544) (b:=92545) (join_sums term (lo:=560001) (a:=46272) (b:=46272) (join_sums term (lo:=560001) (a:=23136) (b:=23136) (join_sums term (lo:=560001) (a:=11568) (b:=11568) (join_sums term (lo:=560001) (a:=5784) (b:=5784) (join_sums term (lo:=560001) (a:=2892) (b:=2892) (join_sums term (lo:=560001) (a:=1446) (b:=1446) (join_sums term (lo:=560001) (a:=723) (b:=723) r560001 r560724) (join_sums term (lo:=561447) (a:=723) (b:=723) r561447 r562170)) (join_sums term (lo:=562893) (a:=1446) (b:=1446) (join_sums term (lo:=562893) (a:=723) (b:=723) r562893 r563616) (join_sums term (lo:=564339) (a:=723) (b:=723) r564339 r565062))) (join_sums term (lo:=565785) (a:=2892) (b:=2892) (join_sums term (lo:=565785) (a:=1446) (b:=1446) (join_sums term (lo:=565785) (a:=723) (b:=723) r565785 r566508) (join_sums term (lo:=567231) (a:=723) (b:=723) r567231 r567954)) (join_sums term (lo:=568677) (a:=1446) (b:=1446) (join_sums term (lo:=568677) (a:=723) (b:=723) r568677 r569400) (join_sums term (lo:=570123) (a:=723) (b:=723) r570123 r570846)))) (join_sums term (lo:=571569) (a:=5784) (b:=5784) (join_sums term (lo:=571569) (a:=2892) (b:=2892) (join_sums term (lo:=571569) (a:=1446) (b:=1446) (join_sums term (lo:=571569) (a:=723) (b:=723) r571569 r572292) (join_sums term (lo:=573015) (a:=723) (b:=723) r573015 r573738)) (join_sums term (lo:=574461) (a:=1446) (b:=1446) (join_sums term (lo:=574461) (a:=723) (b:=723) r574461 r575184) (join_sums term (lo:=575907) (a:=723) (b:=723) r575907 r576630))) (join_sums term (lo:=577353) (a:=2892) (b:=2892) (join_sums term (lo:=577353) (a:=1446) (b:=1446) (join_sums term (lo:=577353) (a:=723) (b:=723) r577353 r578076) (join_sums term (lo:=578799) (a:=723) (b:=723) r578799 r579522)) (join_sums term (lo:=580245) (a:=1446) (b:=1446) (join_sums term (lo:=580245) (a:=723) (b:=723) r580245 r580968) (join_sums term (lo:=581691) (a:=723) (b:=723) r581691 r582414))))) (join_sums term (lo:=583137) (a:=11568) (b:=11568) (join_sums term (lo:=583137) (a:=5784) (b:=5784) (join_sums term (lo:=583137) (a:=2892) (b:=2892) (join_sums term (lo:=583137) (a:=1446) (b:=1446) (join_sums term (lo:=583137) (a:=723) (b:=723) r583137 r583860) (join_sums term (lo:=584583) (a:=723) (b:=723) r584583 r585306)) (join_sums term (lo:=586029) (a:=1446) (b:=1446) (join_sums term (lo:=586029) (a:=723) (b:=723) r586029 r586752) (join_sums term (lo:=587475) (a:=723) (b:=723) r587475 r588198))) (join_sums term (lo:=588921) (a:=2892) (b:=2892) (join_sums term (lo:=588921) (a:=1446) (b:=1446) (join_sums term (lo:=588921) (a:=723) (b:=723) r588921 r589644) (join_sums term (lo:=590367) (a:=723) (b:=723) r590367 r591090)) (join_sums term (lo:=591813) (a:=1446) (b:=1446) (join_sums term (lo:=591813) (a:=723) (b:=723) r591813 r592536) (join_sums term (lo:=593259) (a:=723) (b:=723) r593259 r593982)))) (join_sums term (lo:=594705) (a:=5784) (b:=5784) (join_sums term (lo:=594705) (a:=2892) (b:=2892) (join_sums term (lo:=594705) (a:=1446) (b:=1446) (join_sums term (lo:=594705) (a:=723) (b:=723) r594705 r595428) (join_sums term (lo:=596151) (a:=723) (b:=723) r596151 r596874)) (join_sums term (lo:=597597) (a:=1446) (b:=1446) (join_sums term (lo:=597597) (a:=723) (b:=723) r597597 r598320) (join_sums term (lo:=599043) (a:=723) (b:=723) r599043 r599766))) (join_sums term (lo:=600489) (a:=2892) (b:=2892) (join_sums term (lo:=600489) (a:=1446) (b:=1446) (join_sums term (lo:=600489) (a:=723) (b:=723) r600489 r601212) (join_sums term (lo:=601935) (a:=723) (b:=723) r601935 r602658)) (join_sums term (lo:=603381) (a:=1446) (b:=1446) (join_sums term (lo:=603381) (a:=723) (b:=723) r603381 r604104) (join_sums term (lo:=604827) (a:=723) (b:=723) r604827 r605550)))))) (join_sums term (lo:=606273) (a:=23136) (b:=23136) (join_sums term (lo:=606273) (a:=11568) (b:=11568) (join_sums term (lo:=606273) (a:=5784) (b:=5784) (join_sums term (lo:=606273) (a:=2892) (b:=2892) (join_sums term (lo:=606273) (a:=1446) (b:=1446) (join_sums term (lo:=606273) (a:=723) (b:=723) r606273 r606996) (join_sums term (lo:=607719) (a:=723) (b:=723) r607719 r608442)) (join_sums term (lo:=609165) (a:=1446) (b:=1446) (join_sums term (lo:=609165) (a:=723) (b:=723) r609165 r609888) (join_sums term (lo:=610611) (a:=723) (b:=723) r610611 r611334))) (join_sums term (lo:=612057) (a:=2892) (b:=2892) (join_sums term (lo:=612057) (a:=1446) (b:=1446) (join_sums term (lo:=612057) (a:=723) (b:=723) r612057 r612780) (join_sums term (lo:=613503) (a:=723) (b:=723) r613503 r614226)) (join_sums term (lo:=614949) (a:=1446) (b:=1446) (join_sums term (lo:=614949) (a:=723) (b:=723) r614949 r615672) (join_sums term (lo:=616395) (a:=723) (b:=723) r616395 r617118)))) (join_sums term (lo:=617841) (a:=5784) (b:=5784) (join_sums term (lo:=617841) (a:=2892) (b:=2892) (join_sums term (lo:=617841) (a:=1446) (b:=1446) (join_sums term (lo:=617841) (a:=723) (b:=723) r617841 r618564) (join_sums term (lo:=619287) (a:=723) (b:=723) r619287 r620010)) (join_sums term (lo:=620733) (a:=1446) (b:=1446) (join_sums term (lo:=620733) (a:=723) (b:=723) r620733 r621456) (join_sums term (lo:=622179) (a:=723) (b:=723) r622179 r622902))) (join_sums term (lo:=623625) (a:=2892) (b:=2892) (join_sums term (lo:=623625) (a:=1446) (b:=1446) (join_sums term (lo:=623625) (a:=723) (b:=723) r623625 r624348) (join_sums term (lo:=625071) (a:=723) (b:=723) r625071 r625794)) (join_sums term (lo:=626517) (a:=1446) (b:=1446) (join_sums term (lo:=626517) (a:=723) (b:=723) r626517 r627240) (join_sums term (lo:=627963) (a:=723) (b:=723) r627963 r628686))))) (join_sums term (lo:=629409) (a:=11568) (b:=11568) (join_sums term (lo:=629409) (a:=5784) (b:=5784) (join_sums term (lo:=629409) (a:=2892) (b:=2892) (join_sums term (lo:=629409) (a:=1446) (b:=1446) (join_sums term (lo:=629409) (a:=723) (b:=723) r629409 r630132) (join_sums term (lo:=630855) (a:=723) (b:=723) r630855 r631578)) (join_sums term (lo:=632301) (a:=1446) (b:=1446) (join_sums term (lo:=632301) (a:=723) (b:=723) r632301 r633024) (join_sums term (lo:=633747) (a:=723) (b:=723) r633747 r634470))) (join_sums term (lo:=635193) (a:=2892) (b:=2892) (join_sums term (lo:=635193) (a:=1446) (b:=1446) (join_sums term (lo:=635193) (a:=723) (b:=723) r635193 r635916) (join_sums term (lo:=636639) (a:=723) (b:=723) r636639 r637362)) (join_sums term (lo:=638085) (a:=1446) (b:=1446) (join_sums term (lo:=638085) (a:=723) (b:=723) r638085 r638808) (join_sums term (lo:=639531) (a:=723) (b:=723) r639531 r640254)))) (join_sums term (lo:=640977) (a:=5784) (b:=5784) (join_sums term (lo:=640977) (a:=2892) (b:=2892) (join_sums term (lo:=640977) (a:=1446) (b:=1446) (join_sums term (lo:=640977) (a:=723) (b:=723) r640977 r641700) (join_sums term (lo:=642423) (a:=723) (b:=723) r642423 r643146)) (join_sums term (lo:=643869) (a:=1446) (b:=1446) (join_sums term (lo:=643869) (a:=723) (b:=723) r643869 r644592) (join_sums term (lo:=645315) (a:=723) (b:=723) r645315 r646038))) (join_sums term (lo:=646761) (a:=2892) (b:=2892) (join_sums term (lo:=646761) (a:=1446) (b:=1446) (join_sums term (lo:=646761) (a:=723) (b:=723) r646761 r647484) (join_sums term (lo:=648207) (a:=723) (b:=723) r648207 r648930)) (join_sums term (lo:=649653) (a:=1446) (b:=1446) (join_sums term (lo:=649653) (a:=723) (b:=723) r649653 r650376) (join_sums term (lo:=651099) (a:=723) (b:=723) r651099 r651822))))))) (join_sums term (lo:=652545) (a:=46272) (b:=46273) (join_sums term (lo:=652545) (a:=23136) (b:=23136) (join_sums term (lo:=652545) (a:=11568) (b:=11568) (join_sums term (lo:=652545) (a:=5784) (b:=5784) (join_sums term (lo:=652545) (a:=2892) (b:=2892) (join_sums term (lo:=652545) (a:=1446) (b:=1446) (join_sums term (lo:=652545) (a:=723) (b:=723) r652545 r653268) (join_sums term (lo:=653991) (a:=723) (b:=723) r653991 r654714)) (join_sums term (lo:=655437) (a:=1446) (b:=1446) (join_sums term (lo:=655437) (a:=723) (b:=723) r655437 r656160) (join_sums term (lo:=656883) (a:=723) (b:=723) r656883 r657606))) (join_sums term (lo:=658329) (a:=2892) (b:=2892) (join_sums term (lo:=658329) (a:=1446) (b:=1446) (join_sums term (lo:=658329) (a:=723) (b:=723) r658329 r659052) (join_sums term (lo:=659775) (a:=723) (b:=723) r659775 r660498)) (join_sums term (lo:=661221) (a:=1446) (b:=1446) (join_sums term (lo:=661221) (a:=723) (b:=723) r661221 r661944) (join_sums term (lo:=662667) (a:=723) (b:=723) r662667 r663390)))) (join_sums term (lo:=664113) (a:=5784) (b:=5784) (join_sums term (lo:=664113) (a:=2892) (b:=2892) (join_sums term (lo:=664113) (a:=1446) (b:=1446) (join_sums term (lo:=664113) (a:=723) (b:=723) r664113 r664836) (join_sums term (lo:=665559) (a:=723) (b:=723) r665559 r666282)) (join_sums term (lo:=667005) (a:=1446) (b:=1446) (join_sums term (lo:=667005) (a:=723) (b:=723) r667005 r667728) (join_sums term (lo:=668451) (a:=723) (b:=723) r668451 r669174))) (join_sums term (lo:=669897) (a:=2892) (b:=2892) (join_sums term (lo:=669897) (a:=1446) (b:=1446) (join_sums term (lo:=669897) (a:=723) (b:=723) r669897 r670620) (join_sums term (lo:=671343) (a:=723) (b:=723) r671343 r672066)) (join_sums term (lo:=672789) (a:=1446) (b:=1446) (join_sums term (lo:=672789) (a:=723) (b:=723) r672789 r673512) (join_sums term (lo:=674235) (a:=723) (b:=723) r674235 r674958))))) (join_sums term (lo:=675681) (a:=11568) (b:=11568) (join_sums term (lo:=675681) (a:=5784) (b:=5784) (join_sums term (lo:=675681) (a:=2892) (b:=2892) (join_sums term (lo:=675681) (a:=1446) (b:=1446) (join_sums term (lo:=675681) (a:=723) (b:=723) r675681 r676404) (join_sums term (lo:=677127) (a:=723) (b:=723) r677127 r677850)) (join_sums term (lo:=678573) (a:=1446) (b:=1446) (join_sums term (lo:=678573) (a:=723) (b:=723) r678573 r679296) (join_sums term (lo:=680019) (a:=723) (b:=723) r680019 r680742))) (join_sums term (lo:=681465) (a:=2892) (b:=2892) (join_sums term (lo:=681465) (a:=1446) (b:=1446) (join_sums term (lo:=681465) (a:=723) (b:=723) r681465 r682188) (join_sums term (lo:=682911) (a:=723) (b:=723) r682911 r683634)) (join_sums term (lo:=684357) (a:=1446) (b:=1446) (join_sums term (lo:=684357) (a:=723) (b:=723) r684357 r685080) (join_sums term (lo:=685803) (a:=723) (b:=723) r685803 r686526)))) (join_sums term (lo:=687249) (a:=5784) (b:=5784) (join_sums term (lo:=687249) (a:=2892) (b:=2892) (join_sums term (lo:=687249) (a:=1446) (b:=1446) (join_sums term (lo:=687249) (a:=723) (b:=723) r687249 r687972) (join_sums term (lo:=688695) (a:=723) (b:=723) r688695 r689418)) (join_sums term (lo:=690141) (a:=1446) (b:=1446) (join_sums term (lo:=690141) (a:=723) (b:=723) r690141 r690864) (join_sums term (lo:=691587) (a:=723) (b:=723) r691587 r692310))) (join_sums term (lo:=693033) (a:=2892) (b:=2892) (join_sums term (lo:=693033) (a:=1446) (b:=1446) (join_sums term (lo:=693033) (a:=723) (b:=723) r693033 r693756) (join_sums term (lo:=694479) (a:=723) (b:=723) r694479 r695202)) (join_sums term (lo:=695925) (a:=1446) (b:=1446) (join_sums term (lo:=695925) (a:=723) (b:=723) r695925 r696648) (join_sums term (lo:=697371) (a:=723) (b:=723) r697371 r698094)))))) (join_sums term (lo:=698817) (a:=23136) (b:=23137) (join_sums term (lo:=698817) (a:=11568) (b:=11568) (join_sums term (lo:=698817) (a:=5784) (b:=5784) (join_sums term (lo:=698817) (a:=2892) (b:=2892) (join_sums term (lo:=698817) (a:=1446) (b:=1446) (join_sums term (lo:=698817) (a:=723) (b:=723) r698817 r699540) (join_sums term (lo:=700263) (a:=723) (b:=723) r700263 r700986)) (join_sums term (lo:=701709) (a:=1446) (b:=1446) (join_sums term (lo:=701709) (a:=723) (b:=723) r701709 r702432) (join_sums term (lo:=703155) (a:=723) (b:=723) r703155 r703878))) (join_sums term (lo:=704601) (a:=2892) (b:=2892) (join_sums term (lo:=704601) (a:=1446) (b:=1446) (join_sums term (lo:=704601) (a:=723) (b:=723) r704601 r705324) (join_sums term (lo:=706047) (a:=723) (b:=723) r706047 r706770)) (join_sums term (lo:=707493) (a:=1446) (b:=1446) (join_sums term (lo:=707493) (a:=723) (b:=723) r707493 r708216) (join_sums term (lo:=708939) (a:=723) (b:=723) r708939 r709662)))) (join_sums term (lo:=710385) (a:=5784) (b:=5784) (join_sums term (lo:=710385) (a:=2892) (b:=2892) (join_sums term (lo:=710385) (a:=1446) (b:=1446) (join_sums term (lo:=710385) (a:=723) (b:=723) r710385 r711108) (join_sums term (lo:=711831) (a:=723) (b:=723) r711831 r712554)) (join_sums term (lo:=713277) (a:=1446) (b:=1446) (join_sums term (lo:=713277) (a:=723) (b:=723) r713277 r714000) (join_sums term (lo:=714723) (a:=723) (b:=723) r714723 r715446))) (join_sums term (lo:=716169) (a:=2892) (b:=2892) (join_sums term (lo:=716169) (a:=1446) (b:=1446) (join_sums term (lo:=716169) (a:=723) (b:=723) r716169 r716892) (join_sums term (lo:=717615) (a:=723) (b:=723) r717615 r718338)) (join_sums term (lo:=719061) (a:=1446) (b:=1446) (join_sums term (lo:=719061) (a:=723) (b:=723) r719061 r719784) (join_sums term (lo:=720507) (a:=723) (b:=723) r720507 r721230))))) (join_sums term (lo:=721953) (a:=11568) (b:=11569) (join_sums term (lo:=721953) (a:=5784) (b:=5784) (join_sums term (lo:=721953) (a:=2892) (b:=2892) (join_sums term (lo:=721953) (a:=1446) (b:=1446) (join_sums term (lo:=721953) (a:=723) (b:=723) r721953 r722676) (join_sums term (lo:=723399) (a:=723) (b:=723) r723399 r724122)) (join_sums term (lo:=724845) (a:=1446) (b:=1446) (join_sums term (lo:=724845) (a:=723) (b:=723) r724845 r725568) (join_sums term (lo:=726291) (a:=723) (b:=723) r726291 r727014))) (join_sums term (lo:=727737) (a:=2892) (b:=2892) (join_sums term (lo:=727737) (a:=1446) (b:=1446) (join_sums term (lo:=727737) (a:=723) (b:=723) r727737 r728460) (join_sums term (lo:=729183) (a:=723) (b:=723) r729183 r729906)) (join_sums term (lo:=730629) (a:=1446) (b:=1446) (join_sums term (lo:=730629) (a:=723) (b:=723) r730629 r731352) (join_sums term (lo:=732075) (a:=723) (b:=723) r732075 r732798)))) (join_sums term (lo:=733521) (a:=5784) (b:=5785) (join_sums term (lo:=733521) (a:=2892) (b:=2892) (join_sums term (lo:=733521) (a:=1446) (b:=1446) (join_sums term (lo:=733521) (a:=723) (b:=723) r733521 r734244) (join_sums term (lo:=734967) (a:=723) (b:=723) r734967 r735690)) (join_sums term (lo:=736413) (a:=1446) (b:=1446) (join_sums term (lo:=736413) (a:=723) (b:=723) r736413 r737136) (join_sums term (lo:=737859) (a:=723) (b:=723) r737859 r738582))) (join_sums term (lo:=739305) (a:=2892) (b:=2893) (join_sums term (lo:=739305) (a:=1446) (b:=1446) (join_sums term (lo:=739305) (a:=723) (b:=723) r739305 r740028) (join_sums term (lo:=740751) (a:=723) (b:=723) r740751 r741474)) (join_sums term (lo:=742197) (a:=1446) (b:=1447) (join_sums term (lo:=742197) (a:=723) (b:=723) r742197 r742920) (join_sums term (lo:=743643) (a:=723) (b:=724) r743643 r744366))))))))

private theorem rows : blockSum term 0 745090 14441249620 :=
  join_sums term (lo:=0) (a:=560001) (b:=185089) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 745089).filter (560000 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=14441249620 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=745089)
    SparsePrimeA204.fast FastDenseA26.fast FastDenseA26.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From560000To745089
