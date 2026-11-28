import certificates.«semiprime-correction-555157672301-small»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 610,000 through 690,000

The sum covers 5,954 primes. Their quotient counts are checked by the
certified prime-counting table through 67,545,646.
-/
open Finset
namespace Correction30110134441897From610000To690000

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


private abbrev term := contribution 30110134441897 610000 RangePrimeA26.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 610001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 610000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r610001 : blockSum term 610001 625 110711008 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r610626 : blockSum term 610626 625 148456170 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r611251 : blockSum term 611251 625 122130565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r611876 : blockSum term 611876 625 156874002 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r612501 : blockSum term 612501 625 121885292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r613126 : blockSum term 613126 625 156558623 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r613751 : blockSum term 613751 625 118750669 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r614376 : blockSum term 614376 625 138886456 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r615001 : blockSum term 615001 625 135852196 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r615626 : blockSum term 615626 625 147270472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r616251 : blockSum term 616251 625 150014128 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r616876 : blockSum term 616876 625 152744379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r617501 : blockSum term 617501 625 129566732 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r618126 : blockSum term 618126 625 126562938 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r618751 : blockSum term 618751 625 132181471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r619376 : blockSum term 619376 625 123437198 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r620001 : blockSum term 620001 625 137660036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r620626 : blockSum term 620626 625 134665514 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r621251 : blockSum term 621251 625 125943226 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r621876 : blockSum term 621876 625 131542941 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r622501 : blockSum term 622501 625 128559920 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r623126 : blockSum term 623126 625 131275980 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r623751 : blockSum term 623751 625 142558554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r624376 : blockSum term 624376 625 136727800 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r625001 : blockSum term 625001 625 119521186 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r625626 : blockSum term 625626 625 122248672 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r626251 : blockSum term 626251 625 127804392 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r626876 : blockSum term 626876 625 127686968 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r627501 : blockSum term 627501 625 121894310 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r628126 : blockSum term 628126 625 116118207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r628751 : blockSum term 628751 625 121667422 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r629376 : blockSum term 629376 625 149802858 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r630001 : blockSum term 630001 625 118596307 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r630626 : blockSum term 630626 625 118483465 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r631251 : blockSum term 631251 625 149371357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r631876 : blockSum term 631876 625 146415488 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r632501 : blockSum term 632501 625 120960789 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r633126 : blockSum term 633126 625 118036945 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r633751 : blockSum term 633751 625 151608344 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r634376 : blockSum term 634376 625 137437388 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r635001 : blockSum term 635001 625 134503226 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r635626 : blockSum term 635626 625 131578365 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r636251 : blockSum term 636251 625 131453956 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r636876 : blockSum term 636876 625 131321630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r637501 : blockSum term 637501 625 122833054 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r638126 : blockSum term 638126 625 103189088 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r638751 : blockSum term 638751 625 114228370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r639376 : blockSum term 639376 625 125259256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r640001 : blockSum term 640001 625 130712054 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r640626 : blockSum term 640626 625 127802590 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r641251 : blockSum term 641251 625 127676577 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r641876 : blockSum term 641876 625 113699059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r642501 : blockSum term 642501 625 132974497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r643126 : blockSum term 643126 625 116240937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r643751 : blockSum term 643751 625 132723310 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r644376 : blockSum term 644376 625 149179773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r645001 : blockSum term 645001 625 126956630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r645626 : blockSum term 645626 625 129597394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r646251 : blockSum term 646251 625 118456257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r646876 : blockSum term 646876 625 140362706 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r647501 : blockSum term 647501 625 148473290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r648126 : blockSum term 648126 625 118120726 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r648751 : blockSum term 648751 625 118008093 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r649376 : blockSum term 649376 625 159025780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r650001 : blockSum term 650001 625 106822890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r650626 : blockSum term 650626 625 117668862 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r651251 : blockSum term 651251 625 125765491 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r651876 : blockSum term 651876 625 125645672 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r652501 : blockSum term 652501 625 141912373 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r653126 : blockSum term 653126 625 117232371 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r653751 : blockSum term 653751 625 138921703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r654376 : blockSum term 654376 625 127905756 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r655001 : blockSum term 655001 625 135946060 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r655626 : blockSum term 655626 625 97792062 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r656251 : blockSum term 656251 625 132980163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r656876 : blockSum term 656876 625 130138050 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r657501 : blockSum term 657501 625 108352108 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r658126 : blockSum term 658126 625 129906433 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r658751 : blockSum term 658751 625 127080940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r659376 : blockSum term 659376 625 129660676 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r660001 : blockSum term 660001 625 145733168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r660626 : blockSum term 660626 625 134811678 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r661251 : blockSum term 661251 625 96978823 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r661876 : blockSum term 661876 625 131878295 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r662501 : blockSum term 662501 625 123685462 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r663126 : blockSum term 663126 625 126256819 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r663751 : blockSum term 663751 625 131509748 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r664376 : blockSum term 664376 625 134070415 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r665001 : blockSum term 665001 625 139302959 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r665626 : blockSum term 665626 625 123108835 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r666251 : blockSum term 666251 625 117645500 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r666876 : blockSum term 666876 625 112199284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r667501 : blockSum term 667501 625 130786254 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r668126 : blockSum term 668126 625 103989315 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r668751 : blockSum term 668751 625 114557524 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r669376 : blockSum term 669376 625 130423182 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r670001 : blockSum term 670001 625 130302385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r670626 : blockSum term 670626 625 119557563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r671251 : blockSum term 671251 625 114145080 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r671876 : blockSum term 671876 625 143218348 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r672501 : blockSum term 672501 625 124525426 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r673126 : blockSum term 673126 625 132361951 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r673751 : blockSum term 673751 625 113723587 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r674376 : blockSum term 674376 625 121545183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r675001 : blockSum term 675001 625 131996526 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r675626 : blockSum term 675626 625 116050515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r676251 : blockSum term 676251 625 105409982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r676876 : blockSum term 676876 625 129015658 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r677501 : blockSum term 677501 625 94698590 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r678126 : blockSum term 678126 625 141913731 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r678751 : blockSum term 678751 625 131286800 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r679376 : blockSum term 679376 625 141656636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r680001 : blockSum term 680001 625 133667708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r680626 : blockSum term 680626 625 109981330 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r681251 : blockSum term 681251 625 128201309 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r681876 : blockSum term 681876 625 130694114 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r682501 : blockSum term 682501 625 91407641 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r683126 : blockSum term 683126 625 122633250 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r683751 : blockSum term 683751 625 127744621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r684376 : blockSum term 684376 625 119814225 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r685001 : blockSum term 685001 625 127511640 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r685626 : blockSum term 685626 625 122196400 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r686251 : blockSum term 686251 625 103906535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r686876 : blockSum term 686876 625 150528588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r687501 : blockSum term 687501 625 119279270 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r688126 : blockSum term 688126 625 121760405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r688751 : blockSum term 688751 625 119065242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r689376 : blockSum term 689376 625 129301603 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 610001 80000 16332617699 := (join_sums term (lo:=610001) (a:=40000) (b:=40000) (join_sums term (lo:=610001) (a:=20000) (b:=20000) (join_sums term (lo:=610001) (a:=10000) (b:=10000) (join_sums term (lo:=610001) (a:=5000) (b:=5000) (join_sums term (lo:=610001) (a:=2500) (b:=2500) (join_sums term (lo:=610001) (a:=1250) (b:=1250) (join_sums term (lo:=610001) (a:=625) (b:=625) r610001 r610626) (join_sums term (lo:=611251) (a:=625) (b:=625) r611251 r611876)) (join_sums term (lo:=612501) (a:=1250) (b:=1250) (join_sums term (lo:=612501) (a:=625) (b:=625) r612501 r613126) (join_sums term (lo:=613751) (a:=625) (b:=625) r613751 r614376))) (join_sums term (lo:=615001) (a:=2500) (b:=2500) (join_sums term (lo:=615001) (a:=1250) (b:=1250) (join_sums term (lo:=615001) (a:=625) (b:=625) r615001 r615626) (join_sums term (lo:=616251) (a:=625) (b:=625) r616251 r616876)) (join_sums term (lo:=617501) (a:=1250) (b:=1250) (join_sums term (lo:=617501) (a:=625) (b:=625) r617501 r618126) (join_sums term (lo:=618751) (a:=625) (b:=625) r618751 r619376)))) (join_sums term (lo:=620001) (a:=5000) (b:=5000) (join_sums term (lo:=620001) (a:=2500) (b:=2500) (join_sums term (lo:=620001) (a:=1250) (b:=1250) (join_sums term (lo:=620001) (a:=625) (b:=625) r620001 r620626) (join_sums term (lo:=621251) (a:=625) (b:=625) r621251 r621876)) (join_sums term (lo:=622501) (a:=1250) (b:=1250) (join_sums term (lo:=622501) (a:=625) (b:=625) r622501 r623126) (join_sums term (lo:=623751) (a:=625) (b:=625) r623751 r624376))) (join_sums term (lo:=625001) (a:=2500) (b:=2500) (join_sums term (lo:=625001) (a:=1250) (b:=1250) (join_sums term (lo:=625001) (a:=625) (b:=625) r625001 r625626) (join_sums term (lo:=626251) (a:=625) (b:=625) r626251 r626876)) (join_sums term (lo:=627501) (a:=1250) (b:=1250) (join_sums term (lo:=627501) (a:=625) (b:=625) r627501 r628126) (join_sums term (lo:=628751) (a:=625) (b:=625) r628751 r629376))))) (join_sums term (lo:=630001) (a:=10000) (b:=10000) (join_sums term (lo:=630001) (a:=5000) (b:=5000) (join_sums term (lo:=630001) (a:=2500) (b:=2500) (join_sums term (lo:=630001) (a:=1250) (b:=1250) (join_sums term (lo:=630001) (a:=625) (b:=625) r630001 r630626) (join_sums term (lo:=631251) (a:=625) (b:=625) r631251 r631876)) (join_sums term (lo:=632501) (a:=1250) (b:=1250) (join_sums term (lo:=632501) (a:=625) (b:=625) r632501 r633126) (join_sums term (lo:=633751) (a:=625) (b:=625) r633751 r634376))) (join_sums term (lo:=635001) (a:=2500) (b:=2500) (join_sums term (lo:=635001) (a:=1250) (b:=1250) (join_sums term (lo:=635001) (a:=625) (b:=625) r635001 r635626) (join_sums term (lo:=636251) (a:=625) (b:=625) r636251 r636876)) (join_sums term (lo:=637501) (a:=1250) (b:=1250) (join_sums term (lo:=637501) (a:=625) (b:=625) r637501 r638126) (join_sums term (lo:=638751) (a:=625) (b:=625) r638751 r639376)))) (join_sums term (lo:=640001) (a:=5000) (b:=5000) (join_sums term (lo:=640001) (a:=2500) (b:=2500) (join_sums term (lo:=640001) (a:=1250) (b:=1250) (join_sums term (lo:=640001) (a:=625) (b:=625) r640001 r640626) (join_sums term (lo:=641251) (a:=625) (b:=625) r641251 r641876)) (join_sums term (lo:=642501) (a:=1250) (b:=1250) (join_sums term (lo:=642501) (a:=625) (b:=625) r642501 r643126) (join_sums term (lo:=643751) (a:=625) (b:=625) r643751 r644376))) (join_sums term (lo:=645001) (a:=2500) (b:=2500) (join_sums term (lo:=645001) (a:=1250) (b:=1250) (join_sums term (lo:=645001) (a:=625) (b:=625) r645001 r645626) (join_sums term (lo:=646251) (a:=625) (b:=625) r646251 r646876)) (join_sums term (lo:=647501) (a:=1250) (b:=1250) (join_sums term (lo:=647501) (a:=625) (b:=625) r647501 r648126) (join_sums term (lo:=648751) (a:=625) (b:=625) r648751 r649376)))))) (join_sums term (lo:=650001) (a:=20000) (b:=20000) (join_sums term (lo:=650001) (a:=10000) (b:=10000) (join_sums term (lo:=650001) (a:=5000) (b:=5000) (join_sums term (lo:=650001) (a:=2500) (b:=2500) (join_sums term (lo:=650001) (a:=1250) (b:=1250) (join_sums term (lo:=650001) (a:=625) (b:=625) r650001 r650626) (join_sums term (lo:=651251) (a:=625) (b:=625) r651251 r651876)) (join_sums term (lo:=652501) (a:=1250) (b:=1250) (join_sums term (lo:=652501) (a:=625) (b:=625) r652501 r653126) (join_sums term (lo:=653751) (a:=625) (b:=625) r653751 r654376))) (join_sums term (lo:=655001) (a:=2500) (b:=2500) (join_sums term (lo:=655001) (a:=1250) (b:=1250) (join_sums term (lo:=655001) (a:=625) (b:=625) r655001 r655626) (join_sums term (lo:=656251) (a:=625) (b:=625) r656251 r656876)) (join_sums term (lo:=657501) (a:=1250) (b:=1250) (join_sums term (lo:=657501) (a:=625) (b:=625) r657501 r658126) (join_sums term (lo:=658751) (a:=625) (b:=625) r658751 r659376)))) (join_sums term (lo:=660001) (a:=5000) (b:=5000) (join_sums term (lo:=660001) (a:=2500) (b:=2500) (join_sums term (lo:=660001) (a:=1250) (b:=1250) (join_sums term (lo:=660001) (a:=625) (b:=625) r660001 r660626) (join_sums term (lo:=661251) (a:=625) (b:=625) r661251 r661876)) (join_sums term (lo:=662501) (a:=1250) (b:=1250) (join_sums term (lo:=662501) (a:=625) (b:=625) r662501 r663126) (join_sums term (lo:=663751) (a:=625) (b:=625) r663751 r664376))) (join_sums term (lo:=665001) (a:=2500) (b:=2500) (join_sums term (lo:=665001) (a:=1250) (b:=1250) (join_sums term (lo:=665001) (a:=625) (b:=625) r665001 r665626) (join_sums term (lo:=666251) (a:=625) (b:=625) r666251 r666876)) (join_sums term (lo:=667501) (a:=1250) (b:=1250) (join_sums term (lo:=667501) (a:=625) (b:=625) r667501 r668126) (join_sums term (lo:=668751) (a:=625) (b:=625) r668751 r669376))))) (join_sums term (lo:=670001) (a:=10000) (b:=10000) (join_sums term (lo:=670001) (a:=5000) (b:=5000) (join_sums term (lo:=670001) (a:=2500) (b:=2500) (join_sums term (lo:=670001) (a:=1250) (b:=1250) (join_sums term (lo:=670001) (a:=625) (b:=625) r670001 r670626) (join_sums term (lo:=671251) (a:=625) (b:=625) r671251 r671876)) (join_sums term (lo:=672501) (a:=1250) (b:=1250) (join_sums term (lo:=672501) (a:=625) (b:=625) r672501 r673126) (join_sums term (lo:=673751) (a:=625) (b:=625) r673751 r674376))) (join_sums term (lo:=675001) (a:=2500) (b:=2500) (join_sums term (lo:=675001) (a:=1250) (b:=1250) (join_sums term (lo:=675001) (a:=625) (b:=625) r675001 r675626) (join_sums term (lo:=676251) (a:=625) (b:=625) r676251 r676876)) (join_sums term (lo:=677501) (a:=1250) (b:=1250) (join_sums term (lo:=677501) (a:=625) (b:=625) r677501 r678126) (join_sums term (lo:=678751) (a:=625) (b:=625) r678751 r679376)))) (join_sums term (lo:=680001) (a:=5000) (b:=5000) (join_sums term (lo:=680001) (a:=2500) (b:=2500) (join_sums term (lo:=680001) (a:=1250) (b:=1250) (join_sums term (lo:=680001) (a:=625) (b:=625) r680001 r680626) (join_sums term (lo:=681251) (a:=625) (b:=625) r681251 r681876)) (join_sums term (lo:=682501) (a:=1250) (b:=1250) (join_sums term (lo:=682501) (a:=625) (b:=625) r682501 r683126) (join_sums term (lo:=683751) (a:=625) (b:=625) r683751 r684376))) (join_sums term (lo:=685001) (a:=2500) (b:=2500) (join_sums term (lo:=685001) (a:=1250) (b:=1250) (join_sums term (lo:=685001) (a:=625) (b:=625) r685001 r685626) (join_sums term (lo:=686251) (a:=625) (b:=625) r686251 r686876)) (join_sums term (lo:=687501) (a:=1250) (b:=1250) (join_sums term (lo:=687501) (a:=625) (b:=625) r687501 r688126) (join_sums term (lo:=688751) (a:=625) (b:=625) r688751 r689376)))))))

private theorem rows : blockSum term 0 690001 16332617699 :=
  join_sums term (lo:=0) (a:=610001) (b:=80000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 690000).filter (610000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=16332617699 :=
  right_from_blocks (l:=34751024) (b:=67545646) (small:=745089)
    RangePrimeA26.fast FastDenseA26.fast FastDenseA26.prime (RangePrimeA26.fast_correct RankWheel34751.first_anchor)
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From610000To690000
