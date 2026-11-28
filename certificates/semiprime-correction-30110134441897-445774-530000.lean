import certificates.«semiprime-correction-555157672301-small»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 445,774 through 530,000

The sum covers 6,425 primes. Their quotient counts are checked by the
certified prime-counting table through 67,545,646.
-/
open Finset
namespace Correction30110134441897From445774To530000

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


private abbrev term := contribution 30110134441897 445774 RangePrimeA26.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 445775 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 445774 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r445775 : blockSum term 445775 658 185265806 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r446433 : blockSum term 446433 658 165324373 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r447091 : blockSum term 447091 658 184756004 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r447749 : blockSum term 447749 658 208036797 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r448407 : blockSum term 448407 658 156772224 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r449065 : blockSum term 449065 658 223115531 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r449723 : blockSum term 449723 658 214967861 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r450381 : blockSum term 450381 658 226390637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r451039 : blockSum term 451039 658 190987913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r451697 : blockSum term 451697 658 190736258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r452355 : blockSum term 452355 658 155481610 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r453013 : blockSum term 453013 658 186311475 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r453671 : blockSum term 453671 658 189926002 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r454329 : blockSum term 454329 658 185789102 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r454987 : blockSum term 454987 658 212583547 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r455645 : blockSum term 455645 658 181424374 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r456303 : blockSum term 456303 658 200436505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r456961 : blockSum term 456961 658 204011101 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r457619 : blockSum term 457619 658 169138371 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r458277 : blockSum term 458277 658 184249630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r458935 : blockSum term 458935 658 195520490 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r459593 : blockSum term 459593 658 179921330 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r460251 : blockSum term 460251 658 172021450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r460909 : blockSum term 460909 658 198527042 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r461567 : blockSum term 461567 658 163933415 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r462225 : blockSum term 462225 658 194165244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r462883 : blockSum term 462883 658 186284222 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r463541 : blockSum term 463541 658 201224097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r464199 : blockSum term 464199 658 200956662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r464857 : blockSum term 464857 658 212067917 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r465515 : blockSum term 465515 658 181505323 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r466173 : blockSum term 466173 658 169938372 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r466831 : blockSum term 466831 658 169702386 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r467489 : blockSum term 467489 658 233511653 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r468147 : blockSum term 468147 658 203091790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r468805 : blockSum term 468805 658 184047402 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r469463 : blockSum term 469463 658 176294926 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r470121 : blockSum term 470121 658 221020455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r470779 : blockSum term 470779 658 187056035 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r471437 : blockSum term 471437 658 201746620 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r472095 : blockSum term 472095 658 190277179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r472753 : blockSum term 472753 658 167659673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r473411 : blockSum term 473411 658 204650676 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r474069 : blockSum term 474069 658 189514285 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r474727 : blockSum term 474727 658 200385577 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r475385 : blockSum term 475385 658 226056275 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r476043 : blockSum term 476043 658 173950147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r476701 : blockSum term 476701 658 162641850 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r477359 : blockSum term 477359 658 177180907 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r478017 : blockSum term 478017 658 191695662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r478675 : blockSum term 478675 658 206174444 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r479333 : blockSum term 479333 658 172802997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r479991 : blockSum term 479991 658 198282617 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r480649 : blockSum term 480649 658 190674361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r481307 : blockSum term 481307 658 175784398 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r481965 : blockSum term 481965 658 182869936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r482623 : blockSum term 482623 658 186300814 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r483281 : blockSum term 483281 658 196983475 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r483939 : blockSum term 483939 658 163945571 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r484597 : blockSum term 484597 658 149177216 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r485255 : blockSum term 485255 658 145344530 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r485913 : blockSum term 485913 658 188696393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r486571 : blockSum term 486571 658 192086509 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r487229 : blockSum term 487229 659 188208356 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r487888 : blockSum term 487888 658 198812535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r488546 : blockSum term 488546 658 187729020 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r489204 : blockSum term 489204 658 180270167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r489862 : blockSum term 489862 658 183647833 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r490520 : blockSum term 490520 658 183409150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r491178 : blockSum term 491178 658 190353904 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r491836 : blockSum term 491836 658 157829930 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r492494 : blockSum term 492494 658 179116757 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r493152 : blockSum term 493152 658 178900797 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r493810 : blockSum term 493810 658 185813368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r494468 : blockSum term 494468 658 189148700 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r495126 : blockSum term 495126 658 210280669 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r495784 : blockSum term 495784 658 170865136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r496442 : blockSum term 496442 658 163528775 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r497100 : blockSum term 497100 658 195271415 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r497758 : blockSum term 497758 658 163112718 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r498416 : blockSum term 498416 658 180610817 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r499074 : blockSum term 499074 658 205133516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r499732 : blockSum term 499732 658 173080250 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r500390 : blockSum term 500390 658 190500065 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r501048 : blockSum term 501048 658 165610772 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r501706 : blockSum term 501706 658 154844116 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r502364 : blockSum term 502364 658 158161984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r503022 : blockSum term 503022 658 168485595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r503680 : blockSum term 503680 658 182299749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r504338 : blockSum term 504338 658 175064353 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r504996 : blockSum term 504996 658 202828726 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r505654 : blockSum term 505654 658 150189443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r506312 : blockSum term 506312 658 191858555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r506970 : blockSum term 506970 658 160262519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r507628 : blockSum term 507628 658 173979317 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r508286 : blockSum term 508286 658 166813482 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r508944 : blockSum term 508944 658 166605421 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r509602 : blockSum term 509602 658 197600413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r510260 : blockSum term 510260 658 148885867 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r510918 : blockSum term 510918 658 193653203 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r511576 : blockSum term 511576 658 145071984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r512234 : blockSum term 512234 658 169020785 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r512892 : blockSum term 512892 658 196386286 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r513550 : blockSum term 513550 658 168602012 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r514208 : blockSum term 514208 658 185577806 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r514866 : blockSum term 514866 658 123569622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r515524 : blockSum term 515524 658 174845301 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r516182 : blockSum term 516182 658 198601829 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r516840 : blockSum term 516840 658 194929406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r517498 : blockSum term 517498 658 181035784 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r518156 : blockSum term 518156 658 180803207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r518814 : blockSum term 518814 658 156730934 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r519472 : blockSum term 519472 658 180369579 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r520130 : blockSum term 520130 658 163147172 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r520788 : blockSum term 520788 658 169742766 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r521446 : blockSum term 521446 658 186500290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r522104 : blockSum term 522104 658 179493413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r522762 : blockSum term 522762 658 138694686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r523420 : blockSum term 523420 658 172311772 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r524078 : blockSum term 524078 658 158611703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r524736 : blockSum term 524736 658 185371653 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r525394 : blockSum term 525394 658 178413913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r526052 : blockSum term 526052 658 188278963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r526710 : blockSum term 526710 658 167911212 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r527368 : blockSum term 527368 658 160998346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r528026 : blockSum term 528026 658 150754021 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r528684 : blockSum term 528684 658 173994374 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r529342 : blockSum term 529342 659 163758731 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 445775 84226 23287672387 := (join_sums term (lo:=445775) (a:=42113) (b:=42113) (join_sums term (lo:=445775) (a:=21056) (b:=21057) (join_sums term (lo:=445775) (a:=10528) (b:=10528) (join_sums term (lo:=445775) (a:=5264) (b:=5264) (join_sums term (lo:=445775) (a:=2632) (b:=2632) (join_sums term (lo:=445775) (a:=1316) (b:=1316) (join_sums term (lo:=445775) (a:=658) (b:=658) r445775 r446433) (join_sums term (lo:=447091) (a:=658) (b:=658) r447091 r447749)) (join_sums term (lo:=448407) (a:=1316) (b:=1316) (join_sums term (lo:=448407) (a:=658) (b:=658) r448407 r449065) (join_sums term (lo:=449723) (a:=658) (b:=658) r449723 r450381))) (join_sums term (lo:=451039) (a:=2632) (b:=2632) (join_sums term (lo:=451039) (a:=1316) (b:=1316) (join_sums term (lo:=451039) (a:=658) (b:=658) r451039 r451697) (join_sums term (lo:=452355) (a:=658) (b:=658) r452355 r453013)) (join_sums term (lo:=453671) (a:=1316) (b:=1316) (join_sums term (lo:=453671) (a:=658) (b:=658) r453671 r454329) (join_sums term (lo:=454987) (a:=658) (b:=658) r454987 r455645)))) (join_sums term (lo:=456303) (a:=5264) (b:=5264) (join_sums term (lo:=456303) (a:=2632) (b:=2632) (join_sums term (lo:=456303) (a:=1316) (b:=1316) (join_sums term (lo:=456303) (a:=658) (b:=658) r456303 r456961) (join_sums term (lo:=457619) (a:=658) (b:=658) r457619 r458277)) (join_sums term (lo:=458935) (a:=1316) (b:=1316) (join_sums term (lo:=458935) (a:=658) (b:=658) r458935 r459593) (join_sums term (lo:=460251) (a:=658) (b:=658) r460251 r460909))) (join_sums term (lo:=461567) (a:=2632) (b:=2632) (join_sums term (lo:=461567) (a:=1316) (b:=1316) (join_sums term (lo:=461567) (a:=658) (b:=658) r461567 r462225) (join_sums term (lo:=462883) (a:=658) (b:=658) r462883 r463541)) (join_sums term (lo:=464199) (a:=1316) (b:=1316) (join_sums term (lo:=464199) (a:=658) (b:=658) r464199 r464857) (join_sums term (lo:=465515) (a:=658) (b:=658) r465515 r466173))))) (join_sums term (lo:=466831) (a:=10528) (b:=10529) (join_sums term (lo:=466831) (a:=5264) (b:=5264) (join_sums term (lo:=466831) (a:=2632) (b:=2632) (join_sums term (lo:=466831) (a:=1316) (b:=1316) (join_sums term (lo:=466831) (a:=658) (b:=658) r466831 r467489) (join_sums term (lo:=468147) (a:=658) (b:=658) r468147 r468805)) (join_sums term (lo:=469463) (a:=1316) (b:=1316) (join_sums term (lo:=469463) (a:=658) (b:=658) r469463 r470121) (join_sums term (lo:=470779) (a:=658) (b:=658) r470779 r471437))) (join_sums term (lo:=472095) (a:=2632) (b:=2632) (join_sums term (lo:=472095) (a:=1316) (b:=1316) (join_sums term (lo:=472095) (a:=658) (b:=658) r472095 r472753) (join_sums term (lo:=473411) (a:=658) (b:=658) r473411 r474069)) (join_sums term (lo:=474727) (a:=1316) (b:=1316) (join_sums term (lo:=474727) (a:=658) (b:=658) r474727 r475385) (join_sums term (lo:=476043) (a:=658) (b:=658) r476043 r476701)))) (join_sums term (lo:=477359) (a:=5264) (b:=5265) (join_sums term (lo:=477359) (a:=2632) (b:=2632) (join_sums term (lo:=477359) (a:=1316) (b:=1316) (join_sums term (lo:=477359) (a:=658) (b:=658) r477359 r478017) (join_sums term (lo:=478675) (a:=658) (b:=658) r478675 r479333)) (join_sums term (lo:=479991) (a:=1316) (b:=1316) (join_sums term (lo:=479991) (a:=658) (b:=658) r479991 r480649) (join_sums term (lo:=481307) (a:=658) (b:=658) r481307 r481965))) (join_sums term (lo:=482623) (a:=2632) (b:=2633) (join_sums term (lo:=482623) (a:=1316) (b:=1316) (join_sums term (lo:=482623) (a:=658) (b:=658) r482623 r483281) (join_sums term (lo:=483939) (a:=658) (b:=658) r483939 r484597)) (join_sums term (lo:=485255) (a:=1316) (b:=1317) (join_sums term (lo:=485255) (a:=658) (b:=658) r485255 r485913) (join_sums term (lo:=486571) (a:=658) (b:=659) r486571 r487229)))))) (join_sums term (lo:=487888) (a:=21056) (b:=21057) (join_sums term (lo:=487888) (a:=10528) (b:=10528) (join_sums term (lo:=487888) (a:=5264) (b:=5264) (join_sums term (lo:=487888) (a:=2632) (b:=2632) (join_sums term (lo:=487888) (a:=1316) (b:=1316) (join_sums term (lo:=487888) (a:=658) (b:=658) r487888 r488546) (join_sums term (lo:=489204) (a:=658) (b:=658) r489204 r489862)) (join_sums term (lo:=490520) (a:=1316) (b:=1316) (join_sums term (lo:=490520) (a:=658) (b:=658) r490520 r491178) (join_sums term (lo:=491836) (a:=658) (b:=658) r491836 r492494))) (join_sums term (lo:=493152) (a:=2632) (b:=2632) (join_sums term (lo:=493152) (a:=1316) (b:=1316) (join_sums term (lo:=493152) (a:=658) (b:=658) r493152 r493810) (join_sums term (lo:=494468) (a:=658) (b:=658) r494468 r495126)) (join_sums term (lo:=495784) (a:=1316) (b:=1316) (join_sums term (lo:=495784) (a:=658) (b:=658) r495784 r496442) (join_sums term (lo:=497100) (a:=658) (b:=658) r497100 r497758)))) (join_sums term (lo:=498416) (a:=5264) (b:=5264) (join_sums term (lo:=498416) (a:=2632) (b:=2632) (join_sums term (lo:=498416) (a:=1316) (b:=1316) (join_sums term (lo:=498416) (a:=658) (b:=658) r498416 r499074) (join_sums term (lo:=499732) (a:=658) (b:=658) r499732 r500390)) (join_sums term (lo:=501048) (a:=1316) (b:=1316) (join_sums term (lo:=501048) (a:=658) (b:=658) r501048 r501706) (join_sums term (lo:=502364) (a:=658) (b:=658) r502364 r503022))) (join_sums term (lo:=503680) (a:=2632) (b:=2632) (join_sums term (lo:=503680) (a:=1316) (b:=1316) (join_sums term (lo:=503680) (a:=658) (b:=658) r503680 r504338) (join_sums term (lo:=504996) (a:=658) (b:=658) r504996 r505654)) (join_sums term (lo:=506312) (a:=1316) (b:=1316) (join_sums term (lo:=506312) (a:=658) (b:=658) r506312 r506970) (join_sums term (lo:=507628) (a:=658) (b:=658) r507628 r508286))))) (join_sums term (lo:=508944) (a:=10528) (b:=10529) (join_sums term (lo:=508944) (a:=5264) (b:=5264) (join_sums term (lo:=508944) (a:=2632) (b:=2632) (join_sums term (lo:=508944) (a:=1316) (b:=1316) (join_sums term (lo:=508944) (a:=658) (b:=658) r508944 r509602) (join_sums term (lo:=510260) (a:=658) (b:=658) r510260 r510918)) (join_sums term (lo:=511576) (a:=1316) (b:=1316) (join_sums term (lo:=511576) (a:=658) (b:=658) r511576 r512234) (join_sums term (lo:=512892) (a:=658) (b:=658) r512892 r513550))) (join_sums term (lo:=514208) (a:=2632) (b:=2632) (join_sums term (lo:=514208) (a:=1316) (b:=1316) (join_sums term (lo:=514208) (a:=658) (b:=658) r514208 r514866) (join_sums term (lo:=515524) (a:=658) (b:=658) r515524 r516182)) (join_sums term (lo:=516840) (a:=1316) (b:=1316) (join_sums term (lo:=516840) (a:=658) (b:=658) r516840 r517498) (join_sums term (lo:=518156) (a:=658) (b:=658) r518156 r518814)))) (join_sums term (lo:=519472) (a:=5264) (b:=5265) (join_sums term (lo:=519472) (a:=2632) (b:=2632) (join_sums term (lo:=519472) (a:=1316) (b:=1316) (join_sums term (lo:=519472) (a:=658) (b:=658) r519472 r520130) (join_sums term (lo:=520788) (a:=658) (b:=658) r520788 r521446)) (join_sums term (lo:=522104) (a:=1316) (b:=1316) (join_sums term (lo:=522104) (a:=658) (b:=658) r522104 r522762) (join_sums term (lo:=523420) (a:=658) (b:=658) r523420 r524078))) (join_sums term (lo:=524736) (a:=2632) (b:=2633) (join_sums term (lo:=524736) (a:=1316) (b:=1316) (join_sums term (lo:=524736) (a:=658) (b:=658) r524736 r525394) (join_sums term (lo:=526052) (a:=658) (b:=658) r526052 r526710)) (join_sums term (lo:=527368) (a:=1316) (b:=1317) (join_sums term (lo:=527368) (a:=658) (b:=658) r527368 r528026) (join_sums term (lo:=528684) (a:=658) (b:=659) r528684 r529342)))))))

private theorem rows : blockSum term 0 530001 23287672387 :=
  join_sums term (lo:=0) (a:=445775) (b:=84226) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 530000).filter (445774 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=23287672387 :=
  right_from_blocks (l:=34751024) (b:=67545646) (small:=745089)
    RangePrimeA26.fast FastDenseA26.fast FastDenseA26.prime (RangePrimeA26.fast_correct RankWheel34751.first_anchor)
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From445774To530000
