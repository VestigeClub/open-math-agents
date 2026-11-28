import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 430,000 through 560,000

The sum covers 9,910 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction11092009835083From430000To560000

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


private abbrev term := contribution 11092009835083 430000 SparsePrimeA204.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 430001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 430000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r430001 : blockSum term 430001 507 47264571 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r430508 : blockSum term 430508 508 72384629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r431016 : blockSum term 431016 508 64444945 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r431524 : blockSum term 431524 508 65934850 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r432032 : blockSum term 432032 507 70567741 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r432539 : blockSum term 432539 508 57957131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r433047 : blockSum term 433047 508 70408405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r433555 : blockSum term 433555 508 57823504 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r434063 : blockSum term 434063 507 67121389 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r434570 : blockSum term 434570 508 63924307 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r435078 : blockSum term 435078 508 70081521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r435586 : blockSum term 435586 508 63779334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r436094 : blockSum term 436094 508 55935797 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r436602 : blockSum term 436602 508 55874973 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r437110 : blockSum term 437110 508 58912694 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r437618 : blockSum term 437618 508 49556896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r438126 : blockSum term 438126 507 61869713 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r438633 : blockSum term 438633 508 54077156 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r439141 : blockSum term 439141 508 58642990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r439649 : blockSum term 439649 508 60124910 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r440157 : blockSum term 440157 507 67755314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r440664 : blockSum term 440664 508 64600253 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r441172 : blockSum term 441172 508 55311358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r441680 : blockSum term 441680 508 61383622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r442188 : blockSum term 442188 507 56719996 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r442695 : blockSum term 442695 508 73497078 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r443203 : blockSum term 443203 508 65770758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r443711 : blockSum term 443711 508 68748646 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r444219 : blockSum term 444219 508 61039083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r444727 : blockSum term 444727 508 60973545 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r445235 : blockSum term 445235 508 50245613 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r445743 : blockSum term 445743 508 53233217 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r446251 : blockSum term 446251 507 51656865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r446758 : blockSum term 446758 508 60699373 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r447266 : blockSum term 447266 508 48507940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r447774 : blockSum term 447774 508 60569214 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r448282 : blockSum term 448282 507 43864058 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r448789 : blockSum term 448789 508 66476333 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r449297 : blockSum term 449297 508 61874206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r449805 : blockSum term 449805 508 66322014 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r450313 : blockSum term 450313 507 66251024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r450820 : blockSum term 450820 508 60166473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r451328 : blockSum term 451328 508 58592942 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r451836 : blockSum term 451836 508 57032035 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r452344 : blockSum term 452344 508 47970539 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r452852 : blockSum term 452852 508 52407422 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r453360 : blockSum term 453360 508 50856690 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r453868 : blockSum term 453868 508 59768285 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r454376 : blockSum term 454376 507 50747016 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r454883 : blockSum term 454883 508 61127300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r455391 : blockSum term 455391 508 62553298 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r455899 : blockSum term 455899 508 52070358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r456407 : blockSum term 456407 507 63899902 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r456914 : blockSum term 456914 508 65307924 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r457422 : blockSum term 457422 508 50412167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r457930 : blockSum term 457930 508 48875793 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r458438 : blockSum term 458438 507 54740281 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r458945 : blockSum term 458945 508 65028548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r459453 : blockSum term 459453 508 47240124 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r459961 : blockSum term 459961 508 54560894 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r460469 : blockSum term 460469 508 54499703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r460977 : blockSum term 460977 508 61801120 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r461485 : blockSum term 461485 508 45564540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r461993 : blockSum term 461993 508 52853906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r462501 : blockSum term 462501 507 57200802 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r463008 : blockSum term 463008 508 54203558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r463516 : blockSum term 463516 508 61465237 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r464024 : blockSum term 464024 508 57015205 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r464532 : blockSum term 464532 507 68632625 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r465039 : blockSum term 465039 508 58354332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r465547 : blockSum term 465547 508 51000853 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r466055 : blockSum term 466055 508 52405159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r466563 : blockSum term 466563 507 47986042 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r467070 : blockSum term 467070 508 58099515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r467578 : blockSum term 467578 508 68198280 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r468086 : blockSum term 468086 508 56529046 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r468594 : blockSum term 468594 508 60815968 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r469102 : blockSum term 469102 508 52069686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r469610 : blockSum term 469610 508 56348341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r470118 : blockSum term 470118 508 69275536 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r470626 : blockSum term 470626 507 54787367 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r471133 : blockSum term 471133 508 57608105 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r471641 : blockSum term 471641 508 61863414 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r472149 : blockSum term 472149 508 51738588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r472657 : blockSum term 472657 507 48812534 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r473164 : blockSum term 473164 508 63099405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r473672 : blockSum term 473672 508 58730949 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r474180 : blockSum term 474180 508 55810599 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r474688 : blockSum term 474688 507 54323103 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r475195 : blockSum term 475195 508 64260811 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r475703 : blockSum term 475703 508 64195527 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r476211 : blockSum term 476211 508 54149476 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r476719 : blockSum term 476719 508 48400379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r477227 : blockSum term 477227 508 48346707 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r477735 : blockSum term 477735 508 55399815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r478243 : blockSum term 478243 508 61018572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r478751 : blockSum term 478751 507 58120567 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r479258 : blockSum term 479258 508 49563656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r479766 : blockSum term 479766 508 56586552 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r480274 : blockSum term 480274 508 57940014 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r480782 : blockSum term 480782 507 57876677 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r481289 : blockSum term 481289 508 52176480 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r481797 : blockSum term 481797 508 52123115 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r482305 : blockSum term 482305 508 66136782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r482813 : blockSum term 482813 507 47794181 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r483320 : blockSum term 483320 508 58978451 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r483828 : blockSum term 483828 508 51904384 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r484336 : blockSum term 484336 508 47647546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r484844 : blockSum term 484844 508 39196565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r485352 : blockSum term 485352 508 46149554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r485860 : blockSum term 485860 508 51686695 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r486368 : blockSum term 486368 508 61405841 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r486876 : blockSum term 486876 507 50189632 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r487383 : blockSum term 487383 508 61279568 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r487891 : blockSum term 487891 508 59821214 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r488399 : blockSum term 488399 508 56982242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r488907 : blockSum term 488907 507 51368584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r489414 : blockSum term 489414 508 56862566 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r489922 : blockSum term 489922 508 52651585 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r490430 : blockSum term 490430 508 53980788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r490938 : blockSum term 490938 507 55306763 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r491445 : blockSum term 491445 508 55250743 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r491953 : blockSum term 491953 508 44155357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r492461 : blockSum term 492461 508 51002343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r492969 : blockSum term 492969 508 60587871 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r493477 : blockSum term 493477 508 52269748 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r493985 : blockSum term 493985 508 52218656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r494493 : blockSum term 494493 508 59032377 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r495001 : blockSum term 495001 507 57597320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r495508 : blockSum term 495508 508 63021518 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r496016 : blockSum term 496016 508 50636518 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r496524 : blockSum term 496524 508 43749781 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r497032 : blockSum term 497032 507 55999190 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r497539 : blockSum term 497539 508 53215848 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r498047 : blockSum term 498047 508 49070728 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r498555 : blockSum term 498555 508 53107774 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r499063 : blockSum term 499063 507 55777019 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r499570 : blockSum term 499570 508 55723150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r500078 : blockSum term 500078 508 57023013 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r500586 : blockSum term 500586 508 55606221 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r501094 : blockSum term 501094 508 51490297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r501602 : blockSum term 501602 508 50080877 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r502110 : blockSum term 502110 508 41919111 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r502618 : blockSum term 502618 508 43233147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r503126 : blockSum term 503126 507 55332595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r503633 : blockSum term 503633 508 51231244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r504141 : blockSum term 504141 508 52528716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r504649 : blockSum term 504649 508 57854397 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r505157 : blockSum term 505157 507 60486480 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r505664 : blockSum term 505664 508 42970218 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r506172 : blockSum term 506172 508 53657144 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r506680 : blockSum term 506680 508 54944392 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r507188 : blockSum term 507188 507 45516824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r507695 : blockSum term 507695 508 49485866 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r508203 : blockSum term 508203 508 53444565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r508711 : blockSum term 508711 508 45382793 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r509219 : blockSum term 509219 508 56003007 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r509727 : blockSum term 509727 508 55948105 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r510235 : blockSum term 510235 508 46578493 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r510743 : blockSum term 510743 508 53176050 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r511251 : blockSum term 511251 507 53126165 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r511758 : blockSum term 511758 508 41133637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r512266 : blockSum term 512266 508 51692431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r512774 : blockSum term 512774 508 55617938 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r513282 : blockSum term 513282 507 54238939 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r513789 : blockSum term 513789 508 51539791 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r514297 : blockSum term 514297 508 51490022 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r514805 : blockSum term 514805 508 40890603 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r515313 : blockSum term 515313 507 48753271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r515820 : blockSum term 515820 508 52656913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r516328 : blockSum term 516328 508 56553318 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r516836 : blockSum term 516836 508 57808492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r517344 : blockSum term 517344 508 55129515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r517852 : blockSum term 517852 508 53761565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r518360 : blockSum term 518360 508 52396590 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r518868 : blockSum term 518868 508 48418901 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r519376 : blockSum term 519376 507 48375457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r519883 : blockSum term 519883 508 52245885 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r520391 : blockSum term 520391 508 46976992 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r520899 : blockSum term 520899 508 56054263 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r521407 : blockSum term 521407 507 55997384 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r521914 : blockSum term 521914 508 50738339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r522422 : blockSum term 522422 508 51989837 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r522930 : blockSum term 522930 508 38955945 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r523438 : blockSum term 523438 507 51892969 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r523945 : blockSum term 523945 508 51841404 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r524453 : blockSum term 524453 508 45314933 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r524961 : blockSum term 524961 508 56916041 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r525469 : blockSum term 525469 508 50398895 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r525977 : blockSum term 525977 508 52934242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r526485 : blockSum term 526485 508 55463932 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r526993 : blockSum term 526993 508 50255194 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r527501 : blockSum term 527501 507 46343321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r528008 : blockSum term 528008 508 46298543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r528516 : blockSum term 528516 508 44967669 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r529024 : blockSum term 529024 508 52629987 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r529532 : blockSum term 529532 507 48729705 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r530039 : blockSum term 530039 508 52527620 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r530547 : blockSum term 530547 508 49919636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r531055 : blockSum term 531055 508 40921706 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r531563 : blockSum term 531563 507 49823078 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r532070 : blockSum term 532070 508 51049780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r532578 : blockSum term 532578 508 52278865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r533086 : blockSum term 533086 508 45860988 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r533594 : blockSum term 533594 508 53447679 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r534102 : blockSum term 534102 508 41957826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r534610 : blockSum term 534610 508 43190956 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r535118 : blockSum term 535118 508 44418046 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r535626 : blockSum term 535626 507 49446199 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r536133 : blockSum term 536133 508 55731883 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r536641 : blockSum term 536641 508 59473047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r537149 : blockSum term 537149 508 36663346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r537657 : blockSum term 537657 507 50518858 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r538164 : blockSum term 538164 508 46686705 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r538672 : blockSum term 538672 508 51685224 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r539180 : blockSum term 539180 508 45338844 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r539688 : blockSum term 539688 507 41520602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r540195 : blockSum term 540195 508 51538795 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r540703 : blockSum term 540703 508 40188359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r541211 : blockSum term 541211 508 52696532 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r541719 : blockSum term 541719 508 55152430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r542227 : blockSum term 542227 508 42578375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r542735 : blockSum term 542735 508 51296487 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r543243 : blockSum term 543243 508 47501704 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r543751 : blockSum term 543751 507 51206854 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r544258 : blockSum term 544258 508 38677348 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r544766 : blockSum term 544766 508 48614833 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r545274 : blockSum term 545274 508 42339646 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r545782 : blockSum term 545782 507 49767818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r546289 : blockSum term 546289 508 43506776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r546797 : blockSum term 546797 508 42223501 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r547305 : blockSum term 547305 508 52112374 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r547813 : blockSum term 547813 507 42147284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r548320 : blockSum term 548320 508 50777430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r548828 : blockSum term 548828 508 54443530 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r549336 : blockSum term 549336 508 49445988 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r549844 : blockSum term 549844 508 44459587 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r550352 : blockSum term 550352 508 50586430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r550860 : blockSum term 550860 508 46844316 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r551368 : blockSum term 551368 508 48031975 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r551876 : blockSum term 551876 507 45528620 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r552383 : blockSum term 552383 508 45483758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r552891 : blockSum term 552891 508 42988032 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r553399 : blockSum term 553399 508 53992555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r553907 : blockSum term 553907 507 42908421 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r554414 : blockSum term 554414 508 52664150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r554922 : blockSum term 554922 508 44051671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r555430 : blockSum term 555430 508 34231396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r555938 : blockSum term 555938 507 46413465 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r556445 : blockSum term 556445 508 58572459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r556953 : blockSum term 556953 508 41452378 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r557461 : blockSum term 557461 508 45069039 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r557969 : blockSum term 557969 508 43809490 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r558477 : blockSum term 558477 508 47418241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r558985 : blockSum term 558985 508 42514550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r559493 : blockSum term 559493 508 52186884 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 430001 130000 13680862657 := (join_sums term (lo:=430001) (a:=65000) (b:=65000) (join_sums term (lo:=430001) (a:=32500) (b:=32500) (join_sums term (lo:=430001) (a:=16250) (b:=16250) (join_sums term (lo:=430001) (a:=8125) (b:=8125) (join_sums term (lo:=430001) (a:=4062) (b:=4063) (join_sums term (lo:=430001) (a:=2031) (b:=2031) (join_sums term (lo:=430001) (a:=1015) (b:=1016) (join_sums term (lo:=430001) (a:=507) (b:=508) r430001 r430508) (join_sums term (lo:=431016) (a:=508) (b:=508) r431016 r431524)) (join_sums term (lo:=432032) (a:=1015) (b:=1016) (join_sums term (lo:=432032) (a:=507) (b:=508) r432032 r432539) (join_sums term (lo:=433047) (a:=508) (b:=508) r433047 r433555))) (join_sums term (lo:=434063) (a:=2031) (b:=2032) (join_sums term (lo:=434063) (a:=1015) (b:=1016) (join_sums term (lo:=434063) (a:=507) (b:=508) r434063 r434570) (join_sums term (lo:=435078) (a:=508) (b:=508) r435078 r435586)) (join_sums term (lo:=436094) (a:=1016) (b:=1016) (join_sums term (lo:=436094) (a:=508) (b:=508) r436094 r436602) (join_sums term (lo:=437110) (a:=508) (b:=508) r437110 r437618)))) (join_sums term (lo:=438126) (a:=4062) (b:=4063) (join_sums term (lo:=438126) (a:=2031) (b:=2031) (join_sums term (lo:=438126) (a:=1015) (b:=1016) (join_sums term (lo:=438126) (a:=507) (b:=508) r438126 r438633) (join_sums term (lo:=439141) (a:=508) (b:=508) r439141 r439649)) (join_sums term (lo:=440157) (a:=1015) (b:=1016) (join_sums term (lo:=440157) (a:=507) (b:=508) r440157 r440664) (join_sums term (lo:=441172) (a:=508) (b:=508) r441172 r441680))) (join_sums term (lo:=442188) (a:=2031) (b:=2032) (join_sums term (lo:=442188) (a:=1015) (b:=1016) (join_sums term (lo:=442188) (a:=507) (b:=508) r442188 r442695) (join_sums term (lo:=443203) (a:=508) (b:=508) r443203 r443711)) (join_sums term (lo:=444219) (a:=1016) (b:=1016) (join_sums term (lo:=444219) (a:=508) (b:=508) r444219 r444727) (join_sums term (lo:=445235) (a:=508) (b:=508) r445235 r445743))))) (join_sums term (lo:=446251) (a:=8125) (b:=8125) (join_sums term (lo:=446251) (a:=4062) (b:=4063) (join_sums term (lo:=446251) (a:=2031) (b:=2031) (join_sums term (lo:=446251) (a:=1015) (b:=1016) (join_sums term (lo:=446251) (a:=507) (b:=508) r446251 r446758) (join_sums term (lo:=447266) (a:=508) (b:=508) r447266 r447774)) (join_sums term (lo:=448282) (a:=1015) (b:=1016) (join_sums term (lo:=448282) (a:=507) (b:=508) r448282 r448789) (join_sums term (lo:=449297) (a:=508) (b:=508) r449297 r449805))) (join_sums term (lo:=450313) (a:=2031) (b:=2032) (join_sums term (lo:=450313) (a:=1015) (b:=1016) (join_sums term (lo:=450313) (a:=507) (b:=508) r450313 r450820) (join_sums term (lo:=451328) (a:=508) (b:=508) r451328 r451836)) (join_sums term (lo:=452344) (a:=1016) (b:=1016) (join_sums term (lo:=452344) (a:=508) (b:=508) r452344 r452852) (join_sums term (lo:=453360) (a:=508) (b:=508) r453360 r453868)))) (join_sums term (lo:=454376) (a:=4062) (b:=4063) (join_sums term (lo:=454376) (a:=2031) (b:=2031) (join_sums term (lo:=454376) (a:=1015) (b:=1016) (join_sums term (lo:=454376) (a:=507) (b:=508) r454376 r454883) (join_sums term (lo:=455391) (a:=508) (b:=508) r455391 r455899)) (join_sums term (lo:=456407) (a:=1015) (b:=1016) (join_sums term (lo:=456407) (a:=507) (b:=508) r456407 r456914) (join_sums term (lo:=457422) (a:=508) (b:=508) r457422 r457930))) (join_sums term (lo:=458438) (a:=2031) (b:=2032) (join_sums term (lo:=458438) (a:=1015) (b:=1016) (join_sums term (lo:=458438) (a:=507) (b:=508) r458438 r458945) (join_sums term (lo:=459453) (a:=508) (b:=508) r459453 r459961)) (join_sums term (lo:=460469) (a:=1016) (b:=1016) (join_sums term (lo:=460469) (a:=508) (b:=508) r460469 r460977) (join_sums term (lo:=461485) (a:=508) (b:=508) r461485 r461993)))))) (join_sums term (lo:=462501) (a:=16250) (b:=16250) (join_sums term (lo:=462501) (a:=8125) (b:=8125) (join_sums term (lo:=462501) (a:=4062) (b:=4063) (join_sums term (lo:=462501) (a:=2031) (b:=2031) (join_sums term (lo:=462501) (a:=1015) (b:=1016) (join_sums term (lo:=462501) (a:=507) (b:=508) r462501 r463008) (join_sums term (lo:=463516) (a:=508) (b:=508) r463516 r464024)) (join_sums term (lo:=464532) (a:=1015) (b:=1016) (join_sums term (lo:=464532) (a:=507) (b:=508) r464532 r465039) (join_sums term (lo:=465547) (a:=508) (b:=508) r465547 r466055))) (join_sums term (lo:=466563) (a:=2031) (b:=2032) (join_sums term (lo:=466563) (a:=1015) (b:=1016) (join_sums term (lo:=466563) (a:=507) (b:=508) r466563 r467070) (join_sums term (lo:=467578) (a:=508) (b:=508) r467578 r468086)) (join_sums term (lo:=468594) (a:=1016) (b:=1016) (join_sums term (lo:=468594) (a:=508) (b:=508) r468594 r469102) (join_sums term (lo:=469610) (a:=508) (b:=508) r469610 r470118)))) (join_sums term (lo:=470626) (a:=4062) (b:=4063) (join_sums term (lo:=470626) (a:=2031) (b:=2031) (join_sums term (lo:=470626) (a:=1015) (b:=1016) (join_sums term (lo:=470626) (a:=507) (b:=508) r470626 r471133) (join_sums term (lo:=471641) (a:=508) (b:=508) r471641 r472149)) (join_sums term (lo:=472657) (a:=1015) (b:=1016) (join_sums term (lo:=472657) (a:=507) (b:=508) r472657 r473164) (join_sums term (lo:=473672) (a:=508) (b:=508) r473672 r474180))) (join_sums term (lo:=474688) (a:=2031) (b:=2032) (join_sums term (lo:=474688) (a:=1015) (b:=1016) (join_sums term (lo:=474688) (a:=507) (b:=508) r474688 r475195) (join_sums term (lo:=475703) (a:=508) (b:=508) r475703 r476211)) (join_sums term (lo:=476719) (a:=1016) (b:=1016) (join_sums term (lo:=476719) (a:=508) (b:=508) r476719 r477227) (join_sums term (lo:=477735) (a:=508) (b:=508) r477735 r478243))))) (join_sums term (lo:=478751) (a:=8125) (b:=8125) (join_sums term (lo:=478751) (a:=4062) (b:=4063) (join_sums term (lo:=478751) (a:=2031) (b:=2031) (join_sums term (lo:=478751) (a:=1015) (b:=1016) (join_sums term (lo:=478751) (a:=507) (b:=508) r478751 r479258) (join_sums term (lo:=479766) (a:=508) (b:=508) r479766 r480274)) (join_sums term (lo:=480782) (a:=1015) (b:=1016) (join_sums term (lo:=480782) (a:=507) (b:=508) r480782 r481289) (join_sums term (lo:=481797) (a:=508) (b:=508) r481797 r482305))) (join_sums term (lo:=482813) (a:=2031) (b:=2032) (join_sums term (lo:=482813) (a:=1015) (b:=1016) (join_sums term (lo:=482813) (a:=507) (b:=508) r482813 r483320) (join_sums term (lo:=483828) (a:=508) (b:=508) r483828 r484336)) (join_sums term (lo:=484844) (a:=1016) (b:=1016) (join_sums term (lo:=484844) (a:=508) (b:=508) r484844 r485352) (join_sums term (lo:=485860) (a:=508) (b:=508) r485860 r486368)))) (join_sums term (lo:=486876) (a:=4062) (b:=4063) (join_sums term (lo:=486876) (a:=2031) (b:=2031) (join_sums term (lo:=486876) (a:=1015) (b:=1016) (join_sums term (lo:=486876) (a:=507) (b:=508) r486876 r487383) (join_sums term (lo:=487891) (a:=508) (b:=508) r487891 r488399)) (join_sums term (lo:=488907) (a:=1015) (b:=1016) (join_sums term (lo:=488907) (a:=507) (b:=508) r488907 r489414) (join_sums term (lo:=489922) (a:=508) (b:=508) r489922 r490430))) (join_sums term (lo:=490938) (a:=2031) (b:=2032) (join_sums term (lo:=490938) (a:=1015) (b:=1016) (join_sums term (lo:=490938) (a:=507) (b:=508) r490938 r491445) (join_sums term (lo:=491953) (a:=508) (b:=508) r491953 r492461)) (join_sums term (lo:=492969) (a:=1016) (b:=1016) (join_sums term (lo:=492969) (a:=508) (b:=508) r492969 r493477) (join_sums term (lo:=493985) (a:=508) (b:=508) r493985 r494493))))))) (join_sums term (lo:=495001) (a:=32500) (b:=32500) (join_sums term (lo:=495001) (a:=16250) (b:=16250) (join_sums term (lo:=495001) (a:=8125) (b:=8125) (join_sums term (lo:=495001) (a:=4062) (b:=4063) (join_sums term (lo:=495001) (a:=2031) (b:=2031) (join_sums term (lo:=495001) (a:=1015) (b:=1016) (join_sums term (lo:=495001) (a:=507) (b:=508) r495001 r495508) (join_sums term (lo:=496016) (a:=508) (b:=508) r496016 r496524)) (join_sums term (lo:=497032) (a:=1015) (b:=1016) (join_sums term (lo:=497032) (a:=507) (b:=508) r497032 r497539) (join_sums term (lo:=498047) (a:=508) (b:=508) r498047 r498555))) (join_sums term (lo:=499063) (a:=2031) (b:=2032) (join_sums term (lo:=499063) (a:=1015) (b:=1016) (join_sums term (lo:=499063) (a:=507) (b:=508) r499063 r499570) (join_sums term (lo:=500078) (a:=508) (b:=508) r500078 r500586)) (join_sums term (lo:=501094) (a:=1016) (b:=1016) (join_sums term (lo:=501094) (a:=508) (b:=508) r501094 r501602) (join_sums term (lo:=502110) (a:=508) (b:=508) r502110 r502618)))) (join_sums term (lo:=503126) (a:=4062) (b:=4063) (join_sums term (lo:=503126) (a:=2031) (b:=2031) (join_sums term (lo:=503126) (a:=1015) (b:=1016) (join_sums term (lo:=503126) (a:=507) (b:=508) r503126 r503633) (join_sums term (lo:=504141) (a:=508) (b:=508) r504141 r504649)) (join_sums term (lo:=505157) (a:=1015) (b:=1016) (join_sums term (lo:=505157) (a:=507) (b:=508) r505157 r505664) (join_sums term (lo:=506172) (a:=508) (b:=508) r506172 r506680))) (join_sums term (lo:=507188) (a:=2031) (b:=2032) (join_sums term (lo:=507188) (a:=1015) (b:=1016) (join_sums term (lo:=507188) (a:=507) (b:=508) r507188 r507695) (join_sums term (lo:=508203) (a:=508) (b:=508) r508203 r508711)) (join_sums term (lo:=509219) (a:=1016) (b:=1016) (join_sums term (lo:=509219) (a:=508) (b:=508) r509219 r509727) (join_sums term (lo:=510235) (a:=508) (b:=508) r510235 r510743))))) (join_sums term (lo:=511251) (a:=8125) (b:=8125) (join_sums term (lo:=511251) (a:=4062) (b:=4063) (join_sums term (lo:=511251) (a:=2031) (b:=2031) (join_sums term (lo:=511251) (a:=1015) (b:=1016) (join_sums term (lo:=511251) (a:=507) (b:=508) r511251 r511758) (join_sums term (lo:=512266) (a:=508) (b:=508) r512266 r512774)) (join_sums term (lo:=513282) (a:=1015) (b:=1016) (join_sums term (lo:=513282) (a:=507) (b:=508) r513282 r513789) (join_sums term (lo:=514297) (a:=508) (b:=508) r514297 r514805))) (join_sums term (lo:=515313) (a:=2031) (b:=2032) (join_sums term (lo:=515313) (a:=1015) (b:=1016) (join_sums term (lo:=515313) (a:=507) (b:=508) r515313 r515820) (join_sums term (lo:=516328) (a:=508) (b:=508) r516328 r516836)) (join_sums term (lo:=517344) (a:=1016) (b:=1016) (join_sums term (lo:=517344) (a:=508) (b:=508) r517344 r517852) (join_sums term (lo:=518360) (a:=508) (b:=508) r518360 r518868)))) (join_sums term (lo:=519376) (a:=4062) (b:=4063) (join_sums term (lo:=519376) (a:=2031) (b:=2031) (join_sums term (lo:=519376) (a:=1015) (b:=1016) (join_sums term (lo:=519376) (a:=507) (b:=508) r519376 r519883) (join_sums term (lo:=520391) (a:=508) (b:=508) r520391 r520899)) (join_sums term (lo:=521407) (a:=1015) (b:=1016) (join_sums term (lo:=521407) (a:=507) (b:=508) r521407 r521914) (join_sums term (lo:=522422) (a:=508) (b:=508) r522422 r522930))) (join_sums term (lo:=523438) (a:=2031) (b:=2032) (join_sums term (lo:=523438) (a:=1015) (b:=1016) (join_sums term (lo:=523438) (a:=507) (b:=508) r523438 r523945) (join_sums term (lo:=524453) (a:=508) (b:=508) r524453 r524961)) (join_sums term (lo:=525469) (a:=1016) (b:=1016) (join_sums term (lo:=525469) (a:=508) (b:=508) r525469 r525977) (join_sums term (lo:=526485) (a:=508) (b:=508) r526485 r526993)))))) (join_sums term (lo:=527501) (a:=16250) (b:=16250) (join_sums term (lo:=527501) (a:=8125) (b:=8125) (join_sums term (lo:=527501) (a:=4062) (b:=4063) (join_sums term (lo:=527501) (a:=2031) (b:=2031) (join_sums term (lo:=527501) (a:=1015) (b:=1016) (join_sums term (lo:=527501) (a:=507) (b:=508) r527501 r528008) (join_sums term (lo:=528516) (a:=508) (b:=508) r528516 r529024)) (join_sums term (lo:=529532) (a:=1015) (b:=1016) (join_sums term (lo:=529532) (a:=507) (b:=508) r529532 r530039) (join_sums term (lo:=530547) (a:=508) (b:=508) r530547 r531055))) (join_sums term (lo:=531563) (a:=2031) (b:=2032) (join_sums term (lo:=531563) (a:=1015) (b:=1016) (join_sums term (lo:=531563) (a:=507) (b:=508) r531563 r532070) (join_sums term (lo:=532578) (a:=508) (b:=508) r532578 r533086)) (join_sums term (lo:=533594) (a:=1016) (b:=1016) (join_sums term (lo:=533594) (a:=508) (b:=508) r533594 r534102) (join_sums term (lo:=534610) (a:=508) (b:=508) r534610 r535118)))) (join_sums term (lo:=535626) (a:=4062) (b:=4063) (join_sums term (lo:=535626) (a:=2031) (b:=2031) (join_sums term (lo:=535626) (a:=1015) (b:=1016) (join_sums term (lo:=535626) (a:=507) (b:=508) r535626 r536133) (join_sums term (lo:=536641) (a:=508) (b:=508) r536641 r537149)) (join_sums term (lo:=537657) (a:=1015) (b:=1016) (join_sums term (lo:=537657) (a:=507) (b:=508) r537657 r538164) (join_sums term (lo:=538672) (a:=508) (b:=508) r538672 r539180))) (join_sums term (lo:=539688) (a:=2031) (b:=2032) (join_sums term (lo:=539688) (a:=1015) (b:=1016) (join_sums term (lo:=539688) (a:=507) (b:=508) r539688 r540195) (join_sums term (lo:=540703) (a:=508) (b:=508) r540703 r541211)) (join_sums term (lo:=541719) (a:=1016) (b:=1016) (join_sums term (lo:=541719) (a:=508) (b:=508) r541719 r542227) (join_sums term (lo:=542735) (a:=508) (b:=508) r542735 r543243))))) (join_sums term (lo:=543751) (a:=8125) (b:=8125) (join_sums term (lo:=543751) (a:=4062) (b:=4063) (join_sums term (lo:=543751) (a:=2031) (b:=2031) (join_sums term (lo:=543751) (a:=1015) (b:=1016) (join_sums term (lo:=543751) (a:=507) (b:=508) r543751 r544258) (join_sums term (lo:=544766) (a:=508) (b:=508) r544766 r545274)) (join_sums term (lo:=545782) (a:=1015) (b:=1016) (join_sums term (lo:=545782) (a:=507) (b:=508) r545782 r546289) (join_sums term (lo:=546797) (a:=508) (b:=508) r546797 r547305))) (join_sums term (lo:=547813) (a:=2031) (b:=2032) (join_sums term (lo:=547813) (a:=1015) (b:=1016) (join_sums term (lo:=547813) (a:=507) (b:=508) r547813 r548320) (join_sums term (lo:=548828) (a:=508) (b:=508) r548828 r549336)) (join_sums term (lo:=549844) (a:=1016) (b:=1016) (join_sums term (lo:=549844) (a:=508) (b:=508) r549844 r550352) (join_sums term (lo:=550860) (a:=508) (b:=508) r550860 r551368)))) (join_sums term (lo:=551876) (a:=4062) (b:=4063) (join_sums term (lo:=551876) (a:=2031) (b:=2031) (join_sums term (lo:=551876) (a:=1015) (b:=1016) (join_sums term (lo:=551876) (a:=507) (b:=508) r551876 r552383) (join_sums term (lo:=552891) (a:=508) (b:=508) r552891 r553399)) (join_sums term (lo:=553907) (a:=1015) (b:=1016) (join_sums term (lo:=553907) (a:=507) (b:=508) r553907 r554414) (join_sums term (lo:=554922) (a:=508) (b:=508) r554922 r555430))) (join_sums term (lo:=555938) (a:=2031) (b:=2032) (join_sums term (lo:=555938) (a:=1015) (b:=1016) (join_sums term (lo:=555938) (a:=507) (b:=508) r555938 r556445) (join_sums term (lo:=556953) (a:=508) (b:=508) r556953 r557461)) (join_sums term (lo:=557969) (a:=1016) (b:=1016) (join_sums term (lo:=557969) (a:=508) (b:=508) r557969 r558477) (join_sums term (lo:=558985) (a:=508) (b:=508) r558985 r559493))))))))

private theorem rows : blockSum term 0 560001 13680862657 :=
  join_sums term (lo:=0) (a:=430001) (b:=130000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 560000).filter (430000 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=13680862657 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=745089)
    SparsePrimeA204.fast FastDenseA26.fast FastDenseA26.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From430000To560000
