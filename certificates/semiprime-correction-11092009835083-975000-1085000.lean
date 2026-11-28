import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 975,000 through 1,085,000

The sum covers 7,909 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction11092009835083From975000To1085000

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


private abbrev term := contribution 11092009835083 975000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 975001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 975000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r975001 : blockSum term 975001 429 20183562 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r975430 : blockSum term 975430 430 20173603 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r975860 : blockSum term 975860 429 19491741 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r976289 : blockSum term 976289 430 21497334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r976719 : blockSum term 976719 429 15443483 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r977148 : blockSum term 977148 430 18791667 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r977578 : blockSum term 977578 430 17440329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r978008 : blockSum term 978008 430 26148154 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r978438 : blockSum term 978438 429 20773410 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r978867 : blockSum term 978867 430 21432854 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r979297 : blockSum term 979297 430 17406140 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r979727 : blockSum term 979727 430 16727281 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r980157 : blockSum term 980157 429 18056934 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r980586 : blockSum term 980586 430 20721690 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r981016 : blockSum term 981016 430 23383486 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r981446 : blockSum term 981446 430 19365756 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r981876 : blockSum term 981876 429 22025974 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r982305 : blockSum term 982305 430 17344641 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r982735 : blockSum term 982735 429 20669870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r983164 : blockSum term 983164 430 23324782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r983594 : blockSum term 983594 429 17984362 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r984023 : blockSum term 984023 430 21969914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r984453 : blockSum term 984453 430 18632787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r984883 : blockSum term 984883 430 19288410 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r985313 : blockSum term 985313 429 22602885 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r985742 : blockSum term 985742 430 20597658 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r986172 : blockSum term 986172 430 22579343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r986602 : blockSum term 986602 430 22567787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r987032 : blockSum term 987032 429 17913455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r987461 : blockSum term 987461 430 15915075 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r987891 : blockSum term 987891 430 22534814 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r988321 : blockSum term 988321 430 19873767 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r988751 : blockSum term 988751 429 17215737 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r989180 : blockSum term 989180 430 18530849 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r989610 : blockSum term 989610 429 25136187 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r990039 : blockSum term 990039 430 19834115 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r990469 : blockSum term 990469 429 19824864 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r990898 : blockSum term 990898 430 21136145 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r991328 : blockSum term 991328 430 21785219 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r991758 : blockSum term 991758 430 21774167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r992188 : blockSum term 992188 429 18465924 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r992617 : blockSum term 992617 430 18456266 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r993047 : blockSum term 993047 430 20423824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r993477 : blockSum term 993477 430 17120783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r993907 : blockSum term 993907 429 23035585 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r994336 : blockSum term 994336 430 20392907 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r994766 : blockSum term 994766 430 19725680 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r995196 : blockSum term 995196 430 22343234 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r995626 : blockSum term 995626 429 19048189 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r996055 : blockSum term 996055 430 19695788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r996485 : blockSum term 996485 429 20341887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r996914 : blockSum term 996914 430 26234931 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r997344 : blockSum term 997344 429 20322309 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r997773 : blockSum term 997773 430 20312694 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r998203 : blockSum term 998203 430 18992521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r998633 : blockSum term 998633 430 22910195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r999063 : blockSum term 999063 429 17665118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r999492 : blockSum term 999492 430 17656535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r999922 : blockSum term 999922 430 21568681 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1000352 : blockSum term 1000352 430 21558269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1000782 : blockSum term 1000782 429 21547091 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1001211 : blockSum term 1001211 430 22841458 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1001641 : blockSum term 1001641 430 17611661 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1002071 : blockSum term 1002071 430 23470836 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1002501 : blockSum term 1002501 429 25413362 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1002930 : blockSum term 1002930 430 18236357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1003360 : blockSum term 1003360 429 22132778 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1003789 : blockSum term 1003789 430 17567391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1004219 : blockSum term 1004219 429 16908700 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1004648 : blockSum term 1004648 430 20150041 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1005078 : blockSum term 1005078 430 23388112 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1005508 : blockSum term 1005508 430 16883394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1005938 : blockSum term 1005938 429 25960335 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1006367 : blockSum term 1006367 430 18812498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1006797 : blockSum term 1006797 430 20100308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1007227 : blockSum term 1007227 430 18794478 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1007657 : blockSum term 1007657 429 25263580 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1008086 : blockSum term 1008086 430 22012640 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1008516 : blockSum term 1008516 430 21354763 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1008946 : blockSum term 1008946 430 23283966 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1009376 : blockSum term 1009376 429 18748299 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1009805 : blockSum term 1009805 430 17446672 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1010235 : blockSum term 1010235 429 16792064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1010664 : blockSum term 1010664 430 23884403 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1011094 : blockSum term 1011094 429 17421279 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1011523 : blockSum term 1011523 430 19992346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1011953 : blockSum term 1011953 430 21915656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1012383 : blockSum term 1012383 430 27058890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1012813 : blockSum term 1012813 429 14810499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1013242 : blockSum term 1013242 430 18021170 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1013672 : blockSum term 1013672 430 19942976 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1014102 : blockSum term 1014102 430 21861761 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1014532 : blockSum term 1014532 429 19279827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1014961 : blockSum term 1014961 430 17986043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1015391 : blockSum term 1015391 430 21829175 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1015821 : blockSum term 1015821 430 23742551 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1016251 : blockSum term 1016251 429 16675821 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1016680 : blockSum term 1016680 430 19873323 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1017110 : blockSum term 1017110 429 20504689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1017539 : blockSum term 1017539 430 19853694 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1017969 : blockSum term 1017969 429 14722599 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1018398 : blockSum term 1018398 430 21113054 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1018828 : blockSum term 1018828 430 19824044 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1019258 : blockSum term 1019258 430 21732332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1019688 : blockSum term 1019688 429 24277304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1020117 : blockSum term 1020117 430 17879555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1020547 : blockSum term 1020547 430 20423426 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1020977 : blockSum term 1020977 430 26792823 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1021407 : blockSum term 1021407 429 17215110 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1021836 : blockSum term 1021836 430 20393201 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1022266 : blockSum term 1022266 430 19109017 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1022696 : blockSum term 1022696 430 18463329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1023126 : blockSum term 1023126 429 22272193 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1023555 : blockSum term 1023555 430 15900371 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1023985 : blockSum term 1023985 429 18435331 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1024414 : blockSum term 1024414 430 17791404 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1024844 : blockSum term 1024844 429 24133729 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1025273 : blockSum term 1025273 430 21583235 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1025703 : blockSum term 1025703 430 19034474 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1026133 : blockSum term 1026133 430 19025278 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1026563 : blockSum term 1026563 429 20917188 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1026992 : blockSum term 1026992 430 19006194 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1027422 : blockSum term 1027422 430 19630096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1027852 : blockSum term 1027852 430 21518727 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1028282 : blockSum term 1028282 429 16448304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1028711 : blockSum term 1028711 430 17705155 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1029141 : blockSum term 1029141 430 23383909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1029571 : blockSum term 1029571 430 18950725 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1030001 : blockSum term 1030001 429 19574091 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1030430 : blockSum term 1030430 430 18932673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1030860 : blockSum term 1030860 429 15770296 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1031289 : blockSum term 1031289 430 20176231 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1031719 : blockSum term 1031719 429 13864805 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1032148 : blockSum term 1032148 430 20156715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1032578 : blockSum term 1032578 430 22035902 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1033008 : blockSum term 1033008 430 21395055 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1033438 : blockSum term 1033438 429 22014418 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1033867 : blockSum term 1033867 430 17602100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1034297 : blockSum term 1034297 430 18851684 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1034727 : blockSum term 1034727 430 19470959 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1035157 : blockSum term 1035157 429 21971113 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1035586 : blockSum term 1035586 430 16313522 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1036016 : blockSum term 1036016 430 22576396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1036446 : blockSum term 1036446 430 18804265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1036876 : blockSum term 1036876 429 17542459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1037305 : blockSum term 1037305 430 16907980 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1037735 : blockSum term 1037735 429 20655169 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1038164 : blockSum term 1038164 430 18768169 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1038594 : blockSum term 1038594 429 18759431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1039023 : blockSum term 1039023 430 17499863 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1039453 : blockSum term 1039453 430 14992273 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1039883 : blockSum term 1039883 430 20604295 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1040313 : blockSum term 1040313 429 16849827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1040742 : blockSum term 1040742 430 24950260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1041172 : blockSum term 1041172 430 19950502 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1041602 : blockSum term 1041602 430 18694165 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1042032 : blockSum term 1042032 429 20553804 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1042461 : blockSum term 1042461 430 17430897 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1042891 : blockSum term 1042891 430 18666801 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1043321 : blockSum term 1043321 430 18035764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1043751 : blockSum term 1043751 429 21135507 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1044180 : blockSum term 1044180 430 21125103 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1044610 : blockSum term 1044610 429 21114802 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1045039 : blockSum term 1045039 430 19863093 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1045469 : blockSum term 1045469 429 18613264 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1045898 : blockSum term 1045898 430 15503217 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1046328 : blockSum term 1046328 430 17975391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1046758 : blockSum term 1046758 430 19824844 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1047188 : blockSum term 1047188 429 19815721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1047617 : blockSum term 1047617 430 22281298 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1048047 : blockSum term 1048047 430 15465881 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1048477 : blockSum term 1048477 430 19786402 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1048907 : blockSum term 1048907 429 19777509 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1049336 : blockSum term 1049336 430 19150221 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1049766 : blockSum term 1049766 430 19758711 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1050196 : blockSum term 1050196 430 17280339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1050626 : blockSum term 1050626 429 17271191 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1051055 : blockSum term 1051055 430 16646664 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1051485 : blockSum term 1051485 429 20336023 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1051914 : blockSum term 1051914 430 20325506 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1052344 : blockSum term 1052344 429 16006428 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1052773 : blockSum term 1052773 430 17845121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1053203 : blockSum term 1053203 430 19681331 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1053633 : blockSum term 1053633 430 17213225 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1054063 : blockSum term 1054063 429 20891807 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1054492 : blockSum term 1054492 430 16583492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1054922 : blockSum term 1054922 430 16575244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1055352 : blockSum term 1055352 430 17795090 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1055782 : blockSum term 1055782 429 22079056 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1056211 : blockSum term 1056211 430 20842030 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1056641 : blockSum term 1056641 430 17155663 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1057071 : blockSum term 1057071 430 16535158 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1057501 : blockSum term 1057501 429 17139152 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1057930 : blockSum term 1057930 430 20189957 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1058360 : blockSum term 1058360 429 22014436 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1058789 : blockSum term 1058789 430 18947858 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1059219 : blockSum term 1059219 429 17717293 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1059648 : blockSum term 1059648 430 18318953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1060078 : blockSum term 1060078 430 21971491 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1060508 : blockSum term 1060508 430 13421332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1060938 : blockSum term 1060938 429 18292174 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1061367 : blockSum term 1061367 430 20111678 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1061797 : blockSum term 1061797 430 14011277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1062227 : blockSum term 1062227 430 14613399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1062657 : blockSum term 1062657 429 20691900 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1063086 : blockSum term 1063086 430 18857287 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1063516 : blockSum term 1063516 430 23103783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1063946 : blockSum term 1063946 430 20054320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1064376 : blockSum term 1064376 429 18222408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1064805 : blockSum term 1064805 430 18820621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1065235 : blockSum term 1065235 429 15777409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1065664 : blockSum term 1065664 430 19409607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1066094 : blockSum term 1066094 429 18187682 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1066523 : blockSum term 1066523 430 17572924 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1066953 : blockSum term 1066953 430 18169860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1067383 : blockSum term 1067383 430 21187449 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1067813 : blockSum term 1067813 429 16941852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1068242 : blockSum term 1068242 430 19958065 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1068672 : blockSum term 1068672 430 19948431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1069102 : blockSum term 1069102 430 18126157 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1069532 : blockSum term 1069532 429 21137158 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1069961 : blockSum term 1069961 430 21729730 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1070391 : blockSum term 1070391 430 17496859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1070821 : blockSum term 1070821 430 18693492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1071251 : blockSum term 1071251 429 20493265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1071680 : blockSum term 1071680 430 15061625 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1072110 : blockSum term 1072110 429 17463497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1072539 : blockSum term 1072539 430 16852457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1072969 : blockSum term 1072969 429 19853108 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1073398 : blockSum term 1073398 430 17438406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1073828 : blockSum term 1073828 430 16829070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1074258 : blockSum term 1074258 430 18022349 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1074688 : blockSum term 1074688 429 22817138 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1075117 : blockSum term 1075117 430 22205436 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1075547 : blockSum term 1075547 430 18596480 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1075977 : blockSum term 1075977 430 20386212 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1076407 : blockSum term 1076407 429 18578462 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1076836 : blockSum term 1076836 430 14975870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1077266 : blockSum term 1077266 430 14968943 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1077696 : blockSum term 1077696 430 20348399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1078126 : blockSum term 1078126 429 15553083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1078555 : blockSum term 1078555 430 17936786 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1078985 : blockSum term 1078985 429 20917377 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1079414 : blockSum term 1079414 430 19114871 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1079844 : blockSum term 1079844 429 23284969 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1080273 : blockSum term 1080273 430 18499560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1080703 : blockSum term 1080703 430 22069241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1081133 : blockSum term 1081133 430 16693106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1081563 : blockSum term 1081563 429 19664045 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1081992 : blockSum term 1081992 430 19058993 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1082422 : blockSum term 1082422 430 16669080 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1082852 : blockSum term 1082852 430 15470878 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1083282 : blockSum term 1083282 429 19628099 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1083711 : blockSum term 1083711 430 19023519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1084141 : blockSum term 1084141 430 17231535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1084571 : blockSum term 1084571 430 19005036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 975001 110000 4999601650 := (join_sums term (lo:=975001) (a:=55000) (b:=55000) (join_sums term (lo:=975001) (a:=27500) (b:=27500) (join_sums term (lo:=975001) (a:=13750) (b:=13750) (join_sums term (lo:=975001) (a:=6875) (b:=6875) (join_sums term (lo:=975001) (a:=3437) (b:=3438) (join_sums term (lo:=975001) (a:=1718) (b:=1719) (join_sums term (lo:=975001) (a:=859) (b:=859) (join_sums term (lo:=975001) (a:=429) (b:=430) r975001 r975430) (join_sums term (lo:=975860) (a:=429) (b:=430) r975860 r976289)) (join_sums term (lo:=976719) (a:=859) (b:=860) (join_sums term (lo:=976719) (a:=429) (b:=430) r976719 r977148) (join_sums term (lo:=977578) (a:=430) (b:=430) r977578 r978008))) (join_sums term (lo:=978438) (a:=1719) (b:=1719) (join_sums term (lo:=978438) (a:=859) (b:=860) (join_sums term (lo:=978438) (a:=429) (b:=430) r978438 r978867) (join_sums term (lo:=979297) (a:=430) (b:=430) r979297 r979727)) (join_sums term (lo:=980157) (a:=859) (b:=860) (join_sums term (lo:=980157) (a:=429) (b:=430) r980157 r980586) (join_sums term (lo:=981016) (a:=430) (b:=430) r981016 r981446)))) (join_sums term (lo:=981876) (a:=3437) (b:=3438) (join_sums term (lo:=981876) (a:=1718) (b:=1719) (join_sums term (lo:=981876) (a:=859) (b:=859) (join_sums term (lo:=981876) (a:=429) (b:=430) r981876 r982305) (join_sums term (lo:=982735) (a:=429) (b:=430) r982735 r983164)) (join_sums term (lo:=983594) (a:=859) (b:=860) (join_sums term (lo:=983594) (a:=429) (b:=430) r983594 r984023) (join_sums term (lo:=984453) (a:=430) (b:=430) r984453 r984883))) (join_sums term (lo:=985313) (a:=1719) (b:=1719) (join_sums term (lo:=985313) (a:=859) (b:=860) (join_sums term (lo:=985313) (a:=429) (b:=430) r985313 r985742) (join_sums term (lo:=986172) (a:=430) (b:=430) r986172 r986602)) (join_sums term (lo:=987032) (a:=859) (b:=860) (join_sums term (lo:=987032) (a:=429) (b:=430) r987032 r987461) (join_sums term (lo:=987891) (a:=430) (b:=430) r987891 r988321))))) (join_sums term (lo:=988751) (a:=6875) (b:=6875) (join_sums term (lo:=988751) (a:=3437) (b:=3438) (join_sums term (lo:=988751) (a:=1718) (b:=1719) (join_sums term (lo:=988751) (a:=859) (b:=859) (join_sums term (lo:=988751) (a:=429) (b:=430) r988751 r989180) (join_sums term (lo:=989610) (a:=429) (b:=430) r989610 r990039)) (join_sums term (lo:=990469) (a:=859) (b:=860) (join_sums term (lo:=990469) (a:=429) (b:=430) r990469 r990898) (join_sums term (lo:=991328) (a:=430) (b:=430) r991328 r991758))) (join_sums term (lo:=992188) (a:=1719) (b:=1719) (join_sums term (lo:=992188) (a:=859) (b:=860) (join_sums term (lo:=992188) (a:=429) (b:=430) r992188 r992617) (join_sums term (lo:=993047) (a:=430) (b:=430) r993047 r993477)) (join_sums term (lo:=993907) (a:=859) (b:=860) (join_sums term (lo:=993907) (a:=429) (b:=430) r993907 r994336) (join_sums term (lo:=994766) (a:=430) (b:=430) r994766 r995196)))) (join_sums term (lo:=995626) (a:=3437) (b:=3438) (join_sums term (lo:=995626) (a:=1718) (b:=1719) (join_sums term (lo:=995626) (a:=859) (b:=859) (join_sums term (lo:=995626) (a:=429) (b:=430) r995626 r996055) (join_sums term (lo:=996485) (a:=429) (b:=430) r996485 r996914)) (join_sums term (lo:=997344) (a:=859) (b:=860) (join_sums term (lo:=997344) (a:=429) (b:=430) r997344 r997773) (join_sums term (lo:=998203) (a:=430) (b:=430) r998203 r998633))) (join_sums term (lo:=999063) (a:=1719) (b:=1719) (join_sums term (lo:=999063) (a:=859) (b:=860) (join_sums term (lo:=999063) (a:=429) (b:=430) r999063 r999492) (join_sums term (lo:=999922) (a:=430) (b:=430) r999922 r1000352)) (join_sums term (lo:=1000782) (a:=859) (b:=860) (join_sums term (lo:=1000782) (a:=429) (b:=430) r1000782 r1001211) (join_sums term (lo:=1001641) (a:=430) (b:=430) r1001641 r1002071)))))) (join_sums term (lo:=1002501) (a:=13750) (b:=13750) (join_sums term (lo:=1002501) (a:=6875) (b:=6875) (join_sums term (lo:=1002501) (a:=3437) (b:=3438) (join_sums term (lo:=1002501) (a:=1718) (b:=1719) (join_sums term (lo:=1002501) (a:=859) (b:=859) (join_sums term (lo:=1002501) (a:=429) (b:=430) r1002501 r1002930) (join_sums term (lo:=1003360) (a:=429) (b:=430) r1003360 r1003789)) (join_sums term (lo:=1004219) (a:=859) (b:=860) (join_sums term (lo:=1004219) (a:=429) (b:=430) r1004219 r1004648) (join_sums term (lo:=1005078) (a:=430) (b:=430) r1005078 r1005508))) (join_sums term (lo:=1005938) (a:=1719) (b:=1719) (join_sums term (lo:=1005938) (a:=859) (b:=860) (join_sums term (lo:=1005938) (a:=429) (b:=430) r1005938 r1006367) (join_sums term (lo:=1006797) (a:=430) (b:=430) r1006797 r1007227)) (join_sums term (lo:=1007657) (a:=859) (b:=860) (join_sums term (lo:=1007657) (a:=429) (b:=430) r1007657 r1008086) (join_sums term (lo:=1008516) (a:=430) (b:=430) r1008516 r1008946)))) (join_sums term (lo:=1009376) (a:=3437) (b:=3438) (join_sums term (lo:=1009376) (a:=1718) (b:=1719) (join_sums term (lo:=1009376) (a:=859) (b:=859) (join_sums term (lo:=1009376) (a:=429) (b:=430) r1009376 r1009805) (join_sums term (lo:=1010235) (a:=429) (b:=430) r1010235 r1010664)) (join_sums term (lo:=1011094) (a:=859) (b:=860) (join_sums term (lo:=1011094) (a:=429) (b:=430) r1011094 r1011523) (join_sums term (lo:=1011953) (a:=430) (b:=430) r1011953 r1012383))) (join_sums term (lo:=1012813) (a:=1719) (b:=1719) (join_sums term (lo:=1012813) (a:=859) (b:=860) (join_sums term (lo:=1012813) (a:=429) (b:=430) r1012813 r1013242) (join_sums term (lo:=1013672) (a:=430) (b:=430) r1013672 r1014102)) (join_sums term (lo:=1014532) (a:=859) (b:=860) (join_sums term (lo:=1014532) (a:=429) (b:=430) r1014532 r1014961) (join_sums term (lo:=1015391) (a:=430) (b:=430) r1015391 r1015821))))) (join_sums term (lo:=1016251) (a:=6875) (b:=6875) (join_sums term (lo:=1016251) (a:=3437) (b:=3438) (join_sums term (lo:=1016251) (a:=1718) (b:=1719) (join_sums term (lo:=1016251) (a:=859) (b:=859) (join_sums term (lo:=1016251) (a:=429) (b:=430) r1016251 r1016680) (join_sums term (lo:=1017110) (a:=429) (b:=430) r1017110 r1017539)) (join_sums term (lo:=1017969) (a:=859) (b:=860) (join_sums term (lo:=1017969) (a:=429) (b:=430) r1017969 r1018398) (join_sums term (lo:=1018828) (a:=430) (b:=430) r1018828 r1019258))) (join_sums term (lo:=1019688) (a:=1719) (b:=1719) (join_sums term (lo:=1019688) (a:=859) (b:=860) (join_sums term (lo:=1019688) (a:=429) (b:=430) r1019688 r1020117) (join_sums term (lo:=1020547) (a:=430) (b:=430) r1020547 r1020977)) (join_sums term (lo:=1021407) (a:=859) (b:=860) (join_sums term (lo:=1021407) (a:=429) (b:=430) r1021407 r1021836) (join_sums term (lo:=1022266) (a:=430) (b:=430) r1022266 r1022696)))) (join_sums term (lo:=1023126) (a:=3437) (b:=3438) (join_sums term (lo:=1023126) (a:=1718) (b:=1719) (join_sums term (lo:=1023126) (a:=859) (b:=859) (join_sums term (lo:=1023126) (a:=429) (b:=430) r1023126 r1023555) (join_sums term (lo:=1023985) (a:=429) (b:=430) r1023985 r1024414)) (join_sums term (lo:=1024844) (a:=859) (b:=860) (join_sums term (lo:=1024844) (a:=429) (b:=430) r1024844 r1025273) (join_sums term (lo:=1025703) (a:=430) (b:=430) r1025703 r1026133))) (join_sums term (lo:=1026563) (a:=1719) (b:=1719) (join_sums term (lo:=1026563) (a:=859) (b:=860) (join_sums term (lo:=1026563) (a:=429) (b:=430) r1026563 r1026992) (join_sums term (lo:=1027422) (a:=430) (b:=430) r1027422 r1027852)) (join_sums term (lo:=1028282) (a:=859) (b:=860) (join_sums term (lo:=1028282) (a:=429) (b:=430) r1028282 r1028711) (join_sums term (lo:=1029141) (a:=430) (b:=430) r1029141 r1029571))))))) (join_sums term (lo:=1030001) (a:=27500) (b:=27500) (join_sums term (lo:=1030001) (a:=13750) (b:=13750) (join_sums term (lo:=1030001) (a:=6875) (b:=6875) (join_sums term (lo:=1030001) (a:=3437) (b:=3438) (join_sums term (lo:=1030001) (a:=1718) (b:=1719) (join_sums term (lo:=1030001) (a:=859) (b:=859) (join_sums term (lo:=1030001) (a:=429) (b:=430) r1030001 r1030430) (join_sums term (lo:=1030860) (a:=429) (b:=430) r1030860 r1031289)) (join_sums term (lo:=1031719) (a:=859) (b:=860) (join_sums term (lo:=1031719) (a:=429) (b:=430) r1031719 r1032148) (join_sums term (lo:=1032578) (a:=430) (b:=430) r1032578 r1033008))) (join_sums term (lo:=1033438) (a:=1719) (b:=1719) (join_sums term (lo:=1033438) (a:=859) (b:=860) (join_sums term (lo:=1033438) (a:=429) (b:=430) r1033438 r1033867) (join_sums term (lo:=1034297) (a:=430) (b:=430) r1034297 r1034727)) (join_sums term (lo:=1035157) (a:=859) (b:=860) (join_sums term (lo:=1035157) (a:=429) (b:=430) r1035157 r1035586) (join_sums term (lo:=1036016) (a:=430) (b:=430) r1036016 r1036446)))) (join_sums term (lo:=1036876) (a:=3437) (b:=3438) (join_sums term (lo:=1036876) (a:=1718) (b:=1719) (join_sums term (lo:=1036876) (a:=859) (b:=859) (join_sums term (lo:=1036876) (a:=429) (b:=430) r1036876 r1037305) (join_sums term (lo:=1037735) (a:=429) (b:=430) r1037735 r1038164)) (join_sums term (lo:=1038594) (a:=859) (b:=860) (join_sums term (lo:=1038594) (a:=429) (b:=430) r1038594 r1039023) (join_sums term (lo:=1039453) (a:=430) (b:=430) r1039453 r1039883))) (join_sums term (lo:=1040313) (a:=1719) (b:=1719) (join_sums term (lo:=1040313) (a:=859) (b:=860) (join_sums term (lo:=1040313) (a:=429) (b:=430) r1040313 r1040742) (join_sums term (lo:=1041172) (a:=430) (b:=430) r1041172 r1041602)) (join_sums term (lo:=1042032) (a:=859) (b:=860) (join_sums term (lo:=1042032) (a:=429) (b:=430) r1042032 r1042461) (join_sums term (lo:=1042891) (a:=430) (b:=430) r1042891 r1043321))))) (join_sums term (lo:=1043751) (a:=6875) (b:=6875) (join_sums term (lo:=1043751) (a:=3437) (b:=3438) (join_sums term (lo:=1043751) (a:=1718) (b:=1719) (join_sums term (lo:=1043751) (a:=859) (b:=859) (join_sums term (lo:=1043751) (a:=429) (b:=430) r1043751 r1044180) (join_sums term (lo:=1044610) (a:=429) (b:=430) r1044610 r1045039)) (join_sums term (lo:=1045469) (a:=859) (b:=860) (join_sums term (lo:=1045469) (a:=429) (b:=430) r1045469 r1045898) (join_sums term (lo:=1046328) (a:=430) (b:=430) r1046328 r1046758))) (join_sums term (lo:=1047188) (a:=1719) (b:=1719) (join_sums term (lo:=1047188) (a:=859) (b:=860) (join_sums term (lo:=1047188) (a:=429) (b:=430) r1047188 r1047617) (join_sums term (lo:=1048047) (a:=430) (b:=430) r1048047 r1048477)) (join_sums term (lo:=1048907) (a:=859) (b:=860) (join_sums term (lo:=1048907) (a:=429) (b:=430) r1048907 r1049336) (join_sums term (lo:=1049766) (a:=430) (b:=430) r1049766 r1050196)))) (join_sums term (lo:=1050626) (a:=3437) (b:=3438) (join_sums term (lo:=1050626) (a:=1718) (b:=1719) (join_sums term (lo:=1050626) (a:=859) (b:=859) (join_sums term (lo:=1050626) (a:=429) (b:=430) r1050626 r1051055) (join_sums term (lo:=1051485) (a:=429) (b:=430) r1051485 r1051914)) (join_sums term (lo:=1052344) (a:=859) (b:=860) (join_sums term (lo:=1052344) (a:=429) (b:=430) r1052344 r1052773) (join_sums term (lo:=1053203) (a:=430) (b:=430) r1053203 r1053633))) (join_sums term (lo:=1054063) (a:=1719) (b:=1719) (join_sums term (lo:=1054063) (a:=859) (b:=860) (join_sums term (lo:=1054063) (a:=429) (b:=430) r1054063 r1054492) (join_sums term (lo:=1054922) (a:=430) (b:=430) r1054922 r1055352)) (join_sums term (lo:=1055782) (a:=859) (b:=860) (join_sums term (lo:=1055782) (a:=429) (b:=430) r1055782 r1056211) (join_sums term (lo:=1056641) (a:=430) (b:=430) r1056641 r1057071)))))) (join_sums term (lo:=1057501) (a:=13750) (b:=13750) (join_sums term (lo:=1057501) (a:=6875) (b:=6875) (join_sums term (lo:=1057501) (a:=3437) (b:=3438) (join_sums term (lo:=1057501) (a:=1718) (b:=1719) (join_sums term (lo:=1057501) (a:=859) (b:=859) (join_sums term (lo:=1057501) (a:=429) (b:=430) r1057501 r1057930) (join_sums term (lo:=1058360) (a:=429) (b:=430) r1058360 r1058789)) (join_sums term (lo:=1059219) (a:=859) (b:=860) (join_sums term (lo:=1059219) (a:=429) (b:=430) r1059219 r1059648) (join_sums term (lo:=1060078) (a:=430) (b:=430) r1060078 r1060508))) (join_sums term (lo:=1060938) (a:=1719) (b:=1719) (join_sums term (lo:=1060938) (a:=859) (b:=860) (join_sums term (lo:=1060938) (a:=429) (b:=430) r1060938 r1061367) (join_sums term (lo:=1061797) (a:=430) (b:=430) r1061797 r1062227)) (join_sums term (lo:=1062657) (a:=859) (b:=860) (join_sums term (lo:=1062657) (a:=429) (b:=430) r1062657 r1063086) (join_sums term (lo:=1063516) (a:=430) (b:=430) r1063516 r1063946)))) (join_sums term (lo:=1064376) (a:=3437) (b:=3438) (join_sums term (lo:=1064376) (a:=1718) (b:=1719) (join_sums term (lo:=1064376) (a:=859) (b:=859) (join_sums term (lo:=1064376) (a:=429) (b:=430) r1064376 r1064805) (join_sums term (lo:=1065235) (a:=429) (b:=430) r1065235 r1065664)) (join_sums term (lo:=1066094) (a:=859) (b:=860) (join_sums term (lo:=1066094) (a:=429) (b:=430) r1066094 r1066523) (join_sums term (lo:=1066953) (a:=430) (b:=430) r1066953 r1067383))) (join_sums term (lo:=1067813) (a:=1719) (b:=1719) (join_sums term (lo:=1067813) (a:=859) (b:=860) (join_sums term (lo:=1067813) (a:=429) (b:=430) r1067813 r1068242) (join_sums term (lo:=1068672) (a:=430) (b:=430) r1068672 r1069102)) (join_sums term (lo:=1069532) (a:=859) (b:=860) (join_sums term (lo:=1069532) (a:=429) (b:=430) r1069532 r1069961) (join_sums term (lo:=1070391) (a:=430) (b:=430) r1070391 r1070821))))) (join_sums term (lo:=1071251) (a:=6875) (b:=6875) (join_sums term (lo:=1071251) (a:=3437) (b:=3438) (join_sums term (lo:=1071251) (a:=1718) (b:=1719) (join_sums term (lo:=1071251) (a:=859) (b:=859) (join_sums term (lo:=1071251) (a:=429) (b:=430) r1071251 r1071680) (join_sums term (lo:=1072110) (a:=429) (b:=430) r1072110 r1072539)) (join_sums term (lo:=1072969) (a:=859) (b:=860) (join_sums term (lo:=1072969) (a:=429) (b:=430) r1072969 r1073398) (join_sums term (lo:=1073828) (a:=430) (b:=430) r1073828 r1074258))) (join_sums term (lo:=1074688) (a:=1719) (b:=1719) (join_sums term (lo:=1074688) (a:=859) (b:=860) (join_sums term (lo:=1074688) (a:=429) (b:=430) r1074688 r1075117) (join_sums term (lo:=1075547) (a:=430) (b:=430) r1075547 r1075977)) (join_sums term (lo:=1076407) (a:=859) (b:=860) (join_sums term (lo:=1076407) (a:=429) (b:=430) r1076407 r1076836) (join_sums term (lo:=1077266) (a:=430) (b:=430) r1077266 r1077696)))) (join_sums term (lo:=1078126) (a:=3437) (b:=3438) (join_sums term (lo:=1078126) (a:=1718) (b:=1719) (join_sums term (lo:=1078126) (a:=859) (b:=859) (join_sums term (lo:=1078126) (a:=429) (b:=430) r1078126 r1078555) (join_sums term (lo:=1078985) (a:=429) (b:=430) r1078985 r1079414)) (join_sums term (lo:=1079844) (a:=859) (b:=860) (join_sums term (lo:=1079844) (a:=429) (b:=430) r1079844 r1080273) (join_sums term (lo:=1080703) (a:=430) (b:=430) r1080703 r1081133))) (join_sums term (lo:=1081563) (a:=1719) (b:=1719) (join_sums term (lo:=1081563) (a:=859) (b:=860) (join_sums term (lo:=1081563) (a:=429) (b:=430) r1081563 r1081992) (join_sums term (lo:=1082422) (a:=430) (b:=430) r1082422 r1082852)) (join_sums term (lo:=1083282) (a:=859) (b:=860) (join_sums term (lo:=1083282) (a:=429) (b:=430) r1083282 r1083711) (join_sums term (lo:=1084141) (a:=430) (b:=430) r1084141 r1084571))))))))

private theorem rows : blockSum term 0 1085001 4999601650 :=
  join_sums term (lo:=0) (a:=975001) (b:=110000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 1085000).filter (975000 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=4999601650 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From975000To1085000
