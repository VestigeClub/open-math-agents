import certificates.«prime-table-67545646-94085731»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 117,892 through 164,215

The sum covers 3,908 primes. Their quotient counts are checked by the
certified prime-counting table through 94,085,731.
-/
open Finset
namespace Correction11092009835083From117892To164215

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


private abbrev term := contribution 11092009835083 117892 RangePrimeQ67545646To94085731.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 117893 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 117892 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r117893 : blockSum term 117893 723 303151755 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r118616 : blockSum term 118616 724 339075612 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r119340 : blockSum term 119340 724 331700466 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r120064 : blockSum term 120064 724 324536821 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r120788 : blockSum term 120788 723 365068046 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r121511 : blockSum term 121511 724 331402151 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r122235 : blockSum term 122235 724 324348998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r122959 : blockSum term 122959 724 322485732 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r123683 : blockSum term 123683 723 315597257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r124406 : blockSum term 124406 724 313872608 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r125130 : blockSum term 125130 724 317278382 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r125854 : blockSum term 125854 724 315569958 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r126578 : blockSum term 126578 723 288514560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r127301 : blockSum term 127301 724 312159127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r128025 : blockSum term 128025 724 320504030 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r128749 : blockSum term 128749 724 323795080 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r129473 : blockSum term 129473 723 287444516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r130196 : blockSum term 130196 724 310618725 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r130920 : blockSum term 130920 724 289284069 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r131644 : blockSum term 131644 724 292682812 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r132368 : blockSum term 132368 723 310595185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r133091 : blockSum term 133091 724 299364042 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r133815 : blockSum term 133815 724 283380129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r134539 : blockSum term 134539 724 267603103 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r135263 : blockSum term 135263 723 318631055 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r135986 : blockSum term 135986 724 321678399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r136710 : blockSum term 136710 724 291852448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r137434 : blockSum term 137434 724 276340533 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r138158 : blockSum term 138158 724 288989182 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r138882 : blockSum term 138882 724 273596430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r139606 : blockSum term 139606 724 276901907 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r140330 : blockSum term 140330 724 293971642 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r141054 : blockSum term 141054 723 306185388 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r141777 : blockSum term 141777 724 254750132 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r142501 : blockSum term 142501 724 249025651 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r143225 : blockSum term 143225 724 274831451 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r143949 : blockSum term 143949 723 260026402 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r144672 : blockSum term 144672 724 245457471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r145396 : blockSum term 145396 724 306480804 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r146120 : blockSum term 146120 724 256385949 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r146844 : blockSum term 146844 723 272788802 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r147567 : blockSum term 147567 724 245284103 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r148291 : blockSum term 148291 724 270270909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r149015 : blockSum term 149015 724 295125669 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r149739 : blockSum term 149739 724 272140919 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r150463 : blockSum term 150463 724 253688338 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r151187 : blockSum term 151187 724 303904244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r151911 : blockSum term 151911 724 247132299 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r152635 : blockSum term 152635 723 250314878 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r153358 : blockSum term 153358 724 257623402 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r154082 : blockSum term 154082 724 252261333 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r154806 : blockSum term 154806 724 246968878 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r155530 : blockSum term 155530 723 250113992 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r156253 : blockSum term 156253 724 232352893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r156977 : blockSum term 156977 724 268562506 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r157701 : blockSum term 157701 724 234451351 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r158425 : blockSum term 158425 723 217090944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r159148 : blockSum term 159148 724 285421965 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r159872 : blockSum term 159872 724 215190625 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r160596 : blockSum term 160596 724 254765723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r161320 : blockSum term 161320 724 249604857 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r162044 : blockSum term 162044 724 228447106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r162768 : blockSum term 162768 724 247508697 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r163492 : blockSum term 163492 724 234525457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 117893 46323 18070677898 := (join_sums term (lo:=117893) (a:=23161) (b:=23162) (join_sums term (lo:=117893) (a:=11580) (b:=11581) (join_sums term (lo:=117893) (a:=5790) (b:=5790) (join_sums term (lo:=117893) (a:=2895) (b:=2895) (join_sums term (lo:=117893) (a:=1447) (b:=1448) (join_sums term (lo:=117893) (a:=723) (b:=724) r117893 r118616) (join_sums term (lo:=119340) (a:=724) (b:=724) r119340 r120064)) (join_sums term (lo:=120788) (a:=1447) (b:=1448) (join_sums term (lo:=120788) (a:=723) (b:=724) r120788 r121511) (join_sums term (lo:=122235) (a:=724) (b:=724) r122235 r122959))) (join_sums term (lo:=123683) (a:=2895) (b:=2895) (join_sums term (lo:=123683) (a:=1447) (b:=1448) (join_sums term (lo:=123683) (a:=723) (b:=724) r123683 r124406) (join_sums term (lo:=125130) (a:=724) (b:=724) r125130 r125854)) (join_sums term (lo:=126578) (a:=1447) (b:=1448) (join_sums term (lo:=126578) (a:=723) (b:=724) r126578 r127301) (join_sums term (lo:=128025) (a:=724) (b:=724) r128025 r128749)))) (join_sums term (lo:=129473) (a:=5790) (b:=5791) (join_sums term (lo:=129473) (a:=2895) (b:=2895) (join_sums term (lo:=129473) (a:=1447) (b:=1448) (join_sums term (lo:=129473) (a:=723) (b:=724) r129473 r130196) (join_sums term (lo:=130920) (a:=724) (b:=724) r130920 r131644)) (join_sums term (lo:=132368) (a:=1447) (b:=1448) (join_sums term (lo:=132368) (a:=723) (b:=724) r132368 r133091) (join_sums term (lo:=133815) (a:=724) (b:=724) r133815 r134539))) (join_sums term (lo:=135263) (a:=2895) (b:=2896) (join_sums term (lo:=135263) (a:=1447) (b:=1448) (join_sums term (lo:=135263) (a:=723) (b:=724) r135263 r135986) (join_sums term (lo:=136710) (a:=724) (b:=724) r136710 r137434)) (join_sums term (lo:=138158) (a:=1448) (b:=1448) (join_sums term (lo:=138158) (a:=724) (b:=724) r138158 r138882) (join_sums term (lo:=139606) (a:=724) (b:=724) r139606 r140330))))) (join_sums term (lo:=141054) (a:=11581) (b:=11581) (join_sums term (lo:=141054) (a:=5790) (b:=5791) (join_sums term (lo:=141054) (a:=2895) (b:=2895) (join_sums term (lo:=141054) (a:=1447) (b:=1448) (join_sums term (lo:=141054) (a:=723) (b:=724) r141054 r141777) (join_sums term (lo:=142501) (a:=724) (b:=724) r142501 r143225)) (join_sums term (lo:=143949) (a:=1447) (b:=1448) (join_sums term (lo:=143949) (a:=723) (b:=724) r143949 r144672) (join_sums term (lo:=145396) (a:=724) (b:=724) r145396 r146120))) (join_sums term (lo:=146844) (a:=2895) (b:=2896) (join_sums term (lo:=146844) (a:=1447) (b:=1448) (join_sums term (lo:=146844) (a:=723) (b:=724) r146844 r147567) (join_sums term (lo:=148291) (a:=724) (b:=724) r148291 r149015)) (join_sums term (lo:=149739) (a:=1448) (b:=1448) (join_sums term (lo:=149739) (a:=724) (b:=724) r149739 r150463) (join_sums term (lo:=151187) (a:=724) (b:=724) r151187 r151911)))) (join_sums term (lo:=152635) (a:=5790) (b:=5791) (join_sums term (lo:=152635) (a:=2895) (b:=2895) (join_sums term (lo:=152635) (a:=1447) (b:=1448) (join_sums term (lo:=152635) (a:=723) (b:=724) r152635 r153358) (join_sums term (lo:=154082) (a:=724) (b:=724) r154082 r154806)) (join_sums term (lo:=155530) (a:=1447) (b:=1448) (join_sums term (lo:=155530) (a:=723) (b:=724) r155530 r156253) (join_sums term (lo:=156977) (a:=724) (b:=724) r156977 r157701))) (join_sums term (lo:=158425) (a:=2895) (b:=2896) (join_sums term (lo:=158425) (a:=1447) (b:=1448) (join_sums term (lo:=158425) (a:=723) (b:=724) r158425 r159148) (join_sums term (lo:=159872) (a:=724) (b:=724) r159872 r160596)) (join_sums term (lo:=161320) (a:=1448) (b:=1448) (join_sums term (lo:=161320) (a:=724) (b:=724) r161320 r162044) (join_sums term (lo:=162768) (a:=724) (b:=724) r162768 r163492))))))

private theorem rows : blockSum term 0 164216 18070677898 :=
  join_sums term (lo:=0) (a:=117893) (b:=46323) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 164215).filter (117892 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=18070677898 :=
  right_from_blocks (l:=67545646) (b:=94085731) (small:=745089)
    RangePrimeQ67545646To94085731.fast FastDenseA26.fast FastDenseA26.prime QuotientQ67545646To94085731.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From117892To164215
