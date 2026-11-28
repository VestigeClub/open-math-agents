import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 2,910,000 through 3,030,000

The sum covers 8,018 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From2910000To3030000

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


private abbrev term := contribution 30110134441897 2910000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 2910001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 2910000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r2910001 : blockSum term 2910001 468 14732120 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2910469 : blockSum term 2910469 469 13778086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2910938 : blockSum term 2910938 469 15199363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2911407 : blockSum term 2911407 469 13770879 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2911876 : blockSum term 2911876 468 13291960 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2912344 : blockSum term 2912344 469 14237326 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2912813 : blockSum term 2912813 469 15656323 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2913282 : blockSum term 2913282 469 14703604 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2913751 : blockSum term 2913751 468 16121750 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2914219 : blockSum term 2914219 469 12324946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2914688 : blockSum term 2914688 469 12795261 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2915157 : blockSum term 2915157 469 17529338 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2915626 : blockSum term 2915626 468 12314304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2916094 : blockSum term 2916094 469 17519249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2916563 : blockSum term 2916563 469 11834057 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2917032 : blockSum term 2917032 469 16089559 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2917501 : blockSum term 2917501 468 14192822 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2917969 : blockSum term 2917969 469 17026082 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2918438 : blockSum term 2918438 469 16075564 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2918907 : blockSum term 2918907 469 15125518 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2919376 : blockSum term 2919376 468 16066220 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2919844 : blockSum term 2919844 469 14644675 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2920313 : blockSum term 2920313 469 16530375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2920782 : blockSum term 2920782 469 16524945 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2921251 : blockSum term 2921251 468 10384123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2921719 : blockSum term 2921719 469 15572155 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2922188 : blockSum term 2922188 469 16982767 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2922657 : blockSum term 2922657 469 17449634 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2923126 : blockSum term 2923126 468 14144404 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2923594 : blockSum term 2923594 469 11312590 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2924063 : blockSum term 2924063 469 16964032 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2924532 : blockSum term 2924532 469 13661563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2925001 : blockSum term 2925001 468 16483494 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2925469 : blockSum term 2925469 469 16007797 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2925938 : blockSum term 2925938 469 15061736 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2926407 : blockSum term 2926407 469 14586824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2926876 : blockSum term 2926876 468 13171522 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2927344 : blockSum term 2927344 469 13167616 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2927813 : blockSum term 2927813 469 13164245 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2928282 : blockSum term 2928282 469 13161049 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2928751 : blockSum term 2928751 468 14097147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2929219 : blockSum term 2929219 469 15972411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2929688 : blockSum term 2929688 469 14559076 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2930157 : blockSum term 2930157 469 16432841 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2930626 : blockSum term 2930626 468 15958554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2931094 : blockSum term 2931094 469 12669433 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2931563 : blockSum term 2931563 469 14073300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2932032 : blockSum term 2932032 469 15006811 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2932501 : blockSum term 2932501 468 15940091 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2932969 : blockSum term 2932969 469 11248716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2933438 : blockSum term 2933438 469 14525466 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2933907 : blockSum term 2933907 469 13116144 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2934376 : blockSum term 2934376 468 14517156 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2934844 : blockSum term 2934844 469 15917410 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2935313 : blockSum term 2935313 469 15444635 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2935782 : blockSum term 2935782 469 15440387 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2936251 : blockSum term 2936251 468 15435953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2936719 : blockSum term 2936719 469 16366549 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2937188 : blockSum term 2937188 469 15894053 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2937657 : blockSum term 2937657 469 15889611 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2938126 : blockSum term 2938126 468 15885036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2938594 : blockSum term 2938594 469 14012360 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2939063 : blockSum term 2939063 469 15876358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2939532 : blockSum term 2939532 469 14937820 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2940001 : blockSum term 2940001 468 14467185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2940469 : blockSum term 2940469 469 13529915 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2940938 : blockSum term 2940938 469 12593334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2941407 : blockSum term 2941407 469 13522692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2941876 : blockSum term 2941876 468 13518841 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2942344 : blockSum term 2942344 469 13514844 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2942813 : blockSum term 2942813 469 10249839 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2943282 : blockSum term 2943282 469 14904896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2943751 : blockSum term 2943751 468 14900569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2944219 : blockSum term 2944219 469 16292581 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2944688 : blockSum term 2944688 469 13495972 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2945157 : blockSum term 2945157 469 15817851 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2945626 : blockSum term 2945626 468 12557263 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2946094 : blockSum term 2946094 469 16738548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2946563 : blockSum term 2946563 469 13479923 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2947032 : blockSum term 2947032 469 12546981 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2947501 : blockSum term 2947501 468 13473017 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2947969 : blockSum term 2947969 469 14397805 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2948438 : blockSum term 2948438 469 14394083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2948907 : blockSum term 2948907 469 18103392 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2949376 : blockSum term 2949376 468 14385897 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2949844 : blockSum term 2949844 469 14845710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2950313 : blockSum term 2950313 469 12522651 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2950782 : blockSum term 2950782 469 18083324 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2951251 : blockSum term 2951251 468 14369170 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2951719 : blockSum term 2951719 469 15755529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2952188 : blockSum term 2952188 469 16214159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2952657 : blockSum term 2952657 469 13893987 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2953126 : blockSum term 2953126 468 12037975 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2953594 : blockSum term 2953594 469 14348995 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2954063 : blockSum term 2954063 469 15270588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2954532 : blockSum term 2954532 469 12490749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2955001 : blockSum term 2955001 468 13875108 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2955469 : blockSum term 2955469 469 17107721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2955938 : blockSum term 2955938 469 12018317 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2956407 : blockSum term 2956407 469 11552648 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2956876 : blockSum term 2956876 468 12473681 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2957344 : blockSum term 2957344 469 13394021 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2957813 : blockSum term 2957813 469 14775326 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2958282 : blockSum term 2958282 469 13386394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2958751 : blockSum term 2958751 468 13383093 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2959219 : blockSum term 2959219 469 15223980 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2959688 : blockSum term 2959688 469 14297387 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2960157 : blockSum term 2960157 469 17982085 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2960626 : blockSum term 2960626 468 14750440 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2961094 : blockSum term 2961094 469 11520492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2961563 : blockSum term 2961563 469 17966903 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2962032 : blockSum term 2962032 469 17500888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2962501 : blockSum term 2962501 468 13812570 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2962969 : blockSum term 2962969 469 14729316 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2963438 : blockSum term 2963438 469 13344967 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2963907 : blockSum term 2963907 469 15180979 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2964376 : blockSum term 2964376 468 14256954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2964844 : blockSum term 2964844 469 15632211 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2965313 : blockSum term 2965313 469 15628095 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2965782 : blockSum term 2965782 469 15164293 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2966251 : blockSum term 2966251 468 11024962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2966719 : blockSum term 2966719 469 15614794 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2967188 : blockSum term 2967188 469 17446553 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2967657 : blockSum term 2967657 469 13310631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2968126 : blockSum term 2968126 468 15142239 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2968594 : blockSum term 2968594 469 16513529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2969063 : blockSum term 2969063 469 12840157 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2969532 : blockSum term 2969532 469 15128535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2970001 : blockSum term 2970001 468 16040583 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2970469 : blockSum term 2970469 469 12370676 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2970938 : blockSum term 2970938 469 15573343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2971407 : blockSum term 2971407 469 10532221 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2971876 : blockSum term 2971876 468 13734073 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2972344 : blockSum term 2972344 469 14187695 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2972813 : blockSum term 2972813 469 16471451 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2973282 : blockSum term 2973282 469 13722472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2973751 : blockSum term 2973751 468 12346408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2974219 : blockSum term 2974219 469 14628290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2974688 : blockSum term 2974688 469 15081378 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2975157 : blockSum term 2975157 469 15077228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2975626 : blockSum term 2975626 468 13245846 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2976094 : blockSum term 2976094 469 13698742 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2976563 : blockSum term 2976563 469 15520865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2977032 : blockSum term 2977032 469 11409314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2977501 : blockSum term 2977501 468 15968241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2977969 : blockSum term 2977969 469 15051257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2978438 : blockSum term 2978438 469 10943569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2978907 : blockSum term 2978907 469 15954486 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2979376 : blockSum term 2979376 468 15038390 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2979844 : blockSum term 2979844 469 15034281 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2980313 : blockSum term 2980313 469 14574751 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2980782 : blockSum term 2980782 469 16847408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2981251 : blockSum term 2981251 468 15021321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2981719 : blockSum term 2981719 469 15016934 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2982188 : blockSum term 2982188 469 13647733 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2982657 : blockSum term 2982657 469 15463300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2983126 : blockSum term 2983126 468 15913155 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2983594 : blockSum term 2983594 469 12272549 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2984063 : blockSum term 2984063 469 14086868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2984532 : blockSum term 2984532 469 15900178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2985001 : blockSum term 2985001 468 15441224 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2985469 : blockSum term 2985469 469 14074943 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2985938 : blockSum term 2985938 469 14524725 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2986407 : blockSum term 2986407 469 18150235 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2986876 : blockSum term 2986876 468 9979734 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2987344 : blockSum term 2987344 469 13151297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2987813 : blockSum term 2987813 469 14507736 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2988282 : blockSum term 2988282 469 14503346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2988751 : blockSum term 2988751 468 13593011 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2989219 : blockSum term 2989219 469 11777437 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2989688 : blockSum term 2989688 469 11321142 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2990157 : blockSum term 2990157 469 12676521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2990626 : blockSum term 2990626 468 16293871 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2991094 : blockSum term 2991094 469 14026999 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2991563 : blockSum term 2991563 469 14023188 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2992032 : blockSum term 2992032 469 15375838 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2992501 : blockSum term 2992501 468 15822837 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2992969 : blockSum term 2992969 469 14010508 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2993438 : blockSum term 2993438 469 14458232 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2993907 : blockSum term 2993907 469 12195904 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2994376 : blockSum term 2994376 468 14450457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2994844 : blockSum term 2994844 469 14446119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2995313 : blockSum term 2995313 469 14893131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2995782 : blockSum term 2995782 469 14437521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2996251 : blockSum term 2996251 468 14884473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2996719 : blockSum term 2996719 469 11723932 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2997188 : blockSum term 2997188 469 16228269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2997657 : blockSum term 2997657 469 17124624 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2998126 : blockSum term 2998126 468 15317677 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2998594 : blockSum term 2998594 469 13961841 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2999063 : blockSum term 2999063 469 13057499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2999532 : blockSum term 2999532 469 15304024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3000001 : blockSum term 3000001 468 12149920 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3000469 : blockSum term 3000469 469 13045951 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3000938 : blockSum term 3000938 469 14841391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3001407 : blockSum term 3001407 469 13937827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3001876 : blockSum term 3001876 468 14383476 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3002344 : blockSum term 3002344 469 16176616 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3002813 : blockSum term 3002813 469 15722602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3003282 : blockSum term 3003282 469 15718165 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3003751 : blockSum term 3003751 468 13917656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3004219 : blockSum term 3004219 469 14811084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3004688 : blockSum term 3004688 469 13011645 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3005157 : blockSum term 3005157 469 15250849 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3005626 : blockSum term 3005626 468 12556083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3006094 : blockSum term 3006094 469 11655920 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3006563 : blockSum term 3006563 469 14341540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3007032 : blockSum term 3007032 469 14785451 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3007501 : blockSum term 3007501 468 13437603 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3007969 : blockSum term 3007969 469 16568126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3008438 : blockSum term 3008438 469 12534415 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3008907 : blockSum term 3008907 469 12083358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3009376 : blockSum term 3009376 468 13869822 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3009844 : blockSum term 3009844 469 13418660 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3010313 : blockSum term 3010313 469 15650333 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3010782 : blockSum term 3010782 469 16092545 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3011251 : blockSum term 3011251 468 14747724 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3011719 : blockSum term 3011719 469 16083298 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3012188 : blockSum term 3012188 469 16525408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3012657 : blockSum term 3012657 469 11162365 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3013126 : blockSum term 3013126 468 13837654 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3013594 : blockSum term 3013594 469 13387406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3014063 : blockSum term 3014063 469 12045768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3014532 : blockSum term 3014532 469 16502579 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3015001 : blockSum term 3015001 468 11147313 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3015469 : blockSum term 3015469 469 15155832 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3015938 : blockSum term 3015938 469 12477873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3016407 : blockSum term 3016407 469 12028917 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3016876 : blockSum term 3016876 468 14252605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3017344 : blockSum term 3017344 469 15139171 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3017813 : blockSum term 3017813 469 12909183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3018282 : blockSum term 3018282 469 14685521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3018751 : blockSum term 3018751 468 8897551 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3019219 : blockSum term 3019219 469 14232891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3019688 : blockSum term 3019688 469 12450469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3020157 : blockSum term 3020157 469 17336349 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3020626 : blockSum term 3020626 468 15997935 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3021094 : blockSum term 3021094 469 11550466 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3021563 : blockSum term 3021563 469 15100428 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3022032 : blockSum term 3022032 469 13320271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3022501 : blockSum term 3022501 468 12872298 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3022969 : blockSum term 3022969 469 11093807 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3023438 : blockSum term 3023438 469 15527262 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3023907 : blockSum term 3023907 469 10644414 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3024376 : blockSum term 3024376 468 15962040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3024844 : blockSum term 3024844 469 15070786 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3025313 : blockSum term 3025313 469 13294131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3025782 : blockSum term 3025782 469 14618875 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3026251 : blockSum term 3026251 468 13286246 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3026719 : blockSum term 3026719 469 16824502 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3027188 : blockSum term 3027188 469 14163903 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3027657 : blockSum term 3027657 469 11947610 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3028126 : blockSum term 3028126 468 15483271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3028594 : blockSum term 3028594 469 14152127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3029063 : blockSum term 3029063 469 11053195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3029532 : blockSum term 3029532 469 11491885 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 2910001 120000 3675810397 := (join_sums term (lo:=2910001) (a:=60000) (b:=60000) (join_sums term (lo:=2910001) (a:=30000) (b:=30000) (join_sums term (lo:=2910001) (a:=15000) (b:=15000) (join_sums term (lo:=2910001) (a:=7500) (b:=7500) (join_sums term (lo:=2910001) (a:=3750) (b:=3750) (join_sums term (lo:=2910001) (a:=1875) (b:=1875) (join_sums term (lo:=2910001) (a:=937) (b:=938) (join_sums term (lo:=2910001) (a:=468) (b:=469) r2910001 r2910469) (join_sums term (lo:=2910938) (a:=469) (b:=469) r2910938 r2911407)) (join_sums term (lo:=2911876) (a:=937) (b:=938) (join_sums term (lo:=2911876) (a:=468) (b:=469) r2911876 r2912344) (join_sums term (lo:=2912813) (a:=469) (b:=469) r2912813 r2913282))) (join_sums term (lo:=2913751) (a:=1875) (b:=1875) (join_sums term (lo:=2913751) (a:=937) (b:=938) (join_sums term (lo:=2913751) (a:=468) (b:=469) r2913751 r2914219) (join_sums term (lo:=2914688) (a:=469) (b:=469) r2914688 r2915157)) (join_sums term (lo:=2915626) (a:=937) (b:=938) (join_sums term (lo:=2915626) (a:=468) (b:=469) r2915626 r2916094) (join_sums term (lo:=2916563) (a:=469) (b:=469) r2916563 r2917032)))) (join_sums term (lo:=2917501) (a:=3750) (b:=3750) (join_sums term (lo:=2917501) (a:=1875) (b:=1875) (join_sums term (lo:=2917501) (a:=937) (b:=938) (join_sums term (lo:=2917501) (a:=468) (b:=469) r2917501 r2917969) (join_sums term (lo:=2918438) (a:=469) (b:=469) r2918438 r2918907)) (join_sums term (lo:=2919376) (a:=937) (b:=938) (join_sums term (lo:=2919376) (a:=468) (b:=469) r2919376 r2919844) (join_sums term (lo:=2920313) (a:=469) (b:=469) r2920313 r2920782))) (join_sums term (lo:=2921251) (a:=1875) (b:=1875) (join_sums term (lo:=2921251) (a:=937) (b:=938) (join_sums term (lo:=2921251) (a:=468) (b:=469) r2921251 r2921719) (join_sums term (lo:=2922188) (a:=469) (b:=469) r2922188 r2922657)) (join_sums term (lo:=2923126) (a:=937) (b:=938) (join_sums term (lo:=2923126) (a:=468) (b:=469) r2923126 r2923594) (join_sums term (lo:=2924063) (a:=469) (b:=469) r2924063 r2924532))))) (join_sums term (lo:=2925001) (a:=7500) (b:=7500) (join_sums term (lo:=2925001) (a:=3750) (b:=3750) (join_sums term (lo:=2925001) (a:=1875) (b:=1875) (join_sums term (lo:=2925001) (a:=937) (b:=938) (join_sums term (lo:=2925001) (a:=468) (b:=469) r2925001 r2925469) (join_sums term (lo:=2925938) (a:=469) (b:=469) r2925938 r2926407)) (join_sums term (lo:=2926876) (a:=937) (b:=938) (join_sums term (lo:=2926876) (a:=468) (b:=469) r2926876 r2927344) (join_sums term (lo:=2927813) (a:=469) (b:=469) r2927813 r2928282))) (join_sums term (lo:=2928751) (a:=1875) (b:=1875) (join_sums term (lo:=2928751) (a:=937) (b:=938) (join_sums term (lo:=2928751) (a:=468) (b:=469) r2928751 r2929219) (join_sums term (lo:=2929688) (a:=469) (b:=469) r2929688 r2930157)) (join_sums term (lo:=2930626) (a:=937) (b:=938) (join_sums term (lo:=2930626) (a:=468) (b:=469) r2930626 r2931094) (join_sums term (lo:=2931563) (a:=469) (b:=469) r2931563 r2932032)))) (join_sums term (lo:=2932501) (a:=3750) (b:=3750) (join_sums term (lo:=2932501) (a:=1875) (b:=1875) (join_sums term (lo:=2932501) (a:=937) (b:=938) (join_sums term (lo:=2932501) (a:=468) (b:=469) r2932501 r2932969) (join_sums term (lo:=2933438) (a:=469) (b:=469) r2933438 r2933907)) (join_sums term (lo:=2934376) (a:=937) (b:=938) (join_sums term (lo:=2934376) (a:=468) (b:=469) r2934376 r2934844) (join_sums term (lo:=2935313) (a:=469) (b:=469) r2935313 r2935782))) (join_sums term (lo:=2936251) (a:=1875) (b:=1875) (join_sums term (lo:=2936251) (a:=937) (b:=938) (join_sums term (lo:=2936251) (a:=468) (b:=469) r2936251 r2936719) (join_sums term (lo:=2937188) (a:=469) (b:=469) r2937188 r2937657)) (join_sums term (lo:=2938126) (a:=937) (b:=938) (join_sums term (lo:=2938126) (a:=468) (b:=469) r2938126 r2938594) (join_sums term (lo:=2939063) (a:=469) (b:=469) r2939063 r2939532)))))) (join_sums term (lo:=2940001) (a:=15000) (b:=15000) (join_sums term (lo:=2940001) (a:=7500) (b:=7500) (join_sums term (lo:=2940001) (a:=3750) (b:=3750) (join_sums term (lo:=2940001) (a:=1875) (b:=1875) (join_sums term (lo:=2940001) (a:=937) (b:=938) (join_sums term (lo:=2940001) (a:=468) (b:=469) r2940001 r2940469) (join_sums term (lo:=2940938) (a:=469) (b:=469) r2940938 r2941407)) (join_sums term (lo:=2941876) (a:=937) (b:=938) (join_sums term (lo:=2941876) (a:=468) (b:=469) r2941876 r2942344) (join_sums term (lo:=2942813) (a:=469) (b:=469) r2942813 r2943282))) (join_sums term (lo:=2943751) (a:=1875) (b:=1875) (join_sums term (lo:=2943751) (a:=937) (b:=938) (join_sums term (lo:=2943751) (a:=468) (b:=469) r2943751 r2944219) (join_sums term (lo:=2944688) (a:=469) (b:=469) r2944688 r2945157)) (join_sums term (lo:=2945626) (a:=937) (b:=938) (join_sums term (lo:=2945626) (a:=468) (b:=469) r2945626 r2946094) (join_sums term (lo:=2946563) (a:=469) (b:=469) r2946563 r2947032)))) (join_sums term (lo:=2947501) (a:=3750) (b:=3750) (join_sums term (lo:=2947501) (a:=1875) (b:=1875) (join_sums term (lo:=2947501) (a:=937) (b:=938) (join_sums term (lo:=2947501) (a:=468) (b:=469) r2947501 r2947969) (join_sums term (lo:=2948438) (a:=469) (b:=469) r2948438 r2948907)) (join_sums term (lo:=2949376) (a:=937) (b:=938) (join_sums term (lo:=2949376) (a:=468) (b:=469) r2949376 r2949844) (join_sums term (lo:=2950313) (a:=469) (b:=469) r2950313 r2950782))) (join_sums term (lo:=2951251) (a:=1875) (b:=1875) (join_sums term (lo:=2951251) (a:=937) (b:=938) (join_sums term (lo:=2951251) (a:=468) (b:=469) r2951251 r2951719) (join_sums term (lo:=2952188) (a:=469) (b:=469) r2952188 r2952657)) (join_sums term (lo:=2953126) (a:=937) (b:=938) (join_sums term (lo:=2953126) (a:=468) (b:=469) r2953126 r2953594) (join_sums term (lo:=2954063) (a:=469) (b:=469) r2954063 r2954532))))) (join_sums term (lo:=2955001) (a:=7500) (b:=7500) (join_sums term (lo:=2955001) (a:=3750) (b:=3750) (join_sums term (lo:=2955001) (a:=1875) (b:=1875) (join_sums term (lo:=2955001) (a:=937) (b:=938) (join_sums term (lo:=2955001) (a:=468) (b:=469) r2955001 r2955469) (join_sums term (lo:=2955938) (a:=469) (b:=469) r2955938 r2956407)) (join_sums term (lo:=2956876) (a:=937) (b:=938) (join_sums term (lo:=2956876) (a:=468) (b:=469) r2956876 r2957344) (join_sums term (lo:=2957813) (a:=469) (b:=469) r2957813 r2958282))) (join_sums term (lo:=2958751) (a:=1875) (b:=1875) (join_sums term (lo:=2958751) (a:=937) (b:=938) (join_sums term (lo:=2958751) (a:=468) (b:=469) r2958751 r2959219) (join_sums term (lo:=2959688) (a:=469) (b:=469) r2959688 r2960157)) (join_sums term (lo:=2960626) (a:=937) (b:=938) (join_sums term (lo:=2960626) (a:=468) (b:=469) r2960626 r2961094) (join_sums term (lo:=2961563) (a:=469) (b:=469) r2961563 r2962032)))) (join_sums term (lo:=2962501) (a:=3750) (b:=3750) (join_sums term (lo:=2962501) (a:=1875) (b:=1875) (join_sums term (lo:=2962501) (a:=937) (b:=938) (join_sums term (lo:=2962501) (a:=468) (b:=469) r2962501 r2962969) (join_sums term (lo:=2963438) (a:=469) (b:=469) r2963438 r2963907)) (join_sums term (lo:=2964376) (a:=937) (b:=938) (join_sums term (lo:=2964376) (a:=468) (b:=469) r2964376 r2964844) (join_sums term (lo:=2965313) (a:=469) (b:=469) r2965313 r2965782))) (join_sums term (lo:=2966251) (a:=1875) (b:=1875) (join_sums term (lo:=2966251) (a:=937) (b:=938) (join_sums term (lo:=2966251) (a:=468) (b:=469) r2966251 r2966719) (join_sums term (lo:=2967188) (a:=469) (b:=469) r2967188 r2967657)) (join_sums term (lo:=2968126) (a:=937) (b:=938) (join_sums term (lo:=2968126) (a:=468) (b:=469) r2968126 r2968594) (join_sums term (lo:=2969063) (a:=469) (b:=469) r2969063 r2969532))))))) (join_sums term (lo:=2970001) (a:=30000) (b:=30000) (join_sums term (lo:=2970001) (a:=15000) (b:=15000) (join_sums term (lo:=2970001) (a:=7500) (b:=7500) (join_sums term (lo:=2970001) (a:=3750) (b:=3750) (join_sums term (lo:=2970001) (a:=1875) (b:=1875) (join_sums term (lo:=2970001) (a:=937) (b:=938) (join_sums term (lo:=2970001) (a:=468) (b:=469) r2970001 r2970469) (join_sums term (lo:=2970938) (a:=469) (b:=469) r2970938 r2971407)) (join_sums term (lo:=2971876) (a:=937) (b:=938) (join_sums term (lo:=2971876) (a:=468) (b:=469) r2971876 r2972344) (join_sums term (lo:=2972813) (a:=469) (b:=469) r2972813 r2973282))) (join_sums term (lo:=2973751) (a:=1875) (b:=1875) (join_sums term (lo:=2973751) (a:=937) (b:=938) (join_sums term (lo:=2973751) (a:=468) (b:=469) r2973751 r2974219) (join_sums term (lo:=2974688) (a:=469) (b:=469) r2974688 r2975157)) (join_sums term (lo:=2975626) (a:=937) (b:=938) (join_sums term (lo:=2975626) (a:=468) (b:=469) r2975626 r2976094) (join_sums term (lo:=2976563) (a:=469) (b:=469) r2976563 r2977032)))) (join_sums term (lo:=2977501) (a:=3750) (b:=3750) (join_sums term (lo:=2977501) (a:=1875) (b:=1875) (join_sums term (lo:=2977501) (a:=937) (b:=938) (join_sums term (lo:=2977501) (a:=468) (b:=469) r2977501 r2977969) (join_sums term (lo:=2978438) (a:=469) (b:=469) r2978438 r2978907)) (join_sums term (lo:=2979376) (a:=937) (b:=938) (join_sums term (lo:=2979376) (a:=468) (b:=469) r2979376 r2979844) (join_sums term (lo:=2980313) (a:=469) (b:=469) r2980313 r2980782))) (join_sums term (lo:=2981251) (a:=1875) (b:=1875) (join_sums term (lo:=2981251) (a:=937) (b:=938) (join_sums term (lo:=2981251) (a:=468) (b:=469) r2981251 r2981719) (join_sums term (lo:=2982188) (a:=469) (b:=469) r2982188 r2982657)) (join_sums term (lo:=2983126) (a:=937) (b:=938) (join_sums term (lo:=2983126) (a:=468) (b:=469) r2983126 r2983594) (join_sums term (lo:=2984063) (a:=469) (b:=469) r2984063 r2984532))))) (join_sums term (lo:=2985001) (a:=7500) (b:=7500) (join_sums term (lo:=2985001) (a:=3750) (b:=3750) (join_sums term (lo:=2985001) (a:=1875) (b:=1875) (join_sums term (lo:=2985001) (a:=937) (b:=938) (join_sums term (lo:=2985001) (a:=468) (b:=469) r2985001 r2985469) (join_sums term (lo:=2985938) (a:=469) (b:=469) r2985938 r2986407)) (join_sums term (lo:=2986876) (a:=937) (b:=938) (join_sums term (lo:=2986876) (a:=468) (b:=469) r2986876 r2987344) (join_sums term (lo:=2987813) (a:=469) (b:=469) r2987813 r2988282))) (join_sums term (lo:=2988751) (a:=1875) (b:=1875) (join_sums term (lo:=2988751) (a:=937) (b:=938) (join_sums term (lo:=2988751) (a:=468) (b:=469) r2988751 r2989219) (join_sums term (lo:=2989688) (a:=469) (b:=469) r2989688 r2990157)) (join_sums term (lo:=2990626) (a:=937) (b:=938) (join_sums term (lo:=2990626) (a:=468) (b:=469) r2990626 r2991094) (join_sums term (lo:=2991563) (a:=469) (b:=469) r2991563 r2992032)))) (join_sums term (lo:=2992501) (a:=3750) (b:=3750) (join_sums term (lo:=2992501) (a:=1875) (b:=1875) (join_sums term (lo:=2992501) (a:=937) (b:=938) (join_sums term (lo:=2992501) (a:=468) (b:=469) r2992501 r2992969) (join_sums term (lo:=2993438) (a:=469) (b:=469) r2993438 r2993907)) (join_sums term (lo:=2994376) (a:=937) (b:=938) (join_sums term (lo:=2994376) (a:=468) (b:=469) r2994376 r2994844) (join_sums term (lo:=2995313) (a:=469) (b:=469) r2995313 r2995782))) (join_sums term (lo:=2996251) (a:=1875) (b:=1875) (join_sums term (lo:=2996251) (a:=937) (b:=938) (join_sums term (lo:=2996251) (a:=468) (b:=469) r2996251 r2996719) (join_sums term (lo:=2997188) (a:=469) (b:=469) r2997188 r2997657)) (join_sums term (lo:=2998126) (a:=937) (b:=938) (join_sums term (lo:=2998126) (a:=468) (b:=469) r2998126 r2998594) (join_sums term (lo:=2999063) (a:=469) (b:=469) r2999063 r2999532)))))) (join_sums term (lo:=3000001) (a:=15000) (b:=15000) (join_sums term (lo:=3000001) (a:=7500) (b:=7500) (join_sums term (lo:=3000001) (a:=3750) (b:=3750) (join_sums term (lo:=3000001) (a:=1875) (b:=1875) (join_sums term (lo:=3000001) (a:=937) (b:=938) (join_sums term (lo:=3000001) (a:=468) (b:=469) r3000001 r3000469) (join_sums term (lo:=3000938) (a:=469) (b:=469) r3000938 r3001407)) (join_sums term (lo:=3001876) (a:=937) (b:=938) (join_sums term (lo:=3001876) (a:=468) (b:=469) r3001876 r3002344) (join_sums term (lo:=3002813) (a:=469) (b:=469) r3002813 r3003282))) (join_sums term (lo:=3003751) (a:=1875) (b:=1875) (join_sums term (lo:=3003751) (a:=937) (b:=938) (join_sums term (lo:=3003751) (a:=468) (b:=469) r3003751 r3004219) (join_sums term (lo:=3004688) (a:=469) (b:=469) r3004688 r3005157)) (join_sums term (lo:=3005626) (a:=937) (b:=938) (join_sums term (lo:=3005626) (a:=468) (b:=469) r3005626 r3006094) (join_sums term (lo:=3006563) (a:=469) (b:=469) r3006563 r3007032)))) (join_sums term (lo:=3007501) (a:=3750) (b:=3750) (join_sums term (lo:=3007501) (a:=1875) (b:=1875) (join_sums term (lo:=3007501) (a:=937) (b:=938) (join_sums term (lo:=3007501) (a:=468) (b:=469) r3007501 r3007969) (join_sums term (lo:=3008438) (a:=469) (b:=469) r3008438 r3008907)) (join_sums term (lo:=3009376) (a:=937) (b:=938) (join_sums term (lo:=3009376) (a:=468) (b:=469) r3009376 r3009844) (join_sums term (lo:=3010313) (a:=469) (b:=469) r3010313 r3010782))) (join_sums term (lo:=3011251) (a:=1875) (b:=1875) (join_sums term (lo:=3011251) (a:=937) (b:=938) (join_sums term (lo:=3011251) (a:=468) (b:=469) r3011251 r3011719) (join_sums term (lo:=3012188) (a:=469) (b:=469) r3012188 r3012657)) (join_sums term (lo:=3013126) (a:=937) (b:=938) (join_sums term (lo:=3013126) (a:=468) (b:=469) r3013126 r3013594) (join_sums term (lo:=3014063) (a:=469) (b:=469) r3014063 r3014532))))) (join_sums term (lo:=3015001) (a:=7500) (b:=7500) (join_sums term (lo:=3015001) (a:=3750) (b:=3750) (join_sums term (lo:=3015001) (a:=1875) (b:=1875) (join_sums term (lo:=3015001) (a:=937) (b:=938) (join_sums term (lo:=3015001) (a:=468) (b:=469) r3015001 r3015469) (join_sums term (lo:=3015938) (a:=469) (b:=469) r3015938 r3016407)) (join_sums term (lo:=3016876) (a:=937) (b:=938) (join_sums term (lo:=3016876) (a:=468) (b:=469) r3016876 r3017344) (join_sums term (lo:=3017813) (a:=469) (b:=469) r3017813 r3018282))) (join_sums term (lo:=3018751) (a:=1875) (b:=1875) (join_sums term (lo:=3018751) (a:=937) (b:=938) (join_sums term (lo:=3018751) (a:=468) (b:=469) r3018751 r3019219) (join_sums term (lo:=3019688) (a:=469) (b:=469) r3019688 r3020157)) (join_sums term (lo:=3020626) (a:=937) (b:=938) (join_sums term (lo:=3020626) (a:=468) (b:=469) r3020626 r3021094) (join_sums term (lo:=3021563) (a:=469) (b:=469) r3021563 r3022032)))) (join_sums term (lo:=3022501) (a:=3750) (b:=3750) (join_sums term (lo:=3022501) (a:=1875) (b:=1875) (join_sums term (lo:=3022501) (a:=937) (b:=938) (join_sums term (lo:=3022501) (a:=468) (b:=469) r3022501 r3022969) (join_sums term (lo:=3023438) (a:=469) (b:=469) r3023438 r3023907)) (join_sums term (lo:=3024376) (a:=937) (b:=938) (join_sums term (lo:=3024376) (a:=468) (b:=469) r3024376 r3024844) (join_sums term (lo:=3025313) (a:=469) (b:=469) r3025313 r3025782))) (join_sums term (lo:=3026251) (a:=1875) (b:=1875) (join_sums term (lo:=3026251) (a:=937) (b:=938) (join_sums term (lo:=3026251) (a:=468) (b:=469) r3026251 r3026719) (join_sums term (lo:=3027188) (a:=469) (b:=469) r3027188 r3027657)) (join_sums term (lo:=3028126) (a:=937) (b:=938) (join_sums term (lo:=3028126) (a:=468) (b:=469) r3028126 r3028594) (join_sums term (lo:=3029063) (a:=469) (b:=469) r3029063 r3029532))))))))

private theorem rows : blockSum term 0 3030001 3675810397 :=
  join_sums term (lo:=0) (a:=2910001) (b:=120000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 3030000).filter (2910000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=3675810397 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From2910000To3030000
