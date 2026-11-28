import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 2,790,000 through 2,910,000

The sum covers 8,112 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From2790000To2910000

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


private abbrev term := contribution 30110134441897 2790000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 2790001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 2790000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r2790001 : blockSum term 2790001 468 16860259 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2790469 : blockSum term 2790469 469 12258512 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2790938 : blockSum term 2790938 469 16851246 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2791407 : blockSum term 2791407 469 17867635 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2791876 : blockSum term 2791876 468 19393563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2792344 : blockSum term 2792344 469 15306408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2792813 : blockSum term 2792813 469 17852365 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2793282 : blockSum term 2793282 469 14277965 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2793751 : blockSum term 2793751 468 13254153 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2794219 : blockSum term 2794219 469 18347292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2794688 : blockSum term 2794688 469 14775252 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2795157 : blockSum term 2795157 469 19355000 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2795626 : blockSum term 2795626 468 13748463 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2796094 : blockSum term 2796094 469 12727029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2796563 : blockSum term 2796563 469 14250662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2797032 : blockSum term 2797032 469 18825603 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2797501 : blockSum term 2797501 468 13733792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2797969 : blockSum term 2797969 469 16781410 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2798438 : blockSum term 2798438 469 17285065 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2798907 : blockSum term 2798907 469 19312962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2799376 : blockSum term 2799376 468 17275046 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2799844 : blockSum term 2799844 469 17270464 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2800313 : blockSum term 2800313 469 16250016 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2800782 : blockSum term 2800782 469 14722413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2801251 : blockSum term 2801251 468 16748203 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2801719 : blockSum term 2801719 469 16743248 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2802188 : blockSum term 2802188 469 14709957 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2802657 : blockSum term 2802657 469 20283578 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2803126 : blockSum term 2803126 468 13687568 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2803594 : blockSum term 2803594 469 20778893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2804063 : blockSum term 2804063 469 18239455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2804532 : blockSum term 2804532 469 14688412 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2805001 : blockSum term 2805001 468 16204044 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2805469 : blockSum term 2805469 469 14680758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2805938 : blockSum term 2805938 469 18219176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2806407 : blockSum term 2806407 469 15684414 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2806876 : blockSum term 2806876 468 12139599 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2807344 : blockSum term 2807344 469 13147731 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2807813 : blockSum term 2807813 469 15671952 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2808282 : blockSum term 2808282 469 20721590 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2808751 : blockSum term 2808751 468 15157862 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2809219 : blockSum term 2809219 469 21214622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2809688 : blockSum term 2809688 469 16158774 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2810157 : blockSum term 2810157 469 16658843 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2810626 : blockSum term 2810626 468 16653821 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2811094 : blockSum term 2811094 469 19676066 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2811563 : blockSum term 2811563 469 15635357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2812032 : blockSum term 2812032 469 16134812 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2812501 : blockSum term 2812501 468 17642309 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2812969 : blockSum term 2812969 469 17133265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2813438 : blockSum term 2813438 469 18639704 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2813907 : blockSum term 2813907 469 14101859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2814376 : blockSum term 2814376 468 17622007 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2814844 : blockSum term 2814844 469 13590479 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2815313 : blockSum term 2815313 469 14593340 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2815782 : blockSum term 2815782 469 16601193 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2816251 : blockSum term 2816251 468 15087787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2816719 : blockSum term 2816719 469 15586478 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2817188 : blockSum term 2817188 469 18597878 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2817657 : blockSum term 2817657 469 14070276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2818126 : blockSum term 2818126 468 18084664 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2818594 : blockSum term 2818594 469 15066274 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2819063 : blockSum term 2819063 469 16568047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2819532 : blockSum term 2819532 469 16563591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2820001 : blockSum term 2820001 468 15555478 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2820469 : blockSum term 2820469 469 19563618 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2820938 : blockSum term 2820938 469 13038971 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2821407 : blockSum term 2821407 469 17546856 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2821876 : blockSum term 2821876 468 16539166 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2822344 : blockSum term 2822344 469 17536396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2822813 : blockSum term 2822813 469 15527944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2823282 : blockSum term 2823282 469 17025781 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2823751 : blockSum term 2823751 468 16520270 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2824219 : blockSum term 2824219 469 16515434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2824688 : blockSum term 2824688 469 15009749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2825157 : blockSum term 2825157 469 14005213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2825626 : blockSum term 2825626 468 15501678 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2826094 : blockSum term 2826094 469 13997687 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2826563 : blockSum term 2826563 469 13494423 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2827032 : blockSum term 2827032 469 13490504 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2827501 : blockSum term 2827501 468 12487976 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2827969 : blockSum term 2827969 469 15979550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2828438 : blockSum term 2828438 469 13977973 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2828907 : blockSum term 2828907 469 17467815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2829376 : blockSum term 2829376 468 17462914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2829844 : blockSum term 2829844 469 16460129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2830313 : blockSum term 2830313 469 14959655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2830782 : blockSum term 2830782 469 14955801 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2831251 : blockSum term 2831251 468 18938150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2831719 : blockSum term 2831719 469 15943208 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2832188 : blockSum term 2832188 469 15440722 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2832657 : blockSum term 2832657 469 17925779 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2833126 : blockSum term 2833126 468 18418621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2833594 : blockSum term 2833594 469 16920410 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2834063 : blockSum term 2834063 469 18407546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2834532 : blockSum term 2834532 469 16412962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2835001 : blockSum term 2835001 468 16407869 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2835469 : blockSum term 2835469 469 14415416 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2835938 : blockSum term 2835938 469 15902264 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2836407 : blockSum term 2836407 469 16394397 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2836876 : blockSum term 2836876 468 18376514 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2837344 : blockSum term 2837344 469 15392168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2837813 : blockSum term 2837813 469 18366040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2838282 : blockSum term 2838282 469 15383334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2838751 : blockSum term 2838751 468 14387037 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2839219 : blockSum term 2839219 469 13886851 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2839688 : blockSum term 2839688 469 16858062 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2840157 : blockSum term 2840157 469 13879796 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2840626 : blockSum term 2840626 468 14371263 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2841094 : blockSum term 2841094 469 17834628 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2841563 : blockSum term 2841563 469 13372507 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2842032 : blockSum term 2842032 469 14359187 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2842501 : blockSum term 2842501 468 19799727 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2842969 : blockSum term 2842969 469 18309602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2843438 : blockSum term 2843438 469 14841027 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2843907 : blockSum term 2843907 469 15331550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2844376 : blockSum term 2844376 468 11372048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2844844 : blockSum term 2844844 469 13345958 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2845313 : blockSum term 2845313 469 14825244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2845782 : blockSum term 2845782 469 14327007 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2846251 : blockSum term 2846251 468 12841139 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2846719 : blockSum term 2846719 469 18763036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2847188 : blockSum term 2847188 469 16783246 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2847657 : blockSum term 2847657 469 16285024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2848126 : blockSum term 2848126 468 16280230 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2848594 : blockSum term 2848594 469 19728214 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2849063 : blockSum term 2849063 469 11833460 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2849532 : blockSum term 2849532 469 18237792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2850001 : blockSum term 2850001 468 16261502 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2850469 : blockSum term 2850469 469 13301096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2850938 : blockSum term 2850938 469 16252221 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2851407 : blockSum term 2851407 469 16247416 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2851876 : blockSum term 2851876 468 13782197 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2852344 : blockSum term 2852344 469 14270208 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2852813 : blockSum term 2852813 469 16725798 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2853282 : blockSum term 2853282 469 13770259 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2853751 : blockSum term 2853751 468 16225173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2854219 : blockSum term 2854219 469 17203471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2854688 : blockSum term 2854688 469 16214907 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2855157 : blockSum term 2855157 469 17192930 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2855626 : blockSum term 2855626 468 13259161 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2856094 : blockSum term 2856094 469 13746576 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2856563 : blockSum term 2856563 469 10307135 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2857032 : blockSum term 2857032 469 17173927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2857501 : blockSum term 2857501 468 18150132 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2857969 : blockSum term 2857969 469 12750448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2858438 : blockSum term 2858438 469 15198509 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2858907 : blockSum term 2858907 469 14213808 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2859376 : blockSum term 2859376 468 13719921 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2859844 : blockSum term 2859844 469 15675874 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2860313 : blockSum term 2860313 469 15671315 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2860782 : blockSum term 2860782 469 17135791 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2861251 : blockSum term 2861251 468 15662449 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2861719 : blockSum term 2861719 469 14679564 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2862188 : blockSum term 2862188 469 16632113 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2862657 : blockSum term 2862657 469 13693320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2863126 : blockSum term 2863126 468 14667601 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2863594 : blockSum term 2863594 469 16129478 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2864063 : blockSum term 2864063 469 16125048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2864532 : blockSum term 2864532 469 14166672 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2865001 : blockSum term 2865001 468 14162626 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2865469 : blockSum term 2865469 469 20505543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2865938 : blockSum term 2865938 469 15130386 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2866407 : blockSum term 2866407 469 18053560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2866876 : blockSum term 2866876 468 15121514 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2867344 : blockSum term 2867344 469 13654317 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2867813 : blockSum term 2867813 469 18038450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2868282 : blockSum term 2868282 469 12672028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2868751 : blockSum term 2868751 468 14130052 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2869219 : blockSum term 2869219 469 11203923 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2869688 : blockSum term 2869688 469 16070718 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2870157 : blockSum term 2870157 469 15091636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2870626 : blockSum term 2870626 468 15087557 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2871094 : blockSum term 2871094 469 13623773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2871563 : blockSum term 2871563 469 15565321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2872032 : blockSum term 2872032 469 15560839 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2872501 : blockSum term 2872501 468 15070492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2872969 : blockSum term 2872969 469 17010457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2873438 : blockSum term 2873438 469 18949041 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2873907 : blockSum term 2873907 469 13600428 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2874376 : blockSum term 2874376 468 14082190 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2874844 : blockSum term 2874844 469 12622265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2875313 : blockSum term 2875313 469 14560140 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2875782 : blockSum term 2875782 469 12129928 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2876251 : blockSum term 2876251 468 16491962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2876719 : blockSum term 2876719 469 15032368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2877188 : blockSum term 2877188 469 15997423 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2877657 : blockSum term 2877657 469 15023613 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2878126 : blockSum term 2878126 468 11143378 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2878594 : blockSum term 2878594 469 15984105 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2879063 : blockSum term 2879063 469 15495498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2879532 : blockSum term 2879532 469 14038711 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2880001 : blockSum term 2880001 468 15486339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2880469 : blockSum term 2880469 469 17417025 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2880938 : blockSum term 2880938 469 14993673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2881407 : blockSum term 2881407 469 14506332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2881876 : blockSum term 2881876 468 16435849 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2882344 : blockSum term 2882344 469 16431191 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2882813 : blockSum term 2882813 469 13527294 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2883282 : blockSum term 2883282 469 13040950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2883751 : blockSum term 2883751 468 14968813 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2884219 : blockSum term 2884219 469 16895208 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2884688 : blockSum term 2884688 469 16408123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2885157 : blockSum term 2885157 469 14956041 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2885626 : blockSum term 2885626 468 15433843 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2886094 : blockSum term 2886094 469 15429714 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2886563 : blockSum term 2886563 469 15425228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2887032 : blockSum term 2887032 469 13493392 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2887501 : blockSum term 2887501 468 15898181 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2887969 : blockSum term 2887969 469 15412129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2888438 : blockSum term 2888438 469 14926453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2888907 : blockSum term 2888907 469 16365856 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2889376 : blockSum term 2889376 468 15880133 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2889844 : blockSum term 2889844 469 14432479 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2890313 : blockSum term 2890313 469 16833111 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2890782 : blockSum term 2890782 469 13943158 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2891251 : blockSum term 2891251 468 14900664 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2891719 : blockSum term 2891719 469 12493550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2892188 : blockSum term 2892188 469 12970654 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2892657 : blockSum term 2892657 469 15848612 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2893126 : blockSum term 2893126 468 17284394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2893594 : blockSum term 2893594 469 12959919 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2894063 : blockSum term 2894063 469 14875829 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2894532 : blockSum term 2894532 469 16310814 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2895001 : blockSum term 2895001 468 15826282 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2895469 : blockSum term 2895469 469 11986009 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2895938 : blockSum term 2895938 469 15338050 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2896407 : blockSum term 2896407 469 15812413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2896876 : blockSum term 2896876 468 15328785 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2897344 : blockSum term 2897344 469 11972394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2897813 : blockSum term 2897813 469 14841514 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2898282 : blockSum term 2898282 469 11965589 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2898751 : blockSum term 2898751 468 17225761 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2899219 : blockSum term 2899219 469 15307126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2899688 : blockSum term 2899688 469 19128277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2900157 : blockSum term 2900157 469 13864070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2900626 : blockSum term 2900626 468 16249783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2901094 : blockSum term 2901094 469 15767464 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2901563 : blockSum term 2901563 469 12419677 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2902032 : blockSum term 2902032 469 16713933 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2902501 : blockSum term 2902501 468 13844833 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2902969 : blockSum term 2902969 469 14318523 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2903438 : blockSum term 2903438 469 14314252 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2903907 : blockSum term 2903907 469 17171561 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2904376 : blockSum term 2904376 468 15259222 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2904844 : blockSum term 2904844 469 14301670 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2905313 : blockSum term 2905313 469 16204220 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2905782 : blockSum term 2905782 469 14770081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2906251 : blockSum term 2906251 468 15242028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2906719 : blockSum term 2906719 469 14285223 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2907188 : blockSum term 2907188 469 15709431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2907657 : blockSum term 2907657 469 16180696 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2908126 : blockSum term 2908126 468 13321524 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2908594 : blockSum term 2908594 469 17123019 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2909063 : blockSum term 2909063 469 16166946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2909532 : blockSum term 2909532 469 15211602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 2790001 120000 3999757648 := (join_sums term (lo:=2790001) (a:=60000) (b:=60000) (join_sums term (lo:=2790001) (a:=30000) (b:=30000) (join_sums term (lo:=2790001) (a:=15000) (b:=15000) (join_sums term (lo:=2790001) (a:=7500) (b:=7500) (join_sums term (lo:=2790001) (a:=3750) (b:=3750) (join_sums term (lo:=2790001) (a:=1875) (b:=1875) (join_sums term (lo:=2790001) (a:=937) (b:=938) (join_sums term (lo:=2790001) (a:=468) (b:=469) r2790001 r2790469) (join_sums term (lo:=2790938) (a:=469) (b:=469) r2790938 r2791407)) (join_sums term (lo:=2791876) (a:=937) (b:=938) (join_sums term (lo:=2791876) (a:=468) (b:=469) r2791876 r2792344) (join_sums term (lo:=2792813) (a:=469) (b:=469) r2792813 r2793282))) (join_sums term (lo:=2793751) (a:=1875) (b:=1875) (join_sums term (lo:=2793751) (a:=937) (b:=938) (join_sums term (lo:=2793751) (a:=468) (b:=469) r2793751 r2794219) (join_sums term (lo:=2794688) (a:=469) (b:=469) r2794688 r2795157)) (join_sums term (lo:=2795626) (a:=937) (b:=938) (join_sums term (lo:=2795626) (a:=468) (b:=469) r2795626 r2796094) (join_sums term (lo:=2796563) (a:=469) (b:=469) r2796563 r2797032)))) (join_sums term (lo:=2797501) (a:=3750) (b:=3750) (join_sums term (lo:=2797501) (a:=1875) (b:=1875) (join_sums term (lo:=2797501) (a:=937) (b:=938) (join_sums term (lo:=2797501) (a:=468) (b:=469) r2797501 r2797969) (join_sums term (lo:=2798438) (a:=469) (b:=469) r2798438 r2798907)) (join_sums term (lo:=2799376) (a:=937) (b:=938) (join_sums term (lo:=2799376) (a:=468) (b:=469) r2799376 r2799844) (join_sums term (lo:=2800313) (a:=469) (b:=469) r2800313 r2800782))) (join_sums term (lo:=2801251) (a:=1875) (b:=1875) (join_sums term (lo:=2801251) (a:=937) (b:=938) (join_sums term (lo:=2801251) (a:=468) (b:=469) r2801251 r2801719) (join_sums term (lo:=2802188) (a:=469) (b:=469) r2802188 r2802657)) (join_sums term (lo:=2803126) (a:=937) (b:=938) (join_sums term (lo:=2803126) (a:=468) (b:=469) r2803126 r2803594) (join_sums term (lo:=2804063) (a:=469) (b:=469) r2804063 r2804532))))) (join_sums term (lo:=2805001) (a:=7500) (b:=7500) (join_sums term (lo:=2805001) (a:=3750) (b:=3750) (join_sums term (lo:=2805001) (a:=1875) (b:=1875) (join_sums term (lo:=2805001) (a:=937) (b:=938) (join_sums term (lo:=2805001) (a:=468) (b:=469) r2805001 r2805469) (join_sums term (lo:=2805938) (a:=469) (b:=469) r2805938 r2806407)) (join_sums term (lo:=2806876) (a:=937) (b:=938) (join_sums term (lo:=2806876) (a:=468) (b:=469) r2806876 r2807344) (join_sums term (lo:=2807813) (a:=469) (b:=469) r2807813 r2808282))) (join_sums term (lo:=2808751) (a:=1875) (b:=1875) (join_sums term (lo:=2808751) (a:=937) (b:=938) (join_sums term (lo:=2808751) (a:=468) (b:=469) r2808751 r2809219) (join_sums term (lo:=2809688) (a:=469) (b:=469) r2809688 r2810157)) (join_sums term (lo:=2810626) (a:=937) (b:=938) (join_sums term (lo:=2810626) (a:=468) (b:=469) r2810626 r2811094) (join_sums term (lo:=2811563) (a:=469) (b:=469) r2811563 r2812032)))) (join_sums term (lo:=2812501) (a:=3750) (b:=3750) (join_sums term (lo:=2812501) (a:=1875) (b:=1875) (join_sums term (lo:=2812501) (a:=937) (b:=938) (join_sums term (lo:=2812501) (a:=468) (b:=469) r2812501 r2812969) (join_sums term (lo:=2813438) (a:=469) (b:=469) r2813438 r2813907)) (join_sums term (lo:=2814376) (a:=937) (b:=938) (join_sums term (lo:=2814376) (a:=468) (b:=469) r2814376 r2814844) (join_sums term (lo:=2815313) (a:=469) (b:=469) r2815313 r2815782))) (join_sums term (lo:=2816251) (a:=1875) (b:=1875) (join_sums term (lo:=2816251) (a:=937) (b:=938) (join_sums term (lo:=2816251) (a:=468) (b:=469) r2816251 r2816719) (join_sums term (lo:=2817188) (a:=469) (b:=469) r2817188 r2817657)) (join_sums term (lo:=2818126) (a:=937) (b:=938) (join_sums term (lo:=2818126) (a:=468) (b:=469) r2818126 r2818594) (join_sums term (lo:=2819063) (a:=469) (b:=469) r2819063 r2819532)))))) (join_sums term (lo:=2820001) (a:=15000) (b:=15000) (join_sums term (lo:=2820001) (a:=7500) (b:=7500) (join_sums term (lo:=2820001) (a:=3750) (b:=3750) (join_sums term (lo:=2820001) (a:=1875) (b:=1875) (join_sums term (lo:=2820001) (a:=937) (b:=938) (join_sums term (lo:=2820001) (a:=468) (b:=469) r2820001 r2820469) (join_sums term (lo:=2820938) (a:=469) (b:=469) r2820938 r2821407)) (join_sums term (lo:=2821876) (a:=937) (b:=938) (join_sums term (lo:=2821876) (a:=468) (b:=469) r2821876 r2822344) (join_sums term (lo:=2822813) (a:=469) (b:=469) r2822813 r2823282))) (join_sums term (lo:=2823751) (a:=1875) (b:=1875) (join_sums term (lo:=2823751) (a:=937) (b:=938) (join_sums term (lo:=2823751) (a:=468) (b:=469) r2823751 r2824219) (join_sums term (lo:=2824688) (a:=469) (b:=469) r2824688 r2825157)) (join_sums term (lo:=2825626) (a:=937) (b:=938) (join_sums term (lo:=2825626) (a:=468) (b:=469) r2825626 r2826094) (join_sums term (lo:=2826563) (a:=469) (b:=469) r2826563 r2827032)))) (join_sums term (lo:=2827501) (a:=3750) (b:=3750) (join_sums term (lo:=2827501) (a:=1875) (b:=1875) (join_sums term (lo:=2827501) (a:=937) (b:=938) (join_sums term (lo:=2827501) (a:=468) (b:=469) r2827501 r2827969) (join_sums term (lo:=2828438) (a:=469) (b:=469) r2828438 r2828907)) (join_sums term (lo:=2829376) (a:=937) (b:=938) (join_sums term (lo:=2829376) (a:=468) (b:=469) r2829376 r2829844) (join_sums term (lo:=2830313) (a:=469) (b:=469) r2830313 r2830782))) (join_sums term (lo:=2831251) (a:=1875) (b:=1875) (join_sums term (lo:=2831251) (a:=937) (b:=938) (join_sums term (lo:=2831251) (a:=468) (b:=469) r2831251 r2831719) (join_sums term (lo:=2832188) (a:=469) (b:=469) r2832188 r2832657)) (join_sums term (lo:=2833126) (a:=937) (b:=938) (join_sums term (lo:=2833126) (a:=468) (b:=469) r2833126 r2833594) (join_sums term (lo:=2834063) (a:=469) (b:=469) r2834063 r2834532))))) (join_sums term (lo:=2835001) (a:=7500) (b:=7500) (join_sums term (lo:=2835001) (a:=3750) (b:=3750) (join_sums term (lo:=2835001) (a:=1875) (b:=1875) (join_sums term (lo:=2835001) (a:=937) (b:=938) (join_sums term (lo:=2835001) (a:=468) (b:=469) r2835001 r2835469) (join_sums term (lo:=2835938) (a:=469) (b:=469) r2835938 r2836407)) (join_sums term (lo:=2836876) (a:=937) (b:=938) (join_sums term (lo:=2836876) (a:=468) (b:=469) r2836876 r2837344) (join_sums term (lo:=2837813) (a:=469) (b:=469) r2837813 r2838282))) (join_sums term (lo:=2838751) (a:=1875) (b:=1875) (join_sums term (lo:=2838751) (a:=937) (b:=938) (join_sums term (lo:=2838751) (a:=468) (b:=469) r2838751 r2839219) (join_sums term (lo:=2839688) (a:=469) (b:=469) r2839688 r2840157)) (join_sums term (lo:=2840626) (a:=937) (b:=938) (join_sums term (lo:=2840626) (a:=468) (b:=469) r2840626 r2841094) (join_sums term (lo:=2841563) (a:=469) (b:=469) r2841563 r2842032)))) (join_sums term (lo:=2842501) (a:=3750) (b:=3750) (join_sums term (lo:=2842501) (a:=1875) (b:=1875) (join_sums term (lo:=2842501) (a:=937) (b:=938) (join_sums term (lo:=2842501) (a:=468) (b:=469) r2842501 r2842969) (join_sums term (lo:=2843438) (a:=469) (b:=469) r2843438 r2843907)) (join_sums term (lo:=2844376) (a:=937) (b:=938) (join_sums term (lo:=2844376) (a:=468) (b:=469) r2844376 r2844844) (join_sums term (lo:=2845313) (a:=469) (b:=469) r2845313 r2845782))) (join_sums term (lo:=2846251) (a:=1875) (b:=1875) (join_sums term (lo:=2846251) (a:=937) (b:=938) (join_sums term (lo:=2846251) (a:=468) (b:=469) r2846251 r2846719) (join_sums term (lo:=2847188) (a:=469) (b:=469) r2847188 r2847657)) (join_sums term (lo:=2848126) (a:=937) (b:=938) (join_sums term (lo:=2848126) (a:=468) (b:=469) r2848126 r2848594) (join_sums term (lo:=2849063) (a:=469) (b:=469) r2849063 r2849532))))))) (join_sums term (lo:=2850001) (a:=30000) (b:=30000) (join_sums term (lo:=2850001) (a:=15000) (b:=15000) (join_sums term (lo:=2850001) (a:=7500) (b:=7500) (join_sums term (lo:=2850001) (a:=3750) (b:=3750) (join_sums term (lo:=2850001) (a:=1875) (b:=1875) (join_sums term (lo:=2850001) (a:=937) (b:=938) (join_sums term (lo:=2850001) (a:=468) (b:=469) r2850001 r2850469) (join_sums term (lo:=2850938) (a:=469) (b:=469) r2850938 r2851407)) (join_sums term (lo:=2851876) (a:=937) (b:=938) (join_sums term (lo:=2851876) (a:=468) (b:=469) r2851876 r2852344) (join_sums term (lo:=2852813) (a:=469) (b:=469) r2852813 r2853282))) (join_sums term (lo:=2853751) (a:=1875) (b:=1875) (join_sums term (lo:=2853751) (a:=937) (b:=938) (join_sums term (lo:=2853751) (a:=468) (b:=469) r2853751 r2854219) (join_sums term (lo:=2854688) (a:=469) (b:=469) r2854688 r2855157)) (join_sums term (lo:=2855626) (a:=937) (b:=938) (join_sums term (lo:=2855626) (a:=468) (b:=469) r2855626 r2856094) (join_sums term (lo:=2856563) (a:=469) (b:=469) r2856563 r2857032)))) (join_sums term (lo:=2857501) (a:=3750) (b:=3750) (join_sums term (lo:=2857501) (a:=1875) (b:=1875) (join_sums term (lo:=2857501) (a:=937) (b:=938) (join_sums term (lo:=2857501) (a:=468) (b:=469) r2857501 r2857969) (join_sums term (lo:=2858438) (a:=469) (b:=469) r2858438 r2858907)) (join_sums term (lo:=2859376) (a:=937) (b:=938) (join_sums term (lo:=2859376) (a:=468) (b:=469) r2859376 r2859844) (join_sums term (lo:=2860313) (a:=469) (b:=469) r2860313 r2860782))) (join_sums term (lo:=2861251) (a:=1875) (b:=1875) (join_sums term (lo:=2861251) (a:=937) (b:=938) (join_sums term (lo:=2861251) (a:=468) (b:=469) r2861251 r2861719) (join_sums term (lo:=2862188) (a:=469) (b:=469) r2862188 r2862657)) (join_sums term (lo:=2863126) (a:=937) (b:=938) (join_sums term (lo:=2863126) (a:=468) (b:=469) r2863126 r2863594) (join_sums term (lo:=2864063) (a:=469) (b:=469) r2864063 r2864532))))) (join_sums term (lo:=2865001) (a:=7500) (b:=7500) (join_sums term (lo:=2865001) (a:=3750) (b:=3750) (join_sums term (lo:=2865001) (a:=1875) (b:=1875) (join_sums term (lo:=2865001) (a:=937) (b:=938) (join_sums term (lo:=2865001) (a:=468) (b:=469) r2865001 r2865469) (join_sums term (lo:=2865938) (a:=469) (b:=469) r2865938 r2866407)) (join_sums term (lo:=2866876) (a:=937) (b:=938) (join_sums term (lo:=2866876) (a:=468) (b:=469) r2866876 r2867344) (join_sums term (lo:=2867813) (a:=469) (b:=469) r2867813 r2868282))) (join_sums term (lo:=2868751) (a:=1875) (b:=1875) (join_sums term (lo:=2868751) (a:=937) (b:=938) (join_sums term (lo:=2868751) (a:=468) (b:=469) r2868751 r2869219) (join_sums term (lo:=2869688) (a:=469) (b:=469) r2869688 r2870157)) (join_sums term (lo:=2870626) (a:=937) (b:=938) (join_sums term (lo:=2870626) (a:=468) (b:=469) r2870626 r2871094) (join_sums term (lo:=2871563) (a:=469) (b:=469) r2871563 r2872032)))) (join_sums term (lo:=2872501) (a:=3750) (b:=3750) (join_sums term (lo:=2872501) (a:=1875) (b:=1875) (join_sums term (lo:=2872501) (a:=937) (b:=938) (join_sums term (lo:=2872501) (a:=468) (b:=469) r2872501 r2872969) (join_sums term (lo:=2873438) (a:=469) (b:=469) r2873438 r2873907)) (join_sums term (lo:=2874376) (a:=937) (b:=938) (join_sums term (lo:=2874376) (a:=468) (b:=469) r2874376 r2874844) (join_sums term (lo:=2875313) (a:=469) (b:=469) r2875313 r2875782))) (join_sums term (lo:=2876251) (a:=1875) (b:=1875) (join_sums term (lo:=2876251) (a:=937) (b:=938) (join_sums term (lo:=2876251) (a:=468) (b:=469) r2876251 r2876719) (join_sums term (lo:=2877188) (a:=469) (b:=469) r2877188 r2877657)) (join_sums term (lo:=2878126) (a:=937) (b:=938) (join_sums term (lo:=2878126) (a:=468) (b:=469) r2878126 r2878594) (join_sums term (lo:=2879063) (a:=469) (b:=469) r2879063 r2879532)))))) (join_sums term (lo:=2880001) (a:=15000) (b:=15000) (join_sums term (lo:=2880001) (a:=7500) (b:=7500) (join_sums term (lo:=2880001) (a:=3750) (b:=3750) (join_sums term (lo:=2880001) (a:=1875) (b:=1875) (join_sums term (lo:=2880001) (a:=937) (b:=938) (join_sums term (lo:=2880001) (a:=468) (b:=469) r2880001 r2880469) (join_sums term (lo:=2880938) (a:=469) (b:=469) r2880938 r2881407)) (join_sums term (lo:=2881876) (a:=937) (b:=938) (join_sums term (lo:=2881876) (a:=468) (b:=469) r2881876 r2882344) (join_sums term (lo:=2882813) (a:=469) (b:=469) r2882813 r2883282))) (join_sums term (lo:=2883751) (a:=1875) (b:=1875) (join_sums term (lo:=2883751) (a:=937) (b:=938) (join_sums term (lo:=2883751) (a:=468) (b:=469) r2883751 r2884219) (join_sums term (lo:=2884688) (a:=469) (b:=469) r2884688 r2885157)) (join_sums term (lo:=2885626) (a:=937) (b:=938) (join_sums term (lo:=2885626) (a:=468) (b:=469) r2885626 r2886094) (join_sums term (lo:=2886563) (a:=469) (b:=469) r2886563 r2887032)))) (join_sums term (lo:=2887501) (a:=3750) (b:=3750) (join_sums term (lo:=2887501) (a:=1875) (b:=1875) (join_sums term (lo:=2887501) (a:=937) (b:=938) (join_sums term (lo:=2887501) (a:=468) (b:=469) r2887501 r2887969) (join_sums term (lo:=2888438) (a:=469) (b:=469) r2888438 r2888907)) (join_sums term (lo:=2889376) (a:=937) (b:=938) (join_sums term (lo:=2889376) (a:=468) (b:=469) r2889376 r2889844) (join_sums term (lo:=2890313) (a:=469) (b:=469) r2890313 r2890782))) (join_sums term (lo:=2891251) (a:=1875) (b:=1875) (join_sums term (lo:=2891251) (a:=937) (b:=938) (join_sums term (lo:=2891251) (a:=468) (b:=469) r2891251 r2891719) (join_sums term (lo:=2892188) (a:=469) (b:=469) r2892188 r2892657)) (join_sums term (lo:=2893126) (a:=937) (b:=938) (join_sums term (lo:=2893126) (a:=468) (b:=469) r2893126 r2893594) (join_sums term (lo:=2894063) (a:=469) (b:=469) r2894063 r2894532))))) (join_sums term (lo:=2895001) (a:=7500) (b:=7500) (join_sums term (lo:=2895001) (a:=3750) (b:=3750) (join_sums term (lo:=2895001) (a:=1875) (b:=1875) (join_sums term (lo:=2895001) (a:=937) (b:=938) (join_sums term (lo:=2895001) (a:=468) (b:=469) r2895001 r2895469) (join_sums term (lo:=2895938) (a:=469) (b:=469) r2895938 r2896407)) (join_sums term (lo:=2896876) (a:=937) (b:=938) (join_sums term (lo:=2896876) (a:=468) (b:=469) r2896876 r2897344) (join_sums term (lo:=2897813) (a:=469) (b:=469) r2897813 r2898282))) (join_sums term (lo:=2898751) (a:=1875) (b:=1875) (join_sums term (lo:=2898751) (a:=937) (b:=938) (join_sums term (lo:=2898751) (a:=468) (b:=469) r2898751 r2899219) (join_sums term (lo:=2899688) (a:=469) (b:=469) r2899688 r2900157)) (join_sums term (lo:=2900626) (a:=937) (b:=938) (join_sums term (lo:=2900626) (a:=468) (b:=469) r2900626 r2901094) (join_sums term (lo:=2901563) (a:=469) (b:=469) r2901563 r2902032)))) (join_sums term (lo:=2902501) (a:=3750) (b:=3750) (join_sums term (lo:=2902501) (a:=1875) (b:=1875) (join_sums term (lo:=2902501) (a:=937) (b:=938) (join_sums term (lo:=2902501) (a:=468) (b:=469) r2902501 r2902969) (join_sums term (lo:=2903438) (a:=469) (b:=469) r2903438 r2903907)) (join_sums term (lo:=2904376) (a:=937) (b:=938) (join_sums term (lo:=2904376) (a:=468) (b:=469) r2904376 r2904844) (join_sums term (lo:=2905313) (a:=469) (b:=469) r2905313 r2905782))) (join_sums term (lo:=2906251) (a:=1875) (b:=1875) (join_sums term (lo:=2906251) (a:=937) (b:=938) (join_sums term (lo:=2906251) (a:=468) (b:=469) r2906251 r2906719) (join_sums term (lo:=2907188) (a:=469) (b:=469) r2907188 r2907657)) (join_sums term (lo:=2908126) (a:=937) (b:=938) (join_sums term (lo:=2908126) (a:=468) (b:=469) r2908126 r2908594) (join_sums term (lo:=2909063) (a:=469) (b:=469) r2909063 r2909532))))))))

private theorem rows : blockSum term 0 2910001 3999757648 :=
  join_sums term (lo:=0) (a:=2790001) (b:=120000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 2910000).filter (2790000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=3999757648 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From2790000To2910000
