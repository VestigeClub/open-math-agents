import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 3,030,000 through 3,150,000

The sum covers 8,027 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From3030000To3150000

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


private abbrev term := contribution 30110134441897 3030000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 3030001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 3030000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r3030001 : blockSum term 3030001 468 16349504 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3030469 : blockSum term 3030469 469 13252496 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3030938 : blockSum term 3030938 469 13690065 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3031407 : blockSum term 3031407 469 12802812 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3031876 : blockSum term 3031876 468 13240758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3032344 : blockSum term 3032344 469 15001886 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3032813 : blockSum term 3032813 469 13674064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3033282 : blockSum term 3033282 469 14111212 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3033751 : blockSum term 3033751 468 14107354 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3034219 : blockSum term 3034219 469 14103159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3034688 : blockSum term 3034688 469 14099352 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3035157 : blockSum term 3035157 469 10131015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3035626 : blockSum term 3035626 468 13651407 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3036094 : blockSum term 3036094 469 12326472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3036563 : blockSum term 3036563 469 11882919 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3037032 : blockSum term 3037032 469 13639638 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3037501 : blockSum term 3037501 468 16714717 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3037969 : blockSum term 3037969 469 15830485 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3038438 : blockSum term 3038438 469 11429513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3038907 : blockSum term 3038907 469 14942406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3039376 : blockSum term 3039376 468 9666053 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3039844 : blockSum term 3039844 469 13616599 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3040313 : blockSum term 3040313 469 15369122 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3040782 : blockSum term 3040782 469 12730923 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3041251 : blockSum term 3041251 468 14482627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3041719 : blockSum term 3041719 469 14917407 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3042188 : blockSum term 3042188 469 12720167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3042657 : blockSum term 3042657 469 16224015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3043126 : blockSum term 3043126 468 16219076 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3043594 : blockSum term 3043594 469 14899498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3044063 : blockSum term 3044063 469 11828627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3044532 : blockSum term 3044532 469 13139223 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3045001 : blockSum term 3045001 468 14010932 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3045469 : blockSum term 3045469 469 13131371 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3045938 : blockSum term 3045938 469 10502498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3046407 : blockSum term 3046407 469 15311922 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3046876 : blockSum term 3046876 468 14869741 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3047344 : blockSum term 3047344 469 16614380 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3047813 : blockSum term 3047813 469 10490195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3048282 : blockSum term 3048282 469 12672070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3048751 : blockSum term 3048751 468 12668911 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3049219 : blockSum term 3049219 469 12228523 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3049688 : blockSum term 3049688 469 15717801 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3050157 : blockSum term 3050157 469 13094368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3050626 : blockSum term 3050626 468 13963194 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3051094 : blockSum term 3051094 469 10033519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3051563 : blockSum term 3051563 469 13083830 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3052032 : blockSum term 3052032 469 13515825 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3052501 : blockSum term 3052501 468 15691453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3052969 : blockSum term 3052969 469 15686703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3053438 : blockSum term 3053438 469 13939346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3053907 : blockSum term 3053907 469 13499905 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3054376 : blockSum term 3054376 468 12625131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3054844 : blockSum term 3054844 469 10880723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3055313 : blockSum term 3055313 469 14793637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3055782 : blockSum term 3055782 469 12614447 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3056251 : blockSum term 3056251 468 14785380 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3056719 : blockSum term 3056719 469 12172921 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3057188 : blockSum term 3057188 469 13038559 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3057657 : blockSum term 3057657 469 11731680 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3058126 : blockSum term 3058126 468 13031198 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3058594 : blockSum term 3058594 469 18672577 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3059063 : blockSum term 3059063 469 15194244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3059532 : blockSum term 3059532 469 8246237 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3060001 : blockSum term 3060001 468 14752240 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3060469 : blockSum term 3060469 469 14748090 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3060938 : blockSum term 3060938 469 15177292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3061407 : blockSum term 3061407 469 13005443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3061876 : blockSum term 3061876 468 16035783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3062344 : blockSum term 3062344 469 11264929 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3062813 : blockSum term 3062813 469 12994392 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3063282 : blockSum term 3063282 469 12990547 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3063751 : blockSum term 3063751 468 9956589 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3064219 : blockSum term 3064219 469 12983018 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3064688 : blockSum term 3064688 469 9518452 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3065157 : blockSum term 3065157 469 13408804 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3065626 : blockSum term 3065626 468 14702572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3066094 : blockSum term 3066094 469 11671904 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3066563 : blockSum term 3066563 469 15557798 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3067032 : blockSum term 3067032 469 12960605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3067501 : blockSum term 3067501 468 14684495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3067969 : blockSum term 3067969 469 13816843 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3068438 : blockSum term 3068438 469 12949542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3068907 : blockSum term 3068907 469 14672257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3069376 : blockSum term 3069376 468 14668047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3069844 : blockSum term 3069844 469 13801534 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3070313 : blockSum term 3070313 469 13797548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3070782 : blockSum term 3070782 469 15948325 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3071251 : blockSum term 3071251 468 15081366 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3071719 : blockSum term 3071719 469 13784629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3072188 : blockSum term 3072188 469 13350021 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3072657 : blockSum term 3072657 469 13776421 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3073126 : blockSum term 3073126 468 9468665 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3073594 : blockSum term 3073594 469 18501278 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3074063 : blockSum term 3074063 469 14624828 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3074532 : blockSum term 3074532 469 15480159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3075001 : blockSum term 3075001 468 16765098 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3075469 : blockSum term 3075469 469 10313841 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3075938 : blockSum term 3075938 469 16325302 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3076407 : blockSum term 3076407 469 13743516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3076876 : blockSum term 3076876 468 12880994 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3077344 : blockSum term 3077344 469 13735915 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3077813 : blockSum term 3077813 469 13302860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3078282 : blockSum term 3078282 469 13727803 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3078751 : blockSum term 3078751 468 13295254 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3079219 : blockSum term 3079219 469 12434079 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3079688 : blockSum term 3079688 469 14144872 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3080157 : blockSum term 3080157 469 12426888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3080626 : blockSum term 3080626 468 17135138 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3081094 : blockSum term 3081094 469 13276063 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3081563 : blockSum term 3081563 469 14128491 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3082032 : blockSum term 3082032 469 11128321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3082501 : blockSum term 3082501 468 12836845 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3082969 : blockSum term 3082969 469 14116657 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3083438 : blockSum term 3083438 469 11546611 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3083907 : blockSum term 3083907 469 11543769 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3084376 : blockSum term 3084376 468 14105346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3084844 : blockSum term 3084844 469 14955699 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3085313 : blockSum term 3085313 469 15377866 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3085782 : blockSum term 3085782 469 12810996 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3086251 : blockSum term 3086251 468 11953739 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3086719 : blockSum term 3086719 469 13230834 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3087188 : blockSum term 3087188 469 14507139 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3087657 : blockSum term 3087657 469 16635542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3088126 : blockSum term 3088126 468 13219308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3088594 : blockSum term 3088594 469 14494434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3089063 : blockSum term 3089063 469 15342475 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3089532 : blockSum term 3089532 469 13633956 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3090001 : blockSum term 3090001 468 13629509 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3090469 : blockSum term 3090469 469 11922450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3090938 : blockSum term 3090938 469 15324360 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3091407 : blockSum term 3091407 469 14043409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3091876 : blockSum term 3091876 468 12337772 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3092344 : blockSum term 3092344 469 14885860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3092813 : blockSum term 3092813 469 14455793 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3093282 : blockSum term 3093282 469 11476249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3093751 : blockSum term 3093751 468 14022833 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3094219 : blockSum term 3094219 469 11045045 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3094688 : blockSum term 3094688 469 11466539 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3095157 : blockSum term 3095157 469 13585717 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3095626 : blockSum term 3095626 468 14430484 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3096094 : blockSum term 3096094 469 16547775 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3096563 : blockSum term 3096563 469 11452745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3097032 : blockSum term 3097032 469 13145635 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3097501 : blockSum term 3097501 468 10598044 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3097969 : blockSum term 3097969 469 11442935 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3098438 : blockSum term 3098438 469 16100328 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3098907 : blockSum term 3098907 469 10589289 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3099376 : blockSum term 3099376 468 12280818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3099844 : blockSum term 3099844 469 11853609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3100313 : blockSum term 3100313 469 8464628 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3100782 : blockSum term 3100782 469 11000878 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3101251 : blockSum term 3101251 468 13958883 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3101719 : blockSum term 3101719 469 12263241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3102188 : blockSum term 3102188 469 16486983 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3102657 : blockSum term 3102657 469 16904361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3103126 : blockSum term 3103126 468 14364400 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3103594 : blockSum term 3103594 469 9714530 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3104063 : blockSum term 3104063 469 14778581 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3104532 : blockSum term 3104532 469 13930309 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3105001 : blockSum term 3105001 468 13504326 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3105469 : blockSum term 3105469 469 13922291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3105938 : blockSum term 3105938 469 14762025 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3106407 : blockSum term 3106407 469 11805865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3106876 : blockSum term 3106876 468 11381342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3107344 : blockSum term 3107344 469 13063871 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3107813 : blockSum term 3107813 469 15587736 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3108282 : blockSum term 3108282 469 15161931 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3108751 : blockSum term 3108751 468 11789031 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3109219 : blockSum term 3109219 469 13890333 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3109688 : blockSum term 3109688 469 13465754 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3110157 : blockSum term 3110157 469 13461401 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3110626 : blockSum term 3110626 468 14298517 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3111094 : blockSum term 3111094 469 12612548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3111563 : blockSum term 3111563 469 10507625 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3112032 : blockSum term 3112032 469 14286363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3112501 : blockSum term 3112501 468 10921543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3112969 : blockSum term 3112969 469 13018322 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3113438 : blockSum term 3113438 469 13854300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3113907 : blockSum term 3113907 469 13430519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3114376 : blockSum term 3114376 468 12167703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3114844 : blockSum term 3114844 469 15100145 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3115313 : blockSum term 3115313 469 13837489 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3115782 : blockSum term 3115782 469 12575868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3116251 : blockSum term 3116251 468 13829455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3116719 : blockSum term 3116719 469 13406665 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3117188 : blockSum term 3117188 469 13821494 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3117657 : blockSum term 3117657 469 13398670 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3118126 : blockSum term 3118126 468 15487653 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3118594 : blockSum term 3118594 469 16319899 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3119063 : blockSum term 3119063 469 11295174 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3119532 : blockSum term 3119532 469 12546399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3120001 : blockSum term 3120001 468 12124819 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3120469 : blockSum term 3120469 469 14629107 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3120938 : blockSum term 3120938 469 13788979 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3121407 : blockSum term 3121407 469 12531583 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3121876 : blockSum term 3121876 468 12110043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3122344 : blockSum term 3122344 469 11689106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3122813 : blockSum term 3122813 469 15441921 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3123282 : blockSum term 3123282 469 12516615 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3123751 : blockSum term 3123751 468 14181832 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3124219 : blockSum term 3124219 469 10841719 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3124688 : blockSum term 3124688 469 12089209 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3125157 : blockSum term 3125157 469 11252499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3125626 : blockSum term 3125626 468 13749101 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3126094 : blockSum term 3126094 469 13328579 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3126563 : blockSum term 3126563 469 11242685 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3127032 : blockSum term 3127032 469 13321006 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3127501 : blockSum term 3127501 468 15397897 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3127969 : blockSum term 3127969 469 12065253 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3128438 : blockSum term 3128438 469 14556656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3128907 : blockSum term 3128907 469 11226235 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3129376 : blockSum term 3129376 468 14963792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3129844 : blockSum term 3129844 469 12881860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3130313 : blockSum term 3130313 469 14124587 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3130782 : blockSum term 3130782 469 14120143 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3131251 : blockSum term 3131251 468 15361386 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3131719 : blockSum term 3131719 469 9961015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3132188 : blockSum term 3132188 469 11617615 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3132657 : blockSum term 3132657 469 11614846 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3133126 : blockSum term 3133126 468 14099776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3133594 : blockSum term 3133594 469 14924544 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3134063 : blockSum term 3134063 469 12433624 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3134532 : blockSum term 3134532 469 11601554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3135001 : blockSum term 3135001 468 13669360 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3135469 : blockSum term 3135469 469 11180979 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3135938 : blockSum term 3135938 469 13661487 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3136407 : blockSum term 3136407 469 12830011 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3136876 : blockSum term 3136876 468 11171400 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3137344 : blockSum term 3137344 469 12822507 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3137813 : blockSum term 3137813 469 10338032 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3138282 : blockSum term 3138282 469 12815438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3138751 : blockSum term 3138751 468 13225151 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3139219 : blockSum term 3139219 469 16112792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3139688 : blockSum term 3139688 469 13216918 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3140157 : blockSum term 3140157 469 10322932 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3140626 : blockSum term 3140626 468 12796787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3141094 : blockSum term 3141094 469 14443223 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3141563 : blockSum term 3141563 469 10313518 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3142032 : blockSum term 3142032 469 13196764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3142501 : blockSum term 3142501 468 14841876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3142969 : blockSum term 3142969 469 12364859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3143438 : blockSum term 3143438 469 10712935 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3143907 : blockSum term 3143907 469 12769088 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3144376 : blockSum term 3144376 468 12765402 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3144844 : blockSum term 3144844 469 13996787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3145313 : blockSum term 3145313 469 13169365 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3145782 : blockSum term 3145782 469 12342627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3146251 : blockSum term 3146251 468 12338936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3146719 : blockSum term 3146719 469 13157684 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3147188 : blockSum term 3147188 469 11920948 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3147657 : blockSum term 3147657 469 13149995 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3148126 : blockSum term 3148126 468 13146583 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3148594 : blockSum term 3148594 469 14785857 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3149063 : blockSum term 3149063 469 8622666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3149532 : blockSum term 3149532 469 16419453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 3030001 120000 3419946054 := (join_sums term (lo:=3030001) (a:=60000) (b:=60000) (join_sums term (lo:=3030001) (a:=30000) (b:=30000) (join_sums term (lo:=3030001) (a:=15000) (b:=15000) (join_sums term (lo:=3030001) (a:=7500) (b:=7500) (join_sums term (lo:=3030001) (a:=3750) (b:=3750) (join_sums term (lo:=3030001) (a:=1875) (b:=1875) (join_sums term (lo:=3030001) (a:=937) (b:=938) (join_sums term (lo:=3030001) (a:=468) (b:=469) r3030001 r3030469) (join_sums term (lo:=3030938) (a:=469) (b:=469) r3030938 r3031407)) (join_sums term (lo:=3031876) (a:=937) (b:=938) (join_sums term (lo:=3031876) (a:=468) (b:=469) r3031876 r3032344) (join_sums term (lo:=3032813) (a:=469) (b:=469) r3032813 r3033282))) (join_sums term (lo:=3033751) (a:=1875) (b:=1875) (join_sums term (lo:=3033751) (a:=937) (b:=938) (join_sums term (lo:=3033751) (a:=468) (b:=469) r3033751 r3034219) (join_sums term (lo:=3034688) (a:=469) (b:=469) r3034688 r3035157)) (join_sums term (lo:=3035626) (a:=937) (b:=938) (join_sums term (lo:=3035626) (a:=468) (b:=469) r3035626 r3036094) (join_sums term (lo:=3036563) (a:=469) (b:=469) r3036563 r3037032)))) (join_sums term (lo:=3037501) (a:=3750) (b:=3750) (join_sums term (lo:=3037501) (a:=1875) (b:=1875) (join_sums term (lo:=3037501) (a:=937) (b:=938) (join_sums term (lo:=3037501) (a:=468) (b:=469) r3037501 r3037969) (join_sums term (lo:=3038438) (a:=469) (b:=469) r3038438 r3038907)) (join_sums term (lo:=3039376) (a:=937) (b:=938) (join_sums term (lo:=3039376) (a:=468) (b:=469) r3039376 r3039844) (join_sums term (lo:=3040313) (a:=469) (b:=469) r3040313 r3040782))) (join_sums term (lo:=3041251) (a:=1875) (b:=1875) (join_sums term (lo:=3041251) (a:=937) (b:=938) (join_sums term (lo:=3041251) (a:=468) (b:=469) r3041251 r3041719) (join_sums term (lo:=3042188) (a:=469) (b:=469) r3042188 r3042657)) (join_sums term (lo:=3043126) (a:=937) (b:=938) (join_sums term (lo:=3043126) (a:=468) (b:=469) r3043126 r3043594) (join_sums term (lo:=3044063) (a:=469) (b:=469) r3044063 r3044532))))) (join_sums term (lo:=3045001) (a:=7500) (b:=7500) (join_sums term (lo:=3045001) (a:=3750) (b:=3750) (join_sums term (lo:=3045001) (a:=1875) (b:=1875) (join_sums term (lo:=3045001) (a:=937) (b:=938) (join_sums term (lo:=3045001) (a:=468) (b:=469) r3045001 r3045469) (join_sums term (lo:=3045938) (a:=469) (b:=469) r3045938 r3046407)) (join_sums term (lo:=3046876) (a:=937) (b:=938) (join_sums term (lo:=3046876) (a:=468) (b:=469) r3046876 r3047344) (join_sums term (lo:=3047813) (a:=469) (b:=469) r3047813 r3048282))) (join_sums term (lo:=3048751) (a:=1875) (b:=1875) (join_sums term (lo:=3048751) (a:=937) (b:=938) (join_sums term (lo:=3048751) (a:=468) (b:=469) r3048751 r3049219) (join_sums term (lo:=3049688) (a:=469) (b:=469) r3049688 r3050157)) (join_sums term (lo:=3050626) (a:=937) (b:=938) (join_sums term (lo:=3050626) (a:=468) (b:=469) r3050626 r3051094) (join_sums term (lo:=3051563) (a:=469) (b:=469) r3051563 r3052032)))) (join_sums term (lo:=3052501) (a:=3750) (b:=3750) (join_sums term (lo:=3052501) (a:=1875) (b:=1875) (join_sums term (lo:=3052501) (a:=937) (b:=938) (join_sums term (lo:=3052501) (a:=468) (b:=469) r3052501 r3052969) (join_sums term (lo:=3053438) (a:=469) (b:=469) r3053438 r3053907)) (join_sums term (lo:=3054376) (a:=937) (b:=938) (join_sums term (lo:=3054376) (a:=468) (b:=469) r3054376 r3054844) (join_sums term (lo:=3055313) (a:=469) (b:=469) r3055313 r3055782))) (join_sums term (lo:=3056251) (a:=1875) (b:=1875) (join_sums term (lo:=3056251) (a:=937) (b:=938) (join_sums term (lo:=3056251) (a:=468) (b:=469) r3056251 r3056719) (join_sums term (lo:=3057188) (a:=469) (b:=469) r3057188 r3057657)) (join_sums term (lo:=3058126) (a:=937) (b:=938) (join_sums term (lo:=3058126) (a:=468) (b:=469) r3058126 r3058594) (join_sums term (lo:=3059063) (a:=469) (b:=469) r3059063 r3059532)))))) (join_sums term (lo:=3060001) (a:=15000) (b:=15000) (join_sums term (lo:=3060001) (a:=7500) (b:=7500) (join_sums term (lo:=3060001) (a:=3750) (b:=3750) (join_sums term (lo:=3060001) (a:=1875) (b:=1875) (join_sums term (lo:=3060001) (a:=937) (b:=938) (join_sums term (lo:=3060001) (a:=468) (b:=469) r3060001 r3060469) (join_sums term (lo:=3060938) (a:=469) (b:=469) r3060938 r3061407)) (join_sums term (lo:=3061876) (a:=937) (b:=938) (join_sums term (lo:=3061876) (a:=468) (b:=469) r3061876 r3062344) (join_sums term (lo:=3062813) (a:=469) (b:=469) r3062813 r3063282))) (join_sums term (lo:=3063751) (a:=1875) (b:=1875) (join_sums term (lo:=3063751) (a:=937) (b:=938) (join_sums term (lo:=3063751) (a:=468) (b:=469) r3063751 r3064219) (join_sums term (lo:=3064688) (a:=469) (b:=469) r3064688 r3065157)) (join_sums term (lo:=3065626) (a:=937) (b:=938) (join_sums term (lo:=3065626) (a:=468) (b:=469) r3065626 r3066094) (join_sums term (lo:=3066563) (a:=469) (b:=469) r3066563 r3067032)))) (join_sums term (lo:=3067501) (a:=3750) (b:=3750) (join_sums term (lo:=3067501) (a:=1875) (b:=1875) (join_sums term (lo:=3067501) (a:=937) (b:=938) (join_sums term (lo:=3067501) (a:=468) (b:=469) r3067501 r3067969) (join_sums term (lo:=3068438) (a:=469) (b:=469) r3068438 r3068907)) (join_sums term (lo:=3069376) (a:=937) (b:=938) (join_sums term (lo:=3069376) (a:=468) (b:=469) r3069376 r3069844) (join_sums term (lo:=3070313) (a:=469) (b:=469) r3070313 r3070782))) (join_sums term (lo:=3071251) (a:=1875) (b:=1875) (join_sums term (lo:=3071251) (a:=937) (b:=938) (join_sums term (lo:=3071251) (a:=468) (b:=469) r3071251 r3071719) (join_sums term (lo:=3072188) (a:=469) (b:=469) r3072188 r3072657)) (join_sums term (lo:=3073126) (a:=937) (b:=938) (join_sums term (lo:=3073126) (a:=468) (b:=469) r3073126 r3073594) (join_sums term (lo:=3074063) (a:=469) (b:=469) r3074063 r3074532))))) (join_sums term (lo:=3075001) (a:=7500) (b:=7500) (join_sums term (lo:=3075001) (a:=3750) (b:=3750) (join_sums term (lo:=3075001) (a:=1875) (b:=1875) (join_sums term (lo:=3075001) (a:=937) (b:=938) (join_sums term (lo:=3075001) (a:=468) (b:=469) r3075001 r3075469) (join_sums term (lo:=3075938) (a:=469) (b:=469) r3075938 r3076407)) (join_sums term (lo:=3076876) (a:=937) (b:=938) (join_sums term (lo:=3076876) (a:=468) (b:=469) r3076876 r3077344) (join_sums term (lo:=3077813) (a:=469) (b:=469) r3077813 r3078282))) (join_sums term (lo:=3078751) (a:=1875) (b:=1875) (join_sums term (lo:=3078751) (a:=937) (b:=938) (join_sums term (lo:=3078751) (a:=468) (b:=469) r3078751 r3079219) (join_sums term (lo:=3079688) (a:=469) (b:=469) r3079688 r3080157)) (join_sums term (lo:=3080626) (a:=937) (b:=938) (join_sums term (lo:=3080626) (a:=468) (b:=469) r3080626 r3081094) (join_sums term (lo:=3081563) (a:=469) (b:=469) r3081563 r3082032)))) (join_sums term (lo:=3082501) (a:=3750) (b:=3750) (join_sums term (lo:=3082501) (a:=1875) (b:=1875) (join_sums term (lo:=3082501) (a:=937) (b:=938) (join_sums term (lo:=3082501) (a:=468) (b:=469) r3082501 r3082969) (join_sums term (lo:=3083438) (a:=469) (b:=469) r3083438 r3083907)) (join_sums term (lo:=3084376) (a:=937) (b:=938) (join_sums term (lo:=3084376) (a:=468) (b:=469) r3084376 r3084844) (join_sums term (lo:=3085313) (a:=469) (b:=469) r3085313 r3085782))) (join_sums term (lo:=3086251) (a:=1875) (b:=1875) (join_sums term (lo:=3086251) (a:=937) (b:=938) (join_sums term (lo:=3086251) (a:=468) (b:=469) r3086251 r3086719) (join_sums term (lo:=3087188) (a:=469) (b:=469) r3087188 r3087657)) (join_sums term (lo:=3088126) (a:=937) (b:=938) (join_sums term (lo:=3088126) (a:=468) (b:=469) r3088126 r3088594) (join_sums term (lo:=3089063) (a:=469) (b:=469) r3089063 r3089532))))))) (join_sums term (lo:=3090001) (a:=30000) (b:=30000) (join_sums term (lo:=3090001) (a:=15000) (b:=15000) (join_sums term (lo:=3090001) (a:=7500) (b:=7500) (join_sums term (lo:=3090001) (a:=3750) (b:=3750) (join_sums term (lo:=3090001) (a:=1875) (b:=1875) (join_sums term (lo:=3090001) (a:=937) (b:=938) (join_sums term (lo:=3090001) (a:=468) (b:=469) r3090001 r3090469) (join_sums term (lo:=3090938) (a:=469) (b:=469) r3090938 r3091407)) (join_sums term (lo:=3091876) (a:=937) (b:=938) (join_sums term (lo:=3091876) (a:=468) (b:=469) r3091876 r3092344) (join_sums term (lo:=3092813) (a:=469) (b:=469) r3092813 r3093282))) (join_sums term (lo:=3093751) (a:=1875) (b:=1875) (join_sums term (lo:=3093751) (a:=937) (b:=938) (join_sums term (lo:=3093751) (a:=468) (b:=469) r3093751 r3094219) (join_sums term (lo:=3094688) (a:=469) (b:=469) r3094688 r3095157)) (join_sums term (lo:=3095626) (a:=937) (b:=938) (join_sums term (lo:=3095626) (a:=468) (b:=469) r3095626 r3096094) (join_sums term (lo:=3096563) (a:=469) (b:=469) r3096563 r3097032)))) (join_sums term (lo:=3097501) (a:=3750) (b:=3750) (join_sums term (lo:=3097501) (a:=1875) (b:=1875) (join_sums term (lo:=3097501) (a:=937) (b:=938) (join_sums term (lo:=3097501) (a:=468) (b:=469) r3097501 r3097969) (join_sums term (lo:=3098438) (a:=469) (b:=469) r3098438 r3098907)) (join_sums term (lo:=3099376) (a:=937) (b:=938) (join_sums term (lo:=3099376) (a:=468) (b:=469) r3099376 r3099844) (join_sums term (lo:=3100313) (a:=469) (b:=469) r3100313 r3100782))) (join_sums term (lo:=3101251) (a:=1875) (b:=1875) (join_sums term (lo:=3101251) (a:=937) (b:=938) (join_sums term (lo:=3101251) (a:=468) (b:=469) r3101251 r3101719) (join_sums term (lo:=3102188) (a:=469) (b:=469) r3102188 r3102657)) (join_sums term (lo:=3103126) (a:=937) (b:=938) (join_sums term (lo:=3103126) (a:=468) (b:=469) r3103126 r3103594) (join_sums term (lo:=3104063) (a:=469) (b:=469) r3104063 r3104532))))) (join_sums term (lo:=3105001) (a:=7500) (b:=7500) (join_sums term (lo:=3105001) (a:=3750) (b:=3750) (join_sums term (lo:=3105001) (a:=1875) (b:=1875) (join_sums term (lo:=3105001) (a:=937) (b:=938) (join_sums term (lo:=3105001) (a:=468) (b:=469) r3105001 r3105469) (join_sums term (lo:=3105938) (a:=469) (b:=469) r3105938 r3106407)) (join_sums term (lo:=3106876) (a:=937) (b:=938) (join_sums term (lo:=3106876) (a:=468) (b:=469) r3106876 r3107344) (join_sums term (lo:=3107813) (a:=469) (b:=469) r3107813 r3108282))) (join_sums term (lo:=3108751) (a:=1875) (b:=1875) (join_sums term (lo:=3108751) (a:=937) (b:=938) (join_sums term (lo:=3108751) (a:=468) (b:=469) r3108751 r3109219) (join_sums term (lo:=3109688) (a:=469) (b:=469) r3109688 r3110157)) (join_sums term (lo:=3110626) (a:=937) (b:=938) (join_sums term (lo:=3110626) (a:=468) (b:=469) r3110626 r3111094) (join_sums term (lo:=3111563) (a:=469) (b:=469) r3111563 r3112032)))) (join_sums term (lo:=3112501) (a:=3750) (b:=3750) (join_sums term (lo:=3112501) (a:=1875) (b:=1875) (join_sums term (lo:=3112501) (a:=937) (b:=938) (join_sums term (lo:=3112501) (a:=468) (b:=469) r3112501 r3112969) (join_sums term (lo:=3113438) (a:=469) (b:=469) r3113438 r3113907)) (join_sums term (lo:=3114376) (a:=937) (b:=938) (join_sums term (lo:=3114376) (a:=468) (b:=469) r3114376 r3114844) (join_sums term (lo:=3115313) (a:=469) (b:=469) r3115313 r3115782))) (join_sums term (lo:=3116251) (a:=1875) (b:=1875) (join_sums term (lo:=3116251) (a:=937) (b:=938) (join_sums term (lo:=3116251) (a:=468) (b:=469) r3116251 r3116719) (join_sums term (lo:=3117188) (a:=469) (b:=469) r3117188 r3117657)) (join_sums term (lo:=3118126) (a:=937) (b:=938) (join_sums term (lo:=3118126) (a:=468) (b:=469) r3118126 r3118594) (join_sums term (lo:=3119063) (a:=469) (b:=469) r3119063 r3119532)))))) (join_sums term (lo:=3120001) (a:=15000) (b:=15000) (join_sums term (lo:=3120001) (a:=7500) (b:=7500) (join_sums term (lo:=3120001) (a:=3750) (b:=3750) (join_sums term (lo:=3120001) (a:=1875) (b:=1875) (join_sums term (lo:=3120001) (a:=937) (b:=938) (join_sums term (lo:=3120001) (a:=468) (b:=469) r3120001 r3120469) (join_sums term (lo:=3120938) (a:=469) (b:=469) r3120938 r3121407)) (join_sums term (lo:=3121876) (a:=937) (b:=938) (join_sums term (lo:=3121876) (a:=468) (b:=469) r3121876 r3122344) (join_sums term (lo:=3122813) (a:=469) (b:=469) r3122813 r3123282))) (join_sums term (lo:=3123751) (a:=1875) (b:=1875) (join_sums term (lo:=3123751) (a:=937) (b:=938) (join_sums term (lo:=3123751) (a:=468) (b:=469) r3123751 r3124219) (join_sums term (lo:=3124688) (a:=469) (b:=469) r3124688 r3125157)) (join_sums term (lo:=3125626) (a:=937) (b:=938) (join_sums term (lo:=3125626) (a:=468) (b:=469) r3125626 r3126094) (join_sums term (lo:=3126563) (a:=469) (b:=469) r3126563 r3127032)))) (join_sums term (lo:=3127501) (a:=3750) (b:=3750) (join_sums term (lo:=3127501) (a:=1875) (b:=1875) (join_sums term (lo:=3127501) (a:=937) (b:=938) (join_sums term (lo:=3127501) (a:=468) (b:=469) r3127501 r3127969) (join_sums term (lo:=3128438) (a:=469) (b:=469) r3128438 r3128907)) (join_sums term (lo:=3129376) (a:=937) (b:=938) (join_sums term (lo:=3129376) (a:=468) (b:=469) r3129376 r3129844) (join_sums term (lo:=3130313) (a:=469) (b:=469) r3130313 r3130782))) (join_sums term (lo:=3131251) (a:=1875) (b:=1875) (join_sums term (lo:=3131251) (a:=937) (b:=938) (join_sums term (lo:=3131251) (a:=468) (b:=469) r3131251 r3131719) (join_sums term (lo:=3132188) (a:=469) (b:=469) r3132188 r3132657)) (join_sums term (lo:=3133126) (a:=937) (b:=938) (join_sums term (lo:=3133126) (a:=468) (b:=469) r3133126 r3133594) (join_sums term (lo:=3134063) (a:=469) (b:=469) r3134063 r3134532))))) (join_sums term (lo:=3135001) (a:=7500) (b:=7500) (join_sums term (lo:=3135001) (a:=3750) (b:=3750) (join_sums term (lo:=3135001) (a:=1875) (b:=1875) (join_sums term (lo:=3135001) (a:=937) (b:=938) (join_sums term (lo:=3135001) (a:=468) (b:=469) r3135001 r3135469) (join_sums term (lo:=3135938) (a:=469) (b:=469) r3135938 r3136407)) (join_sums term (lo:=3136876) (a:=937) (b:=938) (join_sums term (lo:=3136876) (a:=468) (b:=469) r3136876 r3137344) (join_sums term (lo:=3137813) (a:=469) (b:=469) r3137813 r3138282))) (join_sums term (lo:=3138751) (a:=1875) (b:=1875) (join_sums term (lo:=3138751) (a:=937) (b:=938) (join_sums term (lo:=3138751) (a:=468) (b:=469) r3138751 r3139219) (join_sums term (lo:=3139688) (a:=469) (b:=469) r3139688 r3140157)) (join_sums term (lo:=3140626) (a:=937) (b:=938) (join_sums term (lo:=3140626) (a:=468) (b:=469) r3140626 r3141094) (join_sums term (lo:=3141563) (a:=469) (b:=469) r3141563 r3142032)))) (join_sums term (lo:=3142501) (a:=3750) (b:=3750) (join_sums term (lo:=3142501) (a:=1875) (b:=1875) (join_sums term (lo:=3142501) (a:=937) (b:=938) (join_sums term (lo:=3142501) (a:=468) (b:=469) r3142501 r3142969) (join_sums term (lo:=3143438) (a:=469) (b:=469) r3143438 r3143907)) (join_sums term (lo:=3144376) (a:=937) (b:=938) (join_sums term (lo:=3144376) (a:=468) (b:=469) r3144376 r3144844) (join_sums term (lo:=3145313) (a:=469) (b:=469) r3145313 r3145782))) (join_sums term (lo:=3146251) (a:=1875) (b:=1875) (join_sums term (lo:=3146251) (a:=937) (b:=938) (join_sums term (lo:=3146251) (a:=468) (b:=469) r3146251 r3146719) (join_sums term (lo:=3147188) (a:=469) (b:=469) r3147188 r3147657)) (join_sums term (lo:=3148126) (a:=937) (b:=938) (join_sums term (lo:=3148126) (a:=468) (b:=469) r3148126 r3148594) (join_sums term (lo:=3149063) (a:=469) (b:=469) r3149063 r3149532))))))))

private theorem rows : blockSum term 0 3150001 3419946054 :=
  join_sums term (lo:=0) (a:=3030001) (b:=120000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 3150000).filter (3030000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=3419946054 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From3030000To3150000
