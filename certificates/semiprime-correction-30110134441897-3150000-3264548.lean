import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 3,150,000 through 3,264,548

The sum covers 7,710 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From3150000To3264548

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


private abbrev term := contribution 30110134441897 3150000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 3150001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 3150000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r3150001 : blockSum term 3150001 447 12310692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3150448 : blockSum term 3150448 447 13537880 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3150895 : blockSum term 3150895 447 9022860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3151342 : blockSum term 3151342 448 15170225 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3151790 : blockSum term 3151790 447 13936144 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3152237 : blockSum term 3152237 448 12702732 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3152685 : blockSum term 3152685 447 11880215 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3153132 : blockSum term 3153132 448 12286561 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3153580 : blockSum term 3153580 447 15558621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3154027 : blockSum term 3154027 448 15553363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3154475 : blockSum term 3154475 447 9411295 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3154922 : blockSum term 3154922 448 10636104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3155370 : blockSum term 3155370 447 12269204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3155817 : blockSum term 3155817 448 12674382 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3156265 : blockSum term 3156265 447 15123008 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3156712 : blockSum term 3156712 448 11849762 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3157160 : blockSum term 3157160 447 14297641 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3157607 : blockSum term 3157607 447 10618306 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3158054 : blockSum term 3158054 447 8982361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3158501 : blockSum term 3158501 448 9796159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3158949 : blockSum term 3158949 447 12241720 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3159396 : blockSum term 3159396 448 12238074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3159844 : blockSum term 3159844 447 13050678 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3160291 : blockSum term 3160291 448 10600853 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3160739 : blockSum term 3160739 447 12635823 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3161186 : blockSum term 3161186 448 11409888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3161634 : blockSum term 3161634 447 9370037 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3162081 : blockSum term 3162081 448 8960068 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3162529 : blockSum term 3162529 447 13436503 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3162976 : blockSum term 3162976 448 11397380 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3163424 : blockSum term 3163424 447 15870953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3163871 : blockSum term 3163871 448 11798015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3164319 : blockSum term 3164319 447 11388078 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3164766 : blockSum term 3164766 447 14637755 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3165213 : blockSum term 3165213 447 14226925 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3165660 : blockSum term 3165660 448 12191111 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3166108 : blockSum term 3166108 447 16656137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3166555 : blockSum term 3166555 448 12589797 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3167003 : blockSum term 3167003 447 10556351 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3167450 : blockSum term 3167450 448 12177155 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3167898 : blockSum term 3167898 447 10956135 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3168345 : blockSum term 3168345 448 8924784 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3168793 : blockSum term 3168793 447 10950121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3169240 : blockSum term 3169240 448 12974366 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3169688 : blockSum term 3169688 447 12565394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3170135 : blockSum term 3170135 448 12967074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3170583 : blockSum term 3170583 447 12153176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3171030 : blockSum term 3171030 448 12554901 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3171478 : blockSum term 3171478 447 14575368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3171925 : blockSum term 3171925 448 14166459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3172373 : blockSum term 3172373 447 12543648 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3172820 : blockSum term 3172820 448 12540539 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3173268 : blockSum term 3173268 447 12536758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3173715 : blockSum term 3173715 448 10107419 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3174163 : blockSum term 3174163 447 13742083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3174610 : blockSum term 3174610 448 13333759 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3175058 : blockSum term 3175058 447 7271248 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3175505 : blockSum term 3175505 448 12115745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3175953 : blockSum term 3175953 447 11304961 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3176400 : blockSum term 3176400 448 12108881 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3176848 : blockSum term 3176848 447 12509264 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3177295 : blockSum term 3177295 448 12505621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3177743 : blockSum term 3177743 447 10485617 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3178190 : blockSum term 3178190 448 12498896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3178638 : blockSum term 3178638 447 12495306 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3179085 : blockSum term 3179085 447 10073962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3179532 : blockSum term 3179532 447 9265492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3179979 : blockSum term 3179979 448 10068506 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3180427 : blockSum term 3180427 447 14494370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3180874 : blockSum term 3180874 448 11672912 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3181322 : blockSum term 3181322 447 12474415 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3181769 : blockSum term 3181769 448 12873170 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3182217 : blockSum term 3182217 447 14075722 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3182664 : blockSum term 3182664 448 12865372 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3183112 : blockSum term 3183112 447 10852379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3183559 : blockSum term 3183559 448 16876633 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3184007 : blockSum term 3184007 447 10444655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3184454 : blockSum term 3184454 448 9237295 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3184902 : blockSum term 3184902 447 14052574 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3185349 : blockSum term 3185349 448 10034985 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3185797 : blockSum term 3185797 447 14045099 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3186244 : blockSum term 3186244 447 11232708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3186691 : blockSum term 3186691 447 13234550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3187138 : blockSum term 3187138 448 10424206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3187586 : blockSum term 3187586 447 12826391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3188033 : blockSum term 3188033 448 11219927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3188481 : blockSum term 3188481 447 12819279 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3188928 : blockSum term 3188928 448 14417249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3189376 : blockSum term 3189376 447 14012789 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3189823 : blockSum term 3189823 448 13207775 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3190271 : blockSum term 3190271 447 9603160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3190718 : blockSum term 3190718 448 10000572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3191166 : blockSum term 3191166 447 14396804 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3191613 : blockSum term 3191613 448 11194469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3192061 : blockSum term 3192061 447 12790141 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3192508 : blockSum term 3192508 448 10788789 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3192956 : blockSum term 3192956 447 13182708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3193403 : blockSum term 3193403 447 11981110 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3193850 : blockSum term 3193850 447 11977523 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3194297 : blockSum term 3194297 448 12373351 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3194745 : blockSum term 3194745 447 11572004 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3195192 : blockSum term 3195192 448 11568669 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3195640 : blockSum term 3195640 447 9970481 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3196087 : blockSum term 3196087 448 14752220 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3196535 : blockSum term 3196535 447 13152996 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3196982 : blockSum term 3196982 448 10360355 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3197430 : blockSum term 3197430 447 12349171 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3197877 : blockSum term 3197877 448 11947831 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3198325 : blockSum term 3198325 447 12740465 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3198772 : blockSum term 3198772 448 13134753 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3199220 : blockSum term 3199220 447 12732945 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3199667 : blockSum term 3199667 448 11138018 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3200115 : blockSum term 3200115 447 15509938 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3200562 : blockSum term 3200562 448 11927228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3201010 : blockSum term 3201010 447 12320961 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3201457 : blockSum term 3201457 448 11125440 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3201905 : blockSum term 3201905 447 16683372 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3202352 : blockSum term 3202352 448 12310440 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3202800 : blockSum term 3202800 447 10719060 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3203247 : blockSum term 3203247 448 13097459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3203695 : blockSum term 3203695 447 11506609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3204142 : blockSum term 3204142 448 9123264 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3204590 : blockSum term 3204590 447 12689811 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3205037 : blockSum term 3205037 448 9514676 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3205485 : blockSum term 3205485 447 10304967 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3205932 : blockSum term 3205932 448 12679698 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3206380 : blockSum term 3206380 447 11487788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3206827 : blockSum term 3206827 448 15444609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3207275 : blockSum term 3207275 447 11876926 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3207722 : blockSum term 3207722 447 12269359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3208169 : blockSum term 3208169 447 11078599 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3208616 : blockSum term 3208616 448 13448766 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3209064 : blockSum term 3209064 447 12258582 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3209511 : blockSum term 3209511 448 11069256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3209959 : blockSum term 3209959 447 13437475 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3210406 : blockSum term 3210406 448 12248258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3210854 : blockSum term 3210854 447 11060216 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3211301 : blockSum term 3211301 448 13031704 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3211749 : blockSum term 3211749 447 14212057 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3212196 : blockSum term 3212196 448 11050629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3212644 : blockSum term 3212644 447 9469443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3213091 : blockSum term 3213091 448 9467147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3213539 : blockSum term 3213539 447 9464277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3213986 : blockSum term 3213986 448 14192483 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3214434 : blockSum term 3214434 447 13400246 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3214881 : blockSum term 3214881 447 12214297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3215328 : blockSum term 3215328 447 11029118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3215775 : blockSum term 3215775 448 14963555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3216223 : blockSum term 3216223 447 12597055 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3216670 : blockSum term 3216670 448 10626032 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3217118 : blockSum term 3217118 447 12196789 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3217565 : blockSum term 3217565 448 12193050 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3218013 : blockSum term 3218013 447 11796631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3218460 : blockSum term 3218460 448 12579298 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3218908 : blockSum term 3218908 447 10217689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3219355 : blockSum term 3219355 448 9036583 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3219803 : blockSum term 3219803 447 12176321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3220250 : blockSum term 3220250 448 13350734 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3220698 : blockSum term 3220698 447 11384036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3221145 : blockSum term 3221145 448 12950243 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3221593 : blockSum term 3221593 447 9807974 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3222040 : blockSum term 3222040 447 11766407 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3222487 : blockSum term 3222487 447 11762704 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3222934 : blockSum term 3222934 448 11367475 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3223382 : blockSum term 3223382 447 12540024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3223829 : blockSum term 3223829 448 12536807 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3224277 : blockSum term 3224277 447 10574719 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3224724 : blockSum term 3224724 448 12529267 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3225172 : blockSum term 3225172 447 10960336 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3225619 : blockSum term 3225619 448 11348517 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3226067 : blockSum term 3226067 447 11736299 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3226514 : blockSum term 3226514 448 10950899 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3226962 : blockSum term 3226962 447 10947894 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3227409 : blockSum term 3227409 448 12899140 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3227857 : blockSum term 3227857 447 14067816 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3228304 : blockSum term 3228304 448 9766556 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3228752 : blockSum term 3228752 447 13278619 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3229199 : blockSum term 3229199 448 12493931 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3229647 : blockSum term 3229647 447 9367735 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3230094 : blockSum term 3230094 448 12486924 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3230542 : blockSum term 3230542 447 9362914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3230989 : blockSum term 3230989 448 12870384 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3231437 : blockSum term 3231437 447 12086889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3231884 : blockSum term 3231884 448 10524535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3232332 : blockSum term 3232332 447 13638863 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3232779 : blockSum term 3232779 448 10908176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3233227 : blockSum term 3233227 447 13241605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3233674 : blockSum term 3233674 448 12458826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3234122 : blockSum term 3234122 447 8563227 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3234569 : blockSum term 3234569 448 12841073 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3235017 : blockSum term 3235017 447 12059427 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3235464 : blockSum term 3235464 448 13611831 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3235912 : blockSum term 3235912 447 12829967 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3236359 : blockSum term 3236359 447 13604028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3236806 : blockSum term 3236806 447 11268321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3237253 : blockSum term 3237253 448 13207194 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3237701 : blockSum term 3237701 447 10484952 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3238148 : blockSum term 3238148 448 14364222 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3238596 : blockSum term 3238596 447 11254980 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3239043 : blockSum term 3239043 448 11251838 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3239491 : blockSum term 3239491 447 10085109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3239938 : blockSum term 3239938 448 11633195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3240386 : blockSum term 3240386 447 10854810 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3240833 : blockSum term 3240833 448 8914090 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3241281 : blockSum term 3241281 447 10848851 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3241728 : blockSum term 3241728 448 12782742 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3242176 : blockSum term 3242176 447 10068552 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3242623 : blockSum term 3242623 448 11227134 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3243071 : blockSum term 3243071 447 10836990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3243518 : blockSum term 3243518 447 10833955 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3243965 : blockSum term 3243965 447 13151828 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3244412 : blockSum term 3244412 448 9667657 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3244860 : blockSum term 3244860 447 12371053 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3245307 : blockSum term 3245307 448 10435050 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3245755 : blockSum term 3245755 447 12363990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3246202 : blockSum term 3246202 448 12360553 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3246650 : blockSum term 3246650 447 11584762 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3247097 : blockSum term 3247097 448 12353538 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3247545 : blockSum term 3247545 447 12349957 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3247992 : blockSum term 3247992 448 11574512 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3248440 : blockSum term 3248440 447 10028288 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3248887 : blockSum term 3248887 448 10796718 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3249335 : blockSum term 3249335 447 10408421 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3249782 : blockSum term 3249782 448 12332343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3250230 : blockSum term 3250230 447 11558220 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3250677 : blockSum term 3250677 447 11555302 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3251124 : blockSum term 3251124 447 11167166 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3251571 : blockSum term 3251571 448 12318889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3252019 : blockSum term 3252019 447 11160746 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3252466 : blockSum term 3252466 448 11157433 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3252914 : blockSum term 3252914 447 11154168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3253361 : blockSum term 3253361 448 9228572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3253809 : blockSum term 3253809 447 11917088 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3254256 : blockSum term 3254256 448 10376560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3254704 : blockSum term 3254704 447 9605431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3255151 : blockSum term 3255151 448 12674889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3255599 : blockSum term 3255599 447 13822916 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3256046 : blockSum term 3256046 448 10363972 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3256494 : blockSum term 3256494 447 11128861 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3256941 : blockSum term 3256941 448 12660557 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3257389 : blockSum term 3257389 447 11506176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3257836 : blockSum term 3257836 448 10736037 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3258284 : blockSum term 3258284 447 13032824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3258731 : blockSum term 3258731 448 9197210 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3259179 : blockSum term 3259179 447 11109898 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3259626 : blockSum term 3259626 448 13787719 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3260074 : blockSum term 3260074 447 13400840 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3260521 : blockSum term 3260521 448 13014025 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3260969 : blockSum term 3260969 447 11479614 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3261416 : blockSum term 3261416 448 10711456 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3261864 : blockSum term 3261864 447 9178720 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3262311 : blockSum term 3262311 448 11470142 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3262759 : blockSum term 3262759 447 11848796 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3263206 : blockSum term 3263206 448 11845397 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3263654 : blockSum term 3263654 447 10695842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r3264101 : blockSum term 3264101 448 9929307 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 3150001 114548 3053523629 := (join_sums term (lo:=3150001) (a:=57274) (b:=57274) (join_sums term (lo:=3150001) (a:=28637) (b:=28637) (join_sums term (lo:=3150001) (a:=14318) (b:=14319) (join_sums term (lo:=3150001) (a:=7159) (b:=7159) (join_sums term (lo:=3150001) (a:=3579) (b:=3580) (join_sums term (lo:=3150001) (a:=1789) (b:=1790) (join_sums term (lo:=3150001) (a:=894) (b:=895) (join_sums term (lo:=3150001) (a:=447) (b:=447) r3150001 r3150448) (join_sums term (lo:=3150895) (a:=447) (b:=448) r3150895 r3151342)) (join_sums term (lo:=3151790) (a:=895) (b:=895) (join_sums term (lo:=3151790) (a:=447) (b:=448) r3151790 r3152237) (join_sums term (lo:=3152685) (a:=447) (b:=448) r3152685 r3153132))) (join_sums term (lo:=3153580) (a:=1790) (b:=1790) (join_sums term (lo:=3153580) (a:=895) (b:=895) (join_sums term (lo:=3153580) (a:=447) (b:=448) r3153580 r3154027) (join_sums term (lo:=3154475) (a:=447) (b:=448) r3154475 r3154922)) (join_sums term (lo:=3155370) (a:=895) (b:=895) (join_sums term (lo:=3155370) (a:=447) (b:=448) r3155370 r3155817) (join_sums term (lo:=3156265) (a:=447) (b:=448) r3156265 r3156712)))) (join_sums term (lo:=3157160) (a:=3579) (b:=3580) (join_sums term (lo:=3157160) (a:=1789) (b:=1790) (join_sums term (lo:=3157160) (a:=894) (b:=895) (join_sums term (lo:=3157160) (a:=447) (b:=447) r3157160 r3157607) (join_sums term (lo:=3158054) (a:=447) (b:=448) r3158054 r3158501)) (join_sums term (lo:=3158949) (a:=895) (b:=895) (join_sums term (lo:=3158949) (a:=447) (b:=448) r3158949 r3159396) (join_sums term (lo:=3159844) (a:=447) (b:=448) r3159844 r3160291))) (join_sums term (lo:=3160739) (a:=1790) (b:=1790) (join_sums term (lo:=3160739) (a:=895) (b:=895) (join_sums term (lo:=3160739) (a:=447) (b:=448) r3160739 r3161186) (join_sums term (lo:=3161634) (a:=447) (b:=448) r3161634 r3162081)) (join_sums term (lo:=3162529) (a:=895) (b:=895) (join_sums term (lo:=3162529) (a:=447) (b:=448) r3162529 r3162976) (join_sums term (lo:=3163424) (a:=447) (b:=448) r3163424 r3163871))))) (join_sums term (lo:=3164319) (a:=7159) (b:=7160) (join_sums term (lo:=3164319) (a:=3579) (b:=3580) (join_sums term (lo:=3164319) (a:=1789) (b:=1790) (join_sums term (lo:=3164319) (a:=894) (b:=895) (join_sums term (lo:=3164319) (a:=447) (b:=447) r3164319 r3164766) (join_sums term (lo:=3165213) (a:=447) (b:=448) r3165213 r3165660)) (join_sums term (lo:=3166108) (a:=895) (b:=895) (join_sums term (lo:=3166108) (a:=447) (b:=448) r3166108 r3166555) (join_sums term (lo:=3167003) (a:=447) (b:=448) r3167003 r3167450))) (join_sums term (lo:=3167898) (a:=1790) (b:=1790) (join_sums term (lo:=3167898) (a:=895) (b:=895) (join_sums term (lo:=3167898) (a:=447) (b:=448) r3167898 r3168345) (join_sums term (lo:=3168793) (a:=447) (b:=448) r3168793 r3169240)) (join_sums term (lo:=3169688) (a:=895) (b:=895) (join_sums term (lo:=3169688) (a:=447) (b:=448) r3169688 r3170135) (join_sums term (lo:=3170583) (a:=447) (b:=448) r3170583 r3171030)))) (join_sums term (lo:=3171478) (a:=3580) (b:=3580) (join_sums term (lo:=3171478) (a:=1790) (b:=1790) (join_sums term (lo:=3171478) (a:=895) (b:=895) (join_sums term (lo:=3171478) (a:=447) (b:=448) r3171478 r3171925) (join_sums term (lo:=3172373) (a:=447) (b:=448) r3172373 r3172820)) (join_sums term (lo:=3173268) (a:=895) (b:=895) (join_sums term (lo:=3173268) (a:=447) (b:=448) r3173268 r3173715) (join_sums term (lo:=3174163) (a:=447) (b:=448) r3174163 r3174610))) (join_sums term (lo:=3175058) (a:=1790) (b:=1790) (join_sums term (lo:=3175058) (a:=895) (b:=895) (join_sums term (lo:=3175058) (a:=447) (b:=448) r3175058 r3175505) (join_sums term (lo:=3175953) (a:=447) (b:=448) r3175953 r3176400)) (join_sums term (lo:=3176848) (a:=895) (b:=895) (join_sums term (lo:=3176848) (a:=447) (b:=448) r3176848 r3177295) (join_sums term (lo:=3177743) (a:=447) (b:=448) r3177743 r3178190)))))) (join_sums term (lo:=3178638) (a:=14318) (b:=14319) (join_sums term (lo:=3178638) (a:=7159) (b:=7159) (join_sums term (lo:=3178638) (a:=3579) (b:=3580) (join_sums term (lo:=3178638) (a:=1789) (b:=1790) (join_sums term (lo:=3178638) (a:=894) (b:=895) (join_sums term (lo:=3178638) (a:=447) (b:=447) r3178638 r3179085) (join_sums term (lo:=3179532) (a:=447) (b:=448) r3179532 r3179979)) (join_sums term (lo:=3180427) (a:=895) (b:=895) (join_sums term (lo:=3180427) (a:=447) (b:=448) r3180427 r3180874) (join_sums term (lo:=3181322) (a:=447) (b:=448) r3181322 r3181769))) (join_sums term (lo:=3182217) (a:=1790) (b:=1790) (join_sums term (lo:=3182217) (a:=895) (b:=895) (join_sums term (lo:=3182217) (a:=447) (b:=448) r3182217 r3182664) (join_sums term (lo:=3183112) (a:=447) (b:=448) r3183112 r3183559)) (join_sums term (lo:=3184007) (a:=895) (b:=895) (join_sums term (lo:=3184007) (a:=447) (b:=448) r3184007 r3184454) (join_sums term (lo:=3184902) (a:=447) (b:=448) r3184902 r3185349)))) (join_sums term (lo:=3185797) (a:=3579) (b:=3580) (join_sums term (lo:=3185797) (a:=1789) (b:=1790) (join_sums term (lo:=3185797) (a:=894) (b:=895) (join_sums term (lo:=3185797) (a:=447) (b:=447) r3185797 r3186244) (join_sums term (lo:=3186691) (a:=447) (b:=448) r3186691 r3187138)) (join_sums term (lo:=3187586) (a:=895) (b:=895) (join_sums term (lo:=3187586) (a:=447) (b:=448) r3187586 r3188033) (join_sums term (lo:=3188481) (a:=447) (b:=448) r3188481 r3188928))) (join_sums term (lo:=3189376) (a:=1790) (b:=1790) (join_sums term (lo:=3189376) (a:=895) (b:=895) (join_sums term (lo:=3189376) (a:=447) (b:=448) r3189376 r3189823) (join_sums term (lo:=3190271) (a:=447) (b:=448) r3190271 r3190718)) (join_sums term (lo:=3191166) (a:=895) (b:=895) (join_sums term (lo:=3191166) (a:=447) (b:=448) r3191166 r3191613) (join_sums term (lo:=3192061) (a:=447) (b:=448) r3192061 r3192508))))) (join_sums term (lo:=3192956) (a:=7159) (b:=7160) (join_sums term (lo:=3192956) (a:=3579) (b:=3580) (join_sums term (lo:=3192956) (a:=1789) (b:=1790) (join_sums term (lo:=3192956) (a:=894) (b:=895) (join_sums term (lo:=3192956) (a:=447) (b:=447) r3192956 r3193403) (join_sums term (lo:=3193850) (a:=447) (b:=448) r3193850 r3194297)) (join_sums term (lo:=3194745) (a:=895) (b:=895) (join_sums term (lo:=3194745) (a:=447) (b:=448) r3194745 r3195192) (join_sums term (lo:=3195640) (a:=447) (b:=448) r3195640 r3196087))) (join_sums term (lo:=3196535) (a:=1790) (b:=1790) (join_sums term (lo:=3196535) (a:=895) (b:=895) (join_sums term (lo:=3196535) (a:=447) (b:=448) r3196535 r3196982) (join_sums term (lo:=3197430) (a:=447) (b:=448) r3197430 r3197877)) (join_sums term (lo:=3198325) (a:=895) (b:=895) (join_sums term (lo:=3198325) (a:=447) (b:=448) r3198325 r3198772) (join_sums term (lo:=3199220) (a:=447) (b:=448) r3199220 r3199667)))) (join_sums term (lo:=3200115) (a:=3580) (b:=3580) (join_sums term (lo:=3200115) (a:=1790) (b:=1790) (join_sums term (lo:=3200115) (a:=895) (b:=895) (join_sums term (lo:=3200115) (a:=447) (b:=448) r3200115 r3200562) (join_sums term (lo:=3201010) (a:=447) (b:=448) r3201010 r3201457)) (join_sums term (lo:=3201905) (a:=895) (b:=895) (join_sums term (lo:=3201905) (a:=447) (b:=448) r3201905 r3202352) (join_sums term (lo:=3202800) (a:=447) (b:=448) r3202800 r3203247))) (join_sums term (lo:=3203695) (a:=1790) (b:=1790) (join_sums term (lo:=3203695) (a:=895) (b:=895) (join_sums term (lo:=3203695) (a:=447) (b:=448) r3203695 r3204142) (join_sums term (lo:=3204590) (a:=447) (b:=448) r3204590 r3205037)) (join_sums term (lo:=3205485) (a:=895) (b:=895) (join_sums term (lo:=3205485) (a:=447) (b:=448) r3205485 r3205932) (join_sums term (lo:=3206380) (a:=447) (b:=448) r3206380 r3206827))))))) (join_sums term (lo:=3207275) (a:=28637) (b:=28637) (join_sums term (lo:=3207275) (a:=14318) (b:=14319) (join_sums term (lo:=3207275) (a:=7159) (b:=7159) (join_sums term (lo:=3207275) (a:=3579) (b:=3580) (join_sums term (lo:=3207275) (a:=1789) (b:=1790) (join_sums term (lo:=3207275) (a:=894) (b:=895) (join_sums term (lo:=3207275) (a:=447) (b:=447) r3207275 r3207722) (join_sums term (lo:=3208169) (a:=447) (b:=448) r3208169 r3208616)) (join_sums term (lo:=3209064) (a:=895) (b:=895) (join_sums term (lo:=3209064) (a:=447) (b:=448) r3209064 r3209511) (join_sums term (lo:=3209959) (a:=447) (b:=448) r3209959 r3210406))) (join_sums term (lo:=3210854) (a:=1790) (b:=1790) (join_sums term (lo:=3210854) (a:=895) (b:=895) (join_sums term (lo:=3210854) (a:=447) (b:=448) r3210854 r3211301) (join_sums term (lo:=3211749) (a:=447) (b:=448) r3211749 r3212196)) (join_sums term (lo:=3212644) (a:=895) (b:=895) (join_sums term (lo:=3212644) (a:=447) (b:=448) r3212644 r3213091) (join_sums term (lo:=3213539) (a:=447) (b:=448) r3213539 r3213986)))) (join_sums term (lo:=3214434) (a:=3579) (b:=3580) (join_sums term (lo:=3214434) (a:=1789) (b:=1790) (join_sums term (lo:=3214434) (a:=894) (b:=895) (join_sums term (lo:=3214434) (a:=447) (b:=447) r3214434 r3214881) (join_sums term (lo:=3215328) (a:=447) (b:=448) r3215328 r3215775)) (join_sums term (lo:=3216223) (a:=895) (b:=895) (join_sums term (lo:=3216223) (a:=447) (b:=448) r3216223 r3216670) (join_sums term (lo:=3217118) (a:=447) (b:=448) r3217118 r3217565))) (join_sums term (lo:=3218013) (a:=1790) (b:=1790) (join_sums term (lo:=3218013) (a:=895) (b:=895) (join_sums term (lo:=3218013) (a:=447) (b:=448) r3218013 r3218460) (join_sums term (lo:=3218908) (a:=447) (b:=448) r3218908 r3219355)) (join_sums term (lo:=3219803) (a:=895) (b:=895) (join_sums term (lo:=3219803) (a:=447) (b:=448) r3219803 r3220250) (join_sums term (lo:=3220698) (a:=447) (b:=448) r3220698 r3221145))))) (join_sums term (lo:=3221593) (a:=7159) (b:=7160) (join_sums term (lo:=3221593) (a:=3579) (b:=3580) (join_sums term (lo:=3221593) (a:=1789) (b:=1790) (join_sums term (lo:=3221593) (a:=894) (b:=895) (join_sums term (lo:=3221593) (a:=447) (b:=447) r3221593 r3222040) (join_sums term (lo:=3222487) (a:=447) (b:=448) r3222487 r3222934)) (join_sums term (lo:=3223382) (a:=895) (b:=895) (join_sums term (lo:=3223382) (a:=447) (b:=448) r3223382 r3223829) (join_sums term (lo:=3224277) (a:=447) (b:=448) r3224277 r3224724))) (join_sums term (lo:=3225172) (a:=1790) (b:=1790) (join_sums term (lo:=3225172) (a:=895) (b:=895) (join_sums term (lo:=3225172) (a:=447) (b:=448) r3225172 r3225619) (join_sums term (lo:=3226067) (a:=447) (b:=448) r3226067 r3226514)) (join_sums term (lo:=3226962) (a:=895) (b:=895) (join_sums term (lo:=3226962) (a:=447) (b:=448) r3226962 r3227409) (join_sums term (lo:=3227857) (a:=447) (b:=448) r3227857 r3228304)))) (join_sums term (lo:=3228752) (a:=3580) (b:=3580) (join_sums term (lo:=3228752) (a:=1790) (b:=1790) (join_sums term (lo:=3228752) (a:=895) (b:=895) (join_sums term (lo:=3228752) (a:=447) (b:=448) r3228752 r3229199) (join_sums term (lo:=3229647) (a:=447) (b:=448) r3229647 r3230094)) (join_sums term (lo:=3230542) (a:=895) (b:=895) (join_sums term (lo:=3230542) (a:=447) (b:=448) r3230542 r3230989) (join_sums term (lo:=3231437) (a:=447) (b:=448) r3231437 r3231884))) (join_sums term (lo:=3232332) (a:=1790) (b:=1790) (join_sums term (lo:=3232332) (a:=895) (b:=895) (join_sums term (lo:=3232332) (a:=447) (b:=448) r3232332 r3232779) (join_sums term (lo:=3233227) (a:=447) (b:=448) r3233227 r3233674)) (join_sums term (lo:=3234122) (a:=895) (b:=895) (join_sums term (lo:=3234122) (a:=447) (b:=448) r3234122 r3234569) (join_sums term (lo:=3235017) (a:=447) (b:=448) r3235017 r3235464)))))) (join_sums term (lo:=3235912) (a:=14318) (b:=14319) (join_sums term (lo:=3235912) (a:=7159) (b:=7159) (join_sums term (lo:=3235912) (a:=3579) (b:=3580) (join_sums term (lo:=3235912) (a:=1789) (b:=1790) (join_sums term (lo:=3235912) (a:=894) (b:=895) (join_sums term (lo:=3235912) (a:=447) (b:=447) r3235912 r3236359) (join_sums term (lo:=3236806) (a:=447) (b:=448) r3236806 r3237253)) (join_sums term (lo:=3237701) (a:=895) (b:=895) (join_sums term (lo:=3237701) (a:=447) (b:=448) r3237701 r3238148) (join_sums term (lo:=3238596) (a:=447) (b:=448) r3238596 r3239043))) (join_sums term (lo:=3239491) (a:=1790) (b:=1790) (join_sums term (lo:=3239491) (a:=895) (b:=895) (join_sums term (lo:=3239491) (a:=447) (b:=448) r3239491 r3239938) (join_sums term (lo:=3240386) (a:=447) (b:=448) r3240386 r3240833)) (join_sums term (lo:=3241281) (a:=895) (b:=895) (join_sums term (lo:=3241281) (a:=447) (b:=448) r3241281 r3241728) (join_sums term (lo:=3242176) (a:=447) (b:=448) r3242176 r3242623)))) (join_sums term (lo:=3243071) (a:=3579) (b:=3580) (join_sums term (lo:=3243071) (a:=1789) (b:=1790) (join_sums term (lo:=3243071) (a:=894) (b:=895) (join_sums term (lo:=3243071) (a:=447) (b:=447) r3243071 r3243518) (join_sums term (lo:=3243965) (a:=447) (b:=448) r3243965 r3244412)) (join_sums term (lo:=3244860) (a:=895) (b:=895) (join_sums term (lo:=3244860) (a:=447) (b:=448) r3244860 r3245307) (join_sums term (lo:=3245755) (a:=447) (b:=448) r3245755 r3246202))) (join_sums term (lo:=3246650) (a:=1790) (b:=1790) (join_sums term (lo:=3246650) (a:=895) (b:=895) (join_sums term (lo:=3246650) (a:=447) (b:=448) r3246650 r3247097) (join_sums term (lo:=3247545) (a:=447) (b:=448) r3247545 r3247992)) (join_sums term (lo:=3248440) (a:=895) (b:=895) (join_sums term (lo:=3248440) (a:=447) (b:=448) r3248440 r3248887) (join_sums term (lo:=3249335) (a:=447) (b:=448) r3249335 r3249782))))) (join_sums term (lo:=3250230) (a:=7159) (b:=7160) (join_sums term (lo:=3250230) (a:=3579) (b:=3580) (join_sums term (lo:=3250230) (a:=1789) (b:=1790) (join_sums term (lo:=3250230) (a:=894) (b:=895) (join_sums term (lo:=3250230) (a:=447) (b:=447) r3250230 r3250677) (join_sums term (lo:=3251124) (a:=447) (b:=448) r3251124 r3251571)) (join_sums term (lo:=3252019) (a:=895) (b:=895) (join_sums term (lo:=3252019) (a:=447) (b:=448) r3252019 r3252466) (join_sums term (lo:=3252914) (a:=447) (b:=448) r3252914 r3253361))) (join_sums term (lo:=3253809) (a:=1790) (b:=1790) (join_sums term (lo:=3253809) (a:=895) (b:=895) (join_sums term (lo:=3253809) (a:=447) (b:=448) r3253809 r3254256) (join_sums term (lo:=3254704) (a:=447) (b:=448) r3254704 r3255151)) (join_sums term (lo:=3255599) (a:=895) (b:=895) (join_sums term (lo:=3255599) (a:=447) (b:=448) r3255599 r3256046) (join_sums term (lo:=3256494) (a:=447) (b:=448) r3256494 r3256941)))) (join_sums term (lo:=3257389) (a:=3580) (b:=3580) (join_sums term (lo:=3257389) (a:=1790) (b:=1790) (join_sums term (lo:=3257389) (a:=895) (b:=895) (join_sums term (lo:=3257389) (a:=447) (b:=448) r3257389 r3257836) (join_sums term (lo:=3258284) (a:=447) (b:=448) r3258284 r3258731)) (join_sums term (lo:=3259179) (a:=895) (b:=895) (join_sums term (lo:=3259179) (a:=447) (b:=448) r3259179 r3259626) (join_sums term (lo:=3260074) (a:=447) (b:=448) r3260074 r3260521))) (join_sums term (lo:=3260969) (a:=1790) (b:=1790) (join_sums term (lo:=3260969) (a:=895) (b:=895) (join_sums term (lo:=3260969) (a:=447) (b:=448) r3260969 r3261416) (join_sums term (lo:=3261864) (a:=447) (b:=448) r3261864 r3262311)) (join_sums term (lo:=3262759) (a:=895) (b:=895) (join_sums term (lo:=3262759) (a:=447) (b:=448) r3262759 r3263206) (join_sums term (lo:=3263654) (a:=447) (b:=448) r3263654 r3264101))))))))

private theorem rows : blockSum term 0 3264549 3053523629 :=
  join_sums term (lo:=0) (a:=3150001) (b:=114548) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 3264548).filter (3150000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=3053523629 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From3150000To3264548
