import certificates.«prime-table-through-9223368»

/-!
# Semiprime correction above 3,264,548 through 4,500,000 at 30,110,134,441,897

The proof uses a shared certified prime-counting table for every prime and quotient.
-/
open Finset
namespace CorrectionNext30

private def contribution (x y : ℕ) (tab : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then tab (x/p) - tab (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z b value : ℕ} (tab : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, n≤b → tab n = Nat.primeCounting n)
    (prime_ok : ∀ n, n≤b → (prime n=true ↔ n.Prime))
    (hz : z≤b) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y tab prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y tab prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p≤b := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ (le_trans ub hq),ok _ (by omega : p-1≤b)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y tab prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y tab prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result

private abbrev tab := CheckpointA28006Slim.fast

private abbrev prime := CheckpointA28006Slim.prime
private theorem prime_ok (n : ℕ) (hn : n≤9223368) : prime n=true ↔ n.Prime := CheckpointA28006Slim.prime_ok n hn

private abbrev term := contribution 30110134441897 3264548 tab prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))

private theorem before : blockSum term 0 3264549 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 3264548 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 6000 in
private theorem block3264549 : blockSum term 3264549 1206 33206064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3265755 : blockSum term 3265755 1206 31273317 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3266961 : blockSum term 3266961 1206 31249127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3268167 : blockSum term 3268167 1207 29701518 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3269374 : blockSum term 3269374 1206 29678547 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3270580 : blockSum term 3270580 1207 29276034 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3271787 : blockSum term 3271787 1206 30394286 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3272993 : blockSum term 3272993 1207 29611555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3274200 : blockSum term 3274200 1206 30347407 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3275406 : blockSum term 3275406 1207 35251117 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3276613 : blockSum term 3276613 1206 32950011 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3277819 : blockSum term 3277819 1207 34059169 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3279026 : blockSum term 3279026 1206 22688808 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3280232 : blockSum term 3280232 1207 32118303 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3281439 : blockSum term 3281439 1206 26052132 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3282645 : blockSum term 3282645 1207 33955342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3283852 : blockSum term 3283852 1206 29405195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3285058 : blockSum term 3285058 1207 28251759 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3286265 : blockSum term 3286265 1206 31242482 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3287471 : blockSum term 3287471 1207 30841837 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3288678 : blockSum term 3288678 1206 31570261 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3289884 : blockSum term 3289884 1207 31921758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3291091 : blockSum term 3291091 1206 31521588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3292297 : blockSum term 3292297 1207 27747831 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3293504 : blockSum term 3293504 1206 27725689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3294710 : blockSum term 3294710 1207 29950408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3295917 : blockSum term 3295917 1206 30674181 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3297123 : blockSum term 3297123 1207 31024673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3298330 : blockSum term 3298330 1206 27639503 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3299536 : blockSum term 3299536 1207 24633091 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3300743 : blockSum term 3300743 1206 28718058 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3301949 : blockSum term 3301949 1207 27950861 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3303156 : blockSum term 3303156 1206 30536648 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3304362 : blockSum term 3304362 1207 32001558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3305569 : blockSum term 3305569 1206 33463980 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3306775 : blockSum term 3306775 1207 27122265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3307982 : blockSum term 3307982 1206 33039067 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3309188 : blockSum term 3309188 1207 29675905 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3310395 : blockSum term 3310395 1206 29282048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3311601 : blockSum term 3311601 1207 31482738 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3312808 : blockSum term 3312808 1206 30716002 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3314014 : blockSum term 3314014 1207 29212858 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3315221 : blockSum term 3315221 1206 28081526 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3316427 : blockSum term 3316427 1207 31014177 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3317634 : blockSum term 3317634 1206 26931849 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3318840 : blockSum term 3318840 1207 28754716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3320047 : blockSum term 3320047 1206 27627197 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3321253 : blockSum term 3321253 1207 33494385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3322460 : blockSum term 3322460 1206 26480994 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3323666 : blockSum term 3323666 1207 32339712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3324873 : blockSum term 3324873 1206 31212838 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3326079 : blockSum term 3326079 1207 28987668 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3327286 : blockSum term 3327286 1206 28966044 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3328492 : blockSum term 3328492 1207 30774486 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3329699 : blockSum term 3329699 1206 26358361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3330905 : blockSum term 3330905 1207 29630361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3332112 : blockSum term 3332112 1206 28509914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3333318 : blockSum term 3333318 1207 26662963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3334525 : blockSum term 3334525 1206 28466708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3335731 : blockSum term 3335731 1207 27716686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3336938 : blockSum term 3336938 1206 32067418 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3338144 : blockSum term 3338144 1207 28400113 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3339351 : blockSum term 3339351 1206 30561763 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3340557 : blockSum term 3340557 1207 32719032 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3341764 : blockSum term 3341764 1206 31240738 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3342970 : blockSum term 3342970 1207 25409466 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3344177 : blockSum term 3344177 1206 28655924 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3345383 : blockSum term 3345383 1207 28271729 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3346590 : blockSum term 3346590 1206 28249482 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3347796 : blockSum term 3347796 1207 30760227 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3349003 : blockSum term 3349003 1206 28205651 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3350209 : blockSum term 3350209 1207 31072526 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3351416 : blockSum term 3351416 1206 23827944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3352622 : blockSum term 3352622 1207 30302082 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3353829 : blockSum term 3353829 1206 27394587 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3355035 : blockSum term 3355035 1207 28094267 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3356242 : blockSum term 3356242 1206 26273049 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3357448 : blockSum term 3357448 1207 25175304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3358655 : blockSum term 3358655 1206 25874139 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3359861 : blockSum term 3359861 1207 29804949 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3361068 : blockSum term 3361068 1206 27988906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3362274 : blockSum term 3362274 1207 24381712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3363481 : blockSum term 3363481 1206 32243679 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3364687 : blockSum term 3364687 1207 33649221 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3365894 : blockSum term 3365894 1206 28615462 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3367100 : blockSum term 3367100 1207 31095301 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3368307 : blockSum term 3368307 1206 29998236 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3369513 : blockSum term 3369513 1207 28903967 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3370720 : blockSum term 3370720 1206 28168682 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3371926 : blockSum term 3371926 1207 28146758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3373133 : blockSum term 3373133 1206 25276070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3374339 : blockSum term 3374339 1207 30947163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3375546 : blockSum term 3375546 1206 26301871 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3376752 : blockSum term 3376752 1207 32674091 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3377959 : blockSum term 3377959 1206 30872836 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3379165 : blockSum term 3379165 1207 23756666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3380372 : blockSum term 3380372 1206 30114773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3381578 : blockSum term 3381578 1207 27967383 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3382785 : blockSum term 3382785 1206 27946569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3383991 : blockSum term 3383991 1207 30044453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3385198 : blockSum term 3385198 1206 27548450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3386404 : blockSum term 3386404 1207 31761542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3387611 : blockSum term 3387611 1206 27505483 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3388817 : blockSum term 3388817 1207 28187949 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3390024 : blockSum term 3390024 1206 29574620 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3391230 : blockSum term 3391230 1207 24978029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3392437 : blockSum term 3392437 1206 27418567 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3393643 : blockSum term 3393643 1207 28450145 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3394850 : blockSum term 3394850 1206 29831444 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3396056 : blockSum term 3396056 1207 29457691 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3397263 : blockSum term 3397263 1206 29084467 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3398469 : blockSum term 3398469 1207 25209823 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3399676 : blockSum term 3399676 1206 26591546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3400882 : blockSum term 3400882 1207 30065979 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3402089 : blockSum term 3402089 1206 31788195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3403295 : blockSum term 3403295 1207 31411652 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3404502 : blockSum term 3404502 1206 23715644 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3405708 : blockSum term 3405708 1207 27182616 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3406915 : blockSum term 3406915 1206 26465527 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3408121 : blockSum term 3408121 1207 32706383 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3409328 : blockSum term 3409328 1206 26075329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3410534 : blockSum term 3410534 1207 31613020 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3411741 : blockSum term 3411741 1206 29503047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3412947 : blockSum term 3412947 1207 27051932 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3414154 : blockSum term 3414154 1206 27032398 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3415360 : blockSum term 3415360 1207 27009691 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3416567 : blockSum term 3416567 1206 27334524 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3417773 : blockSum term 3417773 1207 28350621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3418980 : blockSum term 3418980 1206 25219509 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3420186 : blockSum term 3420186 1207 27962149 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3421393 : blockSum term 3421393 1206 29318430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3422599 : blockSum term 3422599 1207 24814877 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3423806 : blockSum term 3423806 1206 29617074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3425012 : blockSum term 3425012 1207 28217631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3426219 : blockSum term 3426219 1206 29570324 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3427425 : blockSum term 3427425 1207 27484250 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3428632 : blockSum term 3428632 1206 27117485 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3429838 : blockSum term 3429838 1207 24352970 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3431045 : blockSum term 3431045 1206 29475649 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3432251 : blockSum term 3432251 1207 29108967 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3433458 : blockSum term 3433458 1206 27032505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3434664 : blockSum term 3434664 1207 26668369 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3435871 : blockSum term 3435871 1206 30404759 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3437077 : blockSum term 3437077 1207 30720147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3438284 : blockSum term 3438284 1206 25919606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3439490 : blockSum term 3439490 1207 28626356 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3440697 : blockSum term 3440697 1206 26899963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3441903 : blockSum term 3441903 1207 27899629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3443110 : blockSum term 3443110 1206 29917196 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3444316 : blockSum term 3444316 1207 29213176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3445523 : blockSum term 3445523 1206 24438482 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3446729 : blockSum term 3446729 1207 25097909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3447936 : blockSum term 3447936 1206 28127593 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3449142 : blockSum term 3449142 1207 31490016 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3450349 : blockSum term 3450349 1206 25375043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3451555 : blockSum term 3451555 1207 22651040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3452762 : blockSum term 3452762 1206 26011152 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3453968 : blockSum term 3453968 1207 29027315 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3455175 : blockSum term 3455175 1206 27317453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3456381 : blockSum term 3456381 1207 26620315 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3457588 : blockSum term 3457588 1206 25926439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3458794 : blockSum term 3458794 1207 24223857 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3460001 : blockSum term 3460001 1206 25885406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3461207 : blockSum term 3461207 1207 27208241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3462414 : blockSum term 3462414 1206 25507739 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3463620 : blockSum term 3463620 1207 23811079 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3464827 : blockSum term 3464827 1206 28818350 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3466033 : blockSum term 3466033 1207 24777551 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3467240 : blockSum term 3467240 1206 27767846 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3468446 : blockSum term 3468446 1207 27745438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3469653 : blockSum term 3469653 1206 25051966 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3470859 : blockSum term 3470859 1207 25699925 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3472066 : blockSum term 3472066 1206 27013609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3473272 : blockSum term 3473272 1207 28324312 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3474479 : blockSum term 3474479 1206 22975416 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3475685 : blockSum term 3475685 1207 23956141 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3476892 : blockSum term 3476892 1206 26263119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3478098 : blockSum term 3478098 1207 24913692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3479305 : blockSum term 3479305 1206 26883836 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3480511 : blockSum term 3480511 1207 26529640 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3481718 : blockSum term 3481718 1206 22201712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3482924 : blockSum term 3482924 1207 28474903 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3484131 : blockSum term 3484131 1206 24152271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3485337 : blockSum term 3485337 1207 24462769 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3486544 : blockSum term 3486544 1206 25764845 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3487750 : blockSum term 3487750 1207 24753846 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3488957 : blockSum term 3488957 1206 25394764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3490163 : blockSum term 3490163 1207 28997740 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3491370 : blockSum term 3491370 1206 26669777 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3492576 : blockSum term 3492576 1207 27306242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3493783 : blockSum term 3493783 1206 27283890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3494989 : blockSum term 3494989 1207 24634127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3496196 : blockSum term 3496196 1206 25927142 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3497402 : blockSum term 3497402 1207 22953763 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3498609 : blockSum term 3498609 1206 28833305 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3499815 : blockSum term 3499815 1207 22589937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3501022 : blockSum term 3501022 1206 23880427 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3502228 : blockSum term 3502228 1207 28110029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3503435 : blockSum term 3503435 1206 29393697 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3504641 : blockSum term 3504641 1207 27410353 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3505848 : blockSum term 3505848 1206 21846430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3507054 : blockSum term 3507054 1207 25413126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3508261 : blockSum term 3508261 1206 25718221 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3509467 : blockSum term 3509467 1207 26347371 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3510674 : blockSum term 3510674 1206 26975057 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3511880 : blockSum term 3511880 1207 29549172 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3513087 : blockSum term 3513087 1206 24657469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3514293 : blockSum term 3514293 1207 26905994 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3515500 : blockSum term 3515500 1206 22998708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3516706 : blockSum term 3516706 1207 23304219 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3517913 : blockSum term 3517913 1206 24903269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3519119 : blockSum term 3519119 1207 28115252 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3520326 : blockSum term 3520326 1206 26152375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3521532 : blockSum term 3521532 1207 23550471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3522739 : blockSum term 3522739 1206 22887961 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3523945 : blockSum term 3523945 1207 26412636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3525152 : blockSum term 3525152 1206 25102692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3526358 : blockSum term 3526358 1207 21545060 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3527565 : blockSum term 3527565 1206 26669594 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3528771 : blockSum term 3528771 1207 23436995 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3529978 : blockSum term 3529978 1206 26946854 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3531184 : blockSum term 3531184 1207 25642948 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3532391 : blockSum term 3532391 1206 27221825 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3533597 : blockSum term 3533597 1207 25599008 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3534804 : blockSum term 3534804 1206 29093972 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3536010 : blockSum term 3536010 1207 23958542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3537217 : blockSum term 3537217 1206 23619893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3538423 : blockSum term 3538423 1207 22324559 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3539630 : blockSum term 3539630 1206 25812839 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3540836 : blockSum term 3540836 1207 23880379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3542043 : blockSum term 3542043 1206 24498249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3543249 : blockSum term 3543249 1207 24478817 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3544456 : blockSum term 3544456 1206 26363938 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3545662 : blockSum term 3545662 1207 26024393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3546869 : blockSum term 3546869 1206 27905319 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3548075 : blockSum term 3548075 1207 23446762 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3549282 : blockSum term 3549282 1206 22477499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3550488 : blockSum term 3550488 1207 25305584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3551695 : blockSum term 3551695 1206 24968449 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3552901 : blockSum term 3552901 1207 24632083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3554108 : blockSum term 3554108 1206 27765592 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3555314 : blockSum term 3555314 1207 25220945 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3556521 : blockSum term 3556521 1206 24886529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3557727 : blockSum term 3557727 1207 24866320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3558934 : blockSum term 3558934 1206 27990393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3560140 : blockSum term 3560140 1207 22938863 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3561347 : blockSum term 3561347 1206 23547876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3562553 : blockSum term 3562553 1207 26038125 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3563760 : blockSum term 3563760 1206 26329584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3564966 : blockSum term 3564966 1207 25055783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3566173 : blockSum term 3566173 1206 25974314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3567379 : blockSum term 3567379 1207 27204459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3568586 : blockSum term 3568586 1206 23744302 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3569792 : blockSum term 3569792 1207 27159207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3570999 : blockSum term 3570999 1206 24640880 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3572205 : blockSum term 3572205 1207 20569996 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3573412 : blockSum term 3573412 1206 24603228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3574618 : blockSum term 3574618 1206 23338258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3575824 : blockSum term 3575824 1206 27050179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3577030 : blockSum term 3577030 1207 24541297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3578237 : blockSum term 3578237 1206 22038425 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3579443 : blockSum term 3579443 1207 24500877 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3580650 : blockSum term 3580650 1206 25719689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3581856 : blockSum term 3581856 1207 24150671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3583063 : blockSum term 3583063 1206 26606260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3584269 : blockSum term 3584269 1207 24110363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3585476 : blockSum term 3585476 1206 24090382 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3586682 : blockSum term 3586682 1207 29008012 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3587889 : blockSum term 3587889 1206 23125028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3589095 : blockSum term 3589095 1207 23721591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3590302 : blockSum term 3590302 1206 24010874 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3591508 : blockSum term 3591508 1207 20607124 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3592715 : blockSum term 3592715 1206 24278849 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3593921 : blockSum term 3593921 1207 27941411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3595128 : blockSum term 3595128 1206 23929603 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3596334 : blockSum term 3596334 1207 26974976 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3597541 : blockSum term 3597541 1206 24502427 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3598747 : blockSum term 3598747 1207 24481986 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3599954 : blockSum term 3599954 1206 27213044 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3601160 : blockSum term 3601160 1207 22914581 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3602367 : blockSum term 3602367 1206 23506326 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3603573 : blockSum term 3603573 1207 25012001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3604780 : blockSum term 3604780 1206 26209852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3605986 : blockSum term 3605986 1207 25273185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3607193 : blockSum term 3607193 1206 26468384 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3608399 : blockSum term 3608399 1207 25229059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3609606 : blockSum term 3609606 1206 26725379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3610812 : blockSum term 3610812 1207 21544364 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3612019 : blockSum term 3612019 1206 28802670 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3613225 : blockSum term 3613225 1207 25445113 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3614432 : blockSum term 3614432 1206 22398136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3615638 : blockSum term 3615638 1207 24798546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3616845 : blockSum term 3616845 1206 26590575 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3618051 : blockSum term 3618051 1207 22342115 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3619258 : blockSum term 3619258 1206 22021306 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3620464 : blockSum term 3620464 1207 26524018 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3621671 : blockSum term 3621671 1206 28006039 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3622877 : blockSum term 3622877 1207 23468269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3624084 : blockSum term 3624084 1206 25553798 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3625290 : blockSum term 3625290 1207 24029487 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3626497 : blockSum term 3626497 1206 22809402 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3627703 : blockSum term 3627703 1207 24289173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3628910 : blockSum term 3628910 1206 24868248 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3630116 : blockSum term 3630116 1207 24547412 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3631323 : blockSum term 3631323 1206 23927855 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3632529 : blockSum term 3632529 1207 25701762 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3633736 : blockSum term 3633736 1206 22096924 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3634942 : blockSum term 3634942 1207 21779411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3636149 : blockSum term 3636149 1206 22655349 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3637355 : blockSum term 3637355 1207 24125002 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3638562 : blockSum term 3638562 1206 22616500 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3639768 : blockSum term 3639768 1207 23787453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3640975 : blockSum term 3640975 1206 24658217 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3642181 : blockSum term 3642181 1207 21372504 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3643388 : blockSum term 3643388 1206 24024525 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3644594 : blockSum term 3644594 1207 23707405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3645801 : blockSum term 3645801 1206 24279843 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3647007 : blockSum term 3647007 1207 20413843 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3648214 : blockSum term 3648214 1206 23057912 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3649420 : blockSum term 3649420 1207 22152057 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3650627 : blockSum term 3650627 1206 19183914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3651833 : blockSum term 3651833 1207 22706363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3653040 : blockSum term 3653040 1206 21214245 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3654246 : blockSum term 3654246 1207 24139454 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3655453 : blockSum term 3655453 1206 26765577 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3656659 : blockSum term 3656659 1207 24978642 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3657866 : blockSum term 3657866 1206 22021229 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3659072 : blockSum term 3659072 1207 22002927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3660279 : blockSum term 3660279 1206 21691127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3661485 : blockSum term 3661485 1207 23137287 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3662692 : blockSum term 3662692 1206 25459306 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3663898 : blockSum term 3663898 1207 23390239 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3665105 : blockSum term 3665105 1206 25123010 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3666311 : blockSum term 3666311 1207 21306782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3667518 : blockSum term 3667518 1206 21580264 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3668724 : blockSum term 3668724 1207 26223009 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3669931 : blockSum term 3669931 1206 23288029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3671137 : blockSum term 3671137 1207 23849767 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3672344 : blockSum term 3672344 1206 25282406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3673550 : blockSum term 3673550 1207 21485694 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3674757 : blockSum term 3674757 1206 24078577 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3675963 : blockSum term 3675963 1207 26376993 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3677170 : blockSum term 3677170 1206 25773927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3678376 : blockSum term 3678376 1207 25751753 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3679583 : blockSum term 3679583 1206 21681552 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3680789 : blockSum term 3680789 1207 20795885 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3681996 : blockSum term 3681996 1206 23086161 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3683202 : blockSum term 3683202 1207 21625505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3684409 : blockSum term 3684409 1206 22760037 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3685615 : blockSum term 3685615 1207 23028488 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3686822 : blockSum term 3686822 1206 22434263 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3688028 : blockSum term 3688028 1207 23851217 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3689235 : blockSum term 3689235 1206 21246341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3690441 : blockSum term 3690441 1207 26104992 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3691648 : blockSum term 3691648 1206 22355168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3692854 : blockSum term 3692854 1207 20903558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3694061 : blockSum term 3694061 1206 25176571 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3695267 : blockSum term 3695267 1207 25439515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3696474 : blockSum term 3696474 1206 21705947 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3697680 : blockSum term 3697680 1207 23113655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3698887 : blockSum term 3698887 1206 24804562 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3700093 : blockSum term 3700093 1207 21934809 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3701300 : blockSum term 3701300 1206 23908698 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3702506 : blockSum term 3702506 1207 21613121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3703713 : blockSum term 3703713 1206 23584607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3704919 : blockSum term 3704919 1207 22427832 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3706126 : blockSum term 3706126 1206 18720025 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3707332 : blockSum term 3707332 1207 24371974 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3708539 : blockSum term 3708539 1206 22934995 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3709745 : blockSum term 3709745 1207 18953507 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3710952 : blockSum term 3710952 1206 23743137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3712158 : blockSum term 3712158 1207 24287040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3713365 : blockSum term 3713365 1206 22290313 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3714571 : blockSum term 3714571 1207 21707343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3715778 : blockSum term 3715778 1206 22815542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3716984 : blockSum term 3716984 1207 23639956 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3718191 : blockSum term 3718191 1206 23338270 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3719397 : blockSum term 3719397 1207 23036928 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3720604 : blockSum term 3720604 1206 21895077 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3721810 : blockSum term 3721810 1207 22157563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3723017 : blockSum term 3723017 1206 22697698 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3724223 : blockSum term 3724223 1207 23517954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3725430 : blockSum term 3725430 1206 24616068 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3726636 : blockSum term 3726636 1207 22638991 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3727843 : blockSum term 3727843 1206 23735921 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3729049 : blockSum term 3729049 1207 24552473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3730256 : blockSum term 3730256 1206 22579269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3731462 : blockSum term 3731462 1207 23951744 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3732669 : blockSum term 3732669 1206 20869890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3733875 : blockSum term 3733875 1207 19739750 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3735082 : blockSum term 3735082 1206 25277325 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3736288 : blockSum term 3736288 1207 21369715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3737495 : blockSum term 3737495 1206 22458978 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3738701 : blockSum term 3738701 1207 20499303 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3739908 : blockSum term 3739908 1206 19928585 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3741114 : blockSum term 3741114 1207 23230414 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3742321 : blockSum term 3742321 1206 20998727 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3743527 : blockSum term 3743527 1207 20152719 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3744734 : blockSum term 3744734 1206 21237383 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3745940 : blockSum term 3745940 1207 22322259 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3747147 : blockSum term 3747147 1206 20099874 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3748353 : blockSum term 3748353 1207 24485169 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3749560 : blockSum term 3749560 1206 23363879 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3750766 : blockSum term 3750766 1207 23343000 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3751973 : blockSum term 3751973 1206 21401323 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3753179 : blockSum term 3753179 1207 24397452 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3754386 : blockSum term 3754386 1206 19446017 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3755592 : blockSum term 3755592 1207 23260247 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3756799 : blockSum term 3756799 1206 21326248 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3758005 : blockSum term 3758005 1207 21307687 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3759212 : blockSum term 3759212 1206 20743196 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3760418 : blockSum term 3760418 1207 16362707 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3761625 : blockSum term 3761625 1206 19891293 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3762831 : blockSum term 3762831 1207 21779145 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3764038 : blockSum term 3764038 1206 20128631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3765244 : blockSum term 3765244 1207 22013620 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3766451 : blockSum term 3766451 1206 23079598 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3767657 : blockSum term 3767657 1207 21160473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3768864 : blockSum term 3768864 1206 21684357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3770070 : blockSum term 3770070 1207 19498609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3771277 : blockSum term 3771277 1206 19210581 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3772483 : blockSum term 3772483 1207 22167499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3773690 : blockSum term 3773690 1206 22958026 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3774896 : blockSum term 3774896 1207 21857277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3776103 : blockSum term 3776103 1206 20758992 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3777309 : blockSum term 3777309 1207 22626753 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3778516 : blockSum term 3778516 1206 21798535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3779722 : blockSum term 3779722 1207 21241935 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3780929 : blockSum term 3780929 1206 20416865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3782135 : blockSum term 3782135 1207 20131570 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3783342 : blockSum term 3783342 1206 24134419 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3784548 : blockSum term 3784548 1207 20095083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3785755 : blockSum term 3785755 1206 23825648 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3786961 : blockSum term 3786961 1207 20326977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3788168 : blockSum term 3788168 1206 20041916 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3789374 : blockSum term 3789374 1207 19489847 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3790581 : blockSum term 3790581 1206 21339573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3791787 : blockSum term 3791787 1207 22918803 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3792994 : blockSum term 3792994 1206 18638612 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3794200 : blockSum term 3794200 1207 18090842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3795407 : blockSum term 3795407 1206 22593179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3796613 : blockSum term 3796613 1207 21775906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3797820 : blockSum term 3797820 1206 23082605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3799026 : blockSum term 3799026 1207 21736194 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3800233 : blockSum term 3800233 1206 21186357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3801439 : blockSum term 3801439 1207 19580859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3802646 : blockSum term 3802646 1206 20356685 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3803852 : blockSum term 3803852 1207 25092361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3805059 : blockSum term 3805059 1206 20846664 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3806265 : blockSum term 3806265 1207 18455691 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3807472 : blockSum term 3807472 1206 18966248 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3808678 : blockSum term 3808678 1207 21316129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3809885 : blockSum term 3809885 1206 24453972 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3811091 : blockSum term 3811091 1207 20228479 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3812298 : blockSum term 3812298 1206 20997790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3813504 : blockSum term 3813504 1207 22027217 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3814711 : blockSum term 3814711 1206 23317174 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3815917 : blockSum term 3815917 1207 19369933 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3817124 : blockSum term 3817124 1206 24058703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3818330 : blockSum term 3818330 1207 20640432 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3819537 : blockSum term 3819537 1206 20359948 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3820743 : blockSum term 3820743 1207 22427434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3821950 : blockSum term 3821950 1206 21885191 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3823156 : blockSum term 3823156 1207 20824469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3824363 : blockSum term 3824363 1206 21583973 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3825569 : blockSum term 3825569 1207 17927604 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3826776 : blockSum term 3826776 1206 19209371 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3827982 : blockSum term 3827982 1207 21787058 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3829189 : blockSum term 3829189 1206 23579854 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3830395 : blockSum term 3830395 1207 19674876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3831602 : blockSum term 3831602 1206 19657182 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3832808 : blockSum term 3832808 1207 19123403 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3834015 : blockSum term 3834015 1206 18589566 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3835221 : blockSum term 3835221 1207 21668325 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3836428 : blockSum term 3836428 1206 20874911 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3837634 : blockSum term 3837634 1207 18796216 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3838841 : blockSum term 3838841 1206 21864728 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3840047 : blockSum term 3840047 1207 21072976 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3841254 : blockSum term 3841254 1206 22336822 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3842460 : blockSum term 3842460 1207 20263471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3843667 : blockSum term 3843667 1206 19476227 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3844873 : blockSum term 3844873 1207 20995191 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3846080 : blockSum term 3846080 1206 20976181 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3847286 : blockSum term 3847286 1207 19934962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3848493 : blockSum term 3848493 1206 22214857 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3849699 : blockSum term 3849699 1207 17857304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3850906 : blockSum term 3850906 1206 20390202 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3852112 : blockSum term 3852112 1207 19862820 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3853319 : blockSum term 3853319 1206 20352791 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3854525 : blockSum term 3854525 1207 18554820 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3855732 : blockSum term 3855732 1206 21584660 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3856938 : blockSum term 3856938 1207 20042453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3858145 : blockSum term 3858145 1206 22810323 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3859351 : blockSum term 3859351 1207 18738207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3860558 : blockSum term 3860558 1206 18721213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3861764 : blockSum term 3861764 1207 20979160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3862971 : blockSum term 3862971 1206 18434064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3864177 : blockSum term 3864177 1207 21192966 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3865384 : blockSum term 3865384 1206 16636837 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3866590 : blockSum term 3866590 1207 22162930 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3867797 : blockSum term 3867797 1206 20381824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3869003 : blockSum term 3869003 1207 18100574 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3870210 : blockSum term 3870210 1206 19590438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3871416 : blockSum term 3871416 1207 18067754 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3872623 : blockSum term 3872623 1206 21059413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3873829 : blockSum term 3873829 1207 20037142 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3875036 : blockSum term 3875036 1206 19518347 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3876242 : blockSum term 3876242 1207 18001129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3877449 : blockSum term 3877449 1206 20482963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3878655 : blockSum term 3878655 1207 20462971 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3879862 : blockSum term 3879862 1206 20194967 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3881068 : blockSum term 3881068 1207 19180491 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3882275 : blockSum term 3882275 1206 21401657 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3883481 : blockSum term 3883481 1206 16907319 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3884687 : blockSum term 3884687 1206 20120445 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3885893 : blockSum term 3885893 1207 21838260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3887100 : blockSum term 3887100 1206 19834855 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3888306 : blockSum term 3888306 1207 19568518 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3889513 : blockSum term 3889513 1206 21035036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3890719 : blockSum term 3890719 1207 20520457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3891926 : blockSum term 3891926 1206 19760883 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3893132 : blockSum term 3893132 1207 23937323 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3894339 : blockSum term 3894339 1206 17751601 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3895545 : blockSum term 3895545 1207 20444941 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3896752 : blockSum term 3896752 1206 18457325 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3897958 : blockSum term 3897958 1207 18686640 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3899165 : blockSum term 3899165 1206 19897059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3900371 : blockSum term 3900371 1207 18650503 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3901578 : blockSum term 3901578 1206 17898130 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3902784 : blockSum term 3902784 1207 19105987 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3903991 : blockSum term 3903991 1206 17619998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3905197 : blockSum term 3905197 1207 18092968 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3906404 : blockSum term 3906404 1206 22228591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3907610 : blockSum term 3907610 1207 21475389 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3908817 : blockSum term 3908817 1206 19991665 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3910023 : blockSum term 3910023 1207 21191075 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3911230 : blockSum term 3911230 1206 16547864 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3912436 : blockSum term 3912436 1207 18963708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3913643 : blockSum term 3913643 1206 18216575 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3914849 : blockSum term 3914849 1207 21353521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3916056 : blockSum term 3916056 1206 18666259 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3917262 : blockSum term 3917262 1207 16953094 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3918469 : blockSum term 3918469 1206 21292530 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3919675 : blockSum term 3919675 1207 18613618 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3920882 : blockSum term 3920882 1206 18837571 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3922088 : blockSum term 3922088 1207 19302591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3923295 : blockSum term 3923295 1206 21212300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3924501 : blockSum term 3924501 1207 18542967 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3925708 : blockSum term 3925708 1206 19006495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3926914 : blockSum term 3926914 1207 20670695 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3928121 : blockSum term 3928121 1206 19930119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3929327 : blockSum term 3929327 1207 20391240 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3930534 : blockSum term 3930534 1206 18693937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3931740 : blockSum term 3931740 1207 18675747 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3932947 : blockSum term 3932947 1206 18180471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3934153 : blockSum term 3934153 1207 17445953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3935360 : blockSum term 3935360 1206 17669359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3936566 : blockSum term 3936566 1207 21944721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3937773 : blockSum term 3937773 1206 19063523 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3938979 : blockSum term 3938979 1207 17854669 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3940186 : blockSum term 3940186 1206 21405889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3941392 : blockSum term 3941392 1207 17582569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3942599 : blockSum term 3942599 1206 20177842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3943805 : blockSum term 3943805 1207 19683890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3945012 : blockSum term 3945012 1206 15875647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3946218 : blockSum term 3946218 1207 20832031 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3947425 : blockSum term 3947425 1206 20337035 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3948631 : blockSum term 3948631 1207 19607634 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3949838 : blockSum term 3949838 1206 18172085 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3951044 : blockSum term 3951044 1207 19806258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3952251 : blockSum term 3952251 1206 14840940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3953457 : blockSum term 3953457 1207 18357790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3954664 : blockSum term 3954664 1206 19986596 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3955870 : blockSum term 3955870 1207 17852949 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3957077 : blockSum term 3957077 1206 18774420 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3958283 : blockSum term 3958283 1207 17817858 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3959490 : blockSum term 3959490 1206 17098043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3960696 : blockSum term 3960696 1207 18017889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3961903 : blockSum term 3961903 1206 17532908 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3963109 : blockSum term 3963109 1207 17982803 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3964316 : blockSum term 3964316 1206 18665603 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3965522 : blockSum term 3965522 1207 16082906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3966729 : blockSum term 3966729 1206 18629639 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3967935 : blockSum term 3967935 1207 17913003 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3969142 : blockSum term 3969142 1206 20684285 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3970348 : blockSum term 3970348 1207 18110066 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3971555 : blockSum term 3971555 1206 17165622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3972761 : blockSum term 3972761 1207 19698312 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3973968 : blockSum term 3973968 1206 19910038 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3975174 : blockSum term 3975174 1207 17809636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3976381 : blockSum term 3976381 1206 20796788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3977587 : blockSum term 3977587 1207 18466939 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3978794 : blockSum term 3978794 1206 16604634 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3980000 : blockSum term 3980000 1207 18432823 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3981207 : blockSum term 3981207 1206 19335471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3982413 : blockSum term 3982413 1207 15407466 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3983620 : blockSum term 3983620 1206 17001468 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3984826 : blockSum term 3984826 1207 15608130 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3986033 : blockSum term 3986033 1206 20408671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3987239 : blockSum term 3987239 1207 16493574 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3988446 : blockSum term 3988446 1206 17393492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3989652 : blockSum term 3989652 1207 16690821 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3990859 : blockSum term 3990859 1206 17588075 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3992065 : blockSum term 3992065 1207 21905577 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3993272 : blockSum term 3993272 1206 15500208 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3994478 : blockSum term 3994478 1207 18673951 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3995685 : blockSum term 3995685 1206 15926334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3996891 : blockSum term 3996891 1207 16138000 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3998098 : blockSum term 3998098 1206 17712035 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block3999304 : blockSum term 3999304 1207 17921083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4000511 : blockSum term 4000511 1206 20850046 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4001717 : blockSum term 4001717 1207 18338740 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4002924 : blockSum term 4002924 1206 16511743 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4004130 : blockSum term 4004130 1207 16496759 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4005337 : blockSum term 4005337 1206 18285199 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4006543 : blockSum term 4006543 1207 20071131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4007750 : blockSum term 4007750 1206 18248462 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4008956 : blockSum term 4008956 1207 16656103 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4010163 : blockSum term 4010163 1206 19338260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4011369 : blockSum term 4011369 1207 17970954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4012576 : blockSum term 4012576 1206 15260178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4013782 : blockSum term 4013782 1207 19281183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4014989 : blockSum term 4014989 1206 19261357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4016195 : blockSum term 4016195 1207 15662478 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4017402 : blockSum term 4017402 1206 18554459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4018608 : blockSum term 4018608 1207 17642777 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4019815 : blockSum term 4019815 1206 15617962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4021021 : blockSum term 4021021 1207 20060192 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4022228 : blockSum term 4022228 1206 18703447 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4023434 : blockSum term 4023434 1207 16905686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4024641 : blockSum term 4024641 1206 17333665 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4025847 : blockSum term 4025847 1207 18648667 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4027054 : blockSum term 4027054 1206 17076709 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4028260 : blockSum term 4028260 1207 17722699 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4029467 : blockSum term 4029467 1206 18369205 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4030673 : blockSum term 4030673 1207 17908724 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4031880 : blockSum term 4031880 1206 17669904 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4033086 : blockSum term 4033086 1207 17432554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4034293 : blockSum term 4034293 1206 18296626 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4035499 : blockSum term 4035499 1207 19160393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4036706 : blockSum term 4036706 1206 17160716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4037912 : blockSum term 4037912 1207 21098935 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4039119 : blockSum term 4039119 1206 15369472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4040325 : blockSum term 4040325 1207 18864431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4041532 : blockSum term 4041532 1206 17968574 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4042738 : blockSum term 4042738 1207 17511638 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4043945 : blockSum term 4043945 1206 18586628 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4045151 : blockSum term 4045151 1207 17693286 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4046358 : blockSum term 4046358 1206 18112221 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4047564 : blockSum term 4047564 1207 18093097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4048771 : blockSum term 4048771 1206 16333632 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4049977 : blockSum term 4049977 1207 17840093 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4051184 : blockSum term 4051184 1206 15214009 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4052390 : blockSum term 4052390 1207 18021277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4053597 : blockSum term 4053597 1206 15834634 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4054803 : blockSum term 4054803 1207 16684637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4056010 : blockSum term 4056010 1206 15585859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4057216 : blockSum term 4057216 1207 19895224 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4058423 : blockSum term 4058423 1206 17282068 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4059629 : blockSum term 4059629 1207 15106879 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4060836 : blockSum term 4060836 1206 17678468 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4062042 : blockSum term 4062042 1207 17013811 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4063249 : blockSum term 4063249 1206 16781698 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4064455 : blockSum term 4064455 1207 16549856 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4065662 : blockSum term 4065662 1206 15675080 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4066868 : blockSum term 4066868 1207 18233971 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4068075 : blockSum term 4068075 1206 17785983 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4069281 : blockSum term 4069281 1207 15413446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4070488 : blockSum term 4070488 1206 17536520 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4071694 : blockSum term 4071694 1207 16022972 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4072901 : blockSum term 4072901 1206 19849113 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4074107 : blockSum term 4074107 1207 17056668 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4075314 : blockSum term 4075314 1206 16400257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4076520 : blockSum term 4076520 1207 17448554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4077727 : blockSum term 4077727 1206 18492796 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4078933 : blockSum term 4078933 1207 16137710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4080140 : blockSum term 4080140 1206 16546125 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4081346 : blockSum term 4081346 1207 15257741 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4082553 : blockSum term 4082553 1206 15876557 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4083759 : blockSum term 4083759 1207 16283500 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4084966 : blockSum term 4084966 1206 18801712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4086172 : blockSum term 4086172 1207 17093612 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4087379 : blockSum term 4087379 1206 17707860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4088585 : blockSum term 4088585 1207 15584460 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4089792 : blockSum term 4089792 1206 17671381 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4090998 : blockSum term 4090998 1207 15971683 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4092205 : blockSum term 4092205 1206 17215212 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4093411 : blockSum term 4093411 1207 17406359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4094618 : blockSum term 4094618 1206 16968674 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4095824 : blockSum term 4095824 1207 15904852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4097031 : blockSum term 4097031 1206 16098147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4098237 : blockSum term 4098237 1207 18169790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4099444 : blockSum term 4099444 1206 14812785 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4100650 : blockSum term 4100650 1207 15007375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4101857 : blockSum term 4101857 1206 16033090 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4103063 : blockSum term 4103063 1207 15809834 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4104270 : blockSum term 4104270 1206 17248179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4105476 : blockSum term 4105476 1207 18889705 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4106683 : blockSum term 4106683 1206 16588822 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4107889 : blockSum term 4107889 1207 15536119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4109096 : blockSum term 4109096 1206 18210520 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4110302 : blockSum term 4110302 1207 16123849 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4111509 : blockSum term 4111509 1206 16313523 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4112715 : blockSum term 4112715 1207 14646379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4113922 : blockSum term 4113922 1206 15250207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4115128 : blockSum term 4115128 1207 17291740 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4116335 : blockSum term 4116335 1206 16039457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4117541 : blockSum term 4117541 1207 13148366 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4118748 : blockSum term 4118748 1206 16008573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4119954 : blockSum term 4119954 1207 16811440 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4121161 : blockSum term 4121161 1206 15770101 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4122367 : blockSum term 4122367 1207 14116807 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4123574 : blockSum term 4123574 1206 17576978 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4124780 : blockSum term 4124780 1207 15925859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4125987 : blockSum term 4125987 1206 16520921 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4127193 : blockSum term 4127193 1207 16095775 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4128400 : blockSum term 4128400 1206 15875964 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4129606 : blockSum term 4129606 1207 15452295 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4130813 : blockSum term 4130813 1206 14420040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4132019 : blockSum term 4132019 1207 15419686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4133226 : blockSum term 4133226 1206 13985434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4134432 : blockSum term 4134432 1207 16198438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4135639 : blockSum term 4135639 1206 15776342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4136845 : blockSum term 4136845 1207 15356406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4138052 : blockSum term 4138052 1206 15945511 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4139258 : blockSum term 4139258 1207 15727448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4140465 : blockSum term 4140465 1206 16918257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4141671 : blockSum term 4141671 1207 15291386 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4142878 : blockSum term 4142878 1206 18289246 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4144084 : blockSum term 4144084 1207 14455217 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4145291 : blockSum term 4145291 1206 15242043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4146497 : blockSum term 4146497 1207 14423975 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4147704 : blockSum term 4147704 1206 17410834 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4148910 : blockSum term 4148910 1207 17392083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4150117 : blockSum term 4150117 1206 16574765 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4151323 : blockSum term 4151323 1207 15160320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4152530 : blockSum term 4152530 1206 15343835 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4153736 : blockSum term 4153736 1207 15327349 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4154943 : blockSum term 4154943 1206 17498172 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4156149 : blockSum term 4156149 1207 15691198 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4157356 : blockSum term 4157356 1206 16269263 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4158562 : blockSum term 4158562 1207 15458304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4159769 : blockSum term 4159769 1206 15442358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4160975 : blockSum term 4160975 1207 17798753 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4162182 : blockSum term 4162182 1206 17383551 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4163388 : blockSum term 4163388 1207 15785721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4164595 : blockSum term 4164595 1206 16163411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4165801 : blockSum term 4165801 1207 15162653 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4167008 : blockSum term 4167008 1206 15342699 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4168214 : blockSum term 4168214 1207 13754520 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4169421 : blockSum term 4169421 1206 15898782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4170627 : blockSum term 4170627 1207 15097293 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4171834 : blockSum term 4171834 1206 14689666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4173040 : blockSum term 4173040 1207 15065670 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4174247 : blockSum term 4174247 1206 15245196 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4175453 : blockSum term 4175453 1207 15618868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4176660 : blockSum term 4176660 1206 13846991 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4177866 : blockSum term 4177866 1207 17533410 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4179073 : blockSum term 4179073 1206 14984706 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4180279 : blockSum term 4180279 1207 15356785 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4181486 : blockSum term 4181486 1206 16699022 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4182692 : blockSum term 4182692 1207 14934826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4183899 : blockSum term 4183899 1206 15887282 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4185105 : blockSum term 4185105 1207 17224339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4186312 : blockSum term 4186312 1206 14885274 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4187518 : blockSum term 4187518 1207 15834520 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4188725 : blockSum term 4188725 1206 15817258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4189931 : blockSum term 4189931 1207 15992607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4191138 : blockSum term 4191138 1206 15781783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4192344 : blockSum term 4192344 1206 14996123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4193550 : blockSum term 4193550 1206 13635244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4194756 : blockSum term 4194756 1207 15731423 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4195963 : blockSum term 4195963 1206 15523533 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4197169 : blockSum term 4197169 1207 13592273 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4198376 : blockSum term 4198376 1206 13769617 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4199582 : blockSum term 4199582 1207 16810613 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4200789 : blockSum term 4200789 1206 15074471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4201995 : blockSum term 4201995 1207 15819820 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4203202 : blockSum term 4203202 1206 14088798 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4204408 : blockSum term 4204408 1207 15595576 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4205615 : blockSum term 4205615 1206 17857141 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4206821 : blockSum term 4206821 1207 13472427 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4208028 : blockSum term 4208028 1206 15353518 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4209234 : blockSum term 4209234 1207 14957789 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4210441 : blockSum term 4210441 1206 14752316 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4211647 : blockSum term 4211647 1207 16057973 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4212854 : blockSum term 4212854 1206 13209641 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4214060 : blockSum term 4214060 1207 15080816 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4215267 : blockSum term 4215267 1206 14122263 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4216473 : blockSum term 4216473 1207 14106373 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4217680 : blockSum term 4217680 1206 15782739 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4218886 : blockSum term 4218886 1207 13512877 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4220093 : blockSum term 4220093 1206 15747329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4221299 : blockSum term 4221299 1207 15355979 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4222506 : blockSum term 4222506 1206 15899554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4223712 : blockSum term 4223712 1207 15321579 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4224919 : blockSum term 4224919 1206 13999265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4226125 : blockSum term 4226125 1207 14543413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4227332 : blockSum term 4227332 1206 14154193 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4228538 : blockSum term 4228538 1207 14510800 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4229745 : blockSum term 4229745 1206 13195156 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4230951 : blockSum term 4230951 1207 15037730 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4232158 : blockSum term 4232158 1206 13907480 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4233364 : blockSum term 4233364 1207 17596270 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4234571 : blockSum term 4234571 1206 12950596 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4235777 : blockSum term 4235777 1207 11828613 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4236984 : blockSum term 4236984 1206 15323052 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4238190 : blockSum term 4238190 1207 12170827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4239397 : blockSum term 4239397 1206 15104698 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4240603 : blockSum term 4240603 1207 16006364 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4241810 : blockSum term 4241810 1206 15068274 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4243016 : blockSum term 4243016 1207 14867870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4244223 : blockSum term 4244223 1206 13934859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4245429 : blockSum term 4245429 1207 13004292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4246636 : blockSum term 4246636 1206 14635204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4247842 : blockSum term 4247842 1207 14070205 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4249049 : blockSum term 4249049 1206 16426652 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4250255 : blockSum term 4250255 1207 14584630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4251462 : blockSum term 4251462 1206 14204134 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4252668 : blockSum term 4252668 1207 17098109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4253875 : blockSum term 4253875 1206 13262551 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4255081 : blockSum term 4255081 1207 13792024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4256288 : blockSum term 4256288 1206 13595507 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4257494 : blockSum term 4257494 1207 14303917 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4258701 : blockSum term 4258701 1206 14648534 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4259907 : blockSum term 4259907 1207 14090607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4261114 : blockSum term 4261114 1206 14796498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4262320 : blockSum term 4262320 1207 13338136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4263527 : blockSum term 4263527 1206 14764712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4264733 : blockSum term 4264733 1207 15107749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4265940 : blockSum term 4265940 1206 12575220 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4267146 : blockSum term 4267146 1207 13637660 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4268353 : blockSum term 4268353 1206 12368308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4269559 : blockSum term 4269559 1207 14682177 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4270766 : blockSum term 4270766 1206 15559265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4271972 : blockSum term 4271972 1207 14111198 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4273179 : blockSum term 4273179 1206 13916155 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4274385 : blockSum term 4274385 1207 14969595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4275592 : blockSum term 4275592 1206 11570012 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4276798 : blockSum term 4276798 1207 13335225 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4278005 : blockSum term 4278005 1206 14385056 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4279211 : blockSum term 4279211 1207 15609314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4280418 : blockSum term 4280418 1206 12932820 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4281624 : blockSum term 4281624 1207 14688133 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4282831 : blockSum term 4282831 1206 12196412 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4284037 : blockSum term 4284037 1207 12711673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4285244 : blockSum term 4285244 1206 14108095 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4286450 : blockSum term 4286450 1207 14091161 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4287657 : blockSum term 4287657 1206 12316321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4288863 : blockSum term 4288863 1207 13883356 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4290070 : blockSum term 4290070 1206 13691225 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4291276 : blockSum term 4291276 1207 13849895 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4292483 : blockSum term 4292483 1206 14359992 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4293689 : blockSum term 4293689 1207 12768827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4294896 : blockSum term 4294896 1206 13803264 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4296102 : blockSum term 4296102 1207 12914633 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4297309 : blockSum term 4297309 1206 13945280 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4298515 : blockSum term 4298515 1207 13755468 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4299722 : blockSum term 4299722 1206 14608939 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4300928 : blockSum term 4300928 1207 13376279 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4302135 : blockSum term 4302135 1206 15441629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4303341 : blockSum term 4303341 1207 14730154 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4304548 : blockSum term 4304548 1206 12288680 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4305754 : blockSum term 4305754 1207 12101870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4306961 : blockSum term 4306961 1206 14679291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4308167 : blockSum term 4308167 1207 13970922 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4309374 : blockSum term 4309374 1206 12404191 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4310580 : blockSum term 4310580 1207 13938420 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4311787 : blockSum term 4311787 1206 14609590 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4312993 : blockSum term 4312993 1207 14077609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4314200 : blockSum term 4314200 1206 11660177 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4315406 : blockSum term 4315406 1207 13531515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4316613 : blockSum term 4316613 1206 14541483 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4317819 : blockSum term 4317819 1207 14523833 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4319026 : blockSum term 4319026 1206 13141179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4320232 : blockSum term 4320232 1207 13126187 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4321439 : blockSum term 4321439 1206 11238011 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4322645 : blockSum term 4322645 1207 13095654 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4323852 : blockSum term 4323852 1206 11721319 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4325058 : blockSum term 4325058 1207 15439450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4326265 : blockSum term 4326265 1206 14911647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4327471 : blockSum term 4327471 1207 12694466 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4328678 : blockSum term 4328678 1206 14032835 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4329884 : blockSum term 4329884 1207 12495397 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4331091 : blockSum term 4331091 1206 13659638 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4332297 : blockSum term 4332297 1207 13138439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4333504 : blockSum term 4333504 1206 12112607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4334710 : blockSum term 4334710 1207 12434550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4335917 : blockSum term 4335917 1206 15104426 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4337123 : blockSum term 4337123 1207 13075171 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4338330 : blockSum term 4338330 1206 13729011 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4339536 : blockSum term 4339536 1207 13377646 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4340743 : blockSum term 4340743 1206 13027337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4341949 : blockSum term 4341949 1207 12343788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4343156 : blockSum term 4343156 1206 13328398 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4344362 : blockSum term 4344362 1207 12646515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4345569 : blockSum term 4345569 1206 11634667 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4346775 : blockSum term 4346775 1207 13447476 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4347982 : blockSum term 4347982 1206 13597195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4349188 : blockSum term 4349188 1207 12256008 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4350395 : blockSum term 4350395 1206 13068659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4351601 : blockSum term 4351601 1207 11730647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4352808 : blockSum term 4352808 1206 15015904 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4354014 : blockSum term 4354014 1207 11372436 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4355221 : blockSum term 4355221 1206 13334368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4356427 : blockSum term 4356427 1207 12660357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4357634 : blockSum term 4357634 1206 12316454 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4358840 : blockSum term 4358840 1207 12465735 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4360047 : blockSum term 4360047 1206 12450429 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4361253 : blockSum term 4361253 1207 12599809 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4362460 : blockSum term 4362460 1206 15198818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4363666 : blockSum term 4363666 1207 11099217 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4364873 : blockSum term 4364873 1206 12228521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4366079 : blockSum term 4366079 1207 13678595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4367286 : blockSum term 4367286 1206 12847862 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4368492 : blockSum term 4368492 1207 12995131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4369699 : blockSum term 4369699 1206 11680852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4370905 : blockSum term 4370905 1207 13287071 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4372112 : blockSum term 4372112 1206 16182806 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4373318 : blockSum term 4373318 1207 13090979 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4374525 : blockSum term 4374525 1206 12105570 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4375731 : blockSum term 4375731 1207 11607025 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4376938 : blockSum term 4376938 1206 12398284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4378144 : blockSum term 4378144 1207 11418320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4379351 : blockSum term 4379351 1206 14777258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4380557 : blockSum term 4380557 1207 11710029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4381764 : blockSum term 4381764 1206 14579904 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4382970 : blockSum term 4382970 1207 12481131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4384177 : blockSum term 4384177 1206 12785430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4385383 : blockSum term 4385383 1207 11013728 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4386590 : blockSum term 4386590 1206 13391306 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4387796 : blockSum term 4387796 1207 10667297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4389003 : blockSum term 4389003 1206 13674898 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4390209 : blockSum term 4390209 1207 12069532 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4391416 : blockSum term 4391416 1206 13798254 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4392622 : blockSum term 4392622 1207 10929171 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4393829 : blockSum term 4393829 1206 11548629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4395035 : blockSum term 4395035 1207 12481859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4396242 : blockSum term 4396242 1206 12625086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4397448 : blockSum term 4397448 1207 11191101 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4398655 : blockSum term 4398655 1206 12279299 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4399861 : blockSum term 4399861 1207 12106305 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4401068 : blockSum term 4401068 1206 12718322 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4402274 : blockSum term 4402274 1207 12859712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4403481 : blockSum term 4403481 1206 11746838 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4404687 : blockSum term 4404687 1207 13296807 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4405894 : blockSum term 4405894 1206 11248533 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4407100 : blockSum term 4407100 1207 11078852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4408307 : blockSum term 4408307 1206 12000472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4409513 : blockSum term 4409513 1207 12763314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4410720 : blockSum term 4410720 1206 12746473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4411926 : blockSum term 4411926 1207 12574684 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4413133 : blockSum term 4413133 1206 14419764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4414339 : blockSum term 4414339 1207 11148698 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4415546 : blockSum term 4415546 1206 12216808 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4416752 : blockSum term 4416752 1207 11892584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4417959 : blockSum term 4417959 1206 13265626 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4419165 : blockSum term 4419165 1207 12015998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4420372 : blockSum term 4420372 1206 12154021 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4421578 : blockSum term 4421578 1207 13521051 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4422785 : blockSum term 4422785 1206 12735963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4423991 : blockSum term 4423991 1207 12106298 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4425198 : blockSum term 4425198 1206 13314743 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4426404 : blockSum term 4426404 1207 11615379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4427611 : blockSum term 4427611 1206 12822039 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4428817 : blockSum term 4428817 1207 13565834 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4430024 : blockSum term 4430024 1206 11264568 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4431230 : blockSum term 4431230 1207 11554831 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4432437 : blockSum term 4432437 1206 12298615 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4433643 : blockSum term 4433643 1207 10767590 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4434850 : blockSum term 4434850 1206 12117820 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4436056 : blockSum term 4436056 1207 11951034 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4437263 : blockSum term 4437263 1206 13748452 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4438469 : blockSum term 4438469 1207 11919124 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4439676 : blockSum term 4439676 1206 12958565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4440882 : blockSum term 4440882 1207 12940792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4442089 : blockSum term 4442089 1206 12172166 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4443295 : blockSum term 4443295 1207 11706174 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4444502 : blockSum term 4444502 1206 12290163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4445708 : blockSum term 4445708 1207 11825307 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4446915 : blockSum term 4446915 1206 11958848 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4448121 : blockSum term 4448121 1207 10301467 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4449328 : blockSum term 4449328 1206 13271152 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4450534 : blockSum term 4450534 1207 12210745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4451741 : blockSum term 4451741 1206 11004907 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4452947 : blockSum term 4452947 1207 12476521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4454154 : blockSum term 4454154 1206 11569563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4455360 : blockSum term 4455360 1207 11257606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4456567 : blockSum term 4456567 1206 12425690 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4457773 : blockSum term 4457773 1207 11522100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4458980 : blockSum term 4458980 1206 11654609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4460186 : blockSum term 4460186 1207 11344766 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4461393 : blockSum term 4461393 1206 12212582 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4462599 : blockSum term 4462599 1207 11461238 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4463806 : blockSum term 4463806 1206 10858282 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4465012 : blockSum term 4465012 1207 11430710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4466219 : blockSum term 4466219 1206 12293659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4467425 : blockSum term 4467425 1207 11692883 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4468632 : blockSum term 4468632 1206 11969267 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4469838 : blockSum term 4469838 1207 11515598 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4471045 : blockSum term 4471045 1206 10190409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4472251 : blockSum term 4472251 1207 11485491 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4473458 : blockSum term 4473458 1206 11325081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4474664 : blockSum term 4474664 1207 11600269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4475871 : blockSum term 4475871 1206 12453028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4477077 : blockSum term 4477077 1207 11568099 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4478284 : blockSum term 4478284 1206 11119284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4479490 : blockSum term 4479490 1207 11103362 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4480697 : blockSum term 4480697 1206 11809074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4481903 : blockSum term 4481903 1207 10786467 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4483110 : blockSum term 4483110 1206 11634002 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4484316 : blockSum term 4484316 1207 12477885 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4485523 : blockSum term 4485523 1206 13033244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4486729 : blockSum term 4486729 1207 11298563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4487936 : blockSum term 4487936 1206 11996722 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4489142 : blockSum term 4489142 1207 10696316 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4490349 : blockSum term 4490349 1206 10396982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4491555 : blockSum term 4491555 1207 12374104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4492762 : blockSum term 4492762 1206 9658119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4493968 : blockSum term 4493968 1207 12056690 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4495175 : blockSum term 4495175 1206 10906488 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4496381 : blockSum term 4496381 1207 10467755 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4497588 : blockSum term 4497588 1206 10736431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 6000 in
private theorem block4498794 : blockSum term 4498794 1207 10862863 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem after_cut : blockSum term 3264549 1235452 20629663754 := (join_sums term (lo:=3264549) (a:=617726) (b:=617726) (join_sums term (lo:=3264549) (a:=308863) (b:=308863) (join_sums term (lo:=3264549) (a:=154431) (b:=154432) (join_sums term (lo:=3264549) (a:=77215) (b:=77216) (join_sums term (lo:=3264549) (a:=38607) (b:=38608) (join_sums term (lo:=3264549) (a:=19303) (b:=19304) (join_sums term (lo:=3264549) (a:=9651) (b:=9652) (join_sums term (lo:=3264549) (a:=4825) (b:=4826) (join_sums term (lo:=3264549) (a:=2412) (b:=2413) (join_sums term (lo:=3264549) (a:=1206) (b:=1206) block3264549 block3265755) (join_sums term (lo:=3266961) (a:=1206) (b:=1207) block3266961 block3268167)) (join_sums term (lo:=3269374) (a:=2413) (b:=2413) (join_sums term (lo:=3269374) (a:=1206) (b:=1207) block3269374 block3270580) (join_sums term (lo:=3271787) (a:=1206) (b:=1207) block3271787 block3272993))) (join_sums term (lo:=3274200) (a:=4826) (b:=4826) (join_sums term (lo:=3274200) (a:=2413) (b:=2413) (join_sums term (lo:=3274200) (a:=1206) (b:=1207) block3274200 block3275406) (join_sums term (lo:=3276613) (a:=1206) (b:=1207) block3276613 block3277819)) (join_sums term (lo:=3279026) (a:=2413) (b:=2413) (join_sums term (lo:=3279026) (a:=1206) (b:=1207) block3279026 block3280232) (join_sums term (lo:=3281439) (a:=1206) (b:=1207) block3281439 block3282645)))) (join_sums term (lo:=3283852) (a:=9652) (b:=9652) (join_sums term (lo:=3283852) (a:=4826) (b:=4826) (join_sums term (lo:=3283852) (a:=2413) (b:=2413) (join_sums term (lo:=3283852) (a:=1206) (b:=1207) block3283852 block3285058) (join_sums term (lo:=3286265) (a:=1206) (b:=1207) block3286265 block3287471)) (join_sums term (lo:=3288678) (a:=2413) (b:=2413) (join_sums term (lo:=3288678) (a:=1206) (b:=1207) block3288678 block3289884) (join_sums term (lo:=3291091) (a:=1206) (b:=1207) block3291091 block3292297))) (join_sums term (lo:=3293504) (a:=4826) (b:=4826) (join_sums term (lo:=3293504) (a:=2413) (b:=2413) (join_sums term (lo:=3293504) (a:=1206) (b:=1207) block3293504 block3294710) (join_sums term (lo:=3295917) (a:=1206) (b:=1207) block3295917 block3297123)) (join_sums term (lo:=3298330) (a:=2413) (b:=2413) (join_sums term (lo:=3298330) (a:=1206) (b:=1207) block3298330 block3299536) (join_sums term (lo:=3300743) (a:=1206) (b:=1207) block3300743 block3301949))))) (join_sums term (lo:=3303156) (a:=19304) (b:=19304) (join_sums term (lo:=3303156) (a:=9652) (b:=9652) (join_sums term (lo:=3303156) (a:=4826) (b:=4826) (join_sums term (lo:=3303156) (a:=2413) (b:=2413) (join_sums term (lo:=3303156) (a:=1206) (b:=1207) block3303156 block3304362) (join_sums term (lo:=3305569) (a:=1206) (b:=1207) block3305569 block3306775)) (join_sums term (lo:=3307982) (a:=2413) (b:=2413) (join_sums term (lo:=3307982) (a:=1206) (b:=1207) block3307982 block3309188) (join_sums term (lo:=3310395) (a:=1206) (b:=1207) block3310395 block3311601))) (join_sums term (lo:=3312808) (a:=4826) (b:=4826) (join_sums term (lo:=3312808) (a:=2413) (b:=2413) (join_sums term (lo:=3312808) (a:=1206) (b:=1207) block3312808 block3314014) (join_sums term (lo:=3315221) (a:=1206) (b:=1207) block3315221 block3316427)) (join_sums term (lo:=3317634) (a:=2413) (b:=2413) (join_sums term (lo:=3317634) (a:=1206) (b:=1207) block3317634 block3318840) (join_sums term (lo:=3320047) (a:=1206) (b:=1207) block3320047 block3321253)))) (join_sums term (lo:=3322460) (a:=9652) (b:=9652) (join_sums term (lo:=3322460) (a:=4826) (b:=4826) (join_sums term (lo:=3322460) (a:=2413) (b:=2413) (join_sums term (lo:=3322460) (a:=1206) (b:=1207) block3322460 block3323666) (join_sums term (lo:=3324873) (a:=1206) (b:=1207) block3324873 block3326079)) (join_sums term (lo:=3327286) (a:=2413) (b:=2413) (join_sums term (lo:=3327286) (a:=1206) (b:=1207) block3327286 block3328492) (join_sums term (lo:=3329699) (a:=1206) (b:=1207) block3329699 block3330905))) (join_sums term (lo:=3332112) (a:=4826) (b:=4826) (join_sums term (lo:=3332112) (a:=2413) (b:=2413) (join_sums term (lo:=3332112) (a:=1206) (b:=1207) block3332112 block3333318) (join_sums term (lo:=3334525) (a:=1206) (b:=1207) block3334525 block3335731)) (join_sums term (lo:=3336938) (a:=2413) (b:=2413) (join_sums term (lo:=3336938) (a:=1206) (b:=1207) block3336938 block3338144) (join_sums term (lo:=3339351) (a:=1206) (b:=1207) block3339351 block3340557)))))) (join_sums term (lo:=3341764) (a:=38608) (b:=38608) (join_sums term (lo:=3341764) (a:=19304) (b:=19304) (join_sums term (lo:=3341764) (a:=9652) (b:=9652) (join_sums term (lo:=3341764) (a:=4826) (b:=4826) (join_sums term (lo:=3341764) (a:=2413) (b:=2413) (join_sums term (lo:=3341764) (a:=1206) (b:=1207) block3341764 block3342970) (join_sums term (lo:=3344177) (a:=1206) (b:=1207) block3344177 block3345383)) (join_sums term (lo:=3346590) (a:=2413) (b:=2413) (join_sums term (lo:=3346590) (a:=1206) (b:=1207) block3346590 block3347796) (join_sums term (lo:=3349003) (a:=1206) (b:=1207) block3349003 block3350209))) (join_sums term (lo:=3351416) (a:=4826) (b:=4826) (join_sums term (lo:=3351416) (a:=2413) (b:=2413) (join_sums term (lo:=3351416) (a:=1206) (b:=1207) block3351416 block3352622) (join_sums term (lo:=3353829) (a:=1206) (b:=1207) block3353829 block3355035)) (join_sums term (lo:=3356242) (a:=2413) (b:=2413) (join_sums term (lo:=3356242) (a:=1206) (b:=1207) block3356242 block3357448) (join_sums term (lo:=3358655) (a:=1206) (b:=1207) block3358655 block3359861)))) (join_sums term (lo:=3361068) (a:=9652) (b:=9652) (join_sums term (lo:=3361068) (a:=4826) (b:=4826) (join_sums term (lo:=3361068) (a:=2413) (b:=2413) (join_sums term (lo:=3361068) (a:=1206) (b:=1207) block3361068 block3362274) (join_sums term (lo:=3363481) (a:=1206) (b:=1207) block3363481 block3364687)) (join_sums term (lo:=3365894) (a:=2413) (b:=2413) (join_sums term (lo:=3365894) (a:=1206) (b:=1207) block3365894 block3367100) (join_sums term (lo:=3368307) (a:=1206) (b:=1207) block3368307 block3369513))) (join_sums term (lo:=3370720) (a:=4826) (b:=4826) (join_sums term (lo:=3370720) (a:=2413) (b:=2413) (join_sums term (lo:=3370720) (a:=1206) (b:=1207) block3370720 block3371926) (join_sums term (lo:=3373133) (a:=1206) (b:=1207) block3373133 block3374339)) (join_sums term (lo:=3375546) (a:=2413) (b:=2413) (join_sums term (lo:=3375546) (a:=1206) (b:=1207) block3375546 block3376752) (join_sums term (lo:=3377959) (a:=1206) (b:=1207) block3377959 block3379165))))) (join_sums term (lo:=3380372) (a:=19304) (b:=19304) (join_sums term (lo:=3380372) (a:=9652) (b:=9652) (join_sums term (lo:=3380372) (a:=4826) (b:=4826) (join_sums term (lo:=3380372) (a:=2413) (b:=2413) (join_sums term (lo:=3380372) (a:=1206) (b:=1207) block3380372 block3381578) (join_sums term (lo:=3382785) (a:=1206) (b:=1207) block3382785 block3383991)) (join_sums term (lo:=3385198) (a:=2413) (b:=2413) (join_sums term (lo:=3385198) (a:=1206) (b:=1207) block3385198 block3386404) (join_sums term (lo:=3387611) (a:=1206) (b:=1207) block3387611 block3388817))) (join_sums term (lo:=3390024) (a:=4826) (b:=4826) (join_sums term (lo:=3390024) (a:=2413) (b:=2413) (join_sums term (lo:=3390024) (a:=1206) (b:=1207) block3390024 block3391230) (join_sums term (lo:=3392437) (a:=1206) (b:=1207) block3392437 block3393643)) (join_sums term (lo:=3394850) (a:=2413) (b:=2413) (join_sums term (lo:=3394850) (a:=1206) (b:=1207) block3394850 block3396056) (join_sums term (lo:=3397263) (a:=1206) (b:=1207) block3397263 block3398469)))) (join_sums term (lo:=3399676) (a:=9652) (b:=9652) (join_sums term (lo:=3399676) (a:=4826) (b:=4826) (join_sums term (lo:=3399676) (a:=2413) (b:=2413) (join_sums term (lo:=3399676) (a:=1206) (b:=1207) block3399676 block3400882) (join_sums term (lo:=3402089) (a:=1206) (b:=1207) block3402089 block3403295)) (join_sums term (lo:=3404502) (a:=2413) (b:=2413) (join_sums term (lo:=3404502) (a:=1206) (b:=1207) block3404502 block3405708) (join_sums term (lo:=3406915) (a:=1206) (b:=1207) block3406915 block3408121))) (join_sums term (lo:=3409328) (a:=4826) (b:=4826) (join_sums term (lo:=3409328) (a:=2413) (b:=2413) (join_sums term (lo:=3409328) (a:=1206) (b:=1207) block3409328 block3410534) (join_sums term (lo:=3411741) (a:=1206) (b:=1207) block3411741 block3412947)) (join_sums term (lo:=3414154) (a:=2413) (b:=2413) (join_sums term (lo:=3414154) (a:=1206) (b:=1207) block3414154 block3415360) (join_sums term (lo:=3416567) (a:=1206) (b:=1207) block3416567 block3417773))))))) (join_sums term (lo:=3418980) (a:=77216) (b:=77216) (join_sums term (lo:=3418980) (a:=38608) (b:=38608) (join_sums term (lo:=3418980) (a:=19304) (b:=19304) (join_sums term (lo:=3418980) (a:=9652) (b:=9652) (join_sums term (lo:=3418980) (a:=4826) (b:=4826) (join_sums term (lo:=3418980) (a:=2413) (b:=2413) (join_sums term (lo:=3418980) (a:=1206) (b:=1207) block3418980 block3420186) (join_sums term (lo:=3421393) (a:=1206) (b:=1207) block3421393 block3422599)) (join_sums term (lo:=3423806) (a:=2413) (b:=2413) (join_sums term (lo:=3423806) (a:=1206) (b:=1207) block3423806 block3425012) (join_sums term (lo:=3426219) (a:=1206) (b:=1207) block3426219 block3427425))) (join_sums term (lo:=3428632) (a:=4826) (b:=4826) (join_sums term (lo:=3428632) (a:=2413) (b:=2413) (join_sums term (lo:=3428632) (a:=1206) (b:=1207) block3428632 block3429838) (join_sums term (lo:=3431045) (a:=1206) (b:=1207) block3431045 block3432251)) (join_sums term (lo:=3433458) (a:=2413) (b:=2413) (join_sums term (lo:=3433458) (a:=1206) (b:=1207) block3433458 block3434664) (join_sums term (lo:=3435871) (a:=1206) (b:=1207) block3435871 block3437077)))) (join_sums term (lo:=3438284) (a:=9652) (b:=9652) (join_sums term (lo:=3438284) (a:=4826) (b:=4826) (join_sums term (lo:=3438284) (a:=2413) (b:=2413) (join_sums term (lo:=3438284) (a:=1206) (b:=1207) block3438284 block3439490) (join_sums term (lo:=3440697) (a:=1206) (b:=1207) block3440697 block3441903)) (join_sums term (lo:=3443110) (a:=2413) (b:=2413) (join_sums term (lo:=3443110) (a:=1206) (b:=1207) block3443110 block3444316) (join_sums term (lo:=3445523) (a:=1206) (b:=1207) block3445523 block3446729))) (join_sums term (lo:=3447936) (a:=4826) (b:=4826) (join_sums term (lo:=3447936) (a:=2413) (b:=2413) (join_sums term (lo:=3447936) (a:=1206) (b:=1207) block3447936 block3449142) (join_sums term (lo:=3450349) (a:=1206) (b:=1207) block3450349 block3451555)) (join_sums term (lo:=3452762) (a:=2413) (b:=2413) (join_sums term (lo:=3452762) (a:=1206) (b:=1207) block3452762 block3453968) (join_sums term (lo:=3455175) (a:=1206) (b:=1207) block3455175 block3456381))))) (join_sums term (lo:=3457588) (a:=19304) (b:=19304) (join_sums term (lo:=3457588) (a:=9652) (b:=9652) (join_sums term (lo:=3457588) (a:=4826) (b:=4826) (join_sums term (lo:=3457588) (a:=2413) (b:=2413) (join_sums term (lo:=3457588) (a:=1206) (b:=1207) block3457588 block3458794) (join_sums term (lo:=3460001) (a:=1206) (b:=1207) block3460001 block3461207)) (join_sums term (lo:=3462414) (a:=2413) (b:=2413) (join_sums term (lo:=3462414) (a:=1206) (b:=1207) block3462414 block3463620) (join_sums term (lo:=3464827) (a:=1206) (b:=1207) block3464827 block3466033))) (join_sums term (lo:=3467240) (a:=4826) (b:=4826) (join_sums term (lo:=3467240) (a:=2413) (b:=2413) (join_sums term (lo:=3467240) (a:=1206) (b:=1207) block3467240 block3468446) (join_sums term (lo:=3469653) (a:=1206) (b:=1207) block3469653 block3470859)) (join_sums term (lo:=3472066) (a:=2413) (b:=2413) (join_sums term (lo:=3472066) (a:=1206) (b:=1207) block3472066 block3473272) (join_sums term (lo:=3474479) (a:=1206) (b:=1207) block3474479 block3475685)))) (join_sums term (lo:=3476892) (a:=9652) (b:=9652) (join_sums term (lo:=3476892) (a:=4826) (b:=4826) (join_sums term (lo:=3476892) (a:=2413) (b:=2413) (join_sums term (lo:=3476892) (a:=1206) (b:=1207) block3476892 block3478098) (join_sums term (lo:=3479305) (a:=1206) (b:=1207) block3479305 block3480511)) (join_sums term (lo:=3481718) (a:=2413) (b:=2413) (join_sums term (lo:=3481718) (a:=1206) (b:=1207) block3481718 block3482924) (join_sums term (lo:=3484131) (a:=1206) (b:=1207) block3484131 block3485337))) (join_sums term (lo:=3486544) (a:=4826) (b:=4826) (join_sums term (lo:=3486544) (a:=2413) (b:=2413) (join_sums term (lo:=3486544) (a:=1206) (b:=1207) block3486544 block3487750) (join_sums term (lo:=3488957) (a:=1206) (b:=1207) block3488957 block3490163)) (join_sums term (lo:=3491370) (a:=2413) (b:=2413) (join_sums term (lo:=3491370) (a:=1206) (b:=1207) block3491370 block3492576) (join_sums term (lo:=3493783) (a:=1206) (b:=1207) block3493783 block3494989)))))) (join_sums term (lo:=3496196) (a:=38608) (b:=38608) (join_sums term (lo:=3496196) (a:=19304) (b:=19304) (join_sums term (lo:=3496196) (a:=9652) (b:=9652) (join_sums term (lo:=3496196) (a:=4826) (b:=4826) (join_sums term (lo:=3496196) (a:=2413) (b:=2413) (join_sums term (lo:=3496196) (a:=1206) (b:=1207) block3496196 block3497402) (join_sums term (lo:=3498609) (a:=1206) (b:=1207) block3498609 block3499815)) (join_sums term (lo:=3501022) (a:=2413) (b:=2413) (join_sums term (lo:=3501022) (a:=1206) (b:=1207) block3501022 block3502228) (join_sums term (lo:=3503435) (a:=1206) (b:=1207) block3503435 block3504641))) (join_sums term (lo:=3505848) (a:=4826) (b:=4826) (join_sums term (lo:=3505848) (a:=2413) (b:=2413) (join_sums term (lo:=3505848) (a:=1206) (b:=1207) block3505848 block3507054) (join_sums term (lo:=3508261) (a:=1206) (b:=1207) block3508261 block3509467)) (join_sums term (lo:=3510674) (a:=2413) (b:=2413) (join_sums term (lo:=3510674) (a:=1206) (b:=1207) block3510674 block3511880) (join_sums term (lo:=3513087) (a:=1206) (b:=1207) block3513087 block3514293)))) (join_sums term (lo:=3515500) (a:=9652) (b:=9652) (join_sums term (lo:=3515500) (a:=4826) (b:=4826) (join_sums term (lo:=3515500) (a:=2413) (b:=2413) (join_sums term (lo:=3515500) (a:=1206) (b:=1207) block3515500 block3516706) (join_sums term (lo:=3517913) (a:=1206) (b:=1207) block3517913 block3519119)) (join_sums term (lo:=3520326) (a:=2413) (b:=2413) (join_sums term (lo:=3520326) (a:=1206) (b:=1207) block3520326 block3521532) (join_sums term (lo:=3522739) (a:=1206) (b:=1207) block3522739 block3523945))) (join_sums term (lo:=3525152) (a:=4826) (b:=4826) (join_sums term (lo:=3525152) (a:=2413) (b:=2413) (join_sums term (lo:=3525152) (a:=1206) (b:=1207) block3525152 block3526358) (join_sums term (lo:=3527565) (a:=1206) (b:=1207) block3527565 block3528771)) (join_sums term (lo:=3529978) (a:=2413) (b:=2413) (join_sums term (lo:=3529978) (a:=1206) (b:=1207) block3529978 block3531184) (join_sums term (lo:=3532391) (a:=1206) (b:=1207) block3532391 block3533597))))) (join_sums term (lo:=3534804) (a:=19304) (b:=19304) (join_sums term (lo:=3534804) (a:=9652) (b:=9652) (join_sums term (lo:=3534804) (a:=4826) (b:=4826) (join_sums term (lo:=3534804) (a:=2413) (b:=2413) (join_sums term (lo:=3534804) (a:=1206) (b:=1207) block3534804 block3536010) (join_sums term (lo:=3537217) (a:=1206) (b:=1207) block3537217 block3538423)) (join_sums term (lo:=3539630) (a:=2413) (b:=2413) (join_sums term (lo:=3539630) (a:=1206) (b:=1207) block3539630 block3540836) (join_sums term (lo:=3542043) (a:=1206) (b:=1207) block3542043 block3543249))) (join_sums term (lo:=3544456) (a:=4826) (b:=4826) (join_sums term (lo:=3544456) (a:=2413) (b:=2413) (join_sums term (lo:=3544456) (a:=1206) (b:=1207) block3544456 block3545662) (join_sums term (lo:=3546869) (a:=1206) (b:=1207) block3546869 block3548075)) (join_sums term (lo:=3549282) (a:=2413) (b:=2413) (join_sums term (lo:=3549282) (a:=1206) (b:=1207) block3549282 block3550488) (join_sums term (lo:=3551695) (a:=1206) (b:=1207) block3551695 block3552901)))) (join_sums term (lo:=3554108) (a:=9652) (b:=9652) (join_sums term (lo:=3554108) (a:=4826) (b:=4826) (join_sums term (lo:=3554108) (a:=2413) (b:=2413) (join_sums term (lo:=3554108) (a:=1206) (b:=1207) block3554108 block3555314) (join_sums term (lo:=3556521) (a:=1206) (b:=1207) block3556521 block3557727)) (join_sums term (lo:=3558934) (a:=2413) (b:=2413) (join_sums term (lo:=3558934) (a:=1206) (b:=1207) block3558934 block3560140) (join_sums term (lo:=3561347) (a:=1206) (b:=1207) block3561347 block3562553))) (join_sums term (lo:=3563760) (a:=4826) (b:=4826) (join_sums term (lo:=3563760) (a:=2413) (b:=2413) (join_sums term (lo:=3563760) (a:=1206) (b:=1207) block3563760 block3564966) (join_sums term (lo:=3566173) (a:=1206) (b:=1207) block3566173 block3567379)) (join_sums term (lo:=3568586) (a:=2413) (b:=2413) (join_sums term (lo:=3568586) (a:=1206) (b:=1207) block3568586 block3569792) (join_sums term (lo:=3570999) (a:=1206) (b:=1207) block3570999 block3572205)))))))) (join_sums term (lo:=3573412) (a:=154431) (b:=154432) (join_sums term (lo:=3573412) (a:=77215) (b:=77216) (join_sums term (lo:=3573412) (a:=38607) (b:=38608) (join_sums term (lo:=3573412) (a:=19303) (b:=19304) (join_sums term (lo:=3573412) (a:=9651) (b:=9652) (join_sums term (lo:=3573412) (a:=4825) (b:=4826) (join_sums term (lo:=3573412) (a:=2412) (b:=2413) (join_sums term (lo:=3573412) (a:=1206) (b:=1206) block3573412 block3574618) (join_sums term (lo:=3575824) (a:=1206) (b:=1207) block3575824 block3577030)) (join_sums term (lo:=3578237) (a:=2413) (b:=2413) (join_sums term (lo:=3578237) (a:=1206) (b:=1207) block3578237 block3579443) (join_sums term (lo:=3580650) (a:=1206) (b:=1207) block3580650 block3581856))) (join_sums term (lo:=3583063) (a:=4826) (b:=4826) (join_sums term (lo:=3583063) (a:=2413) (b:=2413) (join_sums term (lo:=3583063) (a:=1206) (b:=1207) block3583063 block3584269) (join_sums term (lo:=3585476) (a:=1206) (b:=1207) block3585476 block3586682)) (join_sums term (lo:=3587889) (a:=2413) (b:=2413) (join_sums term (lo:=3587889) (a:=1206) (b:=1207) block3587889 block3589095) (join_sums term (lo:=3590302) (a:=1206) (b:=1207) block3590302 block3591508)))) (join_sums term (lo:=3592715) (a:=9652) (b:=9652) (join_sums term (lo:=3592715) (a:=4826) (b:=4826) (join_sums term (lo:=3592715) (a:=2413) (b:=2413) (join_sums term (lo:=3592715) (a:=1206) (b:=1207) block3592715 block3593921) (join_sums term (lo:=3595128) (a:=1206) (b:=1207) block3595128 block3596334)) (join_sums term (lo:=3597541) (a:=2413) (b:=2413) (join_sums term (lo:=3597541) (a:=1206) (b:=1207) block3597541 block3598747) (join_sums term (lo:=3599954) (a:=1206) (b:=1207) block3599954 block3601160))) (join_sums term (lo:=3602367) (a:=4826) (b:=4826) (join_sums term (lo:=3602367) (a:=2413) (b:=2413) (join_sums term (lo:=3602367) (a:=1206) (b:=1207) block3602367 block3603573) (join_sums term (lo:=3604780) (a:=1206) (b:=1207) block3604780 block3605986)) (join_sums term (lo:=3607193) (a:=2413) (b:=2413) (join_sums term (lo:=3607193) (a:=1206) (b:=1207) block3607193 block3608399) (join_sums term (lo:=3609606) (a:=1206) (b:=1207) block3609606 block3610812))))) (join_sums term (lo:=3612019) (a:=19304) (b:=19304) (join_sums term (lo:=3612019) (a:=9652) (b:=9652) (join_sums term (lo:=3612019) (a:=4826) (b:=4826) (join_sums term (lo:=3612019) (a:=2413) (b:=2413) (join_sums term (lo:=3612019) (a:=1206) (b:=1207) block3612019 block3613225) (join_sums term (lo:=3614432) (a:=1206) (b:=1207) block3614432 block3615638)) (join_sums term (lo:=3616845) (a:=2413) (b:=2413) (join_sums term (lo:=3616845) (a:=1206) (b:=1207) block3616845 block3618051) (join_sums term (lo:=3619258) (a:=1206) (b:=1207) block3619258 block3620464))) (join_sums term (lo:=3621671) (a:=4826) (b:=4826) (join_sums term (lo:=3621671) (a:=2413) (b:=2413) (join_sums term (lo:=3621671) (a:=1206) (b:=1207) block3621671 block3622877) (join_sums term (lo:=3624084) (a:=1206) (b:=1207) block3624084 block3625290)) (join_sums term (lo:=3626497) (a:=2413) (b:=2413) (join_sums term (lo:=3626497) (a:=1206) (b:=1207) block3626497 block3627703) (join_sums term (lo:=3628910) (a:=1206) (b:=1207) block3628910 block3630116)))) (join_sums term (lo:=3631323) (a:=9652) (b:=9652) (join_sums term (lo:=3631323) (a:=4826) (b:=4826) (join_sums term (lo:=3631323) (a:=2413) (b:=2413) (join_sums term (lo:=3631323) (a:=1206) (b:=1207) block3631323 block3632529) (join_sums term (lo:=3633736) (a:=1206) (b:=1207) block3633736 block3634942)) (join_sums term (lo:=3636149) (a:=2413) (b:=2413) (join_sums term (lo:=3636149) (a:=1206) (b:=1207) block3636149 block3637355) (join_sums term (lo:=3638562) (a:=1206) (b:=1207) block3638562 block3639768))) (join_sums term (lo:=3640975) (a:=4826) (b:=4826) (join_sums term (lo:=3640975) (a:=2413) (b:=2413) (join_sums term (lo:=3640975) (a:=1206) (b:=1207) block3640975 block3642181) (join_sums term (lo:=3643388) (a:=1206) (b:=1207) block3643388 block3644594)) (join_sums term (lo:=3645801) (a:=2413) (b:=2413) (join_sums term (lo:=3645801) (a:=1206) (b:=1207) block3645801 block3647007) (join_sums term (lo:=3648214) (a:=1206) (b:=1207) block3648214 block3649420)))))) (join_sums term (lo:=3650627) (a:=38608) (b:=38608) (join_sums term (lo:=3650627) (a:=19304) (b:=19304) (join_sums term (lo:=3650627) (a:=9652) (b:=9652) (join_sums term (lo:=3650627) (a:=4826) (b:=4826) (join_sums term (lo:=3650627) (a:=2413) (b:=2413) (join_sums term (lo:=3650627) (a:=1206) (b:=1207) block3650627 block3651833) (join_sums term (lo:=3653040) (a:=1206) (b:=1207) block3653040 block3654246)) (join_sums term (lo:=3655453) (a:=2413) (b:=2413) (join_sums term (lo:=3655453) (a:=1206) (b:=1207) block3655453 block3656659) (join_sums term (lo:=3657866) (a:=1206) (b:=1207) block3657866 block3659072))) (join_sums term (lo:=3660279) (a:=4826) (b:=4826) (join_sums term (lo:=3660279) (a:=2413) (b:=2413) (join_sums term (lo:=3660279) (a:=1206) (b:=1207) block3660279 block3661485) (join_sums term (lo:=3662692) (a:=1206) (b:=1207) block3662692 block3663898)) (join_sums term (lo:=3665105) (a:=2413) (b:=2413) (join_sums term (lo:=3665105) (a:=1206) (b:=1207) block3665105 block3666311) (join_sums term (lo:=3667518) (a:=1206) (b:=1207) block3667518 block3668724)))) (join_sums term (lo:=3669931) (a:=9652) (b:=9652) (join_sums term (lo:=3669931) (a:=4826) (b:=4826) (join_sums term (lo:=3669931) (a:=2413) (b:=2413) (join_sums term (lo:=3669931) (a:=1206) (b:=1207) block3669931 block3671137) (join_sums term (lo:=3672344) (a:=1206) (b:=1207) block3672344 block3673550)) (join_sums term (lo:=3674757) (a:=2413) (b:=2413) (join_sums term (lo:=3674757) (a:=1206) (b:=1207) block3674757 block3675963) (join_sums term (lo:=3677170) (a:=1206) (b:=1207) block3677170 block3678376))) (join_sums term (lo:=3679583) (a:=4826) (b:=4826) (join_sums term (lo:=3679583) (a:=2413) (b:=2413) (join_sums term (lo:=3679583) (a:=1206) (b:=1207) block3679583 block3680789) (join_sums term (lo:=3681996) (a:=1206) (b:=1207) block3681996 block3683202)) (join_sums term (lo:=3684409) (a:=2413) (b:=2413) (join_sums term (lo:=3684409) (a:=1206) (b:=1207) block3684409 block3685615) (join_sums term (lo:=3686822) (a:=1206) (b:=1207) block3686822 block3688028))))) (join_sums term (lo:=3689235) (a:=19304) (b:=19304) (join_sums term (lo:=3689235) (a:=9652) (b:=9652) (join_sums term (lo:=3689235) (a:=4826) (b:=4826) (join_sums term (lo:=3689235) (a:=2413) (b:=2413) (join_sums term (lo:=3689235) (a:=1206) (b:=1207) block3689235 block3690441) (join_sums term (lo:=3691648) (a:=1206) (b:=1207) block3691648 block3692854)) (join_sums term (lo:=3694061) (a:=2413) (b:=2413) (join_sums term (lo:=3694061) (a:=1206) (b:=1207) block3694061 block3695267) (join_sums term (lo:=3696474) (a:=1206) (b:=1207) block3696474 block3697680))) (join_sums term (lo:=3698887) (a:=4826) (b:=4826) (join_sums term (lo:=3698887) (a:=2413) (b:=2413) (join_sums term (lo:=3698887) (a:=1206) (b:=1207) block3698887 block3700093) (join_sums term (lo:=3701300) (a:=1206) (b:=1207) block3701300 block3702506)) (join_sums term (lo:=3703713) (a:=2413) (b:=2413) (join_sums term (lo:=3703713) (a:=1206) (b:=1207) block3703713 block3704919) (join_sums term (lo:=3706126) (a:=1206) (b:=1207) block3706126 block3707332)))) (join_sums term (lo:=3708539) (a:=9652) (b:=9652) (join_sums term (lo:=3708539) (a:=4826) (b:=4826) (join_sums term (lo:=3708539) (a:=2413) (b:=2413) (join_sums term (lo:=3708539) (a:=1206) (b:=1207) block3708539 block3709745) (join_sums term (lo:=3710952) (a:=1206) (b:=1207) block3710952 block3712158)) (join_sums term (lo:=3713365) (a:=2413) (b:=2413) (join_sums term (lo:=3713365) (a:=1206) (b:=1207) block3713365 block3714571) (join_sums term (lo:=3715778) (a:=1206) (b:=1207) block3715778 block3716984))) (join_sums term (lo:=3718191) (a:=4826) (b:=4826) (join_sums term (lo:=3718191) (a:=2413) (b:=2413) (join_sums term (lo:=3718191) (a:=1206) (b:=1207) block3718191 block3719397) (join_sums term (lo:=3720604) (a:=1206) (b:=1207) block3720604 block3721810)) (join_sums term (lo:=3723017) (a:=2413) (b:=2413) (join_sums term (lo:=3723017) (a:=1206) (b:=1207) block3723017 block3724223) (join_sums term (lo:=3725430) (a:=1206) (b:=1207) block3725430 block3726636))))))) (join_sums term (lo:=3727843) (a:=77216) (b:=77216) (join_sums term (lo:=3727843) (a:=38608) (b:=38608) (join_sums term (lo:=3727843) (a:=19304) (b:=19304) (join_sums term (lo:=3727843) (a:=9652) (b:=9652) (join_sums term (lo:=3727843) (a:=4826) (b:=4826) (join_sums term (lo:=3727843) (a:=2413) (b:=2413) (join_sums term (lo:=3727843) (a:=1206) (b:=1207) block3727843 block3729049) (join_sums term (lo:=3730256) (a:=1206) (b:=1207) block3730256 block3731462)) (join_sums term (lo:=3732669) (a:=2413) (b:=2413) (join_sums term (lo:=3732669) (a:=1206) (b:=1207) block3732669 block3733875) (join_sums term (lo:=3735082) (a:=1206) (b:=1207) block3735082 block3736288))) (join_sums term (lo:=3737495) (a:=4826) (b:=4826) (join_sums term (lo:=3737495) (a:=2413) (b:=2413) (join_sums term (lo:=3737495) (a:=1206) (b:=1207) block3737495 block3738701) (join_sums term (lo:=3739908) (a:=1206) (b:=1207) block3739908 block3741114)) (join_sums term (lo:=3742321) (a:=2413) (b:=2413) (join_sums term (lo:=3742321) (a:=1206) (b:=1207) block3742321 block3743527) (join_sums term (lo:=3744734) (a:=1206) (b:=1207) block3744734 block3745940)))) (join_sums term (lo:=3747147) (a:=9652) (b:=9652) (join_sums term (lo:=3747147) (a:=4826) (b:=4826) (join_sums term (lo:=3747147) (a:=2413) (b:=2413) (join_sums term (lo:=3747147) (a:=1206) (b:=1207) block3747147 block3748353) (join_sums term (lo:=3749560) (a:=1206) (b:=1207) block3749560 block3750766)) (join_sums term (lo:=3751973) (a:=2413) (b:=2413) (join_sums term (lo:=3751973) (a:=1206) (b:=1207) block3751973 block3753179) (join_sums term (lo:=3754386) (a:=1206) (b:=1207) block3754386 block3755592))) (join_sums term (lo:=3756799) (a:=4826) (b:=4826) (join_sums term (lo:=3756799) (a:=2413) (b:=2413) (join_sums term (lo:=3756799) (a:=1206) (b:=1207) block3756799 block3758005) (join_sums term (lo:=3759212) (a:=1206) (b:=1207) block3759212 block3760418)) (join_sums term (lo:=3761625) (a:=2413) (b:=2413) (join_sums term (lo:=3761625) (a:=1206) (b:=1207) block3761625 block3762831) (join_sums term (lo:=3764038) (a:=1206) (b:=1207) block3764038 block3765244))))) (join_sums term (lo:=3766451) (a:=19304) (b:=19304) (join_sums term (lo:=3766451) (a:=9652) (b:=9652) (join_sums term (lo:=3766451) (a:=4826) (b:=4826) (join_sums term (lo:=3766451) (a:=2413) (b:=2413) (join_sums term (lo:=3766451) (a:=1206) (b:=1207) block3766451 block3767657) (join_sums term (lo:=3768864) (a:=1206) (b:=1207) block3768864 block3770070)) (join_sums term (lo:=3771277) (a:=2413) (b:=2413) (join_sums term (lo:=3771277) (a:=1206) (b:=1207) block3771277 block3772483) (join_sums term (lo:=3773690) (a:=1206) (b:=1207) block3773690 block3774896))) (join_sums term (lo:=3776103) (a:=4826) (b:=4826) (join_sums term (lo:=3776103) (a:=2413) (b:=2413) (join_sums term (lo:=3776103) (a:=1206) (b:=1207) block3776103 block3777309) (join_sums term (lo:=3778516) (a:=1206) (b:=1207) block3778516 block3779722)) (join_sums term (lo:=3780929) (a:=2413) (b:=2413) (join_sums term (lo:=3780929) (a:=1206) (b:=1207) block3780929 block3782135) (join_sums term (lo:=3783342) (a:=1206) (b:=1207) block3783342 block3784548)))) (join_sums term (lo:=3785755) (a:=9652) (b:=9652) (join_sums term (lo:=3785755) (a:=4826) (b:=4826) (join_sums term (lo:=3785755) (a:=2413) (b:=2413) (join_sums term (lo:=3785755) (a:=1206) (b:=1207) block3785755 block3786961) (join_sums term (lo:=3788168) (a:=1206) (b:=1207) block3788168 block3789374)) (join_sums term (lo:=3790581) (a:=2413) (b:=2413) (join_sums term (lo:=3790581) (a:=1206) (b:=1207) block3790581 block3791787) (join_sums term (lo:=3792994) (a:=1206) (b:=1207) block3792994 block3794200))) (join_sums term (lo:=3795407) (a:=4826) (b:=4826) (join_sums term (lo:=3795407) (a:=2413) (b:=2413) (join_sums term (lo:=3795407) (a:=1206) (b:=1207) block3795407 block3796613) (join_sums term (lo:=3797820) (a:=1206) (b:=1207) block3797820 block3799026)) (join_sums term (lo:=3800233) (a:=2413) (b:=2413) (join_sums term (lo:=3800233) (a:=1206) (b:=1207) block3800233 block3801439) (join_sums term (lo:=3802646) (a:=1206) (b:=1207) block3802646 block3803852)))))) (join_sums term (lo:=3805059) (a:=38608) (b:=38608) (join_sums term (lo:=3805059) (a:=19304) (b:=19304) (join_sums term (lo:=3805059) (a:=9652) (b:=9652) (join_sums term (lo:=3805059) (a:=4826) (b:=4826) (join_sums term (lo:=3805059) (a:=2413) (b:=2413) (join_sums term (lo:=3805059) (a:=1206) (b:=1207) block3805059 block3806265) (join_sums term (lo:=3807472) (a:=1206) (b:=1207) block3807472 block3808678)) (join_sums term (lo:=3809885) (a:=2413) (b:=2413) (join_sums term (lo:=3809885) (a:=1206) (b:=1207) block3809885 block3811091) (join_sums term (lo:=3812298) (a:=1206) (b:=1207) block3812298 block3813504))) (join_sums term (lo:=3814711) (a:=4826) (b:=4826) (join_sums term (lo:=3814711) (a:=2413) (b:=2413) (join_sums term (lo:=3814711) (a:=1206) (b:=1207) block3814711 block3815917) (join_sums term (lo:=3817124) (a:=1206) (b:=1207) block3817124 block3818330)) (join_sums term (lo:=3819537) (a:=2413) (b:=2413) (join_sums term (lo:=3819537) (a:=1206) (b:=1207) block3819537 block3820743) (join_sums term (lo:=3821950) (a:=1206) (b:=1207) block3821950 block3823156)))) (join_sums term (lo:=3824363) (a:=9652) (b:=9652) (join_sums term (lo:=3824363) (a:=4826) (b:=4826) (join_sums term (lo:=3824363) (a:=2413) (b:=2413) (join_sums term (lo:=3824363) (a:=1206) (b:=1207) block3824363 block3825569) (join_sums term (lo:=3826776) (a:=1206) (b:=1207) block3826776 block3827982)) (join_sums term (lo:=3829189) (a:=2413) (b:=2413) (join_sums term (lo:=3829189) (a:=1206) (b:=1207) block3829189 block3830395) (join_sums term (lo:=3831602) (a:=1206) (b:=1207) block3831602 block3832808))) (join_sums term (lo:=3834015) (a:=4826) (b:=4826) (join_sums term (lo:=3834015) (a:=2413) (b:=2413) (join_sums term (lo:=3834015) (a:=1206) (b:=1207) block3834015 block3835221) (join_sums term (lo:=3836428) (a:=1206) (b:=1207) block3836428 block3837634)) (join_sums term (lo:=3838841) (a:=2413) (b:=2413) (join_sums term (lo:=3838841) (a:=1206) (b:=1207) block3838841 block3840047) (join_sums term (lo:=3841254) (a:=1206) (b:=1207) block3841254 block3842460))))) (join_sums term (lo:=3843667) (a:=19304) (b:=19304) (join_sums term (lo:=3843667) (a:=9652) (b:=9652) (join_sums term (lo:=3843667) (a:=4826) (b:=4826) (join_sums term (lo:=3843667) (a:=2413) (b:=2413) (join_sums term (lo:=3843667) (a:=1206) (b:=1207) block3843667 block3844873) (join_sums term (lo:=3846080) (a:=1206) (b:=1207) block3846080 block3847286)) (join_sums term (lo:=3848493) (a:=2413) (b:=2413) (join_sums term (lo:=3848493) (a:=1206) (b:=1207) block3848493 block3849699) (join_sums term (lo:=3850906) (a:=1206) (b:=1207) block3850906 block3852112))) (join_sums term (lo:=3853319) (a:=4826) (b:=4826) (join_sums term (lo:=3853319) (a:=2413) (b:=2413) (join_sums term (lo:=3853319) (a:=1206) (b:=1207) block3853319 block3854525) (join_sums term (lo:=3855732) (a:=1206) (b:=1207) block3855732 block3856938)) (join_sums term (lo:=3858145) (a:=2413) (b:=2413) (join_sums term (lo:=3858145) (a:=1206) (b:=1207) block3858145 block3859351) (join_sums term (lo:=3860558) (a:=1206) (b:=1207) block3860558 block3861764)))) (join_sums term (lo:=3862971) (a:=9652) (b:=9652) (join_sums term (lo:=3862971) (a:=4826) (b:=4826) (join_sums term (lo:=3862971) (a:=2413) (b:=2413) (join_sums term (lo:=3862971) (a:=1206) (b:=1207) block3862971 block3864177) (join_sums term (lo:=3865384) (a:=1206) (b:=1207) block3865384 block3866590)) (join_sums term (lo:=3867797) (a:=2413) (b:=2413) (join_sums term (lo:=3867797) (a:=1206) (b:=1207) block3867797 block3869003) (join_sums term (lo:=3870210) (a:=1206) (b:=1207) block3870210 block3871416))) (join_sums term (lo:=3872623) (a:=4826) (b:=4826) (join_sums term (lo:=3872623) (a:=2413) (b:=2413) (join_sums term (lo:=3872623) (a:=1206) (b:=1207) block3872623 block3873829) (join_sums term (lo:=3875036) (a:=1206) (b:=1207) block3875036 block3876242)) (join_sums term (lo:=3877449) (a:=2413) (b:=2413) (join_sums term (lo:=3877449) (a:=1206) (b:=1207) block3877449 block3878655) (join_sums term (lo:=3879862) (a:=1206) (b:=1207) block3879862 block3881068))))))))) (join_sums term (lo:=3882275) (a:=308863) (b:=308863) (join_sums term (lo:=3882275) (a:=154431) (b:=154432) (join_sums term (lo:=3882275) (a:=77215) (b:=77216) (join_sums term (lo:=3882275) (a:=38607) (b:=38608) (join_sums term (lo:=3882275) (a:=19303) (b:=19304) (join_sums term (lo:=3882275) (a:=9651) (b:=9652) (join_sums term (lo:=3882275) (a:=4825) (b:=4826) (join_sums term (lo:=3882275) (a:=2412) (b:=2413) (join_sums term (lo:=3882275) (a:=1206) (b:=1206) block3882275 block3883481) (join_sums term (lo:=3884687) (a:=1206) (b:=1207) block3884687 block3885893)) (join_sums term (lo:=3887100) (a:=2413) (b:=2413) (join_sums term (lo:=3887100) (a:=1206) (b:=1207) block3887100 block3888306) (join_sums term (lo:=3889513) (a:=1206) (b:=1207) block3889513 block3890719))) (join_sums term (lo:=3891926) (a:=4826) (b:=4826) (join_sums term (lo:=3891926) (a:=2413) (b:=2413) (join_sums term (lo:=3891926) (a:=1206) (b:=1207) block3891926 block3893132) (join_sums term (lo:=3894339) (a:=1206) (b:=1207) block3894339 block3895545)) (join_sums term (lo:=3896752) (a:=2413) (b:=2413) (join_sums term (lo:=3896752) (a:=1206) (b:=1207) block3896752 block3897958) (join_sums term (lo:=3899165) (a:=1206) (b:=1207) block3899165 block3900371)))) (join_sums term (lo:=3901578) (a:=9652) (b:=9652) (join_sums term (lo:=3901578) (a:=4826) (b:=4826) (join_sums term (lo:=3901578) (a:=2413) (b:=2413) (join_sums term (lo:=3901578) (a:=1206) (b:=1207) block3901578 block3902784) (join_sums term (lo:=3903991) (a:=1206) (b:=1207) block3903991 block3905197)) (join_sums term (lo:=3906404) (a:=2413) (b:=2413) (join_sums term (lo:=3906404) (a:=1206) (b:=1207) block3906404 block3907610) (join_sums term (lo:=3908817) (a:=1206) (b:=1207) block3908817 block3910023))) (join_sums term (lo:=3911230) (a:=4826) (b:=4826) (join_sums term (lo:=3911230) (a:=2413) (b:=2413) (join_sums term (lo:=3911230) (a:=1206) (b:=1207) block3911230 block3912436) (join_sums term (lo:=3913643) (a:=1206) (b:=1207) block3913643 block3914849)) (join_sums term (lo:=3916056) (a:=2413) (b:=2413) (join_sums term (lo:=3916056) (a:=1206) (b:=1207) block3916056 block3917262) (join_sums term (lo:=3918469) (a:=1206) (b:=1207) block3918469 block3919675))))) (join_sums term (lo:=3920882) (a:=19304) (b:=19304) (join_sums term (lo:=3920882) (a:=9652) (b:=9652) (join_sums term (lo:=3920882) (a:=4826) (b:=4826) (join_sums term (lo:=3920882) (a:=2413) (b:=2413) (join_sums term (lo:=3920882) (a:=1206) (b:=1207) block3920882 block3922088) (join_sums term (lo:=3923295) (a:=1206) (b:=1207) block3923295 block3924501)) (join_sums term (lo:=3925708) (a:=2413) (b:=2413) (join_sums term (lo:=3925708) (a:=1206) (b:=1207) block3925708 block3926914) (join_sums term (lo:=3928121) (a:=1206) (b:=1207) block3928121 block3929327))) (join_sums term (lo:=3930534) (a:=4826) (b:=4826) (join_sums term (lo:=3930534) (a:=2413) (b:=2413) (join_sums term (lo:=3930534) (a:=1206) (b:=1207) block3930534 block3931740) (join_sums term (lo:=3932947) (a:=1206) (b:=1207) block3932947 block3934153)) (join_sums term (lo:=3935360) (a:=2413) (b:=2413) (join_sums term (lo:=3935360) (a:=1206) (b:=1207) block3935360 block3936566) (join_sums term (lo:=3937773) (a:=1206) (b:=1207) block3937773 block3938979)))) (join_sums term (lo:=3940186) (a:=9652) (b:=9652) (join_sums term (lo:=3940186) (a:=4826) (b:=4826) (join_sums term (lo:=3940186) (a:=2413) (b:=2413) (join_sums term (lo:=3940186) (a:=1206) (b:=1207) block3940186 block3941392) (join_sums term (lo:=3942599) (a:=1206) (b:=1207) block3942599 block3943805)) (join_sums term (lo:=3945012) (a:=2413) (b:=2413) (join_sums term (lo:=3945012) (a:=1206) (b:=1207) block3945012 block3946218) (join_sums term (lo:=3947425) (a:=1206) (b:=1207) block3947425 block3948631))) (join_sums term (lo:=3949838) (a:=4826) (b:=4826) (join_sums term (lo:=3949838) (a:=2413) (b:=2413) (join_sums term (lo:=3949838) (a:=1206) (b:=1207) block3949838 block3951044) (join_sums term (lo:=3952251) (a:=1206) (b:=1207) block3952251 block3953457)) (join_sums term (lo:=3954664) (a:=2413) (b:=2413) (join_sums term (lo:=3954664) (a:=1206) (b:=1207) block3954664 block3955870) (join_sums term (lo:=3957077) (a:=1206) (b:=1207) block3957077 block3958283)))))) (join_sums term (lo:=3959490) (a:=38608) (b:=38608) (join_sums term (lo:=3959490) (a:=19304) (b:=19304) (join_sums term (lo:=3959490) (a:=9652) (b:=9652) (join_sums term (lo:=3959490) (a:=4826) (b:=4826) (join_sums term (lo:=3959490) (a:=2413) (b:=2413) (join_sums term (lo:=3959490) (a:=1206) (b:=1207) block3959490 block3960696) (join_sums term (lo:=3961903) (a:=1206) (b:=1207) block3961903 block3963109)) (join_sums term (lo:=3964316) (a:=2413) (b:=2413) (join_sums term (lo:=3964316) (a:=1206) (b:=1207) block3964316 block3965522) (join_sums term (lo:=3966729) (a:=1206) (b:=1207) block3966729 block3967935))) (join_sums term (lo:=3969142) (a:=4826) (b:=4826) (join_sums term (lo:=3969142) (a:=2413) (b:=2413) (join_sums term (lo:=3969142) (a:=1206) (b:=1207) block3969142 block3970348) (join_sums term (lo:=3971555) (a:=1206) (b:=1207) block3971555 block3972761)) (join_sums term (lo:=3973968) (a:=2413) (b:=2413) (join_sums term (lo:=3973968) (a:=1206) (b:=1207) block3973968 block3975174) (join_sums term (lo:=3976381) (a:=1206) (b:=1207) block3976381 block3977587)))) (join_sums term (lo:=3978794) (a:=9652) (b:=9652) (join_sums term (lo:=3978794) (a:=4826) (b:=4826) (join_sums term (lo:=3978794) (a:=2413) (b:=2413) (join_sums term (lo:=3978794) (a:=1206) (b:=1207) block3978794 block3980000) (join_sums term (lo:=3981207) (a:=1206) (b:=1207) block3981207 block3982413)) (join_sums term (lo:=3983620) (a:=2413) (b:=2413) (join_sums term (lo:=3983620) (a:=1206) (b:=1207) block3983620 block3984826) (join_sums term (lo:=3986033) (a:=1206) (b:=1207) block3986033 block3987239))) (join_sums term (lo:=3988446) (a:=4826) (b:=4826) (join_sums term (lo:=3988446) (a:=2413) (b:=2413) (join_sums term (lo:=3988446) (a:=1206) (b:=1207) block3988446 block3989652) (join_sums term (lo:=3990859) (a:=1206) (b:=1207) block3990859 block3992065)) (join_sums term (lo:=3993272) (a:=2413) (b:=2413) (join_sums term (lo:=3993272) (a:=1206) (b:=1207) block3993272 block3994478) (join_sums term (lo:=3995685) (a:=1206) (b:=1207) block3995685 block3996891))))) (join_sums term (lo:=3998098) (a:=19304) (b:=19304) (join_sums term (lo:=3998098) (a:=9652) (b:=9652) (join_sums term (lo:=3998098) (a:=4826) (b:=4826) (join_sums term (lo:=3998098) (a:=2413) (b:=2413) (join_sums term (lo:=3998098) (a:=1206) (b:=1207) block3998098 block3999304) (join_sums term (lo:=4000511) (a:=1206) (b:=1207) block4000511 block4001717)) (join_sums term (lo:=4002924) (a:=2413) (b:=2413) (join_sums term (lo:=4002924) (a:=1206) (b:=1207) block4002924 block4004130) (join_sums term (lo:=4005337) (a:=1206) (b:=1207) block4005337 block4006543))) (join_sums term (lo:=4007750) (a:=4826) (b:=4826) (join_sums term (lo:=4007750) (a:=2413) (b:=2413) (join_sums term (lo:=4007750) (a:=1206) (b:=1207) block4007750 block4008956) (join_sums term (lo:=4010163) (a:=1206) (b:=1207) block4010163 block4011369)) (join_sums term (lo:=4012576) (a:=2413) (b:=2413) (join_sums term (lo:=4012576) (a:=1206) (b:=1207) block4012576 block4013782) (join_sums term (lo:=4014989) (a:=1206) (b:=1207) block4014989 block4016195)))) (join_sums term (lo:=4017402) (a:=9652) (b:=9652) (join_sums term (lo:=4017402) (a:=4826) (b:=4826) (join_sums term (lo:=4017402) (a:=2413) (b:=2413) (join_sums term (lo:=4017402) (a:=1206) (b:=1207) block4017402 block4018608) (join_sums term (lo:=4019815) (a:=1206) (b:=1207) block4019815 block4021021)) (join_sums term (lo:=4022228) (a:=2413) (b:=2413) (join_sums term (lo:=4022228) (a:=1206) (b:=1207) block4022228 block4023434) (join_sums term (lo:=4024641) (a:=1206) (b:=1207) block4024641 block4025847))) (join_sums term (lo:=4027054) (a:=4826) (b:=4826) (join_sums term (lo:=4027054) (a:=2413) (b:=2413) (join_sums term (lo:=4027054) (a:=1206) (b:=1207) block4027054 block4028260) (join_sums term (lo:=4029467) (a:=1206) (b:=1207) block4029467 block4030673)) (join_sums term (lo:=4031880) (a:=2413) (b:=2413) (join_sums term (lo:=4031880) (a:=1206) (b:=1207) block4031880 block4033086) (join_sums term (lo:=4034293) (a:=1206) (b:=1207) block4034293 block4035499))))))) (join_sums term (lo:=4036706) (a:=77216) (b:=77216) (join_sums term (lo:=4036706) (a:=38608) (b:=38608) (join_sums term (lo:=4036706) (a:=19304) (b:=19304) (join_sums term (lo:=4036706) (a:=9652) (b:=9652) (join_sums term (lo:=4036706) (a:=4826) (b:=4826) (join_sums term (lo:=4036706) (a:=2413) (b:=2413) (join_sums term (lo:=4036706) (a:=1206) (b:=1207) block4036706 block4037912) (join_sums term (lo:=4039119) (a:=1206) (b:=1207) block4039119 block4040325)) (join_sums term (lo:=4041532) (a:=2413) (b:=2413) (join_sums term (lo:=4041532) (a:=1206) (b:=1207) block4041532 block4042738) (join_sums term (lo:=4043945) (a:=1206) (b:=1207) block4043945 block4045151))) (join_sums term (lo:=4046358) (a:=4826) (b:=4826) (join_sums term (lo:=4046358) (a:=2413) (b:=2413) (join_sums term (lo:=4046358) (a:=1206) (b:=1207) block4046358 block4047564) (join_sums term (lo:=4048771) (a:=1206) (b:=1207) block4048771 block4049977)) (join_sums term (lo:=4051184) (a:=2413) (b:=2413) (join_sums term (lo:=4051184) (a:=1206) (b:=1207) block4051184 block4052390) (join_sums term (lo:=4053597) (a:=1206) (b:=1207) block4053597 block4054803)))) (join_sums term (lo:=4056010) (a:=9652) (b:=9652) (join_sums term (lo:=4056010) (a:=4826) (b:=4826) (join_sums term (lo:=4056010) (a:=2413) (b:=2413) (join_sums term (lo:=4056010) (a:=1206) (b:=1207) block4056010 block4057216) (join_sums term (lo:=4058423) (a:=1206) (b:=1207) block4058423 block4059629)) (join_sums term (lo:=4060836) (a:=2413) (b:=2413) (join_sums term (lo:=4060836) (a:=1206) (b:=1207) block4060836 block4062042) (join_sums term (lo:=4063249) (a:=1206) (b:=1207) block4063249 block4064455))) (join_sums term (lo:=4065662) (a:=4826) (b:=4826) (join_sums term (lo:=4065662) (a:=2413) (b:=2413) (join_sums term (lo:=4065662) (a:=1206) (b:=1207) block4065662 block4066868) (join_sums term (lo:=4068075) (a:=1206) (b:=1207) block4068075 block4069281)) (join_sums term (lo:=4070488) (a:=2413) (b:=2413) (join_sums term (lo:=4070488) (a:=1206) (b:=1207) block4070488 block4071694) (join_sums term (lo:=4072901) (a:=1206) (b:=1207) block4072901 block4074107))))) (join_sums term (lo:=4075314) (a:=19304) (b:=19304) (join_sums term (lo:=4075314) (a:=9652) (b:=9652) (join_sums term (lo:=4075314) (a:=4826) (b:=4826) (join_sums term (lo:=4075314) (a:=2413) (b:=2413) (join_sums term (lo:=4075314) (a:=1206) (b:=1207) block4075314 block4076520) (join_sums term (lo:=4077727) (a:=1206) (b:=1207) block4077727 block4078933)) (join_sums term (lo:=4080140) (a:=2413) (b:=2413) (join_sums term (lo:=4080140) (a:=1206) (b:=1207) block4080140 block4081346) (join_sums term (lo:=4082553) (a:=1206) (b:=1207) block4082553 block4083759))) (join_sums term (lo:=4084966) (a:=4826) (b:=4826) (join_sums term (lo:=4084966) (a:=2413) (b:=2413) (join_sums term (lo:=4084966) (a:=1206) (b:=1207) block4084966 block4086172) (join_sums term (lo:=4087379) (a:=1206) (b:=1207) block4087379 block4088585)) (join_sums term (lo:=4089792) (a:=2413) (b:=2413) (join_sums term (lo:=4089792) (a:=1206) (b:=1207) block4089792 block4090998) (join_sums term (lo:=4092205) (a:=1206) (b:=1207) block4092205 block4093411)))) (join_sums term (lo:=4094618) (a:=9652) (b:=9652) (join_sums term (lo:=4094618) (a:=4826) (b:=4826) (join_sums term (lo:=4094618) (a:=2413) (b:=2413) (join_sums term (lo:=4094618) (a:=1206) (b:=1207) block4094618 block4095824) (join_sums term (lo:=4097031) (a:=1206) (b:=1207) block4097031 block4098237)) (join_sums term (lo:=4099444) (a:=2413) (b:=2413) (join_sums term (lo:=4099444) (a:=1206) (b:=1207) block4099444 block4100650) (join_sums term (lo:=4101857) (a:=1206) (b:=1207) block4101857 block4103063))) (join_sums term (lo:=4104270) (a:=4826) (b:=4826) (join_sums term (lo:=4104270) (a:=2413) (b:=2413) (join_sums term (lo:=4104270) (a:=1206) (b:=1207) block4104270 block4105476) (join_sums term (lo:=4106683) (a:=1206) (b:=1207) block4106683 block4107889)) (join_sums term (lo:=4109096) (a:=2413) (b:=2413) (join_sums term (lo:=4109096) (a:=1206) (b:=1207) block4109096 block4110302) (join_sums term (lo:=4111509) (a:=1206) (b:=1207) block4111509 block4112715)))))) (join_sums term (lo:=4113922) (a:=38608) (b:=38608) (join_sums term (lo:=4113922) (a:=19304) (b:=19304) (join_sums term (lo:=4113922) (a:=9652) (b:=9652) (join_sums term (lo:=4113922) (a:=4826) (b:=4826) (join_sums term (lo:=4113922) (a:=2413) (b:=2413) (join_sums term (lo:=4113922) (a:=1206) (b:=1207) block4113922 block4115128) (join_sums term (lo:=4116335) (a:=1206) (b:=1207) block4116335 block4117541)) (join_sums term (lo:=4118748) (a:=2413) (b:=2413) (join_sums term (lo:=4118748) (a:=1206) (b:=1207) block4118748 block4119954) (join_sums term (lo:=4121161) (a:=1206) (b:=1207) block4121161 block4122367))) (join_sums term (lo:=4123574) (a:=4826) (b:=4826) (join_sums term (lo:=4123574) (a:=2413) (b:=2413) (join_sums term (lo:=4123574) (a:=1206) (b:=1207) block4123574 block4124780) (join_sums term (lo:=4125987) (a:=1206) (b:=1207) block4125987 block4127193)) (join_sums term (lo:=4128400) (a:=2413) (b:=2413) (join_sums term (lo:=4128400) (a:=1206) (b:=1207) block4128400 block4129606) (join_sums term (lo:=4130813) (a:=1206) (b:=1207) block4130813 block4132019)))) (join_sums term (lo:=4133226) (a:=9652) (b:=9652) (join_sums term (lo:=4133226) (a:=4826) (b:=4826) (join_sums term (lo:=4133226) (a:=2413) (b:=2413) (join_sums term (lo:=4133226) (a:=1206) (b:=1207) block4133226 block4134432) (join_sums term (lo:=4135639) (a:=1206) (b:=1207) block4135639 block4136845)) (join_sums term (lo:=4138052) (a:=2413) (b:=2413) (join_sums term (lo:=4138052) (a:=1206) (b:=1207) block4138052 block4139258) (join_sums term (lo:=4140465) (a:=1206) (b:=1207) block4140465 block4141671))) (join_sums term (lo:=4142878) (a:=4826) (b:=4826) (join_sums term (lo:=4142878) (a:=2413) (b:=2413) (join_sums term (lo:=4142878) (a:=1206) (b:=1207) block4142878 block4144084) (join_sums term (lo:=4145291) (a:=1206) (b:=1207) block4145291 block4146497)) (join_sums term (lo:=4147704) (a:=2413) (b:=2413) (join_sums term (lo:=4147704) (a:=1206) (b:=1207) block4147704 block4148910) (join_sums term (lo:=4150117) (a:=1206) (b:=1207) block4150117 block4151323))))) (join_sums term (lo:=4152530) (a:=19304) (b:=19304) (join_sums term (lo:=4152530) (a:=9652) (b:=9652) (join_sums term (lo:=4152530) (a:=4826) (b:=4826) (join_sums term (lo:=4152530) (a:=2413) (b:=2413) (join_sums term (lo:=4152530) (a:=1206) (b:=1207) block4152530 block4153736) (join_sums term (lo:=4154943) (a:=1206) (b:=1207) block4154943 block4156149)) (join_sums term (lo:=4157356) (a:=2413) (b:=2413) (join_sums term (lo:=4157356) (a:=1206) (b:=1207) block4157356 block4158562) (join_sums term (lo:=4159769) (a:=1206) (b:=1207) block4159769 block4160975))) (join_sums term (lo:=4162182) (a:=4826) (b:=4826) (join_sums term (lo:=4162182) (a:=2413) (b:=2413) (join_sums term (lo:=4162182) (a:=1206) (b:=1207) block4162182 block4163388) (join_sums term (lo:=4164595) (a:=1206) (b:=1207) block4164595 block4165801)) (join_sums term (lo:=4167008) (a:=2413) (b:=2413) (join_sums term (lo:=4167008) (a:=1206) (b:=1207) block4167008 block4168214) (join_sums term (lo:=4169421) (a:=1206) (b:=1207) block4169421 block4170627)))) (join_sums term (lo:=4171834) (a:=9652) (b:=9652) (join_sums term (lo:=4171834) (a:=4826) (b:=4826) (join_sums term (lo:=4171834) (a:=2413) (b:=2413) (join_sums term (lo:=4171834) (a:=1206) (b:=1207) block4171834 block4173040) (join_sums term (lo:=4174247) (a:=1206) (b:=1207) block4174247 block4175453)) (join_sums term (lo:=4176660) (a:=2413) (b:=2413) (join_sums term (lo:=4176660) (a:=1206) (b:=1207) block4176660 block4177866) (join_sums term (lo:=4179073) (a:=1206) (b:=1207) block4179073 block4180279))) (join_sums term (lo:=4181486) (a:=4826) (b:=4826) (join_sums term (lo:=4181486) (a:=2413) (b:=2413) (join_sums term (lo:=4181486) (a:=1206) (b:=1207) block4181486 block4182692) (join_sums term (lo:=4183899) (a:=1206) (b:=1207) block4183899 block4185105)) (join_sums term (lo:=4186312) (a:=2413) (b:=2413) (join_sums term (lo:=4186312) (a:=1206) (b:=1207) block4186312 block4187518) (join_sums term (lo:=4188725) (a:=1206) (b:=1207) block4188725 block4189931)))))))) (join_sums term (lo:=4191138) (a:=154431) (b:=154432) (join_sums term (lo:=4191138) (a:=77215) (b:=77216) (join_sums term (lo:=4191138) (a:=38607) (b:=38608) (join_sums term (lo:=4191138) (a:=19303) (b:=19304) (join_sums term (lo:=4191138) (a:=9651) (b:=9652) (join_sums term (lo:=4191138) (a:=4825) (b:=4826) (join_sums term (lo:=4191138) (a:=2412) (b:=2413) (join_sums term (lo:=4191138) (a:=1206) (b:=1206) block4191138 block4192344) (join_sums term (lo:=4193550) (a:=1206) (b:=1207) block4193550 block4194756)) (join_sums term (lo:=4195963) (a:=2413) (b:=2413) (join_sums term (lo:=4195963) (a:=1206) (b:=1207) block4195963 block4197169) (join_sums term (lo:=4198376) (a:=1206) (b:=1207) block4198376 block4199582))) (join_sums term (lo:=4200789) (a:=4826) (b:=4826) (join_sums term (lo:=4200789) (a:=2413) (b:=2413) (join_sums term (lo:=4200789) (a:=1206) (b:=1207) block4200789 block4201995) (join_sums term (lo:=4203202) (a:=1206) (b:=1207) block4203202 block4204408)) (join_sums term (lo:=4205615) (a:=2413) (b:=2413) (join_sums term (lo:=4205615) (a:=1206) (b:=1207) block4205615 block4206821) (join_sums term (lo:=4208028) (a:=1206) (b:=1207) block4208028 block4209234)))) (join_sums term (lo:=4210441) (a:=9652) (b:=9652) (join_sums term (lo:=4210441) (a:=4826) (b:=4826) (join_sums term (lo:=4210441) (a:=2413) (b:=2413) (join_sums term (lo:=4210441) (a:=1206) (b:=1207) block4210441 block4211647) (join_sums term (lo:=4212854) (a:=1206) (b:=1207) block4212854 block4214060)) (join_sums term (lo:=4215267) (a:=2413) (b:=2413) (join_sums term (lo:=4215267) (a:=1206) (b:=1207) block4215267 block4216473) (join_sums term (lo:=4217680) (a:=1206) (b:=1207) block4217680 block4218886))) (join_sums term (lo:=4220093) (a:=4826) (b:=4826) (join_sums term (lo:=4220093) (a:=2413) (b:=2413) (join_sums term (lo:=4220093) (a:=1206) (b:=1207) block4220093 block4221299) (join_sums term (lo:=4222506) (a:=1206) (b:=1207) block4222506 block4223712)) (join_sums term (lo:=4224919) (a:=2413) (b:=2413) (join_sums term (lo:=4224919) (a:=1206) (b:=1207) block4224919 block4226125) (join_sums term (lo:=4227332) (a:=1206) (b:=1207) block4227332 block4228538))))) (join_sums term (lo:=4229745) (a:=19304) (b:=19304) (join_sums term (lo:=4229745) (a:=9652) (b:=9652) (join_sums term (lo:=4229745) (a:=4826) (b:=4826) (join_sums term (lo:=4229745) (a:=2413) (b:=2413) (join_sums term (lo:=4229745) (a:=1206) (b:=1207) block4229745 block4230951) (join_sums term (lo:=4232158) (a:=1206) (b:=1207) block4232158 block4233364)) (join_sums term (lo:=4234571) (a:=2413) (b:=2413) (join_sums term (lo:=4234571) (a:=1206) (b:=1207) block4234571 block4235777) (join_sums term (lo:=4236984) (a:=1206) (b:=1207) block4236984 block4238190))) (join_sums term (lo:=4239397) (a:=4826) (b:=4826) (join_sums term (lo:=4239397) (a:=2413) (b:=2413) (join_sums term (lo:=4239397) (a:=1206) (b:=1207) block4239397 block4240603) (join_sums term (lo:=4241810) (a:=1206) (b:=1207) block4241810 block4243016)) (join_sums term (lo:=4244223) (a:=2413) (b:=2413) (join_sums term (lo:=4244223) (a:=1206) (b:=1207) block4244223 block4245429) (join_sums term (lo:=4246636) (a:=1206) (b:=1207) block4246636 block4247842)))) (join_sums term (lo:=4249049) (a:=9652) (b:=9652) (join_sums term (lo:=4249049) (a:=4826) (b:=4826) (join_sums term (lo:=4249049) (a:=2413) (b:=2413) (join_sums term (lo:=4249049) (a:=1206) (b:=1207) block4249049 block4250255) (join_sums term (lo:=4251462) (a:=1206) (b:=1207) block4251462 block4252668)) (join_sums term (lo:=4253875) (a:=2413) (b:=2413) (join_sums term (lo:=4253875) (a:=1206) (b:=1207) block4253875 block4255081) (join_sums term (lo:=4256288) (a:=1206) (b:=1207) block4256288 block4257494))) (join_sums term (lo:=4258701) (a:=4826) (b:=4826) (join_sums term (lo:=4258701) (a:=2413) (b:=2413) (join_sums term (lo:=4258701) (a:=1206) (b:=1207) block4258701 block4259907) (join_sums term (lo:=4261114) (a:=1206) (b:=1207) block4261114 block4262320)) (join_sums term (lo:=4263527) (a:=2413) (b:=2413) (join_sums term (lo:=4263527) (a:=1206) (b:=1207) block4263527 block4264733) (join_sums term (lo:=4265940) (a:=1206) (b:=1207) block4265940 block4267146)))))) (join_sums term (lo:=4268353) (a:=38608) (b:=38608) (join_sums term (lo:=4268353) (a:=19304) (b:=19304) (join_sums term (lo:=4268353) (a:=9652) (b:=9652) (join_sums term (lo:=4268353) (a:=4826) (b:=4826) (join_sums term (lo:=4268353) (a:=2413) (b:=2413) (join_sums term (lo:=4268353) (a:=1206) (b:=1207) block4268353 block4269559) (join_sums term (lo:=4270766) (a:=1206) (b:=1207) block4270766 block4271972)) (join_sums term (lo:=4273179) (a:=2413) (b:=2413) (join_sums term (lo:=4273179) (a:=1206) (b:=1207) block4273179 block4274385) (join_sums term (lo:=4275592) (a:=1206) (b:=1207) block4275592 block4276798))) (join_sums term (lo:=4278005) (a:=4826) (b:=4826) (join_sums term (lo:=4278005) (a:=2413) (b:=2413) (join_sums term (lo:=4278005) (a:=1206) (b:=1207) block4278005 block4279211) (join_sums term (lo:=4280418) (a:=1206) (b:=1207) block4280418 block4281624)) (join_sums term (lo:=4282831) (a:=2413) (b:=2413) (join_sums term (lo:=4282831) (a:=1206) (b:=1207) block4282831 block4284037) (join_sums term (lo:=4285244) (a:=1206) (b:=1207) block4285244 block4286450)))) (join_sums term (lo:=4287657) (a:=9652) (b:=9652) (join_sums term (lo:=4287657) (a:=4826) (b:=4826) (join_sums term (lo:=4287657) (a:=2413) (b:=2413) (join_sums term (lo:=4287657) (a:=1206) (b:=1207) block4287657 block4288863) (join_sums term (lo:=4290070) (a:=1206) (b:=1207) block4290070 block4291276)) (join_sums term (lo:=4292483) (a:=2413) (b:=2413) (join_sums term (lo:=4292483) (a:=1206) (b:=1207) block4292483 block4293689) (join_sums term (lo:=4294896) (a:=1206) (b:=1207) block4294896 block4296102))) (join_sums term (lo:=4297309) (a:=4826) (b:=4826) (join_sums term (lo:=4297309) (a:=2413) (b:=2413) (join_sums term (lo:=4297309) (a:=1206) (b:=1207) block4297309 block4298515) (join_sums term (lo:=4299722) (a:=1206) (b:=1207) block4299722 block4300928)) (join_sums term (lo:=4302135) (a:=2413) (b:=2413) (join_sums term (lo:=4302135) (a:=1206) (b:=1207) block4302135 block4303341) (join_sums term (lo:=4304548) (a:=1206) (b:=1207) block4304548 block4305754))))) (join_sums term (lo:=4306961) (a:=19304) (b:=19304) (join_sums term (lo:=4306961) (a:=9652) (b:=9652) (join_sums term (lo:=4306961) (a:=4826) (b:=4826) (join_sums term (lo:=4306961) (a:=2413) (b:=2413) (join_sums term (lo:=4306961) (a:=1206) (b:=1207) block4306961 block4308167) (join_sums term (lo:=4309374) (a:=1206) (b:=1207) block4309374 block4310580)) (join_sums term (lo:=4311787) (a:=2413) (b:=2413) (join_sums term (lo:=4311787) (a:=1206) (b:=1207) block4311787 block4312993) (join_sums term (lo:=4314200) (a:=1206) (b:=1207) block4314200 block4315406))) (join_sums term (lo:=4316613) (a:=4826) (b:=4826) (join_sums term (lo:=4316613) (a:=2413) (b:=2413) (join_sums term (lo:=4316613) (a:=1206) (b:=1207) block4316613 block4317819) (join_sums term (lo:=4319026) (a:=1206) (b:=1207) block4319026 block4320232)) (join_sums term (lo:=4321439) (a:=2413) (b:=2413) (join_sums term (lo:=4321439) (a:=1206) (b:=1207) block4321439 block4322645) (join_sums term (lo:=4323852) (a:=1206) (b:=1207) block4323852 block4325058)))) (join_sums term (lo:=4326265) (a:=9652) (b:=9652) (join_sums term (lo:=4326265) (a:=4826) (b:=4826) (join_sums term (lo:=4326265) (a:=2413) (b:=2413) (join_sums term (lo:=4326265) (a:=1206) (b:=1207) block4326265 block4327471) (join_sums term (lo:=4328678) (a:=1206) (b:=1207) block4328678 block4329884)) (join_sums term (lo:=4331091) (a:=2413) (b:=2413) (join_sums term (lo:=4331091) (a:=1206) (b:=1207) block4331091 block4332297) (join_sums term (lo:=4333504) (a:=1206) (b:=1207) block4333504 block4334710))) (join_sums term (lo:=4335917) (a:=4826) (b:=4826) (join_sums term (lo:=4335917) (a:=2413) (b:=2413) (join_sums term (lo:=4335917) (a:=1206) (b:=1207) block4335917 block4337123) (join_sums term (lo:=4338330) (a:=1206) (b:=1207) block4338330 block4339536)) (join_sums term (lo:=4340743) (a:=2413) (b:=2413) (join_sums term (lo:=4340743) (a:=1206) (b:=1207) block4340743 block4341949) (join_sums term (lo:=4343156) (a:=1206) (b:=1207) block4343156 block4344362))))))) (join_sums term (lo:=4345569) (a:=77216) (b:=77216) (join_sums term (lo:=4345569) (a:=38608) (b:=38608) (join_sums term (lo:=4345569) (a:=19304) (b:=19304) (join_sums term (lo:=4345569) (a:=9652) (b:=9652) (join_sums term (lo:=4345569) (a:=4826) (b:=4826) (join_sums term (lo:=4345569) (a:=2413) (b:=2413) (join_sums term (lo:=4345569) (a:=1206) (b:=1207) block4345569 block4346775) (join_sums term (lo:=4347982) (a:=1206) (b:=1207) block4347982 block4349188)) (join_sums term (lo:=4350395) (a:=2413) (b:=2413) (join_sums term (lo:=4350395) (a:=1206) (b:=1207) block4350395 block4351601) (join_sums term (lo:=4352808) (a:=1206) (b:=1207) block4352808 block4354014))) (join_sums term (lo:=4355221) (a:=4826) (b:=4826) (join_sums term (lo:=4355221) (a:=2413) (b:=2413) (join_sums term (lo:=4355221) (a:=1206) (b:=1207) block4355221 block4356427) (join_sums term (lo:=4357634) (a:=1206) (b:=1207) block4357634 block4358840)) (join_sums term (lo:=4360047) (a:=2413) (b:=2413) (join_sums term (lo:=4360047) (a:=1206) (b:=1207) block4360047 block4361253) (join_sums term (lo:=4362460) (a:=1206) (b:=1207) block4362460 block4363666)))) (join_sums term (lo:=4364873) (a:=9652) (b:=9652) (join_sums term (lo:=4364873) (a:=4826) (b:=4826) (join_sums term (lo:=4364873) (a:=2413) (b:=2413) (join_sums term (lo:=4364873) (a:=1206) (b:=1207) block4364873 block4366079) (join_sums term (lo:=4367286) (a:=1206) (b:=1207) block4367286 block4368492)) (join_sums term (lo:=4369699) (a:=2413) (b:=2413) (join_sums term (lo:=4369699) (a:=1206) (b:=1207) block4369699 block4370905) (join_sums term (lo:=4372112) (a:=1206) (b:=1207) block4372112 block4373318))) (join_sums term (lo:=4374525) (a:=4826) (b:=4826) (join_sums term (lo:=4374525) (a:=2413) (b:=2413) (join_sums term (lo:=4374525) (a:=1206) (b:=1207) block4374525 block4375731) (join_sums term (lo:=4376938) (a:=1206) (b:=1207) block4376938 block4378144)) (join_sums term (lo:=4379351) (a:=2413) (b:=2413) (join_sums term (lo:=4379351) (a:=1206) (b:=1207) block4379351 block4380557) (join_sums term (lo:=4381764) (a:=1206) (b:=1207) block4381764 block4382970))))) (join_sums term (lo:=4384177) (a:=19304) (b:=19304) (join_sums term (lo:=4384177) (a:=9652) (b:=9652) (join_sums term (lo:=4384177) (a:=4826) (b:=4826) (join_sums term (lo:=4384177) (a:=2413) (b:=2413) (join_sums term (lo:=4384177) (a:=1206) (b:=1207) block4384177 block4385383) (join_sums term (lo:=4386590) (a:=1206) (b:=1207) block4386590 block4387796)) (join_sums term (lo:=4389003) (a:=2413) (b:=2413) (join_sums term (lo:=4389003) (a:=1206) (b:=1207) block4389003 block4390209) (join_sums term (lo:=4391416) (a:=1206) (b:=1207) block4391416 block4392622))) (join_sums term (lo:=4393829) (a:=4826) (b:=4826) (join_sums term (lo:=4393829) (a:=2413) (b:=2413) (join_sums term (lo:=4393829) (a:=1206) (b:=1207) block4393829 block4395035) (join_sums term (lo:=4396242) (a:=1206) (b:=1207) block4396242 block4397448)) (join_sums term (lo:=4398655) (a:=2413) (b:=2413) (join_sums term (lo:=4398655) (a:=1206) (b:=1207) block4398655 block4399861) (join_sums term (lo:=4401068) (a:=1206) (b:=1207) block4401068 block4402274)))) (join_sums term (lo:=4403481) (a:=9652) (b:=9652) (join_sums term (lo:=4403481) (a:=4826) (b:=4826) (join_sums term (lo:=4403481) (a:=2413) (b:=2413) (join_sums term (lo:=4403481) (a:=1206) (b:=1207) block4403481 block4404687) (join_sums term (lo:=4405894) (a:=1206) (b:=1207) block4405894 block4407100)) (join_sums term (lo:=4408307) (a:=2413) (b:=2413) (join_sums term (lo:=4408307) (a:=1206) (b:=1207) block4408307 block4409513) (join_sums term (lo:=4410720) (a:=1206) (b:=1207) block4410720 block4411926))) (join_sums term (lo:=4413133) (a:=4826) (b:=4826) (join_sums term (lo:=4413133) (a:=2413) (b:=2413) (join_sums term (lo:=4413133) (a:=1206) (b:=1207) block4413133 block4414339) (join_sums term (lo:=4415546) (a:=1206) (b:=1207) block4415546 block4416752)) (join_sums term (lo:=4417959) (a:=2413) (b:=2413) (join_sums term (lo:=4417959) (a:=1206) (b:=1207) block4417959 block4419165) (join_sums term (lo:=4420372) (a:=1206) (b:=1207) block4420372 block4421578)))))) (join_sums term (lo:=4422785) (a:=38608) (b:=38608) (join_sums term (lo:=4422785) (a:=19304) (b:=19304) (join_sums term (lo:=4422785) (a:=9652) (b:=9652) (join_sums term (lo:=4422785) (a:=4826) (b:=4826) (join_sums term (lo:=4422785) (a:=2413) (b:=2413) (join_sums term (lo:=4422785) (a:=1206) (b:=1207) block4422785 block4423991) (join_sums term (lo:=4425198) (a:=1206) (b:=1207) block4425198 block4426404)) (join_sums term (lo:=4427611) (a:=2413) (b:=2413) (join_sums term (lo:=4427611) (a:=1206) (b:=1207) block4427611 block4428817) (join_sums term (lo:=4430024) (a:=1206) (b:=1207) block4430024 block4431230))) (join_sums term (lo:=4432437) (a:=4826) (b:=4826) (join_sums term (lo:=4432437) (a:=2413) (b:=2413) (join_sums term (lo:=4432437) (a:=1206) (b:=1207) block4432437 block4433643) (join_sums term (lo:=4434850) (a:=1206) (b:=1207) block4434850 block4436056)) (join_sums term (lo:=4437263) (a:=2413) (b:=2413) (join_sums term (lo:=4437263) (a:=1206) (b:=1207) block4437263 block4438469) (join_sums term (lo:=4439676) (a:=1206) (b:=1207) block4439676 block4440882)))) (join_sums term (lo:=4442089) (a:=9652) (b:=9652) (join_sums term (lo:=4442089) (a:=4826) (b:=4826) (join_sums term (lo:=4442089) (a:=2413) (b:=2413) (join_sums term (lo:=4442089) (a:=1206) (b:=1207) block4442089 block4443295) (join_sums term (lo:=4444502) (a:=1206) (b:=1207) block4444502 block4445708)) (join_sums term (lo:=4446915) (a:=2413) (b:=2413) (join_sums term (lo:=4446915) (a:=1206) (b:=1207) block4446915 block4448121) (join_sums term (lo:=4449328) (a:=1206) (b:=1207) block4449328 block4450534))) (join_sums term (lo:=4451741) (a:=4826) (b:=4826) (join_sums term (lo:=4451741) (a:=2413) (b:=2413) (join_sums term (lo:=4451741) (a:=1206) (b:=1207) block4451741 block4452947) (join_sums term (lo:=4454154) (a:=1206) (b:=1207) block4454154 block4455360)) (join_sums term (lo:=4456567) (a:=2413) (b:=2413) (join_sums term (lo:=4456567) (a:=1206) (b:=1207) block4456567 block4457773) (join_sums term (lo:=4458980) (a:=1206) (b:=1207) block4458980 block4460186))))) (join_sums term (lo:=4461393) (a:=19304) (b:=19304) (join_sums term (lo:=4461393) (a:=9652) (b:=9652) (join_sums term (lo:=4461393) (a:=4826) (b:=4826) (join_sums term (lo:=4461393) (a:=2413) (b:=2413) (join_sums term (lo:=4461393) (a:=1206) (b:=1207) block4461393 block4462599) (join_sums term (lo:=4463806) (a:=1206) (b:=1207) block4463806 block4465012)) (join_sums term (lo:=4466219) (a:=2413) (b:=2413) (join_sums term (lo:=4466219) (a:=1206) (b:=1207) block4466219 block4467425) (join_sums term (lo:=4468632) (a:=1206) (b:=1207) block4468632 block4469838))) (join_sums term (lo:=4471045) (a:=4826) (b:=4826) (join_sums term (lo:=4471045) (a:=2413) (b:=2413) (join_sums term (lo:=4471045) (a:=1206) (b:=1207) block4471045 block4472251) (join_sums term (lo:=4473458) (a:=1206) (b:=1207) block4473458 block4474664)) (join_sums term (lo:=4475871) (a:=2413) (b:=2413) (join_sums term (lo:=4475871) (a:=1206) (b:=1207) block4475871 block4477077) (join_sums term (lo:=4478284) (a:=1206) (b:=1207) block4478284 block4479490)))) (join_sums term (lo:=4480697) (a:=9652) (b:=9652) (join_sums term (lo:=4480697) (a:=4826) (b:=4826) (join_sums term (lo:=4480697) (a:=2413) (b:=2413) (join_sums term (lo:=4480697) (a:=1206) (b:=1207) block4480697 block4481903) (join_sums term (lo:=4483110) (a:=1206) (b:=1207) block4483110 block4484316)) (join_sums term (lo:=4485523) (a:=2413) (b:=2413) (join_sums term (lo:=4485523) (a:=1206) (b:=1207) block4485523 block4486729) (join_sums term (lo:=4487936) (a:=1206) (b:=1207) block4487936 block4489142))) (join_sums term (lo:=4490349) (a:=4826) (b:=4826) (join_sums term (lo:=4490349) (a:=2413) (b:=2413) (join_sums term (lo:=4490349) (a:=1206) (b:=1207) block4490349 block4491555) (join_sums term (lo:=4492762) (a:=1206) (b:=1207) block4492762 block4493968)) (join_sums term (lo:=4495175) (a:=2413) (b:=2413) (join_sums term (lo:=4495175) (a:=1206) (b:=1207) block4495175 block4496381) (join_sums term (lo:=4497588) (a:=1206) (b:=1207) block4497588 block4498794))))))))))

private theorem rows : blockSum term 0 4500001 20629663754 :=
  join_sums term (lo:=0) (a:=3264549) (b:=1235452) before after_cut

theorem exact_interval_sum :
    (∑ p ∈ (Nat.primesLE 4500000).filter (3264548 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1))) = 20629663754 :=
  right_from_blocks tab prime CheckpointA28006Slim.fast_correct prime_ok (by decide) (by decide) rows

end CorrectionNext30
