import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 2,430,000 through 2,550,000

The sum covers 8,136 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From2430000To2550000

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


private abbrev term := contribution 30110134441897 2430000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 2430001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 2430000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r2430001 : blockSum term 2430001 468 17741692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2430469 : blockSum term 2430469 469 21537607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2430938 : blockSum term 2430938 469 19631851 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2431407 : blockSum term 2431407 469 22159002 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2431876 : blockSum term 2431876 468 17088948 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2432344 : blockSum term 2432344 469 20247971 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2432813 : blockSum term 2432813 469 17079277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2433282 : blockSum term 2433282 469 19604605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2433751 : blockSum term 2433751 468 22127880 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2434219 : blockSum term 2434219 469 21489459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2434688 : blockSum term 2434688 469 20219398 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2435157 : blockSum term 2435157 469 21476776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2435626 : blockSum term 2435626 468 20838346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2436094 : blockSum term 2436094 469 16413691 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2436563 : blockSum term 2436563 469 20826800 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2437032 : blockSum term 2437032 469 17665749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2437501 : blockSum term 2437501 468 18292019 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2437969 : blockSum term 2437969 469 18286684 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2438438 : blockSum term 2438438 469 19542708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2438907 : blockSum term 2438907 469 18276248 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2439376 : blockSum term 2439376 468 17641588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2439844 : blockSum term 2439844 469 23935180 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2440313 : blockSum term 2440313 469 23299239 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2440782 : blockSum term 2440782 469 23292469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2441251 : blockSum term 2441251 468 18880736 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2441719 : blockSum term 2441719 469 17617217 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2442188 : blockSum term 2442188 469 19499337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2442657 : blockSum term 2442657 469 20122927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2443126 : blockSum term 2443126 468 15716879 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2443594 : blockSum term 2443594 469 22626110 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2444063 : blockSum term 2444063 469 23876182 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2444532 : blockSum term 2444532 469 20728168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2445001 : blockSum term 2445001 468 21978282 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2445469 : blockSum term 2445469 469 21971655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2445938 : blockSum term 2445938 469 18199802 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2446407 : blockSum term 2446407 469 18194443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2446876 : blockSum term 2446876 468 16935016 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2447344 : blockSum term 2447344 469 20692363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2447813 : blockSum term 2447813 469 21313380 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2448282 : blockSum term 2448282 469 18800215 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2448751 : blockSum term 2448751 468 21928222 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2449219 : blockSum term 2449219 469 19416546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2449688 : blockSum term 2449688 469 24419882 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2450157 : blockSum term 2450157 469 15649181 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2450626 : blockSum term 2450626 468 18148084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2451094 : blockSum term 2451094 469 21896236 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2451563 : blockSum term 2451563 469 21890625 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2452032 : blockSum term 2452032 469 21259109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2452501 : blockSum term 2452501 468 24378650 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2452969 : blockSum term 2452969 469 19372118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2453438 : blockSum term 2453438 469 21865951 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2453907 : blockSum term 2453907 469 19985487 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2454376 : blockSum term 2454376 468 16858050 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2454844 : blockSum term 2454844 469 18102176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2455313 : blockSum term 2455313 469 21841027 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2455782 : blockSum term 2455782 469 18091932 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2456251 : blockSum term 2456251 468 19334005 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2456719 : blockSum term 2456719 469 18081835 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2457188 : blockSum term 2457188 469 20569922 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2457657 : blockSum term 2457657 469 18694679 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2458126 : blockSum term 2458126 468 23050461 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2458594 : blockSum term 2458594 469 21175790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2459063 : blockSum term 2459063 469 20547048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2459532 : blockSum term 2459532 469 21786278 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2460001 : blockSum term 2460001 468 16801968 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2460469 : blockSum term 2460469 469 26129341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2460938 : blockSum term 2460938 469 19280735 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2461407 : blockSum term 2461407 469 19896233 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2461876 : blockSum term 2461876 468 15539805 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2462344 : blockSum term 2462344 469 19263637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2462813 : blockSum term 2462813 469 18637289 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2463282 : blockSum term 2463282 469 18631953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2463751 : blockSum term 2463751 468 24835316 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2464219 : blockSum term 2464219 469 19862532 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2464688 : blockSum term 2464688 469 22960082 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2465157 : blockSum term 2465157 469 19231122 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2465626 : blockSum term 2465626 468 18605098 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2466094 : blockSum term 2466094 469 18599563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2466563 : blockSum term 2466563 469 19214204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2467032 : blockSum term 2467032 469 19208853 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2467501 : blockSum term 2467501 468 17964702 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2467969 : blockSum term 2467969 469 19817715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2468438 : blockSum term 2468438 469 18574003 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2468907 : blockSum term 2468907 469 15474250 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2469376 : blockSum term 2469376 468 17326934 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2469844 : blockSum term 2469844 469 23508251 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2470313 : blockSum term 2470313 469 19172365 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2470782 : blockSum term 2470782 469 21639608 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2471251 : blockSum term 2471251 468 20397340 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2471719 : blockSum term 2471719 469 18537589 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2472188 : blockSum term 2472188 469 18532862 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2472657 : blockSum term 2472657 469 20380899 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2473126 : blockSum term 2473126 468 21610085 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2473594 : blockSum term 2473594 469 16048119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2474063 : blockSum term 2474063 469 12958770 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2474532 : blockSum term 2474532 469 25293806 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2475001 : blockSum term 2475001 468 17885334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2475469 : blockSum term 2475469 469 17880392 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2475938 : blockSum term 2475938 469 21573834 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2476407 : blockSum term 2476407 469 19103062 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2476876 : blockSum term 2476876 468 22177539 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2477344 : blockSum term 2477344 469 16012712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2477813 : blockSum term 2477813 469 19087514 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2478282 : blockSum term 2478282 469 22774900 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2478751 : blockSum term 2478751 468 12307448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2479219 : blockSum term 2479219 469 23377473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2479688 : blockSum term 2479688 469 18450646 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2480157 : blockSum term 2480157 469 20904496 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2480626 : blockSum term 2480626 468 19054335 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2481094 : blockSum term 2481094 469 20278328 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2481563 : blockSum term 2481563 469 19043290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2482032 : blockSum term 2482032 469 18424337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2482501 : blockSum term 2482501 468 20261198 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2482969 : blockSum term 2482969 469 14731832 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2483438 : blockSum term 2483438 469 20864059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2483907 : blockSum term 2483907 469 19630968 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2484376 : blockSum term 2484376 468 17785646 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2484844 : blockSum term 2484844 469 22072768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2485313 : blockSum term 2485313 469 20840378 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2485782 : blockSum term 2485782 469 20221193 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2486251 : blockSum term 2486251 468 23890773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2486719 : blockSum term 2486719 469 17760104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2487188 : blockSum term 2487188 469 22653033 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2487657 : blockSum term 2487657 469 20810207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2488126 : blockSum term 2488126 468 22639839 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2488594 : blockSum term 2488594 469 14681314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2489063 : blockSum term 2489063 469 18346624 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2489532 : blockSum term 2489532 469 20787195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2490001 : blockSum term 2490001 468 17114418 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2490469 : blockSum term 2490469 469 21998324 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2490938 : blockSum term 2490938 469 18326439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2491407 : blockSum term 2491407 469 17710719 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2491876 : blockSum term 2491876 468 18316620 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2492344 : blockSum term 2492344 469 16480685 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2492813 : blockSum term 2492813 469 17086388 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2493282 : blockSum term 2493282 469 19521984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2493751 : blockSum term 2493751 468 20125963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2494219 : blockSum term 2494219 469 22558982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2494688 : blockSum term 2494688 469 18896048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2495157 : blockSum term 2495157 469 19500051 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2495626 : blockSum term 2495626 468 17666764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2496094 : blockSum term 2496094 469 20707174 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2496563 : blockSum term 2496563 469 19483318 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2497032 : blockSum term 2497032 469 20086206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2497501 : blockSum term 2497501 468 21905629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2497969 : blockSum term 2497969 469 20074292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2498438 : blockSum term 2498438 469 15203994 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2498907 : blockSum term 2498907 469 18847794 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2499376 : blockSum term 2499376 468 19450251 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2499844 : blockSum term 2499844 469 21268109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2500313 : blockSum term 2500313 469 17616599 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2500782 : blockSum term 2500782 469 19433710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2501251 : blockSum term 2501251 468 18821351 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2501719 : blockSum term 2501719 469 20029680 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2502188 : blockSum term 2502188 469 23665177 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2502657 : blockSum term 2502657 469 16379211 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2503126 : blockSum term 2503126 468 21832434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2503594 : blockSum term 2503594 469 15763536 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2504063 : blockSum term 2504063 469 21820521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2504532 : blockSum term 2504532 469 21208714 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2505001 : blockSum term 2505001 468 21808549 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2505469 : blockSum term 2505469 469 16957386 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2505938 : blockSum term 2505938 469 17557751 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2506407 : blockSum term 2506407 469 22395074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2506876 : blockSum term 2506876 468 18153006 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2507344 : blockSum term 2507344 469 15727925 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2507813 : blockSum term 2507813 469 22980821 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2508282 : blockSum term 2508282 469 16928645 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2508751 : blockSum term 2508751 468 16924234 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2509219 : blockSum term 2509219 469 21149703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2509688 : blockSum term 2509688 469 18726999 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2510157 : blockSum term 2510157 469 18721650 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2510626 : blockSum term 2510626 468 18113195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2511094 : blockSum term 2511094 469 22333351 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2511563 : blockSum term 2511563 469 19912893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2512032 : blockSum term 2512032 469 18701011 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2512501 : blockSum term 2512501 468 19901845 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2512969 : blockSum term 2512969 469 18690387 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2513438 : blockSum term 2513438 469 21095988 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2513907 : blockSum term 2513907 469 19282239 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2514376 : blockSum term 2514376 468 18072496 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2514844 : blockSum term 2514844 469 19873946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2515313 : blockSum term 2515313 469 24685167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2515782 : blockSum term 2515782 469 13242057 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2516251 : blockSum term 2516251 468 16247375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2516719 : blockSum term 2516719 469 18047238 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2517188 : blockSum term 2517188 469 16238439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2517657 : blockSum term 2517657 469 16233964 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2518126 : blockSum term 2518126 468 21639186 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2518594 : blockSum term 2518594 469 18027000 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2519063 : blockSum term 2519063 469 19824521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2519532 : blockSum term 2519532 469 19818493 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2520001 : blockSum term 2520001 468 19212310 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2520469 : blockSum term 2520469 469 16206021 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2520938 : blockSum term 2520938 469 18601517 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2521407 : blockSum term 2521407 469 19196075 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2521876 : blockSum term 2521876 468 17391728 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2522344 : blockSum term 2522344 469 20984167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2522813 : blockSum term 2522813 469 22177054 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2523282 : blockSum term 2523282 469 20372904 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2523751 : blockSum term 2523751 468 25159928 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2524219 : blockSum term 2524219 469 20960036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2524688 : blockSum term 2524688 469 20355043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2525157 : blockSum term 2525157 469 21546241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2525626 : blockSum term 2525626 468 15557033 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2526094 : blockSum term 2526094 469 19739701 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2526563 : blockSum term 2526563 469 20930262 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2527032 : blockSum term 2527032 469 17934988 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2527501 : blockSum term 2527501 468 14344176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2527969 : blockSum term 2527969 469 15535359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2528438 : blockSum term 2528438 469 20907149 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2528907 : blockSum term 2528907 469 22692641 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2529376 : blockSum term 2529376 468 20894965 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2529844 : blockSum term 2529844 469 25066514 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2530313 : blockSum term 2530313 469 17899618 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2530782 : blockSum term 2530782 469 20280373 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2531251 : blockSum term 2531251 468 19081711 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2531719 : blockSum term 2531719 469 17288484 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2532188 : blockSum term 2532188 469 18476083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2532657 : blockSum term 2532657 469 18470827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2533126 : blockSum term 2533126 468 17274609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2533594 : blockSum term 2533594 469 16673916 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2534063 : blockSum term 2534063 469 19646207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2534532 : blockSum term 2534532 469 19640421 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2535001 : blockSum term 2535001 468 21419636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2535469 : blockSum term 2535469 469 14870275 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2535938 : blockSum term 2535938 469 19623647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2536407 : blockSum term 2536407 469 19618109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2536876 : blockSum term 2536876 468 14858346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2537344 : blockSum term 2537344 469 16636818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2537813 : blockSum term 2537813 469 16631989 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2538282 : blockSum term 2538282 469 25534827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2538751 : blockSum term 2538751 468 18403486 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2539219 : blockSum term 2539219 469 22551778 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2539688 : blockSum term 2539688 469 10679385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2540157 : blockSum term 2540157 469 20167168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2540626 : blockSum term 2540626 468 19568615 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2541094 : blockSum term 2541094 469 15413020 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2541563 : blockSum term 2541563 469 20150074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2542032 : blockSum term 2542032 469 15997509 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2542501 : blockSum term 2542501 468 18362825 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2542969 : blockSum term 2542969 469 19542024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2543438 : blockSum term 2543438 469 18352654 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2543907 : blockSum term 2543907 469 21898225 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2544376 : blockSum term 2544376 468 18342306 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2544844 : blockSum term 2544844 469 18337442 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2545313 : blockSum term 2545313 469 19515055 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2545782 : blockSum term 2545782 469 20691676 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2546251 : blockSum term 2546251 468 15957888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2546719 : blockSum term 2546719 469 15362765 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2547188 : blockSum term 2547188 469 15358662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2547657 : blockSum term 2547657 469 17716589 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2548126 : blockSum term 2548126 468 22434556 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2548594 : blockSum term 2548594 469 19477016 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2549063 : blockSum term 2549063 469 21242206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2549532 : blockSum term 2549532 469 18286835 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 2430001 120000 4974874079 := (join_sums term (lo:=2430001) (a:=60000) (b:=60000) (join_sums term (lo:=2430001) (a:=30000) (b:=30000) (join_sums term (lo:=2430001) (a:=15000) (b:=15000) (join_sums term (lo:=2430001) (a:=7500) (b:=7500) (join_sums term (lo:=2430001) (a:=3750) (b:=3750) (join_sums term (lo:=2430001) (a:=1875) (b:=1875) (join_sums term (lo:=2430001) (a:=937) (b:=938) (join_sums term (lo:=2430001) (a:=468) (b:=469) r2430001 r2430469) (join_sums term (lo:=2430938) (a:=469) (b:=469) r2430938 r2431407)) (join_sums term (lo:=2431876) (a:=937) (b:=938) (join_sums term (lo:=2431876) (a:=468) (b:=469) r2431876 r2432344) (join_sums term (lo:=2432813) (a:=469) (b:=469) r2432813 r2433282))) (join_sums term (lo:=2433751) (a:=1875) (b:=1875) (join_sums term (lo:=2433751) (a:=937) (b:=938) (join_sums term (lo:=2433751) (a:=468) (b:=469) r2433751 r2434219) (join_sums term (lo:=2434688) (a:=469) (b:=469) r2434688 r2435157)) (join_sums term (lo:=2435626) (a:=937) (b:=938) (join_sums term (lo:=2435626) (a:=468) (b:=469) r2435626 r2436094) (join_sums term (lo:=2436563) (a:=469) (b:=469) r2436563 r2437032)))) (join_sums term (lo:=2437501) (a:=3750) (b:=3750) (join_sums term (lo:=2437501) (a:=1875) (b:=1875) (join_sums term (lo:=2437501) (a:=937) (b:=938) (join_sums term (lo:=2437501) (a:=468) (b:=469) r2437501 r2437969) (join_sums term (lo:=2438438) (a:=469) (b:=469) r2438438 r2438907)) (join_sums term (lo:=2439376) (a:=937) (b:=938) (join_sums term (lo:=2439376) (a:=468) (b:=469) r2439376 r2439844) (join_sums term (lo:=2440313) (a:=469) (b:=469) r2440313 r2440782))) (join_sums term (lo:=2441251) (a:=1875) (b:=1875) (join_sums term (lo:=2441251) (a:=937) (b:=938) (join_sums term (lo:=2441251) (a:=468) (b:=469) r2441251 r2441719) (join_sums term (lo:=2442188) (a:=469) (b:=469) r2442188 r2442657)) (join_sums term (lo:=2443126) (a:=937) (b:=938) (join_sums term (lo:=2443126) (a:=468) (b:=469) r2443126 r2443594) (join_sums term (lo:=2444063) (a:=469) (b:=469) r2444063 r2444532))))) (join_sums term (lo:=2445001) (a:=7500) (b:=7500) (join_sums term (lo:=2445001) (a:=3750) (b:=3750) (join_sums term (lo:=2445001) (a:=1875) (b:=1875) (join_sums term (lo:=2445001) (a:=937) (b:=938) (join_sums term (lo:=2445001) (a:=468) (b:=469) r2445001 r2445469) (join_sums term (lo:=2445938) (a:=469) (b:=469) r2445938 r2446407)) (join_sums term (lo:=2446876) (a:=937) (b:=938) (join_sums term (lo:=2446876) (a:=468) (b:=469) r2446876 r2447344) (join_sums term (lo:=2447813) (a:=469) (b:=469) r2447813 r2448282))) (join_sums term (lo:=2448751) (a:=1875) (b:=1875) (join_sums term (lo:=2448751) (a:=937) (b:=938) (join_sums term (lo:=2448751) (a:=468) (b:=469) r2448751 r2449219) (join_sums term (lo:=2449688) (a:=469) (b:=469) r2449688 r2450157)) (join_sums term (lo:=2450626) (a:=937) (b:=938) (join_sums term (lo:=2450626) (a:=468) (b:=469) r2450626 r2451094) (join_sums term (lo:=2451563) (a:=469) (b:=469) r2451563 r2452032)))) (join_sums term (lo:=2452501) (a:=3750) (b:=3750) (join_sums term (lo:=2452501) (a:=1875) (b:=1875) (join_sums term (lo:=2452501) (a:=937) (b:=938) (join_sums term (lo:=2452501) (a:=468) (b:=469) r2452501 r2452969) (join_sums term (lo:=2453438) (a:=469) (b:=469) r2453438 r2453907)) (join_sums term (lo:=2454376) (a:=937) (b:=938) (join_sums term (lo:=2454376) (a:=468) (b:=469) r2454376 r2454844) (join_sums term (lo:=2455313) (a:=469) (b:=469) r2455313 r2455782))) (join_sums term (lo:=2456251) (a:=1875) (b:=1875) (join_sums term (lo:=2456251) (a:=937) (b:=938) (join_sums term (lo:=2456251) (a:=468) (b:=469) r2456251 r2456719) (join_sums term (lo:=2457188) (a:=469) (b:=469) r2457188 r2457657)) (join_sums term (lo:=2458126) (a:=937) (b:=938) (join_sums term (lo:=2458126) (a:=468) (b:=469) r2458126 r2458594) (join_sums term (lo:=2459063) (a:=469) (b:=469) r2459063 r2459532)))))) (join_sums term (lo:=2460001) (a:=15000) (b:=15000) (join_sums term (lo:=2460001) (a:=7500) (b:=7500) (join_sums term (lo:=2460001) (a:=3750) (b:=3750) (join_sums term (lo:=2460001) (a:=1875) (b:=1875) (join_sums term (lo:=2460001) (a:=937) (b:=938) (join_sums term (lo:=2460001) (a:=468) (b:=469) r2460001 r2460469) (join_sums term (lo:=2460938) (a:=469) (b:=469) r2460938 r2461407)) (join_sums term (lo:=2461876) (a:=937) (b:=938) (join_sums term (lo:=2461876) (a:=468) (b:=469) r2461876 r2462344) (join_sums term (lo:=2462813) (a:=469) (b:=469) r2462813 r2463282))) (join_sums term (lo:=2463751) (a:=1875) (b:=1875) (join_sums term (lo:=2463751) (a:=937) (b:=938) (join_sums term (lo:=2463751) (a:=468) (b:=469) r2463751 r2464219) (join_sums term (lo:=2464688) (a:=469) (b:=469) r2464688 r2465157)) (join_sums term (lo:=2465626) (a:=937) (b:=938) (join_sums term (lo:=2465626) (a:=468) (b:=469) r2465626 r2466094) (join_sums term (lo:=2466563) (a:=469) (b:=469) r2466563 r2467032)))) (join_sums term (lo:=2467501) (a:=3750) (b:=3750) (join_sums term (lo:=2467501) (a:=1875) (b:=1875) (join_sums term (lo:=2467501) (a:=937) (b:=938) (join_sums term (lo:=2467501) (a:=468) (b:=469) r2467501 r2467969) (join_sums term (lo:=2468438) (a:=469) (b:=469) r2468438 r2468907)) (join_sums term (lo:=2469376) (a:=937) (b:=938) (join_sums term (lo:=2469376) (a:=468) (b:=469) r2469376 r2469844) (join_sums term (lo:=2470313) (a:=469) (b:=469) r2470313 r2470782))) (join_sums term (lo:=2471251) (a:=1875) (b:=1875) (join_sums term (lo:=2471251) (a:=937) (b:=938) (join_sums term (lo:=2471251) (a:=468) (b:=469) r2471251 r2471719) (join_sums term (lo:=2472188) (a:=469) (b:=469) r2472188 r2472657)) (join_sums term (lo:=2473126) (a:=937) (b:=938) (join_sums term (lo:=2473126) (a:=468) (b:=469) r2473126 r2473594) (join_sums term (lo:=2474063) (a:=469) (b:=469) r2474063 r2474532))))) (join_sums term (lo:=2475001) (a:=7500) (b:=7500) (join_sums term (lo:=2475001) (a:=3750) (b:=3750) (join_sums term (lo:=2475001) (a:=1875) (b:=1875) (join_sums term (lo:=2475001) (a:=937) (b:=938) (join_sums term (lo:=2475001) (a:=468) (b:=469) r2475001 r2475469) (join_sums term (lo:=2475938) (a:=469) (b:=469) r2475938 r2476407)) (join_sums term (lo:=2476876) (a:=937) (b:=938) (join_sums term (lo:=2476876) (a:=468) (b:=469) r2476876 r2477344) (join_sums term (lo:=2477813) (a:=469) (b:=469) r2477813 r2478282))) (join_sums term (lo:=2478751) (a:=1875) (b:=1875) (join_sums term (lo:=2478751) (a:=937) (b:=938) (join_sums term (lo:=2478751) (a:=468) (b:=469) r2478751 r2479219) (join_sums term (lo:=2479688) (a:=469) (b:=469) r2479688 r2480157)) (join_sums term (lo:=2480626) (a:=937) (b:=938) (join_sums term (lo:=2480626) (a:=468) (b:=469) r2480626 r2481094) (join_sums term (lo:=2481563) (a:=469) (b:=469) r2481563 r2482032)))) (join_sums term (lo:=2482501) (a:=3750) (b:=3750) (join_sums term (lo:=2482501) (a:=1875) (b:=1875) (join_sums term (lo:=2482501) (a:=937) (b:=938) (join_sums term (lo:=2482501) (a:=468) (b:=469) r2482501 r2482969) (join_sums term (lo:=2483438) (a:=469) (b:=469) r2483438 r2483907)) (join_sums term (lo:=2484376) (a:=937) (b:=938) (join_sums term (lo:=2484376) (a:=468) (b:=469) r2484376 r2484844) (join_sums term (lo:=2485313) (a:=469) (b:=469) r2485313 r2485782))) (join_sums term (lo:=2486251) (a:=1875) (b:=1875) (join_sums term (lo:=2486251) (a:=937) (b:=938) (join_sums term (lo:=2486251) (a:=468) (b:=469) r2486251 r2486719) (join_sums term (lo:=2487188) (a:=469) (b:=469) r2487188 r2487657)) (join_sums term (lo:=2488126) (a:=937) (b:=938) (join_sums term (lo:=2488126) (a:=468) (b:=469) r2488126 r2488594) (join_sums term (lo:=2489063) (a:=469) (b:=469) r2489063 r2489532))))))) (join_sums term (lo:=2490001) (a:=30000) (b:=30000) (join_sums term (lo:=2490001) (a:=15000) (b:=15000) (join_sums term (lo:=2490001) (a:=7500) (b:=7500) (join_sums term (lo:=2490001) (a:=3750) (b:=3750) (join_sums term (lo:=2490001) (a:=1875) (b:=1875) (join_sums term (lo:=2490001) (a:=937) (b:=938) (join_sums term (lo:=2490001) (a:=468) (b:=469) r2490001 r2490469) (join_sums term (lo:=2490938) (a:=469) (b:=469) r2490938 r2491407)) (join_sums term (lo:=2491876) (a:=937) (b:=938) (join_sums term (lo:=2491876) (a:=468) (b:=469) r2491876 r2492344) (join_sums term (lo:=2492813) (a:=469) (b:=469) r2492813 r2493282))) (join_sums term (lo:=2493751) (a:=1875) (b:=1875) (join_sums term (lo:=2493751) (a:=937) (b:=938) (join_sums term (lo:=2493751) (a:=468) (b:=469) r2493751 r2494219) (join_sums term (lo:=2494688) (a:=469) (b:=469) r2494688 r2495157)) (join_sums term (lo:=2495626) (a:=937) (b:=938) (join_sums term (lo:=2495626) (a:=468) (b:=469) r2495626 r2496094) (join_sums term (lo:=2496563) (a:=469) (b:=469) r2496563 r2497032)))) (join_sums term (lo:=2497501) (a:=3750) (b:=3750) (join_sums term (lo:=2497501) (a:=1875) (b:=1875) (join_sums term (lo:=2497501) (a:=937) (b:=938) (join_sums term (lo:=2497501) (a:=468) (b:=469) r2497501 r2497969) (join_sums term (lo:=2498438) (a:=469) (b:=469) r2498438 r2498907)) (join_sums term (lo:=2499376) (a:=937) (b:=938) (join_sums term (lo:=2499376) (a:=468) (b:=469) r2499376 r2499844) (join_sums term (lo:=2500313) (a:=469) (b:=469) r2500313 r2500782))) (join_sums term (lo:=2501251) (a:=1875) (b:=1875) (join_sums term (lo:=2501251) (a:=937) (b:=938) (join_sums term (lo:=2501251) (a:=468) (b:=469) r2501251 r2501719) (join_sums term (lo:=2502188) (a:=469) (b:=469) r2502188 r2502657)) (join_sums term (lo:=2503126) (a:=937) (b:=938) (join_sums term (lo:=2503126) (a:=468) (b:=469) r2503126 r2503594) (join_sums term (lo:=2504063) (a:=469) (b:=469) r2504063 r2504532))))) (join_sums term (lo:=2505001) (a:=7500) (b:=7500) (join_sums term (lo:=2505001) (a:=3750) (b:=3750) (join_sums term (lo:=2505001) (a:=1875) (b:=1875) (join_sums term (lo:=2505001) (a:=937) (b:=938) (join_sums term (lo:=2505001) (a:=468) (b:=469) r2505001 r2505469) (join_sums term (lo:=2505938) (a:=469) (b:=469) r2505938 r2506407)) (join_sums term (lo:=2506876) (a:=937) (b:=938) (join_sums term (lo:=2506876) (a:=468) (b:=469) r2506876 r2507344) (join_sums term (lo:=2507813) (a:=469) (b:=469) r2507813 r2508282))) (join_sums term (lo:=2508751) (a:=1875) (b:=1875) (join_sums term (lo:=2508751) (a:=937) (b:=938) (join_sums term (lo:=2508751) (a:=468) (b:=469) r2508751 r2509219) (join_sums term (lo:=2509688) (a:=469) (b:=469) r2509688 r2510157)) (join_sums term (lo:=2510626) (a:=937) (b:=938) (join_sums term (lo:=2510626) (a:=468) (b:=469) r2510626 r2511094) (join_sums term (lo:=2511563) (a:=469) (b:=469) r2511563 r2512032)))) (join_sums term (lo:=2512501) (a:=3750) (b:=3750) (join_sums term (lo:=2512501) (a:=1875) (b:=1875) (join_sums term (lo:=2512501) (a:=937) (b:=938) (join_sums term (lo:=2512501) (a:=468) (b:=469) r2512501 r2512969) (join_sums term (lo:=2513438) (a:=469) (b:=469) r2513438 r2513907)) (join_sums term (lo:=2514376) (a:=937) (b:=938) (join_sums term (lo:=2514376) (a:=468) (b:=469) r2514376 r2514844) (join_sums term (lo:=2515313) (a:=469) (b:=469) r2515313 r2515782))) (join_sums term (lo:=2516251) (a:=1875) (b:=1875) (join_sums term (lo:=2516251) (a:=937) (b:=938) (join_sums term (lo:=2516251) (a:=468) (b:=469) r2516251 r2516719) (join_sums term (lo:=2517188) (a:=469) (b:=469) r2517188 r2517657)) (join_sums term (lo:=2518126) (a:=937) (b:=938) (join_sums term (lo:=2518126) (a:=468) (b:=469) r2518126 r2518594) (join_sums term (lo:=2519063) (a:=469) (b:=469) r2519063 r2519532)))))) (join_sums term (lo:=2520001) (a:=15000) (b:=15000) (join_sums term (lo:=2520001) (a:=7500) (b:=7500) (join_sums term (lo:=2520001) (a:=3750) (b:=3750) (join_sums term (lo:=2520001) (a:=1875) (b:=1875) (join_sums term (lo:=2520001) (a:=937) (b:=938) (join_sums term (lo:=2520001) (a:=468) (b:=469) r2520001 r2520469) (join_sums term (lo:=2520938) (a:=469) (b:=469) r2520938 r2521407)) (join_sums term (lo:=2521876) (a:=937) (b:=938) (join_sums term (lo:=2521876) (a:=468) (b:=469) r2521876 r2522344) (join_sums term (lo:=2522813) (a:=469) (b:=469) r2522813 r2523282))) (join_sums term (lo:=2523751) (a:=1875) (b:=1875) (join_sums term (lo:=2523751) (a:=937) (b:=938) (join_sums term (lo:=2523751) (a:=468) (b:=469) r2523751 r2524219) (join_sums term (lo:=2524688) (a:=469) (b:=469) r2524688 r2525157)) (join_sums term (lo:=2525626) (a:=937) (b:=938) (join_sums term (lo:=2525626) (a:=468) (b:=469) r2525626 r2526094) (join_sums term (lo:=2526563) (a:=469) (b:=469) r2526563 r2527032)))) (join_sums term (lo:=2527501) (a:=3750) (b:=3750) (join_sums term (lo:=2527501) (a:=1875) (b:=1875) (join_sums term (lo:=2527501) (a:=937) (b:=938) (join_sums term (lo:=2527501) (a:=468) (b:=469) r2527501 r2527969) (join_sums term (lo:=2528438) (a:=469) (b:=469) r2528438 r2528907)) (join_sums term (lo:=2529376) (a:=937) (b:=938) (join_sums term (lo:=2529376) (a:=468) (b:=469) r2529376 r2529844) (join_sums term (lo:=2530313) (a:=469) (b:=469) r2530313 r2530782))) (join_sums term (lo:=2531251) (a:=1875) (b:=1875) (join_sums term (lo:=2531251) (a:=937) (b:=938) (join_sums term (lo:=2531251) (a:=468) (b:=469) r2531251 r2531719) (join_sums term (lo:=2532188) (a:=469) (b:=469) r2532188 r2532657)) (join_sums term (lo:=2533126) (a:=937) (b:=938) (join_sums term (lo:=2533126) (a:=468) (b:=469) r2533126 r2533594) (join_sums term (lo:=2534063) (a:=469) (b:=469) r2534063 r2534532))))) (join_sums term (lo:=2535001) (a:=7500) (b:=7500) (join_sums term (lo:=2535001) (a:=3750) (b:=3750) (join_sums term (lo:=2535001) (a:=1875) (b:=1875) (join_sums term (lo:=2535001) (a:=937) (b:=938) (join_sums term (lo:=2535001) (a:=468) (b:=469) r2535001 r2535469) (join_sums term (lo:=2535938) (a:=469) (b:=469) r2535938 r2536407)) (join_sums term (lo:=2536876) (a:=937) (b:=938) (join_sums term (lo:=2536876) (a:=468) (b:=469) r2536876 r2537344) (join_sums term (lo:=2537813) (a:=469) (b:=469) r2537813 r2538282))) (join_sums term (lo:=2538751) (a:=1875) (b:=1875) (join_sums term (lo:=2538751) (a:=937) (b:=938) (join_sums term (lo:=2538751) (a:=468) (b:=469) r2538751 r2539219) (join_sums term (lo:=2539688) (a:=469) (b:=469) r2539688 r2540157)) (join_sums term (lo:=2540626) (a:=937) (b:=938) (join_sums term (lo:=2540626) (a:=468) (b:=469) r2540626 r2541094) (join_sums term (lo:=2541563) (a:=469) (b:=469) r2541563 r2542032)))) (join_sums term (lo:=2542501) (a:=3750) (b:=3750) (join_sums term (lo:=2542501) (a:=1875) (b:=1875) (join_sums term (lo:=2542501) (a:=937) (b:=938) (join_sums term (lo:=2542501) (a:=468) (b:=469) r2542501 r2542969) (join_sums term (lo:=2543438) (a:=469) (b:=469) r2543438 r2543907)) (join_sums term (lo:=2544376) (a:=937) (b:=938) (join_sums term (lo:=2544376) (a:=468) (b:=469) r2544376 r2544844) (join_sums term (lo:=2545313) (a:=469) (b:=469) r2545313 r2545782))) (join_sums term (lo:=2546251) (a:=1875) (b:=1875) (join_sums term (lo:=2546251) (a:=937) (b:=938) (join_sums term (lo:=2546251) (a:=468) (b:=469) r2546251 r2546719) (join_sums term (lo:=2547188) (a:=469) (b:=469) r2547188 r2547657)) (join_sums term (lo:=2548126) (a:=937) (b:=938) (join_sums term (lo:=2548126) (a:=468) (b:=469) r2548126 r2548594) (join_sums term (lo:=2549063) (a:=469) (b:=469) r2549063 r2549532))))))))

private theorem rows : blockSum term 0 2550001 4974874079 :=
  join_sums term (lo:=0) (a:=2430001) (b:=120000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 2550000).filter (2430000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4974874079 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From2430000To2550000
