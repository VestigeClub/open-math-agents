import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 2,550,000 through 2,670,000

The sum covers 8,151 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From2550000To2670000

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


private abbrev term := contribution 30110134441897 2550000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 2550001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 2550000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r2550001 : blockSum term 2550001 468 15922825 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2550469 : blockSum term 2550469 469 15328858 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2550938 : blockSum term 2550938 469 18861032 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2551407 : blockSum term 2551407 469 18266229 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2551876 : blockSum term 2551876 468 19439249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2552344 : blockSum term 2552344 469 22966415 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2552813 : blockSum term 2552813 469 18250228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2553282 : blockSum term 2553282 469 19422712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2553751 : blockSum term 2553751 468 18240349 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2554219 : blockSum term 2554219 469 20588439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2554688 : blockSum term 2554688 469 19994075 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2555157 : blockSum term 2555157 469 19400455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2555626 : blockSum term 2555626 468 18218878 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2556094 : blockSum term 2556094 469 18213656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2556563 : blockSum term 2556563 469 15271891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2557032 : blockSum term 2557032 469 15855070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2557501 : blockSum term 2557501 468 21134283 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2557969 : blockSum term 2557969 469 18194089 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2558438 : blockSum term 2558438 469 16428572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2558907 : blockSum term 2558907 469 17010697 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2559376 : blockSum term 2559376 468 23456779 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2559844 : blockSum term 2559844 469 18759990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2560313 : blockSum term 2560313 469 18755208 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2560782 : blockSum term 2560782 469 20507366 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2561251 : blockSum term 2561251 468 16401470 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2561719 : blockSum term 2561719 469 20496670 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2562188 : blockSum term 2562188 469 20490356 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2562657 : blockSum term 2562657 469 16972712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2563126 : blockSum term 2563126 468 19308605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2563594 : blockSum term 2563594 469 21057542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2564063 : blockSum term 2564063 469 16958507 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2564532 : blockSum term 2564532 469 16369426 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2565001 : blockSum term 2565001 468 18702774 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2565469 : blockSum term 2565469 469 12270071 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2565938 : blockSum term 2565938 469 21028913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2566407 : blockSum term 2566407 469 20438666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2566876 : blockSum term 2566876 468 14594795 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2567344 : blockSum term 2567344 469 23929170 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2567813 : blockSum term 2567813 469 19837929 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2568282 : blockSum term 2568282 469 20415843 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2568751 : blockSum term 2568751 468 16328105 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2569219 : blockSum term 2569219 469 15740749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2569688 : blockSum term 2569688 469 15736584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2570157 : blockSum term 2570157 469 21558501 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2570626 : blockSum term 2570626 468 22717695 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2571094 : blockSum term 2571094 469 15722961 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2571563 : blockSum term 2571563 469 16300985 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2572032 : blockSum term 2572032 469 23280882 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2572501 : blockSum term 2572501 468 18037906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2572969 : blockSum term 2572969 469 18032554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2573438 : blockSum term 2573438 469 16864153 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2573907 : blockSum term 2573907 469 18022006 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2574376 : blockSum term 2574376 468 20922888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2574844 : blockSum term 2574844 469 19173847 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2575313 : blockSum term 2575313 469 18006890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2575782 : blockSum term 2575782 469 19744040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2576251 : blockSum term 2576251 468 21479895 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2576719 : blockSum term 2576719 469 19732370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2577188 : blockSum term 2577188 469 19726275 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2577657 : blockSum term 2577657 469 22040948 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2578126 : blockSum term 2578126 468 18555614 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2578594 : blockSum term 2578594 469 17391580 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2579063 : blockSum term 2579063 469 16807443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2579532 : blockSum term 2579532 469 17961655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2580001 : blockSum term 2580001 468 15060191 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2580469 : blockSum term 2580469 469 24900901 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2580938 : blockSum term 2580938 469 20261986 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2581407 : blockSum term 2581407 469 19099052 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2581876 : blockSum term 2581876 468 20829722 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2582344 : blockSum term 2582344 469 17931126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2582813 : blockSum term 2582813 469 19660676 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2583282 : blockSum term 2583282 469 20811351 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2583751 : blockSum term 2583751 468 17337957 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2584219 : blockSum term 2584219 469 16754901 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2584688 : blockSum term 2584688 469 19060450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2585157 : blockSum term 2585157 469 17322715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2585626 : blockSum term 2585626 468 16163358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2586094 : blockSum term 2586094 469 16159205 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2586563 : blockSum term 2586563 469 22501274 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2587032 : blockSum term 2587032 469 16727424 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2587501 : blockSum term 2587501 468 17875850 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2587969 : blockSum term 2587969 469 20177248 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2588438 : blockSum term 2588438 469 17290125 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2588907 : blockSum term 2588907 469 20166216 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2589376 : blockSum term 2589376 468 19584794 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2589844 : blockSum term 2589844 469 16124369 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2590313 : blockSum term 2590313 469 17271234 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2590782 : blockSum term 2590782 469 17266150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2591251 : blockSum term 2591251 468 15535201 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2591719 : blockSum term 2591719 469 18407362 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2592188 : blockSum term 2592188 469 18401462 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2592657 : blockSum term 2592657 469 17246443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2593126 : blockSum term 2593126 468 17241467 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2593594 : blockSum term 2593594 469 19534305 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2594063 : blockSum term 2594063 469 16656930 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2594532 : blockSum term 2594532 469 24116193 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2595001 : blockSum term 2595001 468 17795081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2595469 : blockSum term 2595469 469 18364000 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2595938 : blockSum term 2595938 469 16637687 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2596407 : blockSum term 2596407 469 20074499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2596876 : blockSum term 2596876 468 19495472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2597344 : blockSum term 2597344 469 18916723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2597813 : blockSum term 2597813 469 16619058 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2598282 : blockSum term 2598282 469 17760283 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2598751 : blockSum term 2598751 468 18900911 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2599219 : blockSum term 2599219 469 17177334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2599688 : blockSum term 2599688 469 17745503 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2600157 : blockSum term 2600157 469 20601469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2600626 : blockSum term 2600626 468 14302377 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2601094 : blockSum term 2601094 469 16586617 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2601563 : blockSum term 2601563 469 17725803 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2602032 : blockSum term 2602032 469 20007242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2602501 : blockSum term 2602501 468 16001478 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2602969 : blockSum term 2602969 469 15997097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2603438 : blockSum term 2603438 469 18277362 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2603907 : blockSum term 2603907 469 17130116 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2604376 : blockSum term 2604376 468 19979167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2604844 : blockSum term 2604844 469 17120366 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2605313 : blockSum term 2605313 469 18256918 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2605782 : blockSum term 2605782 469 15400073 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2606251 : blockSum term 2606251 468 16536370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2606719 : blockSum term 2606719 469 18811718 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2607188 : blockSum term 2607188 469 17096697 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2607657 : blockSum term 2607657 469 15382930 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2608126 : blockSum term 2608126 468 19935619 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2608594 : blockSum term 2608594 469 16513122 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2609063 : blockSum term 2609063 469 21631149 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2609532 : blockSum term 2609532 469 14796100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2610001 : blockSum term 2610001 468 15929705 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2610469 : blockSum term 2610469 469 18769402 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2610938 : blockSum term 2610938 469 18764079 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2611407 : blockSum term 2611407 469 18758192 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2611876 : blockSum term 2611876 468 18753205 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2612344 : blockSum term 2612344 469 17611676 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2612813 : blockSum term 2612813 469 18742430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2613282 : blockSum term 2613282 469 17033049 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2613751 : blockSum term 2613751 468 20434348 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2614219 : blockSum term 2614219 469 20428682 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2614688 : blockSum term 2614688 469 16451910 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2615157 : blockSum term 2615157 469 19850308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2615626 : blockSum term 2615626 468 22112536 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2616094 : blockSum term 2616094 469 14737754 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2616563 : blockSum term 2616563 469 19267592 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2617032 : blockSum term 2617032 469 20961541 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2617501 : blockSum term 2617501 468 16991121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2617969 : blockSum term 2617969 469 16986471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2618438 : blockSum term 2618438 469 18679493 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2618907 : blockSum term 2618907 469 15844889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2619376 : blockSum term 2619376 468 13011764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2619844 : blockSum term 2619844 469 21491692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2620313 : blockSum term 2620313 469 14701131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2620782 : blockSum term 2620782 469 16958114 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2621251 : blockSum term 2621251 468 15258096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2621719 : blockSum term 2621719 469 18643975 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2622188 : blockSum term 2622188 469 20897873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2622657 : blockSum term 2622657 469 14680840 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2623126 : blockSum term 2623126 468 22579787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2623594 : blockSum term 2623594 469 17494137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2624063 : blockSum term 2624063 469 17489744 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2624532 : blockSum term 2624532 469 19740272 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2625001 : blockSum term 2625001 468 15224081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2625469 : blockSum term 2625469 469 18602097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2625938 : blockSum term 2625938 469 14651991 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2626407 : blockSum term 2626407 469 17464758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2626876 : blockSum term 2626876 468 16896937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2627344 : blockSum term 2627344 469 18581146 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2627813 : blockSum term 2627813 469 16886965 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2628282 : blockSum term 2628282 469 15756303 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2628751 : blockSum term 2628751 468 16877123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2629219 : blockSum term 2629219 469 19684137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2629688 : blockSum term 2629688 469 19116844 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2630157 : blockSum term 2630157 469 20797510 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2630626 : blockSum term 2630626 468 19667606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2631094 : blockSum term 2631094 469 20785405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2631563 : blockSum term 2631563 469 17409692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2632032 : blockSum term 2632032 469 21896355 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2632501 : blockSum term 2632501 468 17961086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2632969 : blockSum term 2632969 469 18517105 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2633438 : blockSum term 2633438 469 20756361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2633907 : blockSum term 2633907 469 12899207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2634376 : blockSum term 2634376 468 20184610 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2634844 : blockSum term 2634844 469 15694907 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2635313 : blockSum term 2635313 469 13448963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2635782 : blockSum term 2635782 469 19047497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2636251 : blockSum term 2636251 468 17922107 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2636719 : blockSum term 2636719 469 15117456 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2637188 : blockSum term 2637188 469 17911886 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2637657 : blockSum term 2637657 469 16787779 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2638126 : blockSum term 2638126 468 16223515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2638594 : blockSum term 2638594 469 15660243 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2639063 : blockSum term 2639063 469 20128536 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2639532 : blockSum term 2639532 469 18445724 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2640001 : blockSum term 2640001 468 15088216 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2640469 : blockSum term 2640469 469 18994540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2640938 : blockSum term 2640938 469 17872192 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2641407 : blockSum term 2641407 469 21775991 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2641876 : blockSum term 2641876 468 17861988 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2642344 : blockSum term 2642344 469 15624855 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2642813 : blockSum term 2642813 469 17293840 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2643282 : blockSum term 2643282 469 20634881 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2643751 : blockSum term 2643751 468 19514199 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2644219 : blockSum term 2644219 469 15049688 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2644688 : blockSum term 2644688 469 16717475 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2645157 : blockSum term 2645157 469 21726560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2645626 : blockSum term 2645626 468 23390750 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2646094 : blockSum term 2646094 469 11135486 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2646563 : blockSum term 2646563 469 17812066 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2647032 : blockSum term 2647032 469 18920164 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2647501 : blockSum term 2647501 468 16689497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2647969 : blockSum term 2647969 469 21134183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2648438 : blockSum term 2648438 469 16680140 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2648907 : blockSum term 2648907 469 16119827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2649376 : blockSum term 2649376 468 17226951 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2649844 : blockSum term 2649844 469 18888782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2650313 : blockSum term 2650313 469 17217388 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2650782 : blockSum term 2650782 469 17212607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2651251 : blockSum term 2651251 468 21647767 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2651719 : blockSum term 2651719 469 18867261 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2652188 : blockSum term 2652188 469 15533477 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2652657 : blockSum term 2652657 469 16083531 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2653126 : blockSum term 2653126 468 14415418 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2653594 : blockSum term 2653594 469 19954679 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2654063 : blockSum term 2654063 469 17178271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2654532 : blockSum term 2654532 469 19389409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2655001 : blockSum term 2655001 468 18830230 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2655469 : blockSum term 2655469 469 17164122 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2655938 : blockSum term 2655938 469 21033887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2656407 : blockSum term 2656407 469 16601012 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2656876 : blockSum term 2656876 468 22681799 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2657344 : blockSum term 2657344 469 17145167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2657813 : blockSum term 2657813 469 14928622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2658282 : blockSum term 2658282 469 18793862 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2658751 : blockSum term 2658751 468 20446007 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2659219 : blockSum term 2659219 469 18230194 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2659688 : blockSum term 2659688 469 15463517 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2660157 : blockSum term 2660157 469 17115448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2660626 : blockSum term 2660626 468 14351393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2661094 : blockSum term 2661094 469 19313595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2661563 : blockSum term 2661563 469 16549839 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2662032 : blockSum term 2662032 469 14339266 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2662501 : blockSum term 2662501 468 17091860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2662969 : blockSum term 2662969 469 14882573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2663438 : blockSum term 2663438 469 18184842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2663907 : blockSum term 2663907 469 20933819 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2664376 : blockSum term 2664376 468 18174660 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2664844 : blockSum term 2664844 469 22574666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2665313 : blockSum term 2665313 469 16513569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2665782 : blockSum term 2665782 469 17059350 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2666251 : blockSum term 2666251 468 15953703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2666719 : blockSum term 2666719 469 14299302 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2667188 : blockSum term 2667188 469 17044689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2667657 : blockSum term 2667657 469 16489827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2668126 : blockSum term 2668126 468 19782386 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2668594 : blockSum term 2668594 469 14832554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2669063 : blockSum term 2669063 469 19221660 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2669532 : blockSum term 2669532 469 13726218 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 2550001 120000 4639168756 := (join_sums term (lo:=2550001) (a:=60000) (b:=60000) (join_sums term (lo:=2550001) (a:=30000) (b:=30000) (join_sums term (lo:=2550001) (a:=15000) (b:=15000) (join_sums term (lo:=2550001) (a:=7500) (b:=7500) (join_sums term (lo:=2550001) (a:=3750) (b:=3750) (join_sums term (lo:=2550001) (a:=1875) (b:=1875) (join_sums term (lo:=2550001) (a:=937) (b:=938) (join_sums term (lo:=2550001) (a:=468) (b:=469) r2550001 r2550469) (join_sums term (lo:=2550938) (a:=469) (b:=469) r2550938 r2551407)) (join_sums term (lo:=2551876) (a:=937) (b:=938) (join_sums term (lo:=2551876) (a:=468) (b:=469) r2551876 r2552344) (join_sums term (lo:=2552813) (a:=469) (b:=469) r2552813 r2553282))) (join_sums term (lo:=2553751) (a:=1875) (b:=1875) (join_sums term (lo:=2553751) (a:=937) (b:=938) (join_sums term (lo:=2553751) (a:=468) (b:=469) r2553751 r2554219) (join_sums term (lo:=2554688) (a:=469) (b:=469) r2554688 r2555157)) (join_sums term (lo:=2555626) (a:=937) (b:=938) (join_sums term (lo:=2555626) (a:=468) (b:=469) r2555626 r2556094) (join_sums term (lo:=2556563) (a:=469) (b:=469) r2556563 r2557032)))) (join_sums term (lo:=2557501) (a:=3750) (b:=3750) (join_sums term (lo:=2557501) (a:=1875) (b:=1875) (join_sums term (lo:=2557501) (a:=937) (b:=938) (join_sums term (lo:=2557501) (a:=468) (b:=469) r2557501 r2557969) (join_sums term (lo:=2558438) (a:=469) (b:=469) r2558438 r2558907)) (join_sums term (lo:=2559376) (a:=937) (b:=938) (join_sums term (lo:=2559376) (a:=468) (b:=469) r2559376 r2559844) (join_sums term (lo:=2560313) (a:=469) (b:=469) r2560313 r2560782))) (join_sums term (lo:=2561251) (a:=1875) (b:=1875) (join_sums term (lo:=2561251) (a:=937) (b:=938) (join_sums term (lo:=2561251) (a:=468) (b:=469) r2561251 r2561719) (join_sums term (lo:=2562188) (a:=469) (b:=469) r2562188 r2562657)) (join_sums term (lo:=2563126) (a:=937) (b:=938) (join_sums term (lo:=2563126) (a:=468) (b:=469) r2563126 r2563594) (join_sums term (lo:=2564063) (a:=469) (b:=469) r2564063 r2564532))))) (join_sums term (lo:=2565001) (a:=7500) (b:=7500) (join_sums term (lo:=2565001) (a:=3750) (b:=3750) (join_sums term (lo:=2565001) (a:=1875) (b:=1875) (join_sums term (lo:=2565001) (a:=937) (b:=938) (join_sums term (lo:=2565001) (a:=468) (b:=469) r2565001 r2565469) (join_sums term (lo:=2565938) (a:=469) (b:=469) r2565938 r2566407)) (join_sums term (lo:=2566876) (a:=937) (b:=938) (join_sums term (lo:=2566876) (a:=468) (b:=469) r2566876 r2567344) (join_sums term (lo:=2567813) (a:=469) (b:=469) r2567813 r2568282))) (join_sums term (lo:=2568751) (a:=1875) (b:=1875) (join_sums term (lo:=2568751) (a:=937) (b:=938) (join_sums term (lo:=2568751) (a:=468) (b:=469) r2568751 r2569219) (join_sums term (lo:=2569688) (a:=469) (b:=469) r2569688 r2570157)) (join_sums term (lo:=2570626) (a:=937) (b:=938) (join_sums term (lo:=2570626) (a:=468) (b:=469) r2570626 r2571094) (join_sums term (lo:=2571563) (a:=469) (b:=469) r2571563 r2572032)))) (join_sums term (lo:=2572501) (a:=3750) (b:=3750) (join_sums term (lo:=2572501) (a:=1875) (b:=1875) (join_sums term (lo:=2572501) (a:=937) (b:=938) (join_sums term (lo:=2572501) (a:=468) (b:=469) r2572501 r2572969) (join_sums term (lo:=2573438) (a:=469) (b:=469) r2573438 r2573907)) (join_sums term (lo:=2574376) (a:=937) (b:=938) (join_sums term (lo:=2574376) (a:=468) (b:=469) r2574376 r2574844) (join_sums term (lo:=2575313) (a:=469) (b:=469) r2575313 r2575782))) (join_sums term (lo:=2576251) (a:=1875) (b:=1875) (join_sums term (lo:=2576251) (a:=937) (b:=938) (join_sums term (lo:=2576251) (a:=468) (b:=469) r2576251 r2576719) (join_sums term (lo:=2577188) (a:=469) (b:=469) r2577188 r2577657)) (join_sums term (lo:=2578126) (a:=937) (b:=938) (join_sums term (lo:=2578126) (a:=468) (b:=469) r2578126 r2578594) (join_sums term (lo:=2579063) (a:=469) (b:=469) r2579063 r2579532)))))) (join_sums term (lo:=2580001) (a:=15000) (b:=15000) (join_sums term (lo:=2580001) (a:=7500) (b:=7500) (join_sums term (lo:=2580001) (a:=3750) (b:=3750) (join_sums term (lo:=2580001) (a:=1875) (b:=1875) (join_sums term (lo:=2580001) (a:=937) (b:=938) (join_sums term (lo:=2580001) (a:=468) (b:=469) r2580001 r2580469) (join_sums term (lo:=2580938) (a:=469) (b:=469) r2580938 r2581407)) (join_sums term (lo:=2581876) (a:=937) (b:=938) (join_sums term (lo:=2581876) (a:=468) (b:=469) r2581876 r2582344) (join_sums term (lo:=2582813) (a:=469) (b:=469) r2582813 r2583282))) (join_sums term (lo:=2583751) (a:=1875) (b:=1875) (join_sums term (lo:=2583751) (a:=937) (b:=938) (join_sums term (lo:=2583751) (a:=468) (b:=469) r2583751 r2584219) (join_sums term (lo:=2584688) (a:=469) (b:=469) r2584688 r2585157)) (join_sums term (lo:=2585626) (a:=937) (b:=938) (join_sums term (lo:=2585626) (a:=468) (b:=469) r2585626 r2586094) (join_sums term (lo:=2586563) (a:=469) (b:=469) r2586563 r2587032)))) (join_sums term (lo:=2587501) (a:=3750) (b:=3750) (join_sums term (lo:=2587501) (a:=1875) (b:=1875) (join_sums term (lo:=2587501) (a:=937) (b:=938) (join_sums term (lo:=2587501) (a:=468) (b:=469) r2587501 r2587969) (join_sums term (lo:=2588438) (a:=469) (b:=469) r2588438 r2588907)) (join_sums term (lo:=2589376) (a:=937) (b:=938) (join_sums term (lo:=2589376) (a:=468) (b:=469) r2589376 r2589844) (join_sums term (lo:=2590313) (a:=469) (b:=469) r2590313 r2590782))) (join_sums term (lo:=2591251) (a:=1875) (b:=1875) (join_sums term (lo:=2591251) (a:=937) (b:=938) (join_sums term (lo:=2591251) (a:=468) (b:=469) r2591251 r2591719) (join_sums term (lo:=2592188) (a:=469) (b:=469) r2592188 r2592657)) (join_sums term (lo:=2593126) (a:=937) (b:=938) (join_sums term (lo:=2593126) (a:=468) (b:=469) r2593126 r2593594) (join_sums term (lo:=2594063) (a:=469) (b:=469) r2594063 r2594532))))) (join_sums term (lo:=2595001) (a:=7500) (b:=7500) (join_sums term (lo:=2595001) (a:=3750) (b:=3750) (join_sums term (lo:=2595001) (a:=1875) (b:=1875) (join_sums term (lo:=2595001) (a:=937) (b:=938) (join_sums term (lo:=2595001) (a:=468) (b:=469) r2595001 r2595469) (join_sums term (lo:=2595938) (a:=469) (b:=469) r2595938 r2596407)) (join_sums term (lo:=2596876) (a:=937) (b:=938) (join_sums term (lo:=2596876) (a:=468) (b:=469) r2596876 r2597344) (join_sums term (lo:=2597813) (a:=469) (b:=469) r2597813 r2598282))) (join_sums term (lo:=2598751) (a:=1875) (b:=1875) (join_sums term (lo:=2598751) (a:=937) (b:=938) (join_sums term (lo:=2598751) (a:=468) (b:=469) r2598751 r2599219) (join_sums term (lo:=2599688) (a:=469) (b:=469) r2599688 r2600157)) (join_sums term (lo:=2600626) (a:=937) (b:=938) (join_sums term (lo:=2600626) (a:=468) (b:=469) r2600626 r2601094) (join_sums term (lo:=2601563) (a:=469) (b:=469) r2601563 r2602032)))) (join_sums term (lo:=2602501) (a:=3750) (b:=3750) (join_sums term (lo:=2602501) (a:=1875) (b:=1875) (join_sums term (lo:=2602501) (a:=937) (b:=938) (join_sums term (lo:=2602501) (a:=468) (b:=469) r2602501 r2602969) (join_sums term (lo:=2603438) (a:=469) (b:=469) r2603438 r2603907)) (join_sums term (lo:=2604376) (a:=937) (b:=938) (join_sums term (lo:=2604376) (a:=468) (b:=469) r2604376 r2604844) (join_sums term (lo:=2605313) (a:=469) (b:=469) r2605313 r2605782))) (join_sums term (lo:=2606251) (a:=1875) (b:=1875) (join_sums term (lo:=2606251) (a:=937) (b:=938) (join_sums term (lo:=2606251) (a:=468) (b:=469) r2606251 r2606719) (join_sums term (lo:=2607188) (a:=469) (b:=469) r2607188 r2607657)) (join_sums term (lo:=2608126) (a:=937) (b:=938) (join_sums term (lo:=2608126) (a:=468) (b:=469) r2608126 r2608594) (join_sums term (lo:=2609063) (a:=469) (b:=469) r2609063 r2609532))))))) (join_sums term (lo:=2610001) (a:=30000) (b:=30000) (join_sums term (lo:=2610001) (a:=15000) (b:=15000) (join_sums term (lo:=2610001) (a:=7500) (b:=7500) (join_sums term (lo:=2610001) (a:=3750) (b:=3750) (join_sums term (lo:=2610001) (a:=1875) (b:=1875) (join_sums term (lo:=2610001) (a:=937) (b:=938) (join_sums term (lo:=2610001) (a:=468) (b:=469) r2610001 r2610469) (join_sums term (lo:=2610938) (a:=469) (b:=469) r2610938 r2611407)) (join_sums term (lo:=2611876) (a:=937) (b:=938) (join_sums term (lo:=2611876) (a:=468) (b:=469) r2611876 r2612344) (join_sums term (lo:=2612813) (a:=469) (b:=469) r2612813 r2613282))) (join_sums term (lo:=2613751) (a:=1875) (b:=1875) (join_sums term (lo:=2613751) (a:=937) (b:=938) (join_sums term (lo:=2613751) (a:=468) (b:=469) r2613751 r2614219) (join_sums term (lo:=2614688) (a:=469) (b:=469) r2614688 r2615157)) (join_sums term (lo:=2615626) (a:=937) (b:=938) (join_sums term (lo:=2615626) (a:=468) (b:=469) r2615626 r2616094) (join_sums term (lo:=2616563) (a:=469) (b:=469) r2616563 r2617032)))) (join_sums term (lo:=2617501) (a:=3750) (b:=3750) (join_sums term (lo:=2617501) (a:=1875) (b:=1875) (join_sums term (lo:=2617501) (a:=937) (b:=938) (join_sums term (lo:=2617501) (a:=468) (b:=469) r2617501 r2617969) (join_sums term (lo:=2618438) (a:=469) (b:=469) r2618438 r2618907)) (join_sums term (lo:=2619376) (a:=937) (b:=938) (join_sums term (lo:=2619376) (a:=468) (b:=469) r2619376 r2619844) (join_sums term (lo:=2620313) (a:=469) (b:=469) r2620313 r2620782))) (join_sums term (lo:=2621251) (a:=1875) (b:=1875) (join_sums term (lo:=2621251) (a:=937) (b:=938) (join_sums term (lo:=2621251) (a:=468) (b:=469) r2621251 r2621719) (join_sums term (lo:=2622188) (a:=469) (b:=469) r2622188 r2622657)) (join_sums term (lo:=2623126) (a:=937) (b:=938) (join_sums term (lo:=2623126) (a:=468) (b:=469) r2623126 r2623594) (join_sums term (lo:=2624063) (a:=469) (b:=469) r2624063 r2624532))))) (join_sums term (lo:=2625001) (a:=7500) (b:=7500) (join_sums term (lo:=2625001) (a:=3750) (b:=3750) (join_sums term (lo:=2625001) (a:=1875) (b:=1875) (join_sums term (lo:=2625001) (a:=937) (b:=938) (join_sums term (lo:=2625001) (a:=468) (b:=469) r2625001 r2625469) (join_sums term (lo:=2625938) (a:=469) (b:=469) r2625938 r2626407)) (join_sums term (lo:=2626876) (a:=937) (b:=938) (join_sums term (lo:=2626876) (a:=468) (b:=469) r2626876 r2627344) (join_sums term (lo:=2627813) (a:=469) (b:=469) r2627813 r2628282))) (join_sums term (lo:=2628751) (a:=1875) (b:=1875) (join_sums term (lo:=2628751) (a:=937) (b:=938) (join_sums term (lo:=2628751) (a:=468) (b:=469) r2628751 r2629219) (join_sums term (lo:=2629688) (a:=469) (b:=469) r2629688 r2630157)) (join_sums term (lo:=2630626) (a:=937) (b:=938) (join_sums term (lo:=2630626) (a:=468) (b:=469) r2630626 r2631094) (join_sums term (lo:=2631563) (a:=469) (b:=469) r2631563 r2632032)))) (join_sums term (lo:=2632501) (a:=3750) (b:=3750) (join_sums term (lo:=2632501) (a:=1875) (b:=1875) (join_sums term (lo:=2632501) (a:=937) (b:=938) (join_sums term (lo:=2632501) (a:=468) (b:=469) r2632501 r2632969) (join_sums term (lo:=2633438) (a:=469) (b:=469) r2633438 r2633907)) (join_sums term (lo:=2634376) (a:=937) (b:=938) (join_sums term (lo:=2634376) (a:=468) (b:=469) r2634376 r2634844) (join_sums term (lo:=2635313) (a:=469) (b:=469) r2635313 r2635782))) (join_sums term (lo:=2636251) (a:=1875) (b:=1875) (join_sums term (lo:=2636251) (a:=937) (b:=938) (join_sums term (lo:=2636251) (a:=468) (b:=469) r2636251 r2636719) (join_sums term (lo:=2637188) (a:=469) (b:=469) r2637188 r2637657)) (join_sums term (lo:=2638126) (a:=937) (b:=938) (join_sums term (lo:=2638126) (a:=468) (b:=469) r2638126 r2638594) (join_sums term (lo:=2639063) (a:=469) (b:=469) r2639063 r2639532)))))) (join_sums term (lo:=2640001) (a:=15000) (b:=15000) (join_sums term (lo:=2640001) (a:=7500) (b:=7500) (join_sums term (lo:=2640001) (a:=3750) (b:=3750) (join_sums term (lo:=2640001) (a:=1875) (b:=1875) (join_sums term (lo:=2640001) (a:=937) (b:=938) (join_sums term (lo:=2640001) (a:=468) (b:=469) r2640001 r2640469) (join_sums term (lo:=2640938) (a:=469) (b:=469) r2640938 r2641407)) (join_sums term (lo:=2641876) (a:=937) (b:=938) (join_sums term (lo:=2641876) (a:=468) (b:=469) r2641876 r2642344) (join_sums term (lo:=2642813) (a:=469) (b:=469) r2642813 r2643282))) (join_sums term (lo:=2643751) (a:=1875) (b:=1875) (join_sums term (lo:=2643751) (a:=937) (b:=938) (join_sums term (lo:=2643751) (a:=468) (b:=469) r2643751 r2644219) (join_sums term (lo:=2644688) (a:=469) (b:=469) r2644688 r2645157)) (join_sums term (lo:=2645626) (a:=937) (b:=938) (join_sums term (lo:=2645626) (a:=468) (b:=469) r2645626 r2646094) (join_sums term (lo:=2646563) (a:=469) (b:=469) r2646563 r2647032)))) (join_sums term (lo:=2647501) (a:=3750) (b:=3750) (join_sums term (lo:=2647501) (a:=1875) (b:=1875) (join_sums term (lo:=2647501) (a:=937) (b:=938) (join_sums term (lo:=2647501) (a:=468) (b:=469) r2647501 r2647969) (join_sums term (lo:=2648438) (a:=469) (b:=469) r2648438 r2648907)) (join_sums term (lo:=2649376) (a:=937) (b:=938) (join_sums term (lo:=2649376) (a:=468) (b:=469) r2649376 r2649844) (join_sums term (lo:=2650313) (a:=469) (b:=469) r2650313 r2650782))) (join_sums term (lo:=2651251) (a:=1875) (b:=1875) (join_sums term (lo:=2651251) (a:=937) (b:=938) (join_sums term (lo:=2651251) (a:=468) (b:=469) r2651251 r2651719) (join_sums term (lo:=2652188) (a:=469) (b:=469) r2652188 r2652657)) (join_sums term (lo:=2653126) (a:=937) (b:=938) (join_sums term (lo:=2653126) (a:=468) (b:=469) r2653126 r2653594) (join_sums term (lo:=2654063) (a:=469) (b:=469) r2654063 r2654532))))) (join_sums term (lo:=2655001) (a:=7500) (b:=7500) (join_sums term (lo:=2655001) (a:=3750) (b:=3750) (join_sums term (lo:=2655001) (a:=1875) (b:=1875) (join_sums term (lo:=2655001) (a:=937) (b:=938) (join_sums term (lo:=2655001) (a:=468) (b:=469) r2655001 r2655469) (join_sums term (lo:=2655938) (a:=469) (b:=469) r2655938 r2656407)) (join_sums term (lo:=2656876) (a:=937) (b:=938) (join_sums term (lo:=2656876) (a:=468) (b:=469) r2656876 r2657344) (join_sums term (lo:=2657813) (a:=469) (b:=469) r2657813 r2658282))) (join_sums term (lo:=2658751) (a:=1875) (b:=1875) (join_sums term (lo:=2658751) (a:=937) (b:=938) (join_sums term (lo:=2658751) (a:=468) (b:=469) r2658751 r2659219) (join_sums term (lo:=2659688) (a:=469) (b:=469) r2659688 r2660157)) (join_sums term (lo:=2660626) (a:=937) (b:=938) (join_sums term (lo:=2660626) (a:=468) (b:=469) r2660626 r2661094) (join_sums term (lo:=2661563) (a:=469) (b:=469) r2661563 r2662032)))) (join_sums term (lo:=2662501) (a:=3750) (b:=3750) (join_sums term (lo:=2662501) (a:=1875) (b:=1875) (join_sums term (lo:=2662501) (a:=937) (b:=938) (join_sums term (lo:=2662501) (a:=468) (b:=469) r2662501 r2662969) (join_sums term (lo:=2663438) (a:=469) (b:=469) r2663438 r2663907)) (join_sums term (lo:=2664376) (a:=937) (b:=938) (join_sums term (lo:=2664376) (a:=468) (b:=469) r2664376 r2664844) (join_sums term (lo:=2665313) (a:=469) (b:=469) r2665313 r2665782))) (join_sums term (lo:=2666251) (a:=1875) (b:=1875) (join_sums term (lo:=2666251) (a:=937) (b:=938) (join_sums term (lo:=2666251) (a:=468) (b:=469) r2666251 r2666719) (join_sums term (lo:=2667188) (a:=469) (b:=469) r2667188 r2667657)) (join_sums term (lo:=2668126) (a:=937) (b:=938) (join_sums term (lo:=2668126) (a:=468) (b:=469) r2668126 r2668594) (join_sums term (lo:=2669063) (a:=469) (b:=469) r2669063 r2669532))))))))

private theorem rows : blockSum term 0 2670001 4639168756 :=
  join_sums term (lo:=0) (a:=2550001) (b:=120000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 2670000).filter (2550000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4639168756 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From2550000To2670000
