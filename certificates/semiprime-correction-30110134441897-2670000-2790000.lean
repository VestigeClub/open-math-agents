import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 2,670,000 through 2,790,000

The sum covers 8,065 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From2670000To2790000

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


private abbrev term := contribution 30110134441897 2670000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 2670001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 2670000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r2670001 : blockSum term 2670001 468 13173909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2670469 : blockSum term 2670469 469 14816684 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2670938 : blockSum term 2670938 469 16458301 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2671407 : blockSum term 2671407 469 17550869 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2671876 : blockSum term 2671876 468 16998141 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2672344 : blockSum term 2672344 469 16445490 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2672813 : blockSum term 2672813 469 16440505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2673282 : blockSum term 2673282 469 17531977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2673751 : blockSum term 2673751 468 15883963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2674219 : blockSum term 2674219 469 20260070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2674688 : blockSum term 2674688 469 19159095 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2675157 : blockSum term 2675157 469 15870749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2675626 : blockSum term 2675626 468 18601836 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2676094 : blockSum term 2676094 469 19142968 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2676563 : blockSum term 2676563 469 16403776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2677032 : blockSum term 2677032 469 15306015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2677501 : blockSum term 2677501 468 16941069 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2677969 : blockSum term 2677969 469 16936173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2678438 : blockSum term 2678438 469 15839092 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2678907 : blockSum term 2678907 469 17472396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2679376 : blockSum term 2679376 468 20743116 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2679844 : blockSum term 2679844 469 16371572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2680313 : blockSum term 2680313 469 17457831 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2680782 : blockSum term 2680782 469 18543807 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2681251 : blockSum term 2681251 468 15812561 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2681719 : blockSum term 2681719 469 17443597 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2682188 : blockSum term 2682188 469 17438785 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2682657 : blockSum term 2682657 469 15254619 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2683126 : blockSum term 2683126 468 17973940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2683594 : blockSum term 2683594 469 17968851 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2684063 : blockSum term 2684063 469 17419378 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2684532 : blockSum term 2684532 469 17958359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2685001 : blockSum term 2685001 468 17409876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2685469 : blockSum term 2685469 469 17948916 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2685938 : blockSum term 2685938 469 16312496 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2686407 : blockSum term 2686407 469 15220814 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2686876 : blockSum term 2686876 468 20107990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2687344 : blockSum term 2687344 469 17385654 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2687813 : blockSum term 2687813 469 15751534 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2688282 : blockSum term 2688282 469 15203922 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2688751 : blockSum term 2688751 468 20085450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2689219 : blockSum term 2689219 469 20622110 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2689688 : blockSum term 2689688 469 18988459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2690157 : blockSum term 2690157 469 17356259 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2690626 : blockSum term 2690626 468 16266644 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2691094 : blockSum term 2691094 469 16804673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2691563 : blockSum term 2691563 469 15716405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2692032 : blockSum term 2692032 469 15711834 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2692501 : blockSum term 2692501 468 18415365 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2692969 : blockSum term 2692969 469 19492852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2693438 : blockSum term 2693438 469 15698225 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2693907 : blockSum term 2693907 469 18940706 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2694376 : blockSum term 2694376 468 18394040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2694844 : blockSum term 2694844 469 16766202 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2695313 : blockSum term 2695313 469 15139389 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2695782 : blockSum term 2695782 469 19459497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2696251 : blockSum term 2696251 468 18372987 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2696719 : blockSum term 2696719 469 14586161 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2697188 : blockSum term 2697188 469 16742546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2697657 : blockSum term 2697657 469 21596737 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2698126 : blockSum term 2698126 468 16193055 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2698594 : blockSum term 2698594 469 17268003 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2699063 : blockSum term 2699063 469 17262564 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2699532 : blockSum term 2699532 469 16718824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2700001 : blockSum term 2700001 468 18331499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2700469 : blockSum term 2700469 469 18326402 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2700938 : blockSum term 2700938 469 14548642 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2701407 : blockSum term 2701407 469 15622498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2701876 : blockSum term 2701876 468 19387768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2702344 : blockSum term 2702344 469 13997924 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2702813 : blockSum term 2702813 469 13994525 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2703282 : blockSum term 2703282 469 17219104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2703751 : blockSum term 2703751 468 17214469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2704219 : blockSum term 2704219 469 13983025 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2704688 : blockSum term 2704688 469 26882714 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2705157 : blockSum term 2705157 469 15049745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2705626 : blockSum term 2705626 468 18269676 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2706094 : blockSum term 2706094 469 15579144 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2706563 : blockSum term 2706563 469 16112182 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2707032 : blockSum term 2707032 469 19329439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2707501 : blockSum term 2707501 468 17177068 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2707969 : blockSum term 2707969 469 16098687 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2708438 : blockSum term 2708438 469 21995741 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2708907 : blockSum term 2708907 469 15017058 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2709376 : blockSum term 2709376 468 17157438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2709844 : blockSum term 2709844 469 15008861 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2710313 : blockSum term 2710313 469 16076246 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2710782 : blockSum term 2710782 469 17678960 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2711251 : blockSum term 2711251 468 14995965 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2711719 : blockSum term 2711719 469 18204365 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2712188 : blockSum term 2712188 469 19269772 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2712657 : blockSum term 2712657 469 15518488 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2713126 : blockSum term 2713126 468 17654152 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2713594 : blockSum term 2713594 469 18183536 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2714063 : blockSum term 2714063 469 14436202 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2714532 : blockSum term 2714532 469 18173557 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2715001 : blockSum term 2715001 468 16564662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2715469 : blockSum term 2715469 469 18697316 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2715938 : blockSum term 2715938 469 15487566 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2716407 : blockSum term 2716407 469 17618942 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2716876 : blockSum term 2716876 468 19215190 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2717344 : blockSum term 2717344 469 16542005 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2717813 : blockSum term 2717813 469 19737424 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2718282 : blockSum term 2718282 469 17598918 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2718751 : blockSum term 2718751 468 21325526 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2719219 : blockSum term 2719219 469 19186961 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2719688 : blockSum term 2719688 469 11722395 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2720157 : blockSum term 2720157 469 15980739 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2720626 : blockSum term 2720626 468 15443822 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2721094 : blockSum term 2721094 469 17036900 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2721563 : blockSum term 2721563 469 12773926 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2722032 : blockSum term 2722032 469 15963212 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2722501 : blockSum term 2722501 468 15958349 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2722969 : blockSum term 2722969 469 19144591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2723438 : blockSum term 2723438 469 18075796 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2723907 : blockSum term 2723907 469 17539414 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2724376 : blockSum term 2724376 468 15408765 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2724844 : blockSum term 2724844 469 12748622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2725313 : blockSum term 2725313 469 15400595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2725782 : blockSum term 2725782 469 16988842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2726251 : blockSum term 2726251 468 13799697 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2726719 : blockSum term 2726719 469 18040376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2727188 : blockSum term 2727188 469 13792135 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2727657 : blockSum term 2727657 469 15378838 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2728126 : blockSum term 2728126 468 16434896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2728594 : blockSum term 2728594 469 17490477 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2729063 : blockSum term 2729063 469 19605176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2729532 : blockSum term 2729532 469 15891540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2730001 : blockSum term 2730001 468 12180333 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2730469 : blockSum term 2730469 469 19059430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2730938 : blockSum term 2730938 469 17995477 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2731407 : blockSum term 2731407 469 17990035 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2731876 : blockSum term 2731876 468 17985010 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2732344 : blockSum term 2732344 469 16393562 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2732813 : blockSum term 2732813 469 16917601 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2733282 : blockSum term 2733282 469 14798880 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2733751 : blockSum term 2733751 468 16908495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2734219 : blockSum term 2734219 469 16375708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2734688 : blockSum term 2734688 469 12146257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2735157 : blockSum term 2735157 469 16367241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2735626 : blockSum term 2735626 468 15307023 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2736094 : blockSum term 2736094 469 15302992 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2736563 : blockSum term 2736563 469 13715977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2737032 : blockSum term 2737032 469 17403999 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2737501 : blockSum term 2737501 468 13181100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2737969 : blockSum term 2737969 469 21084051 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2738438 : blockSum term 2738438 469 14754630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2738907 : blockSum term 2738907 469 16330716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2739376 : blockSum term 2739376 468 19485910 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2739844 : blockSum term 2739844 469 16848048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2740313 : blockSum term 2740313 469 17370101 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2740782 : blockSum term 2740782 469 15260325 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2741251 : blockSum term 2741251 468 17886277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2741719 : blockSum term 2741719 469 17881106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2742188 : blockSum term 2742188 469 18927396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2742657 : blockSum term 2742657 469 21024637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2743126 : blockSum term 2743126 468 14712412 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2743594 : blockSum term 2743594 469 14708461 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2744063 : blockSum term 2744063 469 16805261 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2744532 : blockSum term 2744532 469 15751338 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2745001 : blockSum term 2745001 468 16271513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2745469 : blockSum term 2745469 469 15742197 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2745938 : blockSum term 2745938 469 14164327 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2746407 : blockSum term 2746407 469 17831443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2746876 : blockSum term 2746876 468 17301533 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2747344 : blockSum term 2747344 469 19393594 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2747813 : blockSum term 2747813 469 16767891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2748282 : blockSum term 2748282 469 14667854 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2748751 : blockSum term 2748751 468 14663782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2749219 : blockSum term 2749219 469 15183638 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2749688 : blockSum term 2749688 469 12039104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2750157 : blockSum term 2750157 469 18315031 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2750626 : blockSum term 2750626 468 16740442 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2751094 : blockSum term 2751094 469 17781260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2751563 : blockSum term 2751563 469 17253167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2752032 : blockSum term 2752032 469 17771138 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2752501 : blockSum term 2752501 468 16720877 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2752969 : blockSum term 2752969 469 14104243 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2753438 : blockSum term 2753438 469 15144906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2753907 : blockSum term 2753907 469 14618725 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2754376 : blockSum term 2754376 468 14093090 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2754844 : blockSum term 2754844 469 20872233 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2755313 : blockSum term 2755313 469 12519788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2755782 : blockSum term 2755782 469 17209725 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2756251 : blockSum term 2756251 468 19289875 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2756719 : blockSum term 2756719 469 16157265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2757188 : blockSum term 2757188 469 16152842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2757657 : blockSum term 2757657 469 15627189 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2758126 : blockSum term 2758126 468 17185069 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2758594 : blockSum term 2758594 469 14056599 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2759063 : blockSum term 2759063 469 20819151 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2759532 : blockSum term 2759532 469 14569058 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2760001 : blockSum term 2760001 468 16125930 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2760469 : blockSum term 2760469 469 17161631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2760938 : blockSum term 2760938 469 18716656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2761407 : blockSum term 2761407 469 17151771 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2761876 : blockSum term 2761876 468 18705308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2762344 : blockSum term 2762344 469 16622281 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2762813 : blockSum term 2762813 469 15578872 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2763282 : blockSum term 2763282 469 17131785 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2763751 : blockSum term 2763751 468 18683764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2764219 : blockSum term 2764219 469 12971077 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2764688 : blockSum term 2764688 469 14005186 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2765157 : blockSum term 2765157 469 19187104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2765626 : blockSum term 2765626 468 15552321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2766094 : blockSum term 2766094 469 15029984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2766563 : blockSum term 2766563 469 18652599 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2767032 : blockSum term 2767032 469 17093516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2767501 : blockSum term 2767501 468 16571017 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2767969 : blockSum term 2767969 469 17601542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2768438 : blockSum term 2768438 469 16561759 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2768907 : blockSum term 2768907 469 17074649 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2769376 : blockSum term 2769376 468 15001229 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2769844 : blockSum term 2769844 469 12411082 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2770313 : blockSum term 2770313 469 13958618 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2770782 : blockSum term 2770782 469 20156937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2771251 : blockSum term 2771251 468 16017529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2771719 : blockSum term 2771719 469 18595861 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2772188 : blockSum term 2772188 469 15491997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2772657 : blockSum term 2772657 469 16003232 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2773126 : blockSum term 2773126 468 15483399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2773594 : blockSum term 2773594 469 15995092 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2774063 : blockSum term 2774063 469 17022289 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2774532 : blockSum term 2774532 469 17533185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2775001 : blockSum term 2775001 468 15981517 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2775469 : blockSum term 2775469 469 16492367 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2775938 : blockSum term 2775938 469 12881253 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2776407 : blockSum term 2776407 469 15452860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2776876 : blockSum term 2776876 468 18023208 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2777344 : blockSum term 2777344 469 15958879 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2777813 : blockSum term 2777813 469 18527023 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2778282 : blockSum term 2778282 469 12862614 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2778751 : blockSum term 2778751 468 14916545 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2779219 : blockSum term 2779219 469 16454591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2779688 : blockSum term 2779688 469 16963936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2780157 : blockSum term 2780157 469 14389945 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2780626 : blockSum term 2780626 468 17468568 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2781094 : blockSum term 2781094 469 16436370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2781563 : blockSum term 2781563 469 14377654 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2782032 : blockSum term 2782032 469 16940953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2782501 : blockSum term 2782501 468 14369942 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2782969 : blockSum term 2782969 469 16931723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2783438 : blockSum term 2783438 469 15901197 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2783907 : blockSum term 2783907 469 21536879 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2784376 : blockSum term 2784376 468 13841363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2784844 : blockSum term 2784844 469 17937548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2785313 : blockSum term 2785313 469 17419602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2785782 : blockSum term 2785782 469 14341688 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2786251 : blockSum term 2786251 468 18434019 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2786719 : blockSum term 2786719 469 15357234 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2787188 : blockSum term 2787188 469 19447046 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2787657 : blockSum term 2787657 469 11767271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2788126 : blockSum term 2788126 468 14832612 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2788594 : blockSum term 2788594 469 11760940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2789063 : blockSum term 2789063 469 17380956 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2789532 : blockSum term 2789532 469 13287674 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 2670001 120000 4273061665 := (join_sums term (lo:=2670001) (a:=60000) (b:=60000) (join_sums term (lo:=2670001) (a:=30000) (b:=30000) (join_sums term (lo:=2670001) (a:=15000) (b:=15000) (join_sums term (lo:=2670001) (a:=7500) (b:=7500) (join_sums term (lo:=2670001) (a:=3750) (b:=3750) (join_sums term (lo:=2670001) (a:=1875) (b:=1875) (join_sums term (lo:=2670001) (a:=937) (b:=938) (join_sums term (lo:=2670001) (a:=468) (b:=469) r2670001 r2670469) (join_sums term (lo:=2670938) (a:=469) (b:=469) r2670938 r2671407)) (join_sums term (lo:=2671876) (a:=937) (b:=938) (join_sums term (lo:=2671876) (a:=468) (b:=469) r2671876 r2672344) (join_sums term (lo:=2672813) (a:=469) (b:=469) r2672813 r2673282))) (join_sums term (lo:=2673751) (a:=1875) (b:=1875) (join_sums term (lo:=2673751) (a:=937) (b:=938) (join_sums term (lo:=2673751) (a:=468) (b:=469) r2673751 r2674219) (join_sums term (lo:=2674688) (a:=469) (b:=469) r2674688 r2675157)) (join_sums term (lo:=2675626) (a:=937) (b:=938) (join_sums term (lo:=2675626) (a:=468) (b:=469) r2675626 r2676094) (join_sums term (lo:=2676563) (a:=469) (b:=469) r2676563 r2677032)))) (join_sums term (lo:=2677501) (a:=3750) (b:=3750) (join_sums term (lo:=2677501) (a:=1875) (b:=1875) (join_sums term (lo:=2677501) (a:=937) (b:=938) (join_sums term (lo:=2677501) (a:=468) (b:=469) r2677501 r2677969) (join_sums term (lo:=2678438) (a:=469) (b:=469) r2678438 r2678907)) (join_sums term (lo:=2679376) (a:=937) (b:=938) (join_sums term (lo:=2679376) (a:=468) (b:=469) r2679376 r2679844) (join_sums term (lo:=2680313) (a:=469) (b:=469) r2680313 r2680782))) (join_sums term (lo:=2681251) (a:=1875) (b:=1875) (join_sums term (lo:=2681251) (a:=937) (b:=938) (join_sums term (lo:=2681251) (a:=468) (b:=469) r2681251 r2681719) (join_sums term (lo:=2682188) (a:=469) (b:=469) r2682188 r2682657)) (join_sums term (lo:=2683126) (a:=937) (b:=938) (join_sums term (lo:=2683126) (a:=468) (b:=469) r2683126 r2683594) (join_sums term (lo:=2684063) (a:=469) (b:=469) r2684063 r2684532))))) (join_sums term (lo:=2685001) (a:=7500) (b:=7500) (join_sums term (lo:=2685001) (a:=3750) (b:=3750) (join_sums term (lo:=2685001) (a:=1875) (b:=1875) (join_sums term (lo:=2685001) (a:=937) (b:=938) (join_sums term (lo:=2685001) (a:=468) (b:=469) r2685001 r2685469) (join_sums term (lo:=2685938) (a:=469) (b:=469) r2685938 r2686407)) (join_sums term (lo:=2686876) (a:=937) (b:=938) (join_sums term (lo:=2686876) (a:=468) (b:=469) r2686876 r2687344) (join_sums term (lo:=2687813) (a:=469) (b:=469) r2687813 r2688282))) (join_sums term (lo:=2688751) (a:=1875) (b:=1875) (join_sums term (lo:=2688751) (a:=937) (b:=938) (join_sums term (lo:=2688751) (a:=468) (b:=469) r2688751 r2689219) (join_sums term (lo:=2689688) (a:=469) (b:=469) r2689688 r2690157)) (join_sums term (lo:=2690626) (a:=937) (b:=938) (join_sums term (lo:=2690626) (a:=468) (b:=469) r2690626 r2691094) (join_sums term (lo:=2691563) (a:=469) (b:=469) r2691563 r2692032)))) (join_sums term (lo:=2692501) (a:=3750) (b:=3750) (join_sums term (lo:=2692501) (a:=1875) (b:=1875) (join_sums term (lo:=2692501) (a:=937) (b:=938) (join_sums term (lo:=2692501) (a:=468) (b:=469) r2692501 r2692969) (join_sums term (lo:=2693438) (a:=469) (b:=469) r2693438 r2693907)) (join_sums term (lo:=2694376) (a:=937) (b:=938) (join_sums term (lo:=2694376) (a:=468) (b:=469) r2694376 r2694844) (join_sums term (lo:=2695313) (a:=469) (b:=469) r2695313 r2695782))) (join_sums term (lo:=2696251) (a:=1875) (b:=1875) (join_sums term (lo:=2696251) (a:=937) (b:=938) (join_sums term (lo:=2696251) (a:=468) (b:=469) r2696251 r2696719) (join_sums term (lo:=2697188) (a:=469) (b:=469) r2697188 r2697657)) (join_sums term (lo:=2698126) (a:=937) (b:=938) (join_sums term (lo:=2698126) (a:=468) (b:=469) r2698126 r2698594) (join_sums term (lo:=2699063) (a:=469) (b:=469) r2699063 r2699532)))))) (join_sums term (lo:=2700001) (a:=15000) (b:=15000) (join_sums term (lo:=2700001) (a:=7500) (b:=7500) (join_sums term (lo:=2700001) (a:=3750) (b:=3750) (join_sums term (lo:=2700001) (a:=1875) (b:=1875) (join_sums term (lo:=2700001) (a:=937) (b:=938) (join_sums term (lo:=2700001) (a:=468) (b:=469) r2700001 r2700469) (join_sums term (lo:=2700938) (a:=469) (b:=469) r2700938 r2701407)) (join_sums term (lo:=2701876) (a:=937) (b:=938) (join_sums term (lo:=2701876) (a:=468) (b:=469) r2701876 r2702344) (join_sums term (lo:=2702813) (a:=469) (b:=469) r2702813 r2703282))) (join_sums term (lo:=2703751) (a:=1875) (b:=1875) (join_sums term (lo:=2703751) (a:=937) (b:=938) (join_sums term (lo:=2703751) (a:=468) (b:=469) r2703751 r2704219) (join_sums term (lo:=2704688) (a:=469) (b:=469) r2704688 r2705157)) (join_sums term (lo:=2705626) (a:=937) (b:=938) (join_sums term (lo:=2705626) (a:=468) (b:=469) r2705626 r2706094) (join_sums term (lo:=2706563) (a:=469) (b:=469) r2706563 r2707032)))) (join_sums term (lo:=2707501) (a:=3750) (b:=3750) (join_sums term (lo:=2707501) (a:=1875) (b:=1875) (join_sums term (lo:=2707501) (a:=937) (b:=938) (join_sums term (lo:=2707501) (a:=468) (b:=469) r2707501 r2707969) (join_sums term (lo:=2708438) (a:=469) (b:=469) r2708438 r2708907)) (join_sums term (lo:=2709376) (a:=937) (b:=938) (join_sums term (lo:=2709376) (a:=468) (b:=469) r2709376 r2709844) (join_sums term (lo:=2710313) (a:=469) (b:=469) r2710313 r2710782))) (join_sums term (lo:=2711251) (a:=1875) (b:=1875) (join_sums term (lo:=2711251) (a:=937) (b:=938) (join_sums term (lo:=2711251) (a:=468) (b:=469) r2711251 r2711719) (join_sums term (lo:=2712188) (a:=469) (b:=469) r2712188 r2712657)) (join_sums term (lo:=2713126) (a:=937) (b:=938) (join_sums term (lo:=2713126) (a:=468) (b:=469) r2713126 r2713594) (join_sums term (lo:=2714063) (a:=469) (b:=469) r2714063 r2714532))))) (join_sums term (lo:=2715001) (a:=7500) (b:=7500) (join_sums term (lo:=2715001) (a:=3750) (b:=3750) (join_sums term (lo:=2715001) (a:=1875) (b:=1875) (join_sums term (lo:=2715001) (a:=937) (b:=938) (join_sums term (lo:=2715001) (a:=468) (b:=469) r2715001 r2715469) (join_sums term (lo:=2715938) (a:=469) (b:=469) r2715938 r2716407)) (join_sums term (lo:=2716876) (a:=937) (b:=938) (join_sums term (lo:=2716876) (a:=468) (b:=469) r2716876 r2717344) (join_sums term (lo:=2717813) (a:=469) (b:=469) r2717813 r2718282))) (join_sums term (lo:=2718751) (a:=1875) (b:=1875) (join_sums term (lo:=2718751) (a:=937) (b:=938) (join_sums term (lo:=2718751) (a:=468) (b:=469) r2718751 r2719219) (join_sums term (lo:=2719688) (a:=469) (b:=469) r2719688 r2720157)) (join_sums term (lo:=2720626) (a:=937) (b:=938) (join_sums term (lo:=2720626) (a:=468) (b:=469) r2720626 r2721094) (join_sums term (lo:=2721563) (a:=469) (b:=469) r2721563 r2722032)))) (join_sums term (lo:=2722501) (a:=3750) (b:=3750) (join_sums term (lo:=2722501) (a:=1875) (b:=1875) (join_sums term (lo:=2722501) (a:=937) (b:=938) (join_sums term (lo:=2722501) (a:=468) (b:=469) r2722501 r2722969) (join_sums term (lo:=2723438) (a:=469) (b:=469) r2723438 r2723907)) (join_sums term (lo:=2724376) (a:=937) (b:=938) (join_sums term (lo:=2724376) (a:=468) (b:=469) r2724376 r2724844) (join_sums term (lo:=2725313) (a:=469) (b:=469) r2725313 r2725782))) (join_sums term (lo:=2726251) (a:=1875) (b:=1875) (join_sums term (lo:=2726251) (a:=937) (b:=938) (join_sums term (lo:=2726251) (a:=468) (b:=469) r2726251 r2726719) (join_sums term (lo:=2727188) (a:=469) (b:=469) r2727188 r2727657)) (join_sums term (lo:=2728126) (a:=937) (b:=938) (join_sums term (lo:=2728126) (a:=468) (b:=469) r2728126 r2728594) (join_sums term (lo:=2729063) (a:=469) (b:=469) r2729063 r2729532))))))) (join_sums term (lo:=2730001) (a:=30000) (b:=30000) (join_sums term (lo:=2730001) (a:=15000) (b:=15000) (join_sums term (lo:=2730001) (a:=7500) (b:=7500) (join_sums term (lo:=2730001) (a:=3750) (b:=3750) (join_sums term (lo:=2730001) (a:=1875) (b:=1875) (join_sums term (lo:=2730001) (a:=937) (b:=938) (join_sums term (lo:=2730001) (a:=468) (b:=469) r2730001 r2730469) (join_sums term (lo:=2730938) (a:=469) (b:=469) r2730938 r2731407)) (join_sums term (lo:=2731876) (a:=937) (b:=938) (join_sums term (lo:=2731876) (a:=468) (b:=469) r2731876 r2732344) (join_sums term (lo:=2732813) (a:=469) (b:=469) r2732813 r2733282))) (join_sums term (lo:=2733751) (a:=1875) (b:=1875) (join_sums term (lo:=2733751) (a:=937) (b:=938) (join_sums term (lo:=2733751) (a:=468) (b:=469) r2733751 r2734219) (join_sums term (lo:=2734688) (a:=469) (b:=469) r2734688 r2735157)) (join_sums term (lo:=2735626) (a:=937) (b:=938) (join_sums term (lo:=2735626) (a:=468) (b:=469) r2735626 r2736094) (join_sums term (lo:=2736563) (a:=469) (b:=469) r2736563 r2737032)))) (join_sums term (lo:=2737501) (a:=3750) (b:=3750) (join_sums term (lo:=2737501) (a:=1875) (b:=1875) (join_sums term (lo:=2737501) (a:=937) (b:=938) (join_sums term (lo:=2737501) (a:=468) (b:=469) r2737501 r2737969) (join_sums term (lo:=2738438) (a:=469) (b:=469) r2738438 r2738907)) (join_sums term (lo:=2739376) (a:=937) (b:=938) (join_sums term (lo:=2739376) (a:=468) (b:=469) r2739376 r2739844) (join_sums term (lo:=2740313) (a:=469) (b:=469) r2740313 r2740782))) (join_sums term (lo:=2741251) (a:=1875) (b:=1875) (join_sums term (lo:=2741251) (a:=937) (b:=938) (join_sums term (lo:=2741251) (a:=468) (b:=469) r2741251 r2741719) (join_sums term (lo:=2742188) (a:=469) (b:=469) r2742188 r2742657)) (join_sums term (lo:=2743126) (a:=937) (b:=938) (join_sums term (lo:=2743126) (a:=468) (b:=469) r2743126 r2743594) (join_sums term (lo:=2744063) (a:=469) (b:=469) r2744063 r2744532))))) (join_sums term (lo:=2745001) (a:=7500) (b:=7500) (join_sums term (lo:=2745001) (a:=3750) (b:=3750) (join_sums term (lo:=2745001) (a:=1875) (b:=1875) (join_sums term (lo:=2745001) (a:=937) (b:=938) (join_sums term (lo:=2745001) (a:=468) (b:=469) r2745001 r2745469) (join_sums term (lo:=2745938) (a:=469) (b:=469) r2745938 r2746407)) (join_sums term (lo:=2746876) (a:=937) (b:=938) (join_sums term (lo:=2746876) (a:=468) (b:=469) r2746876 r2747344) (join_sums term (lo:=2747813) (a:=469) (b:=469) r2747813 r2748282))) (join_sums term (lo:=2748751) (a:=1875) (b:=1875) (join_sums term (lo:=2748751) (a:=937) (b:=938) (join_sums term (lo:=2748751) (a:=468) (b:=469) r2748751 r2749219) (join_sums term (lo:=2749688) (a:=469) (b:=469) r2749688 r2750157)) (join_sums term (lo:=2750626) (a:=937) (b:=938) (join_sums term (lo:=2750626) (a:=468) (b:=469) r2750626 r2751094) (join_sums term (lo:=2751563) (a:=469) (b:=469) r2751563 r2752032)))) (join_sums term (lo:=2752501) (a:=3750) (b:=3750) (join_sums term (lo:=2752501) (a:=1875) (b:=1875) (join_sums term (lo:=2752501) (a:=937) (b:=938) (join_sums term (lo:=2752501) (a:=468) (b:=469) r2752501 r2752969) (join_sums term (lo:=2753438) (a:=469) (b:=469) r2753438 r2753907)) (join_sums term (lo:=2754376) (a:=937) (b:=938) (join_sums term (lo:=2754376) (a:=468) (b:=469) r2754376 r2754844) (join_sums term (lo:=2755313) (a:=469) (b:=469) r2755313 r2755782))) (join_sums term (lo:=2756251) (a:=1875) (b:=1875) (join_sums term (lo:=2756251) (a:=937) (b:=938) (join_sums term (lo:=2756251) (a:=468) (b:=469) r2756251 r2756719) (join_sums term (lo:=2757188) (a:=469) (b:=469) r2757188 r2757657)) (join_sums term (lo:=2758126) (a:=937) (b:=938) (join_sums term (lo:=2758126) (a:=468) (b:=469) r2758126 r2758594) (join_sums term (lo:=2759063) (a:=469) (b:=469) r2759063 r2759532)))))) (join_sums term (lo:=2760001) (a:=15000) (b:=15000) (join_sums term (lo:=2760001) (a:=7500) (b:=7500) (join_sums term (lo:=2760001) (a:=3750) (b:=3750) (join_sums term (lo:=2760001) (a:=1875) (b:=1875) (join_sums term (lo:=2760001) (a:=937) (b:=938) (join_sums term (lo:=2760001) (a:=468) (b:=469) r2760001 r2760469) (join_sums term (lo:=2760938) (a:=469) (b:=469) r2760938 r2761407)) (join_sums term (lo:=2761876) (a:=937) (b:=938) (join_sums term (lo:=2761876) (a:=468) (b:=469) r2761876 r2762344) (join_sums term (lo:=2762813) (a:=469) (b:=469) r2762813 r2763282))) (join_sums term (lo:=2763751) (a:=1875) (b:=1875) (join_sums term (lo:=2763751) (a:=937) (b:=938) (join_sums term (lo:=2763751) (a:=468) (b:=469) r2763751 r2764219) (join_sums term (lo:=2764688) (a:=469) (b:=469) r2764688 r2765157)) (join_sums term (lo:=2765626) (a:=937) (b:=938) (join_sums term (lo:=2765626) (a:=468) (b:=469) r2765626 r2766094) (join_sums term (lo:=2766563) (a:=469) (b:=469) r2766563 r2767032)))) (join_sums term (lo:=2767501) (a:=3750) (b:=3750) (join_sums term (lo:=2767501) (a:=1875) (b:=1875) (join_sums term (lo:=2767501) (a:=937) (b:=938) (join_sums term (lo:=2767501) (a:=468) (b:=469) r2767501 r2767969) (join_sums term (lo:=2768438) (a:=469) (b:=469) r2768438 r2768907)) (join_sums term (lo:=2769376) (a:=937) (b:=938) (join_sums term (lo:=2769376) (a:=468) (b:=469) r2769376 r2769844) (join_sums term (lo:=2770313) (a:=469) (b:=469) r2770313 r2770782))) (join_sums term (lo:=2771251) (a:=1875) (b:=1875) (join_sums term (lo:=2771251) (a:=937) (b:=938) (join_sums term (lo:=2771251) (a:=468) (b:=469) r2771251 r2771719) (join_sums term (lo:=2772188) (a:=469) (b:=469) r2772188 r2772657)) (join_sums term (lo:=2773126) (a:=937) (b:=938) (join_sums term (lo:=2773126) (a:=468) (b:=469) r2773126 r2773594) (join_sums term (lo:=2774063) (a:=469) (b:=469) r2774063 r2774532))))) (join_sums term (lo:=2775001) (a:=7500) (b:=7500) (join_sums term (lo:=2775001) (a:=3750) (b:=3750) (join_sums term (lo:=2775001) (a:=1875) (b:=1875) (join_sums term (lo:=2775001) (a:=937) (b:=938) (join_sums term (lo:=2775001) (a:=468) (b:=469) r2775001 r2775469) (join_sums term (lo:=2775938) (a:=469) (b:=469) r2775938 r2776407)) (join_sums term (lo:=2776876) (a:=937) (b:=938) (join_sums term (lo:=2776876) (a:=468) (b:=469) r2776876 r2777344) (join_sums term (lo:=2777813) (a:=469) (b:=469) r2777813 r2778282))) (join_sums term (lo:=2778751) (a:=1875) (b:=1875) (join_sums term (lo:=2778751) (a:=937) (b:=938) (join_sums term (lo:=2778751) (a:=468) (b:=469) r2778751 r2779219) (join_sums term (lo:=2779688) (a:=469) (b:=469) r2779688 r2780157)) (join_sums term (lo:=2780626) (a:=937) (b:=938) (join_sums term (lo:=2780626) (a:=468) (b:=469) r2780626 r2781094) (join_sums term (lo:=2781563) (a:=469) (b:=469) r2781563 r2782032)))) (join_sums term (lo:=2782501) (a:=3750) (b:=3750) (join_sums term (lo:=2782501) (a:=1875) (b:=1875) (join_sums term (lo:=2782501) (a:=937) (b:=938) (join_sums term (lo:=2782501) (a:=468) (b:=469) r2782501 r2782969) (join_sums term (lo:=2783438) (a:=469) (b:=469) r2783438 r2783907)) (join_sums term (lo:=2784376) (a:=937) (b:=938) (join_sums term (lo:=2784376) (a:=468) (b:=469) r2784376 r2784844) (join_sums term (lo:=2785313) (a:=469) (b:=469) r2785313 r2785782))) (join_sums term (lo:=2786251) (a:=1875) (b:=1875) (join_sums term (lo:=2786251) (a:=937) (b:=938) (join_sums term (lo:=2786251) (a:=468) (b:=469) r2786251 r2786719) (join_sums term (lo:=2787188) (a:=469) (b:=469) r2787188 r2787657)) (join_sums term (lo:=2788126) (a:=937) (b:=938) (join_sums term (lo:=2788126) (a:=468) (b:=469) r2788126 r2788594) (join_sums term (lo:=2789063) (a:=469) (b:=469) r2789063 r2789532))))))))

private theorem rows : blockSum term 0 2790001 4273061665 :=
  join_sums term (lo:=0) (a:=2670001) (b:=120000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 2790000).filter (2670000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=4273061665 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From2670000To2790000
