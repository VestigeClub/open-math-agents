import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 2,310,000 through 2,430,000

The sum covers 8,125 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From2310000To2430000

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


private abbrev term := contribution 30110134441897 2310000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 2310001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 2310000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r2310001 : blockSum term 2310001 468 19750600 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2310469 : blockSum term 2310469 469 25873298 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2310938 : blockSum term 2310938 469 19059228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2311407 : blockSum term 2311407 469 25858964 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2311876 : blockSum term 2311876 468 15647265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2312344 : blockSum term 2312344 469 18363298 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2312813 : blockSum term 2312813 469 18358045 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2313282 : blockSum term 2313282 469 22431361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2313751 : blockSum term 2313751 468 23104172 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2314219 : blockSum term 2314219 469 16304535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2314688 : blockSum term 2314688 469 28524775 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2315157 : blockSum term 2315157 469 17652942 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2315626 : blockSum term 2315626 468 21041997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2316094 : blockSum term 2316094 469 24428271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2316563 : blockSum term 2316563 469 15602758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2317032 : blockSum term 2317032 469 18989244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2317501 : blockSum term 2317501 468 22373380 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2317969 : blockSum term 2317969 469 20333757 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2318438 : blockSum term 2318438 469 25071398 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2318907 : blockSum term 2318907 469 20322150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2319376 : blockSum term 2319376 468 23025814 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2319844 : blockSum term 2319844 469 18957253 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2320313 : blockSum term 2320313 469 20305858 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2320782 : blockSum term 2320782 469 23006601 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2321251 : blockSum term 2321251 468 16912276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2321719 : blockSum term 2321719 469 22317239 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2322188 : blockSum term 2322188 469 22987286 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2322657 : blockSum term 2322657 469 20277238 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2323126 : blockSum term 2323126 468 22974463 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2323594 : blockSum term 2323594 469 21616945 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2324063 : blockSum term 2324063 469 20935391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2324532 : blockSum term 2324532 469 17553768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2325001 : blockSum term 2325001 468 17549200 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2325469 : blockSum term 2325469 469 22267613 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2325938 : blockSum term 2325938 469 22260963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2326407 : blockSum term 2326407 469 22929258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2326876 : blockSum term 2326876 468 24271274 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2327344 : blockSum term 2327344 469 26286024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2327813 : blockSum term 2327813 469 20888244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2328282 : blockSum term 2328282 469 20882491 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2328751 : blockSum term 2328751 468 20203142 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2329219 : blockSum term 2329219 469 21543655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2329688 : blockSum term 2329688 469 20191745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2330157 : blockSum term 2330157 469 16822001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2330626 : blockSum term 2330626 468 21526064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2331094 : blockSum term 2331094 469 18830374 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2331563 : blockSum term 2331563 469 20169756 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2332032 : blockSum term 2332032 469 20835779 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2332501 : blockSum term 2332501 468 22846438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2332969 : blockSum term 2332969 469 23511445 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2333438 : blockSum term 2333438 469 26190603 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2333907 : blockSum term 2333907 469 24169396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2334376 : blockSum term 2334376 468 18793211 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2334844 : blockSum term 2334844 469 22814097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2335313 : blockSum term 2335313 469 20794928 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2335782 : blockSum term 2335782 469 21459679 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2336251 : blockSum term 2336251 468 22124258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2336719 : blockSum term 2336719 469 22787845 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2337188 : blockSum term 2337188 469 20771721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2337657 : blockSum term 2337657 469 20096167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2338126 : blockSum term 2338126 468 17412062 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2338594 : blockSum term 2338594 469 22094187 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2339063 : blockSum term 2339063 469 16733477 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2339532 : blockSum term 2339532 469 23420059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2340001 : blockSum term 2340001 468 22075070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2340469 : blockSum term 2340469 469 24743404 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2340938 : blockSum term 2340938 469 18719232 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2341407 : blockSum term 2341407 469 22056044 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2341876 : blockSum term 2341876 468 24054588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2342344 : blockSum term 2342344 469 22711164 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2342813 : blockSum term 2342813 469 19365904 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2343282 : blockSum term 2343282 469 20695907 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2343751 : blockSum term 2343751 468 20022421 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2344219 : blockSum term 2344219 469 22018445 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2344688 : blockSum term 2344688 469 22012151 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2345157 : blockSum term 2345157 469 18671515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2345626 : blockSum term 2345626 468 19333416 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2346094 : blockSum term 2346094 469 15329060 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2346563 : blockSum term 2346563 469 19988669 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2347032 : blockSum term 2347032 469 24645242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2347501 : blockSum term 2347501 468 21974808 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2347969 : blockSum term 2347969 469 19971352 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2348438 : blockSum term 2348438 469 22627583 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2348907 : blockSum term 2348907 469 23286464 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2349376 : blockSum term 2349376 468 14632927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2349844 : blockSum term 2349844 469 23938461 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2350313 : blockSum term 2350313 469 25260997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2350782 : blockSum term 2350782 469 17944198 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2351251 : blockSum term 2351251 468 16610289 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2351719 : blockSum term 2351719 469 25904604 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2352188 : blockSum term 2352188 469 19256625 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2352657 : blockSum term 2352657 469 19915180 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2353126 : blockSum term 2353126 468 16591318 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2353594 : blockSum term 2353594 469 25211856 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2354063 : blockSum term 2354063 469 22551602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2354532 : blockSum term 2354532 469 19892861 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2355001 : blockSum term 2355001 468 25853529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2355469 : blockSum term 2355469 469 13917305 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2355938 : blockSum term 2355938 469 21863726 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2356407 : blockSum term 2356407 469 19870620 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2356876 : blockSum term 2356876 468 21189411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2357344 : blockSum term 2357344 469 23168955 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2357813 : blockSum term 2357813 469 23162458 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2358282 : blockSum term 2358282 469 19847618 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2358751 : blockSum term 2358751 468 25133178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2359219 : blockSum term 2359219 469 22481480 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2359688 : blockSum term 2359688 469 21152450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2360157 : blockSum term 2360157 469 21146562 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2360626 : blockSum term 2360626 468 18497535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2361094 : blockSum term 2361094 469 19813729 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2361563 : blockSum term 2361563 469 21128771 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2362032 : blockSum term 2362032 469 21783151 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2362501 : blockSum term 2362501 468 22436564 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2362969 : blockSum term 2362969 469 23749741 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2363438 : blockSum term 2363438 469 19125996 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2363907 : blockSum term 2363907 469 26373123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2364376 : blockSum term 2364376 468 21751343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2364844 : blockSum term 2364844 469 21085815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2365313 : blockSum term 2365313 469 21739026 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2365782 : blockSum term 2365782 469 21073870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2366251 : blockSum term 2366251 468 21067794 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2366719 : blockSum term 2366719 469 19745686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2367188 : blockSum term 2367188 469 20398297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2367657 : blockSum term 2367657 469 20392268 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2368126 : blockSum term 2368126 468 25646782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2368594 : blockSum term 2368594 469 16435563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2369063 : blockSum term 2369063 469 23660390 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2369532 : blockSum term 2369532 469 21025619 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2370001 : blockSum term 2370001 468 19706045 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2370469 : blockSum term 2370469 469 21014462 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2370938 : blockSum term 2370938 469 19695175 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2371407 : blockSum term 2371407 469 19032704 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2371876 : blockSum term 2371876 468 16403502 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2372344 : blockSum term 2372344 469 26238157 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2372813 : blockSum term 2372813 469 28852914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2373282 : blockSum term 2373282 469 14422807 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2373751 : blockSum term 2373751 468 20316960 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2374219 : blockSum term 2374219 469 18345869 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2374688 : blockSum term 2374688 469 14410480 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2375157 : blockSum term 2375157 469 20955044 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2375626 : blockSum term 2375626 468 20948739 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2376094 : blockSum term 2376094 469 24215340 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2376563 : blockSum term 2376563 469 22899484 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2377032 : blockSum term 2377032 469 20930517 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2377501 : blockSum term 2377501 468 17001616 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2377969 : blockSum term 2377969 469 18304562 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2378438 : blockSum term 2378438 469 22874763 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2378907 : blockSum term 2378907 469 19600927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2379376 : blockSum term 2379376 468 21555317 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2379844 : blockSum term 2379844 469 18284324 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2380313 : blockSum term 2380313 469 24807524 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2380782 : blockSum term 2380782 469 23494637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2381251 : blockSum term 2381251 468 22836170 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2381719 : blockSum term 2381719 469 20872689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2382188 : blockSum term 2382188 469 22822904 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2382657 : blockSum term 2382657 469 20860998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2383126 : blockSum term 2383126 468 19551557 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2383594 : blockSum term 2383594 469 22151948 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2384063 : blockSum term 2384063 469 15631982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2384532 : blockSum term 2384532 469 22139706 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2385001 : blockSum term 2385001 468 16925466 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2385469 : blockSum term 2385469 469 19523788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2385938 : blockSum term 2385938 469 26675838 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2386407 : blockSum term 2386407 469 21463775 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2386876 : blockSum term 2386876 468 22758447 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2387344 : blockSum term 2387344 469 19502519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2387813 : blockSum term 2387813 469 24695271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2388282 : blockSum term 2388282 469 20789605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2388751 : blockSum term 2388751 468 18835204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2389219 : blockSum term 2389219 469 23374765 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2389688 : blockSum term 2389688 469 25964370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2390157 : blockSum term 2390157 469 18818936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2390626 : blockSum term 2390626 468 23354420 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2391094 : blockSum term 2391094 469 20105183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2391563 : blockSum term 2391563 469 18802740 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2392032 : blockSum term 2392032 469 19445848 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2392501 : blockSum term 2392501 468 19440615 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2392969 : blockSum term 2392969 469 16196104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2393438 : blockSum term 2393438 469 20077065 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2393907 : blockSum term 2393907 469 23309109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2394376 : blockSum term 2394376 468 17476692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2394844 : blockSum term 2394844 469 17472000 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2395313 : blockSum term 2395313 469 18760967 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2395782 : blockSum term 2395782 469 21342399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2396251 : blockSum term 2396251 468 20043612 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2396719 : blockSum term 2396719 469 25855586 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2397188 : blockSum term 2397188 469 21970888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2397657 : blockSum term 2397657 469 19380809 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2398126 : blockSum term 2398126 468 29709106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2398594 : blockSum term 2398594 469 17432683 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2399063 : blockSum term 2399063 469 20009746 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2399532 : blockSum term 2399532 469 22585538 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2400001 : blockSum term 2400001 468 19353830 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2400469 : blockSum term 2400469 469 19992729 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2400938 : blockSum term 2400938 469 17408055 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2401407 : blockSum term 2401407 469 18048497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2401876 : blockSum term 2401876 468 19331941 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2402344 : blockSum term 2402344 469 21904162 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2402813 : blockSum term 2402813 469 21253870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2403282 : blockSum term 2403282 469 25111110 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2403751 : blockSum term 2403751 468 19310538 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2404219 : blockSum term 2404219 469 16731257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2404688 : blockSum term 2404688 469 23159468 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2405157 : blockSum term 2405157 469 21223257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2405626 : blockSum term 2405626 468 18645285 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2406094 : blockSum term 2406094 469 16711674 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2406563 : blockSum term 2406563 469 21205175 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2407032 : blockSum term 2407032 469 24410888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2407501 : blockSum term 2407501 468 19266502 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2407969 : blockSum term 2407969 469 16692888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2408438 : blockSum term 2408438 469 17330274 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2408907 : blockSum term 2408907 469 23742560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2409376 : blockSum term 2409376 468 19245844 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2409844 : blockSum term 2409844 469 13468665 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2410313 : blockSum term 2410313 469 24365081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2410782 : blockSum term 2410782 469 23716782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2411251 : blockSum term 2411251 468 16661204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2411719 : blockSum term 2411719 469 16656919 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2412188 : blockSum term 2412188 469 21776039 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2412657 : blockSum term 2412657 469 20489490 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2413126 : blockSum term 2413126 468 24323363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2413594 : blockSum term 2413594 469 21756954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2414063 : blockSum term 2414063 469 21111176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2414532 : blockSum term 2414532 469 22383749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2415001 : blockSum term 2415001 468 17902375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2415469 : blockSum term 2415469 469 19176541 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2415938 : blockSum term 2415938 469 24282642 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2416407 : blockSum term 2416407 469 19803786 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2416876 : blockSum term 2416876 468 20436600 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2417344 : blockSum term 2417344 469 20431139 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2417813 : blockSum term 2417813 469 21702469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2418282 : blockSum term 2418282 469 22971964 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2418751 : blockSum term 2418751 468 18500182 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2419219 : blockSum term 2419219 469 18494825 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2419688 : blockSum term 2419688 469 21677822 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2420157 : blockSum term 2420157 469 19121705 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2420626 : blockSum term 2420626 468 21665116 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2421094 : blockSum term 2421094 469 22932938 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2421563 : blockSum term 2421563 469 19742336 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2422032 : blockSum term 2422032 469 22283691 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2422501 : blockSum term 2422501 468 21641291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2422969 : blockSum term 2422969 469 18453290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2423438 : blockSum term 2423438 469 19084347 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2423907 : blockSum term 2423907 469 17171448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2424376 : blockSum term 2424376 468 17801982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2424844 : blockSum term 2424844 469 19068705 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2425313 : blockSum term 2425313 469 23511084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2425782 : blockSum term 2425782 469 17787110 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2426251 : blockSum term 2426251 468 22227335 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2426719 : blockSum term 2426719 469 22220771 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2427188 : blockSum term 2427188 469 20310103 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2427657 : blockSum term 2427657 469 20938802 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2428126 : blockSum term 2428126 468 19030451 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2428594 : blockSum term 2428594 469 20927046 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2429063 : blockSum term 2429063 469 19019425 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2429532 : blockSum term 2429532 469 17112790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 2310001 120000 5338670692 := (join_sums term (lo:=2310001) (a:=60000) (b:=60000) (join_sums term (lo:=2310001) (a:=30000) (b:=30000) (join_sums term (lo:=2310001) (a:=15000) (b:=15000) (join_sums term (lo:=2310001) (a:=7500) (b:=7500) (join_sums term (lo:=2310001) (a:=3750) (b:=3750) (join_sums term (lo:=2310001) (a:=1875) (b:=1875) (join_sums term (lo:=2310001) (a:=937) (b:=938) (join_sums term (lo:=2310001) (a:=468) (b:=469) r2310001 r2310469) (join_sums term (lo:=2310938) (a:=469) (b:=469) r2310938 r2311407)) (join_sums term (lo:=2311876) (a:=937) (b:=938) (join_sums term (lo:=2311876) (a:=468) (b:=469) r2311876 r2312344) (join_sums term (lo:=2312813) (a:=469) (b:=469) r2312813 r2313282))) (join_sums term (lo:=2313751) (a:=1875) (b:=1875) (join_sums term (lo:=2313751) (a:=937) (b:=938) (join_sums term (lo:=2313751) (a:=468) (b:=469) r2313751 r2314219) (join_sums term (lo:=2314688) (a:=469) (b:=469) r2314688 r2315157)) (join_sums term (lo:=2315626) (a:=937) (b:=938) (join_sums term (lo:=2315626) (a:=468) (b:=469) r2315626 r2316094) (join_sums term (lo:=2316563) (a:=469) (b:=469) r2316563 r2317032)))) (join_sums term (lo:=2317501) (a:=3750) (b:=3750) (join_sums term (lo:=2317501) (a:=1875) (b:=1875) (join_sums term (lo:=2317501) (a:=937) (b:=938) (join_sums term (lo:=2317501) (a:=468) (b:=469) r2317501 r2317969) (join_sums term (lo:=2318438) (a:=469) (b:=469) r2318438 r2318907)) (join_sums term (lo:=2319376) (a:=937) (b:=938) (join_sums term (lo:=2319376) (a:=468) (b:=469) r2319376 r2319844) (join_sums term (lo:=2320313) (a:=469) (b:=469) r2320313 r2320782))) (join_sums term (lo:=2321251) (a:=1875) (b:=1875) (join_sums term (lo:=2321251) (a:=937) (b:=938) (join_sums term (lo:=2321251) (a:=468) (b:=469) r2321251 r2321719) (join_sums term (lo:=2322188) (a:=469) (b:=469) r2322188 r2322657)) (join_sums term (lo:=2323126) (a:=937) (b:=938) (join_sums term (lo:=2323126) (a:=468) (b:=469) r2323126 r2323594) (join_sums term (lo:=2324063) (a:=469) (b:=469) r2324063 r2324532))))) (join_sums term (lo:=2325001) (a:=7500) (b:=7500) (join_sums term (lo:=2325001) (a:=3750) (b:=3750) (join_sums term (lo:=2325001) (a:=1875) (b:=1875) (join_sums term (lo:=2325001) (a:=937) (b:=938) (join_sums term (lo:=2325001) (a:=468) (b:=469) r2325001 r2325469) (join_sums term (lo:=2325938) (a:=469) (b:=469) r2325938 r2326407)) (join_sums term (lo:=2326876) (a:=937) (b:=938) (join_sums term (lo:=2326876) (a:=468) (b:=469) r2326876 r2327344) (join_sums term (lo:=2327813) (a:=469) (b:=469) r2327813 r2328282))) (join_sums term (lo:=2328751) (a:=1875) (b:=1875) (join_sums term (lo:=2328751) (a:=937) (b:=938) (join_sums term (lo:=2328751) (a:=468) (b:=469) r2328751 r2329219) (join_sums term (lo:=2329688) (a:=469) (b:=469) r2329688 r2330157)) (join_sums term (lo:=2330626) (a:=937) (b:=938) (join_sums term (lo:=2330626) (a:=468) (b:=469) r2330626 r2331094) (join_sums term (lo:=2331563) (a:=469) (b:=469) r2331563 r2332032)))) (join_sums term (lo:=2332501) (a:=3750) (b:=3750) (join_sums term (lo:=2332501) (a:=1875) (b:=1875) (join_sums term (lo:=2332501) (a:=937) (b:=938) (join_sums term (lo:=2332501) (a:=468) (b:=469) r2332501 r2332969) (join_sums term (lo:=2333438) (a:=469) (b:=469) r2333438 r2333907)) (join_sums term (lo:=2334376) (a:=937) (b:=938) (join_sums term (lo:=2334376) (a:=468) (b:=469) r2334376 r2334844) (join_sums term (lo:=2335313) (a:=469) (b:=469) r2335313 r2335782))) (join_sums term (lo:=2336251) (a:=1875) (b:=1875) (join_sums term (lo:=2336251) (a:=937) (b:=938) (join_sums term (lo:=2336251) (a:=468) (b:=469) r2336251 r2336719) (join_sums term (lo:=2337188) (a:=469) (b:=469) r2337188 r2337657)) (join_sums term (lo:=2338126) (a:=937) (b:=938) (join_sums term (lo:=2338126) (a:=468) (b:=469) r2338126 r2338594) (join_sums term (lo:=2339063) (a:=469) (b:=469) r2339063 r2339532)))))) (join_sums term (lo:=2340001) (a:=15000) (b:=15000) (join_sums term (lo:=2340001) (a:=7500) (b:=7500) (join_sums term (lo:=2340001) (a:=3750) (b:=3750) (join_sums term (lo:=2340001) (a:=1875) (b:=1875) (join_sums term (lo:=2340001) (a:=937) (b:=938) (join_sums term (lo:=2340001) (a:=468) (b:=469) r2340001 r2340469) (join_sums term (lo:=2340938) (a:=469) (b:=469) r2340938 r2341407)) (join_sums term (lo:=2341876) (a:=937) (b:=938) (join_sums term (lo:=2341876) (a:=468) (b:=469) r2341876 r2342344) (join_sums term (lo:=2342813) (a:=469) (b:=469) r2342813 r2343282))) (join_sums term (lo:=2343751) (a:=1875) (b:=1875) (join_sums term (lo:=2343751) (a:=937) (b:=938) (join_sums term (lo:=2343751) (a:=468) (b:=469) r2343751 r2344219) (join_sums term (lo:=2344688) (a:=469) (b:=469) r2344688 r2345157)) (join_sums term (lo:=2345626) (a:=937) (b:=938) (join_sums term (lo:=2345626) (a:=468) (b:=469) r2345626 r2346094) (join_sums term (lo:=2346563) (a:=469) (b:=469) r2346563 r2347032)))) (join_sums term (lo:=2347501) (a:=3750) (b:=3750) (join_sums term (lo:=2347501) (a:=1875) (b:=1875) (join_sums term (lo:=2347501) (a:=937) (b:=938) (join_sums term (lo:=2347501) (a:=468) (b:=469) r2347501 r2347969) (join_sums term (lo:=2348438) (a:=469) (b:=469) r2348438 r2348907)) (join_sums term (lo:=2349376) (a:=937) (b:=938) (join_sums term (lo:=2349376) (a:=468) (b:=469) r2349376 r2349844) (join_sums term (lo:=2350313) (a:=469) (b:=469) r2350313 r2350782))) (join_sums term (lo:=2351251) (a:=1875) (b:=1875) (join_sums term (lo:=2351251) (a:=937) (b:=938) (join_sums term (lo:=2351251) (a:=468) (b:=469) r2351251 r2351719) (join_sums term (lo:=2352188) (a:=469) (b:=469) r2352188 r2352657)) (join_sums term (lo:=2353126) (a:=937) (b:=938) (join_sums term (lo:=2353126) (a:=468) (b:=469) r2353126 r2353594) (join_sums term (lo:=2354063) (a:=469) (b:=469) r2354063 r2354532))))) (join_sums term (lo:=2355001) (a:=7500) (b:=7500) (join_sums term (lo:=2355001) (a:=3750) (b:=3750) (join_sums term (lo:=2355001) (a:=1875) (b:=1875) (join_sums term (lo:=2355001) (a:=937) (b:=938) (join_sums term (lo:=2355001) (a:=468) (b:=469) r2355001 r2355469) (join_sums term (lo:=2355938) (a:=469) (b:=469) r2355938 r2356407)) (join_sums term (lo:=2356876) (a:=937) (b:=938) (join_sums term (lo:=2356876) (a:=468) (b:=469) r2356876 r2357344) (join_sums term (lo:=2357813) (a:=469) (b:=469) r2357813 r2358282))) (join_sums term (lo:=2358751) (a:=1875) (b:=1875) (join_sums term (lo:=2358751) (a:=937) (b:=938) (join_sums term (lo:=2358751) (a:=468) (b:=469) r2358751 r2359219) (join_sums term (lo:=2359688) (a:=469) (b:=469) r2359688 r2360157)) (join_sums term (lo:=2360626) (a:=937) (b:=938) (join_sums term (lo:=2360626) (a:=468) (b:=469) r2360626 r2361094) (join_sums term (lo:=2361563) (a:=469) (b:=469) r2361563 r2362032)))) (join_sums term (lo:=2362501) (a:=3750) (b:=3750) (join_sums term (lo:=2362501) (a:=1875) (b:=1875) (join_sums term (lo:=2362501) (a:=937) (b:=938) (join_sums term (lo:=2362501) (a:=468) (b:=469) r2362501 r2362969) (join_sums term (lo:=2363438) (a:=469) (b:=469) r2363438 r2363907)) (join_sums term (lo:=2364376) (a:=937) (b:=938) (join_sums term (lo:=2364376) (a:=468) (b:=469) r2364376 r2364844) (join_sums term (lo:=2365313) (a:=469) (b:=469) r2365313 r2365782))) (join_sums term (lo:=2366251) (a:=1875) (b:=1875) (join_sums term (lo:=2366251) (a:=937) (b:=938) (join_sums term (lo:=2366251) (a:=468) (b:=469) r2366251 r2366719) (join_sums term (lo:=2367188) (a:=469) (b:=469) r2367188 r2367657)) (join_sums term (lo:=2368126) (a:=937) (b:=938) (join_sums term (lo:=2368126) (a:=468) (b:=469) r2368126 r2368594) (join_sums term (lo:=2369063) (a:=469) (b:=469) r2369063 r2369532))))))) (join_sums term (lo:=2370001) (a:=30000) (b:=30000) (join_sums term (lo:=2370001) (a:=15000) (b:=15000) (join_sums term (lo:=2370001) (a:=7500) (b:=7500) (join_sums term (lo:=2370001) (a:=3750) (b:=3750) (join_sums term (lo:=2370001) (a:=1875) (b:=1875) (join_sums term (lo:=2370001) (a:=937) (b:=938) (join_sums term (lo:=2370001) (a:=468) (b:=469) r2370001 r2370469) (join_sums term (lo:=2370938) (a:=469) (b:=469) r2370938 r2371407)) (join_sums term (lo:=2371876) (a:=937) (b:=938) (join_sums term (lo:=2371876) (a:=468) (b:=469) r2371876 r2372344) (join_sums term (lo:=2372813) (a:=469) (b:=469) r2372813 r2373282))) (join_sums term (lo:=2373751) (a:=1875) (b:=1875) (join_sums term (lo:=2373751) (a:=937) (b:=938) (join_sums term (lo:=2373751) (a:=468) (b:=469) r2373751 r2374219) (join_sums term (lo:=2374688) (a:=469) (b:=469) r2374688 r2375157)) (join_sums term (lo:=2375626) (a:=937) (b:=938) (join_sums term (lo:=2375626) (a:=468) (b:=469) r2375626 r2376094) (join_sums term (lo:=2376563) (a:=469) (b:=469) r2376563 r2377032)))) (join_sums term (lo:=2377501) (a:=3750) (b:=3750) (join_sums term (lo:=2377501) (a:=1875) (b:=1875) (join_sums term (lo:=2377501) (a:=937) (b:=938) (join_sums term (lo:=2377501) (a:=468) (b:=469) r2377501 r2377969) (join_sums term (lo:=2378438) (a:=469) (b:=469) r2378438 r2378907)) (join_sums term (lo:=2379376) (a:=937) (b:=938) (join_sums term (lo:=2379376) (a:=468) (b:=469) r2379376 r2379844) (join_sums term (lo:=2380313) (a:=469) (b:=469) r2380313 r2380782))) (join_sums term (lo:=2381251) (a:=1875) (b:=1875) (join_sums term (lo:=2381251) (a:=937) (b:=938) (join_sums term (lo:=2381251) (a:=468) (b:=469) r2381251 r2381719) (join_sums term (lo:=2382188) (a:=469) (b:=469) r2382188 r2382657)) (join_sums term (lo:=2383126) (a:=937) (b:=938) (join_sums term (lo:=2383126) (a:=468) (b:=469) r2383126 r2383594) (join_sums term (lo:=2384063) (a:=469) (b:=469) r2384063 r2384532))))) (join_sums term (lo:=2385001) (a:=7500) (b:=7500) (join_sums term (lo:=2385001) (a:=3750) (b:=3750) (join_sums term (lo:=2385001) (a:=1875) (b:=1875) (join_sums term (lo:=2385001) (a:=937) (b:=938) (join_sums term (lo:=2385001) (a:=468) (b:=469) r2385001 r2385469) (join_sums term (lo:=2385938) (a:=469) (b:=469) r2385938 r2386407)) (join_sums term (lo:=2386876) (a:=937) (b:=938) (join_sums term (lo:=2386876) (a:=468) (b:=469) r2386876 r2387344) (join_sums term (lo:=2387813) (a:=469) (b:=469) r2387813 r2388282))) (join_sums term (lo:=2388751) (a:=1875) (b:=1875) (join_sums term (lo:=2388751) (a:=937) (b:=938) (join_sums term (lo:=2388751) (a:=468) (b:=469) r2388751 r2389219) (join_sums term (lo:=2389688) (a:=469) (b:=469) r2389688 r2390157)) (join_sums term (lo:=2390626) (a:=937) (b:=938) (join_sums term (lo:=2390626) (a:=468) (b:=469) r2390626 r2391094) (join_sums term (lo:=2391563) (a:=469) (b:=469) r2391563 r2392032)))) (join_sums term (lo:=2392501) (a:=3750) (b:=3750) (join_sums term (lo:=2392501) (a:=1875) (b:=1875) (join_sums term (lo:=2392501) (a:=937) (b:=938) (join_sums term (lo:=2392501) (a:=468) (b:=469) r2392501 r2392969) (join_sums term (lo:=2393438) (a:=469) (b:=469) r2393438 r2393907)) (join_sums term (lo:=2394376) (a:=937) (b:=938) (join_sums term (lo:=2394376) (a:=468) (b:=469) r2394376 r2394844) (join_sums term (lo:=2395313) (a:=469) (b:=469) r2395313 r2395782))) (join_sums term (lo:=2396251) (a:=1875) (b:=1875) (join_sums term (lo:=2396251) (a:=937) (b:=938) (join_sums term (lo:=2396251) (a:=468) (b:=469) r2396251 r2396719) (join_sums term (lo:=2397188) (a:=469) (b:=469) r2397188 r2397657)) (join_sums term (lo:=2398126) (a:=937) (b:=938) (join_sums term (lo:=2398126) (a:=468) (b:=469) r2398126 r2398594) (join_sums term (lo:=2399063) (a:=469) (b:=469) r2399063 r2399532)))))) (join_sums term (lo:=2400001) (a:=15000) (b:=15000) (join_sums term (lo:=2400001) (a:=7500) (b:=7500) (join_sums term (lo:=2400001) (a:=3750) (b:=3750) (join_sums term (lo:=2400001) (a:=1875) (b:=1875) (join_sums term (lo:=2400001) (a:=937) (b:=938) (join_sums term (lo:=2400001) (a:=468) (b:=469) r2400001 r2400469) (join_sums term (lo:=2400938) (a:=469) (b:=469) r2400938 r2401407)) (join_sums term (lo:=2401876) (a:=937) (b:=938) (join_sums term (lo:=2401876) (a:=468) (b:=469) r2401876 r2402344) (join_sums term (lo:=2402813) (a:=469) (b:=469) r2402813 r2403282))) (join_sums term (lo:=2403751) (a:=1875) (b:=1875) (join_sums term (lo:=2403751) (a:=937) (b:=938) (join_sums term (lo:=2403751) (a:=468) (b:=469) r2403751 r2404219) (join_sums term (lo:=2404688) (a:=469) (b:=469) r2404688 r2405157)) (join_sums term (lo:=2405626) (a:=937) (b:=938) (join_sums term (lo:=2405626) (a:=468) (b:=469) r2405626 r2406094) (join_sums term (lo:=2406563) (a:=469) (b:=469) r2406563 r2407032)))) (join_sums term (lo:=2407501) (a:=3750) (b:=3750) (join_sums term (lo:=2407501) (a:=1875) (b:=1875) (join_sums term (lo:=2407501) (a:=937) (b:=938) (join_sums term (lo:=2407501) (a:=468) (b:=469) r2407501 r2407969) (join_sums term (lo:=2408438) (a:=469) (b:=469) r2408438 r2408907)) (join_sums term (lo:=2409376) (a:=937) (b:=938) (join_sums term (lo:=2409376) (a:=468) (b:=469) r2409376 r2409844) (join_sums term (lo:=2410313) (a:=469) (b:=469) r2410313 r2410782))) (join_sums term (lo:=2411251) (a:=1875) (b:=1875) (join_sums term (lo:=2411251) (a:=937) (b:=938) (join_sums term (lo:=2411251) (a:=468) (b:=469) r2411251 r2411719) (join_sums term (lo:=2412188) (a:=469) (b:=469) r2412188 r2412657)) (join_sums term (lo:=2413126) (a:=937) (b:=938) (join_sums term (lo:=2413126) (a:=468) (b:=469) r2413126 r2413594) (join_sums term (lo:=2414063) (a:=469) (b:=469) r2414063 r2414532))))) (join_sums term (lo:=2415001) (a:=7500) (b:=7500) (join_sums term (lo:=2415001) (a:=3750) (b:=3750) (join_sums term (lo:=2415001) (a:=1875) (b:=1875) (join_sums term (lo:=2415001) (a:=937) (b:=938) (join_sums term (lo:=2415001) (a:=468) (b:=469) r2415001 r2415469) (join_sums term (lo:=2415938) (a:=469) (b:=469) r2415938 r2416407)) (join_sums term (lo:=2416876) (a:=937) (b:=938) (join_sums term (lo:=2416876) (a:=468) (b:=469) r2416876 r2417344) (join_sums term (lo:=2417813) (a:=469) (b:=469) r2417813 r2418282))) (join_sums term (lo:=2418751) (a:=1875) (b:=1875) (join_sums term (lo:=2418751) (a:=937) (b:=938) (join_sums term (lo:=2418751) (a:=468) (b:=469) r2418751 r2419219) (join_sums term (lo:=2419688) (a:=469) (b:=469) r2419688 r2420157)) (join_sums term (lo:=2420626) (a:=937) (b:=938) (join_sums term (lo:=2420626) (a:=468) (b:=469) r2420626 r2421094) (join_sums term (lo:=2421563) (a:=469) (b:=469) r2421563 r2422032)))) (join_sums term (lo:=2422501) (a:=3750) (b:=3750) (join_sums term (lo:=2422501) (a:=1875) (b:=1875) (join_sums term (lo:=2422501) (a:=937) (b:=938) (join_sums term (lo:=2422501) (a:=468) (b:=469) r2422501 r2422969) (join_sums term (lo:=2423438) (a:=469) (b:=469) r2423438 r2423907)) (join_sums term (lo:=2424376) (a:=937) (b:=938) (join_sums term (lo:=2424376) (a:=468) (b:=469) r2424376 r2424844) (join_sums term (lo:=2425313) (a:=469) (b:=469) r2425313 r2425782))) (join_sums term (lo:=2426251) (a:=1875) (b:=1875) (join_sums term (lo:=2426251) (a:=937) (b:=938) (join_sums term (lo:=2426251) (a:=468) (b:=469) r2426251 r2426719) (join_sums term (lo:=2427188) (a:=469) (b:=469) r2427188 r2427657)) (join_sums term (lo:=2428126) (a:=937) (b:=938) (join_sums term (lo:=2428126) (a:=468) (b:=469) r2428126 r2428594) (join_sums term (lo:=2429063) (a:=469) (b:=469) r2429063 r2429532))))))))

private theorem rows : blockSum term 0 2430001 5338670692 :=
  join_sums term (lo:=0) (a:=2310001) (b:=120000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 2430000).filter (2310000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=5338670692 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From2310000To2430000
