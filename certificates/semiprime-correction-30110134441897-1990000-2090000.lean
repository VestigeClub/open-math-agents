import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 1,990,000 through 2,090,000

The sum covers 6,912 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From1990000To2090000

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


private abbrev term := contribution 30110134441897 1990000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 1990001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 1990000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r1990001 : blockSum term 1990001 390 28229277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1990391 : blockSum term 1990391 391 21581923 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1990782 : blockSum term 1990782 390 23236081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1991172 : blockSum term 1991172 391 20741228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1991563 : blockSum term 1991563 390 24883297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1991953 : blockSum term 1991953 391 23218868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1992344 : blockSum term 1992344 391 22383810 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1992735 : blockSum term 1992735 391 20721043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1993126 : blockSum term 1993126 390 24030286 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1993516 : blockSum term 1993516 391 22367941 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1993907 : blockSum term 1993907 390 19049681 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1994297 : blockSum term 1994297 391 27324258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1994688 : blockSum term 1994688 390 20694868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1995078 : blockSum term 1995078 391 19862616 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1995469 : blockSum term 1995469 391 23167096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1995860 : blockSum term 1995860 391 23160871 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1996251 : blockSum term 1996251 390 28117020 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1996641 : blockSum term 1996641 391 23149882 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1997032 : blockSum term 1997032 390 25623860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1997422 : blockSum term 1997422 391 23964275 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1997813 : blockSum term 1997813 390 22306355 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1998203 : blockSum term 1998203 391 28082193 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1998594 : blockSum term 1998594 391 19817812 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1998985 : blockSum term 1998985 391 23115097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1999376 : blockSum term 1999376 390 20633399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1999766 : blockSum term 1999766 391 20628260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2000157 : blockSum term 2000157 390 25572669 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2000547 : blockSum term 2000547 391 16494626 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2000938 : blockSum term 2000938 390 19788771 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2001328 : blockSum term 2001328 391 28851255 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2001719 : blockSum term 2001719 391 16482359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2002110 : blockSum term 2002110 391 23069221 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2002501 : blockSum term 2002501 390 23063375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2002891 : blockSum term 2002891 391 23881441 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2003282 : blockSum term 2003282 390 22228445 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2003672 : blockSum term 2003672 391 21399934 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2004063 : blockSum term 2004063 390 18103452 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2004453 : blockSum term 2004453 391 26325004 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2004844 : blockSum term 2004844 391 25495958 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2005235 : blockSum term 2005235 391 21378454 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2005626 : blockSum term 2005626 390 22195507 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2006016 : blockSum term 2006016 391 21367948 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2006407 : blockSum term 2006407 390 22184757 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2006797 : blockSum term 2006797 391 20536050 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2007188 : blockSum term 2007188 390 25458497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2007578 : blockSum term 2007578 391 28736389 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2007969 : blockSum term 2007969 391 25445568 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2008360 : blockSum term 2008360 391 22977308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2008751 : blockSum term 2008751 390 18869399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2009141 : blockSum term 2009141 391 21325600 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2009532 : blockSum term 2009532 390 22959774 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2009922 : blockSum term 2009922 391 23774625 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2010313 : blockSum term 2010313 390 21309768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2010703 : blockSum term 2010703 391 18026579 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2011094 : blockSum term 2011094 391 22938093 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2011485 : blockSum term 2011485 391 18837308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2011876 : blockSum term 2011876 390 23745488 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2012266 : blockSum term 2012266 391 18009649 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2012657 : blockSum term 2012657 390 22916434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2013047 : blockSum term 2013047 391 27001885 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2013438 : blockSum term 2013438 390 22086664 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2013828 : blockSum term 2013828 391 26170177 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2014219 : blockSum term 2014219 391 22893027 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2014610 : blockSum term 2014610 391 23704423 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2015001 : blockSum term 2015001 390 23698605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2015391 : blockSum term 2015391 391 22058356 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2015782 : blockSum term 2015782 390 20419607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2016172 : blockSum term 2016172 391 26947115 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2016563 : blockSum term 2016563 390 19592891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2016953 : blockSum term 2016953 391 18771789 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2017344 : blockSum term 2017344 391 22847183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2017735 : blockSum term 2017735 391 21210381 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2018126 : blockSum term 2018126 390 17942629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2018516 : blockSum term 2018516 391 23646201 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2018907 : blockSum term 2018907 390 25270528 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2019297 : blockSum term 2019297 391 16299549 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2019688 : blockSum term 2019688 390 25258332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2020078 : blockSum term 2020078 391 20364534 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2020469 : blockSum term 2020469 391 24431684 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2020860 : blockSum term 2020860 391 24425482 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2021251 : blockSum term 2021251 390 21163158 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2021641 : blockSum term 2021641 391 24413653 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2022032 : blockSum term 2022032 390 22779950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2022422 : blockSum term 2022422 391 20333935 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2022813 : blockSum term 2022813 390 23581677 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2023203 : blockSum term 2023203 391 20324598 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2023594 : blockSum term 2023594 391 21945443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2023985 : blockSum term 2023985 391 21126982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2024376 : blockSum term 2024376 390 17060609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2024766 : blockSum term 2024766 391 15432063 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2025157 : blockSum term 2025157 390 24360278 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2025547 : blockSum term 2025547 391 25166206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2025938 : blockSum term 2025938 390 17855085 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2026328 : blockSum term 2026328 391 20285286 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2026719 : blockSum term 2026719 391 24336373 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2027110 : blockSum term 2027110 391 21897015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2027501 : blockSum term 2027501 390 25135271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2027891 : blockSum term 2027891 391 24318324 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2028282 : blockSum term 2028282 390 21070571 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2028672 : blockSum term 2028672 391 21065294 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2029063 : blockSum term 2029063 390 24299786 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2029453 : blockSum term 2029453 391 21863967 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2029844 : blockSum term 2029844 391 19430314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2030235 : blockSum term 2030235 391 23472443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2030626 : blockSum term 2030626 390 17802407 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2031016 : blockSum term 2031016 391 21034130 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2031407 : blockSum term 2031407 390 20220021 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2031797 : blockSum term 2031797 391 20214668 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2032188 : blockSum term 2032188 390 25868765 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2032578 : blockSum term 2032578 391 29095086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2032969 : blockSum term 2032969 391 25855792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2033360 : blockSum term 2033360 391 22618437 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2033751 : blockSum term 2033751 390 20189914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2034141 : blockSum term 2034141 391 23414045 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2034532 : blockSum term 2034532 390 20986617 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2034922 : blockSum term 2034922 391 23402704 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2035313 : blockSum term 2035313 390 20170047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2035703 : blockSum term 2035703 391 19358313 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2036094 : blockSum term 2036094 391 20966423 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2036485 : blockSum term 2036485 391 21767369 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2036876 : blockSum term 2036876 390 23374325 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2037266 : blockSum term 2037266 391 19339752 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2037657 : blockSum term 2037657 390 20946100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2038047 : blockSum term 2038047 391 20134579 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2038438 : blockSum term 2038438 390 19324659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2038828 : blockSum term 2038828 391 20124748 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2039219 : blockSum term 2039219 391 20119781 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2039610 : blockSum term 2039610 391 26551555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2040001 : blockSum term 2040001 390 23327591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2040391 : blockSum term 2040391 391 22517808 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2040782 : blockSum term 2040782 390 16883829 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2041172 : blockSum term 2041172 391 18487144 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2041563 : blockSum term 2041563 390 20090231 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2041953 : blockSum term 2041953 391 25708947 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2042344 : blockSum term 2042344 391 22490033 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2042735 : blockSum term 2042735 391 24893177 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2043126 : blockSum term 2043126 390 23281085 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2043516 : blockSum term 2043516 391 20065367 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2043907 : blockSum term 2043907 390 22467700 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2044297 : blockSum term 2044297 391 17648377 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2044688 : blockSum term 2044688 390 22456204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2045078 : blockSum term 2045078 391 15234617 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2045469 : blockSum term 2045469 391 24850299 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2045860 : blockSum term 2045860 391 20837016 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2046251 : blockSum term 2046251 390 20030793 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2046641 : blockSum term 2046641 391 24030907 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2047032 : blockSum term 2047032 390 21622767 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2047422 : blockSum term 2047422 391 18414682 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2047813 : blockSum term 2047813 390 20010766 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2048203 : blockSum term 2048203 391 20806436 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2048594 : blockSum term 2048594 391 18401249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2048985 : blockSum term 2048985 391 19996646 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2049376 : blockSum term 2049376 390 21591162 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2049766 : blockSum term 2049766 391 19986954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2050157 : blockSum term 2050157 390 24778028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2050547 : blockSum term 2050547 391 21575146 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2050938 : blockSum term 2050938 390 23167115 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2051328 : blockSum term 2051328 391 19966826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2051719 : blockSum term 2051719 391 19163367 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2052110 : blockSum term 2052110 391 16764070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2052501 : blockSum term 2052501 390 22346606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2052891 : blockSum term 2052891 391 21543435 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2053282 : blockSum term 2053282 390 20739911 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2053672 : blockSum term 2053672 391 24721867 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2054063 : blockSum term 2054063 390 18338134 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2054453 : blockSum term 2054453 391 22318898 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2054844 : blockSum term 2054844 391 27094503 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2055235 : blockSum term 2055235 391 17527346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2055626 : blockSum term 2055626 390 15930641 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2056016 : blockSum term 2056016 391 21500850 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2056407 : blockSum term 2056407 390 23884100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2056797 : blockSum term 2056797 391 23082415 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2057188 : blockSum term 2057188 390 20689573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2057578 : blockSum term 2057578 391 23866794 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2057969 : blockSum term 2057969 391 22270285 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2058360 : blockSum term 2058360 391 23059409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2058751 : blockSum term 2058751 390 20669573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2059141 : blockSum term 2059141 391 23048734 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2059532 : blockSum term 2059532 390 23837441 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2059922 : blockSum term 2059922 391 21448558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2060313 : blockSum term 2060313 390 21443468 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2060703 : blockSum term 2060703 391 15880213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2061094 : blockSum term 2061094 391 23815118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2061485 : blockSum term 2061485 391 16666708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2061876 : blockSum term 2061876 390 24597056 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2062266 : blockSum term 2062266 391 19831529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2062657 : blockSum term 2062657 390 23791671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2063047 : blockSum term 2063047 391 18235602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2063438 : blockSum term 2063438 390 26950436 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2063828 : blockSum term 2063828 391 22981510 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2064219 : blockSum term 2064219 391 26144783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2064610 : blockSum term 2064610 391 21385651 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2065001 : blockSum term 2065001 390 17421207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2065391 : blockSum term 2065391 391 22166561 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2065782 : blockSum term 2065782 390 20578225 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2066172 : blockSum term 2066172 391 21364481 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2066563 : blockSum term 2066563 390 22150226 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2066953 : blockSum term 2066953 391 18981823 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2067344 : blockSum term 2067344 391 20558235 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2067735 : blockSum term 2067735 391 18971991 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2068126 : blockSum term 2068126 390 23708899 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2068516 : blockSum term 2068516 391 21332946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2068907 : blockSum term 2068907 390 20537964 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2069297 : blockSum term 2069297 391 21322364 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2069688 : blockSum term 2069688 390 25264953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2070078 : blockSum term 2070078 391 20522627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2070469 : blockSum term 2070469 391 22096159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2070860 : blockSum term 2070860 391 15779278 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2071251 : blockSum term 2071251 390 23662860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2071641 : blockSum term 2071641 391 25233980 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2072032 : blockSum term 2072032 390 16556117 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2072422 : blockSum term 2072422 391 22069301 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2072813 : blockSum term 2072813 390 21275271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2073203 : blockSum term 2073203 391 19695181 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2073594 : blockSum term 2073594 391 18114813 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2073985 : blockSum term 2073985 391 21259944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2074376 : blockSum term 2074376 390 18893722 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2074766 : blockSum term 2074766 391 19676073 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2075157 : blockSum term 2075157 390 18884544 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2075547 : blockSum term 2075547 391 25959873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2075938 : blockSum term 2075938 390 18875168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2076328 : blockSum term 2076328 391 19656781 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2076719 : blockSum term 2076719 391 18079977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2077110 : blockSum term 2077110 391 18075995 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2077501 : blockSum term 2077501 390 20428513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2077891 : blockSum term 2077891 391 20424025 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2078282 : blockSum term 2078282 390 22775007 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2078672 : blockSum term 2078672 391 24339752 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2079063 : blockSum term 2079063 390 23549067 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2079453 : blockSum term 2079453 391 23542536 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2079844 : blockSum term 2079844 391 19613524 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2080235 : blockSum term 2080235 391 21962029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2080626 : blockSum term 2080626 390 18820129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2081016 : blockSum term 2081016 391 19599236 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2081407 : blockSum term 2081407 390 17243701 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2081797 : blockSum term 2081797 391 23508516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2082188 : blockSum term 2082188 390 13317916 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2082578 : blockSum term 2082578 391 26629940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2082969 : blockSum term 2082969 391 24274062 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2083360 : blockSum term 2083360 391 18788227 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2083751 : blockSum term 2083751 390 20349106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2084141 : blockSum term 2084141 391 21909013 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2084532 : blockSum term 2084532 390 14863181 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2084922 : blockSum term 2084922 391 26590599 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2085313 : blockSum term 2085313 390 17201275 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2085703 : blockSum term 2085703 391 22669348 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2086094 : blockSum term 2086094 391 20319307 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2086485 : blockSum term 2086485 391 24220997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2086876 : blockSum term 2086876 390 21090600 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2087266 : blockSum term 2087266 391 22647563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2087657 : blockSum term 2087657 390 21080361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2088047 : blockSum term 2088047 391 23416538 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2088438 : blockSum term 2088438 390 22630921 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2088828 : blockSum term 2088828 391 21845089 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2089219 : blockSum term 2089219 391 20279776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2089610 : blockSum term 2089610 391 18715401 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 1990001 100000 5563042513 := (join_sums term (lo:=1990001) (a:=50000) (b:=50000) (join_sums term (lo:=1990001) (a:=25000) (b:=25000) (join_sums term (lo:=1990001) (a:=12500) (b:=12500) (join_sums term (lo:=1990001) (a:=6250) (b:=6250) (join_sums term (lo:=1990001) (a:=3125) (b:=3125) (join_sums term (lo:=1990001) (a:=1562) (b:=1563) (join_sums term (lo:=1990001) (a:=781) (b:=781) (join_sums term (lo:=1990001) (a:=390) (b:=391) r1990001 r1990391) (join_sums term (lo:=1990782) (a:=390) (b:=391) r1990782 r1991172)) (join_sums term (lo:=1991563) (a:=781) (b:=782) (join_sums term (lo:=1991563) (a:=390) (b:=391) r1991563 r1991953) (join_sums term (lo:=1992344) (a:=391) (b:=391) r1992344 r1992735))) (join_sums term (lo:=1993126) (a:=1562) (b:=1563) (join_sums term (lo:=1993126) (a:=781) (b:=781) (join_sums term (lo:=1993126) (a:=390) (b:=391) r1993126 r1993516) (join_sums term (lo:=1993907) (a:=390) (b:=391) r1993907 r1994297)) (join_sums term (lo:=1994688) (a:=781) (b:=782) (join_sums term (lo:=1994688) (a:=390) (b:=391) r1994688 r1995078) (join_sums term (lo:=1995469) (a:=391) (b:=391) r1995469 r1995860)))) (join_sums term (lo:=1996251) (a:=3125) (b:=3125) (join_sums term (lo:=1996251) (a:=1562) (b:=1563) (join_sums term (lo:=1996251) (a:=781) (b:=781) (join_sums term (lo:=1996251) (a:=390) (b:=391) r1996251 r1996641) (join_sums term (lo:=1997032) (a:=390) (b:=391) r1997032 r1997422)) (join_sums term (lo:=1997813) (a:=781) (b:=782) (join_sums term (lo:=1997813) (a:=390) (b:=391) r1997813 r1998203) (join_sums term (lo:=1998594) (a:=391) (b:=391) r1998594 r1998985))) (join_sums term (lo:=1999376) (a:=1562) (b:=1563) (join_sums term (lo:=1999376) (a:=781) (b:=781) (join_sums term (lo:=1999376) (a:=390) (b:=391) r1999376 r1999766) (join_sums term (lo:=2000157) (a:=390) (b:=391) r2000157 r2000547)) (join_sums term (lo:=2000938) (a:=781) (b:=782) (join_sums term (lo:=2000938) (a:=390) (b:=391) r2000938 r2001328) (join_sums term (lo:=2001719) (a:=391) (b:=391) r2001719 r2002110))))) (join_sums term (lo:=2002501) (a:=6250) (b:=6250) (join_sums term (lo:=2002501) (a:=3125) (b:=3125) (join_sums term (lo:=2002501) (a:=1562) (b:=1563) (join_sums term (lo:=2002501) (a:=781) (b:=781) (join_sums term (lo:=2002501) (a:=390) (b:=391) r2002501 r2002891) (join_sums term (lo:=2003282) (a:=390) (b:=391) r2003282 r2003672)) (join_sums term (lo:=2004063) (a:=781) (b:=782) (join_sums term (lo:=2004063) (a:=390) (b:=391) r2004063 r2004453) (join_sums term (lo:=2004844) (a:=391) (b:=391) r2004844 r2005235))) (join_sums term (lo:=2005626) (a:=1562) (b:=1563) (join_sums term (lo:=2005626) (a:=781) (b:=781) (join_sums term (lo:=2005626) (a:=390) (b:=391) r2005626 r2006016) (join_sums term (lo:=2006407) (a:=390) (b:=391) r2006407 r2006797)) (join_sums term (lo:=2007188) (a:=781) (b:=782) (join_sums term (lo:=2007188) (a:=390) (b:=391) r2007188 r2007578) (join_sums term (lo:=2007969) (a:=391) (b:=391) r2007969 r2008360)))) (join_sums term (lo:=2008751) (a:=3125) (b:=3125) (join_sums term (lo:=2008751) (a:=1562) (b:=1563) (join_sums term (lo:=2008751) (a:=781) (b:=781) (join_sums term (lo:=2008751) (a:=390) (b:=391) r2008751 r2009141) (join_sums term (lo:=2009532) (a:=390) (b:=391) r2009532 r2009922)) (join_sums term (lo:=2010313) (a:=781) (b:=782) (join_sums term (lo:=2010313) (a:=390) (b:=391) r2010313 r2010703) (join_sums term (lo:=2011094) (a:=391) (b:=391) r2011094 r2011485))) (join_sums term (lo:=2011876) (a:=1562) (b:=1563) (join_sums term (lo:=2011876) (a:=781) (b:=781) (join_sums term (lo:=2011876) (a:=390) (b:=391) r2011876 r2012266) (join_sums term (lo:=2012657) (a:=390) (b:=391) r2012657 r2013047)) (join_sums term (lo:=2013438) (a:=781) (b:=782) (join_sums term (lo:=2013438) (a:=390) (b:=391) r2013438 r2013828) (join_sums term (lo:=2014219) (a:=391) (b:=391) r2014219 r2014610)))))) (join_sums term (lo:=2015001) (a:=12500) (b:=12500) (join_sums term (lo:=2015001) (a:=6250) (b:=6250) (join_sums term (lo:=2015001) (a:=3125) (b:=3125) (join_sums term (lo:=2015001) (a:=1562) (b:=1563) (join_sums term (lo:=2015001) (a:=781) (b:=781) (join_sums term (lo:=2015001) (a:=390) (b:=391) r2015001 r2015391) (join_sums term (lo:=2015782) (a:=390) (b:=391) r2015782 r2016172)) (join_sums term (lo:=2016563) (a:=781) (b:=782) (join_sums term (lo:=2016563) (a:=390) (b:=391) r2016563 r2016953) (join_sums term (lo:=2017344) (a:=391) (b:=391) r2017344 r2017735))) (join_sums term (lo:=2018126) (a:=1562) (b:=1563) (join_sums term (lo:=2018126) (a:=781) (b:=781) (join_sums term (lo:=2018126) (a:=390) (b:=391) r2018126 r2018516) (join_sums term (lo:=2018907) (a:=390) (b:=391) r2018907 r2019297)) (join_sums term (lo:=2019688) (a:=781) (b:=782) (join_sums term (lo:=2019688) (a:=390) (b:=391) r2019688 r2020078) (join_sums term (lo:=2020469) (a:=391) (b:=391) r2020469 r2020860)))) (join_sums term (lo:=2021251) (a:=3125) (b:=3125) (join_sums term (lo:=2021251) (a:=1562) (b:=1563) (join_sums term (lo:=2021251) (a:=781) (b:=781) (join_sums term (lo:=2021251) (a:=390) (b:=391) r2021251 r2021641) (join_sums term (lo:=2022032) (a:=390) (b:=391) r2022032 r2022422)) (join_sums term (lo:=2022813) (a:=781) (b:=782) (join_sums term (lo:=2022813) (a:=390) (b:=391) r2022813 r2023203) (join_sums term (lo:=2023594) (a:=391) (b:=391) r2023594 r2023985))) (join_sums term (lo:=2024376) (a:=1562) (b:=1563) (join_sums term (lo:=2024376) (a:=781) (b:=781) (join_sums term (lo:=2024376) (a:=390) (b:=391) r2024376 r2024766) (join_sums term (lo:=2025157) (a:=390) (b:=391) r2025157 r2025547)) (join_sums term (lo:=2025938) (a:=781) (b:=782) (join_sums term (lo:=2025938) (a:=390) (b:=391) r2025938 r2026328) (join_sums term (lo:=2026719) (a:=391) (b:=391) r2026719 r2027110))))) (join_sums term (lo:=2027501) (a:=6250) (b:=6250) (join_sums term (lo:=2027501) (a:=3125) (b:=3125) (join_sums term (lo:=2027501) (a:=1562) (b:=1563) (join_sums term (lo:=2027501) (a:=781) (b:=781) (join_sums term (lo:=2027501) (a:=390) (b:=391) r2027501 r2027891) (join_sums term (lo:=2028282) (a:=390) (b:=391) r2028282 r2028672)) (join_sums term (lo:=2029063) (a:=781) (b:=782) (join_sums term (lo:=2029063) (a:=390) (b:=391) r2029063 r2029453) (join_sums term (lo:=2029844) (a:=391) (b:=391) r2029844 r2030235))) (join_sums term (lo:=2030626) (a:=1562) (b:=1563) (join_sums term (lo:=2030626) (a:=781) (b:=781) (join_sums term (lo:=2030626) (a:=390) (b:=391) r2030626 r2031016) (join_sums term (lo:=2031407) (a:=390) (b:=391) r2031407 r2031797)) (join_sums term (lo:=2032188) (a:=781) (b:=782) (join_sums term (lo:=2032188) (a:=390) (b:=391) r2032188 r2032578) (join_sums term (lo:=2032969) (a:=391) (b:=391) r2032969 r2033360)))) (join_sums term (lo:=2033751) (a:=3125) (b:=3125) (join_sums term (lo:=2033751) (a:=1562) (b:=1563) (join_sums term (lo:=2033751) (a:=781) (b:=781) (join_sums term (lo:=2033751) (a:=390) (b:=391) r2033751 r2034141) (join_sums term (lo:=2034532) (a:=390) (b:=391) r2034532 r2034922)) (join_sums term (lo:=2035313) (a:=781) (b:=782) (join_sums term (lo:=2035313) (a:=390) (b:=391) r2035313 r2035703) (join_sums term (lo:=2036094) (a:=391) (b:=391) r2036094 r2036485))) (join_sums term (lo:=2036876) (a:=1562) (b:=1563) (join_sums term (lo:=2036876) (a:=781) (b:=781) (join_sums term (lo:=2036876) (a:=390) (b:=391) r2036876 r2037266) (join_sums term (lo:=2037657) (a:=390) (b:=391) r2037657 r2038047)) (join_sums term (lo:=2038438) (a:=781) (b:=782) (join_sums term (lo:=2038438) (a:=390) (b:=391) r2038438 r2038828) (join_sums term (lo:=2039219) (a:=391) (b:=391) r2039219 r2039610))))))) (join_sums term (lo:=2040001) (a:=25000) (b:=25000) (join_sums term (lo:=2040001) (a:=12500) (b:=12500) (join_sums term (lo:=2040001) (a:=6250) (b:=6250) (join_sums term (lo:=2040001) (a:=3125) (b:=3125) (join_sums term (lo:=2040001) (a:=1562) (b:=1563) (join_sums term (lo:=2040001) (a:=781) (b:=781) (join_sums term (lo:=2040001) (a:=390) (b:=391) r2040001 r2040391) (join_sums term (lo:=2040782) (a:=390) (b:=391) r2040782 r2041172)) (join_sums term (lo:=2041563) (a:=781) (b:=782) (join_sums term (lo:=2041563) (a:=390) (b:=391) r2041563 r2041953) (join_sums term (lo:=2042344) (a:=391) (b:=391) r2042344 r2042735))) (join_sums term (lo:=2043126) (a:=1562) (b:=1563) (join_sums term (lo:=2043126) (a:=781) (b:=781) (join_sums term (lo:=2043126) (a:=390) (b:=391) r2043126 r2043516) (join_sums term (lo:=2043907) (a:=390) (b:=391) r2043907 r2044297)) (join_sums term (lo:=2044688) (a:=781) (b:=782) (join_sums term (lo:=2044688) (a:=390) (b:=391) r2044688 r2045078) (join_sums term (lo:=2045469) (a:=391) (b:=391) r2045469 r2045860)))) (join_sums term (lo:=2046251) (a:=3125) (b:=3125) (join_sums term (lo:=2046251) (a:=1562) (b:=1563) (join_sums term (lo:=2046251) (a:=781) (b:=781) (join_sums term (lo:=2046251) (a:=390) (b:=391) r2046251 r2046641) (join_sums term (lo:=2047032) (a:=390) (b:=391) r2047032 r2047422)) (join_sums term (lo:=2047813) (a:=781) (b:=782) (join_sums term (lo:=2047813) (a:=390) (b:=391) r2047813 r2048203) (join_sums term (lo:=2048594) (a:=391) (b:=391) r2048594 r2048985))) (join_sums term (lo:=2049376) (a:=1562) (b:=1563) (join_sums term (lo:=2049376) (a:=781) (b:=781) (join_sums term (lo:=2049376) (a:=390) (b:=391) r2049376 r2049766) (join_sums term (lo:=2050157) (a:=390) (b:=391) r2050157 r2050547)) (join_sums term (lo:=2050938) (a:=781) (b:=782) (join_sums term (lo:=2050938) (a:=390) (b:=391) r2050938 r2051328) (join_sums term (lo:=2051719) (a:=391) (b:=391) r2051719 r2052110))))) (join_sums term (lo:=2052501) (a:=6250) (b:=6250) (join_sums term (lo:=2052501) (a:=3125) (b:=3125) (join_sums term (lo:=2052501) (a:=1562) (b:=1563) (join_sums term (lo:=2052501) (a:=781) (b:=781) (join_sums term (lo:=2052501) (a:=390) (b:=391) r2052501 r2052891) (join_sums term (lo:=2053282) (a:=390) (b:=391) r2053282 r2053672)) (join_sums term (lo:=2054063) (a:=781) (b:=782) (join_sums term (lo:=2054063) (a:=390) (b:=391) r2054063 r2054453) (join_sums term (lo:=2054844) (a:=391) (b:=391) r2054844 r2055235))) (join_sums term (lo:=2055626) (a:=1562) (b:=1563) (join_sums term (lo:=2055626) (a:=781) (b:=781) (join_sums term (lo:=2055626) (a:=390) (b:=391) r2055626 r2056016) (join_sums term (lo:=2056407) (a:=390) (b:=391) r2056407 r2056797)) (join_sums term (lo:=2057188) (a:=781) (b:=782) (join_sums term (lo:=2057188) (a:=390) (b:=391) r2057188 r2057578) (join_sums term (lo:=2057969) (a:=391) (b:=391) r2057969 r2058360)))) (join_sums term (lo:=2058751) (a:=3125) (b:=3125) (join_sums term (lo:=2058751) (a:=1562) (b:=1563) (join_sums term (lo:=2058751) (a:=781) (b:=781) (join_sums term (lo:=2058751) (a:=390) (b:=391) r2058751 r2059141) (join_sums term (lo:=2059532) (a:=390) (b:=391) r2059532 r2059922)) (join_sums term (lo:=2060313) (a:=781) (b:=782) (join_sums term (lo:=2060313) (a:=390) (b:=391) r2060313 r2060703) (join_sums term (lo:=2061094) (a:=391) (b:=391) r2061094 r2061485))) (join_sums term (lo:=2061876) (a:=1562) (b:=1563) (join_sums term (lo:=2061876) (a:=781) (b:=781) (join_sums term (lo:=2061876) (a:=390) (b:=391) r2061876 r2062266) (join_sums term (lo:=2062657) (a:=390) (b:=391) r2062657 r2063047)) (join_sums term (lo:=2063438) (a:=781) (b:=782) (join_sums term (lo:=2063438) (a:=390) (b:=391) r2063438 r2063828) (join_sums term (lo:=2064219) (a:=391) (b:=391) r2064219 r2064610)))))) (join_sums term (lo:=2065001) (a:=12500) (b:=12500) (join_sums term (lo:=2065001) (a:=6250) (b:=6250) (join_sums term (lo:=2065001) (a:=3125) (b:=3125) (join_sums term (lo:=2065001) (a:=1562) (b:=1563) (join_sums term (lo:=2065001) (a:=781) (b:=781) (join_sums term (lo:=2065001) (a:=390) (b:=391) r2065001 r2065391) (join_sums term (lo:=2065782) (a:=390) (b:=391) r2065782 r2066172)) (join_sums term (lo:=2066563) (a:=781) (b:=782) (join_sums term (lo:=2066563) (a:=390) (b:=391) r2066563 r2066953) (join_sums term (lo:=2067344) (a:=391) (b:=391) r2067344 r2067735))) (join_sums term (lo:=2068126) (a:=1562) (b:=1563) (join_sums term (lo:=2068126) (a:=781) (b:=781) (join_sums term (lo:=2068126) (a:=390) (b:=391) r2068126 r2068516) (join_sums term (lo:=2068907) (a:=390) (b:=391) r2068907 r2069297)) (join_sums term (lo:=2069688) (a:=781) (b:=782) (join_sums term (lo:=2069688) (a:=390) (b:=391) r2069688 r2070078) (join_sums term (lo:=2070469) (a:=391) (b:=391) r2070469 r2070860)))) (join_sums term (lo:=2071251) (a:=3125) (b:=3125) (join_sums term (lo:=2071251) (a:=1562) (b:=1563) (join_sums term (lo:=2071251) (a:=781) (b:=781) (join_sums term (lo:=2071251) (a:=390) (b:=391) r2071251 r2071641) (join_sums term (lo:=2072032) (a:=390) (b:=391) r2072032 r2072422)) (join_sums term (lo:=2072813) (a:=781) (b:=782) (join_sums term (lo:=2072813) (a:=390) (b:=391) r2072813 r2073203) (join_sums term (lo:=2073594) (a:=391) (b:=391) r2073594 r2073985))) (join_sums term (lo:=2074376) (a:=1562) (b:=1563) (join_sums term (lo:=2074376) (a:=781) (b:=781) (join_sums term (lo:=2074376) (a:=390) (b:=391) r2074376 r2074766) (join_sums term (lo:=2075157) (a:=390) (b:=391) r2075157 r2075547)) (join_sums term (lo:=2075938) (a:=781) (b:=782) (join_sums term (lo:=2075938) (a:=390) (b:=391) r2075938 r2076328) (join_sums term (lo:=2076719) (a:=391) (b:=391) r2076719 r2077110))))) (join_sums term (lo:=2077501) (a:=6250) (b:=6250) (join_sums term (lo:=2077501) (a:=3125) (b:=3125) (join_sums term (lo:=2077501) (a:=1562) (b:=1563) (join_sums term (lo:=2077501) (a:=781) (b:=781) (join_sums term (lo:=2077501) (a:=390) (b:=391) r2077501 r2077891) (join_sums term (lo:=2078282) (a:=390) (b:=391) r2078282 r2078672)) (join_sums term (lo:=2079063) (a:=781) (b:=782) (join_sums term (lo:=2079063) (a:=390) (b:=391) r2079063 r2079453) (join_sums term (lo:=2079844) (a:=391) (b:=391) r2079844 r2080235))) (join_sums term (lo:=2080626) (a:=1562) (b:=1563) (join_sums term (lo:=2080626) (a:=781) (b:=781) (join_sums term (lo:=2080626) (a:=390) (b:=391) r2080626 r2081016) (join_sums term (lo:=2081407) (a:=390) (b:=391) r2081407 r2081797)) (join_sums term (lo:=2082188) (a:=781) (b:=782) (join_sums term (lo:=2082188) (a:=390) (b:=391) r2082188 r2082578) (join_sums term (lo:=2082969) (a:=391) (b:=391) r2082969 r2083360)))) (join_sums term (lo:=2083751) (a:=3125) (b:=3125) (join_sums term (lo:=2083751) (a:=1562) (b:=1563) (join_sums term (lo:=2083751) (a:=781) (b:=781) (join_sums term (lo:=2083751) (a:=390) (b:=391) r2083751 r2084141) (join_sums term (lo:=2084532) (a:=390) (b:=391) r2084532 r2084922)) (join_sums term (lo:=2085313) (a:=781) (b:=782) (join_sums term (lo:=2085313) (a:=390) (b:=391) r2085313 r2085703) (join_sums term (lo:=2086094) (a:=391) (b:=391) r2086094 r2086485))) (join_sums term (lo:=2086876) (a:=1562) (b:=1563) (join_sums term (lo:=2086876) (a:=781) (b:=781) (join_sums term (lo:=2086876) (a:=390) (b:=391) r2086876 r2087266) (join_sums term (lo:=2087657) (a:=390) (b:=391) r2087657 r2088047)) (join_sums term (lo:=2088438) (a:=781) (b:=782) (join_sums term (lo:=2088438) (a:=390) (b:=391) r2088438 r2088828) (join_sums term (lo:=2089219) (a:=391) (b:=391) r2089219 r2089610))))))))

private theorem rows : blockSum term 0 2090001 5563042513 :=
  join_sums term (lo:=0) (a:=1990001) (b:=100000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 2090000).filter (1990000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=5563042513 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From1990000To2090000
