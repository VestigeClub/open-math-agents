import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 990,000 through 1,090,000

The sum covers 7,199 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From990000To1090000

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


private abbrev term := contribution 30110134441897 990000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 990001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 990000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r990001 : blockSum term 990001 390 57722345 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r990391 : blockSum term 990391 391 41472472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r990782 : blockSum term 990782 390 55874787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r991172 : blockSum term 991172 391 46844062 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r991563 : blockSum term 991563 390 55830594 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r991953 : blockSum term 991953 391 50408689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r992344 : blockSum term 992344 391 46788815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r992735 : blockSum term 992735 391 48567419 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r993126 : blockSum term 993126 390 50346256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r993516 : blockSum term 993516 391 41338589 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r993907 : blockSum term 993907 390 52102893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r994297 : blockSum term 994297 391 53878669 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r994688 : blockSum term 994688 390 55651868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r995078 : blockSum term 995078 391 48449445 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r995469 : blockSum term 995469 391 48432512 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r995860 : blockSum term 995860 391 51998397 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r996251 : blockSum term 996251 390 51977326 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r996641 : blockSum term 996641 391 46580554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r997032 : blockSum term 997032 390 64472947 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r997422 : blockSum term 997422 391 55493884 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r997813 : blockSum term 997813 390 48314045 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r998203 : blockSum term 998203 391 46507411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r998594 : blockSum term 998594 391 57216262 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r998985 : blockSum term 998985 391 46470083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r999376 : blockSum term 999376 390 46450652 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r999766 : blockSum term 999766 391 42860234 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1000157 : blockSum term 1000157 390 57126713 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1000547 : blockSum term 1000547 391 51749726 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1000938 : blockSum term 1000938 390 57078455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1001328 : blockSum term 1001328 391 53490444 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1001719 : blockSum term 1001719 391 49903014 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1002110 : blockSum term 1002110 391 53446938 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1002501 : blockSum term 1002501 390 60549271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1002891 : blockSum term 1002891 391 49845163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1003282 : blockSum term 1003282 390 48045483 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1003672 : blockSum term 1003672 391 51583842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1004063 : blockSum term 1004063 390 44450568 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1004453 : blockSum term 1004453 391 46210605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1004844 : blockSum term 1004844 391 51519959 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1005235 : blockSum term 1005235 391 55052857 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1005626 : blockSum term 1005626 390 40828622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1006016 : blockSum term 1006016 391 67427633 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1006407 : blockSum term 1006407 390 46117106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1006797 : blockSum term 1006797 391 53190986 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1007188 : blockSum term 1007188 390 44308160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1007578 : blockSum term 1007578 391 62006313 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1007969 : blockSum term 1007969 391 51356045 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1008360 : blockSum term 1008360 391 51336610 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1008751 : blockSum term 1008751 390 53084681 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1009141 : blockSum term 1009141 391 63675408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1009532 : blockSum term 1009532 390 44201276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1009922 : blockSum term 1009922 391 40650027 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1010313 : blockSum term 1010313 390 44167078 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1010703 : blockSum term 1010703 391 60043567 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1011094 : blockSum term 1011094 391 45897883 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1011485 : blockSum term 1011485 391 45880337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1011876 : blockSum term 1011876 390 56445432 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1012266 : blockSum term 1012266 391 61713867 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1012657 : blockSum term 1012657 390 51115386 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1013047 : blockSum term 1013047 391 36998144 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1013438 : blockSum term 1013438 390 52833504 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1013828 : blockSum term 1013828 391 51052606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1014219 : blockSum term 1014219 391 47513554 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1014610 : blockSum term 1014610 391 47494768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1015001 : blockSum term 1015001 390 45718423 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1015391 : blockSum term 1015391 391 58003455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1015782 : blockSum term 1015782 390 54465018 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1016172 : blockSum term 1016172 391 40395505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1016563 : blockSum term 1016563 390 54422963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1016953 : blockSum term 1016953 391 50891341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1017344 : blockSum term 1017344 391 50871929 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1017735 : blockSum term 1017735 391 42084178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1018126 : blockSum term 1018126 390 40314221 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1018516 : blockSum term 1018516 391 50811564 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1018907 : blockSum term 1018907 390 52544469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1019297 : blockSum term 1019297 391 52523917 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1019688 : blockSum term 1019688 390 59503663 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1020078 : blockSum term 1020078 391 48982206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1020469 : blockSum term 1020469 391 47213845 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1020860 : blockSum term 1020860 391 55937438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1021251 : blockSum term 1021251 390 55916931 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1021641 : blockSum term 1021641 391 45413226 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1022032 : blockSum term 1022032 390 48887769 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1022422 : blockSum term 1022422 391 48869182 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1022813 : blockSum term 1022813 390 48849565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1023203 : blockSum term 1023203 391 57551723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1023594 : blockSum term 1023594 391 38351825 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1023985 : blockSum term 1023985 391 43565231 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1024376 : blockSum term 1024376 390 48774950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1024766 : blockSum term 1024766 391 57461099 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1025157 : blockSum term 1025157 390 55698838 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1025547 : blockSum term 1025547 391 50456607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1025938 : blockSum term 1025938 390 45218742 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1026328 : blockSum term 1026328 391 48679173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1026719 : blockSum term 1026719 391 48659863 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1027110 : blockSum term 1027110 391 52114803 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1027501 : blockSum term 1027501 390 45148158 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1027891 : blockSum term 1027891 391 55543927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1028282 : blockSum term 1028282 390 41642042 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1028672 : blockSum term 1028672 391 45094545 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1029063 : blockSum term 1029063 390 50277594 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1029453 : blockSum term 1029453 391 53725379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1029844 : blockSum term 1029844 391 51972037 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1030235 : blockSum term 1030235 391 39830272 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1030626 : blockSum term 1030626 390 51932505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1031016 : blockSum term 1031016 391 36338623 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1031407 : blockSum term 1031407 390 53622556 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1031797 : blockSum term 1031797 391 29394605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1032188 : blockSum term 1032188 390 53580899 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1032578 : blockSum term 1032578 391 57015892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1032969 : blockSum term 1032969 391 48357490 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1033360 : blockSum term 1033360 391 55246946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1033751 : blockSum term 1033751 390 41419028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1034141 : blockSum term 1034141 391 56928517 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1034532 : blockSum term 1034532 390 50007401 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1034922 : blockSum term 1034922 391 43093959 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1035313 : blockSum term 1035313 390 55139277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1035703 : blockSum term 1035703 391 41337202 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1036094 : blockSum term 1036094 391 55096611 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1036485 : blockSum term 1036485 391 48190664 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1036876 : blockSum term 1036876 390 41291226 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1037266 : blockSum term 1037266 391 46434464 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1037657 : blockSum term 1037657 390 51572569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1038047 : blockSum term 1038047 391 46398118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1038438 : blockSum term 1038438 390 53250811 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1038828 : blockSum term 1038828 391 39493038 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1039219 : blockSum term 1039219 391 42911151 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1039610 : blockSum term 1039610 391 37747475 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1040001 : blockSum term 1040001 390 51455281 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1040391 : blockSum term 1040391 391 44576915 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1040782 : blockSum term 1040782 390 59984963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1041172 : blockSum term 1041172 391 47968893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1041563 : blockSum term 1041563 390 49662909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1041953 : blockSum term 1041953 391 51355390 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1042344 : blockSum term 1042344 391 47912998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1042735 : blockSum term 1042735 391 39341934 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1043126 : blockSum term 1043126 390 44457503 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1043516 : blockSum term 1043516 391 56403535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1043907 : blockSum term 1043907 390 52963824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1044297 : blockSum term 1044297 391 44406171 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1044688 : blockSum term 1044688 390 56339509 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1045078 : blockSum term 1045078 391 49491960 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1045469 : blockSum term 1045469 391 51179568 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1045860 : blockSum term 1045860 391 39220513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1046251 : blockSum term 1046251 390 39206727 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1046641 : blockSum term 1046641 391 44304634 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1047032 : blockSum term 1047032 390 57915030 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1047422 : blockSum term 1047422 391 47675666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1047813 : blockSum term 1047813 390 49360151 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1048203 : blockSum term 1048203 391 40833310 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1048594 : blockSum term 1048594 391 45920840 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1048985 : blockSum term 1048985 391 51004830 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1049376 : blockSum term 1049376 390 50985084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1049766 : blockSum term 1049766 391 49267344 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1050157 : blockSum term 1050157 390 47549395 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1050547 : blockSum term 1050547 391 35647570 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1050938 : blockSum term 1050938 390 45816376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1051328 : blockSum term 1051328 391 49190035 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1051719 : blockSum term 1051719 391 45780780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1052110 : blockSum term 1052110 391 47458184 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1052501 : blockSum term 1052501 390 44051404 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1052891 : blockSum term 1052891 391 44035082 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1053282 : blockSum term 1053282 390 45710966 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1053672 : blockSum term 1053672 391 47385558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1054063 : blockSum term 1054063 390 52442032 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1054453 : blockSum term 1054453 391 45658890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1054844 : blockSum term 1054844 391 38879111 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1055235 : blockSum term 1055235 391 49003776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1055626 : blockSum term 1055626 390 45606070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1056016 : blockSum term 1056016 391 55720548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1056407 : blockSum term 1056407 390 45571512 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1056797 : blockSum term 1056797 391 43866030 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1057188 : blockSum term 1057188 390 38790088 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1057578 : blockSum term 1057578 391 45520001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1057969 : blockSum term 1057969 391 50558419 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1058360 : blockSum term 1058360 391 53907544 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1058751 : blockSum term 1058751 390 48835473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1059141 : blockSum term 1059141 391 47133677 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1059532 : blockSum term 1059532 390 43750245 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1059922 : blockSum term 1059922 391 45416195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1060313 : blockSum term 1060313 390 52126627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1060703 : blockSum term 1060703 391 33616143 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1061094 : blockSum term 1061094 391 47045611 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1061485 : blockSum term 1061485 391 52065671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1061876 : blockSum term 1061876 390 35258183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1062266 : blockSum term 1062266 391 35244826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1062657 : blockSum term 1062657 390 53685127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1063047 : blockSum term 1063047 391 41926575 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1063438 : blockSum term 1063438 390 55322357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1063828 : blockSum term 1063828 391 56977037 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1064219 : blockSum term 1064219 391 46903205 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1064610 : blockSum term 1064610 391 45210348 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1065001 : blockSum term 1065001 390 46868534 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1065391 : blockSum term 1065391 391 41829667 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1065782 : blockSum term 1065782 390 48505354 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1066172 : blockSum term 1066172 391 46813656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1066563 : blockSum term 1066563 390 41782049 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1066953 : blockSum term 1066953 391 43437967 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1067344 : blockSum term 1067344 391 51770730 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1067735 : blockSum term 1067735 391 48412337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1068126 : blockSum term 1068126 390 53399837 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1068516 : blockSum term 1068516 391 48375453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1068907 : blockSum term 1068907 390 43355047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1069297 : blockSum term 1069297 391 53340061 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1069688 : blockSum term 1069688 390 46654773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1070078 : blockSum term 1070078 391 54965214 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1070469 : blockSum term 1070469 391 43290717 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1070860 : blockSum term 1070860 391 46601597 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1071251 : blockSum term 1071251 390 48250103 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1071641 : blockSum term 1071641 391 46568568 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1072032 : blockSum term 1072032 390 36574555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1072422 : blockSum term 1072422 391 34900209 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1072813 : blockSum term 1072813 390 56483289 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1073203 : blockSum term 1073203 391 48159287 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1073594 : blockSum term 1073594 391 43161357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1073985 : blockSum term 1073985 391 43145077 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1074376 : blockSum term 1074376 390 49762792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1074766 : blockSum term 1074766 391 53059613 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1075157 : blockSum term 1075157 390 56355591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1075547 : blockSum term 1075547 391 48051122 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1075938 : blockSum term 1075938 390 49688978 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1076328 : blockSum term 1076328 391 48014851 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1076719 : blockSum term 1076719 391 39721382 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1077110 : blockSum term 1077110 391 39706033 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1077501 : blockSum term 1077501 390 44652028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1077891 : blockSum term 1077891 391 46290010 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1078282 : blockSum term 1078282 390 31399480 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1078672 : blockSum term 1078672 391 54514353 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1079063 : blockSum term 1079063 390 49540100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1079453 : blockSum term 1079453 391 49520715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1079844 : blockSum term 1079844 391 56102631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1080235 : blockSum term 1080235 391 51133198 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1080626 : blockSum term 1080626 390 52761559 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1081016 : blockSum term 1081016 391 51094146 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1081407 : blockSum term 1081407 390 46130448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1081797 : blockSum term 1081797 391 46114568 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1082188 : blockSum term 1082188 390 41160134 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1082578 : blockSum term 1082578 391 36209688 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1082969 : blockSum term 1082969 391 54290836 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1083360 : blockSum term 1083360 391 44403718 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1083751 : blockSum term 1083751 390 46030804 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1084141 : blockSum term 1084141 391 42727118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1084532 : blockSum term 1084532 390 45997645 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1084922 : blockSum term 1084922 391 44339744 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1085313 : blockSum term 1085313 390 41038659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1085703 : blockSum term 1085703 391 42663317 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1086094 : blockSum term 1086094 391 55769345 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1086485 : blockSum term 1086485 391 42631871 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1086876 : blockSum term 1086876 390 39337973 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1087266 : blockSum term 1087266 391 42599916 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1087657 : blockSum term 1087657 390 54049568 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1088047 : blockSum term 1088047 391 42568430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1088438 : blockSum term 1088438 390 54009575 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1088828 : blockSum term 1088828 391 39265070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1089219 : blockSum term 1089219 391 37615600 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1089610 : blockSum term 1089610 391 34332109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 990001 100000 12362794193 := (join_sums term (lo:=990001) (a:=50000) (b:=50000) (join_sums term (lo:=990001) (a:=25000) (b:=25000) (join_sums term (lo:=990001) (a:=12500) (b:=12500) (join_sums term (lo:=990001) (a:=6250) (b:=6250) (join_sums term (lo:=990001) (a:=3125) (b:=3125) (join_sums term (lo:=990001) (a:=1562) (b:=1563) (join_sums term (lo:=990001) (a:=781) (b:=781) (join_sums term (lo:=990001) (a:=390) (b:=391) r990001 r990391) (join_sums term (lo:=990782) (a:=390) (b:=391) r990782 r991172)) (join_sums term (lo:=991563) (a:=781) (b:=782) (join_sums term (lo:=991563) (a:=390) (b:=391) r991563 r991953) (join_sums term (lo:=992344) (a:=391) (b:=391) r992344 r992735))) (join_sums term (lo:=993126) (a:=1562) (b:=1563) (join_sums term (lo:=993126) (a:=781) (b:=781) (join_sums term (lo:=993126) (a:=390) (b:=391) r993126 r993516) (join_sums term (lo:=993907) (a:=390) (b:=391) r993907 r994297)) (join_sums term (lo:=994688) (a:=781) (b:=782) (join_sums term (lo:=994688) (a:=390) (b:=391) r994688 r995078) (join_sums term (lo:=995469) (a:=391) (b:=391) r995469 r995860)))) (join_sums term (lo:=996251) (a:=3125) (b:=3125) (join_sums term (lo:=996251) (a:=1562) (b:=1563) (join_sums term (lo:=996251) (a:=781) (b:=781) (join_sums term (lo:=996251) (a:=390) (b:=391) r996251 r996641) (join_sums term (lo:=997032) (a:=390) (b:=391) r997032 r997422)) (join_sums term (lo:=997813) (a:=781) (b:=782) (join_sums term (lo:=997813) (a:=390) (b:=391) r997813 r998203) (join_sums term (lo:=998594) (a:=391) (b:=391) r998594 r998985))) (join_sums term (lo:=999376) (a:=1562) (b:=1563) (join_sums term (lo:=999376) (a:=781) (b:=781) (join_sums term (lo:=999376) (a:=390) (b:=391) r999376 r999766) (join_sums term (lo:=1000157) (a:=390) (b:=391) r1000157 r1000547)) (join_sums term (lo:=1000938) (a:=781) (b:=782) (join_sums term (lo:=1000938) (a:=390) (b:=391) r1000938 r1001328) (join_sums term (lo:=1001719) (a:=391) (b:=391) r1001719 r1002110))))) (join_sums term (lo:=1002501) (a:=6250) (b:=6250) (join_sums term (lo:=1002501) (a:=3125) (b:=3125) (join_sums term (lo:=1002501) (a:=1562) (b:=1563) (join_sums term (lo:=1002501) (a:=781) (b:=781) (join_sums term (lo:=1002501) (a:=390) (b:=391) r1002501 r1002891) (join_sums term (lo:=1003282) (a:=390) (b:=391) r1003282 r1003672)) (join_sums term (lo:=1004063) (a:=781) (b:=782) (join_sums term (lo:=1004063) (a:=390) (b:=391) r1004063 r1004453) (join_sums term (lo:=1004844) (a:=391) (b:=391) r1004844 r1005235))) (join_sums term (lo:=1005626) (a:=1562) (b:=1563) (join_sums term (lo:=1005626) (a:=781) (b:=781) (join_sums term (lo:=1005626) (a:=390) (b:=391) r1005626 r1006016) (join_sums term (lo:=1006407) (a:=390) (b:=391) r1006407 r1006797)) (join_sums term (lo:=1007188) (a:=781) (b:=782) (join_sums term (lo:=1007188) (a:=390) (b:=391) r1007188 r1007578) (join_sums term (lo:=1007969) (a:=391) (b:=391) r1007969 r1008360)))) (join_sums term (lo:=1008751) (a:=3125) (b:=3125) (join_sums term (lo:=1008751) (a:=1562) (b:=1563) (join_sums term (lo:=1008751) (a:=781) (b:=781) (join_sums term (lo:=1008751) (a:=390) (b:=391) r1008751 r1009141) (join_sums term (lo:=1009532) (a:=390) (b:=391) r1009532 r1009922)) (join_sums term (lo:=1010313) (a:=781) (b:=782) (join_sums term (lo:=1010313) (a:=390) (b:=391) r1010313 r1010703) (join_sums term (lo:=1011094) (a:=391) (b:=391) r1011094 r1011485))) (join_sums term (lo:=1011876) (a:=1562) (b:=1563) (join_sums term (lo:=1011876) (a:=781) (b:=781) (join_sums term (lo:=1011876) (a:=390) (b:=391) r1011876 r1012266) (join_sums term (lo:=1012657) (a:=390) (b:=391) r1012657 r1013047)) (join_sums term (lo:=1013438) (a:=781) (b:=782) (join_sums term (lo:=1013438) (a:=390) (b:=391) r1013438 r1013828) (join_sums term (lo:=1014219) (a:=391) (b:=391) r1014219 r1014610)))))) (join_sums term (lo:=1015001) (a:=12500) (b:=12500) (join_sums term (lo:=1015001) (a:=6250) (b:=6250) (join_sums term (lo:=1015001) (a:=3125) (b:=3125) (join_sums term (lo:=1015001) (a:=1562) (b:=1563) (join_sums term (lo:=1015001) (a:=781) (b:=781) (join_sums term (lo:=1015001) (a:=390) (b:=391) r1015001 r1015391) (join_sums term (lo:=1015782) (a:=390) (b:=391) r1015782 r1016172)) (join_sums term (lo:=1016563) (a:=781) (b:=782) (join_sums term (lo:=1016563) (a:=390) (b:=391) r1016563 r1016953) (join_sums term (lo:=1017344) (a:=391) (b:=391) r1017344 r1017735))) (join_sums term (lo:=1018126) (a:=1562) (b:=1563) (join_sums term (lo:=1018126) (a:=781) (b:=781) (join_sums term (lo:=1018126) (a:=390) (b:=391) r1018126 r1018516) (join_sums term (lo:=1018907) (a:=390) (b:=391) r1018907 r1019297)) (join_sums term (lo:=1019688) (a:=781) (b:=782) (join_sums term (lo:=1019688) (a:=390) (b:=391) r1019688 r1020078) (join_sums term (lo:=1020469) (a:=391) (b:=391) r1020469 r1020860)))) (join_sums term (lo:=1021251) (a:=3125) (b:=3125) (join_sums term (lo:=1021251) (a:=1562) (b:=1563) (join_sums term (lo:=1021251) (a:=781) (b:=781) (join_sums term (lo:=1021251) (a:=390) (b:=391) r1021251 r1021641) (join_sums term (lo:=1022032) (a:=390) (b:=391) r1022032 r1022422)) (join_sums term (lo:=1022813) (a:=781) (b:=782) (join_sums term (lo:=1022813) (a:=390) (b:=391) r1022813 r1023203) (join_sums term (lo:=1023594) (a:=391) (b:=391) r1023594 r1023985))) (join_sums term (lo:=1024376) (a:=1562) (b:=1563) (join_sums term (lo:=1024376) (a:=781) (b:=781) (join_sums term (lo:=1024376) (a:=390) (b:=391) r1024376 r1024766) (join_sums term (lo:=1025157) (a:=390) (b:=391) r1025157 r1025547)) (join_sums term (lo:=1025938) (a:=781) (b:=782) (join_sums term (lo:=1025938) (a:=390) (b:=391) r1025938 r1026328) (join_sums term (lo:=1026719) (a:=391) (b:=391) r1026719 r1027110))))) (join_sums term (lo:=1027501) (a:=6250) (b:=6250) (join_sums term (lo:=1027501) (a:=3125) (b:=3125) (join_sums term (lo:=1027501) (a:=1562) (b:=1563) (join_sums term (lo:=1027501) (a:=781) (b:=781) (join_sums term (lo:=1027501) (a:=390) (b:=391) r1027501 r1027891) (join_sums term (lo:=1028282) (a:=390) (b:=391) r1028282 r1028672)) (join_sums term (lo:=1029063) (a:=781) (b:=782) (join_sums term (lo:=1029063) (a:=390) (b:=391) r1029063 r1029453) (join_sums term (lo:=1029844) (a:=391) (b:=391) r1029844 r1030235))) (join_sums term (lo:=1030626) (a:=1562) (b:=1563) (join_sums term (lo:=1030626) (a:=781) (b:=781) (join_sums term (lo:=1030626) (a:=390) (b:=391) r1030626 r1031016) (join_sums term (lo:=1031407) (a:=390) (b:=391) r1031407 r1031797)) (join_sums term (lo:=1032188) (a:=781) (b:=782) (join_sums term (lo:=1032188) (a:=390) (b:=391) r1032188 r1032578) (join_sums term (lo:=1032969) (a:=391) (b:=391) r1032969 r1033360)))) (join_sums term (lo:=1033751) (a:=3125) (b:=3125) (join_sums term (lo:=1033751) (a:=1562) (b:=1563) (join_sums term (lo:=1033751) (a:=781) (b:=781) (join_sums term (lo:=1033751) (a:=390) (b:=391) r1033751 r1034141) (join_sums term (lo:=1034532) (a:=390) (b:=391) r1034532 r1034922)) (join_sums term (lo:=1035313) (a:=781) (b:=782) (join_sums term (lo:=1035313) (a:=390) (b:=391) r1035313 r1035703) (join_sums term (lo:=1036094) (a:=391) (b:=391) r1036094 r1036485))) (join_sums term (lo:=1036876) (a:=1562) (b:=1563) (join_sums term (lo:=1036876) (a:=781) (b:=781) (join_sums term (lo:=1036876) (a:=390) (b:=391) r1036876 r1037266) (join_sums term (lo:=1037657) (a:=390) (b:=391) r1037657 r1038047)) (join_sums term (lo:=1038438) (a:=781) (b:=782) (join_sums term (lo:=1038438) (a:=390) (b:=391) r1038438 r1038828) (join_sums term (lo:=1039219) (a:=391) (b:=391) r1039219 r1039610))))))) (join_sums term (lo:=1040001) (a:=25000) (b:=25000) (join_sums term (lo:=1040001) (a:=12500) (b:=12500) (join_sums term (lo:=1040001) (a:=6250) (b:=6250) (join_sums term (lo:=1040001) (a:=3125) (b:=3125) (join_sums term (lo:=1040001) (a:=1562) (b:=1563) (join_sums term (lo:=1040001) (a:=781) (b:=781) (join_sums term (lo:=1040001) (a:=390) (b:=391) r1040001 r1040391) (join_sums term (lo:=1040782) (a:=390) (b:=391) r1040782 r1041172)) (join_sums term (lo:=1041563) (a:=781) (b:=782) (join_sums term (lo:=1041563) (a:=390) (b:=391) r1041563 r1041953) (join_sums term (lo:=1042344) (a:=391) (b:=391) r1042344 r1042735))) (join_sums term (lo:=1043126) (a:=1562) (b:=1563) (join_sums term (lo:=1043126) (a:=781) (b:=781) (join_sums term (lo:=1043126) (a:=390) (b:=391) r1043126 r1043516) (join_sums term (lo:=1043907) (a:=390) (b:=391) r1043907 r1044297)) (join_sums term (lo:=1044688) (a:=781) (b:=782) (join_sums term (lo:=1044688) (a:=390) (b:=391) r1044688 r1045078) (join_sums term (lo:=1045469) (a:=391) (b:=391) r1045469 r1045860)))) (join_sums term (lo:=1046251) (a:=3125) (b:=3125) (join_sums term (lo:=1046251) (a:=1562) (b:=1563) (join_sums term (lo:=1046251) (a:=781) (b:=781) (join_sums term (lo:=1046251) (a:=390) (b:=391) r1046251 r1046641) (join_sums term (lo:=1047032) (a:=390) (b:=391) r1047032 r1047422)) (join_sums term (lo:=1047813) (a:=781) (b:=782) (join_sums term (lo:=1047813) (a:=390) (b:=391) r1047813 r1048203) (join_sums term (lo:=1048594) (a:=391) (b:=391) r1048594 r1048985))) (join_sums term (lo:=1049376) (a:=1562) (b:=1563) (join_sums term (lo:=1049376) (a:=781) (b:=781) (join_sums term (lo:=1049376) (a:=390) (b:=391) r1049376 r1049766) (join_sums term (lo:=1050157) (a:=390) (b:=391) r1050157 r1050547)) (join_sums term (lo:=1050938) (a:=781) (b:=782) (join_sums term (lo:=1050938) (a:=390) (b:=391) r1050938 r1051328) (join_sums term (lo:=1051719) (a:=391) (b:=391) r1051719 r1052110))))) (join_sums term (lo:=1052501) (a:=6250) (b:=6250) (join_sums term (lo:=1052501) (a:=3125) (b:=3125) (join_sums term (lo:=1052501) (a:=1562) (b:=1563) (join_sums term (lo:=1052501) (a:=781) (b:=781) (join_sums term (lo:=1052501) (a:=390) (b:=391) r1052501 r1052891) (join_sums term (lo:=1053282) (a:=390) (b:=391) r1053282 r1053672)) (join_sums term (lo:=1054063) (a:=781) (b:=782) (join_sums term (lo:=1054063) (a:=390) (b:=391) r1054063 r1054453) (join_sums term (lo:=1054844) (a:=391) (b:=391) r1054844 r1055235))) (join_sums term (lo:=1055626) (a:=1562) (b:=1563) (join_sums term (lo:=1055626) (a:=781) (b:=781) (join_sums term (lo:=1055626) (a:=390) (b:=391) r1055626 r1056016) (join_sums term (lo:=1056407) (a:=390) (b:=391) r1056407 r1056797)) (join_sums term (lo:=1057188) (a:=781) (b:=782) (join_sums term (lo:=1057188) (a:=390) (b:=391) r1057188 r1057578) (join_sums term (lo:=1057969) (a:=391) (b:=391) r1057969 r1058360)))) (join_sums term (lo:=1058751) (a:=3125) (b:=3125) (join_sums term (lo:=1058751) (a:=1562) (b:=1563) (join_sums term (lo:=1058751) (a:=781) (b:=781) (join_sums term (lo:=1058751) (a:=390) (b:=391) r1058751 r1059141) (join_sums term (lo:=1059532) (a:=390) (b:=391) r1059532 r1059922)) (join_sums term (lo:=1060313) (a:=781) (b:=782) (join_sums term (lo:=1060313) (a:=390) (b:=391) r1060313 r1060703) (join_sums term (lo:=1061094) (a:=391) (b:=391) r1061094 r1061485))) (join_sums term (lo:=1061876) (a:=1562) (b:=1563) (join_sums term (lo:=1061876) (a:=781) (b:=781) (join_sums term (lo:=1061876) (a:=390) (b:=391) r1061876 r1062266) (join_sums term (lo:=1062657) (a:=390) (b:=391) r1062657 r1063047)) (join_sums term (lo:=1063438) (a:=781) (b:=782) (join_sums term (lo:=1063438) (a:=390) (b:=391) r1063438 r1063828) (join_sums term (lo:=1064219) (a:=391) (b:=391) r1064219 r1064610)))))) (join_sums term (lo:=1065001) (a:=12500) (b:=12500) (join_sums term (lo:=1065001) (a:=6250) (b:=6250) (join_sums term (lo:=1065001) (a:=3125) (b:=3125) (join_sums term (lo:=1065001) (a:=1562) (b:=1563) (join_sums term (lo:=1065001) (a:=781) (b:=781) (join_sums term (lo:=1065001) (a:=390) (b:=391) r1065001 r1065391) (join_sums term (lo:=1065782) (a:=390) (b:=391) r1065782 r1066172)) (join_sums term (lo:=1066563) (a:=781) (b:=782) (join_sums term (lo:=1066563) (a:=390) (b:=391) r1066563 r1066953) (join_sums term (lo:=1067344) (a:=391) (b:=391) r1067344 r1067735))) (join_sums term (lo:=1068126) (a:=1562) (b:=1563) (join_sums term (lo:=1068126) (a:=781) (b:=781) (join_sums term (lo:=1068126) (a:=390) (b:=391) r1068126 r1068516) (join_sums term (lo:=1068907) (a:=390) (b:=391) r1068907 r1069297)) (join_sums term (lo:=1069688) (a:=781) (b:=782) (join_sums term (lo:=1069688) (a:=390) (b:=391) r1069688 r1070078) (join_sums term (lo:=1070469) (a:=391) (b:=391) r1070469 r1070860)))) (join_sums term (lo:=1071251) (a:=3125) (b:=3125) (join_sums term (lo:=1071251) (a:=1562) (b:=1563) (join_sums term (lo:=1071251) (a:=781) (b:=781) (join_sums term (lo:=1071251) (a:=390) (b:=391) r1071251 r1071641) (join_sums term (lo:=1072032) (a:=390) (b:=391) r1072032 r1072422)) (join_sums term (lo:=1072813) (a:=781) (b:=782) (join_sums term (lo:=1072813) (a:=390) (b:=391) r1072813 r1073203) (join_sums term (lo:=1073594) (a:=391) (b:=391) r1073594 r1073985))) (join_sums term (lo:=1074376) (a:=1562) (b:=1563) (join_sums term (lo:=1074376) (a:=781) (b:=781) (join_sums term (lo:=1074376) (a:=390) (b:=391) r1074376 r1074766) (join_sums term (lo:=1075157) (a:=390) (b:=391) r1075157 r1075547)) (join_sums term (lo:=1075938) (a:=781) (b:=782) (join_sums term (lo:=1075938) (a:=390) (b:=391) r1075938 r1076328) (join_sums term (lo:=1076719) (a:=391) (b:=391) r1076719 r1077110))))) (join_sums term (lo:=1077501) (a:=6250) (b:=6250) (join_sums term (lo:=1077501) (a:=3125) (b:=3125) (join_sums term (lo:=1077501) (a:=1562) (b:=1563) (join_sums term (lo:=1077501) (a:=781) (b:=781) (join_sums term (lo:=1077501) (a:=390) (b:=391) r1077501 r1077891) (join_sums term (lo:=1078282) (a:=390) (b:=391) r1078282 r1078672)) (join_sums term (lo:=1079063) (a:=781) (b:=782) (join_sums term (lo:=1079063) (a:=390) (b:=391) r1079063 r1079453) (join_sums term (lo:=1079844) (a:=391) (b:=391) r1079844 r1080235))) (join_sums term (lo:=1080626) (a:=1562) (b:=1563) (join_sums term (lo:=1080626) (a:=781) (b:=781) (join_sums term (lo:=1080626) (a:=390) (b:=391) r1080626 r1081016) (join_sums term (lo:=1081407) (a:=390) (b:=391) r1081407 r1081797)) (join_sums term (lo:=1082188) (a:=781) (b:=782) (join_sums term (lo:=1082188) (a:=390) (b:=391) r1082188 r1082578) (join_sums term (lo:=1082969) (a:=391) (b:=391) r1082969 r1083360)))) (join_sums term (lo:=1083751) (a:=3125) (b:=3125) (join_sums term (lo:=1083751) (a:=1562) (b:=1563) (join_sums term (lo:=1083751) (a:=781) (b:=781) (join_sums term (lo:=1083751) (a:=390) (b:=391) r1083751 r1084141) (join_sums term (lo:=1084532) (a:=390) (b:=391) r1084532 r1084922)) (join_sums term (lo:=1085313) (a:=781) (b:=782) (join_sums term (lo:=1085313) (a:=390) (b:=391) r1085313 r1085703) (join_sums term (lo:=1086094) (a:=391) (b:=391) r1086094 r1086485))) (join_sums term (lo:=1086876) (a:=1562) (b:=1563) (join_sums term (lo:=1086876) (a:=781) (b:=781) (join_sums term (lo:=1086876) (a:=390) (b:=391) r1086876 r1087266) (join_sums term (lo:=1087657) (a:=390) (b:=391) r1087657 r1088047)) (join_sums term (lo:=1088438) (a:=781) (b:=782) (join_sums term (lo:=1088438) (a:=390) (b:=391) r1088438 r1088828) (join_sums term (lo:=1089219) (a:=391) (b:=391) r1089219 r1089610))))))))

private theorem rows : blockSum term 0 1090001 12362794193 :=
  join_sums term (lo:=0) (a:=990001) (b:=100000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 1090000).filter (990000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=12362794193 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From990000To1090000
