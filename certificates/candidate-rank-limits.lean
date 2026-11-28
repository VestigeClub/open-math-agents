import certificates.«first-63-candidate-exclusions»

/-!
# How many candidate indices can share the required prime ranks?

A candidate encodes an index and a slope. The rank at the corresponding
point must equal its index. The checked counts between points determine
which starting rank each candidate of a given slope would require.
-/
namespace CandidateRankLimits

def matchesWith (count : ℕ → ℕ) (e : ℕ) : Bool :=
  decide (count ((e%32)*(e/32+1322164)-20868473) = e/32)

noncomputable def rankMatches := matchesWith Nat.primeCounting

theorem rank_miss_iff (e : ℕ) : (¬rankMatches e) ↔ AbsoluteCandidateRanks.excluded e := by
  simp only [rankMatches,matchesWith,AbsoluteCandidateRanks.excluded,decide_eq_true_eq]


def first : List ℕ := [
    174075153, 174075345, 174075409, 174076561, 174076689,
    174076881, 174076945, 174078993, 174080529, 174081169,
    174081361, 174081553, 174081681, 174082449, 174083473,
    174083665, 174084241, 174084369, 174085201, 986922323,
    986923091, 986923987, 986924179, 986924627, 986924947,
    986926163, 986926547, 15152523830, 15152524150, 15152524246,
    15152524598, 15152524630, 15152524726, 15152525174, 15152525494,
    15152525558, 15152526166, 15152526326, 15152526550, 15152526838,
    15152527094, 15152527606, 15152528534, 15152528566, 15152528758,
    15152529206, 15152529238, 15152529590, 38951803543, 262101173401,
    262101173785, 262101173849, 262101174233, 262101174425, 262101175001,
    262101175129, 262101176089, 683254356346, 683254356858, 683254357210,
    683254357402, 683254357498, 683254357530]

def seventh : List ℕ := [
    12239439846429, 12239439847197, 12239439848797, 12239439849181, 12239439850077,
    12239439850461, 12239439851037, 12239439851229, 12239439852573, 12239439853341,
    12239439854557, 12239439855133, 12239439855261, 12239439855837, 12239439857821]

def eighth : List ℕ := [
    32117456688510, 32117456688766, 32117456688926, 32117456689438]

def candidates := first ++ seventh ++ eighth

private theorem zero_on_first (f : ℕ → Bool) (miss : ∀ e ∈ first, ¬f e) :
    first.countP f=0 :=
  (List.countP_eq_zero (l:=first) (p:=f)).mpr miss

private theorem at_window (count : ℕ → ℕ) {e q a delta need : ℕ}
    (arg : (e%32)*(e/32+1322164)-20868473=q)
    (window : count q=count a+delta) (index : e/32=need+delta) :
    matchesWith count e = decide (count a=need) := by
  have h : count ((e%32)*(e/32+1322164)-20868473)=e/32 ↔ count a=need := by
    rw [arg]
    omega
  simp only [matchesWith,h]

private def seventhRanks : List ℕ := [
    382482495200, 382482495194, 382482495189, 382482495188, 382482495185,
    382482495186, 382482495191, 382482495190, 382482495185, 382482495180,
    382482495179, 382482495182, 382482495182, 382482495183, 382482495197]

private theorem seventh_count (count : ℕ → ℕ)
    (h63 : count 11092009835083=count 11092009835083+0)
    (h64 : count 11092009835779=count 11092009835083+30)
    (h65 : count 11092009837229=count 11092009835083+85)
    (h66 : count 11092009837577=count 11092009835083+98)
    (h67 : count 11092009838389=count 11092009835083+129)
    (h68 : count 11092009838737=count 11092009835083+140)
    (h69 : count 11092009839259=count 11092009835083+153)
    (h70 : count 11092009839433=count 11092009835083+160)
    (h71 : count 11092009840651=count 11092009835083+207)
    (h72 : count 11092009841347=count 11092009835083+236)
    (h73 : count 11092009842449=count 11092009835083+275)
    (h74 : count 11092009842971=count 11092009835083+290)
    (h75 : count 11092009843087=count 11092009835083+294)
    (h76 : count 11092009843609=count 11092009835083+311)
    (h77 : count 11092009845407=count 11092009835083+359) :
    seventh.countP (matchesWith count) =
      seventhRanks.countP (fun v => decide (count 11092009835083=v)) := by
  have hit63 : matchesWith count 12239439846429 = decide (count 11092009835083=382482495200) :=
    at_window count (e:=12239439846429) (q:=11092009835083) (a:=11092009835083) (need:=382482495200) (delta:=0) rfl h63 rfl
  have hit64 : matchesWith count 12239439847197 = decide (count 11092009835083=382482495194) :=
    at_window count (e:=12239439847197) (q:=11092009835779) (a:=11092009835083) (need:=382482495194) (delta:=30) rfl h64 rfl
  have hit65 : matchesWith count 12239439848797 = decide (count 11092009835083=382482495189) :=
    at_window count (e:=12239439848797) (q:=11092009837229) (a:=11092009835083) (need:=382482495189) (delta:=85) rfl h65 rfl
  have hit66 : matchesWith count 12239439849181 = decide (count 11092009835083=382482495188) :=
    at_window count (e:=12239439849181) (q:=11092009837577) (a:=11092009835083) (need:=382482495188) (delta:=98) rfl h66 rfl
  have hit67 : matchesWith count 12239439850077 = decide (count 11092009835083=382482495185) :=
    at_window count (e:=12239439850077) (q:=11092009838389) (a:=11092009835083) (need:=382482495185) (delta:=129) rfl h67 rfl
  have hit68 : matchesWith count 12239439850461 = decide (count 11092009835083=382482495186) :=
    at_window count (e:=12239439850461) (q:=11092009838737) (a:=11092009835083) (need:=382482495186) (delta:=140) rfl h68 rfl
  have hit69 : matchesWith count 12239439851037 = decide (count 11092009835083=382482495191) :=
    at_window count (e:=12239439851037) (q:=11092009839259) (a:=11092009835083) (need:=382482495191) (delta:=153) rfl h69 rfl
  have hit70 : matchesWith count 12239439851229 = decide (count 11092009835083=382482495190) :=
    at_window count (e:=12239439851229) (q:=11092009839433) (a:=11092009835083) (need:=382482495190) (delta:=160) rfl h70 rfl
  have hit71 : matchesWith count 12239439852573 = decide (count 11092009835083=382482495185) :=
    at_window count (e:=12239439852573) (q:=11092009840651) (a:=11092009835083) (need:=382482495185) (delta:=207) rfl h71 rfl
  have hit72 : matchesWith count 12239439853341 = decide (count 11092009835083=382482495180) :=
    at_window count (e:=12239439853341) (q:=11092009841347) (a:=11092009835083) (need:=382482495180) (delta:=236) rfl h72 rfl
  have hit73 : matchesWith count 12239439854557 = decide (count 11092009835083=382482495179) :=
    at_window count (e:=12239439854557) (q:=11092009842449) (a:=11092009835083) (need:=382482495179) (delta:=275) rfl h73 rfl
  have hit74 : matchesWith count 12239439855133 = decide (count 11092009835083=382482495182) :=
    at_window count (e:=12239439855133) (q:=11092009842971) (a:=11092009835083) (need:=382482495182) (delta:=290) rfl h74 rfl
  have hit75 : matchesWith count 12239439855261 = decide (count 11092009835083=382482495182) :=
    at_window count (e:=12239439855261) (q:=11092009843087) (a:=11092009835083) (need:=382482495182) (delta:=294) rfl h75 rfl
  have hit76 : matchesWith count 12239439855837 = decide (count 11092009835083=382482495183) :=
    at_window count (e:=12239439855837) (q:=11092009843609) (a:=11092009835083) (need:=382482495183) (delta:=311) rfl h76 rfl
  have hit77 : matchesWith count 12239439857821 = decide (count 11092009835083=382482495197) :=
    at_window count (e:=12239439857821) (q:=11092009845407) (a:=11092009835083) (need:=382482495197) (delta:=359) rfl h77 rfl
  simp only [seventh,seventhRanks,List.countP_cons,List.countP_nil,
    hit63,hit64,hit65,hit66,hit67,hit68,hit69,hit70,hit71,hit72,hit73,hit74,hit75,hit76,hit77]

private theorem seventh_maximum (v : ℕ) :
    seventhRanks.countP (fun t => decide (v=t)) ≤ 2 := by
  by_cases h0 : v=382482495179
  · subst v
    decide
  by_cases h1 : v=382482495180
  · subst v
    decide
  by_cases h2 : v=382482495182
  · subst v
    decide
  by_cases h3 : v=382482495183
  · subst v
    decide
  by_cases h4 : v=382482495185
  · subst v
    decide
  by_cases h5 : v=382482495186
  · subst v
    decide
  by_cases h6 : v=382482495188
  · subst v
    decide
  by_cases h7 : v=382482495189
  · subst v
    decide
  by_cases h8 : v=382482495190
  · subst v
    decide
  by_cases h9 : v=382482495191
  · subst v
    decide
  by_cases h10 : v=382482495194
  · subst v
    decide
  by_cases h11 : v=382482495197
  · subst v
    decide
  by_cases h12 : v=382482495200
  · subst v
    decide
  simp [seventhRanks,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12]

private theorem seventh_residue (v : ℕ) (h : v%9=7) :
    seventhRanks.countP (fun t => decide (v=t)) = 0 := by
  have h0 : v≠382482495179 := by omega
  have h1 : v≠382482495180 := by omega
  have h2 : v≠382482495182 := by omega
  have h3 : v≠382482495183 := by omega
  have h4 : v≠382482495185 := by omega
  have h5 : v≠382482495186 := by omega
  have h6 : v≠382482495188 := by omega
  have h7 : v≠382482495189 := by omega
  have h8 : v≠382482495190 := by omega
  have h9 : v≠382482495191 := by omega
  have h10 : v≠382482495194 := by omega
  have h11 : v≠382482495197 := by omega
  have h12 : v≠382482495200 := by omega
  simp [seventhRanks,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12]

private def eighthRanks : List ℕ := [
    1003670521515, 1003670521511, 1003670521512, 1003670521509]

private theorem eighth_count (count : ℕ → ℕ)
    (h78 : count 30110134441897=count 30110134441897+0)
    (h79 : count 30110134442137=count 30110134441897+12)
    (h80 : count 30110134442287=count 30110134441897+16)
    (h81 : count 30110134442767=count 30110134441897+35) :
    eighth.countP (matchesWith count) =
      eighthRanks.countP (fun v => decide (count 30110134441897=v)) := by
  have hit78 : matchesWith count 32117456688510 = decide (count 30110134441897=1003670521515) :=
    at_window count (e:=32117456688510) (q:=30110134441897) (a:=30110134441897) (need:=1003670521515) (delta:=0) rfl h78 rfl
  have hit79 : matchesWith count 32117456688766 = decide (count 30110134441897=1003670521511) :=
    at_window count (e:=32117456688766) (q:=30110134442137) (a:=30110134441897) (need:=1003670521511) (delta:=12) rfl h79 rfl
  have hit80 : matchesWith count 32117456688926 = decide (count 30110134441897=1003670521512) :=
    at_window count (e:=32117456688926) (q:=30110134442287) (a:=30110134441897) (need:=1003670521512) (delta:=16) rfl h80 rfl
  have hit81 : matchesWith count 32117456689438 = decide (count 30110134441897=1003670521509) :=
    at_window count (e:=32117456689438) (q:=30110134442767) (a:=30110134441897) (need:=1003670521509) (delta:=35) rfl h81 rfl
  simp only [eighth,eighthRanks,List.countP_cons,List.countP_nil,
    hit78,hit79,hit80,hit81]

private theorem eighth_maximum (v : ℕ) :
    eighthRanks.countP (fun t => decide (v=t)) ≤ 1 := by
  by_cases h0 : v=1003670521509
  · subst v
    decide
  by_cases h1 : v=1003670521511
  · subst v
    decide
  by_cases h2 : v=1003670521512
  · subst v
    decide
  by_cases h3 : v=1003670521515
  · subst v
    decide
  simp [eighthRanks,h0,h1,h2,h3]

private theorem eighth_residue (v : ℕ) (h : v%5=3) :
    eighthRanks.countP (fun t => decide (v=t)) = 0 := by
  have h0 : v≠1003670521509 := by omega
  have h1 : v≠1003670521511 := by omega
  have h2 : v≠1003670521512 := by omega
  have h3 : v≠1003670521515 := by omega
  simp [eighthRanks,h0,h1,h2,h3]

private theorem consistent_counts (f : ℕ → Bool) (s t : ℕ)
    (hfirst : first.countP f=0)
    (hseven : seventh.countP f=seventhRanks.countP (fun v => decide (s=v)))
    (height : eighth.countP f=eighthRanks.countP (fun v => decide (t=v))) :
    (candidates.countP f ≤ 3) ∧
    (79 ≤ candidates.countP (fun e => ¬f e)) ∧
    (s%9=7 → t%5=3 → candidates.countP f=0) := by
  have total : candidates.countP f = 0 + (seventh.countP f + eighth.countP f) := by
    simp only [candidates,List.countP_append,hfirst,Nat.add_assoc]
  have left := seventh_maximum s
  have right := eighth_maximum t
  have bound : candidates.countP f ≤ 3 := by omega
  have full := List.length_eq_countP_add_countP (l:=candidates) f
  have size : candidates.length=82 := rfl
  refine ⟨bound,by omega,?_⟩
  intro hs ht
  have none_s := seventh_residue s hs
  have none_t := eighth_residue t ht
  omega

/-- The 82 indices are distinct. At most three can match simultaneously.
The two displayed prime-count residues would exclude all of them. -/
theorem candidate_bounds :
    (candidates.length=82 ∧ candidates.Nodup) ∧
    (candidates.countP rankMatches ≤ 3) ∧
    (79 ≤ candidates.countP (fun e => ¬rankMatches e)) ∧
    (Nat.primeCounting 11092009835083 % 9 = 7 →
      Nat.primeCounting 30110134441897 % 5 = 3 →
      ∀ e ∈ candidates, AbsoluteCandidateRanks.excluded e) := by
  have first_ok : first.countP rankMatches=0 :=
    zero_on_first rankMatches (fun e he =>
      (rank_miss_iff e).mpr (CertifiedCandidateExclusions.first_63 e he))
  have limits := consistent_counts rankMatches
    (Nat.primeCounting 11092009835083) (Nat.primeCounting 30110134441897) first_ok
    (seventh_count Nat.primeCounting
      WindowRanks.a11092009835083 WindowRanks.a11092009835779 WindowRanks.a11092009837229
      WindowRanks.a11092009837577 WindowRanks.a11092009838389 WindowRanks.a11092009838737
      WindowRanks.a11092009839259 WindowRanks.a11092009839433 WindowRanks.a11092009840651
      WindowRanks.a11092009841347 WindowRanks.a11092009842449 WindowRanks.a11092009842971
      WindowRanks.a11092009843087 WindowRanks.a11092009843609 WindowRanks.a11092009845407)
    (eighth_count Nat.primeCounting
      WindowRanks.a30110134441897 WindowRanks.a30110134442137 WindowRanks.a30110134442287
      WindowRanks.a30110134442767)
  refine ⟨⟨rfl,by decide +kernel⟩,limits.1,limits.2.1,?_⟩
  intro hs ht e he
  exact (rank_miss_iff e).mp
    ((List.countP_eq_zero (l:=candidates) (p:=rankMatches)).mp (limits.2.2 hs ht) e he)

end CandidateRankLimits
