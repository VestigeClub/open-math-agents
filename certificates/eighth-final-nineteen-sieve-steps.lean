import certificates.«eighth-prime-count-sieve-remainder»
import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-950000000-975000000»

/-! The last 19 primes at the eighth endpoint, including the gap from 31,091 to the cube-root cutoff. -/

/- Exact changes for sieve primes 3332 through 3343. -/
open Finset
namespace Tail30110134441897From30881To31033

set_option maxRecDepth 16000 in
private theorem row30893 :
    FinalSeventhSieve.rough 30110134441897 30893+49621482=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.row (p:=30893) (q:=974658804) (s:=31219) (rank:=49623760) (tiny:=3331) (pairs:=1052)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 974658804 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row30911 :
    FinalSeventhSieve.rough 30110134441897 30911+49594025=FinalSeventhSieve.rough 30110134441897 30893 :=
  LargeQuotientSieve.row (p:=30911) (q:=974091243) (s:=31210) (rank:=49596418) (tiny:=3332) (pairs:=938)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 974091243 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30911 : FinalSeventhSieve.rough 30110134441897 30911+99215507=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.combine row30893 row30911 rfl

set_option maxRecDepth 16000 in
private theorem row30931 :
    FinalSeventhSieve.rough 30110134441897 30931+49563385=FinalSeventhSieve.rough 30110134441897 30911 :=
  LargeQuotientSieve.row (p:=30931) (q:=973461396) (s:=31200) (rank:=49565902) (tiny:=3333) (pairs:=815)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 973461396 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30931 : FinalSeventhSieve.rough 30110134441897 30931+148778892=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.combine to30911 row30931 rfl

set_option maxRecDepth 16000 in
private theorem row30937 :
    FinalSeventhSieve.rough 30110134441897 30937+49554200=FinalSeventhSieve.rough 30110134441897 30931 :=
  LargeQuotientSieve.row (p:=30937) (q:=973272600) (s:=31197) (rank:=49556793) (tiny:=3334) (pairs:=740)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 973272600 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30937 : FinalSeventhSieve.rough 30110134441897 30937+198333092=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.combine to30931 row30937 rfl

set_option maxRecDepth 16000 in
private theorem row30941 :
    FinalSeventhSieve.rough 30110134441897 30941+49548066=FinalSeventhSieve.rough 30110134441897 30937 :=
  LargeQuotientSieve.row (p:=30941) (q:=973146777) (s:=31195) (rank:=49550716) (tiny:=3335) (pairs:=684)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 973146777 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30941 : FinalSeventhSieve.rough 30110134441897 30941+247881158=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.combine to30937 row30941 rfl

set_option maxRecDepth 16000 in
private theorem row30949 :
    FinalSeventhSieve.rough 30110134441897 30949+49535948=FinalSeventhSieve.rough 30110134441897 30941 :=
  LargeQuotientSieve.row (p:=30949) (q:=972895228) (s:=31191) (rank:=49538668) (tiny:=3336) (pairs:=615)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 972895228 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30949 : FinalSeventhSieve.rough 30110134441897 30949+297417106=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.combine to30941 row30949 rfl

set_option maxRecDepth 16000 in
private theorem row30971 :
    FinalSeventhSieve.rough 30110134441897 30971+49502536=FinalSeventhSieve.rough 30110134441897 30949 :=
  LargeQuotientSieve.row (p:=30971) (q:=972204140) (s:=31180) (rank:=49505365) (tiny:=3337) (pairs:=507)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 972204140 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30971 : FinalSeventhSieve.rough 30110134441897 30971+346919642=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.combine to30949 row30971 rfl

set_option maxRecDepth 16000 in
private theorem row30977 :
    FinalSeventhSieve.rough 30110134441897 30977+49493378=FinalSeventhSieve.rough 30110134441897 30971 :=
  LargeQuotientSieve.row (p:=30977) (q:=972015832) (s:=31177) (rank:=49496267) (tiny:=3338) (pairs:=448)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 972015832 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30977 : FinalSeventhSieve.rough 30110134441897 30977+396413020=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.combine to30971 row30977 rfl

set_option maxRecDepth 16000 in
private theorem row30983 :
    FinalSeventhSieve.rough 30110134441897 30983+49484223=FinalSeventhSieve.rough 30110134441897 30977 :=
  LargeQuotientSieve.row (p:=30983) (q:=971827597) (s:=31174) (rank:=49487166) (tiny:=3339) (pairs:=395)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 971827597 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to30983 : FinalSeventhSieve.rough 30110134441897 30983+445897243=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.combine to30977 row30983 rfl

set_option maxRecDepth 16000 in
private theorem row31013 :
    FinalSeventhSieve.rough 30110134441897 31013+49438777=FinalSeventhSieve.rough 30110134441897 30983 :=
  LargeQuotientSieve.row (p:=31013) (q:=970887513) (s:=31159) (rank:=49441826) (tiny:=3340) (pairs:=290)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 970887513 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to31013 : FinalSeventhSieve.rough 30110134441897 31013+495336020=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.combine to30983 row31013 rfl

set_option maxRecDepth 16000 in
private theorem row31019 :
    FinalSeventhSieve.rough 30110134441897 31019+49429594=FinalSeventhSieve.rough 30110134441897 31013 :=
  LargeQuotientSieve.row (p:=31019) (q:=970699714) (s:=31156) (rank:=49432689) (tiny:=3341) (pairs:=245)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 970699714 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to31019 : FinalSeventhSieve.rough 30110134441897 31019+544765614=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.combine to31013 row31019 rfl

set_option maxRecDepth 16000 in
private theorem row31033 :
    FinalSeventhSieve.rough 30110134441897 31033+49408344=FinalSeventhSieve.rough 30110134441897 31019 :=
  LargeQuotientSieve.row (p:=31033) (q:=970261800) (s:=31149) (rank:=49411505) (tiny:=3342) (pairs:=180)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 970261800 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to31033 : FinalSeventhSieve.rough 30110134441897 31033+594173958=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.combine to31019 row31033 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 31033+594173958=FinalSeventhSieve.rough 30110134441897 30881 := to31033

end Tail30110134441897From30881To31033

/- Exact changes for sieve primes 3344 through 3350. -/
open Finset
namespace Tail30110134441897From31033To31091

set_option maxRecDepth 16000 in
private theorem row31039 :
    FinalSeventhSieve.rough 30110134441897 31039+49399214=FinalSeventhSieve.rough 30110134441897 31033 :=
  LargeQuotientSieve.row (p:=31039) (q:=970074243) (s:=31146) (rank:=49402412) (tiny:=3343) (pairs:=144)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 970074243 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row31051 :
    FinalSeventhSieve.rough 30110134441897 31051+49381084=FinalSeventhSieve.rough 30110134441897 31039 :=
  LargeQuotientSieve.row (p:=31051) (q:=969699347) (s:=31139) (rank:=49384320) (tiny:=3344) (pairs:=107)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 969699347 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to31051 : FinalSeventhSieve.rough 30110134441897 31051+98780298=FinalSeventhSieve.rough 30110134441897 31033 :=
  LargeQuotientSieve.combine row31039 row31051 rfl

set_option maxRecDepth 16000 in
private theorem row31063 :
    FinalSeventhSieve.rough 30110134441897 31063+49362933=FinalSeventhSieve.rough 30110134441897 31051 :=
  LargeQuotientSieve.row (p:=31063) (q:=969324741) (s:=31133) (rank:=49366204) (tiny:=3345) (pairs:=73)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 969324741 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to31063 : FinalSeventhSieve.rough 30110134441897 31063+148143231=FinalSeventhSieve.rough 30110134441897 31033 :=
  LargeQuotientSieve.combine to31051 row31063 rfl

set_option maxRecDepth 16000 in
private theorem row31069 :
    FinalSeventhSieve.rough 30110134441897 31069+49353788=FinalSeventhSieve.rough 30110134441897 31063 :=
  LargeQuotientSieve.row (p:=31069) (q:=969137546) (s:=31130) (rank:=49357081) (tiny:=3346) (pairs:=52)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 969137546 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to31069 : FinalSeventhSieve.rough 30110134441897 31069+197497019=FinalSeventhSieve.rough 30110134441897 31033 :=
  LargeQuotientSieve.combine to31063 row31069 rfl

set_option maxRecDepth 16000 in
private theorem row31079 :
    FinalSeventhSieve.rough 30110134441897 31079+49338708=FinalSeventhSieve.rough 30110134441897 31069 :=
  LargeQuotientSieve.row (p:=31079) (q:=968825716) (s:=31125) (rank:=49342024) (tiny:=3347) (pairs:=30)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 968825716 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to31079 : FinalSeventhSieve.rough 30110134441897 31079+246835727=FinalSeventhSieve.rough 30110134441897 31033 :=
  LargeQuotientSieve.combine to31069 row31079 rfl

set_option maxRecDepth 16000 in
private theorem row31081 :
    FinalSeventhSieve.rough 30110134441897 31081+49335676=FinalSeventhSieve.rough 30110134441897 31079 :=
  LargeQuotientSieve.row (p:=31081) (q:=968763374) (s:=31124) (rank:=49339004) (tiny:=3348) (pairs:=19)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 968763374 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to31081 : FinalSeventhSieve.rough 30110134441897 31081+296171403=FinalSeventhSieve.rough 30110134441897 31033 :=
  LargeQuotientSieve.combine to31079 row31081 rfl

set_option maxRecDepth 16000 in
private theorem row31091 :
    FinalSeventhSieve.rough 30110134441897 31091+49320618=FinalSeventhSieve.rough 30110134441897 31081 :=
  LargeQuotientSieve.row (p:=31091) (q:=968451784) (s:=31119) (rank:=49323961) (tiny:=3349) (pairs:=5)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ950000000To975000000.count_correct 968451784 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to31091 : FinalSeventhSieve.rough 30110134441897 31091+345492021=FinalSeventhSieve.rough 30110134441897 31033 :=
  LargeQuotientSieve.combine to31081 row31091 rfl

theorem change : FinalSeventhSieve.rough 30110134441897 31091+345492021=FinalSeventhSieve.rough 30110134441897 31033 := to31091

end Tail30110134441897From31033To31091

/- Exact changes for the consecutive sieve primes from 30,881 to 31,091. -/
namespace TailSeries30110134441897From30881To31091

theorem change : FinalSeventhSieve.rough 30110134441897 31091+939665979=FinalSeventhSieve.rough 30110134441897 30881 :=
  LargeQuotientSieve.combine Tail30110134441897From30881To31033.change Tail30110134441897From31033To31091.change rfl

end TailSeries30110134441897From30881To31091

open Finset
namespace EighthEndpointSieve

private theorem same_primes {y z : ℕ} (le : y ≤ z) (cap : z ≤ 745089)
    (gap : ∀ r ∈ Icc (y+1) z, FastDenseA26.prime r = false) :
    Nat.primesLE y = Nat.primesLE z := by
  ext p
  simp only [Nat.mem_primesLE]
  constructor
  · rintro ⟨h, pr⟩
    exact ⟨h.trans le,pr⟩
  · rintro ⟨h, pr⟩
    refine ⟨?_,pr⟩
    by_contra! above
    have hfalse := gap p (mem_Icc.mpr ⟨by omega,h⟩)
    have htrue := (FastDenseA26.prime_ok p (h.trans cap)).mpr pr
    simp [hfalse] at htrue

private theorem last_prime : Nat.primesLE 31091 = Nat.primesLE 31110 :=
  same_primes (y:=31091) (z:=31110) (by decide) (by decide) (by decide +kernel)

private theorem rough_eq {x y z : ℕ} (h : Nat.primesLE y=Nat.primesLE z) :
    FinalSeventhSieve.rough x y=FinalSeventhSieve.rough x z := by
  exact congrArg (fun primes : Finset ℕ =>
    ((Icc 1 x).filter (fun n => ∀ p ∈ primes, ¬p∣n)).card) h

private theorem change_cut {a b c k : ℕ} (sum : a+k=c) (eq : a=b) : b+k=c :=
  eq ▸ sum

theorem final_nineteen : FinalSeventhSieve.rough 30110134441897 31110 + 939665979 =
    FinalSeventhSieve.rough 30110134441897 30881 :=
  change_cut (a:=FinalSeventhSieve.rough 30110134441897 31091)
    (b:=FinalSeventhSieve.rough 30110134441897 31110)
    (c:=FinalSeventhSieve.rough 30110134441897 30881) (k:=939665979)
    TailSeries30110134441897From30881To31091.change
    (rough_eq (x:=30110134441897) (y:=31091) (z:=31110) last_prime)

private theorem mod_five (a b : ℕ) (h : a+939665979=b) : (a%5=3 ↔ b%5=2) := by omega

private theorem read_residue {x y : ℕ} (h : criterion x y) :
    (Nat.primeCounting x%5=3 ↔ FinalSeventhSieve.rough x y%5=3) := h.2.1

theorem earlier_residue :
    (Nat.primeCounting 30110134441897 % 5 = 3 ↔
      FinalSeventhSieve.rough 30110134441897 30881 % 5 = 2) :=
  (read_residue (x:=30110134441897) (y:=31110) prime_count_and_residue).trans
    (mod_five (FinalSeventhSieve.rough 30110134441897 31110)
      (FinalSeventhSieve.rough 30110134441897 30881) final_nineteen)

end EighthEndpointSieve
