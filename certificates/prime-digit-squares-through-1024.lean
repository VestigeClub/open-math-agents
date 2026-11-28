import Mathlib

/-! The two exceptional decimal digit-square sums for primes. -/
namespace DigitSquarePrimes

def squareSum (n : ℕ) : ℕ := ((Nat.digits 10 n).map (fun d => d^2)).sum

private lemma small_digits (ds : List ℕ)
    (h : (ds.map (fun d => d^2)).sum ≤ 3) :
    ds.sum = (ds.map (fun d => d^2)).sum := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.map_cons,List.sum_cons] at h ⊢
    have hd : d ≤ 1 := by
      by_contra! greater
      have bound := Nat.pow_le_pow_left (show 2 ≤ d by omega) 2
      omega
    have same : d^2=d := by interval_cases d <;> rfl
    rw [same,ih (by omega)]

private lemma value_zero (ds : List ℕ) (h : ds.sum=0) : Nat.ofDigits 10 ds=0 := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.sum_cons] at h
    rw [Nat.ofDigits_cons,ih (by omega)]
    omega

theorem exceptions (p : ℕ) (hp : p.Prime) : squareSum p ≠ 1 ∧ squareSum p ≠ 3 := by
  have old := Nat.ofDigits_digits 10 p
  constructor
  · intro one
    have hs : (Nat.digits 10 p).sum=1 := (small_digits _ (by change squareSum p ≤ 3; omega)).trans one
    cases ds : Nat.digits 10 p with
    | nil => simp [ds] at hs
    | cons d rest =>
      rw [ds,List.sum_cons] at hs
      rw [ds,Nat.ofDigits_cons] at old
      by_cases hd : d=0
      · have div : 10 ∣ p := ⟨Nat.ofDigits 10 rest,by simpa [hd] using old.symm⟩
        have two : 2=p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
          (dvd_trans (by decide : 2 ∣ 10) div)
        rw [←two] at div
        exact (by decide : ¬10 ∣ 2) div
      · rw [value_zero rest (by omega)] at old
        have := hp.two_le
        omega
  · intro three
    have hs : (Nat.digits 10 p).sum=3 := (small_digits _ (by change squareSum p ≤ 3; omega)).trans three
    have div : 3 ∣ p := (Nat.three_dvd_iff p).mpr (by simpa only [hs] using (dvd_refl 3))
    have eq : 3=p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp div
    rw [←eq] at three
    exact (by decide : squareSum 3 ≠ 3) three



def remPower (p a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1%p
  | f+1, e =>
    let v := remPower p a f (e/2)
    (v^2*(if e%2=1 then a else 1))%p

private theorem rem_bound (p a f e : ℕ) (hp : 0 < p) : remPower p a f e < p := by
  cases f <;> exact Nat.mod_lt _ hp

private theorem rem_cast (p a f e : ℕ) (bound : e < 2^f) :
    ((remPower p a f e : ℕ) : ZMod p) = (a:ZMod p)^e := by
  induction f generalizing e with
  | zero =>
    have eq : e=0 := by simpa using bound
    subst e
    simp [remPower,ZMod.natCast_mod]
  | succ f ih =>
    have half : e/2 < 2^f := by rw [pow_succ] at bound; omega
    rw [remPower,ZMod.natCast_mod,Nat.cast_mul,Nat.cast_pow,ih _ half,←pow_mul]
    by_cases bit : e%2=1
    · rw [if_pos bit,←pow_succ]
      congr 1
      omega
    · rw [if_neg bit,Nat.cast_one,mul_one]
      congr 1
      omega

private theorem rem_one (p a f e : ℕ) (hp : 1 < p) (h : e < 2^f) :
    (a:ZMod p)^e=1 ↔ remPower p a f e=1 := by
  rw [←rem_cast p a f e h]
  simpa only [Nat.cast_one,Nat.mod_eq_of_lt (rem_bound p a f e (by omega)),Nat.mod_eq_of_lt hp]
    using ZMod.natCast_eq_natCast_iff' (remPower p a f e) 1 p

def factorProduct (fs : List (ℕ×ℕ)) : ℕ := (fs.map fun v => v.1^v.2).prod

private theorem prime_factor_mem (q : ℕ) (hq : q.Prime) (fs : List (ℕ×ℕ))
    (primes : ∀ n ∈ fs.map Prod.fst, n.Prime) (h : q ∣ factorProduct fs) :
    q ∈ fs.map Prod.fst := by
  induction fs with
  | nil => simp [factorProduct,hq.not_dvd_one] at h
  | cons v tail ih =>
    change q ∣ v.1^v.2*factorProduct tail at h
    rcases hq.dvd_mul.mp h with left|right
    · have he := Nat.prime_eq_prime_of_dvd_pow hq (primes _ (by simp)) left
      simp [he]
    · exact List.mem_cons_of_mem _ (ih (fun p h => primes p (List.mem_cons_of_mem _ h)) right)

def primeData (p a : ℕ) (fs : List (ℕ×ℕ)) : Bool :=
  decide (1 < p ∧ p < 2^64 ∧ factorProduct fs = p-1 ∧ remPower p a 64 (p-1)=1) &&
    fs.all (fun v => remPower p a 64 ((p-1)/v.1) != 1)

theorem lucasData (p a : ℕ) (fs : List (ℕ×ℕ))
    (primes : ∀ q ∈ fs.map Prod.fst, q.Prime) (data : primeData p a fs=true) : p.Prime := by
  simp only [primeData,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at data
  obtain ⟨⟨hp,cap,hf,main⟩,rest⟩ := data
  apply lucas_primality p (a:ZMod p)
  · exact (rem_one _ _ _ _ hp (by omega)).mpr main
  · intro q hq hd
    have memb := prime_factor_mem q hq fs primes (hf ▸ hd)
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp memb
    subst q
    have nz := rest v hv
    have small := Nat.div_le_self (p-1) v.1
    intro eq
    have no : remPower p a 64 ((p-1)/v.1) ≠ 1 := by simpa using nz
    exact no ((rem_one p a 64 _ hp (by omega)).mp eq)

abbrev Certified := {n : ℕ // n.Prime}

def certifiedPrime (p a : ℕ) (factors : List (Certified×ℕ))
    (check : primeData p a (factors.map fun v => (v.1.val,v.2))=true) : Certified :=
  ⟨p, lucasData p a _ (by
    intro q hq
    obtain ⟨t,ht,eq⟩ := List.mem_map.mp hq
    obtain ⟨d,_,rfl⟩ := List.mem_map.mp ht
    exact eq ▸ d.1.property) check⟩



private def p2 : Certified := ⟨2,by decide +kernel⟩

private def p3 : Certified := ⟨3,by decide +kernel⟩

private def p5 : Certified := ⟨5,by decide +kernel⟩

private def p7 : Certified := ⟨7,by decide +kernel⟩

private def p11 : Certified := ⟨11,by decide +kernel⟩

private def p13 : Certified := ⟨13,by decide +kernel⟩

private def p17 : Certified := ⟨17,by decide +kernel⟩

private def p19 : Certified := ⟨19,by decide +kernel⟩

private def p23 : Certified := ⟨23,by decide +kernel⟩

private def p29 : Certified := ⟨29,by decide +kernel⟩

private def p31 : Certified := ⟨31,by decide +kernel⟩

private def p37 : Certified := ⟨37,by decide +kernel⟩

private def p41 : Certified := ⟨41,by decide +kernel⟩

private def p43 : Certified := ⟨43,by decide +kernel⟩

private def p47 : Certified := ⟨47,by decide +kernel⟩

private def p53 : Certified := ⟨53,by decide +kernel⟩

private def p59 : Certified := ⟨59,by decide +kernel⟩

private def p61 : Certified := ⟨61,by decide +kernel⟩

private def p67 : Certified := ⟨67,by decide +kernel⟩

private def p71 : Certified := ⟨71,by decide +kernel⟩

private def p73 : Certified := ⟨73,by decide +kernel⟩

private def p79 : Certified := ⟨79,by decide +kernel⟩

private def p83 : Certified := ⟨83,by decide +kernel⟩

private def p89 : Certified := ⟨89,by decide +kernel⟩

private def p97 : Certified := ⟨97,by decide +kernel⟩

private def p101 : Certified := ⟨101,by decide +kernel⟩

private def p103 : Certified := ⟨103,by decide +kernel⟩

private def p107 : Certified := ⟨107,by decide +kernel⟩

private def p109 : Certified := ⟨109,by decide +kernel⟩

private def p113 : Certified := ⟨113,by decide +kernel⟩

private def p127 : Certified := ⟨127,by decide +kernel⟩

private def p131 : Certified := ⟨131,by decide +kernel⟩

private def p137 : Certified := ⟨137,by decide +kernel⟩

private def p139 : Certified := ⟨139,by decide +kernel⟩

private def p149 : Certified := ⟨149,by decide +kernel⟩

private def p151 : Certified := ⟨151,by decide +kernel⟩

private def p157 : Certified := ⟨157,by decide +kernel⟩

private def p163 : Certified := ⟨163,by decide +kernel⟩

private def p167 : Certified := ⟨167,by decide +kernel⟩

private def p173 : Certified := ⟨173,by decide +kernel⟩

private def p179 : Certified := ⟨179,by decide +kernel⟩

private def p181 : Certified := ⟨181,by decide +kernel⟩

private def p191 : Certified := ⟨191,by decide +kernel⟩

private def p193 : Certified := ⟨193,by decide +kernel⟩

private def p197 : Certified := ⟨197,by decide +kernel⟩

private def p199 : Certified := ⟨199,by decide +kernel⟩

private def p211 : Certified := ⟨211,by decide +kernel⟩

private def p223 : Certified := ⟨223,by decide +kernel⟩

private def p227 : Certified := ⟨227,by decide +kernel⟩

private def p229 : Certified := ⟨229,by decide +kernel⟩

private def p233 : Certified := ⟨233,by decide +kernel⟩

private def p239 : Certified := ⟨239,by decide +kernel⟩

private def p241 : Certified := ⟨241,by decide +kernel⟩

private def p251 : Certified := ⟨251,by decide +kernel⟩

private def p257 : Certified := ⟨257,by decide +kernel⟩

private def p263 : Certified := ⟨263,by decide +kernel⟩

private def p269 : Certified := ⟨269,by decide +kernel⟩

private def p271 : Certified := ⟨271,by decide +kernel⟩

private def p277 : Certified := ⟨277,by decide +kernel⟩

private def p281 : Certified := ⟨281,by decide +kernel⟩

private def p283 : Certified := ⟨283,by decide +kernel⟩

private def p293 : Certified := ⟨293,by decide +kernel⟩

private def p307 : Certified := ⟨307,by decide +kernel⟩

private def p311 : Certified := ⟨311,by decide +kernel⟩

private def p313 : Certified := ⟨313,by decide +kernel⟩

private def p317 : Certified := ⟨317,by decide +kernel⟩

private def p331 : Certified := ⟨331,by decide +kernel⟩

private def p337 : Certified := ⟨337,by decide +kernel⟩

private def p347 : Certified := ⟨347,by decide +kernel⟩

private def p349 : Certified := ⟨349,by decide +kernel⟩

private def p353 : Certified := ⟨353,by decide +kernel⟩

private def p359 : Certified := ⟨359,by decide +kernel⟩

private def p367 : Certified := ⟨367,by decide +kernel⟩

private def p373 : Certified := ⟨373,by decide +kernel⟩

private def p379 : Certified := ⟨379,by decide +kernel⟩

private def p383 : Certified := ⟨383,by decide +kernel⟩

private def p389 : Certified := ⟨389,by decide +kernel⟩

private def p397 : Certified := ⟨397,by decide +kernel⟩

private def p401 := certifiedPrime 401 3 [(p2,4),(p5,2)] (by decide +kernel)

private def p409 := certifiedPrime 409 21 [(p2,3),(p3,1),(p17,1)] (by decide +kernel)

private def p419 := certifiedPrime 419 2 [(p2,1),(p11,1),(p19,1)] (by decide +kernel)

private def p421 := certifiedPrime 421 2 [(p2,2),(p3,1),(p5,1),(p7,1)] (by decide +kernel)

private def p431 := certifiedPrime 431 7 [(p2,1),(p5,1),(p43,1)] (by decide +kernel)

private def p433 := certifiedPrime 433 5 [(p2,4),(p3,3)] (by decide +kernel)

private def p439 := certifiedPrime 439 15 [(p2,1),(p3,1),(p73,1)] (by decide +kernel)

private def p443 := certifiedPrime 443 2 [(p2,1),(p13,1),(p17,1)] (by decide +kernel)

private def p449 := certifiedPrime 449 3 [(p2,6),(p7,1)] (by decide +kernel)

private def p457 := certifiedPrime 457 13 [(p2,3),(p3,1),(p19,1)] (by decide +kernel)

private def p461 := certifiedPrime 461 2 [(p2,2),(p5,1),(p23,1)] (by decide +kernel)

private def p463 := certifiedPrime 463 3 [(p2,1),(p3,1),(p7,1),(p11,1)] (by decide +kernel)

private def p467 := certifiedPrime 467 2 [(p2,1),(p233,1)] (by decide +kernel)

private def p479 := certifiedPrime 479 13 [(p2,1),(p239,1)] (by decide +kernel)

private def p487 := certifiedPrime 487 3 [(p2,1),(p3,5)] (by decide +kernel)

private def p491 := certifiedPrime 491 2 [(p2,1),(p5,1),(p7,2)] (by decide +kernel)

private def p499 := certifiedPrime 499 7 [(p2,1),(p3,1),(p83,1)] (by decide +kernel)

private def p503 := certifiedPrime 503 5 [(p2,1),(p251,1)] (by decide +kernel)

private def p509 := certifiedPrime 509 2 [(p2,2),(p127,1)] (by decide +kernel)

private def p521 := certifiedPrime 521 3 [(p2,3),(p5,1),(p13,1)] (by decide +kernel)

private def p523 := certifiedPrime 523 2 [(p2,1),(p3,2),(p29,1)] (by decide +kernel)

private def p541 := certifiedPrime 541 2 [(p2,2),(p3,3),(p5,1)] (by decide +kernel)

private def p547 := certifiedPrime 547 2 [(p2,1),(p3,1),(p7,1),(p13,1)] (by decide +kernel)

private def p557 := certifiedPrime 557 2 [(p2,2),(p139,1)] (by decide +kernel)

private def p563 := certifiedPrime 563 2 [(p2,1),(p281,1)] (by decide +kernel)

private def p569 := certifiedPrime 569 3 [(p2,3),(p71,1)] (by decide +kernel)

private def p571 := certifiedPrime 571 3 [(p2,1),(p3,1),(p5,1),(p19,1)] (by decide +kernel)

private def p577 := certifiedPrime 577 5 [(p2,6),(p3,2)] (by decide +kernel)

private def p587 := certifiedPrime 587 2 [(p2,1),(p293,1)] (by decide +kernel)

private def p593 := certifiedPrime 593 3 [(p2,4),(p37,1)] (by decide +kernel)

private def p599 := certifiedPrime 599 7 [(p2,1),(p13,1),(p23,1)] (by decide +kernel)

private def p601 := certifiedPrime 601 7 [(p2,3),(p3,1),(p5,2)] (by decide +kernel)

private def p607 := certifiedPrime 607 3 [(p2,1),(p3,1),(p101,1)] (by decide +kernel)

private def p613 := certifiedPrime 613 2 [(p2,2),(p3,2),(p17,1)] (by decide +kernel)

private def p617 := certifiedPrime 617 3 [(p2,3),(p7,1),(p11,1)] (by decide +kernel)

private def p619 := certifiedPrime 619 2 [(p2,1),(p3,1),(p103,1)] (by decide +kernel)

private def p631 := certifiedPrime 631 3 [(p2,1),(p3,2),(p5,1),(p7,1)] (by decide +kernel)

private def p641 := certifiedPrime 641 3 [(p2,7),(p5,1)] (by decide +kernel)

private def p643 := certifiedPrime 643 11 [(p2,1),(p3,1),(p107,1)] (by decide +kernel)

private def p647 := certifiedPrime 647 5 [(p2,1),(p17,1),(p19,1)] (by decide +kernel)

private def p653 := certifiedPrime 653 2 [(p2,2),(p163,1)] (by decide +kernel)

private def p659 := certifiedPrime 659 2 [(p2,1),(p7,1),(p47,1)] (by decide +kernel)

private def p661 := certifiedPrime 661 2 [(p2,2),(p3,1),(p5,1),(p11,1)] (by decide +kernel)

private def p673 := certifiedPrime 673 5 [(p2,5),(p3,1),(p7,1)] (by decide +kernel)

private def p677 := certifiedPrime 677 2 [(p2,2),(p13,2)] (by decide +kernel)

private def p683 := certifiedPrime 683 5 [(p2,1),(p11,1),(p31,1)] (by decide +kernel)

private def p691 := certifiedPrime 691 3 [(p2,1),(p3,1),(p5,1),(p23,1)] (by decide +kernel)

private def p701 := certifiedPrime 701 2 [(p2,2),(p5,2),(p7,1)] (by decide +kernel)

private def p709 := certifiedPrime 709 2 [(p2,2),(p3,1),(p59,1)] (by decide +kernel)

private def p719 := certifiedPrime 719 11 [(p2,1),(p359,1)] (by decide +kernel)

private def p727 := certifiedPrime 727 5 [(p2,1),(p3,1),(p11,2)] (by decide +kernel)

private def p733 := certifiedPrime 733 6 [(p2,2),(p3,1),(p61,1)] (by decide +kernel)

private def p739 := certifiedPrime 739 3 [(p2,1),(p3,2),(p41,1)] (by decide +kernel)

private def p743 := certifiedPrime 743 5 [(p2,1),(p7,1),(p53,1)] (by decide +kernel)

private def p751 := certifiedPrime 751 3 [(p2,1),(p3,1),(p5,3)] (by decide +kernel)

private def p757 := certifiedPrime 757 2 [(p2,2),(p3,3),(p7,1)] (by decide +kernel)

private def p761 := certifiedPrime 761 6 [(p2,3),(p5,1),(p19,1)] (by decide +kernel)

private def p769 := certifiedPrime 769 11 [(p2,8),(p3,1)] (by decide +kernel)

private def p773 := certifiedPrime 773 2 [(p2,2),(p193,1)] (by decide +kernel)

private def p787 := certifiedPrime 787 2 [(p2,1),(p3,1),(p131,1)] (by decide +kernel)

private def p797 := certifiedPrime 797 2 [(p2,2),(p199,1)] (by decide +kernel)

private def p809 := certifiedPrime 809 3 [(p2,3),(p101,1)] (by decide +kernel)

private def p811 := certifiedPrime 811 3 [(p2,1),(p3,4),(p5,1)] (by decide +kernel)

private def p821 := certifiedPrime 821 2 [(p2,2),(p5,1),(p41,1)] (by decide +kernel)

private def p823 := certifiedPrime 823 3 [(p2,1),(p3,1),(p137,1)] (by decide +kernel)

private def p827 := certifiedPrime 827 2 [(p2,1),(p7,1),(p59,1)] (by decide +kernel)

private def p829 := certifiedPrime 829 2 [(p2,2),(p3,2),(p23,1)] (by decide +kernel)

private def p839 := certifiedPrime 839 11 [(p2,1),(p419,1)] (by decide +kernel)

private def p853 := certifiedPrime 853 2 [(p2,2),(p3,1),(p71,1)] (by decide +kernel)

private def p857 := certifiedPrime 857 3 [(p2,3),(p107,1)] (by decide +kernel)

private def p859 := certifiedPrime 859 2 [(p2,1),(p3,1),(p11,1),(p13,1)] (by decide +kernel)

private def p863 := certifiedPrime 863 5 [(p2,1),(p431,1)] (by decide +kernel)

private def p881 := certifiedPrime 881 3 [(p2,4),(p5,1),(p11,1)] (by decide +kernel)

private def p883 := certifiedPrime 883 2 [(p2,1),(p3,2),(p7,2)] (by decide +kernel)

private def p887 := certifiedPrime 887 5 [(p2,1),(p443,1)] (by decide +kernel)

private def p907 := certifiedPrime 907 2 [(p2,1),(p3,1),(p151,1)] (by decide +kernel)

private def p911 := certifiedPrime 911 17 [(p2,1),(p5,1),(p7,1),(p13,1)] (by decide +kernel)

private def p919 := certifiedPrime 919 7 [(p2,1),(p3,3),(p17,1)] (by decide +kernel)

private def p929 := certifiedPrime 929 3 [(p2,5),(p29,1)] (by decide +kernel)

private def p937 := certifiedPrime 937 5 [(p2,3),(p3,2),(p13,1)] (by decide +kernel)

private def p947 := certifiedPrime 947 2 [(p2,1),(p11,1),(p43,1)] (by decide +kernel)

private def p953 := certifiedPrime 953 3 [(p2,3),(p7,1),(p17,1)] (by decide +kernel)

private def p967 := certifiedPrime 967 5 [(p2,1),(p3,1),(p7,1),(p23,1)] (by decide +kernel)

private def p971 := certifiedPrime 971 6 [(p2,1),(p5,1),(p97,1)] (by decide +kernel)

private def p977 := certifiedPrime 977 3 [(p2,4),(p61,1)] (by decide +kernel)

private def p983 := certifiedPrime 983 5 [(p2,1),(p491,1)] (by decide +kernel)

private def p991 := certifiedPrime 991 6 [(p2,1),(p3,2),(p5,1),(p11,1)] (by decide +kernel)

private def p997 := certifiedPrime 997 7 [(p2,2),(p3,1),(p83,1)] (by decide +kernel)

private def p1009 := certifiedPrime 1009 11 [(p2,4),(p3,2),(p7,1)] (by decide +kernel)

private def p1013 := certifiedPrime 1013 3 [(p2,2),(p11,1),(p23,1)] (by decide +kernel)

private def p1019 := certifiedPrime 1019 2 [(p2,1),(p509,1)] (by decide +kernel)

private def p1031 := certifiedPrime 1031 14 [(p2,1),(p5,1),(p103,1)] (by decide +kernel)

private def p1033 := certifiedPrime 1033 5 [(p2,3),(p3,1),(p43,1)] (by decide +kernel)

private def p1049 := certifiedPrime 1049 3 [(p2,3),(p131,1)] (by decide +kernel)

private def p1061 := certifiedPrime 1061 2 [(p2,2),(p5,1),(p53,1)] (by decide +kernel)

private def p1063 := certifiedPrime 1063 3 [(p2,1),(p3,2),(p59,1)] (by decide +kernel)

private def p1087 := certifiedPrime 1087 3 [(p2,1),(p3,1),(p181,1)] (by decide +kernel)

private def p1091 := certifiedPrime 1091 2 [(p2,1),(p5,1),(p109,1)] (by decide +kernel)

private def p1097 := certifiedPrime 1097 3 [(p2,3),(p137,1)] (by decide +kernel)

private def p1103 := certifiedPrime 1103 5 [(p2,1),(p19,1),(p29,1)] (by decide +kernel)

private def p1117 := certifiedPrime 1117 2 [(p2,2),(p3,2),(p31,1)] (by decide +kernel)

private def p1123 := certifiedPrime 1123 2 [(p2,1),(p3,1),(p11,1),(p17,1)] (by decide +kernel)

private def p1129 := certifiedPrime 1129 11 [(p2,3),(p3,1),(p47,1)] (by decide +kernel)

private def p1151 := certifiedPrime 1151 17 [(p2,1),(p5,2),(p23,1)] (by decide +kernel)

private def p1153 := certifiedPrime 1153 5 [(p2,7),(p3,2)] (by decide +kernel)

private def p1163 := certifiedPrime 1163 5 [(p2,1),(p7,1),(p83,1)] (by decide +kernel)

private def p1171 := certifiedPrime 1171 2 [(p2,1),(p3,2),(p5,1),(p13,1)] (by decide +kernel)

private def p1181 := certifiedPrime 1181 7 [(p2,2),(p5,1),(p59,1)] (by decide +kernel)

private def p1187 := certifiedPrime 1187 2 [(p2,1),(p593,1)] (by decide +kernel)

private def p1193 := certifiedPrime 1193 3 [(p2,3),(p149,1)] (by decide +kernel)

private def p1201 := certifiedPrime 1201 11 [(p2,4),(p3,1),(p5,2)] (by decide +kernel)

private def p1213 := certifiedPrime 1213 2 [(p2,2),(p3,1),(p101,1)] (by decide +kernel)

private def p1217 := certifiedPrime 1217 3 [(p2,6),(p19,1)] (by decide +kernel)

private def p1223 := certifiedPrime 1223 5 [(p2,1),(p13,1),(p47,1)] (by decide +kernel)

private def p1229 := certifiedPrime 1229 2 [(p2,2),(p307,1)] (by decide +kernel)

private def p1231 := certifiedPrime 1231 3 [(p2,1),(p3,1),(p5,1),(p41,1)] (by decide +kernel)

private def p1237 := certifiedPrime 1237 2 [(p2,2),(p3,1),(p103,1)] (by decide +kernel)

private def p1249 := certifiedPrime 1249 7 [(p2,5),(p3,1),(p13,1)] (by decide +kernel)

private def p1259 := certifiedPrime 1259 2 [(p2,1),(p17,1),(p37,1)] (by decide +kernel)

private def p1277 := certifiedPrime 1277 2 [(p2,2),(p11,1),(p29,1)] (by decide +kernel)

private def p1279 := certifiedPrime 1279 3 [(p2,1),(p3,2),(p71,1)] (by decide +kernel)

private def p1283 := certifiedPrime 1283 2 [(p2,1),(p641,1)] (by decide +kernel)

private def p1289 := certifiedPrime 1289 6 [(p2,3),(p7,1),(p23,1)] (by decide +kernel)

private def p1291 := certifiedPrime 1291 2 [(p2,1),(p3,1),(p5,1),(p43,1)] (by decide +kernel)

private def p1297 := certifiedPrime 1297 10 [(p2,4),(p3,4)] (by decide +kernel)

private def p1303 := certifiedPrime 1303 6 [(p2,1),(p3,1),(p7,1),(p31,1)] (by decide +kernel)

private def p1319 := certifiedPrime 1319 13 [(p2,1),(p659,1)] (by decide +kernel)

private def p1327 := certifiedPrime 1327 3 [(p2,1),(p3,1),(p13,1),(p17,1)] (by decide +kernel)

private def p1361 := certifiedPrime 1361 3 [(p2,4),(p5,1),(p17,1)] (by decide +kernel)

private def p1367 := certifiedPrime 1367 5 [(p2,1),(p683,1)] (by decide +kernel)

private def p1373 := certifiedPrime 1373 2 [(p2,2),(p7,3)] (by decide +kernel)

private def p1381 := certifiedPrime 1381 2 [(p2,2),(p3,1),(p5,1),(p23,1)] (by decide +kernel)

private def p1399 := certifiedPrime 1399 13 [(p2,1),(p3,1),(p233,1)] (by decide +kernel)

private def p1409 := certifiedPrime 1409 3 [(p2,7),(p11,1)] (by decide +kernel)

private def p1423 := certifiedPrime 1423 3 [(p2,1),(p3,2),(p79,1)] (by decide +kernel)

private def p1427 := certifiedPrime 1427 2 [(p2,1),(p23,1),(p31,1)] (by decide +kernel)

private def p1429 := certifiedPrime 1429 6 [(p2,2),(p3,1),(p7,1),(p17,1)] (by decide +kernel)

private def p1433 := certifiedPrime 1433 3 [(p2,3),(p179,1)] (by decide +kernel)

private def p1439 := certifiedPrime 1439 7 [(p2,1),(p719,1)] (by decide +kernel)

private def p1451 := certifiedPrime 1451 2 [(p2,1),(p5,2),(p29,1)] (by decide +kernel)

private def p1453 := certifiedPrime 1453 2 [(p2,2),(p3,1),(p11,2)] (by decide +kernel)

private def p1459 := certifiedPrime 1459 3 [(p2,1),(p3,6)] (by decide +kernel)

private def p1471 := certifiedPrime 1471 6 [(p2,1),(p3,1),(p5,1),(p7,2)] (by decide +kernel)

private def p1481 := certifiedPrime 1481 3 [(p2,3),(p5,1),(p37,1)] (by decide +kernel)

private def p1483 := certifiedPrime 1483 2 [(p2,1),(p3,1),(p13,1),(p19,1)] (by decide +kernel)

private def p1487 := certifiedPrime 1487 5 [(p2,1),(p743,1)] (by decide +kernel)

private def p1493 := certifiedPrime 1493 2 [(p2,2),(p373,1)] (by decide +kernel)

private def p1499 := certifiedPrime 1499 2 [(p2,1),(p7,1),(p107,1)] (by decide +kernel)

private def p1511 := certifiedPrime 1511 11 [(p2,1),(p5,1),(p151,1)] (by decide +kernel)

private def p1523 := certifiedPrime 1523 2 [(p2,1),(p761,1)] (by decide +kernel)

private def p1531 := certifiedPrime 1531 2 [(p2,1),(p3,2),(p5,1),(p17,1)] (by decide +kernel)

private def p1543 := certifiedPrime 1543 5 [(p2,1),(p3,1),(p257,1)] (by decide +kernel)

private def p1549 := certifiedPrime 1549 2 [(p2,2),(p3,2),(p43,1)] (by decide +kernel)

private def p1553 := certifiedPrime 1553 3 [(p2,4),(p97,1)] (by decide +kernel)

private def p1559 := certifiedPrime 1559 19 [(p2,1),(p19,1),(p41,1)] (by decide +kernel)

private def p1567 := certifiedPrime 1567 3 [(p2,1),(p3,3),(p29,1)] (by decide +kernel)

private def p1571 := certifiedPrime 1571 2 [(p2,1),(p5,1),(p157,1)] (by decide +kernel)

private def p1579 := certifiedPrime 1579 3 [(p2,1),(p3,1),(p263,1)] (by decide +kernel)

private def p1583 := certifiedPrime 1583 5 [(p2,1),(p7,1),(p113,1)] (by decide +kernel)

private def p1597 := certifiedPrime 1597 11 [(p2,2),(p3,1),(p7,1),(p19,1)] (by decide +kernel)

private def p1601 := certifiedPrime 1601 3 [(p2,6),(p5,2)] (by decide +kernel)

private def p1607 := certifiedPrime 1607 5 [(p2,1),(p11,1),(p73,1)] (by decide +kernel)

private def p1609 := certifiedPrime 1609 7 [(p2,3),(p3,1),(p67,1)] (by decide +kernel)

private def p1619 := certifiedPrime 1619 2 [(p2,1),(p809,1)] (by decide +kernel)

private def p1621 := certifiedPrime 1621 2 [(p2,2),(p3,4),(p5,1)] (by decide +kernel)

private def p1627 := certifiedPrime 1627 3 [(p2,1),(p3,1),(p271,1)] (by decide +kernel)

private def p1663 := certifiedPrime 1663 3 [(p2,1),(p3,1),(p277,1)] (by decide +kernel)

private def p1667 := certifiedPrime 1667 2 [(p2,1),(p7,2),(p17,1)] (by decide +kernel)

private def p1693 := certifiedPrime 1693 2 [(p2,2),(p3,2),(p47,1)] (by decide +kernel)

private def p1697 := certifiedPrime 1697 3 [(p2,5),(p53,1)] (by decide +kernel)

private def p1699 := certifiedPrime 1699 3 [(p2,1),(p3,1),(p283,1)] (by decide +kernel)

private def p1709 := certifiedPrime 1709 3 [(p2,2),(p7,1),(p61,1)] (by decide +kernel)

private def p1723 := certifiedPrime 1723 3 [(p2,1),(p3,1),(p7,1),(p41,1)] (by decide +kernel)

private def p1733 := certifiedPrime 1733 2 [(p2,2),(p433,1)] (by decide +kernel)

private def p1741 := certifiedPrime 1741 2 [(p2,2),(p3,1),(p5,1),(p29,1)] (by decide +kernel)

private def p1747 := certifiedPrime 1747 2 [(p2,1),(p3,2),(p97,1)] (by decide +kernel)

private def p1753 := certifiedPrime 1753 7 [(p2,3),(p3,1),(p73,1)] (by decide +kernel)

private def p1777 := certifiedPrime 1777 5 [(p2,4),(p3,1),(p37,1)] (by decide +kernel)

private def p1783 := certifiedPrime 1783 10 [(p2,1),(p3,4),(p11,1)] (by decide +kernel)

private def p1787 := certifiedPrime 1787 2 [(p2,1),(p19,1),(p47,1)] (by decide +kernel)

private def p1789 := certifiedPrime 1789 6 [(p2,2),(p3,1),(p149,1)] (by decide +kernel)

private def p1801 := certifiedPrime 1801 11 [(p2,3),(p3,2),(p5,2)] (by decide +kernel)

private def p1811 := certifiedPrime 1811 6 [(p2,1),(p5,1),(p181,1)] (by decide +kernel)

private def p1831 := certifiedPrime 1831 3 [(p2,1),(p3,1),(p5,1),(p61,1)] (by decide +kernel)

private def p1867 := certifiedPrime 1867 2 [(p2,1),(p3,1),(p311,1)] (by decide +kernel)

private def p1871 := certifiedPrime 1871 14 [(p2,1),(p5,1),(p11,1),(p17,1)] (by decide +kernel)

private def p1873 := certifiedPrime 1873 10 [(p2,4),(p3,2),(p13,1)] (by decide +kernel)

private def p1877 := certifiedPrime 1877 2 [(p2,2),(p7,1),(p67,1)] (by decide +kernel)

private def p1879 := certifiedPrime 1879 6 [(p2,1),(p3,1),(p313,1)] (by decide +kernel)

private def p1889 := certifiedPrime 1889 3 [(p2,5),(p59,1)] (by decide +kernel)

private def p1907 := certifiedPrime 1907 2 [(p2,1),(p953,1)] (by decide +kernel)

private def p1933 := certifiedPrime 1933 5 [(p2,2),(p3,1),(p7,1),(p23,1)] (by decide +kernel)

private def p1949 := certifiedPrime 1949 2 [(p2,2),(p487,1)] (by decide +kernel)

private def p1951 := certifiedPrime 1951 3 [(p2,1),(p3,1),(p5,2),(p13,1)] (by decide +kernel)

private def p1973 := certifiedPrime 1973 2 [(p2,2),(p17,1),(p29,1)] (by decide +kernel)

private def p1979 := certifiedPrime 1979 2 [(p2,1),(p23,1),(p43,1)] (by decide +kernel)

private def p1993 := certifiedPrime 1993 5 [(p2,3),(p3,1),(p83,1)] (by decide +kernel)

private def p1999 := certifiedPrime 1999 3 [(p2,1),(p3,3),(p37,1)] (by decide +kernel)

private def p2011 := certifiedPrime 2011 3 [(p2,1),(p3,1),(p5,1),(p67,1)] (by decide +kernel)

private def p2027 := certifiedPrime 2027 2 [(p2,1),(p1013,1)] (by decide +kernel)

private def p2029 := certifiedPrime 2029 2 [(p2,2),(p3,1),(p13,2)] (by decide +kernel)

private def p2039 := certifiedPrime 2039 7 [(p2,1),(p1019,1)] (by decide +kernel)

private def p2053 := certifiedPrime 2053 2 [(p2,2),(p3,3),(p19,1)] (by decide +kernel)

private def p2063 := certifiedPrime 2063 5 [(p2,1),(p1031,1)] (by decide +kernel)

private def p2069 := certifiedPrime 2069 2 [(p2,2),(p11,1),(p47,1)] (by decide +kernel)

private def p2081 := certifiedPrime 2081 3 [(p2,5),(p5,1),(p13,1)] (by decide +kernel)

private def p2083 := certifiedPrime 2083 2 [(p2,1),(p3,1),(p347,1)] (by decide +kernel)

private def p2087 := certifiedPrime 2087 5 [(p2,1),(p7,1),(p149,1)] (by decide +kernel)

private def p2089 := certifiedPrime 2089 7 [(p2,3),(p3,2),(p29,1)] (by decide +kernel)

private def p2111 := certifiedPrime 2111 7 [(p2,1),(p5,1),(p211,1)] (by decide +kernel)

private def p2113 := certifiedPrime 2113 5 [(p2,6),(p3,1),(p11,1)] (by decide +kernel)

private def p2131 := certifiedPrime 2131 2 [(p2,1),(p3,1),(p5,1),(p71,1)] (by decide +kernel)

private def p2141 := certifiedPrime 2141 2 [(p2,2),(p5,1),(p107,1)] (by decide +kernel)

private def p2143 := certifiedPrime 2143 3 [(p2,1),(p3,2),(p7,1),(p17,1)] (by decide +kernel)

private def p2153 := certifiedPrime 2153 3 [(p2,3),(p269,1)] (by decide +kernel)

private def p2203 := certifiedPrime 2203 5 [(p2,1),(p3,1),(p367,1)] (by decide +kernel)

private def p2207 := certifiedPrime 2207 5 [(p2,1),(p1103,1)] (by decide +kernel)

private def p2213 := certifiedPrime 2213 2 [(p2,2),(p7,1),(p79,1)] (by decide +kernel)

private def p2237 := certifiedPrime 2237 2 [(p2,2),(p13,1),(p43,1)] (by decide +kernel)

private def p2243 := certifiedPrime 2243 2 [(p2,1),(p19,1),(p59,1)] (by decide +kernel)

private def p2267 := certifiedPrime 2267 2 [(p2,1),(p11,1),(p103,1)] (by decide +kernel)

private def p2269 := certifiedPrime 2269 2 [(p2,2),(p3,4),(p7,1)] (by decide +kernel)

private def p2273 := certifiedPrime 2273 3 [(p2,5),(p71,1)] (by decide +kernel)

private def p2293 := certifiedPrime 2293 2 [(p2,2),(p3,1),(p191,1)] (by decide +kernel)

private def p2297 := certifiedPrime 2297 5 [(p2,3),(p7,1),(p41,1)] (by decide +kernel)

private def p2309 := certifiedPrime 2309 2 [(p2,2),(p577,1)] (by decide +kernel)

private def p2311 := certifiedPrime 2311 3 [(p2,1),(p3,1),(p5,1),(p7,1),(p11,1)] (by decide +kernel)

private def p2333 := certifiedPrime 2333 2 [(p2,2),(p11,1),(p53,1)] (by decide +kernel)

private def p2339 := certifiedPrime 2339 2 [(p2,1),(p7,1),(p167,1)] (by decide +kernel)

private def p2347 := certifiedPrime 2347 3 [(p2,1),(p3,1),(p17,1),(p23,1)] (by decide +kernel)

private def p2371 := certifiedPrime 2371 2 [(p2,1),(p3,1),(p5,1),(p79,1)] (by decide +kernel)

private def p2383 := certifiedPrime 2383 5 [(p2,1),(p3,1),(p397,1)] (by decide +kernel)

private def p2389 := certifiedPrime 2389 2 [(p2,2),(p3,1),(p199,1)] (by decide +kernel)

private def p2399 := certifiedPrime 2399 11 [(p2,1),(p11,1),(p109,1)] (by decide +kernel)

private def p2411 := certifiedPrime 2411 6 [(p2,1),(p5,1),(p241,1)] (by decide +kernel)

private def p2417 := certifiedPrime 2417 3 [(p2,4),(p151,1)] (by decide +kernel)

private def p2441 := certifiedPrime 2441 6 [(p2,3),(p5,1),(p61,1)] (by decide +kernel)

private def p2459 := certifiedPrime 2459 2 [(p2,1),(p1229,1)] (by decide +kernel)

private def p2467 := certifiedPrime 2467 2 [(p2,1),(p3,2),(p137,1)] (by decide +kernel)

private def p2477 := certifiedPrime 2477 2 [(p2,2),(p619,1)] (by decide +kernel)

private def p2521 := certifiedPrime 2521 17 [(p2,3),(p3,2),(p5,1),(p7,1)] (by decide +kernel)

private def p2539 := certifiedPrime 2539 2 [(p2,1),(p3,3),(p47,1)] (by decide +kernel)

private def p2543 := certifiedPrime 2543 5 [(p2,1),(p31,1),(p41,1)] (by decide +kernel)

private def p2549 := certifiedPrime 2549 2 [(p2,2),(p7,2),(p13,1)] (by decide +kernel)

private def p2551 := certifiedPrime 2551 6 [(p2,1),(p3,1),(p5,2),(p17,1)] (by decide +kernel)

private def p2579 := certifiedPrime 2579 2 [(p2,1),(p1289,1)] (by decide +kernel)

private def p2593 := certifiedPrime 2593 7 [(p2,5),(p3,4)] (by decide +kernel)

private def p2609 := certifiedPrime 2609 3 [(p2,4),(p163,1)] (by decide +kernel)

private def p2621 := certifiedPrime 2621 2 [(p2,2),(p5,1),(p131,1)] (by decide +kernel)

private def p2657 := certifiedPrime 2657 3 [(p2,5),(p83,1)] (by decide +kernel)

private def p2659 := certifiedPrime 2659 2 [(p2,1),(p3,1),(p443,1)] (by decide +kernel)

private def p2683 := certifiedPrime 2683 2 [(p2,1),(p3,2),(p149,1)] (by decide +kernel)

private def p2687 := certifiedPrime 2687 5 [(p2,1),(p17,1),(p79,1)] (by decide +kernel)

private def p2689 := certifiedPrime 2689 19 [(p2,7),(p3,1),(p7,1)] (by decide +kernel)

private def p2693 := certifiedPrime 2693 2 [(p2,2),(p673,1)] (by decide +kernel)

private def p2699 := certifiedPrime 2699 2 [(p2,1),(p19,1),(p71,1)] (by decide +kernel)

private def p2719 := certifiedPrime 2719 3 [(p2,1),(p3,2),(p151,1)] (by decide +kernel)

private def p2753 := certifiedPrime 2753 3 [(p2,6),(p43,1)] (by decide +kernel)

private def p2767 := certifiedPrime 2767 3 [(p2,1),(p3,1),(p461,1)] (by decide +kernel)

private def p2777 := certifiedPrime 2777 3 [(p2,3),(p347,1)] (by decide +kernel)

private def p2789 := certifiedPrime 2789 2 [(p2,2),(p17,1),(p41,1)] (by decide +kernel)

private def p2797 := certifiedPrime 2797 2 [(p2,2),(p3,1),(p233,1)] (by decide +kernel)

private def p2801 := certifiedPrime 2801 3 [(p2,4),(p5,2),(p7,1)] (by decide +kernel)

private def p2803 := certifiedPrime 2803 2 [(p2,1),(p3,1),(p467,1)] (by decide +kernel)

private def p2819 := certifiedPrime 2819 2 [(p2,1),(p1409,1)] (by decide +kernel)

private def p2833 := certifiedPrime 2833 5 [(p2,4),(p3,1),(p59,1)] (by decide +kernel)

private def p2851 := certifiedPrime 2851 2 [(p2,1),(p3,1),(p5,2),(p19,1)] (by decide +kernel)

private def p2857 := certifiedPrime 2857 11 [(p2,3),(p3,1),(p7,1),(p17,1)] (by decide +kernel)

private def p2887 := certifiedPrime 2887 5 [(p2,1),(p3,1),(p13,1),(p37,1)] (by decide +kernel)

private def p2897 := certifiedPrime 2897 3 [(p2,4),(p181,1)] (by decide +kernel)

private def p2939 := certifiedPrime 2939 2 [(p2,1),(p13,1),(p113,1)] (by decide +kernel)

private def p2971 := certifiedPrime 2971 10 [(p2,1),(p3,3),(p5,1),(p11,1)] (by decide +kernel)

private def p2999 := certifiedPrime 2999 17 [(p2,1),(p1499,1)] (by decide +kernel)

private def p3001 := certifiedPrime 3001 14 [(p2,3),(p3,1),(p5,3)] (by decide +kernel)

private def p3023 := certifiedPrime 3023 5 [(p2,1),(p1511,1)] (by decide +kernel)

private def p3037 := certifiedPrime 3037 2 [(p2,2),(p3,1),(p11,1),(p23,1)] (by decide +kernel)

private def p3041 := certifiedPrime 3041 3 [(p2,5),(p5,1),(p19,1)] (by decide +kernel)

private def p3061 := certifiedPrime 3061 6 [(p2,2),(p3,2),(p5,1),(p17,1)] (by decide +kernel)

private def p3083 := certifiedPrime 3083 2 [(p2,1),(p23,1),(p67,1)] (by decide +kernel)

private def p3089 := certifiedPrime 3089 3 [(p2,4),(p193,1)] (by decide +kernel)

private def p3109 := certifiedPrime 3109 6 [(p2,2),(p3,1),(p7,1),(p37,1)] (by decide +kernel)

private def p3121 := certifiedPrime 3121 7 [(p2,4),(p3,1),(p5,1),(p13,1)] (by decide +kernel)

private def p3181 := certifiedPrime 3181 7 [(p2,2),(p3,1),(p5,1),(p53,1)] (by decide +kernel)

private def p3191 := certifiedPrime 3191 11 [(p2,1),(p5,1),(p11,1),(p29,1)] (by decide +kernel)

private def p3209 := certifiedPrime 3209 3 [(p2,3),(p401,1)] (by decide +kernel)

private def p3217 := certifiedPrime 3217 5 [(p2,4),(p3,1),(p67,1)] (by decide +kernel)

private def p3221 := certifiedPrime 3221 10 [(p2,2),(p5,1),(p7,1),(p23,1)] (by decide +kernel)

private def p3251 := certifiedPrime 3251 6 [(p2,1),(p5,3),(p13,1)] (by decide +kernel)

private def p3271 := certifiedPrime 3271 3 [(p2,1),(p3,1),(p5,1),(p109,1)] (by decide +kernel)

private def p3299 := certifiedPrime 3299 2 [(p2,1),(p17,1),(p97,1)] (by decide +kernel)

private def p3307 := certifiedPrime 3307 2 [(p2,1),(p3,1),(p19,1),(p29,1)] (by decide +kernel)

private def p3319 := certifiedPrime 3319 6 [(p2,1),(p3,1),(p7,1),(p79,1)] (by decide +kernel)

private def p3331 := certifiedPrime 3331 3 [(p2,1),(p3,2),(p5,1),(p37,1)] (by decide +kernel)

private def p3343 := certifiedPrime 3343 5 [(p2,1),(p3,1),(p557,1)] (by decide +kernel)

private def p3359 := certifiedPrime 3359 11 [(p2,1),(p23,1),(p73,1)] (by decide +kernel)

private def p3371 := certifiedPrime 3371 2 [(p2,1),(p5,1),(p337,1)] (by decide +kernel)

private def p3389 := certifiedPrime 3389 3 [(p2,2),(p7,1),(p11,2)] (by decide +kernel)

private def p3391 := certifiedPrime 3391 3 [(p2,1),(p3,1),(p5,1),(p113,1)] (by decide +kernel)

private def p3433 := certifiedPrime 3433 5 [(p2,3),(p3,1),(p11,1),(p13,1)] (by decide +kernel)

private def p3449 := certifiedPrime 3449 3 [(p2,3),(p431,1)] (by decide +kernel)

private def p3461 := certifiedPrime 3461 2 [(p2,2),(p5,1),(p173,1)] (by decide +kernel)

private def p3467 := certifiedPrime 3467 2 [(p2,1),(p1733,1)] (by decide +kernel)

private def p3491 := certifiedPrime 3491 2 [(p2,1),(p5,1),(p349,1)] (by decide +kernel)

private def p3511 := certifiedPrime 3511 7 [(p2,1),(p3,3),(p5,1),(p13,1)] (by decide +kernel)

private def p3517 := certifiedPrime 3517 2 [(p2,2),(p3,1),(p293,1)] (by decide +kernel)

private def p3527 := certifiedPrime 3527 5 [(p2,1),(p41,1),(p43,1)] (by decide +kernel)

private def p3529 := certifiedPrime 3529 17 [(p2,3),(p3,2),(p7,2)] (by decide +kernel)

private def p3539 := certifiedPrime 3539 2 [(p2,1),(p29,1),(p61,1)] (by decide +kernel)

private def p3547 := certifiedPrime 3547 2 [(p2,1),(p3,2),(p197,1)] (by decide +kernel)

private def p3581 := certifiedPrime 3581 2 [(p2,2),(p5,1),(p179,1)] (by decide +kernel)

private def p3583 := certifiedPrime 3583 3 [(p2,1),(p3,2),(p199,1)] (by decide +kernel)

private def p3617 := certifiedPrime 3617 3 [(p2,5),(p113,1)] (by decide +kernel)

private def p3623 := certifiedPrime 3623 5 [(p2,1),(p1811,1)] (by decide +kernel)

private def p3637 := certifiedPrime 3637 2 [(p2,2),(p3,2),(p101,1)] (by decide +kernel)

private def p3643 := certifiedPrime 3643 2 [(p2,1),(p3,1),(p607,1)] (by decide +kernel)

private def p3673 := certifiedPrime 3673 5 [(p2,3),(p3,3),(p17,1)] (by decide +kernel)

private def p3677 := certifiedPrime 3677 2 [(p2,2),(p919,1)] (by decide +kernel)

private def p3697 := certifiedPrime 3697 5 [(p2,4),(p3,1),(p7,1),(p11,1)] (by decide +kernel)

private def p3701 := certifiedPrime 3701 2 [(p2,2),(p5,2),(p37,1)] (by decide +kernel)

private def p3719 := certifiedPrime 3719 7 [(p2,1),(p11,1),(p13,2)] (by decide +kernel)

private def p3733 := certifiedPrime 3733 2 [(p2,2),(p3,1),(p311,1)] (by decide +kernel)

private def p3739 := certifiedPrime 3739 7 [(p2,1),(p3,1),(p7,1),(p89,1)] (by decide +kernel)

private def p3767 := certifiedPrime 3767 5 [(p2,1),(p7,1),(p269,1)] (by decide +kernel)

private def p3769 := certifiedPrime 3769 7 [(p2,3),(p3,1),(p157,1)] (by decide +kernel)

private def p3779 := certifiedPrime 3779 2 [(p2,1),(p1889,1)] (by decide +kernel)

private def p3793 := certifiedPrime 3793 5 [(p2,4),(p3,1),(p79,1)] (by decide +kernel)

private def p3823 := certifiedPrime 3823 3 [(p2,1),(p3,1),(p7,2),(p13,1)] (by decide +kernel)

private def p3847 := certifiedPrime 3847 5 [(p2,1),(p3,1),(p641,1)] (by decide +kernel)

private def p3877 := certifiedPrime 3877 2 [(p2,2),(p3,1),(p17,1),(p19,1)] (by decide +kernel)

private def p3881 := certifiedPrime 3881 13 [(p2,3),(p5,1),(p97,1)] (by decide +kernel)

private def p3889 := certifiedPrime 3889 11 [(p2,4),(p3,5)] (by decide +kernel)

private def p3929 := certifiedPrime 3929 3 [(p2,3),(p491,1)] (by decide +kernel)

private def p3931 := certifiedPrime 3931 2 [(p2,1),(p3,1),(p5,1),(p131,1)] (by decide +kernel)

private def p3943 := certifiedPrime 3943 3 [(p2,1),(p3,3),(p73,1)] (by decide +kernel)

private def p3947 := certifiedPrime 3947 2 [(p2,1),(p1973,1)] (by decide +kernel)

private def p3967 := certifiedPrime 3967 6 [(p2,1),(p3,1),(p661,1)] (by decide +kernel)

private def p3989 := certifiedPrime 3989 2 [(p2,2),(p997,1)] (by decide +kernel)

private def p4019 := certifiedPrime 4019 2 [(p2,1),(p7,2),(p41,1)] (by decide +kernel)

private def p4021 := certifiedPrime 4021 2 [(p2,2),(p3,1),(p5,1),(p67,1)] (by decide +kernel)

private def p4027 := certifiedPrime 4027 3 [(p2,1),(p3,1),(p11,1),(p61,1)] (by decide +kernel)

private def p4049 := certifiedPrime 4049 3 [(p2,4),(p11,1),(p23,1)] (by decide +kernel)

private def p4079 := certifiedPrime 4079 11 [(p2,1),(p2039,1)] (by decide +kernel)

private def p4093 := certifiedPrime 4093 2 [(p2,2),(p3,1),(p11,1),(p31,1)] (by decide +kernel)

private def p4111 := certifiedPrime 4111 12 [(p2,1),(p3,1),(p5,1),(p137,1)] (by decide +kernel)

private def p4127 := certifiedPrime 4127 5 [(p2,1),(p2063,1)] (by decide +kernel)

private def p4133 := certifiedPrime 4133 2 [(p2,2),(p1033,1)] (by decide +kernel)

private def p4211 := certifiedPrime 4211 6 [(p2,1),(p5,1),(p421,1)] (by decide +kernel)

private def p4229 := certifiedPrime 4229 2 [(p2,2),(p7,1),(p151,1)] (by decide +kernel)

private def p4289 := certifiedPrime 4289 3 [(p2,6),(p67,1)] (by decide +kernel)

private def p4349 := certifiedPrime 4349 2 [(p2,2),(p1087,1)] (by decide +kernel)

private def p4363 := certifiedPrime 4363 2 [(p2,1),(p3,1),(p727,1)] (by decide +kernel)

private def p4409 := certifiedPrime 4409 3 [(p2,3),(p19,1),(p29,1)] (by decide +kernel)

private def p4421 := certifiedPrime 4421 3 [(p2,2),(p5,1),(p13,1),(p17,1)] (by decide +kernel)

private def p4481 := certifiedPrime 4481 3 [(p2,7),(p5,1),(p7,1)] (by decide +kernel)

private def p4483 := certifiedPrime 4483 2 [(p2,1),(p3,3),(p83,1)] (by decide +kernel)

private def p4507 := certifiedPrime 4507 2 [(p2,1),(p3,1),(p751,1)] (by decide +kernel)

private def p4513 := certifiedPrime 4513 7 [(p2,5),(p3,1),(p47,1)] (by decide +kernel)

private def p4519 := certifiedPrime 4519 3 [(p2,1),(p3,2),(p251,1)] (by decide +kernel)

private def p4649 := certifiedPrime 4649 3 [(p2,3),(p7,1),(p83,1)] (by decide +kernel)

private def p4651 := certifiedPrime 4651 3 [(p2,1),(p3,1),(p5,2),(p31,1)] (by decide +kernel)

private def p4679 := certifiedPrime 4679 11 [(p2,1),(p2339,1)] (by decide +kernel)

private def p4691 := certifiedPrime 4691 2 [(p2,1),(p5,1),(p7,1),(p67,1)] (by decide +kernel)

private def p4729 := certifiedPrime 4729 17 [(p2,3),(p3,1),(p197,1)] (by decide +kernel)

private def p4793 := certifiedPrime 4793 3 [(p2,3),(p599,1)] (by decide +kernel)

private def p4799 := certifiedPrime 4799 7 [(p2,1),(p2399,1)] (by decide +kernel)

private def p4801 := certifiedPrime 4801 7 [(p2,6),(p3,1),(p5,2)] (by decide +kernel)

private def p4817 := certifiedPrime 4817 3 [(p2,4),(p7,1),(p43,1)] (by decide +kernel)

private def p4871 := certifiedPrime 4871 11 [(p2,1),(p5,1),(p487,1)] (by decide +kernel)

private def p4877 := certifiedPrime 4877 2 [(p2,2),(p23,1),(p53,1)] (by decide +kernel)

private def p4889 := certifiedPrime 4889 3 [(p2,3),(p13,1),(p47,1)] (by decide +kernel)

private def p4919 := certifiedPrime 4919 13 [(p2,1),(p2459,1)] (by decide +kernel)

private def p4937 := certifiedPrime 4937 3 [(p2,3),(p617,1)] (by decide +kernel)

private def p4943 := certifiedPrime 4943 7 [(p2,1),(p7,1),(p353,1)] (by decide +kernel)

private def p4969 := certifiedPrime 4969 11 [(p2,3),(p3,3),(p23,1)] (by decide +kernel)

private def p4987 := certifiedPrime 4987 2 [(p2,1),(p3,2),(p277,1)] (by decide +kernel)

private def p4993 := certifiedPrime 4993 5 [(p2,7),(p3,1),(p13,1)] (by decide +kernel)

private def p4999 := certifiedPrime 4999 3 [(p2,1),(p3,1),(p7,2),(p17,1)] (by decide +kernel)

private def p5003 := certifiedPrime 5003 2 [(p2,1),(p41,1),(p61,1)] (by decide +kernel)

private def p5011 := certifiedPrime 5011 2 [(p2,1),(p3,1),(p5,1),(p167,1)] (by decide +kernel)

private def p5051 := certifiedPrime 5051 2 [(p2,1),(p5,2),(p101,1)] (by decide +kernel)

private def p5059 := certifiedPrime 5059 2 [(p2,1),(p3,2),(p281,1)] (by decide +kernel)

private def p5087 := certifiedPrime 5087 5 [(p2,1),(p2543,1)] (by decide +kernel)

private def p5101 := certifiedPrime 5101 6 [(p2,2),(p3,1),(p5,2),(p17,1)] (by decide +kernel)

private def p5113 := certifiedPrime 5113 19 [(p2,3),(p3,2),(p71,1)] (by decide +kernel)

private def p5147 := certifiedPrime 5147 2 [(p2,1),(p31,1),(p83,1)] (by decide +kernel)

private def p5197 := certifiedPrime 5197 7 [(p2,2),(p3,1),(p433,1)] (by decide +kernel)

private def p5227 := certifiedPrime 5227 2 [(p2,1),(p3,1),(p13,1),(p67,1)] (by decide +kernel)

private def p5281 := certifiedPrime 5281 7 [(p2,5),(p3,1),(p5,1),(p11,1)] (by decide +kernel)

private def p5303 := certifiedPrime 5303 5 [(p2,1),(p11,1),(p241,1)] (by decide +kernel)

private def p5309 := certifiedPrime 5309 2 [(p2,2),(p1327,1)] (by decide +kernel)

private def p5347 := certifiedPrime 5347 3 [(p2,1),(p3,5),(p11,1)] (by decide +kernel)

private def p5381 := certifiedPrime 5381 3 [(p2,2),(p5,1),(p269,1)] (by decide +kernel)

private def p5387 := certifiedPrime 5387 2 [(p2,1),(p2693,1)] (by decide +kernel)

private def p5393 := certifiedPrime 5393 3 [(p2,4),(p337,1)] (by decide +kernel)

private def p5399 := certifiedPrime 5399 7 [(p2,1),(p2699,1)] (by decide +kernel)

private def p5441 := certifiedPrime 5441 3 [(p2,6),(p5,1),(p17,1)] (by decide +kernel)

private def p5443 := certifiedPrime 5443 2 [(p2,1),(p3,1),(p907,1)] (by decide +kernel)

private def p5501 := certifiedPrime 5501 2 [(p2,2),(p5,3),(p11,1)] (by decide +kernel)

private def p5519 := certifiedPrime 5519 13 [(p2,1),(p31,1),(p89,1)] (by decide +kernel)

private def p5527 := certifiedPrime 5527 5 [(p2,1),(p3,2),(p307,1)] (by decide +kernel)

private def p5569 := certifiedPrime 5569 13 [(p2,6),(p3,1),(p29,1)] (by decide +kernel)

private def p5581 := certifiedPrime 5581 6 [(p2,2),(p3,2),(p5,1),(p31,1)] (by decide +kernel)

private def p5639 := certifiedPrime 5639 7 [(p2,1),(p2819,1)] (by decide +kernel)

private def p5657 := certifiedPrime 5657 3 [(p2,3),(p7,1),(p101,1)] (by decide +kernel)

private def p5689 := certifiedPrime 5689 11 [(p2,3),(p3,2),(p79,1)] (by decide +kernel)

private def p5701 := certifiedPrime 5701 2 [(p2,2),(p3,1),(p5,2),(p19,1)] (by decide +kernel)

private def p5711 := certifiedPrime 5711 19 [(p2,1),(p5,1),(p571,1)] (by decide +kernel)

private def p5717 := certifiedPrime 5717 2 [(p2,2),(p1429,1)] (by decide +kernel)

private def p5741 := certifiedPrime 5741 2 [(p2,2),(p5,1),(p7,1),(p41,1)] (by decide +kernel)

private def p5749 := certifiedPrime 5749 2 [(p2,2),(p3,1),(p479,1)] (by decide +kernel)

private def p5779 := certifiedPrime 5779 2 [(p2,1),(p3,3),(p107,1)] (by decide +kernel)

private def p5827 := certifiedPrime 5827 2 [(p2,1),(p3,1),(p971,1)] (by decide +kernel)

private def p5839 := certifiedPrime 5839 6 [(p2,1),(p3,1),(p7,1),(p139,1)] (by decide +kernel)

private def p5849 := certifiedPrime 5849 3 [(p2,3),(p17,1),(p43,1)] (by decide +kernel)

private def p5851 := certifiedPrime 5851 2 [(p2,1),(p3,2),(p5,2),(p13,1)] (by decide +kernel)

private def p5861 := certifiedPrime 5861 3 [(p2,2),(p5,1),(p293,1)] (by decide +kernel)

private def p5867 := certifiedPrime 5867 5 [(p2,1),(p7,1),(p419,1)] (by decide +kernel)

private def p5879 := certifiedPrime 5879 11 [(p2,1),(p2939,1)] (by decide +kernel)

private def p6029 := certifiedPrime 6029 2 [(p2,2),(p11,1),(p137,1)] (by decide +kernel)

private def p6101 := certifiedPrime 6101 2 [(p2,2),(p5,2),(p61,1)] (by decide +kernel)

private def p6121 := certifiedPrime 6121 7 [(p2,3),(p3,2),(p5,1),(p17,1)] (by decide +kernel)

private def p6173 := certifiedPrime 6173 2 [(p2,2),(p1543,1)] (by decide +kernel)

private def p6221 := certifiedPrime 6221 3 [(p2,2),(p5,1),(p311,1)] (by decide +kernel)

private def p6229 := certifiedPrime 6229 2 [(p2,2),(p3,2),(p173,1)] (by decide +kernel)

private def p6269 := certifiedPrime 6269 2 [(p2,2),(p1567,1)] (by decide +kernel)

private def p6277 := certifiedPrime 6277 2 [(p2,2),(p3,1),(p523,1)] (by decide +kernel)

private def p6353 := certifiedPrime 6353 3 [(p2,4),(p397,1)] (by decide +kernel)

private def p6361 := certifiedPrime 6361 19 [(p2,3),(p3,1),(p5,1),(p53,1)] (by decide +kernel)

private def p6389 := certifiedPrime 6389 2 [(p2,2),(p1597,1)] (by decide +kernel)

private def p6449 := certifiedPrime 6449 3 [(p2,4),(p13,1),(p31,1)] (by decide +kernel)

private def p6469 := certifiedPrime 6469 2 [(p2,2),(p3,1),(p7,2),(p11,1)] (by decide +kernel)

private def p6491 := certifiedPrime 6491 2 [(p2,1),(p5,1),(p11,1),(p59,1)] (by decide +kernel)

private def p6599 := certifiedPrime 6599 13 [(p2,1),(p3299,1)] (by decide +kernel)

private def p6619 := certifiedPrime 6619 2 [(p2,1),(p3,1),(p1103,1)] (by decide +kernel)

private def p6673 := certifiedPrime 6673 5 [(p2,4),(p3,1),(p139,1)] (by decide +kernel)

private def p6689 := certifiedPrime 6689 3 [(p2,5),(p11,1),(p19,1)] (by decide +kernel)

private def p6701 := certifiedPrime 6701 2 [(p2,2),(p5,2),(p67,1)] (by decide +kernel)

private def p6703 := certifiedPrime 6703 5 [(p2,1),(p3,1),(p1117,1)] (by decide +kernel)

private def p6709 := certifiedPrime 6709 2 [(p2,2),(p3,1),(p13,1),(p43,1)] (by decide +kernel)

private def p6719 := certifiedPrime 6719 11 [(p2,1),(p3359,1)] (by decide +kernel)

private def p6761 := certifiedPrime 6761 3 [(p2,3),(p5,1),(p13,2)] (by decide +kernel)

private def p6779 := certifiedPrime 6779 2 [(p2,1),(p3389,1)] (by decide +kernel)

private def p6781 := certifiedPrime 6781 2 [(p2,2),(p3,1),(p5,1),(p113,1)] (by decide +kernel)

private def p6829 := certifiedPrime 6829 2 [(p2,2),(p3,1),(p569,1)] (by decide +kernel)

private def p6841 := certifiedPrime 6841 22 [(p2,3),(p3,2),(p5,1),(p19,1)] (by decide +kernel)

private def p6863 := certifiedPrime 6863 5 [(p2,1),(p47,1),(p73,1)] (by decide +kernel)

private def p6871 := certifiedPrime 6871 3 [(p2,1),(p3,1),(p5,1),(p229,1)] (by decide +kernel)

private def p6883 := certifiedPrime 6883 2 [(p2,1),(p3,1),(p31,1),(p37,1)] (by decide +kernel)

private def p6899 := certifiedPrime 6899 2 [(p2,1),(p3449,1)] (by decide +kernel)

private def p6911 := certifiedPrime 6911 7 [(p2,1),(p5,1),(p691,1)] (by decide +kernel)

private def p6959 := certifiedPrime 6959 7 [(p2,1),(p7,2),(p71,1)] (by decide +kernel)

private def p6967 := certifiedPrime 6967 5 [(p2,1),(p3,4),(p43,1)] (by decide +kernel)

private def p6983 := certifiedPrime 6983 5 [(p2,1),(p3491,1)] (by decide +kernel)

private def p7027 := certifiedPrime 7027 2 [(p2,1),(p3,1),(p1171,1)] (by decide +kernel)

private def p7109 := certifiedPrime 7109 2 [(p2,2),(p1777,1)] (by decide +kernel)

private def p7129 := certifiedPrime 7129 7 [(p2,3),(p3,4),(p11,1)] (by decide +kernel)

private def p7237 := certifiedPrime 7237 2 [(p2,2),(p3,3),(p67,1)] (by decide +kernel)

private def p7283 := certifiedPrime 7283 2 [(p2,1),(p11,1),(p331,1)] (by decide +kernel)

private def p7297 := certifiedPrime 7297 5 [(p2,7),(p3,1),(p19,1)] (by decide +kernel)

private def p7321 := certifiedPrime 7321 7 [(p2,3),(p3,1),(p5,1),(p61,1)] (by decide +kernel)

private def p7331 := certifiedPrime 7331 2 [(p2,1),(p5,1),(p733,1)] (by decide +kernel)

private def p7333 := certifiedPrime 7333 6 [(p2,2),(p3,1),(p13,1),(p47,1)] (by decide +kernel)

private def p7349 := certifiedPrime 7349 2 [(p2,2),(p11,1),(p167,1)] (by decide +kernel)

private def p7351 := certifiedPrime 7351 6 [(p2,1),(p3,1),(p5,2),(p7,2)] (by decide +kernel)

private def p7369 := certifiedPrime 7369 7 [(p2,3),(p3,1),(p307,1)] (by decide +kernel)

private def p7411 := certifiedPrime 7411 2 [(p2,1),(p3,1),(p5,1),(p13,1),(p19,1)] (by decide +kernel)

private def p7547 := certifiedPrime 7547 2 [(p2,1),(p7,3),(p11,1)] (by decide +kernel)

private def p7559 := certifiedPrime 7559 13 [(p2,1),(p3779,1)] (by decide +kernel)

private def p7583 := certifiedPrime 7583 5 [(p2,1),(p17,1),(p223,1)] (by decide +kernel)

private def p7589 := certifiedPrime 7589 2 [(p2,2),(p7,1),(p271,1)] (by decide +kernel)

private def p7591 := certifiedPrime 7591 6 [(p2,1),(p3,1),(p5,1),(p11,1),(p23,1)] (by decide +kernel)

private def p7621 := certifiedPrime 7621 2 [(p2,2),(p3,1),(p5,1),(p127,1)] (by decide +kernel)

private def p7649 := certifiedPrime 7649 3 [(p2,5),(p239,1)] (by decide +kernel)

private def p7789 := certifiedPrime 7789 2 [(p2,2),(p3,1),(p11,1),(p59,1)] (by decide +kernel)

private def p7793 := certifiedPrime 7793 3 [(p2,4),(p487,1)] (by decide +kernel)

private def p7829 := certifiedPrime 7829 2 [(p2,2),(p19,1),(p103,1)] (by decide +kernel)

private def p7883 := certifiedPrime 7883 2 [(p2,1),(p7,1),(p563,1)] (by decide +kernel)

private def p7951 := certifiedPrime 7951 6 [(p2,1),(p3,1),(p5,2),(p53,1)] (by decide +kernel)

private def p7993 := certifiedPrime 7993 5 [(p2,3),(p3,3),(p37,1)] (by decide +kernel)

private def p8039 := certifiedPrime 8039 11 [(p2,1),(p4019,1)] (by decide +kernel)

private def p8089 := certifiedPrime 8089 17 [(p2,3),(p3,1),(p337,1)] (by decide +kernel)

private def p8101 := certifiedPrime 8101 6 [(p2,2),(p3,4),(p5,2)] (by decide +kernel)

private def p8243 := certifiedPrime 8243 2 [(p2,1),(p13,1),(p317,1)] (by decide +kernel)

private def p8293 := certifiedPrime 8293 2 [(p2,2),(p3,1),(p691,1)] (by decide +kernel)

private def p8353 := certifiedPrime 8353 5 [(p2,5),(p3,2),(p29,1)] (by decide +kernel)

private def p8377 := certifiedPrime 8377 5 [(p2,3),(p3,1),(p349,1)] (by decide +kernel)

private def p8389 := certifiedPrime 8389 6 [(p2,2),(p3,2),(p233,1)] (by decide +kernel)

private def p8501 := certifiedPrime 8501 7 [(p2,2),(p5,3),(p17,1)] (by decide +kernel)

private def p8599 := certifiedPrime 8599 3 [(p2,1),(p3,1),(p1433,1)] (by decide +kernel)

private def p8669 := certifiedPrime 8669 2 [(p2,2),(p11,1),(p197,1)] (by decide +kernel)

private def p8689 := certifiedPrime 8689 13 [(p2,4),(p3,1),(p181,1)] (by decide +kernel)

private def p8719 := certifiedPrime 8719 3 [(p2,1),(p3,1),(p1453,1)] (by decide +kernel)

private def p8737 := certifiedPrime 8737 5 [(p2,5),(p3,1),(p7,1),(p13,1)] (by decide +kernel)

private def p8779 := certifiedPrime 8779 11 [(p2,1),(p3,1),(p7,1),(p11,1),(p19,1)] (by decide +kernel)

private def p8821 := certifiedPrime 8821 2 [(p2,2),(p3,2),(p5,1),(p7,2)] (by decide +kernel)

private def p8867 := certifiedPrime 8867 2 [(p2,1),(p11,1),(p13,1),(p31,1)] (by decide +kernel)

private def p8887 := certifiedPrime 8887 3 [(p2,1),(p3,1),(p1481,1)] (by decide +kernel)

private def p8929 := certifiedPrime 8929 11 [(p2,5),(p3,2),(p31,1)] (by decide +kernel)

private def p8971 := certifiedPrime 8971 2 [(p2,1),(p3,1),(p5,1),(p13,1),(p23,1)] (by decide +kernel)

private def p8999 := certifiedPrime 8999 7 [(p2,1),(p11,1),(p409,1)] (by decide +kernel)

private def p9001 := certifiedPrime 9001 7 [(p2,3),(p3,2),(p5,3)] (by decide +kernel)

private def p9067 := certifiedPrime 9067 3 [(p2,1),(p3,1),(p1511,1)] (by decide +kernel)

private def p9091 := certifiedPrime 9091 3 [(p2,1),(p3,2),(p5,1),(p101,1)] (by decide +kernel)

private def p9109 := certifiedPrime 9109 10 [(p2,2),(p3,2),(p11,1),(p23,1)] (by decide +kernel)

private def p9137 := certifiedPrime 9137 3 [(p2,4),(p571,1)] (by decide +kernel)

private def p9199 := certifiedPrime 9199 3 [(p2,1),(p3,2),(p7,1),(p73,1)] (by decide +kernel)

private def p9221 := certifiedPrime 9221 2 [(p2,2),(p5,1),(p461,1)] (by decide +kernel)

private def p9227 := certifiedPrime 9227 2 [(p2,1),(p7,1),(p659,1)] (by decide +kernel)

private def p9293 := certifiedPrime 9293 2 [(p2,2),(p23,1),(p101,1)] (by decide +kernel)

private def p9371 := certifiedPrime 9371 2 [(p2,1),(p5,1),(p937,1)] (by decide +kernel)

private def p9461 := certifiedPrime 9461 3 [(p2,2),(p5,1),(p11,1),(p43,1)] (by decide +kernel)

private def p9479 := certifiedPrime 9479 7 [(p2,1),(p7,1),(p677,1)] (by decide +kernel)

private def p9539 := certifiedPrime 9539 2 [(p2,1),(p19,1),(p251,1)] (by decide +kernel)

private def p9743 := certifiedPrime 9743 5 [(p2,1),(p4871,1)] (by decide +kernel)

private def p9767 := certifiedPrime 9767 5 [(p2,1),(p19,1),(p257,1)] (by decide +kernel)

private def p9803 := certifiedPrime 9803 2 [(p2,1),(p13,2),(p29,1)] (by decide +kernel)

private def p9829 := certifiedPrime 9829 10 [(p2,2),(p3,3),(p7,1),(p13,1)] (by decide +kernel)

private def p9833 := certifiedPrime 9833 3 [(p2,3),(p1229,1)] (by decide +kernel)

private def p9857 := certifiedPrime 9857 5 [(p2,7),(p7,1),(p11,1)] (by decide +kernel)

private def p9887 := certifiedPrime 9887 5 [(p2,1),(p4943,1)] (by decide +kernel)

private def p9901 := certifiedPrime 9901 2 [(p2,2),(p3,2),(p5,2),(p11,1)] (by decide +kernel)

private def p10069 := certifiedPrime 10069 2 [(p2,2),(p3,1),(p839,1)] (by decide +kernel)

private def p10103 := certifiedPrime 10103 5 [(p2,1),(p5051,1)] (by decide +kernel)

private def p10111 := certifiedPrime 10111 12 [(p2,1),(p3,1),(p5,1),(p337,1)] (by decide +kernel)

private def p10133 := certifiedPrime 10133 2 [(p2,2),(p17,1),(p149,1)] (by decide +kernel)

private def p10247 := certifiedPrime 10247 5 [(p2,1),(p47,1),(p109,1)] (by decide +kernel)

private def p10259 := certifiedPrime 10259 2 [(p2,1),(p23,1),(p223,1)] (by decide +kernel)

private def p10303 := certifiedPrime 10303 3 [(p2,1),(p3,1),(p17,1),(p101,1)] (by decide +kernel)

private def p10321 := certifiedPrime 10321 7 [(p2,4),(p3,1),(p5,1),(p43,1)] (by decide +kernel)

private def p10427 := certifiedPrime 10427 2 [(p2,1),(p13,1),(p401,1)] (by decide +kernel)

private def p10597 := certifiedPrime 10597 5 [(p2,2),(p3,1),(p883,1)] (by decide +kernel)

private def p10753 := certifiedPrime 10753 11 [(p2,9),(p3,1),(p7,1)] (by decide +kernel)

private def p10781 := certifiedPrime 10781 10 [(p2,2),(p5,1),(p7,2),(p11,1)] (by decide +kernel)

private def p10883 := certifiedPrime 10883 2 [(p2,1),(p5441,1)] (by decide +kernel)

private def p10909 := certifiedPrime 10909 2 [(p2,2),(p3,3),(p101,1)] (by decide +kernel)

private def p10957 := certifiedPrime 10957 5 [(p2,2),(p3,1),(p11,1),(p83,1)] (by decide +kernel)

private def p10973 := certifiedPrime 10973 2 [(p2,2),(p13,1),(p211,1)] (by decide +kernel)

private def p11003 := certifiedPrime 11003 2 [(p2,1),(p5501,1)] (by decide +kernel)

private def p11047 := certifiedPrime 11047 3 [(p2,1),(p3,1),(p7,1),(p263,1)] (by decide +kernel)

private def p11119 := certifiedPrime 11119 3 [(p2,1),(p3,1),(p17,1),(p109,1)] (by decide +kernel)

private def p11161 := certifiedPrime 11161 7 [(p2,3),(p3,2),(p5,1),(p31,1)] (by decide +kernel)

private def p11213 := certifiedPrime 11213 2 [(p2,2),(p2803,1)] (by decide +kernel)

private def p11239 := certifiedPrime 11239 3 [(p2,1),(p3,1),(p1873,1)] (by decide +kernel)

private def p11251 := certifiedPrime 11251 13 [(p2,1),(p3,2),(p5,4)] (by decide +kernel)

private def p11257 := certifiedPrime 11257 10 [(p2,3),(p3,1),(p7,1),(p67,1)] (by decide +kernel)

private def p11273 := certifiedPrime 11273 3 [(p2,3),(p1409,1)] (by decide +kernel)

private def p11279 := certifiedPrime 11279 7 [(p2,1),(p5639,1)] (by decide +kernel)

private def p11299 := certifiedPrime 11299 3 [(p2,1),(p3,1),(p7,1),(p269,1)] (by decide +kernel)

private def p11329 := certifiedPrime 11329 7 [(p2,6),(p3,1),(p59,1)] (by decide +kernel)

private def p11369 := certifiedPrime 11369 3 [(p2,3),(p7,2),(p29,1)] (by decide +kernel)

private def p11447 := certifiedPrime 11447 5 [(p2,1),(p59,1),(p97,1)] (by decide +kernel)

private def p11483 := certifiedPrime 11483 2 [(p2,1),(p5741,1)] (by decide +kernel)

private def p11497 := certifiedPrime 11497 7 [(p2,3),(p3,1),(p479,1)] (by decide +kernel)

private def p11617 := certifiedPrime 11617 10 [(p2,5),(p3,1),(p11,2)] (by decide +kernel)

private def p11633 := certifiedPrime 11633 3 [(p2,4),(p727,1)] (by decide +kernel)

private def p11657 := certifiedPrime 11657 3 [(p2,3),(p31,1),(p47,1)] (by decide +kernel)

private def p11689 := certifiedPrime 11689 7 [(p2,3),(p3,1),(p487,1)] (by decide +kernel)

private def p11699 := certifiedPrime 11699 2 [(p2,1),(p5849,1)] (by decide +kernel)

private def p11789 := certifiedPrime 11789 2 [(p2,2),(p7,1),(p421,1)] (by decide +kernel)

private def p11821 := certifiedPrime 11821 2 [(p2,2),(p3,1),(p5,1),(p197,1)] (by decide +kernel)

private def p11831 := certifiedPrime 11831 7 [(p2,1),(p5,1),(p7,1),(p13,2)] (by decide +kernel)

private def p11833 := certifiedPrime 11833 5 [(p2,3),(p3,1),(p17,1),(p29,1)] (by decide +kernel)

private def p11903 := certifiedPrime 11903 5 [(p2,1),(p11,1),(p541,1)] (by decide +kernel)

private def p11909 := certifiedPrime 11909 2 [(p2,2),(p13,1),(p229,1)] (by decide +kernel)

private def p11959 := certifiedPrime 11959 3 [(p2,1),(p3,1),(p1993,1)] (by decide +kernel)

private def p11971 := certifiedPrime 11971 10 [(p2,1),(p3,2),(p5,1),(p7,1),(p19,1)] (by decide +kernel)

private def p12097 := certifiedPrime 12097 5 [(p2,6),(p3,3),(p7,1)] (by decide +kernel)

private def p12373 := certifiedPrime 12373 2 [(p2,2),(p3,1),(p1031,1)] (by decide +kernel)

private def p12379 := certifiedPrime 12379 2 [(p2,1),(p3,1),(p2063,1)] (by decide +kernel)

private def p12479 := certifiedPrime 12479 23 [(p2,1),(p17,1),(p367,1)] (by decide +kernel)

private def p12491 := certifiedPrime 12491 2 [(p2,1),(p5,1),(p1249,1)] (by decide +kernel)

private def p12539 := certifiedPrime 12539 2 [(p2,1),(p6269,1)] (by decide +kernel)

private def p12583 := certifiedPrime 12583 5 [(p2,1),(p3,3),(p233,1)] (by decide +kernel)

private def p12601 := certifiedPrime 12601 11 [(p2,3),(p3,2),(p5,2),(p7,1)] (by decide +kernel)

private def p12619 := certifiedPrime 12619 2 [(p2,1),(p3,2),(p701,1)] (by decide +kernel)

private def p12637 := certifiedPrime 12637 2 [(p2,2),(p3,5),(p13,1)] (by decide +kernel)

private def p12721 := certifiedPrime 12721 13 [(p2,4),(p3,1),(p5,1),(p53,1)] (by decide +kernel)

private def p12799 := certifiedPrime 12799 13 [(p2,1),(p3,4),(p79,1)] (by decide +kernel)

private def p12899 := certifiedPrime 12899 2 [(p2,1),(p6449,1)] (by decide +kernel)

private def p12959 := certifiedPrime 12959 7 [(p2,1),(p11,1),(p19,1),(p31,1)] (by decide +kernel)

private def p12983 := certifiedPrime 12983 5 [(p2,1),(p6491,1)] (by decide +kernel)

private def p13003 := certifiedPrime 13003 5 [(p2,1),(p3,1),(p11,1),(p197,1)] (by decide +kernel)

private def p13033 := certifiedPrime 13033 5 [(p2,3),(p3,2),(p181,1)] (by decide +kernel)

private def p13049 := certifiedPrime 13049 3 [(p2,3),(p7,1),(p233,1)] (by decide +kernel)

private def p13187 := certifiedPrime 13187 2 [(p2,1),(p19,1),(p347,1)] (by decide +kernel)

private def p13259 := certifiedPrime 13259 6 [(p2,1),(p7,1),(p947,1)] (by decide +kernel)

private def p13313 := certifiedPrime 13313 3 [(p2,10),(p13,1)] (by decide +kernel)

private def p13367 := certifiedPrime 13367 5 [(p2,1),(p41,1),(p163,1)] (by decide +kernel)

private def p13411 := certifiedPrime 13411 2 [(p2,1),(p3,2),(p5,1),(p149,1)] (by decide +kernel)

private def p13523 := certifiedPrime 13523 2 [(p2,1),(p6761,1)] (by decide +kernel)

private def p13553 := certifiedPrime 13553 3 [(p2,4),(p7,1),(p11,2)] (by decide +kernel)

private def p13669 := certifiedPrime 13669 6 [(p2,2),(p3,1),(p17,1),(p67,1)] (by decide +kernel)

private def p13679 := certifiedPrime 13679 7 [(p2,1),(p7,1),(p977,1)] (by decide +kernel)

private def p13721 := certifiedPrime 13721 3 [(p2,3),(p5,1),(p7,3)] (by decide +kernel)

private def p13729 := certifiedPrime 13729 23 [(p2,5),(p3,1),(p11,1),(p13,1)] (by decide +kernel)

private def p13789 := certifiedPrime 13789 7 [(p2,2),(p3,2),(p383,1)] (by decide +kernel)

private def p13799 := certifiedPrime 13799 7 [(p2,1),(p6899,1)] (by decide +kernel)

private def p13859 := certifiedPrime 13859 2 [(p2,1),(p13,2),(p41,1)] (by decide +kernel)

private def p13873 := certifiedPrime 13873 5 [(p2,4),(p3,1),(p17,2)] (by decide +kernel)

private def p13879 := certifiedPrime 13879 6 [(p2,1),(p3,3),(p257,1)] (by decide +kernel)

private def p13967 := certifiedPrime 13967 5 [(p2,1),(p6983,1)] (by decide +kernel)

private def p13999 := certifiedPrime 13999 3 [(p2,1),(p3,1),(p2333,1)] (by decide +kernel)

private def p14177 := certifiedPrime 14177 3 [(p2,5),(p443,1)] (by decide +kernel)

private def p14197 := certifiedPrime 14197 11 [(p2,2),(p3,1),(p7,1),(p13,2)] (by decide +kernel)

private def p14249 := certifiedPrime 14249 3 [(p2,3),(p13,1),(p137,1)] (by decide +kernel)

private def p14327 := certifiedPrime 14327 5 [(p2,1),(p13,1),(p19,1),(p29,1)] (by decide +kernel)

private def p14489 := certifiedPrime 14489 3 [(p2,3),(p1811,1)] (by decide +kernel)

private def p14549 := certifiedPrime 14549 2 [(p2,2),(p3637,1)] (by decide +kernel)

private def p14621 := certifiedPrime 14621 2 [(p2,2),(p5,1),(p17,1),(p43,1)] (by decide +kernel)

private def p14699 := certifiedPrime 14699 2 [(p2,1),(p7349,1)] (by decide +kernel)

private def p14747 := certifiedPrime 14747 2 [(p2,1),(p73,1),(p101,1)] (by decide +kernel)

private def p14831 := certifiedPrime 14831 11 [(p2,1),(p5,1),(p1483,1)] (by decide +kernel)

private def p14887 := certifiedPrime 14887 3 [(p2,1),(p3,2),(p827,1)] (by decide +kernel)

private def p14929 := certifiedPrime 14929 7 [(p2,4),(p3,1),(p311,1)] (by decide +kernel)

private def p14939 := certifiedPrime 14939 2 [(p2,1),(p7,1),(p11,1),(p97,1)] (by decide +kernel)

private def p14969 := certifiedPrime 14969 3 [(p2,3),(p1871,1)] (by decide +kernel)

private def p14983 := certifiedPrime 14983 3 [(p2,1),(p3,1),(p11,1),(p227,1)] (by decide +kernel)

private def p15173 := certifiedPrime 15173 2 [(p2,2),(p3793,1)] (by decide +kernel)

private def p15259 := certifiedPrime 15259 2 [(p2,1),(p3,1),(p2543,1)] (by decide +kernel)

private def p15299 := certifiedPrime 15299 2 [(p2,1),(p7649,1)] (by decide +kernel)

private def p15359 := certifiedPrime 15359 11 [(p2,1),(p7,1),(p1097,1)] (by decide +kernel)

private def p15451 := certifiedPrime 15451 3 [(p2,1),(p3,1),(p5,2),(p103,1)] (by decide +kernel)

private def p15473 := certifiedPrime 15473 3 [(p2,4),(p967,1)] (by decide +kernel)

private def p15727 := certifiedPrime 15727 3 [(p2,1),(p3,1),(p2621,1)] (by decide +kernel)

private def p15767 := certifiedPrime 15767 5 [(p2,1),(p7883,1)] (by decide +kernel)

private def p15797 := certifiedPrime 15797 2 [(p2,2),(p11,1),(p359,1)] (by decide +kernel)

private def p15887 := certifiedPrime 15887 5 [(p2,1),(p13,2),(p47,1)] (by decide +kernel)

private def p15907 := certifiedPrime 15907 2 [(p2,1),(p3,1),(p11,1),(p241,1)] (by decide +kernel)

private def p15923 := certifiedPrime 15923 2 [(p2,1),(p19,1),(p419,1)] (by decide +kernel)

private def p16111 := certifiedPrime 16111 7 [(p2,1),(p3,2),(p5,1),(p179,1)] (by decide +kernel)

private def p16189 := certifiedPrime 16189 2 [(p2,2),(p3,1),(p19,1),(p71,1)] (by decide +kernel)

private def p16421 := certifiedPrime 16421 2 [(p2,2),(p5,1),(p821,1)] (by decide +kernel)

private def p16487 := certifiedPrime 16487 5 [(p2,1),(p8243,1)] (by decide +kernel)

private def p16519 := certifiedPrime 16519 3 [(p2,1),(p3,1),(p2753,1)] (by decide +kernel)

private def p16573 := certifiedPrime 16573 2 [(p2,2),(p3,1),(p1381,1)] (by decide +kernel)

private def p16633 := certifiedPrime 16633 15 [(p2,3),(p3,3),(p7,1),(p11,1)] (by decide +kernel)

private def p16649 := certifiedPrime 16649 3 [(p2,3),(p2081,1)] (by decide +kernel)

private def p16657 := certifiedPrime 16657 5 [(p2,4),(p3,1),(p347,1)] (by decide +kernel)

private def p16693 := certifiedPrime 16693 2 [(p2,2),(p3,1),(p13,1),(p107,1)] (by decide +kernel)

private def p16741 := certifiedPrime 16741 6 [(p2,2),(p3,3),(p5,1),(p31,1)] (by decide +kernel)

private def p16763 := certifiedPrime 16763 2 [(p2,1),(p17,2),(p29,1)] (by decide +kernel)

private def p16843 := certifiedPrime 16843 2 [(p2,1),(p3,1),(p7,1),(p401,1)] (by decide +kernel)

private def p16883 := certifiedPrime 16883 2 [(p2,1),(p23,1),(p367,1)] (by decide +kernel)

private def p16889 := certifiedPrime 16889 3 [(p2,3),(p2111,1)] (by decide +kernel)

private def p16979 := certifiedPrime 16979 2 [(p2,1),(p13,1),(p653,1)] (by decide +kernel)

private def p16993 := certifiedPrime 16993 10 [(p2,5),(p3,2),(p59,1)] (by decide +kernel)

private def p17047 := certifiedPrime 17047 3 [(p2,1),(p3,2),(p947,1)] (by decide +kernel)

private def p17077 := certifiedPrime 17077 2 [(p2,2),(p3,1),(p1423,1)] (by decide +kernel)

private def p17183 := certifiedPrime 17183 5 [(p2,1),(p11,2),(p71,1)] (by decide +kernel)

private def p17519 := certifiedPrime 17519 13 [(p2,1),(p19,1),(p461,1)] (by decide +kernel)

private def p17599 := certifiedPrime 17599 6 [(p2,1),(p3,1),(p7,1),(p419,1)] (by decide +kernel)

private def p17729 := certifiedPrime 17729 3 [(p2,6),(p277,1)] (by decide +kernel)

private def p17909 := certifiedPrime 17909 2 [(p2,2),(p11,2),(p37,1)] (by decide +kernel)

private def p17977 := certifiedPrime 17977 5 [(p2,3),(p3,1),(p7,1),(p107,1)] (by decide +kernel)

private def p17989 := certifiedPrime 17989 2 [(p2,2),(p3,1),(p1499,1)] (by decide +kernel)

private def p18199 := certifiedPrime 18199 11 [(p2,1),(p3,3),(p337,1)] (by decide +kernel)

private def p18251 := certifiedPrime 18251 2 [(p2,1),(p5,3),(p73,1)] (by decide +kernel)

private def p18443 := certifiedPrime 18443 2 [(p2,1),(p9221,1)] (by decide +kernel)

private def p18637 := certifiedPrime 18637 2 [(p2,2),(p3,1),(p1553,1)] (by decide +kernel)

private def p18671 := certifiedPrime 18671 7 [(p2,1),(p5,1),(p1867,1)] (by decide +kernel)

private def p18691 := certifiedPrime 18691 3 [(p2,1),(p3,1),(p5,1),(p7,1),(p89,1)] (by decide +kernel)

private def p18743 := certifiedPrime 18743 5 [(p2,1),(p9371,1)] (by decide +kernel)

private def p18869 := certifiedPrime 18869 2 [(p2,2),(p53,1),(p89,1)] (by decide +kernel)

private def p18899 := certifiedPrime 18899 2 [(p2,1),(p11,1),(p859,1)] (by decide +kernel)

private def p18959 := certifiedPrime 18959 13 [(p2,1),(p9479,1)] (by decide +kernel)

private def p19079 := certifiedPrime 19079 7 [(p2,1),(p9539,1)] (by decide +kernel)

private def p19207 := certifiedPrime 19207 5 [(p2,1),(p3,2),(p11,1),(p97,1)] (by decide +kernel)

private def p19447 := certifiedPrime 19447 3 [(p2,1),(p3,1),(p7,1),(p463,1)] (by decide +kernel)

private def p19469 := certifiedPrime 19469 2 [(p2,2),(p31,1),(p157,1)] (by decide +kernel)

private def p19699 := certifiedPrime 19699 7 [(p2,1),(p3,1),(p7,2),(p67,1)] (by decide +kernel)

private def p19763 := certifiedPrime 19763 2 [(p2,1),(p41,1),(p241,1)] (by decide +kernel)

private def p19919 := certifiedPrime 19919 7 [(p2,1),(p23,1),(p433,1)] (by decide +kernel)

private def p19949 := certifiedPrime 19949 2 [(p2,2),(p4987,1)] (by decide +kernel)

private def p19979 := certifiedPrime 19979 2 [(p2,1),(p7,1),(p1427,1)] (by decide +kernel)

private def p20089 := certifiedPrime 20089 7 [(p2,3),(p3,4),(p31,1)] (by decide +kernel)

private def p20201 := certifiedPrime 20201 6 [(p2,3),(p5,2),(p101,1)] (by decide +kernel)

private def p20599 := certifiedPrime 20599 3 [(p2,1),(p3,1),(p3433,1)] (by decide +kernel)

private def p20771 := certifiedPrime 20771 2 [(p2,1),(p5,1),(p31,1),(p67,1)] (by decide +kernel)

private def p20903 := certifiedPrime 20903 5 [(p2,1),(p7,1),(p1493,1)] (by decide +kernel)

private def p20929 := certifiedPrime 20929 7 [(p2,6),(p3,1),(p109,1)] (by decide +kernel)

private def p21149 := certifiedPrime 21149 3 [(p2,2),(p17,1),(p311,1)] (by decide +kernel)

private def p21163 := certifiedPrime 21163 2 [(p2,1),(p3,1),(p3527,1)] (by decide +kernel)

private def p21221 := certifiedPrime 21221 2 [(p2,2),(p5,1),(p1061,1)] (by decide +kernel)

private def p21313 := certifiedPrime 21313 5 [(p2,6),(p3,2),(p37,1)] (by decide +kernel)

private def p21407 := certifiedPrime 21407 5 [(p2,1),(p7,1),(p11,1),(p139,1)] (by decide +kernel)

private def p21683 := certifiedPrime 21683 2 [(p2,1),(p37,1),(p293,1)] (by decide +kernel)

private def p21773 := certifiedPrime 21773 2 [(p2,2),(p5443,1)] (by decide +kernel)

private def p21803 := certifiedPrime 21803 2 [(p2,1),(p11,1),(p991,1)] (by decide +kernel)

private def p21839 := certifiedPrime 21839 11 [(p2,1),(p61,1),(p179,1)] (by decide +kernel)

private def p22111 := certifiedPrime 22111 6 [(p2,1),(p3,1),(p5,1),(p11,1),(p67,1)] (by decide +kernel)

private def p22159 := certifiedPrime 22159 6 [(p2,1),(p3,2),(p1231,1)] (by decide +kernel)

private def p22273 := certifiedPrime 22273 5 [(p2,8),(p3,1),(p29,1)] (by decide +kernel)

private def p22283 := certifiedPrime 22283 2 [(p2,1),(p13,1),(p857,1)] (by decide +kernel)

private def p22433 := certifiedPrime 22433 3 [(p2,5),(p701,1)] (by decide +kernel)

private def p22549 := certifiedPrime 22549 2 [(p2,2),(p3,1),(p1879,1)] (by decide +kernel)

private def p22669 := certifiedPrime 22669 2 [(p2,2),(p3,1),(p1889,1)] (by decide +kernel)

private def p22807 := certifiedPrime 22807 3 [(p2,1),(p3,2),(p7,1),(p181,1)] (by decide +kernel)

private def p22993 := certifiedPrime 22993 5 [(p2,4),(p3,1),(p479,1)] (by decide +kernel)

private def p23333 := certifiedPrime 23333 2 [(p2,2),(p19,1),(p307,1)] (by decide +kernel)

private def p23531 := certifiedPrime 23531 2 [(p2,1),(p5,1),(p13,1),(p181,1)] (by decide +kernel)

private def p23663 := certifiedPrime 23663 5 [(p2,1),(p11831,1)] (by decide +kernel)

private def p23743 := certifiedPrime 23743 3 [(p2,1),(p3,2),(p1319,1)] (by decide +kernel)

private def p23789 := certifiedPrime 23789 2 [(p2,2),(p19,1),(p313,1)] (by decide +kernel)

private def p23857 := certifiedPrime 23857 5 [(p2,4),(p3,1),(p7,1),(p71,1)] (by decide +kernel)

private def p23899 := certifiedPrime 23899 2 [(p2,1),(p3,1),(p7,1),(p569,1)] (by decide +kernel)

private def p23911 := certifiedPrime 23911 6 [(p2,1),(p3,1),(p5,1),(p797,1)] (by decide +kernel)

private def p23971 := certifiedPrime 23971 10 [(p2,1),(p3,1),(p5,1),(p17,1),(p47,1)] (by decide +kernel)

private def p24683 := certifiedPrime 24683 2 [(p2,1),(p7,1),(p41,1),(p43,1)] (by decide +kernel)

private def p24749 := certifiedPrime 24749 2 [(p2,2),(p23,1),(p269,1)] (by decide +kernel)

private def p24877 := certifiedPrime 24877 5 [(p2,2),(p3,2),(p691,1)] (by decide +kernel)

private def p25577 := certifiedPrime 25577 3 [(p2,3),(p23,1),(p139,1)] (by decide +kernel)

private def p25673 := certifiedPrime 25673 3 [(p2,3),(p3209,1)] (by decide +kernel)

private def p25703 := certifiedPrime 25703 5 [(p2,1),(p71,1),(p181,1)] (by decide +kernel)

private def p25799 := certifiedPrime 25799 7 [(p2,1),(p12899,1)] (by decide +kernel)

private def p25889 := certifiedPrime 25889 3 [(p2,5),(p809,1)] (by decide +kernel)

private def p25999 := certifiedPrime 25999 7 [(p2,1),(p3,1),(p7,1),(p619,1)] (by decide +kernel)

private def p26107 := certifiedPrime 26107 2 [(p2,1),(p3,1),(p19,1),(p229,1)] (by decide +kernel)

private def p26203 := certifiedPrime 26203 3 [(p2,1),(p3,1),(p11,1),(p397,1)] (by decide +kernel)

private def p26489 := certifiedPrime 26489 3 [(p2,3),(p7,1),(p11,1),(p43,1)] (by decide +kernel)

private def p26561 := certifiedPrime 26561 3 [(p2,6),(p5,1),(p83,1)] (by decide +kernel)

private def p26591 := certifiedPrime 26591 22 [(p2,1),(p5,1),(p2659,1)] (by decide +kernel)

private def p26669 := certifiedPrime 26669 2 [(p2,2),(p59,1),(p113,1)] (by decide +kernel)

private def p26813 := certifiedPrime 26813 2 [(p2,2),(p6703,1)] (by decide +kernel)

private def p26879 := certifiedPrime 26879 13 [(p2,1),(p89,1),(p151,1)] (by decide +kernel)

private def p27059 := certifiedPrime 27059 2 [(p2,1),(p83,1),(p163,1)] (by decide +kernel)

private def p27107 := certifiedPrime 27107 2 [(p2,1),(p13553,1)] (by decide +kernel)

private def p27431 := certifiedPrime 27431 17 [(p2,1),(p5,1),(p13,1),(p211,1)] (by decide +kernel)

private def p27551 := certifiedPrime 27551 17 [(p2,1),(p5,2),(p19,1),(p29,1)] (by decide +kernel)

private def p27611 := certifiedPrime 27611 2 [(p2,1),(p5,1),(p11,1),(p251,1)] (by decide +kernel)

private def p27779 := certifiedPrime 27779 2 [(p2,1),(p17,1),(p19,1),(p43,1)] (by decide +kernel)

private def p27799 := certifiedPrime 27799 7 [(p2,1),(p3,1),(p41,1),(p113,1)] (by decide +kernel)

private def p27809 := certifiedPrime 27809 3 [(p2,5),(p11,1),(p79,1)] (by decide +kernel)

private def p27917 := certifiedPrime 27917 2 [(p2,2),(p7,1),(p997,1)] (by decide +kernel)

private def p27983 := certifiedPrime 27983 5 [(p2,1),(p17,1),(p823,1)] (by decide +kernel)

private def p28499 := certifiedPrime 28499 2 [(p2,1),(p14249,1)] (by decide +kernel)

private def p28901 := certifiedPrime 28901 3 [(p2,2),(p5,2),(p17,2)] (by decide +kernel)

private def p28909 := certifiedPrime 28909 2 [(p2,2),(p3,2),(p11,1),(p73,1)] (by decide +kernel)

private def p28949 := certifiedPrime 28949 2 [(p2,2),(p7237,1)] (by decide +kernel)

private def p28979 := certifiedPrime 28979 2 [(p2,1),(p14489,1)] (by decide +kernel)

private def p29009 := certifiedPrime 29009 3 [(p2,4),(p7,2),(p37,1)] (by decide +kernel)

private def p29207 := certifiedPrime 29207 5 [(p2,1),(p17,1),(p859,1)] (by decide +kernel)

private def p29243 := certifiedPrime 29243 2 [(p2,1),(p14621,1)] (by decide +kernel)

private def p29287 := certifiedPrime 29287 5 [(p2,1),(p3,2),(p1627,1)] (by decide +kernel)

private def p29297 := certifiedPrime 29297 3 [(p2,4),(p1831,1)] (by decide +kernel)

private def p29399 := certifiedPrime 29399 13 [(p2,1),(p14699,1)] (by decide +kernel)

private def p29611 := certifiedPrime 29611 3 [(p2,1),(p3,2),(p5,1),(p7,1),(p47,1)] (by decide +kernel)

private def p29663 := certifiedPrime 29663 5 [(p2,1),(p14831,1)] (by decide +kernel)

private def p29761 := certifiedPrime 29761 17 [(p2,6),(p3,1),(p5,1),(p31,1)] (by decide +kernel)

private def p29879 := certifiedPrime 29879 11 [(p2,1),(p14939,1)] (by decide +kernel)

private def p29983 := certifiedPrime 29983 5 [(p2,1),(p3,1),(p19,1),(p263,1)] (by decide +kernel)

private def p29989 := certifiedPrime 29989 2 [(p2,2),(p3,2),(p7,2),(p17,1)] (by decide +kernel)

private def p30011 := certifiedPrime 30011 2 [(p2,1),(p5,1),(p3001,1)] (by decide +kernel)

private def p30493 := certifiedPrime 30493 6 [(p2,2),(p3,2),(p7,1),(p11,2)] (by decide +kernel)

private def p30577 := certifiedPrime 30577 5 [(p2,4),(p3,1),(p7,2),(p13,1)] (by decide +kernel)

private def p30661 := certifiedPrime 30661 2 [(p2,2),(p3,1),(p5,1),(p7,1),(p73,1)] (by decide +kernel)

private def p30703 := certifiedPrime 30703 3 [(p2,1),(p3,1),(p7,1),(p17,1),(p43,1)] (by decide +kernel)

private def p31223 := certifiedPrime 31223 5 [(p2,1),(p67,1),(p233,1)] (by decide +kernel)

private def p31249 := certifiedPrime 31249 23 [(p2,4),(p3,2),(p7,1),(p31,1)] (by decide +kernel)

private def p31667 := certifiedPrime 31667 2 [(p2,1),(p71,1),(p223,1)] (by decide +kernel)

private def p31847 := certifiedPrime 31847 5 [(p2,1),(p15923,1)] (by decide +kernel)

private def p32359 := certifiedPrime 32359 3 [(p2,1),(p3,1),(p5393,1)] (by decide +kernel)

private def p32719 := certifiedPrime 32719 3 [(p2,1),(p3,1),(p7,1),(p19,1),(p41,1)] (by decide +kernel)

private def p32771 := certifiedPrime 32771 2 [(p2,1),(p5,1),(p29,1),(p113,1)] (by decide +kernel)

private def p33161 := certifiedPrime 33161 3 [(p2,3),(p5,1),(p829,1)] (by decide +kernel)

private def p33211 := certifiedPrime 33211 2 [(p2,1),(p3,4),(p5,1),(p41,1)] (by decide +kernel)

private def p33413 := certifiedPrime 33413 2 [(p2,2),(p8353,1)] (by decide +kernel)

private def p33487 := certifiedPrime 33487 6 [(p2,1),(p3,1),(p5581,1)] (by decide +kernel)

private def p33589 := certifiedPrime 33589 2 [(p2,2),(p3,3),(p311,1)] (by decide +kernel)

private def p33629 := certifiedPrime 33629 2 [(p2,2),(p7,1),(p1201,1)] (by decide +kernel)

private def p33797 := certifiedPrime 33797 3 [(p2,2),(p7,1),(p17,1),(p71,1)] (by decide +kernel)

private def p33941 := certifiedPrime 33941 2 [(p2,2),(p5,1),(p1697,1)] (by decide +kernel)

private def p34061 := certifiedPrime 34061 2 [(p2,2),(p5,1),(p13,1),(p131,1)] (by decide +kernel)

private def p34273 := certifiedPrime 34273 5 [(p2,5),(p3,2),(p7,1),(p17,1)] (by decide +kernel)

private def p34361 := certifiedPrime 34361 3 [(p2,3),(p5,1),(p859,1)] (by decide +kernel)

private def p34439 := certifiedPrime 34439 11 [(p2,1),(p67,1),(p257,1)] (by decide +kernel)

private def p34511 := certifiedPrime 34511 7 [(p2,1),(p5,1),(p7,1),(p17,1),(p29,1)] (by decide +kernel)

private def p34603 := certifiedPrime 34603 2 [(p2,1),(p3,1),(p73,1),(p79,1)] (by decide +kernel)

private def p34673 := certifiedPrime 34673 3 [(p2,4),(p11,1),(p197,1)] (by decide +kernel)

private def p34949 := certifiedPrime 34949 2 [(p2,2),(p8737,1)] (by decide +kernel)

private def p35107 := certifiedPrime 35107 2 [(p2,1),(p3,1),(p5851,1)] (by decide +kernel)

private def p35531 := certifiedPrime 35531 6 [(p2,1),(p5,1),(p11,1),(p17,1),(p19,1)] (by decide +kernel)

private def p35797 := certifiedPrime 35797 2 [(p2,2),(p3,1),(p19,1),(p157,1)] (by decide +kernel)

private def p35839 := certifiedPrime 35839 6 [(p2,1),(p3,2),(p11,1),(p181,1)] (by decide +kernel)

private def p35999 := certifiedPrime 35999 13 [(p2,1),(p41,1),(p439,1)] (by decide +kernel)

private def p36389 := certifiedPrime 36389 3 [(p2,2),(p11,1),(p827,1)] (by decide +kernel)

private def p36529 := certifiedPrime 36529 7 [(p2,4),(p3,1),(p761,1)] (by decide +kernel)

private def p36779 := certifiedPrime 36779 2 [(p2,1),(p7,1),(p37,1),(p71,1)] (by decide +kernel)

private def p36887 := certifiedPrime 36887 5 [(p2,1),(p18443,1)] (by decide +kernel)

private def p36899 := certifiedPrime 36899 2 [(p2,1),(p19,1),(p971,1)] (by decide +kernel)

private def p37501 := certifiedPrime 37501 2 [(p2,2),(p3,1),(p5,5)] (by decide +kernel)

private def p37529 := certifiedPrime 37529 3 [(p2,3),(p4691,1)] (by decide +kernel)

private def p37799 := certifiedPrime 37799 11 [(p2,1),(p18899,1)] (by decide +kernel)

private def p37889 := certifiedPrime 37889 3 [(p2,10),(p37,1)] (by decide +kernel)

private def p37907 := certifiedPrime 37907 2 [(p2,1),(p11,1),(p1723,1)] (by decide +kernel)

private def p38047 := certifiedPrime 38047 3 [(p2,1),(p3,1),(p17,1),(p373,1)] (by decide +kernel)

private def p38287 := certifiedPrime 38287 7 [(p2,1),(p3,3),(p709,1)] (by decide +kernel)

private def p38461 := certifiedPrime 38461 13 [(p2,2),(p3,1),(p5,1),(p641,1)] (by decide +kernel)

private def p38669 := certifiedPrime 38669 2 [(p2,2),(p7,1),(p1381,1)] (by decide +kernel)

private def p39023 := certifiedPrime 39023 5 [(p2,1),(p109,1),(p179,1)] (by decide +kernel)

private def p39047 := certifiedPrime 39047 5 [(p2,1),(p7,1),(p2789,1)] (by decide +kernel)

private def p39443 := certifiedPrime 39443 2 [(p2,1),(p13,1),(p37,1),(p41,1)] (by decide +kernel)

private def p39499 := certifiedPrime 39499 2 [(p2,1),(p3,1),(p29,1),(p227,1)] (by decide +kernel)

private def p39727 := certifiedPrime 39727 3 [(p2,1),(p3,2),(p2207,1)] (by decide +kernel)

private def p39749 := certifiedPrime 39749 2 [(p2,2),(p19,1),(p523,1)] (by decide +kernel)

private def p39799 := certifiedPrime 39799 3 [(p2,1),(p3,3),(p11,1),(p67,1)] (by decide +kernel)

private def p39839 := certifiedPrime 39839 7 [(p2,1),(p19919,1)] (by decide +kernel)

private def p39863 := certifiedPrime 39863 5 [(p2,1),(p19,1),(p1049,1)] (by decide +kernel)

private def p39989 := certifiedPrime 39989 2 [(p2,2),(p13,1),(p769,1)] (by decide +kernel)

private def p42073 := certifiedPrime 42073 5 [(p2,3),(p3,1),(p1753,1)] (by decide +kernel)

private def p42221 := certifiedPrime 42221 2 [(p2,2),(p5,1),(p2111,1)] (by decide +kernel)

private def p42299 := certifiedPrime 42299 2 [(p2,1),(p21149,1)] (by decide +kernel)

private def p42463 := certifiedPrime 42463 3 [(p2,1),(p3,2),(p7,1),(p337,1)] (by decide +kernel)

private def p42929 := certifiedPrime 42929 3 [(p2,4),(p2683,1)] (by decide +kernel)

private def p43103 := certifiedPrime 43103 5 [(p2,1),(p23,1),(p937,1)] (by decide +kernel)

private def p43717 := certifiedPrime 43717 5 [(p2,2),(p3,1),(p3643,1)] (by decide +kernel)

private def p44273 := certifiedPrime 44273 3 [(p2,4),(p2767,1)] (by decide +kernel)

private def p44959 := certifiedPrime 44959 3 [(p2,1),(p3,1),(p59,1),(p127,1)] (by decide +kernel)

private def p45281 := certifiedPrime 45281 3 [(p2,5),(p5,1),(p283,1)] (by decide +kernel)

private def p45989 := certifiedPrime 45989 2 [(p2,2),(p11497,1)] (by decide +kernel)

private def p46477 := certifiedPrime 46477 2 [(p2,2),(p3,2),(p1291,1)] (by decide +kernel)

private def p46889 := certifiedPrime 46889 3 [(p2,3),(p5861,1)] (by decide +kernel)

private def p46997 := certifiedPrime 46997 2 [(p2,2),(p31,1),(p379,1)] (by decide +kernel)

private def p47041 := certifiedPrime 47041 29 [(p2,6),(p3,1),(p5,1),(p7,2)] (by decide +kernel)

private def p47189 := certifiedPrime 47189 2 [(p2,2),(p47,1),(p251,1)] (by decide +kernel)

private def p47857 := certifiedPrime 47857 7 [(p2,4),(p3,1),(p997,1)] (by decide +kernel)

private def p48371 := certifiedPrime 48371 2 [(p2,1),(p5,1),(p7,1),(p691,1)] (by decide +kernel)

private def p48589 := certifiedPrime 48589 10 [(p2,2),(p3,1),(p4049,1)] (by decide +kernel)

private def p48787 := certifiedPrime 48787 2 [(p2,1),(p3,1),(p47,1),(p173,1)] (by decide +kernel)

private def p48809 := certifiedPrime 48809 3 [(p2,3),(p6101,1)] (by decide +kernel)

private def p48889 := certifiedPrime 48889 34 [(p2,3),(p3,2),(p7,1),(p97,1)] (by decide +kernel)

private def p48907 := certifiedPrime 48907 2 [(p2,1),(p3,2),(p11,1),(p13,1),(p19,1)] (by decide +kernel)

private def p48989 := certifiedPrime 48989 2 [(p2,2),(p37,1),(p331,1)] (by decide +kernel)

private def p49499 := certifiedPrime 49499 2 [(p2,1),(p24749,1)] (by decide +kernel)

private def p49787 := certifiedPrime 49787 2 [(p2,1),(p11,1),(p31,1),(p73,1)] (by decide +kernel)

private def p49999 := certifiedPrime 49999 3 [(p2,1),(p3,1),(p13,1),(p641,1)] (by decide +kernel)

private def p50051 := certifiedPrime 50051 2 [(p2,1),(p5,2),(p7,1),(p11,1),(p13,1)] (by decide +kernel)

private def p50383 := certifiedPrime 50383 3 [(p2,1),(p3,4),(p311,1)] (by decide +kernel)

private def p50503 := certifiedPrime 50503 5 [(p2,1),(p3,1),(p19,1),(p443,1)] (by decide +kernel)

private def p50549 := certifiedPrime 50549 2 [(p2,2),(p12637,1)] (by decide +kernel)

private def p53323 := certifiedPrime 53323 2 [(p2,1),(p3,1),(p8887,1)] (by decide +kernel)

private def p53377 := certifiedPrime 53377 5 [(p2,7),(p3,1),(p139,1)] (by decide +kernel)

private def p53693 := certifiedPrime 53693 2 [(p2,2),(p31,1),(p433,1)] (by decide +kernel)

private def p53773 := certifiedPrime 53773 2 [(p2,2),(p3,1),(p4481,1)] (by decide +kernel)

private def p53923 := certifiedPrime 53923 5 [(p2,1),(p3,1),(p11,1),(p19,1),(p43,1)] (by decide +kernel)

private def p55259 := certifiedPrime 55259 6 [(p2,1),(p7,1),(p3947,1)] (by decide +kernel)

private def p55619 := certifiedPrime 55619 2 [(p2,1),(p27809,1)] (by decide +kernel)

private def p55673 := certifiedPrime 55673 3 [(p2,3),(p6959,1)] (by decide +kernel)

private def p55807 := certifiedPrime 55807 3 [(p2,1),(p3,1),(p71,1),(p131,1)] (by decide +kernel)

private def p56473 := certifiedPrime 56473 5 [(p2,3),(p3,1),(p13,1),(p181,1)] (by decide +kernel)

private def p56897 := certifiedPrime 56897 5 [(p2,6),(p7,1),(p127,1)] (by decide +kernel)

private def p56989 := certifiedPrime 56989 6 [(p2,2),(p3,2),(p1583,1)] (by decide +kernel)

private def p56999 := certifiedPrime 56999 13 [(p2,1),(p28499,1)] (by decide +kernel)

private def p57259 := certifiedPrime 57259 2 [(p2,1),(p3,2),(p3181,1)] (by decide +kernel)

private def p57899 := certifiedPrime 57899 2 [(p2,1),(p28949,1)] (by decide +kernel)

private def p58391 := certifiedPrime 58391 11 [(p2,1),(p5,1),(p5839,1)] (by decide +kernel)

private def p58789 := certifiedPrime 58789 2 [(p2,2),(p3,2),(p23,1),(p71,1)] (by decide +kernel)

private def p58889 := certifiedPrime 58889 3 [(p2,3),(p17,1),(p433,1)] (by decide +kernel)

private def p59341 := certifiedPrime 59341 14 [(p2,2),(p3,1),(p5,1),(p23,1),(p43,1)] (by decide +kernel)

private def p59669 := certifiedPrime 59669 2 [(p2,2),(p7,1),(p2131,1)] (by decide +kernel)

private def p59707 := certifiedPrime 59707 3 [(p2,1),(p3,2),(p31,1),(p107,1)] (by decide +kernel)

private def p59779 := certifiedPrime 59779 10 [(p2,1),(p3,6),(p41,1)] (by decide +kernel)

private def p59999 := certifiedPrime 59999 7 [(p2,1),(p131,1),(p229,1)] (by decide +kernel)

private def p60037 := certifiedPrime 60037 2 [(p2,2),(p3,1),(p5003,1)] (by decide +kernel)

private def p60101 := certifiedPrime 60101 3 [(p2,2),(p5,2),(p601,1)] (by decide +kernel)

private def p60679 := certifiedPrime 60679 3 [(p2,1),(p3,2),(p3371,1)] (by decide +kernel)

private def p61211 := certifiedPrime 61211 2 [(p2,1),(p5,1),(p6121,1)] (by decide +kernel)

private def p61483 := certifiedPrime 61483 2 [(p2,1),(p3,1),(p10247,1)] (by decide +kernel)

private def p61687 := certifiedPrime 61687 6 [(p2,1),(p3,2),(p23,1),(p149,1)] (by decide +kernel)

private def p61843 := certifiedPrime 61843 2 [(p2,1),(p3,1),(p11,1),(p937,1)] (by decide +kernel)

private def p62819 := certifiedPrime 62819 2 [(p2,1),(p7,2),(p641,1)] (by decide +kernel)

private def p62989 := certifiedPrime 62989 2 [(p2,2),(p3,1),(p29,1),(p181,1)] (by decide +kernel)

private def p64567 := certifiedPrime 64567 3 [(p2,1),(p3,2),(p17,1),(p211,1)] (by decide +kernel)

private def p65839 := certifiedPrime 65839 3 [(p2,1),(p3,1),(p10973,1)] (by decide +kernel)

private def p66293 := certifiedPrime 66293 2 [(p2,2),(p16573,1)] (by decide +kernel)

private def p66629 := certifiedPrime 66629 2 [(p2,2),(p16657,1)] (by decide +kernel)

private def p66749 := certifiedPrime 66749 3 [(p2,2),(p11,1),(p37,1),(p41,1)] (by decide +kernel)

private def p66889 := certifiedPrime 66889 17 [(p2,3),(p3,2),(p929,1)] (by decide +kernel)

private def p67979 := certifiedPrime 67979 2 [(p2,1),(p41,1),(p829,1)] (by decide +kernel)

private def p68389 := certifiedPrime 68389 2 [(p2,2),(p3,1),(p41,1),(p139,1)] (by decide +kernel)

private def p68489 := certifiedPrime 68489 3 [(p2,3),(p7,1),(p1223,1)] (by decide +kernel)

private def p68491 := certifiedPrime 68491 10 [(p2,1),(p3,2),(p5,1),(p761,1)] (by decide +kernel)

private def p68683 := certifiedPrime 68683 2 [(p2,1),(p3,1),(p11447,1)] (by decide +kernel)

private def p68687 := certifiedPrime 68687 5 [(p2,1),(p61,1),(p563,1)] (by decide +kernel)

private def p68729 := certifiedPrime 68729 3 [(p2,3),(p11,2),(p71,1)] (by decide +kernel)

private def p68879 := certifiedPrime 68879 13 [(p2,1),(p34439,1)] (by decide +kernel)

private def p68899 := certifiedPrime 68899 2 [(p2,1),(p3,1),(p11483,1)] (by decide +kernel)

private def p69499 := certifiedPrime 69499 3 [(p2,1),(p3,5),(p11,1),(p13,1)] (by decide +kernel)

private def p69779 := certifiedPrime 69779 2 [(p2,1),(p139,1),(p251,1)] (by decide +kernel)

private def p69899 := certifiedPrime 69899 2 [(p2,1),(p34949,1)] (by decide +kernel)

private def p69997 := certifiedPrime 69997 2 [(p2,2),(p3,1),(p19,1),(p307,1)] (by decide +kernel)

private def p70607 := certifiedPrime 70607 5 [(p2,1),(p43,1),(p821,1)] (by decide +kernel)

private def p70979 := certifiedPrime 70979 2 [(p2,1),(p23,1),(p1543,1)] (by decide +kernel)

private def p70999 := certifiedPrime 70999 11 [(p2,1),(p3,1),(p11833,1)] (by decide +kernel)

private def p71191 := certifiedPrime 71191 3 [(p2,1),(p3,2),(p5,1),(p7,1),(p113,1)] (by decide +kernel)

private def p71419 := certifiedPrime 71419 2 [(p2,1),(p3,1),(p11903,1)] (by decide +kernel)

private def p72973 := certifiedPrime 72973 2 [(p2,2),(p3,2),(p2027,1)] (by decide +kernel)

private def p74509 := certifiedPrime 74509 2 [(p2,2),(p3,1),(p7,1),(p887,1)] (by decide +kernel)

private def p75511 := certifiedPrime 75511 3 [(p2,1),(p3,2),(p5,1),(p839,1)] (by decide +kernel)

private def p76091 := certifiedPrime 76091 2 [(p2,1),(p5,1),(p7,1),(p1087,1)] (by decide +kernel)

private def p76781 := certifiedPrime 76781 2 [(p2,2),(p5,1),(p11,1),(p349,1)] (by decide +kernel)

private def p77899 := certifiedPrime 77899 14 [(p2,1),(p3,1),(p12983,1)] (by decide +kernel)

private def p77999 := certifiedPrime 77999 11 [(p2,1),(p59,1),(p661,1)] (by decide +kernel)

private def p78041 := certifiedPrime 78041 3 [(p2,3),(p5,1),(p1951,1)] (by decide +kernel)

private def p78887 := certifiedPrime 78887 5 [(p2,1),(p39443,1)] (by decide +kernel)

private def p78889 := certifiedPrime 78889 11 [(p2,3),(p3,1),(p19,1),(p173,1)] (by decide +kernel)

private def p78989 := certifiedPrime 78989 2 [(p2,2),(p7,2),(p13,1),(p31,1)] (by decide +kernel)

private def p79999 := certifiedPrime 79999 3 [(p2,1),(p3,1),(p67,1),(p199,1)] (by decide +kernel)

private def p82073 := certifiedPrime 82073 3 [(p2,3),(p10259,1)] (by decide +kernel)

private def p82499 := certifiedPrime 82499 6 [(p2,1),(p13,1),(p19,1),(p167,1)] (by decide +kernel)

private def p83417 := certifiedPrime 83417 3 [(p2,3),(p10427,1)] (by decide +kernel)

private def p83717 := certifiedPrime 83717 2 [(p2,2),(p20929,1)] (by decide +kernel)

private def p84443 := certifiedPrime 84443 2 [(p2,1),(p42221,1)] (by decide +kernel)

private def p84449 := certifiedPrime 84449 3 [(p2,5),(p7,1),(p13,1),(p29,1)] (by decide +kernel)

private def p85999 := certifiedPrime 85999 3 [(p2,1),(p3,1),(p11,1),(p1303,1)] (by decide +kernel)

private def p86249 := certifiedPrime 86249 3 [(p2,3),(p10781,1)] (by decide +kernel)

private def p86311 := certifiedPrime 86311 3 [(p2,1),(p3,2),(p5,1),(p7,1),(p137,1)] (by decide +kernel)

private def p86423 := certifiedPrime 86423 5 [(p2,1),(p7,1),(p6173,1)] (by decide +kernel)

private def p87959 := certifiedPrime 87959 7 [(p2,1),(p13,1),(p17,1),(p199,1)] (by decide +kernel)

private def p88819 := certifiedPrime 88819 2 [(p2,1),(p3,1),(p113,1),(p131,1)] (by decide +kernel)

private def p88883 := certifiedPrime 88883 2 [(p2,1),(p19,1),(p2339,1)] (by decide +kernel)

private def p88951 := certifiedPrime 88951 3 [(p2,1),(p3,1),(p5,2),(p593,1)] (by decide +kernel)

private def p88993 := certifiedPrime 88993 5 [(p2,5),(p3,3),(p103,1)] (by decide +kernel)

private def p89899 := certifiedPrime 89899 2 [(p2,1),(p3,1),(p14983,1)] (by decide +kernel)

private def p90289 := certifiedPrime 90289 23 [(p2,4),(p3,3),(p11,1),(p19,1)] (by decide +kernel)

private def p90793 := certifiedPrime 90793 5 [(p2,3),(p3,2),(p13,1),(p97,1)] (by decide +kernel)

private def p91577 := certifiedPrime 91577 3 [(p2,3),(p11447,1)] (by decide +kernel)

private def p91837 := certifiedPrime 91837 2 [(p2,2),(p3,2),(p2551,1)] (by decide +kernel)

private def p92707 := certifiedPrime 92707 2 [(p2,1),(p3,1),(p15451,1)] (by decide +kernel)

private def p97499 := certifiedPrime 97499 2 [(p2,1),(p29,1),(p41,2)] (by decide +kernel)

private def p98779 := certifiedPrime 98779 2 [(p2,1),(p3,1),(p101,1),(p163,1)] (by decide +kernel)

private def p98999 := certifiedPrime 98999 19 [(p2,1),(p49499,1)] (by decide +kernel)

private def p99013 := certifiedPrime 99013 6 [(p2,2),(p3,1),(p37,1),(p223,1)] (by decide +kernel)

private def p99833 := certifiedPrime 99833 3 [(p2,3),(p12479,1)] (by decide +kernel)

private def p99991 := certifiedPrime 99991 6 [(p2,1),(p3,2),(p5,1),(p11,1),(p101,1)] (by decide +kernel)

private def p100103 := certifiedPrime 100103 5 [(p2,1),(p50051,1)] (by decide +kernel)

private def p100907 := certifiedPrime 100907 2 [(p2,1),(p13,1),(p3881,1)] (by decide +kernel)

private def p101111 := certifiedPrime 101111 17 [(p2,1),(p5,1),(p10111,1)] (by decide +kernel)

private def p102593 := certifiedPrime 102593 3 [(p2,6),(p7,1),(p229,1)] (by decide +kernel)

private def p103333 := certifiedPrime 103333 2 [(p2,2),(p3,1),(p79,1),(p109,1)] (by decide +kernel)

private def p103393 := certifiedPrime 103393 5 [(p2,5),(p3,2),(p359,1)] (by decide +kernel)

private def p104801 := certifiedPrime 104801 13 [(p2,5),(p5,2),(p131,1)] (by decide +kernel)

private def p106031 := certifiedPrime 106031 19 [(p2,1),(p5,1),(p23,1),(p461,1)] (by decide +kernel)

private def p106783 := certifiedPrime 106783 5 [(p2,1),(p3,1),(p13,1),(p37,2)] (by decide +kernel)

private def p107621 := certifiedPrime 107621 2 [(p2,2),(p5,1),(p5381,1)] (by decide +kernel)

private def p110863 := certifiedPrime 110863 5 [(p2,1),(p3,3),(p2053,1)] (by decide +kernel)

private def p112031 := certifiedPrime 112031 19 [(p2,1),(p5,1),(p17,1),(p659,1)] (by decide +kernel)

private def p112121 := certifiedPrime 112121 3 [(p2,3),(p5,1),(p2803,1)] (by decide +kernel)

private def p112223 := certifiedPrime 112223 5 [(p2,1),(p11,1),(p5101,1)] (by decide +kernel)

private def p112361 := certifiedPrime 112361 3 [(p2,3),(p5,1),(p53,2)] (by decide +kernel)

private def p115151 := certifiedPrime 115151 11 [(p2,1),(p5,2),(p7,2),(p47,1)] (by decide +kernel)

private def p115471 := certifiedPrime 115471 6 [(p2,1),(p3,2),(p5,1),(p1283,1)] (by decide +kernel)

private def p115873 := certifiedPrime 115873 5 [(p2,5),(p3,1),(p17,1),(p71,1)] (by decide +kernel)

private def p115981 := certifiedPrime 115981 7 [(p2,2),(p3,1),(p5,1),(p1933,1)] (by decide +kernel)

private def p116959 := certifiedPrime 116959 3 [(p2,1),(p3,1),(p101,1),(p193,1)] (by decide +kernel)

private def p117979 := certifiedPrime 117979 10 [(p2,1),(p3,1),(p7,1),(p53,2)] (by decide +kernel)

private def p118423 := certifiedPrime 118423 3 [(p2,1),(p3,4),(p17,1),(p43,1)] (by decide +kernel)

private def p120833 := certifiedPrime 120833 3 [(p2,11),(p59,1)] (by decide +kernel)

private def p121993 := certifiedPrime 121993 10 [(p2,3),(p3,1),(p13,1),(p17,1),(p23,1)] (by decide +kernel)

private def p122201 := certifiedPrime 122201 3 [(p2,3),(p5,2),(p13,1),(p47,1)] (by decide +kernel)

private def p122497 := certifiedPrime 122497 15 [(p2,7),(p3,1),(p11,1),(p29,1)] (by decide +kernel)

private def p125921 := certifiedPrime 125921 3 [(p2,5),(p5,1),(p787,1)] (by decide +kernel)

private def p126097 := certifiedPrime 126097 5 [(p2,4),(p3,1),(p37,1),(p71,1)] (by decide +kernel)

private def p128591 := certifiedPrime 128591 14 [(p2,1),(p5,1),(p7,1),(p11,1),(p167,1)] (by decide +kernel)

private def p129959 := certifiedPrime 129959 7 [(p2,1),(p181,1),(p359,1)] (by decide +kernel)

private def p131149 := certifiedPrime 131149 10 [(p2,2),(p3,2),(p3643,1)] (by decide +kernel)

private def p132257 := certifiedPrime 132257 3 [(p2,5),(p4133,1)] (by decide +kernel)

private def p133481 := certifiedPrime 133481 3 [(p2,3),(p5,1),(p47,1),(p71,1)] (by decide +kernel)

private def p133499 := certifiedPrime 133499 2 [(p2,1),(p66749,1)] (by decide +kernel)

private def p133657 := certifiedPrime 133657 7 [(p2,3),(p3,1),(p5569,1)] (by decide +kernel)

private def p133949 := certifiedPrime 133949 2 [(p2,2),(p33487,1)] (by decide +kernel)

private def p134503 := certifiedPrime 134503 6 [(p2,1),(p3,1),(p29,1),(p773,1)] (by decide +kernel)

private def p135283 := certifiedPrime 135283 7 [(p2,1),(p3,1),(p7,1),(p3221,1)] (by decide +kernel)

private def p135607 := certifiedPrime 135607 3 [(p2,1),(p3,1),(p97,1),(p233,1)] (by decide +kernel)

private def p136691 := certifiedPrime 136691 6 [(p2,1),(p5,1),(p13669,1)] (by decide +kernel)

private def p136979 := certifiedPrime 136979 2 [(p2,1),(p68489,1)] (by decide +kernel)

private def p137771 := certifiedPrime 137771 10 [(p2,1),(p5,1),(p23,1),(p599,1)] (by decide +kernel)

private def p137999 := certifiedPrime 137999 7 [(p2,1),(p7,1),(p9857,1)] (by decide +kernel)

private def p139837 := certifiedPrime 139837 2 [(p2,2),(p3,1),(p43,1),(p271,1)] (by decide +kernel)

private def p139999 := certifiedPrime 139999 3 [(p2,1),(p3,1),(p23333,1)] (by decide +kernel)

private def p140449 := certifiedPrime 140449 17 [(p2,5),(p3,1),(p7,1),(p11,1),(p19,1)] (by decide +kernel)

private def p141499 := certifiedPrime 141499 13 [(p2,1),(p3,2),(p7,1),(p1123,1)] (by decide +kernel)

private def p147937 := certifiedPrime 147937 5 [(p2,5),(p3,1),(p23,1),(p67,1)] (by decide +kernel)

private def p148537 := certifiedPrime 148537 10 [(p2,3),(p3,2),(p2063,1)] (by decide +kernel)

private def p148549 := certifiedPrime 148549 6 [(p2,2),(p3,1),(p12379,1)] (by decide +kernel)

private def p149771 := certifiedPrime 149771 6 [(p2,1),(p5,1),(p17,1),(p881,1)] (by decide +kernel)

private def p152429 := certifiedPrime 152429 2 [(p2,2),(p53,1),(p719,1)] (by decide +kernel)

private def p154043 := certifiedPrime 154043 2 [(p2,1),(p7,1),(p11003,1)] (by decide +kernel)

private def p154823 := certifiedPrime 154823 5 [(p2,1),(p199,1),(p389,1)] (by decide +kernel)

private def p156899 := certifiedPrime 156899 2 [(p2,1),(p7,2),(p1601,1)] (by decide +kernel)

private def p157799 := certifiedPrime 157799 11 [(p2,1),(p257,1),(p307,1)] (by decide +kernel)

private def p157889 := certifiedPrime 157889 3 [(p2,6),(p2467,1)] (by decide +kernel)

private def p157999 := certifiedPrime 157999 3 [(p2,1),(p3,1),(p17,1),(p1549,1)] (by decide +kernel)

private def p158329 := certifiedPrime 158329 13 [(p2,3),(p3,3),(p733,1)] (by decide +kernel)

private def p158909 := certifiedPrime 158909 2 [(p2,2),(p39727,1)] (by decide +kernel)

private def p159199 := certifiedPrime 159199 12 [(p2,1),(p3,1),(p13,2),(p157,1)] (by decide +kernel)

private def p159899 := certifiedPrime 159899 2 [(p2,1),(p31,1),(p2579,1)] (by decide +kernel)

private def p162229 := certifiedPrime 162229 6 [(p2,2),(p3,1),(p11,1),(p1229,1)] (by decide +kernel)

private def p164149 := certifiedPrime 164149 2 [(p2,2),(p3,1),(p13679,1)] (by decide +kernel)

private def p165047 := certifiedPrime 165047 5 [(p2,1),(p7,1),(p11789,1)] (by decide +kernel)

private def p166301 := certifiedPrime 166301 2 [(p2,2),(p5,2),(p1663,1)] (by decide +kernel)

private def p166667 := certifiedPrime 166667 2 [(p2,1),(p167,1),(p499,1)] (by decide +kernel)

private def p167413 := certifiedPrime 167413 2 [(p2,2),(p3,1),(p7,1),(p1993,1)] (by decide +kernel)

private def p167777 := certifiedPrime 167777 5 [(p2,5),(p7,2),(p107,1)] (by decide +kernel)

private def p167899 := certifiedPrime 167899 3 [(p2,1),(p3,1),(p27983,1)] (by decide +kernel)

private def p168869 := certifiedPrime 168869 2 [(p2,2),(p7,1),(p37,1),(p163,1)] (by decide +kernel)

private def p168887 := certifiedPrime 168887 5 [(p2,1),(p84443,1)] (by decide +kernel)

private def p168899 := certifiedPrime 168899 2 [(p2,1),(p84449,1)] (by decide +kernel)

private def p172999 := certifiedPrime 172999 6 [(p2,1),(p3,2),(p7,1),(p1373,1)] (by decide +kernel)

private def p175909 := certifiedPrime 175909 2 [(p2,2),(p3,1),(p107,1),(p137,1)] (by decide +kernel)

private def p176417 := certifiedPrime 176417 3 [(p2,5),(p37,1),(p149,1)] (by decide +kernel)

private def p176923 := certifiedPrime 176923 2 [(p2,1),(p3,2),(p9829,1)] (by decide +kernel)

private def p177979 := certifiedPrime 177979 3 [(p2,1),(p3,1),(p29663,1)] (by decide +kernel)

private def p178889 := certifiedPrime 178889 3 [(p2,3),(p59,1),(p379,1)] (by decide +kernel)

private def p178907 := certifiedPrime 178907 2 [(p2,1),(p7,1),(p13,1),(p983,1)] (by decide +kernel)

private def p179899 := certifiedPrime 179899 2 [(p2,1),(p3,1),(p29983,1)] (by decide +kernel)

private def p179969 := certifiedPrime 179969 3 [(p2,8),(p19,1),(p37,1)] (by decide +kernel)

private def p179999 := certifiedPrime 179999 7 [(p2,1),(p7,1),(p13,1),(p23,1),(p43,1)] (by decide +kernel)

private def p180281 := certifiedPrime 180281 3 [(p2,3),(p5,1),(p4507,1)] (by decide +kernel)

private def p185183 := certifiedPrime 185183 5 [(p2,1),(p53,1),(p1747,1)] (by decide +kernel)

private def p185677 := certifiedPrime 185677 5 [(p2,2),(p3,1),(p15473,1)] (by decide +kernel)

private def p186773 := certifiedPrime 186773 2 [(p2,2),(p53,1),(p881,1)] (by decide +kernel)

private def p188999 := certifiedPrime 188999 13 [(p2,1),(p53,1),(p1783,1)] (by decide +kernel)

private def p189199 := certifiedPrime 189199 3 [(p2,1),(p3,2),(p23,1),(p457,1)] (by decide +kernel)

private def p192149 := certifiedPrime 192149 2 [(p2,2),(p11,2),(p397,1)] (by decide +kernel)

private def p196961 := certifiedPrime 196961 6 [(p2,5),(p5,1),(p1231,1)] (by decide +kernel)

private def p197831 := certifiedPrime 197831 7 [(p2,1),(p5,1),(p73,1),(p271,1)] (by decide +kernel)

private def p199999 := certifiedPrime 199999 3 [(p2,1),(p3,2),(p41,1),(p271,1)] (by decide +kernel)

private def p202907 := certifiedPrime 202907 2 [(p2,1),(p11,1),(p23,1),(p401,1)] (by decide +kernel)

private def p204367 := certifiedPrime 204367 5 [(p2,1),(p3,1),(p34061,1)] (by decide +kernel)

private def p204427 := certifiedPrime 204427 5 [(p2,1),(p3,2),(p41,1),(p277,1)] (by decide +kernel)

private def p204521 := certifiedPrime 204521 3 [(p2,3),(p5,1),(p5113,1)] (by decide +kernel)

private def p205187 := certifiedPrime 205187 2 [(p2,1),(p102593,1)] (by decide +kernel)

private def p206413 := certifiedPrime 206413 2 [(p2,2),(p3,1),(p103,1),(p167,1)] (by decide +kernel)

private def p207619 := certifiedPrime 207619 3 [(p2,1),(p3,1),(p34603,1)] (by decide +kernel)

private def p207877 := certifiedPrime 207877 6 [(p2,2),(p3,1),(p17,1),(p1019,1)] (by decide +kernel)

private def p211777 := certifiedPrime 211777 10 [(p2,6),(p3,1),(p1103,1)] (by decide +kernel)

private def p213637 := certifiedPrime 213637 2 [(p2,2),(p3,1),(p19,1),(p937,1)] (by decide +kernel)

private def p213641 := certifiedPrime 213641 3 [(p2,3),(p5,1),(p7,2),(p109,1)] (by decide +kernel)

private def p222461 := certifiedPrime 222461 2 [(p2,2),(p5,1),(p7,2),(p227,1)] (by decide +kernel)

private def p222499 := certifiedPrime 222499 2 [(p2,1),(p3,2),(p47,1),(p263,1)] (by decide +kernel)

private def p225089 := certifiedPrime 225089 3 [(p2,6),(p3517,1)] (by decide +kernel)

private def p230303 := certifiedPrime 230303 5 [(p2,1),(p115151,1)] (by decide +kernel)

private def p233941 := certifiedPrime 233941 34 [(p2,2),(p3,1),(p5,1),(p7,1),(p557,1)] (by decide +kernel)

private def p234989 := certifiedPrime 234989 2 [(p2,2),(p13,1),(p4519,1)] (by decide +kernel)

private def p239297 := certifiedPrime 239297 3 [(p2,6),(p3739,1)] (by decide +kernel)

private def p239999 := certifiedPrime 239999 7 [(p2,1),(p11,1),(p10909,1)] (by decide +kernel)

private def p241291 := certifiedPrime 241291 2 [(p2,1),(p3,2),(p5,1),(p7,1),(p383,1)] (by decide +kernel)

private def p243953 := certifiedPrime 243953 3 [(p2,4),(p79,1),(p193,1)] (by decide +kernel)

private def p247069 := certifiedPrime 247069 2 [(p2,2),(p3,2),(p6863,1)] (by decide +kernel)

private def p247337 := certifiedPrime 247337 3 [(p2,3),(p43,1),(p719,1)] (by decide +kernel)

private def p248597 := certifiedPrime 248597 2 [(p2,2),(p19,1),(p3271,1)] (by decide +kernel)

private def p249857 := certifiedPrime 249857 3 [(p2,12),(p61,1)] (by decide +kernel)

private def p250837 := certifiedPrime 250837 7 [(p2,2),(p3,1),(p20903,1)] (by decide +kernel)

private def p252169 := certifiedPrime 252169 23 [(p2,3),(p3,1),(p7,1),(p19,1),(p79,1)] (by decide +kernel)

private def p254777 := certifiedPrime 254777 3 [(p2,3),(p31847,1)] (by decide +kernel)

private def p255443 := certifiedPrime 255443 2 [(p2,1),(p11,1),(p17,1),(p683,1)] (by decide +kernel)

private def p255641 := certifiedPrime 255641 6 [(p2,3),(p5,1),(p7,1),(p11,1),(p83,1)] (by decide +kernel)

private def p260207 := certifiedPrime 260207 5 [(p2,1),(p281,1),(p463,1)] (by decide +kernel)

private def p260573 := certifiedPrime 260573 2 [(p2,2),(p13,1),(p5011,1)] (by decide +kernel)

private def p264697 := certifiedPrime 264697 7 [(p2,3),(p3,1),(p41,1),(p269,1)] (by decide +kernel)

private def p266129 := certifiedPrime 266129 3 [(p2,4),(p16633,1)] (by decide +kernel)

private def p266797 := certifiedPrime 266797 2 [(p2,2),(p3,2),(p7411,1)] (by decide +kernel)

private def p266999 := certifiedPrime 266999 13 [(p2,1),(p133499,1)] (by decide +kernel)

private def p267857 := certifiedPrime 267857 3 [(p2,4),(p16741,1)] (by decide +kernel)

private def p267899 := certifiedPrime 267899 2 [(p2,1),(p133949,1)] (by decide +kernel)

private def p268999 := certifiedPrime 268999 3 [(p2,1),(p3,1),(p107,1),(p419,1)] (by decide +kernel)

private def p269131 := certifiedPrime 269131 3 [(p2,1),(p3,1),(p5,1),(p8971,1)] (by decide +kernel)

private def p271967 := certifiedPrime 271967 5 [(p2,1),(p17,1),(p19,1),(p421,1)] (by decide +kernel)

private def p272549 := certifiedPrime 272549 2 [(p2,2),(p61,1),(p1117,1)] (by decide +kernel)

private def p275543 := certifiedPrime 275543 5 [(p2,1),(p137771,1)] (by decide +kernel)

private def p275999 := certifiedPrime 275999 11 [(p2,1),(p137999,1)] (by decide +kernel)

private def p277889 := certifiedPrime 277889 3 [(p2,7),(p13,1),(p167,1)] (by decide +kernel)

private def p277999 := certifiedPrime 277999 3 [(p2,1),(p3,1),(p7,1),(p6619,1)] (by decide +kernel)

private def p278123 := certifiedPrime 278123 2 [(p2,1),(p13,1),(p19,1),(p563,1)] (by decide +kernel)

private def p279779 := certifiedPrime 279779 2 [(p2,1),(p59,1),(p2371,1)] (by decide +kernel)

private def p283027 := certifiedPrime 283027 2 [(p2,1),(p3,1),(p43,1),(p1097,1)] (by decide +kernel)

private def p284819 := certifiedPrime 284819 2 [(p2,1),(p17,1),(p8377,1)] (by decide +kernel)

private def p285161 := certifiedPrime 285161 3 [(p2,3),(p5,1),(p7129,1)] (by decide +kernel)

private def p288913 := certifiedPrime 288913 10 [(p2,4),(p3,1),(p13,1),(p463,1)] (by decide +kernel)

private def p288989 := certifiedPrime 288989 3 [(p2,2),(p7,1),(p10321,1)] (by decide +kernel)

private def p289999 := certifiedPrime 289999 6 [(p2,1),(p3,2),(p16111,1)] (by decide +kernel)

private def p291721 := certifiedPrime 291721 14 [(p2,3),(p3,1),(p5,1),(p11,1),(p13,1),(p17,1)] (by decide +kernel)

private def p293899 := certifiedPrime 293899 3 [(p2,1),(p3,1),(p11,1),(p61,1),(p73,1)] (by decide +kernel)

private def p296201 := certifiedPrime 296201 3 [(p2,3),(p5,2),(p1481,1)] (by decide +kernel)

private def p297989 := certifiedPrime 297989 2 [(p2,2),(p23,1),(p41,1),(p79,1)] (by decide +kernel)

private def p299699 := certifiedPrime 299699 2 [(p2,1),(p7,1),(p21407,1)] (by decide +kernel)

private def p304979 := certifiedPrime 304979 6 [(p2,1),(p31,1),(p4919,1)] (by decide +kernel)

private def p312101 := certifiedPrime 312101 2 [(p2,2),(p5,2),(p3121,1)] (by decide +kernel)

private def p313897 := certifiedPrime 313897 10 [(p2,3),(p3,1),(p11,1),(p29,1),(p41,1)] (by decide +kernel)

private def p315569 := certifiedPrime 315569 3 [(p2,4),(p11,2),(p163,1)] (by decide +kernel)

private def p319093 := certifiedPrime 319093 2 [(p2,2),(p3,1),(p26591,1)] (by decide +kernel)

private def p320911 := certifiedPrime 320911 3 [(p2,1),(p3,1),(p5,1),(p19,1),(p563,1)] (by decide +kernel)

private def p325333 := certifiedPrime 325333 5 [(p2,2),(p3,2),(p7,1),(p1291,1)] (by decide +kernel)

private def p333233 := certifiedPrime 333233 3 [(p2,4),(p59,1),(p353,1)] (by decide +kernel)

private def p340061 := certifiedPrime 340061 2 [(p2,2),(p5,1),(p7,2),(p347,1)] (by decide +kernel)

private def p342697 := certifiedPrime 342697 5 [(p2,3),(p3,1),(p109,1),(p131,1)] (by decide +kernel)

private def p343997 := certifiedPrime 343997 2 [(p2,2),(p85999,1)] (by decide +kernel)

private def p344941 := certifiedPrime 344941 2 [(p2,2),(p3,1),(p5,1),(p5749,1)] (by decide +kernel)

private def p345679 := certifiedPrime 345679 3 [(p2,1),(p3,1),(p17,1),(p3389,1)] (by decide +kernel)

private def p348989 := certifiedPrime 348989 3 [(p2,2),(p43,1),(p2029,1)] (by decide +kernel)

private def p363173 := certifiedPrime 363173 2 [(p2,2),(p90793,1)] (by decide +kernel)

private def p364129 := certifiedPrime 364129 11 [(p2,5),(p3,1),(p3793,1)] (by decide +kernel)

private def p365747 := certifiedPrime 365747 2 [(p2,1),(p23,1),(p7951,1)] (by decide +kernel)

private def p367889 := certifiedPrime 367889 3 [(p2,4),(p22993,1)] (by decide +kernel)

private def p368881 := certifiedPrime 368881 19 [(p2,4),(p3,1),(p5,1),(p29,1),(p53,1)] (by decide +kernel)

private def p368899 := certifiedPrime 368899 2 [(p2,1),(p3,1),(p61483,1)] (by decide +kernel)

private def p374677 := certifiedPrime 374677 2 [(p2,2),(p3,1),(p31223,1)] (by decide +kernel)

private def p377999 := certifiedPrime 377999 13 [(p2,1),(p188999,1)] (by decide +kernel)

private def p379499 := certifiedPrime 379499 6 [(p2,1),(p7,1),(p27107,1)] (by decide +kernel)

private def p379679 := certifiedPrime 379679 11 [(p2,1),(p13,1),(p17,1),(p859,1)] (by decide +kernel)

private def p379889 := certifiedPrime 379889 3 [(p2,4),(p23743,1)] (by decide +kernel)

private def p379999 := certifiedPrime 379999 3 [(p2,1),(p3,3),(p31,1),(p227,1)] (by decide +kernel)

private def p388789 := certifiedPrime 388789 2 [(p2,2),(p3,1),(p179,1),(p181,1)] (by decide +kernel)

private def p389699 := certifiedPrime 389699 2 [(p2,1),(p271,1),(p719,1)] (by decide +kernel)

private def p389989 := certifiedPrime 389989 2 [(p2,2),(p3,3),(p23,1),(p157,1)] (by decide +kernel)

private def p389999 := certifiedPrime 389999 7 [(p2,1),(p7,1),(p89,1),(p313,1)] (by decide +kernel)

private def p393157 := certifiedPrime 393157 2 [(p2,2),(p3,2),(p67,1),(p163,1)] (by decide +kernel)

private def p397427 := certifiedPrime 397427 2 [(p2,1),(p17,1),(p11689,1)] (by decide +kernel)

private def p399989 := certifiedPrime 399989 2 [(p2,2),(p19,2),(p277,1)] (by decide +kernel)

private def p402541 := certifiedPrime 402541 2 [(p2,2),(p3,1),(p5,1),(p6709,1)] (by decide +kernel)

private def p403549 := certifiedPrime 403549 6 [(p2,2),(p3,1),(p33629,1)] (by decide +kernel)

private def p412037 := certifiedPrime 412037 2 [(p2,2),(p239,1),(p431,1)] (by decide +kernel)

private def p420193 := certifiedPrime 420193 5 [(p2,5),(p3,2),(p1459,1)] (by decide +kernel)

private def p426331 := certifiedPrime 426331 2 [(p2,1),(p3,3),(p5,1),(p1579,1)] (by decide +kernel)

private def p426731 := certifiedPrime 426731 2 [(p2,1),(p5,1),(p139,1),(p307,1)] (by decide +kernel)

private def p434827 := certifiedPrime 434827 2 [(p2,1),(p3,2),(p7,2),(p17,1),(p29,1)] (by decide +kernel)

private def p443123 := certifiedPrime 443123 2 [(p2,1),(p17,1),(p13033,1)] (by decide +kernel)

private def p444443 := certifiedPrime 444443 2 [(p2,1),(p359,1),(p619,1)] (by decide +kernel)

private def p445453 := certifiedPrime 445453 2 [(p2,2),(p3,1),(p7,1),(p5303,1)] (by decide +kernel)

private def p446759 := certifiedPrime 446759 22 [(p2,1),(p13,1),(p17183,1)] (by decide +kernel)

private def p450349 := certifiedPrime 450349 6 [(p2,2),(p3,1),(p37529,1)] (by decide +kernel)

private def p450859 := certifiedPrime 450859 3 [(p2,1),(p3,1),(p163,1),(p461,1)] (by decide +kernel)

private def p464771 := certifiedPrime 464771 2 [(p2,1),(p5,1),(p46477,1)] (by decide +kernel)

private def p467557 := certifiedPrime 467557 2 [(p2,2),(p3,1),(p47,1),(p829,1)] (by decide +kernel)

private def p468899 := certifiedPrime 468899 2 [(p2,1),(p97,1),(p2417,1)] (by decide +kernel)

private def p469979 := certifiedPrime 469979 2 [(p2,1),(p234989,1)] (by decide +kernel)

private def p476519 := certifiedPrime 476519 7 [(p2,1),(p7,1),(p101,1),(p337,1)] (by decide +kernel)

private def p487889 := certifiedPrime 487889 3 [(p2,4),(p30493,1)] (by decide +kernel)

private def p489989 := certifiedPrime 489989 2 [(p2,2),(p122497,1)] (by decide +kernel)

private def p496063 := certifiedPrime 496063 3 [(p2,1),(p3,2),(p7,1),(p31,1),(p127,1)] (by decide +kernel)

private def p496999 := certifiedPrime 496999 3 [(p2,1),(p3,2),(p27611,1)] (by decide +kernel)

private def p497999 := certifiedPrime 497999 13 [(p2,1),(p17,1),(p97,1),(p151,1)] (by decide +kernel)

private def p498611 := certifiedPrime 498611 2 [(p2,1),(p5,1),(p7,1),(p17,1),(p419,1)] (by decide +kernel)

private def p500501 := certifiedPrime 500501 14 [(p2,2),(p5,3),(p7,1),(p11,1),(p13,1)] (by decide +kernel)

private def p504389 := certifiedPrime 504389 2 [(p2,2),(p126097,1)] (by decide +kernel)

private def p505613 := certifiedPrime 505613 2 [(p2,2),(p41,1),(p3083,1)] (by decide +kernel)

private def p514853 := certifiedPrime 514853 2 [(p2,2),(p13,1),(p9901,1)] (by decide +kernel)

private def p520151 := certifiedPrime 520151 7 [(p2,1),(p5,2),(p101,1),(p103,1)] (by decide +kernel)

private def p524957 := certifiedPrime 524957 2 [(p2,2),(p37,1),(p3547,1)] (by decide +kernel)

private def p529999 := certifiedPrime 529999 34 [(p2,1),(p3,1),(p7,1),(p12619,1)] (by decide +kernel)

private def p541181 := certifiedPrime 541181 2 [(p2,2),(p5,1),(p27059,1)] (by decide +kernel)

private def p543827 := certifiedPrime 543827 2 [(p2,1),(p37,1),(p7349,1)] (by decide +kernel)

private def p552611 := certifiedPrime 552611 10 [(p2,1),(p5,1),(p73,1),(p757,1)] (by decide +kernel)

private def p553433 := certifiedPrime 553433 3 [(p2,3),(p11,1),(p19,1),(p331,1)] (by decide +kernel)

private def p553921 := certifiedPrime 553921 31 [(p2,6),(p3,1),(p5,1),(p577,1)] (by decide +kernel)

private def p556243 := certifiedPrime 556243 2 [(p2,1),(p3,1),(p92707,1)] (by decide +kernel)

private def p561797 := certifiedPrime 561797 2 [(p2,2),(p140449,1)] (by decide +kernel)

private def p562493 := certifiedPrime 562493 2 [(p2,2),(p7,1),(p20089,1)] (by decide +kernel)

private def p570967 := certifiedPrime 570967 5 [(p2,1),(p3,1),(p11,1),(p41,1),(p211,1)] (by decide +kernel)

private def p572333 := certifiedPrime 572333 2 [(p2,2),(p23,1),(p6221,1)] (by decide +kernel)

private def p576493 := certifiedPrime 576493 5 [(p2,2),(p3,1),(p7,1),(p6863,1)] (by decide +kernel)

private def p577537 := certifiedPrime 577537 5 [(p2,12),(p3,1),(p47,1)] (by decide +kernel)

private def p581573 := certifiedPrime 581573 2 [(p2,2),(p347,1),(p419,1)] (by decide +kernel)

private def p583657 := certifiedPrime 583657 10 [(p2,3),(p3,1),(p83,1),(p293,1)] (by decide +kernel)

private def p588911 := certifiedPrime 588911 7 [(p2,1),(p5,1),(p7,1),(p47,1),(p179,1)] (by decide +kernel)

private def p589807 := certifiedPrime 589807 5 [(p2,1),(p3,2),(p7,1),(p31,1),(p151,1)] (by decide +kernel)

private def p590269 := certifiedPrime 590269 2 [(p2,2),(p3,1),(p7,1),(p7027,1)] (by decide +kernel)

private def p596899 := certifiedPrime 596899 10 [(p2,1),(p3,2),(p33161,1)] (by decide +kernel)

private def p598999 := certifiedPrime 598999 3 [(p2,1),(p3,1),(p99833,1)] (by decide +kernel)

private def p599999 := certifiedPrime 599999 7 [(p2,1),(p7,1),(p17,1),(p2521,1)] (by decide +kernel)

private def p600221 := certifiedPrime 600221 2 [(p2,2),(p5,1),(p30011,1)] (by decide +kernel)

private def p611111 := certifiedPrime 611111 7 [(p2,1),(p5,1),(p23,1),(p2657,1)] (by decide +kernel)

private def p611641 := certifiedPrime 611641 11 [(p2,3),(p3,2),(p5,1),(p1699,1)] (by decide +kernel)

private def p617689 := certifiedPrime 617689 11 [(p2,3),(p3,2),(p23,1),(p373,1)] (by decide +kernel)

private def p619181 := certifiedPrime 619181 2 [(p2,2),(p5,1),(p83,1),(p373,1)] (by decide +kernel)

private def p619999 := certifiedPrime 619999 3 [(p2,1),(p3,1),(p103333,1)] (by decide +kernel)

private def p637711 := certifiedPrime 637711 12 [(p2,1),(p3,1),(p5,1),(p29,1),(p733,1)] (by decide +kernel)

private def p657523 := certifiedPrime 657523 2 [(p2,1),(p3,2),(p36529,1)] (by decide +kernel)

private def p658997 := certifiedPrime 658997 2 [(p2,2),(p13,1),(p19,1),(p23,1),(p29,1)] (by decide +kernel)

private def p659941 := certifiedPrime 659941 11 [(p2,2),(p3,1),(p5,1),(p17,1),(p647,1)] (by decide +kernel)

private def p667649 := certifiedPrime 667649 3 [(p2,12),(p163,1)] (by decide +kernel)

private def p676391 := certifiedPrime 676391 7 [(p2,1),(p5,1),(p11,2),(p13,1),(p43,1)] (by decide +kernel)

private def p679999 := certifiedPrime 679999 3 [(p2,1),(p3,1),(p11,1),(p10303,1)] (by decide +kernel)

private def p688679 := certifiedPrime 688679 19 [(p2,1),(p149,1),(p2311,1)] (by decide +kernel)

private def p695809 := certifiedPrime 695809 38 [(p2,9),(p3,2),(p151,1)] (by decide +kernel)

private def p697019 := certifiedPrime 697019 2 [(p2,1),(p7,1),(p49787,1)] (by decide +kernel)

private def p697979 := certifiedPrime 697979 2 [(p2,1),(p348989,1)] (by decide +kernel)

private def p705833 := certifiedPrime 705833 3 [(p2,3),(p83,1),(p1063,1)] (by decide +kernel)

private def p715339 := certifiedPrime 715339 7 [(p2,1),(p3,3),(p13,1),(p1019,1)] (by decide +kernel)

private def p727351 := certifiedPrime 727351 3 [(p2,1),(p3,1),(p5,2),(p13,1),(p373,1)] (by decide +kernel)

private def p732617 := certifiedPrime 732617 3 [(p2,3),(p91577,1)] (by decide +kernel)

private def p737533 := certifiedPrime 737533 2 [(p2,2),(p3,3),(p6829,1)] (by decide +kernel)

private def p738083 := certifiedPrime 738083 2 [(p2,1),(p41,1),(p9001,1)] (by decide +kernel)

private def p747869 := certifiedPrime 747869 2 [(p2,2),(p11,1),(p23,1),(p739,1)] (by decide +kernel)

private def p750077 := certifiedPrime 750077 2 [(p2,2),(p23,1),(p31,1),(p263,1)] (by decide +kernel)

private def p754597 := certifiedPrime 754597 6 [(p2,2),(p3,4),(p17,1),(p137,1)] (by decide +kernel)

private def p765329 := certifiedPrime 765329 3 [(p2,4),(p31,1),(p1543,1)] (by decide +kernel)

private def p766817 := certifiedPrime 766817 3 [(p2,5),(p31,1),(p773,1)] (by decide +kernel)

private def p781301 := certifiedPrime 781301 2 [(p2,2),(p5,2),(p13,1),(p601,1)] (by decide +kernel)

private def p788779 := certifiedPrime 788779 2 [(p2,1),(p3,6),(p541,1)] (by decide +kernel)

private def p795997 := certifiedPrime 795997 2 [(p2,2),(p3,2),(p22111,1)] (by decide +kernel)

private def p799979 := certifiedPrime 799979 2 [(p2,1),(p399989,1)] (by decide +kernel)

private def p799999 := certifiedPrime 799999 3 [(p2,1),(p3,1),(p151,1),(p883,1)] (by decide +kernel)

private def p806129 := certifiedPrime 806129 3 [(p2,4),(p50383,1)] (by decide +kernel)

private def p824749 := certifiedPrime 824749 6 [(p2,2),(p3,1),(p68729,1)] (by decide +kernel)

private def p838889 := certifiedPrime 838889 3 [(p2,3),(p19,1),(p5519,1)] (by decide +kernel)

private def p858269 := certifiedPrime 858269 2 [(p2,2),(p19,1),(p23,1),(p491,1)] (by decide +kernel)

private def p858989 := certifiedPrime 858989 2 [(p2,2),(p13,1),(p16519,1)] (by decide +kernel)

private def p861979 := certifiedPrime 861979 3 [(p2,1),(p3,1),(p13,1),(p43,1),(p257,1)] (by decide +kernel)

private def p865591 := certifiedPrime 865591 3 [(p2,1),(p3,1),(p5,1),(p11,1),(p43,1),(p61,1)] (by decide +kernel)

private def p870679 := certifiedPrime 870679 3 [(p2,1),(p3,2),(p48371,1)] (by decide +kernel)

private def p879979 := certifiedPrime 879979 2 [(p2,1),(p3,1),(p11,1),(p67,1),(p199,1)] (by decide +kernel)

private def p888887 := certifiedPrime 888887 5 [(p2,1),(p444443,1)] (by decide +kernel)

private def p888997 := certifiedPrime 888997 5 [(p2,2),(p3,1),(p23,1),(p3221,1)] (by decide +kernel)

private def p889997 := certifiedPrime 889997 2 [(p2,2),(p222499,1)] (by decide +kernel)

private def p898669 := certifiedPrime 898669 2 [(p2,2),(p3,3),(p53,1),(p157,1)] (by decide +kernel)

private def p898889 := certifiedPrime 898889 3 [(p2,3),(p112361,1)] (by decide +kernel)

private def p899687 := certifiedPrime 899687 5 [(p2,1),(p109,1),(p4127,1)] (by decide +kernel)

private def p908053 := certifiedPrime 908053 5 [(p2,2),(p3,1),(p31,1),(p2441,1)] (by decide +kernel)

private def p910103 := certifiedPrime 910103 5 [(p2,1),(p113,1),(p4027,1)] (by decide +kernel)

private def p918889 := certifiedPrime 918889 14 [(p2,3),(p3,1),(p38287,1)] (by decide +kernel)

private def p919183 := certifiedPrime 919183 10 [(p2,1),(p3,1),(p11,1),(p19,1),(p733,1)] (by decide +kernel)

private def p935777 := certifiedPrime 935777 3 [(p2,5),(p29243,1)] (by decide +kernel)

private def p956999 := certifiedPrime 956999 7 [(p2,1),(p7,1),(p17,1),(p4021,1)] (by decide +kernel)

private def p969889 := certifiedPrime 969889 13 [(p2,5),(p3,1),(p10103,1)] (by decide +kernel)

private def p970961 := certifiedPrime 970961 3 [(p2,4),(p5,1),(p53,1),(p229,1)] (by decide +kernel)

private def p971111 := certifiedPrime 971111 11 [(p2,1),(p5,1),(p7,1),(p13873,1)] (by decide +kernel)

private def p988489 := certifiedPrime 988489 7 [(p2,3),(p3,2),(p13729,1)] (by decide +kernel)

private def p988501 := certifiedPrime 988501 6 [(p2,2),(p3,1),(p5,3),(p659,1)] (by decide +kernel)

private def p989999 := certifiedPrime 989999 19 [(p2,1),(p277,1),(p1787,1)] (by decide +kernel)

private def p995081 := certifiedPrime 995081 3 [(p2,3),(p5,1),(p24877,1)] (by decide +kernel)

private def p997807 := certifiedPrime 997807 3 [(p2,1),(p3,1),(p166301,1)] (by decide +kernel)

private def p998759 := certifiedPrime 998759 11 [(p2,1),(p31,1),(p89,1),(p181,1)] (by decide +kernel)

private def p998969 := certifiedPrime 998969 3 [(p2,3),(p193,1),(p647,1)] (by decide +kernel)

private def p998989 := certifiedPrime 998989 2 [(p2,2),(p3,1),(p17,1),(p59,1),(p83,1)] (by decide +kernel)

private def p999499 := certifiedPrime 999499 2 [(p2,1),(p3,1),(p17,1),(p41,1),(p239,1)] (by decide +kernel)

private def p1004453 := certifiedPrime 1004453 2 [(p2,2),(p151,1),(p1663,1)] (by decide +kernel)

private def p1008779 := certifiedPrime 1008779 2 [(p2,1),(p504389,1)] (by decide +kernel)

private def p1039823 := certifiedPrime 1039823 7 [(p2,1),(p7,1),(p17,2),(p257,1)] (by decide +kernel)

private def p1046237 := certifiedPrime 1046237 2 [(p2,2),(p73,1),(p3583,1)] (by decide +kernel)

private def p1046399 := certifiedPrime 1046399 7 [(p2,1),(p71,1),(p7369,1)] (by decide +kernel)

private def p1060303 := certifiedPrime 1060303 3 [(p2,1),(p3,1),(p61,1),(p2897,1)] (by decide +kernel)

private def p1068437 := certifiedPrime 1068437 2 [(p2,2),(p131,1),(p2039,1)] (by decide +kernel)

private def p1081687 := certifiedPrime 1081687 3 [(p2,1),(p3,1),(p180281,1)] (by decide +kernel)

private def p1090909 := certifiedPrime 1090909 2 [(p2,2),(p3,4),(p7,1),(p13,1),(p37,1)] (by decide +kernel)

private def p1096807 := certifiedPrime 1096807 3 [(p2,1),(p3,1),(p17,1),(p10753,1)] (by decide +kernel)

private def p1100093 := certifiedPrime 1100093 3 [(p2,2),(p7,1),(p101,1),(p389,1)] (by decide +kernel)

private def p1112381 := certifiedPrime 1112381 2 [(p2,2),(p5,1),(p55619,1)] (by decide +kernel)

private def p1113461 := certifiedPrime 1113461 7 [(p2,2),(p5,1),(p55673,1)] (by decide +kernel)

private def p1121249 := certifiedPrime 1121249 3 [(p2,5),(p37,1),(p947,1)] (by decide +kernel)

private def p1124987 := certifiedPrime 1124987 2 [(p2,1),(p562493,1)] (by decide +kernel)

private def p1163147 := certifiedPrime 1163147 2 [(p2,1),(p581573,1)] (by decide +kernel)

private def p1184171 := certifiedPrime 1184171 2 [(p2,1),(p5,1),(p13,1),(p9109,1)] (by decide +kernel)

private def p1200443 := certifiedPrime 1200443 2 [(p2,1),(p600221,1)] (by decide +kernel)

private def p1212851 := certifiedPrime 1212851 2 [(p2,1),(p5,2),(p127,1),(p191,1)] (by decide +kernel)

private def p1222499 := certifiedPrime 1222499 2 [(p2,1),(p19,1),(p53,1),(p607,1)] (by decide +kernel)

private def p1228393 := certifiedPrime 1228393 5 [(p2,3),(p3,3),(p11,2),(p47,1)] (by decide +kernel)

private def p1248101 := certifiedPrime 1248101 2 [(p2,2),(p5,2),(p7,1),(p1783,1)] (by decide +kernel)

private def p1253401 := certifiedPrime 1253401 11 [(p2,3),(p3,1),(p5,2),(p2089,1)] (by decide +kernel)

private def p1254251 := certifiedPrime 1254251 2 [(p2,1),(p5,3),(p29,1),(p173,1)] (by decide +kernel)

private def p1256023 := certifiedPrime 1256023 3 [(p2,1),(p3,2),(p69779,1)] (by decide +kernel)

private def p1300921 := certifiedPrime 1300921 31 [(p2,3),(p3,1),(p5,1),(p37,1),(p293,1)] (by decide +kernel)

private def p1319443 := certifiedPrime 1319443 2 [(p2,1),(p3,1),(p29,1),(p7583,1)] (by decide +kernel)

private def p1320377 := certifiedPrime 1320377 3 [(p2,3),(p165047,1)] (by decide +kernel)

private def p1390891 := certifiedPrime 1390891 2 [(p2,1),(p3,1),(p5,1),(p71,1),(p653,1)] (by decide +kernel)

private def p1431257 := certifiedPrime 1431257 3 [(p2,3),(p178907,1)] (by decide +kernel)

private def p1497283 := certifiedPrime 1497283 2 [(p2,1),(p3,1),(p257,1),(p971,1)] (by decide +kernel)

private def p1527017 := certifiedPrime 1527017 3 [(p2,3),(p23,1),(p43,1),(p193,1)] (by decide +kernel)

private def p1538461 := certifiedPrime 1538461 6 [(p2,2),(p3,3),(p5,1),(p7,1),(p11,1),(p37,1)] (by decide +kernel)

private def p1542377 := certifiedPrime 1542377 3 [(p2,3),(p11,1),(p17,1),(p1031,1)] (by decide +kernel)

private def p1649981 := certifiedPrime 1649981 3 [(p2,2),(p5,1),(p82499,1)] (by decide +kernel)

private def p1663147 := certifiedPrime 1663147 3 [(p2,1),(p3,3),(p19,1),(p1621,1)] (by decide +kernel)

private def p1708981 := certifiedPrime 1708981 2 [(p2,2),(p3,1),(p5,1),(p7,1),(p13,1),(p313,1)] (by decide +kernel)

private def p1726139 := certifiedPrime 1726139 2 [(p2,1),(p29,1),(p29761,1)] (by decide +kernel)

private def p1775317 := certifiedPrime 1775317 5 [(p2,2),(p3,1),(p337,1),(p439,1)] (by decide +kernel)

private def p1819999 := certifiedPrime 1819999 3 [(p2,1),(p3,2),(p101111,1)] (by decide +kernel)

private def p1833383 := certifiedPrime 1833383 5 [(p2,1),(p17,1),(p53923,1)] (by decide +kernel)

private def p1860373 := certifiedPrime 1860373 2 [(p2,2),(p3,2),(p31,1),(p1667,1)] (by decide +kernel)

private def p1870229 := certifiedPrime 1870229 2 [(p2,2),(p467557,1)] (by decide +kernel)

private def p1875479 := certifiedPrime 1875479 7 [(p2,1),(p11,1),(p163,1),(p523,1)] (by decide +kernel)

private def p1899949 := certifiedPrime 1899949 10 [(p2,2),(p3,1),(p158329,1)] (by decide +kernel)

private def p1938751 := certifiedPrime 1938751 3 [(p2,1),(p3,1),(p5,4),(p11,1),(p47,1)] (by decide +kernel)

private def p1979993 := certifiedPrime 1979993 3 [(p2,3),(p7,2),(p5051,1)] (by decide +kernel)

private def p1986359 := certifiedPrime 1986359 7 [(p2,1),(p11,1),(p90289,1)] (by decide +kernel)

private def p1999733 := certifiedPrime 1999733 2 [(p2,2),(p7,1),(p71419,1)] (by decide +kernel)

private def p2053841 := certifiedPrime 2053841 3 [(p2,4),(p5,1),(p25673,1)] (by decide +kernel)

private def p2064229 := certifiedPrime 2064229 2 [(p2,2),(p3,1),(p31,2),(p179,1)] (by decide +kernel)

private def p2089169 := certifiedPrime 2089169 3 [(p2,4),(p37,1),(p3529,1)] (by decide +kernel)

private def p2142857 := certifiedPrime 2142857 3 [(p2,3),(p267857,1)] (by decide +kernel)

private def p2152063 := certifiedPrime 2152063 19 [(p2,1),(p3,3),(p11,1),(p3623,1)] (by decide +kernel)

private def p2158033 := certifiedPrime 2158033 5 [(p2,4),(p3,1),(p44959,1)] (by decide +kernel)

private def p2164853 := certifiedPrime 2164853 2 [(p2,2),(p23,1),(p23531,1)] (by decide +kernel)

private def p2181659 := certifiedPrime 2181659 2 [(p2,1),(p149,1),(p7321,1)] (by decide +kernel)

private def p2217569 := certifiedPrime 2217569 3 [(p2,5),(p23,2),(p131,1)] (by decide +kernel)

private def p2224763 := certifiedPrime 2224763 2 [(p2,1),(p1112381,1)] (by decide +kernel)

private def p2224987 := certifiedPrime 2224987 3 [(p2,1),(p3,1),(p97,1),(p3823,1)] (by decide +kernel)

private def p2226923 := certifiedPrime 2226923 2 [(p2,1),(p1113461,1)] (by decide +kernel)

private def p2270549 := certifiedPrime 2270549 2 [(p2,2),(p7,1),(p83,1),(p977,1)] (by decide +kernel)

private def p2277797 := certifiedPrime 2277797 2 [(p2,2),(p17,1),(p19,1),(p41,1),(p43,1)] (by decide +kernel)

private def p2278553 := certifiedPrime 2278553 3 [(p2,3),(p284819,1)] (by decide +kernel)

private def p2326019 := certifiedPrime 2326019 2 [(p2,1),(p19,1),(p61211,1)] (by decide +kernel)

private def p2330221 := certifiedPrime 2330221 6 [(p2,2),(p3,1),(p5,1),(p71,1),(p547,1)] (by decide +kernel)

private def p2398273 := certifiedPrime 2398273 5 [(p2,6),(p3,1),(p12491,1)] (by decide +kernel)

private def p2417243 := certifiedPrime 2417243 2 [(p2,1),(p79,1),(p15299,1)] (by decide +kernel)

private def p2420921 := certifiedPrime 2420921 3 [(p2,3),(p5,1),(p29,1),(p2087,1)] (by decide +kernel)

private def p2518421 := certifiedPrime 2518421 2 [(p2,2),(p5,1),(p125921,1)] (by decide +kernel)

private def p2564101 := certifiedPrime 2564101 10 [(p2,2),(p3,2),(p5,2),(p7,1),(p11,1),(p37,1)] (by decide +kernel)

private def p2599999 := certifiedPrime 2599999 6 [(p2,1),(p3,1),(p19,1),(p22807,1)] (by decide +kernel)

private def p2601091 := certifiedPrime 2601091 10 [(p2,1),(p3,2),(p5,1),(p28901,1)] (by decide +kernel)

private def p2613607 := certifiedPrime 2613607 10 [(p2,1),(p3,1),(p37,1),(p61,1),(p193,1)] (by decide +kernel)

private def p2630093 := certifiedPrime 2630093 2 [(p2,2),(p657523,1)] (by decide +kernel)

private def p2630917 := certifiedPrime 2630917 5 [(p2,2),(p3,2),(p107,1),(p683,1)] (by decide +kernel)

private def p2652439 := certifiedPrime 2652439 3 [(p2,1),(p3,1),(p19,1),(p53,1),(p439,1)] (by decide +kernel)

private def p2699999 := certifiedPrime 2699999 7 [(p2,1),(p7,2),(p27551,1)] (by decide +kernel)

private def p2797999 := certifiedPrime 2797999 7 [(p2,1),(p3,1),(p7,2),(p31,1),(p307,1)] (by decide +kernel)

private def p2824447 := certifiedPrime 2824447 5 [(p2,1),(p3,1),(p23,1),(p97,1),(p211,1)] (by decide +kernel)

private def p2868823 := certifiedPrime 2868823 3 [(p2,1),(p3,2),(p11,1),(p14489,1)] (by decide +kernel)

private def p2899991 := certifiedPrime 2899991 17 [(p2,1),(p5,1),(p289999,1)] (by decide +kernel)

private def p2899993 := certifiedPrime 2899993 5 [(p2,3),(p3,1),(p120833,1)] (by decide +kernel)

private def p2899997 := certifiedPrime 2899997 3 [(p2,2),(p11,1),(p17,1),(p3877,1)] (by decide +kernel)

private def p2956201 := certifiedPrime 2956201 7 [(p2,3),(p3,1),(p5,2),(p13,1),(p379,1)] (by decide +kernel)

private def p2960977 := certifiedPrime 2960977 5 [(p2,4),(p3,1),(p61687,1)] (by decide +kernel)

private def p3081349 := certifiedPrime 3081349 2 [(p2,2),(p3,3),(p103,1),(p277,1)] (by decide +kernel)

private def p3092783 := certifiedPrime 3092783 7 [(p2,1),(p7,2),(p11,1),(p19,1),(p151,1)] (by decide +kernel)

private def p3148333 := certifiedPrime 3148333 6 [(p2,2),(p3,1),(p11,1),(p17,1),(p23,1),(p61,1)] (by decide +kernel)

private def p3183391 := certifiedPrime 3183391 3 [(p2,1),(p3,2),(p5,1),(p7,1),(p31,1),(p163,1)] (by decide +kernel)

private def p3197881 := certifiedPrime 3197881 26 [(p2,3),(p3,5),(p5,1),(p7,1),(p47,1)] (by decide +kernel)

private def p3229573 := certifiedPrime 3229573 2 [(p2,2),(p3,1),(p269131,1)] (by decide +kernel)

private def p3233333 := certifiedPrime 3233333 2 [(p2,2),(p17,2),(p2797,1)] (by decide +kernel)

private def p3307523 := certifiedPrime 3307523 2 [(p2,1),(p67,1),(p24683,1)] (by decide +kernel)

private def p3341269 := certifiedPrime 3341269 2 [(p2,2),(p3,2),(p7,1),(p13259,1)] (by decide +kernel)

private def p3388433 := certifiedPrime 3388433 3 [(p2,4),(p211777,1)] (by decide +kernel)

private def p3407281 := certifiedPrime 3407281 17 [(p2,4),(p3,1),(p5,1),(p14197,1)] (by decide +kernel)

private def p3452279 := certifiedPrime 3452279 19 [(p2,1),(p1726139,1)] (by decide +kernel)

private def p3497999 := certifiedPrime 3497999 7 [(p2,1),(p7,1),(p249857,1)] (by decide +kernel)

private def p3499999 := certifiedPrime 3499999 3 [(p2,1),(p3,1),(p59,1),(p9887,1)] (by decide +kernel)

private def p3503221 := certifiedPrime 3503221 2 [(p2,2),(p3,1),(p5,1),(p7,1),(p19,1),(p439,1)] (by decide +kernel)

private def p3547619 := certifiedPrime 3547619 2 [(p2,1),(p127,1),(p13967,1)] (by decide +kernel)

private def p3622499 := certifiedPrime 3622499 2 [(p2,1),(p11,2),(p14969,1)] (by decide +kernel)

private def p3624529 := certifiedPrime 3624529 7 [(p2,4),(p3,1),(p75511,1)] (by decide +kernel)

private def p3796997 := certifiedPrime 3796997 2 [(p2,2),(p7,1),(p135607,1)] (by decide +kernel)

private def p3845441 := certifiedPrime 3845441 3 [(p2,6),(p5,1),(p61,1),(p197,1)] (by decide +kernel)

private def p3904741 := certifiedPrime 3904741 6 [(p2,2),(p3,3),(p5,1),(p7,1),(p1033,1)] (by decide +kernel)

private def p3913771 := certifiedPrime 3913771 2 [(p2,1),(p3,1),(p5,1),(p7,1),(p18637,1)] (by decide +kernel)

private def p3983033 := certifiedPrime 3983033 5 [(p2,3),(p17,1),(p29287,1)] (by decide +kernel)

private def p3988889 := certifiedPrime 3988889 3 [(p2,3),(p498611,1)] (by decide +kernel)

private def p3997993 := certifiedPrime 3997993 5 [(p2,3),(p3,1),(p17,1),(p41,1),(p239,1)] (by decide +kernel)

private def p4107683 := certifiedPrime 4107683 2 [(p2,1),(p2053841,1)] (by decide +kernel)

private def p4164583 := certifiedPrime 4164583 5 [(p2,1),(p3,1),(p157,1),(p4421,1)] (by decide +kernel)

private def p4180909 := certifiedPrime 4180909 2 [(p2,2),(p3,1),(p31,1),(p11239,1)] (by decide +kernel)

private def p4242253 := certifiedPrime 4242253 2 [(p2,2),(p3,1),(p7,1),(p50503,1)] (by decide +kernel)

private def p4276043 := certifiedPrime 4276043 2 [(p2,1),(p293,1),(p7297,1)] (by decide +kernel)

private def p4278751 := certifiedPrime 4278751 3 [(p2,1),(p3,1),(p5,4),(p7,1),(p163,1)] (by decide +kernel)

private def p4417967 := certifiedPrime 4417967 5 [(p2,1),(p7,1),(p315569,1)] (by decide +kernel)

private def p4449527 := certifiedPrime 4449527 5 [(p2,1),(p2224763,1)] (by decide +kernel)

private def p4487621 := certifiedPrime 4487621 2 [(p2,2),(p5,1),(p173,1),(p1297,1)] (by decide +kernel)

private def p4498001 := certifiedPrime 4498001 6 [(p2,4),(p5,3),(p13,1),(p173,1)] (by decide +kernel)

private def p4540909 := certifiedPrime 4540909 6 [(p2,2),(p3,1),(p227,1),(p1667,1)] (by decide +kernel)

private def p4541099 := certifiedPrime 4541099 2 [(p2,1),(p2270549,1)] (by decide +kernel)

private def p4589797 := certifiedPrime 4589797 2 [(p2,2),(p3,1),(p17,1),(p149,1),(p151,1)] (by decide +kernel)

private def p4694999 := certifiedPrime 4694999 7 [(p2,1),(p7,1),(p11,1),(p43,1),(p709,1)] (by decide +kernel)

private def p4728013 := certifiedPrime 4728013 5 [(p2,2),(p3,1),(p47,1),(p83,1),(p101,1)] (by decide +kernel)

private def p4775339 := certifiedPrime 4775339 2 [(p2,1),(p1171,1),(p2039,1)] (by decide +kernel)

private def p4799999 := certifiedPrime 4799999 7 [(p2,1),(p7,1),(p53,1),(p6469,1)] (by decide +kernel)

private def p4838543 := certifiedPrime 4838543 5 [(p2,1),(p31,1),(p78041,1)] (by decide +kernel)

private def p4878889 := certifiedPrime 4878889 19 [(p2,3),(p3,1),(p7,1),(p113,1),(p257,1)] (by decide +kernel)

private def p4893869 := certifiedPrime 4893869 2 [(p2,2),(p7,1),(p19,1),(p9199,1)] (by decide +kernel)

private def p4938203 := certifiedPrime 4938203 2 [(p2,1),(p233,1),(p10597,1)] (by decide +kernel)

private def p4962953 := certifiedPrime 4962953 3 [(p2,3),(p19,1),(p103,1),(p317,1)] (by decide +kernel)

private def p4978403 := certifiedPrime 4978403 2 [(p2,1),(p11,1),(p13,3),(p103,1)] (by decide +kernel)

private def p4979993 := certifiedPrime 4979993 3 [(p2,3),(p109,1),(p5711,1)] (by decide +kernel)

private def p4989997 := certifiedPrime 4989997 2 [(p2,2),(p3,2),(p11,1),(p12601,1)] (by decide +kernel)

private def p4999999 := certifiedPrime 4999999 3 [(p2,1),(p3,1),(p191,1),(p4363,1)] (by decide +kernel)

private def p5174189 := certifiedPrime 5174189 2 [(p2,2),(p17,1),(p76091,1)] (by decide +kernel)

private def p5334863 := certifiedPrime 5334863 5 [(p2,1),(p13,1),(p205187,1)] (by decide +kernel)

private def p5609867 := certifiedPrime 5609867 2 [(p2,1),(p37,1),(p41,1),(p43,2)] (by decide +kernel)

private def p5806561 := certifiedPrime 5806561 13 [(p2,5),(p3,1),(p5,1),(p12097,1)] (by decide +kernel)

private def p5819999 := certifiedPrime 5819999 11 [(p2,1),(p73,1),(p39863,1)] (by decide +kernel)

private def p5888899 := certifiedPrime 5888899 3 [(p2,1),(p3,2),(p19,1),(p67,1),(p257,1)] (by decide +kernel)

private def p5970487 := certifiedPrime 5970487 5 [(p2,1),(p3,1),(p995081,1)] (by decide +kernel)

private def p5979959 := certifiedPrime 5979959 13 [(p2,1),(p109,1),(p27431,1)] (by decide +kernel)

private def p6086851 := certifiedPrime 6086851 3 [(p2,1),(p3,1),(p5,2),(p7,1),(p11,1),(p17,1),(p31,1)] (by decide +kernel)

private def p6185567 := certifiedPrime 6185567 5 [(p2,1),(p3092783,1)] (by decide +kernel)

private def p6195997 := certifiedPrime 6195997 2 [(p2,2),(p3,2),(p109,1),(p1579,1)] (by decide +kernel)

private def p6289999 := certifiedPrime 6289999 3 [(p2,1),(p3,1),(p11,1),(p13,1),(p7331,1)] (by decide +kernel)

private def p6371867 := certifiedPrime 6371867 2 [(p2,1),(p89,1),(p35797,1)] (by decide +kernel)

private def p6397849 := certifiedPrime 6397849 7 [(p2,3),(p3,2),(p17,1),(p5227,1)] (by decide +kernel)

private def p6615047 := certifiedPrime 6615047 5 [(p2,1),(p3307523,1)] (by decide +kernel)

private def p6794999 := certifiedPrime 6794999 7 [(p2,1),(p7,1),(p569,1),(p853,1)] (by decide +kernel)

private def p6819749 := certifiedPrime 6819749 2 [(p2,2),(p13,1),(p131149,1)] (by decide +kernel)

private def p6855089 := certifiedPrime 6855089 3 [(p2,4),(p563,1),(p761,1)] (by decide +kernel)

private def p6858721 := certifiedPrime 6858721 29 [(p2,5),(p3,2),(p5,1),(p11,1),(p433,1)] (by decide +kernel)

private def p6867997 := certifiedPrime 6867997 2 [(p2,2),(p3,1),(p572333,1)] (by decide +kernel)

private def p6899579 := certifiedPrime 6899579 2 [(p2,1),(p7,1),(p59,1),(p8353,1)] (by decide +kernel)

private def p6978883 := certifiedPrime 6978883 5 [(p2,1),(p3,1),(p1163147,1)] (by decide +kernel)

private def p6991997 := certifiedPrime 6991997 2 [(p2,2),(p11,1),(p158909,1)] (by decide +kernel)

private def p6995999 := certifiedPrime 6995999 17 [(p2,1),(p3497999,1)] (by decide +kernel)

private def p7056661 := certifiedPrime 7056661 6 [(p2,2),(p3,1),(p5,1),(p13,1),(p83,1),(p109,1)] (by decide +kernel)

private def p7244999 := certifiedPrime 7244999 11 [(p2,1),(p3622499,1)] (by decide +kernel)

private def p7259809 := certifiedPrime 7259809 11 [(p2,5),(p3,1),(p47,1),(p1609,1)] (by decide +kernel)

private def p7305241 := certifiedPrime 7305241 13 [(p2,3),(p3,1),(p5,1),(p17,1),(p3581,1)] (by decide +kernel)

private def p7414681 := certifiedPrime 7414681 23 [(p2,3),(p3,1),(p5,1),(p7,2),(p13,1),(p97,1)] (by decide +kernel)

private def p7599797 := certifiedPrime 7599797 2 [(p2,2),(p1899949,1)] (by decide +kernel)

private def p7621087 := certifiedPrime 7621087 5 [(p2,1),(p3,1),(p11,1),(p115471,1)] (by decide +kernel)

private def p7799999 := certifiedPrime 7799999 7 [(p2,1),(p281,1),(p13879,1)] (by decide +kernel)

private def p7887883 := certifiedPrime 7887883 2 [(p2,1),(p3,1),(p37,1),(p35531,1)] (by decide +kernel)

private def p7969999 := certifiedPrime 7969999 3 [(p2,1),(p3,1),(p233,1),(p5701,1)] (by decide +kernel)

private def p7977997 := certifiedPrime 7977997 2 [(p2,2),(p3,2),(p13,1),(p17047,1)] (by decide +kernel)

private def p7999993 := certifiedPrime 7999993 10 [(p2,3),(p3,3),(p7,1),(p11,1),(p13,1),(p37,1)] (by decide +kernel)

private def p8009009 := certifiedPrime 8009009 11 [(p2,4),(p7,1),(p43,1),(p1663,1)] (by decide +kernel)

private def p8140669 := certifiedPrime 8140669 6 [(p2,2),(p3,1),(p73,1),(p9293,1)] (by decide +kernel)

private def p8206943 := certifiedPrime 8206943 5 [(p2,1),(p29,1),(p141499,1)] (by decide +kernel)

private def p8369897 := certifiedPrime 8369897 3 [(p2,3),(p1046237,1)] (by decide +kernel)

private def p8371193 := certifiedPrime 8371193 3 [(p2,3),(p1046399,1)] (by decide +kernel)

private def p8469997 := certifiedPrime 8469997 2 [(p2,2),(p3,1),(p705833,1)] (by decide +kernel)

private def p8496869 := certifiedPrime 8496869 2 [(p2,2),(p317,1),(p6701,1)] (by decide +kernel)

private def p8498989 := certifiedPrime 8498989 2 [(p2,2),(p3,2),(p307,1),(p769,1)] (by decide +kernel)

private def p8659999 := certifiedPrime 8659999 3 [(p2,1),(p3,2),(p37,1),(p13003,1)] (by decide +kernel)

private def p8696999 := certifiedPrime 8696999 11 [(p2,1),(p37,1),(p211,1),(p557,1)] (by decide +kernel)

private def p8719999 := certifiedPrime 8719999 3 [(p2,1),(p3,1),(p7,1),(p207619,1)] (by decide +kernel)

private def p8758889 := certifiedPrime 8758889 3 [(p2,3),(p79,1),(p13859,1)] (by decide +kernel)

private def p8788991 := certifiedPrime 8788991 14 [(p2,1),(p5,1),(p7,1),(p23,1),(p53,1),(p103,1)] (by decide +kernel)

private def p8856997 := certifiedPrime 8856997 5 [(p2,2),(p3,1),(p738083,1)] (by decide +kernel)

private def p8887661 := certifiedPrime 8887661 2 [(p2,2),(p5,1),(p23,1),(p139,2)] (by decide +kernel)

private def p8899937 := certifiedPrime 8899937 3 [(p2,5),(p278123,1)] (by decide +kernel)

private def p8899949 := certifiedPrime 8899949 2 [(p2,2),(p2224987,1)] (by decide +kernel)

private def p8969993 := certifiedPrime 8969993 3 [(p2,3),(p1121249,1)] (by decide +kernel)

private def p8975243 := certifiedPrime 8975243 2 [(p2,1),(p4487621,1)] (by decide +kernel)

private def p8983699 := certifiedPrime 8983699 2 [(p2,1),(p3,1),(p1497283,1)] (by decide +kernel)

private def p8998889 := certifiedPrime 8998889 3 [(p2,3),(p23,1),(p48907,1)] (by decide +kernel)

private def p8999699 := certifiedPrime 8999699 2 [(p2,1),(p17,1),(p264697,1)] (by decide +kernel)

private def p8999897 := certifiedPrime 8999897 3 [(p2,3),(p1124987,1)] (by decide +kernel)

private def p8999993 := certifiedPrime 8999993 3 [(p2,3),(p23,1),(p41,1),(p1193,1)] (by decide +kernel)

private def p9199997 := certifiedPrime 9199997 2 [(p2,2),(p13,1),(p176923,1)] (by decide +kernel)

private def p9373853 := certifiedPrime 9373853 2 [(p2,2),(p1031,1),(p2273,1)] (by decide +kernel)

private def p9379973 := certifiedPrime 9379973 2 [(p2,2),(p7,2),(p47857,1)] (by decide +kernel)

private def p9434923 := certifiedPrime 9434923 2 [(p2,1),(p3,1),(p7,1),(p23,1),(p9767,1)] (by decide +kernel)

private def p9488879 := certifiedPrime 9488879 7 [(p2,1),(p7,1),(p571,1),(p1187,1)] (by decide +kernel)

private def p9494999 := certifiedPrime 9494999 13 [(p2,1),(p23,1),(p206413,1)] (by decide +kernel)

private def p9499961 := certifiedPrime 9499961 3 [(p2,3),(p5,1),(p439,1),(p541,1)] (by decide +kernel)

private def p9540719 := certifiedPrime 9540719 11 [(p2,1),(p11,1),(p47,1),(p9227,1)] (by decide +kernel)

private def p9598997 := certifiedPrime 9598997 2 [(p2,2),(p11,1),(p269,1),(p811,1)] (by decide +kernel)

private def p9759991 := certifiedPrime 9759991 3 [(p2,1),(p3,1),(p5,1),(p325333,1)] (by decide +kernel)

private def p9779993 := certifiedPrime 9779993 3 [(p2,3),(p1222499,1)] (by decide +kernel)

private def p9788887 := certifiedPrime 9788887 5 [(p2,1),(p3,2),(p543827,1)] (by decide +kernel)

private def p9799967 := certifiedPrime 9799967 5 [(p2,1),(p11,1),(p445453,1)] (by decide +kernel)

private def p9829999 := certifiedPrime 9829999 3 [(p2,1),(p3,4),(p60679,1)] (by decide +kernel)

private def p9859999 := certifiedPrime 9859999 3 [(p2,1),(p3,1),(p151,1),(p10883,1)] (by decide +kernel)

private def p9884887 := certifiedPrime 9884887 3 [(p2,1),(p3,1),(p11,1),(p149771,1)] (by decide +kernel)

private def p9886997 := certifiedPrime 9886997 3 [(p2,2),(p7,1),(p17,1),(p20771,1)] (by decide +kernel)

private def p9888887 := certifiedPrime 9888887 5 [(p2,1),(p7,2),(p100907,1)] (by decide +kernel)

private def p9888889 := certifiedPrime 9888889 11 [(p2,3),(p3,1),(p412037,1)] (by decide +kernel)

private def p9896989 := certifiedPrime 9896989 6 [(p2,2),(p3,1),(p824749,1)] (by decide +kernel)

private def p9899887 := certifiedPrime 9899887 3 [(p2,1),(p3,1),(p1649981,1)] (by decide +kernel)

private def p9899999 := certifiedPrime 9899999 7 [(p2,1),(p571,1),(p8669,1)] (by decide +kernel)

private def p9925907 := certifiedPrime 9925907 2 [(p2,1),(p4962953,1)] (by decide +kernel)

private def p9937751 := certifiedPrime 9937751 13 [(p2,1),(p5,3),(p127,1),(p313,1)] (by decide +kernel)

private def p9946999 := certifiedPrime 9946999 3 [(p2,1),(p3,2),(p552611,1)] (by decide +kernel)

private def p9959779 := certifiedPrime 9959779 2 [(p2,1),(p3,2),(p257,1),(p2153,1)] (by decide +kernel)

private def p9967777 := certifiedPrime 9967777 5 [(p2,5),(p3,1),(p7,2),(p13,1),(p163,1)] (by decide +kernel)

private def p9977899 := certifiedPrime 9977899 7 [(p2,1),(p3,1),(p7,1),(p353,1),(p673,1)] (by decide +kernel)

private def p9978883 := certifiedPrime 9978883 2 [(p2,1),(p3,1),(p1663147,1)] (by decide +kernel)

private def p9981889 := certifiedPrime 9981889 26 [(p2,6),(p3,1),(p7,2),(p1061,1)] (by decide +kernel)

private def p9989899 := certifiedPrime 9989899 2 [(p2,1),(p3,1),(p811,1),(p2053,1)] (by decide +kernel)

private def p9996991 := certifiedPrime 9996991 7 [(p2,1),(p3,1),(p5,1),(p333233,1)] (by decide +kernel)

private def p9999883 := certifiedPrime 9999883 3 [(p2,1),(p3,3),(p185183,1)] (by decide +kernel)

private def p9999991 := certifiedPrime 9999991 22 [(p2,1),(p3,3),(p5,1),(p7,1),(p11,1),(p13,1),(p37,1)] (by decide +kernel)

private def p10231511 := certifiedPrime 10231511 11 [(p2,1),(p5,1),(p163,1),(p6277,1)] (by decide +kernel)

private def p10430839 := certifiedPrime 10430839 3 [(p2,1),(p3,2),(p11,1),(p139,1),(p379,1)] (by decide +kernel)

private def p11145259 := certifiedPrime 11145259 2 [(p2,1),(p3,2),(p619181,1)] (by decide +kernel)

private def p11297789 := certifiedPrime 11297789 2 [(p2,2),(p2824447,1)] (by decide +kernel)

private def p11525641 := certifiedPrime 11525641 22 [(p2,3),(p3,1),(p5,1),(p7,1),(p13721,1)] (by decide +kernel)

private def p11653333 := certifiedPrime 11653333 2 [(p2,2),(p3,1),(p971111,1)] (by decide +kernel)

private def p11787493 := certifiedPrime 11787493 2 [(p2,2),(p3,1),(p59,1),(p16649,1)] (by decide +kernel)

private def p12261311 := certifiedPrime 12261311 31 [(p2,1),(p5,1),(p457,1),(p2683,1)] (by decide +kernel)

private def p12487361 := certifiedPrime 12487361 3 [(p2,6),(p5,1),(p39023,1)] (by decide +kernel)

private def p12546343 := certifiedPrime 12546343 5 [(p2,1),(p3,2),(p697019,1)] (by decide +kernel)

private def p12600271 := certifiedPrime 12600271 12 [(p2,1),(p3,2),(p5,1),(p191,1),(p733,1)] (by decide +kernel)

private def p12653863 := certifiedPrime 12653863 3 [(p2,1),(p3,1),(p13,1),(p162229,1)] (by decide +kernel)

private def p12763721 := certifiedPrime 12763721 3 [(p2,3),(p5,1),(p319093,1)] (by decide +kernel)

private def p12918293 := certifiedPrime 12918293 2 [(p2,2),(p3229573,1)] (by decide +kernel)

private def p13027519 := certifiedPrime 13027519 6 [(p2,1),(p3,2),(p7,1),(p103393,1)] (by decide +kernel)

private def p13210357 := certifiedPrime 13210357 6 [(p2,2),(p3,1),(p53,1),(p20771,1)] (by decide +kernel)

private def p13299439 := certifiedPrime 13299439 3 [(p2,1),(p3,1),(p1297,1),(p1709,1)] (by decide +kernel)

private def p13914587 := certifiedPrime 13914587 2 [(p2,1),(p7,1),(p23,1),(p79,1),(p547,1)] (by decide +kernel)

private def p14628617 := certifiedPrime 14628617 3 [(p2,3),(p37,1),(p73,1),(p677,1)] (by decide +kernel)

private def p14723227 := certifiedPrime 14723227 2 [(p2,1),(p3,2),(p7,2),(p16693,1)] (by decide +kernel)

private def p14893793 := certifiedPrime 14893793 3 [(p2,5),(p313,1),(p1487,1)] (by decide +kernel)

private def p15051013 := certifiedPrime 15051013 5 [(p2,2),(p3,1),(p1254251,1)] (by decide +kernel)

private def p15259501 := certifiedPrime 15259501 6 [(p2,2),(p3,2),(p5,3),(p3391,1)] (by decide +kernel)

private def p15715873 := certifiedPrime 15715873 5 [(p2,5),(p3,2),(p197,1),(p277,1)] (by decide +kernel)

private def p15780559 := certifiedPrime 15780559 3 [(p2,1),(p3,1),(p2630093,1)] (by decide +kernel)

private def p15890873 := certifiedPrime 15890873 3 [(p2,3),(p1986359,1)] (by decide +kernel)

private def p16568813 := certifiedPrime 16568813 2 [(p2,2),(p13,1),(p17,1),(p18743,1)] (by decide +kernel)

private def p16622807 := certifiedPrime 16622807 5 [(p2,1),(p1237,1),(p6719,1)] (by decide +kernel)

private def p16658333 := certifiedPrime 16658333 2 [(p2,2),(p4164583,1)] (by decide +kernel)

private def p16664833 := certifiedPrime 16664833 5 [(p2,8),(p3,3),(p2411,1)] (by decide +kernel)

private def p17094017 := certifiedPrime 17094017 3 [(p2,7),(p83,1),(p1609,1)] (by decide +kernel)

private def p18148037 := certifiedPrime 18148037 2 [(p2,2),(p379,1),(p11971,1)] (by decide +kernel)

private def p18449759 := certifiedPrime 18449759 11 [(p2,1),(p173,1),(p53323,1)] (by decide +kernel)

private def p18889999 := certifiedPrime 18889999 6 [(p2,1),(p3,1),(p3148333,1)] (by decide +kernel)

private def p19399999 := certifiedPrime 19399999 3 [(p2,1),(p3,1),(p3233333,1)] (by decide +kernel)

private def p19999999 := certifiedPrime 19999999 3 [(p2,1),(p3,2),(p239,1),(p4649,1)] (by decide +kernel)

private def p20490979 := certifiedPrime 20490979 2 [(p2,1),(p3,1),(p1303,1),(p2621,1)] (by decide +kernel)

private def p21449693 := certifiedPrime 21449693 2 [(p2,2),(p11,1),(p353,1),(p1381,1)] (by decide +kernel)

private def p21510053 := certifiedPrime 21510053 2 [(p2,2),(p19,1),(p283027,1)] (by decide +kernel)

private def p21658163 := certifiedPrime 21658163 2 [(p2,1),(p3251,1),(p3331,1)] (by decide +kernel)

private def p21695747 := certifiedPrime 21695747 2 [(p2,1),(p73,1),(p181,1),(p821,1)] (by decide +kernel)

private def p21723913 := certifiedPrime 21723913 10 [(p2,3),(p3,2),(p7,1),(p43103,1)] (by decide +kernel)

private def p22368421 := certifiedPrime 22368421 2 [(p2,2),(p3,3),(p5,1),(p23,1),(p1801,1)] (by decide +kernel)

private def p22393337 := certifiedPrime 22393337 3 [(p2,3),(p7,1),(p29,1),(p13789,1)] (by decide +kernel)

private def p22561219 := certifiedPrime 22561219 2 [(p2,1),(p3,2),(p1253401,1)] (by decide +kernel)

private def p24267073 := certifiedPrime 24267073 7 [(p2,6),(p3,1),(p97,1),(p1303,1)] (by decide +kernel)

private def p24357001 := certifiedPrime 24357001 26 [(p2,3),(p3,1),(p5,3),(p23,1),(p353,1)] (by decide +kernel)

private def p24770749 := certifiedPrime 24770749 2 [(p2,2),(p3,1),(p2064229,1)] (by decide +kernel)

private def p24979079 := certifiedPrime 24979079 11 [(p2,1),(p71,1),(p175909,1)] (by decide +kernel)

private def p25773067 := certifiedPrime 25773067 5 [(p2,1),(p3,6),(p11,1),(p1607,1)] (by decide +kernel)

private def p26301211 := certifiedPrime 26301211 19 [(p2,1),(p3,1),(p5,1),(p13,1),(p17,1),(p3967,1)] (by decide +kernel)

private def p26457323 := certifiedPrime 26457323 5 [(p2,1),(p31,1),(p426731,1)] (by decide +kernel)

private def p26587381 := certifiedPrime 26587381 6 [(p2,2),(p3,1),(p5,1),(p443123,1)] (by decide +kernel)

private def p26836969 := certifiedPrime 26836969 7 [(p2,3),(p3,1),(p19,1),(p229,1),(p257,1)] (by decide +kernel)

private def p26911111 := certifiedPrime 26911111 13 [(p2,1),(p3,1),(p5,1),(p401,1),(p2237,1)] (by decide +kernel)

private def p27137563 := certifiedPrime 27137563 2 [(p2,1),(p3,1),(p23,1),(p29,1),(p6781,1)] (by decide +kernel)

private def p27799999 := certifiedPrime 27799999 3 [(p2,1),(p3,1),(p17,1),(p272549,1)] (by decide +kernel)

private def p28243879 := certifiedPrime 28243879 6 [(p2,1),(p3,1),(p13,1),(p97,1),(p3733,1)] (by decide +kernel)

private def p28632047 := certifiedPrime 28632047 5 [(p2,1),(p17,1),(p191,1),(p4409,1)] (by decide +kernel)

private def p28873571 := certifiedPrime 28873571 2 [(p2,1),(p5,1),(p11,1),(p71,1),(p3697,1)] (by decide +kernel)

private def p28939019 := certifiedPrime 28939019 2 [(p2,1),(p2689,1),(p5381,1)] (by decide +kernel)

private def p28999991 := certifiedPrime 28999991 11 [(p2,1),(p5,1),(p173,1),(p16763,1)] (by decide +kernel)

private def p29199997 := certifiedPrime 29199997 2 [(p2,2),(p3,2),(p7,1),(p115873,1)] (by decide +kernel)

private def p29999999 := certifiedPrime 29999999 7 [(p2,1),(p7,1),(p2142857,1)] (by decide +kernel)

private def p31211519 := certifiedPrime 31211519 11 [(p2,1),(p13,1),(p1200443,1)] (by decide +kernel)

private def p31249931 := certifiedPrime 31249931 2 [(p2,1),(p5,1),(p401,1),(p7793,1)] (by decide +kernel)

private def p31296989 := certifiedPrime 31296989 2 [(p2,2),(p827,1),(p9461,1)] (by decide +kernel)

private def p33333329 := certifiedPrime 33333329 6 [(p2,4),(p7,2),(p17,1),(p41,1),(p61,1)] (by decide +kernel)

private def p34818257 := certifiedPrime 34818257 3 [(p2,4),(p11,1),(p197831,1)] (by decide +kernel)

private def p34999927 := certifiedPrime 34999927 3 [(p2,1),(p3,1),(p13,1),(p29,1),(p15473,1)] (by decide +kernel)

private def p35248201 := certifiedPrime 35248201 34 [(p2,3),(p3,1),(p5,2),(p13,1),(p4519,1)] (by decide +kernel)

private def p36074587 := certifiedPrime 36074587 2 [(p2,1),(p3,1),(p179,1),(p33589,1)] (by decide +kernel)

private def p37769993 := certifiedPrime 37769993 3 [(p2,3),(p13,1),(p363173,1)] (by decide +kernel)

private def p38354531 := certifiedPrime 38354531 2 [(p2,1),(p5,1),(p29,1),(p132257,1)] (by decide +kernel)

private def p39879997 := certifiedPrime 39879997 2 [(p2,2),(p3,1),(p13,1),(p255641,1)] (by decide +kernel)

private def p39896999 := certifiedPrime 39896999 7 [(p2,1),(p19,2),(p55259,1)] (by decide +kernel)

private def p39982499 := certifiedPrime 39982499 2 [(p2,1),(p19,1),(p31,1),(p33941,1)] (by decide +kernel)

private def p39987889 := certifiedPrime 39987889 19 [(p2,4),(p3,1),(p547,1),(p1523,1)] (by decide +kernel)

private def p39999979 := certifiedPrime 39999979 2 [(p2,1),(p3,2),(p19,1),(p116959,1)] (by decide +kernel)

private def p41356199 := certifiedPrime 41356199 11 [(p2,1),(p13,1),(p19,1),(p83717,1)] (by decide +kernel)

private def p42058109 := certifiedPrime 42058109 2 [(p2,2),(p661,1),(p15907,1)] (by decide +kernel)

private def p43999999 := certifiedPrime 43999999 3 [(p2,1),(p3,1),(p7,1),(p79,1),(p89,1),(p149,1)] (by decide +kernel)

private def p46666111 := certifiedPrime 46666111 3 [(p2,1),(p3,1),(p5,1),(p293,1),(p5309,1)] (by decide +kernel)

private def p46668421 := certifiedPrime 46668421 2 [(p2,2),(p3,3),(p5,1),(p86423,1)] (by decide +kernel)

private def p47399999 := certifiedPrime 47399999 11 [(p2,1),(p3931,1),(p6029,1)] (by decide +kernel)

private def p48933751 := certifiedPrime 48933751 6 [(p2,1),(p3,1),(p5,4),(p13049,1)] (by decide +kernel)

private def p49311959 := certifiedPrime 49311959 7 [(p2,1),(p79,1),(p312101,1)] (by decide +kernel)

private def p49889977 := certifiedPrime 49889977 13 [(p2,3),(p3,1),(p29,1),(p43,1),(p1667,1)] (by decide +kernel)

private def p49979999 := certifiedPrime 49979999 11 [(p2,1),(p31,1),(p806129,1)] (by decide +kernel)

private def p52758499 := certifiedPrime 52758499 3 [(p2,1),(p3,1),(p13,1),(p676391,1)] (by decide +kernel)

private def p53221111 := certifiedPrime 53221111 11 [(p2,1),(p3,1),(p5,1),(p31,1),(p89,1),(p643,1)] (by decide +kernel)

private def p55430839 := certifiedPrime 55430839 6 [(p2,1),(p3,3),(p479,1),(p2143,1)] (by decide +kernel)

private def p55999997 := certifiedPrime 55999997 2 [(p2,2),(p13,1),(p503,1),(p2141,1)] (by decide +kernel)

private def p57899999 := certifiedPrime 57899999 22 [(p2,1),(p13,1),(p2226923,1)] (by decide +kernel)

private def p58892909 := certifiedPrime 58892909 2 [(p2,2),(p14723227,1)] (by decide +kernel)

private def p58898981 := certifiedPrime 58898981 2 [(p2,2),(p5,1),(p7,2),(p60101,1)] (by decide +kernel)

private def p58988899 := certifiedPrime 58988899 3 [(p2,1),(p3,4),(p364129,1)] (by decide +kernel)

private def p58989899 := certifiedPrime 58989899 2 [(p2,1),(p11,1),(p17,1),(p41,1),(p3847,1)] (by decide +kernel)

private def p59538749 := certifiedPrime 59538749 2 [(p2,2),(p509,1),(p29243,1)] (by decide +kernel)

private def p59698897 := certifiedPrime 59698897 5 [(p2,4),(p3,1),(p263,1),(p4729,1)] (by decide +kernel)

private def p59888897 := certifiedPrime 59888897 3 [(p2,8),(p233941,1)] (by decide +kernel)

private def p59991991 := certifiedPrime 59991991 3 [(p2,1),(p3,1),(p5,1),(p1999733,1)] (by decide +kernel)

private def p59999999 := certifiedPrime 59999999 11 [(p2,1),(p29999999,1)] (by decide +kernel)

private def p60477707 := certifiedPrime 60477707 2 [(p2,1),(p41,1),(p737533,1)] (by decide +kernel)

private def p64666583 := certifiedPrime 64666583 7 [(p2,1),(p43,1),(p389,1),(p1933,1)] (by decide +kernel)

private def p65356469 := certifiedPrime 65356469 2 [(p2,2),(p2153,1),(p7589,1)] (by decide +kernel)

private def p65641633 := certifiedPrime 65641633 10 [(p2,5),(p3,1),(p7,1),(p23,1),(p31,1),(p137,1)] (by decide +kernel)

private def p65714959 := certifiedPrime 65714959 3 [(p2,1),(p3,2),(p19,1),(p192149,1)] (by decide +kernel)

private def p65999993 := certifiedPrime 65999993 3 [(p2,3),(p31,1),(p266129,1)] (by decide +kernel)

private def p68988889 := certifiedPrime 68988889 19 [(p2,3),(p3,3),(p31,1),(p10303,1)] (by decide +kernel)

private def p69499999 := certifiedPrime 69499999 3 [(p2,1),(p3,3),(p887,1),(p1451,1)] (by decide +kernel)

private def p69712411 := certifiedPrime 69712411 10 [(p2,1),(p3,1),(p5,1),(p17,1),(p136691,1)] (by decide +kernel)

private def p69919999 := certifiedPrime 69919999 3 [(p2,1),(p3,1),(p11653333,1)] (by decide +kernel)

private def p69979997 := certifiedPrime 69979997 2 [(p2,2),(p113,1),(p154823,1)] (by decide +kernel)

private def p69979999 := certifiedPrime 69979999 3 [(p2,1),(p3,1),(p11,1),(p1060303,1)] (by decide +kernel)

private def p73979797 := certifiedPrime 73979797 2 [(p2,2),(p3,1),(p11,1),(p263,1),(p2131,1)] (by decide +kernel)

private def p74988553 := certifiedPrime 74988553 11 [(p2,3),(p3,1),(p89,1),(p35107,1)] (by decide +kernel)

private def p75833333 := certifiedPrime 75833333 2 [(p2,2),(p19,1),(p997807,1)] (by decide +kernel)

private def p75923179 := certifiedPrime 75923179 3 [(p2,1),(p3,1),(p12653863,1)] (by decide +kernel)

private def p75999689 := certifiedPrime 75999689 3 [(p2,3),(p9499961,1)] (by decide +kernel)

private def p75999991 := certifiedPrime 75999991 3 [(p2,1),(p3,1),(p5,1),(p11,1),(p230303,1)] (by decide +kernel)

private def p77204851 := certifiedPrime 77204851 3 [(p2,1),(p3,1),(p5,2),(p131,1),(p3929,1)] (by decide +kernel)

private def p77599997 := certifiedPrime 77599997 2 [(p2,2),(p19399999,1)] (by decide +kernel)

private def p77789983 := certifiedPrime 77789983 3 [(p2,1),(p3,1),(p47,1),(p223,1),(p1237,1)] (by decide +kernel)

private def p77796599 := certifiedPrime 77796599 19 [(p2,1),(p11,1),(p41,1),(p86249,1)] (by decide +kernel)

private def p78299999 := certifiedPrime 78299999 13 [(p2,1),(p7,1),(p503,1),(p11119,1)] (by decide +kernel)

private def p78689993 := certifiedPrime 78689993 5 [(p2,3),(p23,1),(p29,1),(p14747,1)] (by decide +kernel)

private def p78899993 := certifiedPrime 78899993 3 [(p2,3),(p17,1),(p59,1),(p9833,1)] (by decide +kernel)

private def p78948899 := certifiedPrime 78948899 6 [(p2,1),(p7,2),(p37,1),(p21773,1)] (by decide +kernel)

private def p79222621 := certifiedPrime 79222621 2 [(p2,2),(p3,1),(p5,1),(p1320377,1)] (by decide +kernel)

private def p79648897 := certifiedPrime 79648897 10 [(p2,7),(p3,1),(p41,1),(p5059,1)] (by decide +kernel)

private def p79796869 := certifiedPrime 79796869 2 [(p2,2),(p3,1),(p101,1),(p65839,1)] (by decide +kernel)

private def p79877999 := certifiedPrime 79877999 11 [(p2,1),(p449,1),(p88951,1)] (by decide +kernel)

private def p79878889 := certifiedPrime 79878889 7 [(p2,3),(p3,2),(p19,1),(p58391,1)] (by decide +kernel)

private def p79890163 := certifiedPrime 79890163 2 [(p2,1),(p3,1),(p11,1),(p31,1),(p39047,1)] (by decide +kernel)

private def p79964999 := certifiedPrime 79964999 7 [(p2,1),(p39982499,1)] (by decide +kernel)

private def p79999973 := certifiedPrime 79999973 2 [(p2,2),(p13,1),(p1538461,1)] (by decide +kernel)

private def p79999981 := certifiedPrime 79999981 7 [(p2,2),(p3,1),(p5,1),(p23,1),(p29,1),(p1999,1)] (by decide +kernel)

private def p82281893 := certifiedPrime 82281893 2 [(p2,2),(p7,1),(p11,1),(p311,1),(p859,1)] (by decide +kernel)

private def p84893617 := certifiedPrime 84893617 5 [(p2,4),(p3,3),(p41,1),(p4793,1)] (by decide +kernel)

private def p86499997 := certifiedPrime 86499997 5 [(p2,2),(p3,1),(p11,2),(p41,1),(p1453,1)] (by decide +kernel)

private def p87498737 := certifiedPrime 87498737 3 [(p2,4),(p13,2),(p32359,1)] (by decide +kernel)

private def p87999997 := certifiedPrime 87999997 5 [(p2,2),(p3,1),(p7,1),(p79,1),(p89,1),(p149,1)] (by decide +kernel)

private def p88599997 := certifiedPrime 88599997 2 [(p2,2),(p3,2),(p67,1),(p109,1),(p337,1)] (by decide +kernel)

private def p88899883 := certifiedPrime 88899883 2 [(p2,1),(p3,1),(p2851,1),(p5197,1)] (by decide +kernel)

private def p88987889 := certifiedPrime 88987889 3 [(p2,4),(p11,1),(p505613,1)] (by decide +kernel)

private def p88998881 := certifiedPrime 88998881 7 [(p2,5),(p5,1),(p556243,1)] (by decide +kernel)

private def p89299999 := certifiedPrime 89299999 3 [(p2,1),(p3,2),(p569,1),(p8719,1)] (by decide +kernel)

private def p89699999 := certifiedPrime 89699999 7 [(p2,1),(p653,1),(p68683,1)] (by decide +kernel)

private def p89898997 := certifiedPrime 89898997 6 [(p2,2),(p3,1),(p11,1),(p23,1),(p29611,1)] (by decide +kernel)

private def p89999999 := certifiedPrime 89999999 11 [(p2,1),(p11,1),(p19,1),(p139,1),(p1549,1)] (by decide +kernel)

private def p91979999 := certifiedPrime 91979999 11 [(p2,1),(p11,1),(p4180909,1)] (by decide +kernel)

private def p93679997 := certifiedPrime 93679997 2 [(p2,2),(p17,1),(p1103,1),(p1249,1)] (by decide +kernel)

private def p94298989 := certifiedPrime 94298989 10 [(p2,2),(p3,1),(p7,1),(p23,1),(p48809,1)] (by decide +kernel)

private def p94999897 := certifiedPrime 94999897 5 [(p2,3),(p3,2),(p1319443,1)] (by decide +kernel)

private def p95699999 := certifiedPrime 95699999 13 [(p2,1),(p19,1),(p2518421,1)] (by decide +kernel)

private def p95999993 := certifiedPrime 95999993 3 [(p2,3),(p11,1),(p1090909,1)] (by decide +kernel)

private def p96299989 := certifiedPrime 96299989 6 [(p2,2),(p3,1),(p23,1),(p383,1),(p911,1)] (by decide +kernel)

private def p96627079 := certifiedPrime 96627079 17 [(p2,1),(p3,2),(p41,1),(p311,1),(p421,1)] (by decide +kernel)

private def p96998983 := certifiedPrime 96998983 3 [(p2,1),(p3,1),(p67,1),(p241291,1)] (by decide +kernel)

private def p97759999 := certifiedPrime 97759999 7 [(p2,1),(p3,2),(p7,2),(p271,1),(p409,1)] (by decide +kernel)

private def p98579993 := certifiedPrime 98579993 3 [(p2,3),(p7,1),(p79,1),(p22283,1)] (by decide +kernel)

private def p98599999 := certifiedPrime 98599999 3 [(p2,1),(p3,1),(p7,1),(p41,1),(p57259,1)] (by decide +kernel)

private def p98689999 := certifiedPrime 98689999 3 [(p2,1),(p3,1),(p11,1),(p17,1),(p87959,1)] (by decide +kernel)

private def p98869997 := certifiedPrime 98869997 2 [(p2,2),(p19,1),(p1300921,1)] (by decide +kernel)

private def p98898889 := certifiedPrime 98898889 7 [(p2,3),(p3,1),(p11,1),(p41,1),(p9137,1)] (by decide +kernel)

private def p98988893 := certifiedPrime 98988893 2 [(p2,2),(p17,1),(p1097,1),(p1327,1)] (by decide +kernel)

private def p98994899 := certifiedPrime 98994899 2 [(p2,1),(p23,1),(p2152063,1)] (by decide +kernel)

private def p98999983 := certifiedPrime 98999983 3 [(p2,1),(p3,4),(p611111,1)] (by decide +kernel)

private def p99379991 := certifiedPrime 99379991 7 [(p2,1),(p5,1),(p907,1),(p10957,1)] (by decide +kernel)

private def p99399899 := certifiedPrime 99399899 2 [(p2,1),(p13,1),(p461,1),(p8293,1)] (by decide +kernel)

private def p99889997 := certifiedPrime 99889997 2 [(p2,2),(p677,1),(p36887,1)] (by decide +kernel)

private def p99898889 := certifiedPrime 99898889 3 [(p2,3),(p12487361,1)] (by decide +kernel)

private def p99899999 := certifiedPrime 99899999 11 [(p2,1),(p11,1),(p4540909,1)] (by decide +kernel)

private def p99948889 := certifiedPrime 99948889 7 [(p2,3),(p3,2),(p13,1),(p106783,1)] (by decide +kernel)

private def p99949999 := certifiedPrime 99949999 13 [(p2,1),(p3,1),(p16658333,1)] (by decide +kernel)

private def p99969589 := certifiedPrime 99969589 2 [(p2,2),(p3,2),(p17,1),(p379,1),(p431,1)] (by decide +kernel)

private def p101005001 := certifiedPrime 101005001 6 [(p2,3),(p5,4),(p20201,1)] (by decide +kernel)

private def p103333333 := certifiedPrime 103333333 2 [(p2,2),(p3,1),(p653,1),(p13187,1)] (by decide +kernel)

private def p105948809 := certifiedPrime 105948809 3 [(p2,3),(p7,1),(p167,1),(p11329,1)] (by decide +kernel)

private def p106685633 := certifiedPrime 106685633 3 [(p2,6),(p31,1),(p53773,1)] (by decide +kernel)

private def p116369371 := certifiedPrime 116369371 3 [(p2,1),(p3,2),(p5,1),(p13,1),(p79,1),(p1259,1)] (by decide +kernel)

private def p119077499 := certifiedPrime 119077499 2 [(p2,1),(p59538749,1)] (by decide +kernel)

private def p119650187 := certifiedPrime 119650187 2 [(p2,1),(p23,1),(p2601091,1)] (by decide +kernel)

private def p120121777 := certifiedPrime 120121777 5 [(p2,4),(p3,2),(p31,1),(p71,1),(p379,1)] (by decide +kernel)

private def p130951043 := certifiedPrime 130951043 2 [(p2,1),(p2767,1),(p23663,1)] (by decide +kernel)

private def p132885229 := certifiedPrime 132885229 6 [(p2,2),(p3,1),(p7,1),(p59,1),(p26813,1)] (by decide +kernel)

private def p134830303 := certifiedPrime 134830303 6 [(p2,1),(p3,1),(p421,1),(p53377,1)] (by decide +kernel)

private def p149122807 := certifiedPrime 149122807 3 [(p2,1),(p3,1),(p7,1),(p883,1),(p4021,1)] (by decide +kernel)

private def p155593199 := certifiedPrime 155593199 11 [(p2,1),(p77796599,1)] (by decide +kernel)

private def p155635237 := certifiedPrime 155635237 2 [(p2,2),(p3,3),(p47,1),(p30661,1)] (by decide +kernel)

private def p157652567 := certifiedPrime 157652567 5 [(p2,1),(p613,1),(p128591,1)] (by decide +kernel)

private def p162777037 := certifiedPrime 162777037 6 [(p2,2),(p3,1),(p61,1),(p67,1),(p3319,1)] (by decide +kernel)

private def p162825379 := certifiedPrime 162825379 2 [(p2,1),(p3,1),(p27137563,1)] (by decide +kernel)

private def p166649333 := certifiedPrime 166649333 2 [(p2,2),(p37,1),(p379,1),(p2971,1)] (by decide +kernel)

private def p177545729 := certifiedPrime 177545729 3 [(p2,9),(p19,1),(p18251,1)] (by decide +kernel)

private def p184210421 := certifiedPrime 184210421 3 [(p2,2),(p5,1),(p37,1),(p89,1),(p2797,1)] (by decide +kernel)

private def p184387037 := certifiedPrime 184387037 2 [(p2,2),(p59,1),(p781301,1)] (by decide +kernel)

private def p187477061 := certifiedPrime 187477061 2 [(p2,2),(p5,1),(p9373853,1)] (by decide +kernel)

private def p188599889 := certifiedPrime 188599889 3 [(p2,4),(p11787493,1)] (by decide +kernel)

private def p206934071 := certifiedPrime 206934071 7 [(p2,1),(p5,1),(p7,1),(p2956201,1)] (by decide +kernel)

private def p211897619 := certifiedPrime 211897619 2 [(p2,1),(p105948809,1)] (by decide +kernel)

private def p233602459 := certifiedPrime 233602459 2 [(p2,1),(p3,1),(p557,1),(p69899,1)] (by decide +kernel)

private def p243546181 := certifiedPrime 243546181 2 [(p2,2),(p3,1),(p5,1),(p19,1),(p213637,1)] (by decide +kernel)

private def p247474999 := certifiedPrime 247474999 3 [(p2,1),(p3,2),(p617,1),(p22283,1)] (by decide +kernel)

private def p249949499 := certifiedPrime 249949499 2 [(p2,1),(p2213,1),(p56473,1)] (by decide +kernel)

private def p260552371 := certifiedPrime 260552371 3 [(p2,1),(p3,1),(p5,1),(p13,2),(p17,1),(p3023,1)] (by decide +kernel)

private def p261902087 := certifiedPrime 261902087 5 [(p2,1),(p130951043,1)] (by decide +kernel)

private def p268999999 := certifiedPrime 268999999 3 [(p2,1),(p3,1),(p29,1),(p59,1),(p26203,1)] (by decide +kernel)

private def p270325169 := certifiedPrime 270325169 3 [(p2,4),(p67,1),(p252169,1)] (by decide +kernel)

private def p279999991 := certifiedPrime 279999991 6 [(p2,1),(p3,4),(p5,1),(p345679,1)] (by decide +kernel)

private def p282675709 := certifiedPrime 282675709 2 [(p2,2),(p3,2),(p7,2),(p37,1),(p61,1),(p71,1)] (by decide +kernel)

private def p289999999 := certifiedPrime 289999999 7 [(p2,1),(p3,2),(p43,1),(p374677,1)] (by decide +kernel)

private def p294899999 := certifiedPrime 294899999 7 [(p2,1),(p73,1),(p1289,1),(p1567,1)] (by decide +kernel)

private def p297999997 := certifiedPrime 297999997 2 [(p2,2),(p3,1),(p7,1),(p3547619,1)] (by decide +kernel)

private def p299995999 := certifiedPrime 299995999 3 [(p2,1),(p3,1),(p1319,1),(p37907,1)] (by decide +kernel)

private def p299999699 := certifiedPrime 299999699 2 [(p2,1),(p257,1),(p583657,1)] (by decide +kernel)

private def p311090399 := certifiedPrime 311090399 7 [(p2,1),(p5087,1),(p30577,1)] (by decide +kernel)

private def p314360587 := certifiedPrime 314360587 2 [(p2,1),(p3,2),(p19,1),(p919183,1)] (by decide +kernel)

private def p322933333 := certifiedPrime 322933333 2 [(p2,2),(p3,1),(p26911111,1)] (by decide +kernel)

private def p324502649 := certifiedPrime 324502649 3 [(p2,3),(p2389,1),(p16979,1)] (by decide +kernel)

private def p338452237 := certifiedPrime 338452237 2 [(p2,2),(p3,3),(p73,1),(p42929,1)] (by decide +kernel)

private def p339472807 := certifiedPrime 339472807 3 [(p2,1),(p3,1),(p229,1),(p247069,1)] (by decide +kernel)

private def p345032927 := certifiedPrime 345032927 7 [(p2,1),(p7,1),(p229,1),(p107621,1)] (by decide +kernel)

private def p367979993 := certifiedPrime 367979993 5 [(p2,3),(p19,1),(p2420921,1)] (by decide +kernel)

private def p369889997 := certifiedPrime 369889997 2 [(p2,2),(p7,1),(p13210357,1)] (by decide +kernel)

private def p374954123 := certifiedPrime 374954123 2 [(p2,1),(p187477061,1)] (by decide +kernel)

private def p379999999 := certifiedPrime 379999999 3 [(p2,1),(p3,9),(p7,2),(p197,1)] (by decide +kernel)

private def p389550347 := certifiedPrime 389550347 2 [(p2,1),(p1049,1),(p185677,1)] (by decide +kernel)

private def p389999999 := certifiedPrime 389999999 7 [(p2,1),(p5441,1),(p35839,1)] (by decide +kernel)

private def p397805819 := certifiedPrime 397805819 6 [(p2,1),(p29,1),(p6858721,1)] (by decide +kernel)

private def p400576609 := certifiedPrime 400576609 14 [(p2,5),(p3,2),(p1390891,1)] (by decide +kernel)

private def p444444443 := certifiedPrime 444444443 2 [(p2,1),(p13,1),(p17094017,1)] (by decide +kernel)

private def p459301109 := certifiedPrime 459301109 2 [(p2,2),(p7,2),(p47,1),(p73,1),(p683,1)] (by decide +kernel)

private def p469999997 := certifiedPrime 469999997 2 [(p2,2),(p113,1),(p1039823,1)] (by decide +kernel)

private def p478889899 := certifiedPrime 478889899 2 [(p2,1),(p3,1),(p17,1),(p4694999,1)] (by decide +kernel)

private def p479959999 := certifiedPrime 479959999 3 [(p2,1),(p3,1),(p7,2),(p23,1),(p70979,1)] (by decide +kernel)

private def p489996449 := certifiedPrime 489996449 3 [(p2,5),(p53,1),(p288913,1)] (by decide +kernel)

private def p493499999 := certifiedPrime 493499999 11 [(p2,1),(p1187,1),(p207877,1)] (by decide +kernel)

private def p499499999 := certifiedPrime 499499999 11 [(p2,1),(p499,1),(p500501,1)] (by decide +kernel)

private def p499699999 := certifiedPrime 499699999 3 [(p2,1),(p3,2),(p7,1),(p359,1),(p11047,1)] (by decide +kernel)

private def p499898999 := certifiedPrime 499898999 13 [(p2,1),(p249949499,1)] (by decide +kernel)

private def p544441111 := certifiedPrime 544441111 3 [(p2,1),(p3,1),(p5,1),(p18148037,1)] (by decide +kernel)

private def p569498899 := certifiedPrime 569498899 2 [(p2,1),(p3,1),(p349,1),(p271967,1)] (by decide +kernel)

private def p580656101 := certifiedPrime 580656101 2 [(p2,2),(p5,2),(p5806561,1)] (by decide +kernel)

private def p589399997 := certifiedPrime 589399997 2 [(p2,2),(p17,1),(p2621,1),(p3307,1)] (by decide +kernel)

private def p592842857 := certifiedPrime 592842857 3 [(p2,3),(p59,1),(p1256023,1)] (by decide +kernel)

private def p596998999 := certifiedPrime 596998999 3 [(p2,1),(p3,5),(p1228393,1)] (by decide +kernel)

private def p599497897 := certifiedPrime 599497897 5 [(p2,3),(p3,1),(p24979079,1)] (by decide +kernel)

private def p599678999 := certifiedPrime 599678999 19 [(p2,1),(p179,1),(p293,1),(p5717,1)] (by decide +kernel)

private def p599888797 := certifiedPrime 599888797 2 [(p2,2),(p3,1),(p13,1),(p3845441,1)] (by decide +kernel)

private def p608512511 := certifiedPrime 608512511 17 [(p2,1),(p5,1),(p29,1),(p79,1),(p26561,1)] (by decide +kernel)

private def p619047619 := certifiedPrime 619047619 7 [(p2,1),(p3,1),(p7,1),(p31,1),(p149,1),(p3191,1)] (by decide +kernel)

private def p619999999 := certifiedPrime 619999999 3 [(p2,1),(p3,1),(p103333333,1)] (by decide +kernel)

private def p622540949 := certifiedPrime 622540949 2 [(p2,2),(p155635237,1)] (by decide +kernel)

private def p624230381 := certifiedPrime 624230381 2 [(p2,2),(p5,1),(p31211519,1)] (by decide +kernel)

private def p634975753 := certifiedPrime 634975753 5 [(p2,3),(p3,1),(p26457323,1)] (by decide +kernel)

private def p648998993 := certifiedPrime 648998993 3 [(p2,4),(p53,1),(p765329,1)] (by decide +kernel)

private def p654164843 := certifiedPrime 654164843 2 [(p2,1),(p823,1),(p397427,1)] (by decide +kernel)

private def p669955991 := certifiedPrime 669955991 11 [(p2,1),(p5,1),(p11,1),(p41,1),(p148549,1)] (by decide +kernel)

private def p679989889 := certifiedPrime 679989889 13 [(p2,7),(p3,2),(p590269,1)] (by decide +kernel)

private def p699689899 := certifiedPrime 699689899 3 [(p2,1),(p3,2),(p113,1),(p343997,1)] (by decide +kernel)

private def p699989897 := certifiedPrime 699989897 3 [(p2,3),(p87498737,1)] (by decide +kernel)

private def p729979979 := certifiedPrime 729979979 7 [(p2,1),(p7,1),(p13,1),(p59,1),(p157,1),(p433,1)] (by decide +kernel)

private def p738989899 := certifiedPrime 738989899 2 [(p2,1),(p3,1),(p17,1),(p7244999,1)] (by decide +kernel)

private def p741260431 := certifiedPrime 741260431 7 [(p2,1),(p3,3),(p5,1),(p163,1),(p16843,1)] (by decide +kernel)

private def p755311439 := certifiedPrime 755311439 7 [(p2,1),(p7,1),(p29,1),(p1860373,1)] (by decide +kernel)

private def p773333333 := certifiedPrime 773333333 2 [(p2,2),(p17,1),(p241,1),(p47189,1)] (by decide +kernel)

private def p775998997 := certifiedPrime 775998997 13 [(p2,2),(p3,1),(p64666583,1)] (by decide +kernel)

private def p778889999 := certifiedPrime 778889999 19 [(p2,1),(p73,1),(p5334863,1)] (by decide +kernel)

private def p787699597 := certifiedPrime 787699597 2 [(p2,2),(p3,1),(p65641633,1)] (by decide +kernel)

private def p789999983 := certifiedPrime 789999983 5 [(p2,1),(p101,1),(p1499,1),(p2609,1)] (by decide +kernel)

private def p794989889 := certifiedPrime 794989889 3 [(p2,6),(p7,1),(p11,1),(p353,1),(p457,1)] (by decide +kernel)

private def p794999999 := certifiedPrime 794999999 17 [(p2,1),(p13,2),(p1451,1),(p1621,1)] (by decide +kernel)

private def p799199993 := certifiedPrime 799199993 3 [(p2,3),(p99899999,1)] (by decide +kernel)

private def p799988887 := certifiedPrime 799988887 5 [(p2,1),(p3,4),(p4938203,1)] (by decide +kernel)

private def p799999897 := certifiedPrime 799999897 5 [(p2,3),(p3,1),(p33333329,1)] (by decide +kernel)

private def p799999999 := certifiedPrime 799999999 3 [(p2,1),(p3,1),(p7,1),(p59,1),(p113,1),(p2857,1)] (by decide +kernel)

private def p828499799 := certifiedPrime 828499799 7 [(p2,1),(p7,1),(p277,1),(p213641,1)] (by decide +kernel)

private def p839989999 := certifiedPrime 839989999 3 [(p2,1),(p3,2),(p46666111,1)] (by decide +kernel)

private def p859889999 := certifiedPrime 859889999 11 [(p2,1),(p11,1),(p113,2),(p3061,1)] (by decide +kernel)

private def p859999993 := certifiedPrime 859999993 5 [(p2,3),(p3,1),(p23,1),(p199,1),(p7829,1)] (by decide +kernel)

private def p859999997 := certifiedPrime 859999997 2 [(p2,2),(p71,1),(p631,1),(p4799,1)] (by decide +kernel)

private def p861545089 := certifiedPrime 861545089 14 [(p2,7),(p3,2),(p747869,1)] (by decide +kernel)

private def p865790089 := certifiedPrime 865790089 7 [(p2,3),(p3,1),(p36074587,1)] (by decide +kernel)

private def p866584421 := certifiedPrime 866584421 3 [(p2,2),(p5,1),(p13,1),(p97,1),(p34361,1)] (by decide +kernel)

private def p869999993 := certifiedPrime 869999993 3 [(p2,3),(p41,1),(p2652439,1)] (by decide +kernel)

private def p877788889 := certifiedPrime 877788889 11 [(p2,3),(p3,1),(p37,1),(p988501,1)] (by decide +kernel)

private def p877879999 := certifiedPrime 877879999 3 [(p2,1),(p3,3),(p59,1),(p275543,1)] (by decide +kernel)

private def p882300997 := certifiedPrime 882300997 13 [(p2,2),(p3,2),(p521,1),(p47041,1)] (by decide +kernel)

private def p886999499 := certifiedPrime 886999499 2 [(p2,1),(p7,1),(p11,1),(p1181,1),(p4877,1)] (by decide +kernel)

private def p888699991 := certifiedPrime 888699991 11 [(p2,1),(p3,1),(p5,1),(p17,1),(p23,1),(p239,1),(p317,1)] (by decide +kernel)

private def p888888887 := certifiedPrime 888888887 5 [(p2,1),(p444444443,1)] (by decide +kernel)

private def p888999997 := certifiedPrime 888999997 2 [(p2,2),(p3,1),(p89,1),(p443,1),(p1879,1)] (by decide +kernel)

private def p889888889 := certifiedPrime 889888889 3 [(p2,3),(p7,1),(p15890873,1)] (by decide +kernel)

private def p889988993 := certifiedPrime 889988993 3 [(p2,7),(p47,1),(p147937,1)] (by decide +kernel)

private def p894989899 := certifiedPrime 894989899 14 [(p2,1),(p3,5),(p11,1),(p167413,1)] (by decide +kernel)

private def p895899967 := certifiedPrime 895899967 3 [(p2,1),(p3,1),(p13,1),(p17,1),(p557,1),(p1213,1)] (by decide +kernel)

private def p897888989 := certifiedPrime 897888989 2 [(p2,2),(p367,1),(p611641,1)] (by decide +kernel)

private def p898999999 := certifiedPrime 898999999 3 [(p2,1),(p3,1),(p13,1),(p11525641,1)] (by decide +kernel)

private def p899968999 := certifiedPrime 899968999 3 [(p2,1),(p3,1),(p31,1),(p4838543,1)] (by decide +kernel)

private def p899989889 := certifiedPrime 899989889 3 [(p2,7),(p7,1),(p1004453,1)] (by decide +kernel)

private def p899992991 := certifiedPrime 899992991 7 [(p2,1),(p5,1),(p13,1),(p23,3),(p569,1)] (by decide +kernel)

private def p909999997 := certifiedPrime 909999997 2 [(p2,2),(p3,1),(p75833333,1)] (by decide +kernel)

private def p911078149 := certifiedPrime 911078149 2 [(p2,2),(p3,1),(p75923179,1)] (by decide +kernel)

private def p948449483 := certifiedPrime 948449483 2 [(p2,1),(p17,1),(p23,1),(p1212851,1)] (by decide +kernel)

private def p957979999 := certifiedPrime 957979999 3 [(p2,1),(p3,2),(p53221111,1)] (by decide +kernel)

private def p959959999 := certifiedPrime 959959999 3 [(p2,1),(p3,4),(p193,1),(p30703,1)] (by decide +kernel)

private def p963889999 := certifiedPrime 963889999 3 [(p2,1),(p3,1),(p7591,1),(p21163,1)] (by decide +kernel)

private def p969599999 := certifiedPrime 969599999 7 [(p2,1),(p17,1),(p71,1),(p89,1),(p4513,1)] (by decide +kernel)

private def p969799979 := certifiedPrime 969799979 2 [(p2,1),(p7,1),(p41,1),(p709,1),(p2383,1)] (by decide +kernel)

private def p969996887 := certifiedPrime 969996887 5 [(p2,1),(p109,1),(p4449527,1)] (by decide +kernel)

private def p978899891 := certifiedPrime 978899891 2 [(p2,1),(p5,1),(p991,1),(p98779,1)] (by decide +kernel)

private def p979989991 := certifiedPrime 979989991 3 [(p2,1),(p3,1),(p5,1),(p7,1),(p17,1),(p277,1),(p991,1)] (by decide +kernel)

private def p979992899 := certifiedPrime 979992899 2 [(p2,1),(p489996449,1)] (by decide +kernel)

private def p979999997 := certifiedPrime 979999997 2 [(p2,2),(p131,1),(p1870229,1)] (by decide +kernel)

private def p986999999 := certifiedPrime 986999999 13 [(p2,1),(p493499999,1)] (by decide +kernel)

private def p988888993 := certifiedPrime 988888993 5 [(p2,5),(p3,1),(p7,2),(p13,1),(p103,1),(p157,1)] (by decide +kernel)

private def p988899889 := certifiedPrime 988899889 7 [(p2,4),(p3,1),(p37,2),(p101,1),(p149,1)] (by decide +kernel)

private def p989899997 := certifiedPrime 989899997 2 [(p2,2),(p247474999,1)] (by decide +kernel)

private def p998999999 := certifiedPrime 998999999 7 [(p2,1),(p499499999,1)] (by decide +kernel)

private def p999299999 := certifiedPrime 999299999 11 [(p2,1),(p23,1),(p21723913,1)] (by decide +kernel)

private def p999499999 := certifiedPrime 999499999 15 [(p2,1),(p3,1),(p7,1),(p43,1),(p553433,1)] (by decide +kernel)

private def p999889981 := certifiedPrime 999889981 6 [(p2,2),(p3,1),(p5,1),(p16664833,1)] (by decide +kernel)

private def p999895999 := certifiedPrime 999895999 3 [(p2,1),(p3,1),(p166649333,1)] (by decide +kernel)

private def p999997793 := certifiedPrime 999997793 3 [(p2,5),(p31249931,1)] (by decide +kernel)

private def p999998981 := certifiedPrime 999998981 2 [(p2,2),(p5,1),(p101,1),(p131,1),(p3779,1)] (by decide +kernel)

private def p999999391 := certifiedPrime 999999391 3 [(p2,1),(p3,1),(p5,1),(p13,1),(p2564101,1)] (by decide +kernel)

private def p999999599 := certifiedPrime 999999599 7 [(p2,1),(p13,1),(p5281,1),(p7283,1)] (by decide +kernel)

private def p1124999999 := certifiedPrime 1124999999 7 [(p2,1),(p761,1),(p839,1),(p881,1)] (by decide +kernel)

private def p1211695747 := certifiedPrime 1211695747 2 [(p2,1),(p3,1),(p9067,1),(p22273,1)] (by decide +kernel)

private def p1216025641 := certifiedPrime 1216025641 7 [(p2,3),(p3,2),(p5,1),(p17,1),(p23,1),(p53,1),(p163,1)] (by decide +kernel)

private def p1249724999 := certifiedPrime 1249724999 23 [(p2,1),(p181,1),(p3452279,1)] (by decide +kernel)

private def p1256424581 := certifiedPrime 1256424581 2 [(p2,2),(p5,1),(p241,1),(p463,1),(p563,1)] (by decide +kernel)

private def p1272845953 := certifiedPrime 1272845953 5 [(p2,7),(p3,2),(p7,2),(p22549,1)] (by decide +kernel)

private def p1324102649 := certifiedPrime 1324102649 3 [(p2,3),(p11,1),(p29,1),(p211,1),(p2459,1)] (by decide +kernel)

private def p1324137931 := certifiedPrime 1324137931 3 [(p2,1),(p3,1),(p5,1),(p19,1),(p71,1),(p32719,1)] (by decide +kernel)

private def p1374859583 := certifiedPrime 1374859583 5 [(p2,1),(p127,1),(p1327,1),(p4079,1)] (by decide +kernel)

private def p1515342931 := certifiedPrime 1515342931 3 [(p2,1),(p3,1),(p5,1),(p31,1),(p241,1),(p6761,1)] (by decide +kernel)

private def p1607142857 := certifiedPrime 1607142857 3 [(p2,3),(p11,1),(p487,1),(p37501,1)] (by decide +kernel)

private def p1699999997 := certifiedPrime 1699999997 2 [(p2,2),(p19,1),(p22368421,1)] (by decide +kernel)

private def p1894999999 := certifiedPrime 1894999999 3 [(p2,1),(p3,1),(p19,1),(p16622807,1)] (by decide +kernel)

private def p1896898967 := certifiedPrime 1896898967 5 [(p2,1),(p948449483,1)] (by decide +kernel)

private def p1976889899 := certifiedPrime 1976889899 2 [(p2,1),(p233,1),(p4242253,1)] (by decide +kernel)

private def p1978999999 := certifiedPrime 1978999999 3 [(p2,1),(p3,1),(p193,1),(p1708981,1)] (by decide +kernel)

private def p1989899987 := certifiedPrime 1989899987 2 [(p2,1),(p41,1),(p24267073,1)] (by decide +kernel)

private def p2178304787 := certifiedPrime 2178304787 5 [(p2,1),(p7,1),(p155593199,1)] (by decide +kernel)

private def p2213547619 := certifiedPrime 2213547619 10 [(p2,1),(p3,1),(p6871,1),(p53693,1)] (by decide +kernel)

private def p2249724739 := certifiedPrime 2249724739 2 [(p2,1),(p3,1),(p374954123,1)] (by decide +kernel)

private def p2269047619 := certifiedPrime 2269047619 2 [(p2,1),(p3,2),(p101,1),(p1248101,1)] (by decide +kernel)

private def p2311320283 := certifiedPrime 2311320283 2 [(p2,1),(p3,1),(p6229,1),(p61843,1)] (by decide +kernel)

private def p2474247499 := certifiedPrime 2474247499 3 [(p2,1),(p3,1),(p37,1),(p11145259,1)] (by decide +kernel)

private def p2527805921 := certifiedPrime 2527805921 12 [(p2,5),(p5,1),(p109,1),(p193,1),(p751,1)] (by decide +kernel)

private def p2533333333 := certifiedPrime 2533333333 5 [(p2,2),(p3,1),(p1033,1),(p204367,1)] (by decide +kernel)

private def p2595673807 := certifiedPrime 2595673807 3 [(p2,1),(p3,1),(p11,1),(p71,1),(p553921,1)] (by decide +kernel)

private def p2648690467 := certifiedPrime 2648690467 2 [(p2,1),(p3,1),(p29,1),(p331,1),(p45989,1)] (by decide +kernel)

private def p2685481129 := certifiedPrime 2685481129 13 [(p2,3),(p3,4),(p11,1),(p19,1),(p79,1),(p251,1)] (by decide +kernel)

private def p2912050201 := certifiedPrime 2912050201 13 [(p2,3),(p3,1),(p5,2),(p19,1),(p255443,1)] (by decide +kernel)

private def p3181817713 := certifiedPrime 3181817713 5 [(p2,4),(p3,1),(p73,1),(p908053,1)] (by decide +kernel)

private def p3299333333 := certifiedPrime 3299333333 2 [(p2,2),(p83,1),(p9937751,1)] (by decide +kernel)

private def p3463160357 := certifiedPrime 3463160357 2 [(p2,2),(p865790089,1)] (by decide +kernel)

private def p3571428467 := certifiedPrime 3571428467 2 [(p2,1),(p2063,1),(p865591,1)] (by decide +kernel)

private def p3650793613 := certifiedPrime 3650793613 7 [(p2,2),(p3,1),(p461,1),(p659941,1)] (by decide +kernel)

private def p3679999997 := certifiedPrime 3679999997 2 [(p2,2),(p17,2),(p3183391,1)] (by decide +kernel)

private def p3824999999 := certifiedPrime 3824999999 7 [(p2,1),(p61,1),(p191,1),(p164149,1)] (by decide +kernel)

private def p3879999889 := certifiedPrime 3879999889 7 [(p2,4),(p3,1),(p2029,1),(p39839,1)] (by decide +kernel)

private def p3898999889 := certifiedPrime 3898999889 3 [(p2,4),(p7,1),(p29,1),(p43,1),(p27917,1)] (by decide +kernel)

private def p4201208981 := certifiedPrime 4201208981 2 [(p2,2),(p5,1),(p17,1),(p23,1),(p167,1),(p3217,1)] (by decide +kernel)

private def p4215260017 := certifiedPrime 4215260017 5 [(p2,4),(p3,2),(p11,1),(p389,1),(p6841,1)] (by decide +kernel)

private def p4504090909 := certifiedPrime 4504090909 6 [(p2,2),(p3,1),(p17,1),(p859,1),(p25703,1)] (by decide +kernel)

private def p4560515873 := certifiedPrime 4560515873 3 [(p2,5),(p11,1),(p29,1),(p446759,1)] (by decide +kernel)

private def p4689899999 := certifiedPrime 4689899999 7 [(p2,1),(p7,1),(p19,1),(p37,1),(p476519,1)] (by decide +kernel)

private def p4730128141 := certifiedPrime 4730128141 2 [(p2,2),(p3,1),(p5,1),(p43,1),(p1833383,1)] (by decide +kernel)

private def p4799999993 := certifiedPrime 4799999993 3 [(p2,3),(p97,1),(p6185567,1)] (by decide +kernel)

private def p4799999999 := certifiedPrime 4799999999 7 [(p2,1),(p239,1),(p2309,1),(p4349,1)] (by decide +kernel)

private def p4996999999 := certifiedPrime 4996999999 3 [(p2,1),(p3,5),(p37,1),(p277889,1)] (by decide +kernel)

private def p5071377551 := certifiedPrime 5071377551 7 [(p2,1),(p5,2),(p47,1),(p2158033,1)] (by decide +kernel)

private def p5152173913 := certifiedPrime 5152173913 5 [(p2,3),(p3,3),(p19,1),(p1063,1),(p1181,1)] (by decide +kernel)

private def p5299988999 := certifiedPrime 5299988999 7 [(p2,1),(p59,1),(p2719,1),(p16519,1)] (by decide +kernel)

private def p5524471993 := certifiedPrime 5524471993 5 [(p2,3),(p3,1),(p13,1),(p1627,1),(p10883,1)] (by decide +kernel)

private def p5789898889 := certifiedPrime 5789898889 13 [(p2,3),(p3,1),(p409,1),(p571,1),(p1033,1)] (by decide +kernel)

private def p5799999991 := certifiedPrime 5799999991 3 [(p2,1),(p3,1),(p5,1),(p17,1),(p241,1),(p47189,1)] (by decide +kernel)

private def p5872147651 := certifiedPrime 5872147651 3 [(p2,1),(p3,4),(p5,2),(p17,2),(p29,1),(p173,1)] (by decide +kernel)

private def p5899889999 := certifiedPrime 5899889999 11 [(p2,1),(p3847,1),(p766817,1)] (by decide +kernel)

private def p5916547619 := certifiedPrime 5916547619 2 [(p2,1),(p7349,1),(p402541,1)] (by decide +kernel)

private def p5989999999 := certifiedPrime 5989999999 3 [(p2,1),(p3,1),(p293,1),(p3407281,1)] (by decide +kernel)

private def p6699898999 := certifiedPrime 6699898999 17 [(p2,1),(p3,2),(p13,1),(p28632047,1)] (by decide +kernel)

private def p6730758547 := certifiedPrime 6730758547 2 [(p2,1),(p3,1),(p7109,1),(p157799,1)] (by decide +kernel)

private def p6968489999 := certifiedPrime 6968489999 7 [(p2,1),(p23,1),(p1973,1),(p76781,1)] (by decide +kernel)

private def p6978989993 := certifiedPrime 6978989993 3 [(p2,3),(p13,1),(p61,1),(p1100093,1)] (by decide +kernel)

private def p6988998889 := certifiedPrime 6988998889 13 [(p2,3),(p3,2),(p47,1),(p571,1),(p3617,1)] (by decide +kernel)

private def p6997999997 := certifiedPrime 6997999997 2 [(p2,2),(p13,2),(p1873,1),(p5527,1)] (by decide +kernel)

private def p6998499997 := certifiedPrime 6998499997 2 [(p2,2),(p3,1),(p59,1),(p9884887,1)] (by decide +kernel)

private def p6999995999 := certifiedPrime 6999995999 19 [(p2,1),(p19,1),(p184210421,1)] (by decide +kernel)

private def p7199999999 := certifiedPrime 7199999999 11 [(p2,1),(p29,1),(p2069,1),(p59999,1)] (by decide +kernel)

private def p7305782881 := certifiedPrime 7305782881 17 [(p2,5),(p3,1),(p5,1),(p11,1),(p53,1),(p26107,1)] (by decide +kernel)

private def p7399999991 := certifiedPrime 7399999991 13 [(p2,1),(p5,1),(p23,1),(p139,1),(p211,1),(p1097,1)] (by decide +kernel)

private def p7579999997 := certifiedPrime 7579999997 2 [(p2,2),(p1894999999,1)] (by decide +kernel)

private def p7649999999 := certifiedPrime 7649999999 11 [(p2,1),(p3824999999,1)] (by decide +kernel)

private def p7899399997 := certifiedPrime 7899399997 2 [(p2,2),(p3,1),(p17,2),(p2277797,1)] (by decide +kernel)

private def p7979999999 := certifiedPrime 7979999999 11 [(p2,1),(p47,1),(p84893617,1)] (by decide +kernel)

private def p7998888889 := certifiedPrime 7998888889 7 [(p2,3),(p3,3),(p19,1),(p733,1),(p2659,1)] (by decide +kernel)

private def p7999699999 := certifiedPrime 7999699999 3 [(p2,1),(p3,1),(p19,1),(p97,1),(p457,1),(p1583,1)] (by decide +kernel)

private def p7999797997 := certifiedPrime 7999797997 2 [(p2,2),(p3,2),(p47,1),(p4728013,1)] (by decide +kernel)

private def p8113286479 := certifiedPrime 8113286479 6 [(p2,1),(p3,1),(p11,1),(p23,1),(p1531,1),(p3491,1)] (by decide +kernel)

private def p8166583333 := certifiedPrime 8166583333 5 [(p2,2),(p3,2),(p31,1),(p173,1),(p42299,1)] (by decide +kernel)

private def p8216655833 := certifiedPrime 8216655833 3 [(p2,3),(p7,1),(p11,1),(p17,1),(p107,1),(p7333,1)] (by decide +kernel)

private def p8299799999 := certifiedPrime 8299799999 17 [(p2,1),(p7,1),(p592842857,1)] (by decide +kernel)

private def p8489999897 := certifiedPrime 8489999897 3 [(p2,3),(p7,2),(p21658163,1)] (by decide +kernel)

private def p8789959999 := certifiedPrime 8789959999 6 [(p2,1),(p3,3),(p162777037,1)] (by decide +kernel)

private def p8799959891 := certifiedPrime 8799959891 2 [(p2,1),(p5,1),(p43,1),(p593,1),(p34511,1)] (by decide +kernel)

private def p8799999997 := certifiedPrime 8799999997 11 [(p2,2),(p3,1),(p173,1),(p1559,1),(p2719,1)] (by decide +kernel)

private def p8839799999 := certifiedPrime 8839799999 7 [(p2,1),(p41,1),(p1249,1),(p86311,1)] (by decide +kernel)

private def p8866999991 := certifiedPrime 8866999991 11 [(p2,1),(p5,1),(p19,1),(p46668421,1)] (by decide +kernel)

private def p8889999991 := certifiedPrime 8889999991 11 [(p2,1),(p3,1),(p5,1),(p37,1),(p8009009,1)] (by decide +kernel)

private def p8894999999 := certifiedPrime 8894999999 7 [(p2,1),(p17,1),(p67,1),(p3904741,1)] (by decide +kernel)

private def p8898799999 := certifiedPrime 8898799999 3 [(p2,1),(p3,1),(p11,1),(p134830303,1)] (by decide +kernel)

private def p8898994999 := certifiedPrime 8898994999 3 [(p2,1),(p3,2),(p17,1),(p23,1),(p53,1),(p23857,1)] (by decide +kernel)

private def p8899699999 := certifiedPrime 8899699999 3 [(p2,1),(p3,1),(p7,1),(p211897619,1)] (by decide +kernel)

private def p8949999997 := certifiedPrime 8949999997 2 [(p2,2),(p3,2),(p7,1),(p17,1),(p2089169,1)] (by decide +kernel)

private def p8969899993 := certifiedPrime 8969899993 5 [(p2,3),(p3,1),(p17,1),(p47,1),(p167,1),(p2801,1)] (by decide +kernel)

private def p8988889997 := certifiedPrime 8988889997 5 [(p2,2),(p29,1),(p89,1),(p870679,1)] (by decide +kernel)

private def p8998898957 := certifiedPrime 8998898957 2 [(p2,2),(p2249724739,1)] (by decide +kernel)

private def p8998998889 := certifiedPrime 8998998889 7 [(p2,3),(p3,1),(p11,1),(p131,1),(p260207,1)] (by decide +kernel)

private def p8999899889 := certifiedPrime 8999899889 3 [(p2,4),(p7,1),(p67,1),(p751,1),(p1597,1)] (by decide +kernel)

private def p8999969999 := certifiedPrime 8999969999 11 [(p2,1),(p179,1),(p419,1),(p59999,1)] (by decide +kernel)

private def p8999999993 := certifiedPrime 8999999993 3 [(p2,3),(p1124999999,1)] (by decide +kernel)

private def p9159999991 := certifiedPrime 9159999991 3 [(p2,1),(p3,1),(p5,1),(p149,1),(p587,1),(p3491,1)] (by decide +kernel)

private def p9194204441 := certifiedPrime 9194204441 3 [(p2,3),(p5,1),(p31,1),(p7414681,1)] (by decide +kernel)

private def p9199999999 := certifiedPrime 9199999999 3 [(p2,1),(p3,2),(p7,2),(p10430839,1)] (by decide +kernel)

private def p9279999997 := certifiedPrime 9279999997 2 [(p2,2),(p3,1),(p773333333,1)] (by decide +kernel)

private def p9289699999 := certifiedPrime 9289699999 3 [(p2,1),(p3,1),(p311,1),(p4978403,1)] (by decide +kernel)

private def p9298999999 := certifiedPrime 9298999999 6 [(p2,1),(p3,2),(p41,1),(p12600271,1)] (by decide +kernel)

private def p9438899999 := certifiedPrime 9438899999 7 [(p2,1),(p11,2),(p2089,1),(p18671,1)] (by decide +kernel)

private def p9589979999 := certifiedPrime 9589979999 13 [(p2,1),(p137,1),(p34999927,1)] (by decide +kernel)

private def p9629035313 := certifiedPrime 9629035313 3 [(p2,4),(p13,1),(p89,1),(p520151,1)] (by decide +kernel)

private def p9685999997 := certifiedPrime 9685999997 2 [(p2,2),(p1249,1),(p1938751,1)] (by decide +kernel)

private def p9687999991 := certifiedPrime 9687999991 12 [(p2,1),(p3,1),(p5,1),(p322933333,1)] (by decide +kernel)

private def p9799939999 := certifiedPrime 9799939999 3 [(p2,1),(p3,2),(p544441111,1)] (by decide +kernel)

private def p9799977991 := certifiedPrime 9799977991 3 [(p2,1),(p3,1),(p5,1),(p11,1),(p37,1),(p47,1),(p17077,1)] (by decide +kernel)

private def p9879799991 := certifiedPrime 9879799991 17 [(p2,1),(p5,1),(p647,1),(p1527017,1)] (by decide +kernel)

private def p9889888889 := certifiedPrime 9889888889 3 [(p2,3),(p11,1),(p43,1),(p2613607,1)] (by decide +kernel)

private def p9896989997 := certifiedPrime 9896989997 2 [(p2,2),(p2474247499,1)] (by decide +kernel)

private def p9898488997 := certifiedPrime 9898488997 5 [(p2,2),(p3,1),(p11,1),(p74988553,1)] (by decide +kernel)

private def p9898490099 := certifiedPrime 9898490099 2 [(p2,1),(p7,2),(p101005001,1)] (by decide +kernel)

private def p9898999993 := certifiedPrime 9898999993 5 [(p2,3),(p3,2),(p7,2),(p23,1),(p121993,1)] (by decide +kernel)

private def p9952999999 := certifiedPrime 9952999999 17 [(p2,1),(p3,1),(p113,1),(p1009,1),(p14549,1)] (by decide +kernel)

private def p9956899999 := certifiedPrime 9956899999 15 [(p2,1),(p3,3),(p184387037,1)] (by decide +kernel)

private def p9958979993 := certifiedPrime 9958979993 3 [(p2,3),(p13,1),(p5347,1),(p17909,1)] (by decide +kernel)

private def p9959999999 := certifiedPrime 9959999999 11 [(p2,1),(p13,1),(p2579,1),(p148537,1)] (by decide +kernel)

private def p9978898987 := certifiedPrime 9978898987 22 [(p2,1),(p3,2),(p7,1),(p17,1),(p1433,1),(p3251,1)] (by decide +kernel)

private def p9979599997 := certifiedPrime 9979599997 2 [(p2,2),(p3,2),(p23,1),(p193,1),(p197,1),(p317,1)] (by decide +kernel)

private def p9988999799 := certifiedPrime 9988999799 7 [(p2,1),(p71,1),(p523,1),(p134503,1)] (by decide +kernel)

private def p9989899999 := certifiedPrime 9989899999 3 [(p2,1),(p3,1),(p13,1),(p569,1),(p225089,1)] (by decide +kernel)

private def p9997799993 := certifiedPrime 9997799993 3 [(p2,3),(p1249724999,1)] (by decide +kernel)

private def p9999499999 := certifiedPrime 9999499999 3 [(p2,1),(p3,1),(p367,1),(p4541099,1)] (by decide +kernel)

private def p9999842857 := certifiedPrime 9999842857 10 [(p2,3),(p3,1),(p31,1),(p1531,1),(p8779,1)] (by decide +kernel)

private def p9999996991 := certifiedPrime 9999996991 3 [(p2,1),(p3,1),(p5,1),(p269,1),(p587,1),(p2111,1)] (by decide +kernel)

private def p10183299389 := certifiedPrime 10183299389 2 [(p2,2),(p43,1),(p3041,1),(p19469,1)] (by decide +kernel)

private def p10594761869 := certifiedPrime 10594761869 2 [(p2,2),(p2648690467,1)] (by decide +kernel)

private def p10911360799 := certifiedPrime 10911360799 3 [(p2,1),(p3,4),(p13,1),(p71,1),(p72973,1)] (by decide +kernel)

private def p11001111101 := certifiedPrime 11001111101 2 [(p2,2),(p5,2),(p7,1),(p15715873,1)] (by decide +kernel)

private def p11623747361 := certifiedPrime 11623747361 3 [(p2,5),(p5,1),(p23,1),(p937,1),(p3371,1)] (by decide +kernel)

private def p11633333333 := certifiedPrime 11633333333 2 [(p2,2),(p42463,1),(p68491,1)] (by decide +kernel)

private def p12513466379 := certifiedPrime 12513466379 2 [(p2,1),(p7,1),(p37,1),(p43,1),(p561797,1)] (by decide +kernel)

private def p14383283333 := certifiedPrime 14383283333 2 [(p2,2),(p11,1),(p151,1),(p2164853,1)] (by decide +kernel)

private def p15499137931 := certifiedPrime 15499137931 3 [(p2,1),(p3,1),(p5,1),(p131,1),(p211,1),(p18691,1)] (by decide +kernel)

private def p16498314997 := certifiedPrime 16498314997 2 [(p2,2),(p3,1),(p1374859583,1)] (by decide +kernel)

private def p16999999999 := certifiedPrime 16999999999 11 [(p2,1),(p3,1),(p19,1),(p149122807,1)] (by decide +kernel)

private def p17333333333 := certifiedPrime 17333333333 2 [(p2,2),(p7,1),(p619047619,1)] (by decide +kernel)

private def p18989999999 := certifiedPrime 18989999999 11 [(p2,1),(p157,1),(p60477707,1)] (by decide +kernel)

private def p19482499999 := certifiedPrime 19482499999 3 [(p2,1),(p3,3),(p13,1),(p37,1),(p750077,1)] (by decide +kernel)

private def p19899998999 := certifiedPrime 19899998999 11 [(p2,1),(p11,1),(p29,1),(p47,1),(p73,1),(p9091,1)] (by decide +kernel)

private def p22216111111 := certifiedPrime 22216111111 3 [(p2,1),(p3,3),(p5,1),(p82281893,1)] (by decide +kernel)

private def p23333333333 := certifiedPrime 23333333333 2 [(p2,2),(p31,1),(p617,1),(p304979,1)] (by decide +kernel)

private def p24169052213 := certifiedPrime 24169052213 2 [(p2,2),(p2593,1),(p2330221,1)] (by decide +kernel)

private def p24802259887 := certifiedPrime 24802259887 3 [(p2,1),(p3,3),(p459301109,1)] (by decide +kernel)

private def p24989999999 := certifiedPrime 24989999999 19 [(p2,1),(p59,1),(p13879,1),(p15259,1)] (by decide +kernel)

private def p26041640591 := certifiedPrime 26041640591 7 [(p2,1),(p5,1),(p7,1),(p4993,1),(p74509,1)] (by decide +kernel)

private def p27161111111 := certifiedPrime 27161111111 7 [(p2,1),(p5,1),(p7,2),(p55430839,1)] (by decide +kernel)

private def p27304964539 := certifiedPrime 27304964539 2 [(p2,1),(p3,1),(p461,1),(p2203,1),(p4481,1)] (by decide +kernel)

private def p27611111111 := certifiedPrime 27611111111 11 [(p2,1),(p5,1),(p11,1),(p97,1),(p257,1),(p10069,1)] (by decide +kernel)

private def p32453145917 := certifiedPrime 32453145917 2 [(p2,2),(p8113286479,1)] (by decide +kernel)

private def p38333333333 := certifiedPrime 38333333333 2 [(p2,2),(p7,1),(p37,1),(p181,1),(p204427,1)] (by decide +kernel)

private def p38611111111 := certifiedPrime 38611111111 11 [(p2,1),(p3,1),(p5,1),(p11,1),(p13,1),(p17,1),(p337,1),(p1571,1)] (by decide +kernel)

private def p38699899999 := certifiedPrime 38699899999 13 [(p2,1),(p3,1),(p19,1),(p339472807,1)] (by decide +kernel)

private def p38849999999 := certifiedPrime 38849999999 17 [(p2,1),(p19,1),(p103,1),(p9925907,1)] (by decide +kernel)

private def p38998988999 := certifiedPrime 38998988999 11 [(p2,1),(p73,1),(p229,1),(p277,1),(p4211,1)] (by decide +kernel)

private def p39796999997 := certifiedPrime 39796999997 2 [(p2,2),(p13,1),(p61,1),(p12546343,1)] (by decide +kernel)

private def p39799997999 := certifiedPrime 39799997999 11 [(p2,1),(p19899998999,1)] (by decide +kernel)

private def p39979988887 := certifiedPrime 39979988887 3 [(p2,1),(p3,1),(p269,1),(p24770749,1)] (by decide +kernel)

private def p41200996201 := certifiedPrime 41200996201 22 [(p2,3),(p3,1),(p5,2),(p7,1),(p13,1),(p754597,1)] (by decide +kernel)

private def p43382352941 := certifiedPrime 43382352941 2 [(p2,2),(p5,1),(p31,1),(p991,1),(p70607,1)] (by decide +kernel)

private def p47898888889 := certifiedPrime 47898888889 7 [(p2,3),(p3,1),(p19,1),(p31,1),(p3388433,1)] (by decide +kernel)

private def p48484244999 := certifiedPrime 48484244999 7 [(p2,1),(p7,1),(p3463160357,1)] (by decide +kernel)

private def p48959900989 := certifiedPrime 48959900989 2 [(p2,2),(p3,1),(p4483,1),(p910103,1)] (by decide +kernel)

private def p49449449999 := certifiedPrime 49449449999 11 [(p2,1),(p13,1),(p73,1),(p83,1),(p313897,1)] (by decide +kernel)

private def p49999899889 := certifiedPrime 49999899889 23 [(p2,4),(p3,3),(p107,1),(p1081687,1)] (by decide +kernel)

private def p49999988999 := certifiedPrime 49999988999 7 [(p2,1),(p37,1),(p83,1),(p8140669,1)] (by decide +kernel)

private def p56998999997 := certifiedPrime 56998999997 2 [(p2,2),(p61,1),(p233602459,1)] (by decide +kernel)

private def p59989998997 := certifiedPrime 59989998997 2 [(p2,2),(p3,2),(p59,1),(p28243879,1)] (by decide +kernel)

private def p59999999999 := certifiedPrime 59999999999 7 [(p2,1),(p2113,1),(p3767,1),(p3769,1)] (by decide +kernel)

private def p62848999979 := certifiedPrime 62848999979 2 [(p2,1),(p509,1),(p7621,1),(p8101,1)] (by decide +kernel)

private def p65999999999 := certifiedPrime 65999999999 13 [(p2,1),(p31,1),(p16487,1),(p64567,1)] (by decide +kernel)

private def p66199999997 := certifiedPrime 66199999997 2 [(p2,2),(p13,1),(p151,1),(p2267,1),(p3719,1)] (by decide +kernel)

private def p67899999991 := certifiedPrime 67899999991 12 [(p2,1),(p3,1),(p5,1),(p19,1),(p29,1),(p4107683,1)] (by decide +kernel)

private def p68949899999 := certifiedPrime 68949899999 7 [(p2,1),(p7,1),(p41,1),(p120121777,1)] (by decide +kernel)

private def p68969999999 := certifiedPrime 68969999999 23 [(p2,1),(p29,1),(p37,1),(p263,1),(p122201,1)] (by decide +kernel)

private def p69799999999 := certifiedPrime 69799999999 3 [(p2,1),(p3,1),(p11633333333,1)] (by decide +kernel)

private def p69999989687 := certifiedPrime 69999989687 5 [(p2,1),(p11,1),(p3181817713,1)] (by decide +kernel)

private def p70284057971 := certifiedPrime 70284057971 2 [(p2,1),(p5,1),(p7,3),(p20490979,1)] (by decide +kernel)

private def p70999999999 := certifiedPrime 70999999999 3 [(p2,1),(p3,1),(p29,1),(p2011,1),(p202907,1)] (by decide +kernel)

private def p71999999999 := certifiedPrime 71999999999 7 [(p2,1),(p53,1),(p281,1),(p2417243,1)] (by decide +kernel)

private def p72799999999 := certifiedPrime 72799999999 6 [(p2,1),(p3,1),(p11,1),(p1873,1),(p588911,1)] (by decide +kernel)

private def p73999999993 := certifiedPrime 73999999993 5 [(p2,3),(p3,1),(p17,1),(p23,1),(p59,1),(p133657,1)] (by decide +kernel)

private def p74898999899 := certifiedPrime 74898999899 2 [(p2,1),(p293,1),(p4937,1),(p25889,1)] (by decide +kernel)

private def p75969999997 := certifiedPrime 75969999997 2 [(p2,2),(p3,1),(p11,1),(p61,1),(p9434923,1)] (by decide +kernel)

private def p75999999991 := certifiedPrime 75999999991 6 [(p2,1),(p3,1),(p5,1),(p2533333333,1)] (by decide +kernel)

private def p76799999999 := certifiedPrime 76799999999 7 [(p2,1),(p29,1),(p1324137931,1)] (by decide +kernel)

private def p76823076923 := certifiedPrime 76823076923 2 [(p2,1),(p19,1),(p29,1),(p69712411,1)] (by decide +kernel)

private def p77929999997 := certifiedPrime 77929999997 2 [(p2,2),(p19482499999,1)] (by decide +kernel)

private def p77979999997 := certifiedPrime 77979999997 2 [(p2,2),(p3,3),(p43,1),(p109,1),(p127,1),(p1213,1)] (by decide +kernel)

private def p77988999997 := certifiedPrime 77988999997 2 [(p2,2),(p3,2),(p3673,1),(p589807,1)] (by decide +kernel)

private def p79579999997 := certifiedPrime 79579999997 2 [(p2,2),(p7,1),(p131,1),(p21695747,1)] (by decide +kernel)

private def p79999999993 := certifiedPrime 79999999993 10 [(p2,3),(p3,2),(p11,1),(p41,1),(p271,1),(p9091,1)] (by decide +kernel)

private def p79999999999 := certifiedPrime 79999999999 6 [(p2,1),(p3,1),(p163,1),(p409,1),(p199999,1)] (by decide +kernel)

private def p83898999997 := certifiedPrime 83898999997 2 [(p2,2),(p3,1),(p7,1),(p2297,1),(p434827,1)] (by decide +kernel)

private def p86299699999 := certifiedPrime 86299699999 3 [(p2,1),(p3,1),(p14383283333,1)] (by decide +kernel)

private def p86995999999 := certifiedPrime 86995999999 6 [(p2,1),(p3,3),(p19,1),(p127,1),(p667649,1)] (by decide +kernel)

private def p87489999997 := certifiedPrime 87489999997 2 [(p2,2),(p3,1),(p7,2),(p17,2),(p514853,1)] (by decide +kernel)

private def p87889889999 := certifiedPrime 87889889999 7 [(p2,1),(p29,1),(p1515342931,1)] (by decide +kernel)

private def p89898888883 := certifiedPrime 89898888883 2 [(p2,1),(p3,1),(p11,1),(p21683,1),(p62819,1)] (by decide +kernel)

private def p89959999999 := certifiedPrime 89959999999 3 [(p2,1),(p3,1),(p11,1),(p19,1),(p2069,1),(p34673,1)] (by decide +kernel)

private def p89988789997 := certifiedPrime 89988789997 5 [(p2,2),(p3,4),(p7,1),(p29,1),(p881,1),(p1553,1)] (by decide +kernel)

private def p89999999993 := certifiedPrime 89999999993 3 [(p2,3),(p7,1),(p1607142857,1)] (by decide +kernel)

private def p92968999999 := certifiedPrime 92968999999 3 [(p2,1),(p3,1),(p7,1),(p2213547619,1)] (by decide +kernel)

private def p92989978889 := certifiedPrime 92989978889 3 [(p2,3),(p11623747361,1)] (by decide +kernel)

private def p93499999997 := certifiedPrime 93499999997 2 [(p2,2),(p13,1),(p67,1),(p26836969,1)] (by decide +kernel)

private def p93896899997 := certifiedPrime 93896899997 2 [(p2,2),(p59707,1),(p393157,1)] (by decide +kernel)

private def p95299999999 := certifiedPrime 95299999999 3 [(p2,1),(p3,1),(p7,1),(p2269047619,1)] (by decide +kernel)

private def p95997799999 := certifiedPrime 95997799999 3 [(p2,1),(p3,3),(p3943,1),(p450859,1)] (by decide +kernel)

private def p95999994997 := certifiedPrime 95999994997 2 [(p2,2),(p3,1),(p3511,1),(p2278553,1)] (by decide +kernel)

private def p96056624999 := certifiedPrime 96056624999 11 [(p2,1),(p19,1),(p2527805921,1)] (by decide +kernel)

private def p96499999997 := certifiedPrime 96499999997 2 [(p2,2),(p17,1),(p37,1),(p38354531,1)] (by decide +kernel)

private def p96968489999 := certifiedPrime 96968489999 41 [(p2,1),(p48484244999,1)] (by decide +kernel)

private def p96988999997 := certifiedPrime 96988999997 3 [(p2,2),(p7,1),(p53,1),(p65356469,1)] (by decide +kernel)

private def p96998989999 := certifiedPrime 96998989999 3 [(p2,1),(p3,1),(p2213,1),(p7305241,1)] (by decide +kernel)

private def p97899989899 := certifiedPrime 97899989899 2 [(p2,1),(p3,1),(p22433,1),(p727351,1)] (by decide +kernel)

private def p97938899999 := certifiedPrime 97938899999 13 [(p2,1),(p257,1),(p1609,1),(p118423,1)] (by decide +kernel)

private def p97998999997 := certifiedPrime 97998999997 2 [(p2,2),(p3,1),(p8166583333,1)] (by decide +kernel)

private def p97999799999 := certifiedPrime 97999799999 17 [(p2,1),(p151,1),(p324502649,1)] (by decide +kernel)

private def p98589889999 := certifiedPrime 98589889999 3 [(p2,1),(p3,2),(p17,1),(p47,1),(p6855089,1)] (by decide +kernel)

private def p98599869997 := certifiedPrime 98599869997 2 [(p2,2),(p3,1),(p8216655833,1)] (by decide +kernel)

private def p98677999999 := certifiedPrime 98677999999 6 [(p2,1),(p3,2),(p23,2),(p683,1),(p15173,1)] (by decide +kernel)

private def p98699999999 := certifiedPrime 98699999999 19 [(p2,1),(p19,1),(p463,1),(p5609867,1)] (by decide +kernel)

private def p98898899999 := certifiedPrime 98898899999 7 [(p2,1),(p49449449999,1)] (by decide +kernel)

private def p98899999997 := certifiedPrime 98899999997 2 [(p2,2),(p7,1),(p38461,1),(p91837,1)] (by decide +kernel)

private def p98899999999 := certifiedPrime 98899999999 3 [(p2,1),(p3,1),(p2417,1),(p6819749,1)] (by decide +kernel)

private def p98979999991 := certifiedPrime 98979999991 6 [(p2,1),(p3,1),(p5,1),(p3299333333,1)] (by decide +kernel)

private def p98989889983 := certifiedPrime 98989889983 3 [(p2,1),(p3,1),(p16498314997,1)] (by decide +kernel)

private def p98989989991 := certifiedPrime 98989989991 7 [(p2,1),(p3,1),(p5,1),(p13789,1),(p239297,1)] (by decide +kernel)

private def p98989999993 := certifiedPrime 98989999993 7 [(p2,3),(p3,3),(p13,1),(p17,1),(p71,1),(p29207,1)] (by decide +kernel)

private def p98998988887 := certifiedPrime 98998988887 7 [(p2,1),(p3,3),(p7,1),(p261902087,1)] (by decide +kernel)

private def p98999999999 := certifiedPrime 98999999999 17 [(p2,1),(p23,1),(p673,1),(p3197881,1)] (by decide +kernel)

private def p99089999999 := certifiedPrime 99089999999 7 [(p2,1),(p11,1),(p4504090909,1)] (by decide +kernel)

private def p99289999999 := certifiedPrime 99289999999 3 [(p2,1),(p3,2),(p7,1),(p61,1),(p12918293,1)] (by decide +kernel)

private def p99496999999 := certifiedPrime 99496999999 3 [(p2,1),(p3,3),(p11,1),(p179,1),(p631,1),(p1483,1)] (by decide +kernel)

private def p99499999999 := certifiedPrime 99499999999 3 [(p2,1),(p3,1),(p7,1),(p283,1),(p8371193,1)] (by decide +kernel)

private def p99579899999 := certifiedPrime 99579899999 13 [(p2,1),(p3343,1),(p14893793,1)] (by decide +kernel)

private def p99899988889 := certifiedPrime 99899988889 11 [(p2,3),(p3,1),(p7,1),(p19,1),(p31296989,1)] (by decide +kernel)

private def p99988888889 := certifiedPrime 99988888889 3 [(p2,3),(p7,1),(p173,1),(p2549,1),(p4049,1)] (by decide +kernel)

private def p99999199999 := certifiedPrime 99999199999 3 [(p2,1),(p3,3),(p41,1),(p271,1),(p166667,1)] (by decide +kernel)

private def p99999999947 := certifiedPrime 99999999947 2 [(p2,1),(p7,1),(p11,1),(p17,1),(p5527,1),(p6911,1)] (by decide +kernel)

private def p105258981203 := certifiedPrime 105258981203 2 [(p2,1),(p71,1),(p741260431,1)] (by decide +kernel)

private def p112362487499 := certifiedPrime 112362487499 2 [(p2,1),(p60037,1),(p935777,1)] (by decide +kernel)

private def p124260651629 := certifiedPrime 124260651629 2 [(p2,2),(p43,1),(p6229,1),(p115981,1)] (by decide +kernel)

private def p134999999999 := certifiedPrime 134999999999 7 [(p2,1),(p431,1),(p457,1),(p342697,1)] (by decide +kernel)

private def p138246812749 := certifiedPrime 138246812749 6 [(p2,2),(p3,3),(p11,1),(p116369371,1)] (by decide +kernel)

private def p149816498333 := certifiedPrime 149816498333 2 [(p2,2),(p17,2),(p4483,1),(p28909,1)] (by decide +kernel)

private def p175556547619 := certifiedPrime 175556547619 2 [(p2,1),(p3,1),(p47,1),(p622540949,1)] (by decide +kernel)

private def p186119047619 := certifiedPrime 186119047619 2 [(p2,1),(p7,1),(p3109,1),(p4276043,1)] (by decide +kernel)

private def p189699999997 := certifiedPrime 189699999997 5 [(p2,2),(p3,1),(p13,1),(p1216025641,1)] (by decide +kernel)

private def p195999999997 := certifiedPrime 195999999997 2 [(p2,2),(p3,1),(p106031,1),(p154043,1)] (by decide +kernel)

private def p199707868421 := certifiedPrime 199707868421 2 [(p2,2),(p5,1),(p41,1),(p243546181,1)] (by decide +kernel)

private def p208333124729 := certifiedPrime 208333124729 3 [(p2,3),(p26041640591,1)] (by decide +kernel)

private def p222161111111 := certifiedPrime 222161111111 7 [(p2,1),(p5,1),(p22216111111,1)] (by decide +kernel)

private def p237619047619 := certifiedPrime 237619047619 2 [(p2,1),(p3,2),(p59341,1),(p222461,1)] (by decide +kernel)

private def p249749997499 := certifiedPrime 249749997499 2 [(p2,1),(p3,2),(p47,1),(p3539,1),(p83417,1)] (by decide +kernel)

private def p260294117647 := certifiedPrime 260294117647 3 [(p2,1),(p3,1),(p43382352941,1)] (by decide +kernel)

private def p269999999999 := certifiedPrime 269999999999 7 [(p2,1),(p134999999999,1)] (by decide +kernel)

private def p279979999997 := certifiedPrime 279979999997 2 [(p2,2),(p83,1),(p12721,1),(p66293,1)] (by decide +kernel)

private def p279999999997 := certifiedPrime 279999999997 2 [(p2,2),(p3,1),(p23333333333,1)] (by decide +kernel)

private def p293303030303 := certifiedPrime 293303030303 5 [(p2,1),(p241,1),(p608512511,1)] (by decide +kernel)

private def p299899999999 := certifiedPrime 299899999999 6 [(p2,1),(p3,2),(p53,1),(p314360587,1)] (by decide +kernel)

private def p328357142857 := certifiedPrime 328357142857 5 [(p2,3),(p3,2),(p4560515873,1)] (by decide +kernel)

private def p399878999999 := certifiedPrime 399878999999 13 [(p2,1),(p151,1),(p1324102649,1)] (by decide +kernel)

private def p403708333333 := certifiedPrime 403708333333 5 [(p2,2),(p3,1),(p37,1),(p829,1),(p1096807,1)] (by decide +kernel)

private def p407870833333 := certifiedPrime 407870833333 6 [(p2,2),(p3,1),(p37,1),(p29009,1),(p31667,1)] (by decide +kernel)

private def p413489999999 := certifiedPrime 413489999999 17 [(p2,1),(p29,1),(p239,1),(p419,1),(p71191,1)] (by decide +kernel)

private def p459999999997 := certifiedPrime 459999999997 2 [(p2,2),(p3,1),(p38333333333,1)] (by decide +kernel)

private def p488899999999 := certifiedPrime 488899999999 6 [(p2,1),(p3,2),(p27161111111,1)] (by decide +kernel)

private def p494999449949 := certifiedPrime 494999449949 2 [(p2,2),(p1549,1),(p79890163,1)] (by decide +kernel)

private def p496994999999 := certifiedPrime 496994999999 7 [(p2,1),(p7,2),(p5071377551,1)] (by decide +kernel)

private def p498988999997 := certifiedPrime 498988999997 2 [(p2,2),(p401,1),(p311090399,1)] (by decide +kernel)

private def p499897999999 := certifiedPrime 499897999999 3 [(p2,1),(p3,2),(p251,1),(p541,1),(p204521,1)] (by decide +kernel)

private def p519999999991 := certifiedPrime 519999999991 3 [(p2,1),(p3,1),(p5,1),(p17333333333,1)] (by decide +kernel)

private def p559799999999 := certifiedPrime 559799999999 7 [(p2,1),(p827,1),(p338452237,1)] (by decide +kernel)

private def p569999999999 := certifiedPrime 569999999999 22 [(p2,1),(p11,1),(p13,1),(p89,1),(p22393337,1)] (by decide +kernel)

private def p577999999999 := certifiedPrime 577999999999 3 [(p2,1),(p3,2),(p911,1),(p35248201,1)] (by decide +kernel)

private def p579799999997 := certifiedPrime 579799999997 5 [(p2,2),(p7,1),(p23,1),(p59,1),(p15259501,1)] (by decide +kernel)

private def p579983999999 := certifiedPrime 579983999999 17 [(p2,1),(p13,1),(p137,1),(p162825379,1)] (by decide +kernel)

private def p584788989997 := certifiedPrime 584788989997 2 [(p2,2),(p3,2),(p2539,1),(p6397849,1)] (by decide +kernel)

private def p599999999993 := certifiedPrime 599999999993 3 [(p2,3),(p19,1),(p37,1),(p106685633,1)] (by decide +kernel)

private def p619999988987 := certifiedPrime 619999988987 2 [(p2,1),(p7,1),(p947,1),(p1427,1),(p32771,1)] (by decide +kernel)

private def p668997989999 := certifiedPrime 668997989999 11 [(p2,1),(p13,1),(p739,1),(p34818257,1)] (by decide +kernel)

private def p673999999997 := certifiedPrime 673999999997 2 [(p2,2),(p53,1),(p5147,1),(p617689,1)] (by decide +kernel)

private def p679999999997 := certifiedPrime 679999999997 2 [(p2,2),(p19,1),(p701,1),(p12763721,1)] (by decide +kernel)

private def p694999999999 := certifiedPrime 694999999999 6 [(p2,1),(p3,2),(p38611111111,1)] (by decide +kernel)

private def p697999999999 := certifiedPrime 697999999999 3 [(p2,1),(p3,1),(p7,1),(p1471,1),(p11297789,1)] (by decide +kernel)

private def p699859999999 := certifiedPrime 699859999999 3 [(p2,1),(p3,2),(p17,1),(p19,1),(p173,1),(p695809,1)] (by decide +kernel)

private def p699988999991 := certifiedPrime 699988999991 7 [(p2,1),(p5,1),(p7,1),(p9999842857,1)] (by decide +kernel)

private def p737899989997 := certifiedPrime 737899989997 2 [(p2,2),(p3,1),(p13,1),(p4730128141,1)] (by decide +kernel)

private def p738898998997 := certifiedPrime 738898998997 6 [(p2,2),(p3,1),(p937,1),(p65714959,1)] (by decide +kernel)

private def p790815833333 := certifiedPrime 790815833333 2 [(p2,2),(p7,1),(p31,1),(p911078149,1)] (by decide +kernel)

private def p797999898889 := certifiedPrime 797999898889 11 [(p2,3),(p3,2),(p41,1),(p270325169,1)] (by decide +kernel)

private def p799399999991 := certifiedPrime 799399999991 26 [(p2,1),(p5,1),(p19,1),(p1201,1),(p3503221,1)] (by decide +kernel)

private def p799899999991 := certifiedPrime 799899999991 6 [(p2,1),(p3,1),(p5,1),(p7,1),(p13,1),(p53,1),(p67,1),(p109,1),(p757,1)] (by decide +kernel)

private def p799978999999 := certifiedPrime 799978999999 6 [(p2,1),(p3,1),(p37,1),(p1217,1),(p2960977,1)] (by decide +kernel)

private def p799999999991 := certifiedPrime 799999999991 11 [(p2,1),(p5,1),(p79999999999,1)] (by decide +kernel)

private def p826979999999 := certifiedPrime 826979999999 19 [(p2,1),(p413489999999,1)] (by decide +kernel)

private def p837968999999 := certifiedPrime 837968999999 17 [(p2,1),(p13,1),(p4229,1),(p7621087,1)] (by decide +kernel)

private def p868999999999 := certifiedPrime 868999999999 3 [(p2,1),(p3,1),(p13,1),(p23971,1),(p464771,1)] (by decide +kernel)

private def p869989999993 := certifiedPrime 869989999993 5 [(p2,3),(p3,1),(p19,1),(p479,1),(p3983033,1)] (by decide +kernel)

private def p888379999999 := certifiedPrime 888379999999 6 [(p2,1),(p3,1),(p41,1),(p6673,1),(p541181,1)] (by decide +kernel)

private def p888999999991 := certifiedPrime 888999999991 6 [(p2,1),(p3,1),(p5,1),(p59,1),(p163,1),(p3081349,1)] (by decide +kernel)

private def p889959996997 := certifiedPrime 889959996997 6 [(p2,2),(p3,1),(p7,1),(p10594761869,1)] (by decide +kernel)

private def p889999879889 := certifiedPrime 889999879889 3 [(p2,4),(p7,1),(p983,1),(p1429,1),(p5657,1)] (by decide +kernel)

private def p896299999999 := certifiedPrime 896299999999 6 [(p2,1),(p3,1),(p13,1),(p107,1),(p6361,1),(p16883,1)] (by decide +kernel)

private def p896999999993 := certifiedPrime 896999999993 3 [(p2,3),(p103,1),(p9227,1),(p117979,1)] (by decide +kernel)

private def p896999999999 := certifiedPrime 896999999999 11 [(p2,1),(p8501,1),(p52758499,1)] (by decide +kernel)

private def p897679999999 := certifiedPrime 897679999999 3 [(p2,1),(p3,2),(p241,1),(p206934071,1)] (by decide +kernel)

private def p898898989999 := certifiedPrime 898898989999 3 [(p2,1),(p3,1),(p149816498333,1)] (by decide +kernel)

private def p898899899993 := certifiedPrime 898899899993 3 [(p2,3),(p112362487499,1)] (by decide +kernel)

private def p898949999999 := certifiedPrime 898949999999 7 [(p2,1),(p29,1),(p15499137931,1)] (by decide +kernel)

private def p899599999997 := certifiedPrime 899599999997 2 [(p2,2),(p179,1),(p1256424581,1)] (by decide +kernel)

private def p899995999999 := certifiedPrime 899995999999 3 [(p2,1),(p3,1),(p1459,1),(p1723,1),(p59669,1)] (by decide +kernel)

private def p916999999997 := certifiedPrime 916999999997 2 [(p2,2),(p811,1),(p282675709,1)] (by decide +kernel)

private def p925999999979 := certifiedPrime 925999999979 2 [(p2,1),(p17,1),(p29,1),(p1789,1),(p524957,1)] (by decide +kernel)

private def p947999999993 := certifiedPrime 947999999993 3 [(p2,3),(p23,1),(p5152173913,1)] (by decide +kernel)

private def p949889979979 := certifiedPrime 949889979979 2 [(p2,1),(p3,1),(p887,1),(p1783,1),(p100103,1)] (by decide +kernel)

private def p959899898999 := certifiedPrime 959899898999 13 [(p2,1),(p61,1),(p769,1),(p10231511,1)] (by decide +kernel)

private def p959999999999 := certifiedPrime 959999999999 31 [(p2,1),(p13,1),(p61,1),(p167,1),(p3624529,1)] (by decide +kernel)

private def p969589799999 := certifiedPrime 969589799999 7 [(p2,1),(p97,1),(p1277,1),(p3913771,1)] (by decide +kernel)

private def p974999999999 := certifiedPrime 974999999999 7 [(p2,1),(p383,1),(p1272845953,1)] (by decide +kernel)

private def p976499999999 := certifiedPrime 976499999999 19 [(p2,1),(p19,1),(p163,1),(p157652567,1)] (by decide +kernel)

private def p978999898883 := certifiedPrime 978999898883 2 [(p2,1),(p17,1),(p331,1),(p5827,1),(p14929,1)] (by decide +kernel)

private def p979999799993 := certifiedPrime 979999799993 3 [(p2,3),(p53,1),(p2311320283,1)] (by decide +kernel)

private def p986998999997 := certifiedPrime 986998999997 2 [(p2,2),(p344941,1),(p715339,1)] (by decide +kernel)

private def p989899999993 := certifiedPrime 989899999993 5 [(p2,3),(p3,2),(p83,1),(p193,1),(p858269,1)] (by decide +kernel)

private def p989998899899 := certifiedPrime 989998899899 2 [(p2,1),(p494999449949,1)] (by decide +kernel)

private def p991999999999 := certifiedPrime 991999999999 3 [(p2,1),(p3,2),(p7,1),(p59,1),(p269,1),(p496063,1)] (by decide +kernel)

private def p993979999993 := certifiedPrime 993979999993 10 [(p2,3),(p3,1),(p7,1),(p5916547619,1)] (by decide +kernel)

private def p993989999999 := certifiedPrime 993989999999 19 [(p2,1),(p496994999999,1)] (by decide +kernel)

private def p993999999997 := certifiedPrime 993999999997 2 [(p2,2),(p3,2),(p27611111111,1)] (by decide +kernel)

private def p995989988989 := certifiedPrime 995989988989 2 [(p2,2),(p3,2),(p5347,1),(p5174189,1)] (by decide +kernel)

private def p998998979989 := certifiedPrime 998998979989 2 [(p2,2),(p3,1),(p31,1),(p2685481129,1)] (by decide +kernel)

private def p998999989997 := certifiedPrime 998999989997 2 [(p2,2),(p249749997499,1)] (by decide +kernel)

private def p999619999999 := certifiedPrime 999619999999 3 [(p2,1),(p3,1),(p337,1),(p4993,1),(p99013,1)] (by decide +kernel)

private def p999898888889 := certifiedPrime 999898888889 3 [(p2,3),(p5827,1),(p21449693,1)] (by decide +kernel)

private def p999899899777 := certifiedPrime 999899899777 15 [(p2,7),(p3,2),(p3331,1),(p260573,1)] (by decide +kernel)

private def p999994999999 := certifiedPrime 999994999999 3 [(p2,1),(p3,1),(p17,1),(p4421,1),(p2217569,1)] (by decide +kernel)

private def p999999999899 := certifiedPrime 999999999899 2 [(p2,1),(p19,1),(p101,1),(p260552371,1)] (by decide +kernel)

private def p1049998333333 := certifiedPrime 1049998333333 2 [(p2,2),(p3,1),(p13,1),(p6730758547,1)] (by decide +kernel)

private def p1109037037037 := certifiedPrime 1109037037037 2 [(p2,2),(p2833,1),(p4093,1),(p23911,1)] (by decide +kernel)

private def p1124999999999 := certifiedPrime 1124999999999 7 [(p2,1),(p7,1),(p307,1),(p349,1),(p443,1),(p1693,1)] (by decide +kernel)

private def p1579998989999 := certifiedPrime 1579998989999 11 [(p2,1),(p11,1),(p13,1),(p5524471993,1)] (by decide +kernel)

private def p1739649122807 := certifiedPrime 1739649122807 7 [(p2,1),(p7,1),(p124260651629,1)] (by decide +kernel)

private def p1859999999999 := certifiedPrime 1859999999999 7 [(p2,1),(p7,1),(p19,1),(p263,1),(p26587381,1)] (by decide +kernel)

private def p1977857142857 := certifiedPrime 1977857142857 3 [(p2,3),(p7,1),(p16189,1),(p2181659,1)] (by decide +kernel)

private def p1999988999989 := certifiedPrime 1999988999989 10 [(p2,2),(p3,1),(p7,1),(p17,1),(p4801,1),(p291721,1)] (by decide +kernel)

private def p2389984999999 := certifiedPrime 2389984999999 3 [(p2,1),(p3,1),(p29,1),(p829,1),(p16568813,1)] (by decide +kernel)

private def p2499997496749 := certifiedPrime 2499997496749 2 [(p2,2),(p3,1),(p208333124729,1)] (by decide +kernel)

private def p2599999999999 := certifiedPrime 2599999999999 3 [(p2,1),(p3,1),(p19207,1),(p22561219,1)] (by decide +kernel)

private def p2999999969999 := certifiedPrime 2999999969999 7 [(p2,1),(p2293,1),(p654164843,1)] (by decide +kernel)

private def p3399989999999 := certifiedPrime 3399989999999 13 [(p2,1),(p266797,1),(p6371867,1)] (by decide +kernel)

private def p3799999888889 := certifiedPrime 3799999888889 3 [(p2,3),(p7,1),(p19,1),(p3571428467,1)] (by decide +kernel)

private def p3998899999999 := certifiedPrime 3998899999999 3 [(p2,1),(p3,2),(p222161111111,1)] (by decide +kernel)

private def p3998989999997 := certifiedPrime 3998989999997 2 [(p2,2),(p101,1),(p9898490099,1)] (by decide +kernel)

private def p4887899999999 := certifiedPrime 4887899999999 7 [(p2,1),(p29,1),(p1709,1),(p49311959,1)] (by decide +kernel)

private def p4915583333333 := certifiedPrime 4915583333333 3 [(p2,2),(p7,1),(p175556547619,1)] (by decide +kernel)

private def p4983222221111 := certifiedPrime 4983222221111 7 [(p2,1),(p5,1),(p7,1),(p66629,1),(p1068437,1)] (by decide +kernel)

private def p5819888999999 := certifiedPrime 5819888999999 7 [(p2,1),(p135283,1),(p21510053,1)] (by decide +kernel)

private def p5979999999997 := certifiedPrime 5979999999997 5 [(p2,2),(p3,2),(p11,1),(p17519,1),(p861979,1)] (by decide +kernel)

private def p5989988999899 := certifiedPrime 5989988999899 2 [(p2,1),(p3,2),(p19,1),(p67,1),(p109,1),(p2398273,1)] (by decide +kernel)

private def p5989999999999 := certifiedPrime 5989999999999 7 [(p2,1),(p3,1),(p7,1),(p3391,1),(p42058109,1)] (by decide +kernel)

private def p5999799999797 := certifiedPrime 5999799999797 2 [(p2,2),(p1741,1),(p861545089,1)] (by decide +kernel)

private def p5999887998997 := certifiedPrime 5999887998997 2 [(p2,2),(p3,1),(p37,1),(p47,1),(p8389,1),(p34273,1)] (by decide +kernel)

private def p6299989999999 := certifiedPrime 6299989999999 3 [(p2,1),(p3,1),(p1049998333333,1)] (by decide +kernel)

private def p6799979999999 := certifiedPrime 6799979999999 7 [(p2,1),(p3399989999999,1)] (by decide +kernel)

private def p6859998899989 := certifiedPrime 6859998899989 2 [(p2,2),(p3,1),(p13,1),(p47,1),(p101,1),(p2347,1),(p3947,1)] (by decide +kernel)

private def p6896999999999 := certifiedPrime 6896999999999 7 [(p2,1),(p420193,1),(p8206943,1)] (by decide +kernel)

private def p6997759999999 := certifiedPrime 6997759999999 3 [(p2,1),(p3,1),(p113,1),(p3089,1),(p3341269,1)] (by decide +kernel)

private def p6998939999999 := certifiedPrime 6998939999999 19 [(p2,1),(p479,1),(p7305782881,1)] (by decide +kernel)

private def p6999599999993 := certifiedPrime 6999599999993 3 [(p2,3),(p149,1),(p5872147651,1)] (by decide +kernel)

private def p7399999999993 := certifiedPrime 7399999999993 5 [(p2,3),(p3,1),(p22159,1),(p13914587,1)] (by decide +kernel)

private def p7499799588889 := certifiedPrime 7499799588889 14 [(p2,3),(p3,3),(p19,1),(p7351,1),(p248597,1)] (by decide +kernel)

private def p7588898999999 := certifiedPrime 7588898999999 7 [(p2,1),(p19,1),(p199707868421,1)] (by decide +kernel)

private def p7697999999993 := certifiedPrime 7697999999993 3 [(p2,3),(p365747,1),(p2630917,1)] (by decide +kernel)

private def p7699999999999 := certifiedPrime 7699999999999 3 [(p2,1),(p3,1),(p47,1),(p27304964539,1)] (by decide +kernel)

private def p7717979999999 := certifiedPrime 7717979999999 11 [(p2,1),(p23,1),(p37,1),(p241,1),(p863,1),(p21803,1)] (by decide +kernel)

private def p7779998899999 := certifiedPrime 7779998899999 3 [(p2,1),(p3,2),(p13,1),(p83,1),(p400576609,1)] (by decide +kernel)

private def p7799999999993 := certifiedPrime 7799999999993 3 [(p2,3),(p974999999999,1)] (by decide +kernel)

private def p7816999999999 := certifiedPrime 7816999999999 3 [(p2,1),(p3,1),(p7,1),(p186119047619,1)] (by decide +kernel)

private def p7886999399999 := certifiedPrime 7886999399999 11 [(p2,1),(p179,1),(p21839,1),(p1008779,1)] (by decide +kernel)

private def p7988998899997 := certifiedPrime 7988998899997 6 [(p2,2),(p3,3),(p3037,1),(p24357001,1)] (by decide +kernel)

private def p7989599999993 := certifiedPrime 7989599999993 3 [(p2,3),(p13,1),(p76823076923,1)] (by decide +kernel)

private def p7999499999999 := certifiedPrime 7999499999999 7 [(p2,1),(p13,1),(p23,1),(p1091,1),(p12261311,1)] (by decide +kernel)

private def p7999999999991 := certifiedPrime 7999999999991 17 [(p2,1),(p5,1),(p131,1),(p331,1),(p18449759,1)] (by decide +kernel)

private def p7999999999993 := certifiedPrime 7999999999993 5 [(p2,3),(p3,3),(p7,1),(p11,1),(p13,1),(p37,1),(p101,1),(p9901,1)] (by decide +kernel)

private def p8299999999999 := certifiedPrime 8299999999999 11 [(p2,1),(p3,2),(p7,2),(p38047,1),(p247337,1)] (by decide +kernel)

private def p8689989999997 := certifiedPrime 8689989999997 2 [(p2,2),(p3,2),(p50549,1),(p4775339,1)] (by decide +kernel)

private def p8779999999999 := certifiedPrime 8779999999999 3 [(p2,1),(p3,1),(p59,1),(p24802259887,1)] (by decide +kernel)

private def p8849999999999 := certifiedPrime 8849999999999 7 [(p2,1),(p17,1),(p260294117647,1)] (by decide +kernel)

private def p8879959969999 := certifiedPrime 8879959969999 3 [(p2,1),(p3,1),(p13,1),(p167,1),(p197,1),(p353,1),(p9803,1)] (by decide +kernel)

private def p8888999999993 := certifiedPrime 8888999999993 3 [(p2,3),(p7,1),(p131,1),(p1211695747,1)] (by decide +kernel)

private def p8899989898889 := certifiedPrime 8899989898889 3 [(p2,3),(p11,2),(p9194204441,1)] (by decide +kernel)

private def p8959999999997 := certifiedPrime 8959999999997 2 [(p2,2),(p497999,1),(p4498001,1)] (by decide +kernel)

private def p8998999999999 := certifiedPrime 8998999999999 3 [(p2,1),(p3,1),(p41,1),(p15727,1),(p2326019,1)] (by decide +kernel)

private def p8999888989999 := certifiedPrime 8999888989999 6 [(p2,1),(p3,1),(p439,1),(p13411,1),(p254777,1)] (by decide +kernel)

private def p8999999969999 := certifiedPrime 8999999969999 11 [(p2,1),(p285161,1),(p15780559,1)] (by decide +kernel)

private def p8999999999993 := certifiedPrime 8999999999993 3 [(p2,3),(p1124999999999,1)] (by decide +kernel)

private def p9193999999997 := certifiedPrime 9193999999997 2 [(p2,2),(p7,1),(p328357142857,1)] (by decide +kernel)

private def p9278999999999 := certifiedPrime 9278999999999 7 [(p2,1),(p4969,1),(p29879,1),(p31249,1)] (by decide +kernel)

private def p9489789999997 := certifiedPrime 9489789999997 2 [(p2,2),(p3,1),(p790815833333,1)] (by decide +kernel)

private def p9496889999999 := certifiedPrime 9496889999999 23 [(p2,1),(p307,1),(p1163,1),(p13299439,1)] (by decide +kernel)

private def p9499999999991 := certifiedPrime 9499999999991 7 [(p2,1),(p5,1),(p1949,1),(p4651,1),(p104801,1)] (by decide +kernel)

private def p9559939999997 := certifiedPrime 9559939999997 2 [(p2,2),(p2389984999999,1)] (by decide +kernel)

private def p9659999899999 := certifiedPrime 9659999899999 6 [(p2,1),(p3,3),(p7,2),(p3650793613,1)] (by decide +kernel)

private def p9688999999993 := certifiedPrime 9688999999993 5 [(p2,3),(p3,1),(p403708333333,1)] (by decide +kernel)

private def p9689899999991 := certifiedPrime 9689899999991 7 [(p2,1),(p5,1),(p7,1),(p41,1),(p131,1),(p25773067,1)] (by decide +kernel)

private def p9689998999999 := certifiedPrime 9689998999999 3 [(p2,1),(p3,1),(p55807,1),(p28939019,1)] (by decide +kernel)

private def p9699199999999 := certifiedPrime 9699199999999 6 [(p2,1),(p3,1),(p23,1),(p70284057971,1)] (by decide +kernel)

private def p9729999999997 := certifiedPrime 9729999999997 5 [(p2,2),(p3,1),(p193,1),(p4201208981,1)] (by decide +kernel)

private def p9788899999993 := certifiedPrime 9788899999993 5 [(p2,3),(p3,1),(p407870833333,1)] (by decide +kernel)

private def p9798997999997 := certifiedPrime 9798997999997 2 [(p2,2),(p691,1),(p2477,1),(p1431257,1)] (by decide +kernel)

private def p9849999999997 := certifiedPrime 9849999999997 2 [(p2,2),(p3,2),(p13,1),(p61,1),(p345032927,1)] (by decide +kernel)

private def p9887989889891 := certifiedPrime 9887989889891 2 [(p2,1),(p5,1),(p7,1),(p1063,1),(p132885229,1)] (by decide +kernel)

private def p9888999999883 := certifiedPrime 9888999999883 5 [(p2,1),(p3,1),(p17,1),(p23,1),(p4215260017,1)] (by decide +kernel)

private def p9889899999779 := certifiedPrime 9889899999779 2 [(p2,1),(p101,1),(p48959900989,1)] (by decide +kernel)

private def p9894988999999 := certifiedPrime 9894988999999 11 [(p2,1),(p3,3),(p6967,1),(p26301211,1)] (by decide +kernel)

private def p9896599999997 := certifiedPrime 9896599999997 2 [(p2,2),(p43,1),(p977,1),(p58892909,1)] (by decide +kernel)

private def p9897999999991 := certifiedPrime 9897999999991 11 [(p2,1),(p3,1),(p5,1),(p450349,1),(p732617,1)] (by decide +kernel)

private def p9898999999997 := certifiedPrime 9898999999997 2 [(p2,2),(p6221,1),(p397805819,1)] (by decide +kernel)

private def p9899899899899 := certifiedPrime 9899899899899 2 [(p2,1),(p1907,1),(p2595673807,1)] (by decide +kernel)

private def p9919999999999 := certifiedPrime 9919999999999 6 [(p2,1),(p3,2),(p11,1),(p23,1),(p2178304787,1)] (by decide +kernel)

private def p9969599999999 := certifiedPrime 9969599999999 23 [(p2,1),(p661,1),(p4021,1),(p1875479,1)] (by decide +kernel)

private def p9979999999999 := certifiedPrime 9979999999999 3 [(p2,1),(p3,1),(p7,1),(p237619047619,1)] (by decide +kernel)

private def p9986123624999 := certifiedPrime 9986123624999 7 [(p2,1),(p8599,1),(p580656101,1)] (by decide +kernel)

private def p9989888999897 := certifiedPrime 9989888999897 3 [(p2,3),(p13,1),(p96056624999,1)] (by decide +kernel)

private def p9989998899997 := certifiedPrime 9989998899997 2 [(p2,2),(p3,1),(p41,1),(p263,1),(p77204851,1)] (by decide +kernel)

private def p9994996999997 := certifiedPrime 9994996999997 2 [(p2,2),(p19,1),(p61,1),(p19447,1),(p110863,1)] (by decide +kernel)

private def p9996499999999 := certifiedPrime 9996499999999 6 [(p2,1),(p3,2),(p43,1),(p1439,1),(p8975243,1)] (by decide +kernel)

private def p9997599999991 := certifiedPrime 9997599999991 6 [(p2,1),(p3,1),(p5,1),(p1877,1),(p177545729,1)] (by decide +kernel)

private def p9999599999999 := certifiedPrime 9999599999999 7 [(p2,1),(p7,1),(p19,1),(p67,1),(p127,1),(p4417967,1)] (by decide +kernel)

private def p9999779999999 := certifiedPrime 9999779999999 11 [(p2,1),(p239,1),(p701,1),(p2083,1),(p14327,1)] (by decide +kernel)

private def p9999989986997 := certifiedPrime 9999989986997 2 [(p2,2),(p2499997496749,1)] (by decide +kernel)

private def p9999999499999 := certifiedPrime 9999999499999 3 [(p2,1),(p3,1),(p1889,1),(p882300997,1)] (by decide +kernel)

private def p11653333333333 := certifiedPrime 11653333333333 2 [(p2,2),(p3,1),(p89,1),(p10911360799,1)] (by decide +kernel)

private def p17499987499999 := certifiedPrime 17499987499999 7 [(p2,1),(p3,1),(p347,1),(p881,1),(p9540719,1)] (by decide +kernel)

private def p17993999999999 := certifiedPrime 17993999999999 7 [(p2,1),(p11,1),(p167,1),(p43717,1),(p112031,1)] (by decide +kernel)

private def p19999999999997 := certifiedPrime 19999999999997 2 [(p2,2),(p491,1),(p10183299389,1)] (by decide +kernel)

private def p27689999999999 := certifiedPrime 27689999999999 7 [(p2,1),(p7,1),(p1977857142857,1)] (by decide +kernel)

private def p27998888999999 := certifiedPrime 27998888999999 7 [(p2,1),(p7,1),(p19,1),(p105258981203,1)] (by decide +kernel)

private def p38779899799999 := certifiedPrime 38779899799999 3 [(p2,1),(p3,1),(p7,1),(p18869,1),(p48933751,1)] (by decide +kernel)

private def p38869999999997 := certifiedPrime 38869999999997 2 [(p2,2),(p11,1),(p19,1),(p43,1),(p83,1),(p13027519,1)] (by decide +kernel)

private def p38998989999889 := certifiedPrime 38998989999889 11 [(p2,4),(p3,1),(p133481,1),(p6086851,1)] (by decide +kernel)

private def p39899898999997 := certifiedPrime 39899898999997 5 [(p2,2),(p3,1),(p7,1),(p709,1),(p669955991,1)] (by decide +kernel)

private def p43869998999999 := certifiedPrime 43869998999999 7 [(p2,1),(p113,1),(p257,1),(p755311439,1)] (by decide +kernel)

private def p44474849999999 := certifiedPrime 44474849999999 19 [(p2,1),(p11,1),(p179,1),(p33211,1),(p340061,1)] (by decide +kernel)

private def p44494499494499 := certifiedPrime 44494499494499 2 [(p2,1),(p181,1),(p277,1),(p457,1),(p970961,1)] (by decide +kernel)

private def p44898998999999 := certifiedPrime 44898998999999 11 [(p2,1),(p11,2),(p13,1),(p8039,1),(p1775317,1)] (by decide +kernel)

private def p48998899999999 := certifiedPrime 48998899999999 6 [(p2,1),(p3,5),(p13,1),(p17,2),(p47,1),(p570967,1)] (by decide +kernel)

private def p48998989999997 := certifiedPrime 48998989999997 2 [(p2,2),(p296201,1),(p41356199,1)] (by decide +kernel)

private def p48999999999997 := certifiedPrime 48999999999997 2 [(p2,2),(p3,2),(p157,1),(p2477,1),(p3499999,1)] (by decide +kernel)

private def p58699999999997 := certifiedPrime 58699999999997 2 [(p2,2),(p167,1),(p152429,1),(p576493,1)] (by decide +kernel)

private def p58986999999997 := certifiedPrime 58986999999997 2 [(p2,2),(p3,1),(p4915583333333,1)] (by decide +kernel)

private def p59399999999999 := certifiedPrime 59399999999999 7 [(p2,1),(p7,1),(p31,1),(p47,1),(p2912050201,1)] (by decide +kernel)

private def p59887999999999 := certifiedPrime 59887999999999 3 [(p2,1),(p3,3),(p1109037037037,1)] (by decide +kernel)

private def p59899898899999 := certifiedPrime 59899898899999 3 [(p2,1),(p3,3),(p1777,1),(p624230381,1)] (by decide +kernel)

private def p59988889999991 := certifiedPrime 59988889999991 17 [(p2,1),(p5,1),(p7,1),(p89,1),(p9629035313,1)] (by decide +kernel)

private def p62899999999999 := certifiedPrime 62899999999999 6 [(p2,1),(p3,1),(p7,1),(p250837,1),(p5970487,1)] (by decide +kernel)

private def p64999999999999 := certifiedPrime 64999999999999 7 [(p2,1),(p3,2),(p7,1),(p107,1),(p19763,1),(p243953,1)] (by decide +kernel)

private def p69399899999999 := certifiedPrime 69399899999999 7 [(p2,1),(p251,1),(p138246812749,1)] (by decide +kernel)

private def p69599899999999 := certifiedPrime 69599899999999 6 [(p2,1),(p3,3),(p103,1),(p12513466379,1)] (by decide +kernel)

private def p69748899999997 := certifiedPrime 69748899999997 2 [(p2,2),(p3,1),(p7,1),(p17,1),(p53,1),(p4679,1),(p196961,1)] (by decide +kernel)

private def p69896898999997 := certifiedPrime 69896898999997 5 [(p2,2),(p3,1),(p241,1),(p24169052213,1)] (by decide +kernel)

private def p69919999999999 := certifiedPrime 69919999999999 3 [(p2,1),(p3,1),(p11653333333333,1)] (by decide +kernel)

private def p69999949999997 := certifiedPrime 69999949999997 2 [(p2,2),(p17499987499999,1)] (by decide +kernel)

private def p74989999998889 := certifiedPrime 74989999998889 7 [(p2,3),(p3,1),(p13,1),(p617,1),(p389550347,1)] (by decide +kernel)

private def p77995999999999 := certifiedPrime 77995999999999 3 [(p2,1),(p3,2),(p36389,1),(p119077499,1)] (by decide +kernel)

private def p78897997999999 := certifiedPrime 78897997999999 6 [(p2,1),(p3,3),(p163,1),(p293,1),(p691,1),(p44273,1)] (by decide +kernel)

private def p79888988999993 := certifiedPrime 79888988999993 3 [(p2,3),(p9986123624999,1)] (by decide +kernel)

private def p79898998999991 := certifiedPrime 79898998999991 26 [(p2,1),(p5,1),(p12583,1),(p634975753,1)] (by decide +kernel)

private def p81999999999997 := certifiedPrime 81999999999997 5 [(p2,2),(p3,1),(p13,1),(p19,1),(p761,1),(p4817,1),(p7547,1)] (by decide +kernel)

private def p84998849999993 := certifiedPrime 84998849999993 3 [(p2,3),(p37,1),(p19079,1),(p15051013,1)] (by decide +kernel)

private def p87869699999999 := certifiedPrime 87869699999999 7 [(p2,1),(p7,1),(p277,1),(p35531,1),(p637711,1)] (by decide +kernel)

private def p87997999999993 := certifiedPrime 87997999999993 5 [(p2,3),(p3,1),(p17,1),(p139837,1),(p1542377,1)] (by decide +kernel)

private def p88939898999999 := certifiedPrime 88939898999999 11 [(p2,1),(p37,1),(p43,1),(p9743,1),(p2868823,1)] (by decide +kernel)

private def p88949699999999 := certifiedPrime 88949699999999 11 [(p2,1),(p44474849999999,1)] (by decide +kernel)

private def p88988998988999 := certifiedPrime 88988998988999 7 [(p2,1),(p44494499494499,1)] (by decide +kernel)

private def p88989999999991 := certifiedPrime 88989999999991 3 [(p2,1),(p3,1),(p5,1),(p31,1),(p71,1),(p16421,1),(p82073,1)] (by decide +kernel)

private def p89697999979999 := certifiedPrime 89697999979999 3 [(p2,1),(p3,2),(p4983222221111,1)] (by decide +kernel)

private def p89959979799997 := certifiedPrime 89959979799997 6 [(p2,2),(p3,1),(p863,1),(p1231,1),(p7056661,1)] (by decide +kernel)

private def p89987999999993 := certifiedPrime 89987999999993 3 [(p2,3),(p3701,1),(p7129,1),(p426331,1)] (by decide +kernel)

private def p89989969999991 := certifiedPrime 89989969999991 19 [(p2,1),(p5,1),(p229,1),(p1361,1),(p28873571,1)] (by decide +kernel)

private def p96789999999991 := certifiedPrime 96789999999991 7 [(p2,1),(p3,1),(p5,1),(p11,1),(p293303030303,1)] (by decide +kernel)

private def p96969999999997 := certifiedPrime 96969999999997 5 [(p2,2),(p3,2),(p83,1),(p32453145917,1)] (by decide +kernel)

private def p96998899999993 := certifiedPrime 96998899999993 5 [(p2,3),(p3,1),(p151,1),(p277,1),(p96627079,1)] (by decide +kernel)

private def p97399999999997 := certifiedPrime 97399999999997 2 [(p2,2),(p739,1),(p176417,1),(p186773,1)] (by decide +kernel)

private def p97989899988997 := certifiedPrime 97989899988997 2 [(p2,2),(p3,4),(p349,1),(p866584421,1)] (by decide +kernel)

private def p98799988889999 := certifiedPrime 98799988889999 11 [(p2,1),(p11,1),(p109,1),(p41200996201,1)] (by decide +kernel)

private def p99698998999997 := certifiedPrime 99698998999997 2 [(p2,2),(p11,1),(p137,1),(p13967,1),(p1184171,1)] (by decide +kernel)

private def p99972999999997 := certifiedPrime 99972999999997 2 [(p2,2),(p3,1),(p43,1),(p45281,1),(p4278751,1)] (by decide +kernel)

private def p99975999999991 := certifiedPrime 99975999999991 3 [(p2,1),(p3,1),(p5,1),(p17,1),(p41,1),(p47,1),(p317,1),(p320911,1)] (by decide +kernel)

private def p99993999999991 := certifiedPrime 99993999999991 11 [(p2,1),(p3,1),(p5,1),(p42073,1),(p79222621,1)] (by decide +kernel)

private def p99997799799991 := certifiedPrime 99997799799991 11 [(p2,1),(p3,1),(p5,1),(p197,1),(p29297,1),(p577537,1)] (by decide +kernel)

private def p339999799999997 := certifiedPrime 339999799999997 2 [(p2,2),(p571,1),(p368881,1),(p403549,1)] (by decide +kernel)

private def p347699999999999 := certifiedPrime 347699999999999 11 [(p2,1),(p31,1),(p41,1),(p83,1),(p227,1),(p7259809,1)] (by decide +kernel)

private def p598879999999991 := certifiedPrime 598879999999991 13 [(p2,1),(p5,1),(p59887999999999,1)] (by decide +kernel)

private def p799799999898883 := certifiedPrime 799799999898883 3 [(p2,1),(p3,1),(p271,1),(p4111,1),(p119650187,1)] (by decide +kernel)

private def p967689889999991 := certifiedPrime 967689889999991 7 [(p2,1),(p5,1),(p6615047,1),(p14628617,1)] (by decide +kernel)

private def p991599999999991 := certifiedPrime 991599999999991 7 [(p2,1),(p3,1),(p5,1),(p19,1),(p1739649122807,1)] (by decide +kernel)

private def covers (a b : ℕ) : Prop :=
  ∀ n, a ≤ n → n < b → ∃ p : ℕ, p.Prime ∧ squareSum p=n

private def testBlock : ℕ → List Certified → Bool
  | _, [] => true
  | a, p::ps => decide (squareSum p.val=a) && testBlock (a+1) ps

private theorem block (a : ℕ) (ps : List Certified) (ok : testBlock a ps=true) :
    covers a (a+ps.length) := by
  induction ps generalizing a with
  | nil =>
    intro n h t
    simp only [List.length_nil,Nat.add_zero] at t
    omega
  | cons p ps ih =>
    simp only [testBlock,Bool.and_eq_true,decide_eq_true_eq] at ok
    intro n lo hi
    by_cases start : n=a
    · exact ⟨p.val,p.property,ok.1.trans start.symm⟩
    · apply ih (a+1) ok.2 n (by omega)
      simp only [List.length_cons] at hi
      omega

private theorem join {a b c : ℕ} (first : covers a b) (second : covers b c) : covers a c := by
  intro n lo hi
  by_cases before : n<b
  · exact first n lo before
  · exact second n (by omega) hi


private theorem block4 : covers 4 28 :=
  block 4 [p2,p101111,p211,p2111,p11001111101,p3,p13,p113,p112121,p23,p21221,p1123,p11213,p41,p1223,p313,p10133,p241,p233,p112223,p21313,p5,p431,p151] (by decide +kernel)

private theorem block28 : covers 28 52 :=
  block 28 [p1151,p13313,p251,p2333,p11251,p2243,p53,p1433,p1153,p61,p523,p1523,p11161,p443,p541,p353,p33413,p2621,p163,p1163,p13523,p7,p17,p1453] (by decide +kernel)

private theorem block52 : covers 52 76 :=
  block 52 [p1117,p461,p127,p1217,p11633,p227,p37,p137,p1553,p463,p3461,p1237,p11273,p47,p181,p337,p1373,p281,p563,p11821,p12373,p83,p347,p157] (by decide +kernel)

private theorem block76 : covers 76 100 :=
  block 76 [p1571,p283,p257,p6353,p11257,p4801,p19,p191,p1753,p29,p167,p1129,p11617,p229,p457,p139,p1193,p2267,p239,p1367,p11239,p409,p149,p557] (by decide +kernel)

private theorem block100 : covers 100 124 :=
  block 100 [p1933,p467,p277,p1277,p13367,p2467,p59,p773,p1951,p683,p3467,p1259,p11657,p449,p1087,p359,p14177,p827,p619,p1619,p12539,p269,p1667,p577] (by decide +kernel)

private theorem block124 : covers 124 148 :=
  block 124 [p3359,p2269,p2459,p1693,p11369,p487,p79,p179,p1559,p8821,p677,p1279,p11279,p883,p587,p379,p1973,p15359,p569,p3677,p12379,p89,p479,p5387] (by decide +kernel)

private theorem block148 : covers 148 172 :=
  block 148 [p1777,p829,p1289,p2777,p25577,p2687,p389,p3947,p1579,p6269,p2389,p2579,p15767,p22669,p787,p199,p11909,p4289,p769,p1697,p11299,p6469,p859,p3877] (by decide +kernel)

private theorem block172 : covers 172 196 :=
  block 172 [p1399,p6883,p5867,p2399,p13679,p887,p499,p797,p7559,p2887,p4679,p2797,p17729,p2689,p5849,p599,p3779,p11959,p6389,p20599,p12959,p26669,p14887,p1789] (by decide +kernel)

private theorem block196 : covers 196 220 :=
  block 196 [p5399,p33797,p2789,p1699,p11699,p26489,p2699,p15887,p5779,p15797,p5689,p23789,p16993,p8089,p1889,p997,p1979,p8867,p4969,p6779,p12799,p6689,p3889,p5879] (by decide +kernel)

private theorem block220 : covers 220 244 :=
  block 220 [p7993,p13799,p36887,p6599,p36779,p4889,p38669,p4799,p18199,p17977,p8929,p12899,p27779,p167777,p26879,p3989,p39749,p17599,p25889,p23899,p25799,p8887,p48787,p7789] (by decide +kernel)

private theorem block244 : covers 244 268 :=
  block 244 [p1999,p8689,p16889,p2999,p16979,p68687,p48589,p8599,p18959,p13999,p68389,p56897,p29399,p136979,p9887,p4999,p19949,p46889,p6899,p46997,p27799,p88883,p62989,p37889] (by decide +kernel)

private theorem block268 : covers 268 292 :=
  block 268 [p39499,p37799,p159199,p36899,p25999,p129959,p88819,p49499,p17989,p35999,p168887,p28979,p19699,p66889,p168869,p58789,p157889,p59779,p157799,p56989,p156899,p48889,p78887,p18899] (by decide +kernel)

private theorem block292 : covers 292 316 :=
  block 292 [p70999,p19979,p68879,p69499,p67979,p172999,p58889,p88993,p57899,p39799,p137999,p367889,p56999,p379679,p48989,p8999,p97499,p189199,p177979,p29989,p167899,p279779,p8887661,p267899] (by decide +kernel)

private theorem block316 : covers 316 340 :=
  block 316 [p39989,p379499,p157999,p266999,p293899,p275999,p78889,p178889,p77899,p99991,p68899,p168899,p69997,p179969,p688679,p388789,p85999,p159899,p139999,p368899,p658997,p239999,p487889,p78989] (by decide +kernel)

private theorem block340 : covers 340 364 :=
  block 340 [p49999,p77999,p468899,p69899,p469979,p277999,p838889,p268999,p379889,p59999,p377999,p4893869,p389699,p529999,p6195997,p918889,p788779,p179899,p288989,p9379973,p297989,p619999,p898669,p7887883] (by decide +kernel)

private theorem block364 : covers 364 388 :=
  block 364 [p299699,p4589797,p795997,p6978883,p596899,p888887,p988489,p89899,p188999,p79999,p179999,p899687,p496999,p697979,p8496869,p858989,p389989,p998759,p379999,p1979993,p8369897,p956999,p3796997,p489989] (by decide +kernel)

private theorem block388 : covers 388 412 :=
  block 388 [p98999,p497999,p1819999,p3997993,p289999,p2899991,p9967777,p37769993,p6867997,p389999,p4979993,p9759991,p8856997,p2899993,p4878889,p888997,p8788991,p879979,p199999,p969889,p8469997,p679999,p6991997,p8758889] (by decide +kernel)

private theorem block412 : covers 412 436 :=
  block 412 [p9978883,p598999,p5819999,p7599797,p8983699,p6899579,p898889,p9488879,p889997,p999499,p799979,p5979959,p998969,p6794999,p2797999,p3988889,p6289999,p8899937,p599999,p9779993,p59991991,p8969993,p2599999,p9788887] (by decide +kernel)

private theorem block436 : covers 436 460 :=
  block 436 [p9981889,p9494999,p8719999,p7977997,p79648897,p2899997,p9996991,p5888899,p58898981,p2699999,p77789983,p9959779,p73979797,p8659999,p9888887,p8498989,p998989,p4989997,p799999,p9199997,p9886997,p9946999,p9799967,p29199997] (by decide +kernel)

private theorem block460 : covers 460 484 :=
  block 460 [p8696999,p9999883,p9598997,p7999993,p99379991,p78689993,p6995999,p93679997,p8899949,p989999,p4799999,p98579993,p94298989,p9829999,p28999991,p65999993,p367979993,p79796869,p8999993,p47399999,p75999991,p59698897,p9888889,p88998881] (by decide +kernel)

private theorem block484 : covers 484 508 :=
  block 484 [p9899887,p49889977,p9977899,p9999991,p9896989,p86499997,p7969999,p88899883,p59888897,p39987889,p9859999,p39879997,p77599997,p96998983,p75999689,p8998889,p78948899,p8999897,p4999999,p7799999,p55999997,p8999699,p79964999,p27799999] (by decide +kernel)

private theorem block508 : covers 508 532 :=
  block 508 [p98988893,p96299989,p78899993,p43999999,p79999973,p648998993,p39896999,p787699597,p79878889,p18889999,p68988889,p79999981,p95999993,p828499799,p78299999,p69919999,p58988899,p188599889,p88599997,p599497897,p97759999,p569498899,p99969589,p88987889] (by decide +kernel)

private theorem block532 : covers 532 556 :=
  block 532 [p99948889,p9989899,p94999897,p79877999,p91979999,p98869997,p69499999,p69979997,p279999991,p58989899,p98999983,p57899999,p39999979,p799199993,p369889997,p95699999,p877788889,p98994899,p9899999,p49979999,p589399997,p888699991,p89299999,p899992991] (by decide +kernel)

private theorem block556 : covers 556 580 :=
  block 556 [p729979979,p1896898967,p599888797,p99399899,p775998997,p888888887,p895899967,p98898889,p478889899,p89898997,p978899891,p87999997,p19999999,p98689999,p294899999,p69979999,p988888993,p969996887,p738989899,p98599999,p479959999,p999999391,p963889999,p599678999] (by decide +kernel)

private theorem block580 : covers 580 604 :=
  block 580 [p99898889,p794989889,p99889997,p99949999,p859999993,p886999499,p89699999,p469999997,p297999997,p889988993,p268999999,p789999983,p59999999,p999997793,p9159999991,p869999993,p299995999,p799988887,p999889981,p877879999,p979989991,p679989889,p1976889899,p979992899] (by decide +kernel)

private theorem block604 : covers 604 628 :=
  block 604 [p619999999,p699689899,p8866999991,p299999699,p8799959891,p957979999,p889888889,p596998999,p897888989,p894989899,p778889999,p999998981,p909999997,p959959999,p699989897,p499699999,p969799979,p6968489999,p859889999,p839989999,p859999997,p379999999,p7399999991,p6978989993] (by decide +kernel)

private theorem block628 : covers 628 652 :=
  block 628 [p969599999,p3679999997,p499898999,p89999999,p794999999,p9958979993,p9799977991,p289999999,p9687999991,p5789898889,p62848999979,p9438899999,p389999999,p4799999993,p5799999991,p5299988999,p988899889,p9898488997,p888999997,p1989899987,p799999897,p9879799991,p899968999,p6998499997] (by decide +kernel)

private theorem block652 : covers 652 676 :=
  block 652 [p999299999,p1699999997,p8998898957,p3879999889,p999895999,p7899399997,p7579999997,p8969899993,p9685999997,p899989889,p8489999897,p989899997,p999499999,p979999997,p4689899999,p986999999,p7649999999,p9279999997,p3898999889,p9289699999,p8839799999,p999999599,p9997799993,p47898888889] (by decide +kernel)

private theorem block676 : covers 676 700 :=
  block 676 [p7998888889,p9952999999,p9978898987,p8889999991,p6988998889,p1978999999,p7999797997,p89898888883,p8299799999,p9999996991,p6699898999,p39979988887,p8789959999,p66199999997,p9979599997,p9889888889,p9956899999,p8988889997,p8898994999,p898999999,p8949999997,p799999999,p7199999999,p9896989997] (by decide +kernel)

private theorem block700 : covers 700 724 :=
  block 700 [p4996999999,p6997999997,p96968489999,p5899889999,p9898999993,p9589979999,p9799939999,p86299699999,p93896899997,p6999995999,p39796999997,p8894999999,p998999999,p4799999999,p92989978889,p73999999993,p9298999999,p67899999991,p77929999997,p584788989997,p38849999999,p8999999993,p93499999997,p75999999991] (by decide +kernel)

private theorem block724 : covers 724 748 :=
  block 724 [p98599869997,p8998998889,p75969999997,p8898799999,p87489999997,p8799999997,p9199999999,p8899699999,p24989999999,p7999699999,p98989889983,p69999989687,p83898999997,p5989999999,p95999994997,p79579999997,p38699899999,p56998999997,p8999899889,p74898999899,p9988999799,p9999499999,p7979999999,p68949899999] (by decide +kernel)

private theorem block748 : covers 748 772 :=
  block 748 [p8999969999,p96499999997,p72799999999,p38998988999,p92968999999,p97938899999,p9959999999,p39799997999,p519999999991,p98998988887,p95299999999,p89988789997,p98989989991,p77988999997,p98979999991,p77979999997,p619999988987,p98677999999,p16999999999,p98589889999,p738898998997,p59989998997,p737899989997,p95997799999] (by decide +kernel)

private theorem block772 : covers 772 796 :=
  block 772 [p99988888889,p86995999999,p87889889999,p49999899889,p9989899999,p18989999999,p70999999999,p71999999999,p96988999997,p99496999999,p76799999999,p978999898883,p68969999999,p98989999993,p99579899999,p79999999993,p799399999991,p837968999999,p65999999999,p673999999997,p49999988999,p99089999999,p99999999947,p579983999999] (by decide +kernel)

private theorem block796 : covers 796 820 :=
  block 796 [p993979999993,p99289999999,p189699999997,p279979999997,p7499799588889,p826979999999,p89999999993,p947999999993,p195999999997,p889959996997,p99899988889,p925999999979,p97899989899,p949889979979,p97998999997,p99999199999,p96998989999,p699988999991,p69799999999,p916999999997,p668997989999,p888379999999,p89959999999,p459999999997] (by decide +kernel)

private theorem block820 : covers 820 844 :=
  block 820 [p579799999997,p869989999993,p969589799999,p98898899999,p498988999997,p98899999997,p99499999999,p97999799999,p559799999999,p98699999999,p976499999999,p279999999997,p898899899993,p896299999999,p399878999999,p59999999999,p979999799993,p9559939999997,p896999999993,p9887989889891,p797999898889,p888999999991,p999899899777,p799899999991] (by decide +kernel)

private theorem block844 : covers 844 868 :=
  block 844 [p599999999993,p7717979999999,p897679999999,p999619999999,p995989988989,p5819888999999,p269999999999,p1579998989999,p577999999999,p999898888889,p699859999999,p889999879889,p488899999999,p98899999999,p499897999999,p79999999999,p799999999991,p986998999997,p694999999999,p679999999997,p3799999888889,p959899898999,p989899999993,p899599999997] (by decide +kernel)

private theorem block868 : covers 868 892 :=
  block 868 [p993999999997,p9193999999997,p7886999399999,p569999999999,p7697999999993,p898949999999,p98999999999,p974999999999,p7989599999993,p7399999999993,p299899999999,p7816999999999,p6999599999993,p84998849999993,p5999887998997,p993989999999,p6859998899989,p9997599999991,p8879959969999,p898898989999,p6997759999999,p998998979989,p9489789999997,p799978999999] (by decide +kernel)

private theorem block892 : covers 892 916 :=
  block 892 [p991999999999,p868999999999,p9689899999991,p697999999999,p9888999999883,p7588898999999,p9788899999993,p899995999999,p1859999999999,p5999799999797,p9688999999993,p9896599999997,p989998899899,p4887899999999,p998999989997,p999994999999,p9499999999991,p9496889999999,p896999999999,p9994996999997,p9729999999997,p8888999999993,p6299989999999,p3998989999997] (by decide +kernel)

private theorem block916 : covers 916 940 :=
  block 916 [p959999999999,p7799999999993,p43869998999999,p6998939999999,p2599999999999,p7988998899997,p1999988999989,p7779998899999,p9897999999991,p8689989999997,p69748899999997,p9278999999999,p9699199999999,p5989988999899,p59988889999991,p2999999969999,p38779899799999,p5979999999997,p8899989898889,p9659999899999,p9989888999897,p9894988999999,p9889899999779,p9849999999997] (by decide +kernel)

private theorem block940 : covers 940 964 :=
  block 940 [p9798997999997,p7999999999991,p9999989986997,p9996499999999,p6799979999999,p79888988999993,p6896999999999,p3998899999999,p8959999999997,p7999999999993,p17993999999999,p38869999999997,p9969599999999,p44898998999999,p8849999999999,p999999999899,p7999499999999,p27998888999999,p99997799799991,p8299999999999,p96789999999991,p69896898999997,p967689889999991,p27689999999999] (by decide +kernel)

private theorem block964 : covers 964 988 :=
  block 964 [p8999999999993,p89959979799997,p99975999999991,p58986999999997,p8999888989999,p74989999998889,p9989998899997,p79898998999991,p8779999999999,p9919999999999,p9689998999999,p89989969999991,p7699999999999,p38998989999889,p87869699999999,p39899898999997,p5989999999999,p87997999999993,p99993999999991,p96998899999993,p58699999999997,p9899899899899,p48998989999997,p9898999999997] (by decide +kernel)

private theorem block988 : covers 988 1012 :=
  block 988 [p9999999499999,p9999779999999,p88949699999999,p8999999969999,p69999949999997,p99972999999997,p88939898999999,p62899999999999,p89987999999993,p9999599999999,p97399999999997,p991599999999991,p69399899999999,p347699999999999,p97989899988997,p88989999999991,p78897997999999,p81999999999997,p59399999999999,p339999799999997,p89697999979999,p69919999999999,p59899898899999,p799799999898883] (by decide +kernel)

private theorem block1012 : covers 1012 1025 :=
  block 1012 [p96969999999997,p598879999999991,p77995999999999,p88988998988999,p69599899999999,p98799988889999,p48998899999999,p8998999999999,p48999999999997,p9979999999999,p19999999999997,p99698998999997,p64999999999999] (by decide +kernel)

private theorem initial : covers 4 1025 := (join (join (join (join (join (join block4 block28) (join block52 block76)) (join (join block100 block124) (join block148 block172))) (join (join (join block196 block220) (join block244 block268)) (join (join block292 block316) (join block340 block364)))) (join (join (join (join block388 block412) (join block436 block460)) (join (join block484 block508) (join block532 block556))) (join (join (join block580 block604) (join block628 block652)) (join (join block676 block700) (join block724 block748))))) (join (join (join (join block772 block796) (join block820 block844)) (join (join block868 block892) (join block916 block940))) (join (join block964 block988) block1012)))

theorem through_1024 (n : ℕ) (positive : 0<n) (bound : n≤1024) :
    (∃ p : ℕ, p.Prime ∧ squareSum p=n) ↔ n≠1 ∧ n≠3 := by
  constructor
  · rintro ⟨p,prime,rfl⟩
    exact exceptions p prime
  · rintro ⟨one,three⟩
    by_cases two : n=2
    · subst n
      exact ⟨11,by decide,by decide +kernel⟩
    · exact initial n (by omega) (by omega)

end DigitSquarePrimes
