import certificates.«semiprime-correction-555157672301-middle»

/-!
# The two primes in the prescribed A247824 witness

The first index and both primality certificates are unconditional. The large
index follows once the remaining absolute prime count is known.
-/
namespace PrescribedPrimeWitness

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

private def p11 : Certified := ⟨11,by decide +kernel⟩

private def p13 : Certified := ⟨13,by decide +kernel⟩

private def p17 : Certified := ⟨17,by decide +kernel⟩

private def p167 : Certified := ⟨167,by decide +kernel⟩

private def p251 : Certified := ⟨251,by decide +kernel⟩

private def p331 : Certified := ⟨331,by decide +kernel⟩

private def p503 := certifiedPrime 503 5 [(p2,1),(p251,1)] (by decide +kernel)

private def p2593 := certifiedPrime 2593 7 [(p2,5),(p3,4)] (by decide +kernel)

private def p11969 := certifiedPrime 11969 3 [(p2,6),(p11,1),(p17,1)] (by decide +kernel)

private def p51637 := certifiedPrime 51637 5 [(p2,2),(p3,1),(p13,1),(p331,1)] (by decide +kernel)

private def p1579909 := certifiedPrime 1579909 2 [(p2,2),(p3,1),(p11,1),(p11969,1)] (by decide +kernel)

private def p2608559 := certifiedPrime 2608559 7 [(p2,1),(p503,1),(p2593,1)] (by decide +kernel)

private def p20868473 := certifiedPrime 20868473 3 [(p2,3),(p2608559,1)] (by decide +kernel)

private def p81744924555067 := certifiedPrime 81744924555067 2 [(p2,1),(p3,1),(p167,1),(p51637,1),(p1579909,1)] (by decide +kernel)

private theorem indexed {p n : ℕ} (pr : p.Prime) (rank : Nat.primeCounting p=n+1) :
    Nat.nth Nat.Prime n=p := by
  change Nat.count Nat.Prime (p+1)=n+1 at rank
  rw [Nat.count_succ,if_pos pr] at rank
  have e : Nat.count Nat.Prime p=n := by omega
  rw [←e,Nat.nth_count pr]

theorem first_count : Nat.primeCounting 20868473=1322164 :=
  (SparsePrimeA204.fast_correct 20868473 (by decide)).symm.trans (by decide +kernel)

theorem witness :
    Nat.nth Nat.Prime 1322163=20868473 ∧ Nat.Prime 81744924555067 ∧
    (Nat.primeCounting 81744924555067=2636932401176 →
      (2636932401176+1322164) ∣ Nat.nth Nat.Prime 2636932401175 + 20868473) := by
  refine ⟨indexed (p:=20868473) (n:=1322163) p20868473.property first_count,p81744924555067.property,?_⟩
  intro count
  rw [indexed (p:=81744924555067) (n:=2636932401175) p81744924555067.property count]
  exact ⟨31,rfl⟩

end PrescribedPrimeWitness
