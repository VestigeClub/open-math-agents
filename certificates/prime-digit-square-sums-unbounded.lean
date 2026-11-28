import certificates.«prime-digit-squares-through-1024»

/-!
# Primes with large decimal digit-square sums

For every length there are infinitely many primes ending in that many nines.
Their decimal digit-square sums are consequently unbounded.
-/
namespace DigitSquarePrimes

private lemma suffix (k n : ℕ) (div : 10^k ∣ n+1) : 81*k ≤ squareSum n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    obtain ⟨m,hm⟩ := div
    have product : n+1=10*(10^k*m) := by
      calc n+1 = 10^(k+1)*m := hm
           _ = 10*(10^k*m) := by rw [pow_succ]; ring
    have units : n%10=9 := by omega
    have rest : 10^k ∣ n/10+1 := ⟨m,by omega⟩
    have lower := ih (n/10) rest
    have nh : 0<n := by omega
    have expansion : squareSum n = 81 + squareSum (n/10) := by
      unfold squareSum
      rw [Nat.digits_def' (by decide : 1 < 10) nh,List.map_cons,List.sum_cons,units]
      rfl
    rw [expansion]
    omega

theorem many_primes (k : ℕ) : Set.Infinite {p : ℕ | p.Prime ∧ 81*k ≤ squareSum p} := by
  letI : NeZero (10^k : ℕ) := ⟨pow_ne_zero _ (by decide)⟩
  have many := Nat.infinite_setOfPred_prime_and_eq_mod (q:=10^k) (a:=-1) isUnit_one.neg
  apply many.mono
  rintro p ⟨hp,cong⟩
  refine ⟨hp,suffix k p ?_⟩
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  simp [cong]

theorem infinitely_many_attained :
    (∀ k : ℕ, Set.Infinite {p : ℕ | p.Prime ∧ 81*k ≤ squareSum p}) ∧
    Set.Infinite {s : ℕ | ∃ p : ℕ, p.Prime ∧ squareSum p=s} := by
  refine ⟨many_primes,?_⟩
  intro finite
  obtain ⟨b,bound⟩ := finite.bddAbove
  obtain ⟨p,hp,lower⟩ := (many_primes (b+1)).nonempty
  have ub := bound (show squareSum p ∈ {s : ℕ | ∃ q : ℕ, q.Prime ∧ squareSum q=s} from ⟨p,hp,rfl⟩)
  omega

end DigitSquarePrimes
