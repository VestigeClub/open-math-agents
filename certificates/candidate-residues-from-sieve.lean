import certificates.«candidate-rank-limits»
import certificates.«seventh-prime-count-sieve-criterion»

/-!
# Endpoint residues for the 82 candidate indices

The first six residues follow from the checked exact counts. After these
endpoints, the candidate test asks for just the seventh sieve remainder and
the eighth prime-count remainder.
-/
namespace CandidateEndpointResidues

private theorem six_values (a b c d e f : ℕ)
    (ha : a=5439846) (hb : b=30841326) (hc : c=473516370)
    (hd : d=1217243858) (he : e=8190661670) (hf : f=21351698638) :
    a%6=0 ∧ b%7=5 ∧ c%11=8 ∧ d%3=2 ∧ e%5=0 ∧ f%6=4 := by
  subst_vars
  decide

theorem first_six :
    Nat.primeCounting 94085731 % 6 = 0 ∧ Nat.primeCounting 590237761 % 7 = 5 ∧
    Nat.primeCounting 10425579253 % 11 = 8 ∧ Nat.primeCounting 28006150079 % 3 = 2 ∧
    Nat.primeCounting 204778727327 % 5 = 0 ∧ Nat.primeCounting 555157672301 % 6 = 4 :=
  six_values _ _ _ _ _ _ JointRankWheel94.first_anchor RankWheel590.first_anchor
    JointEndpoint10425.exact_count JointEndpoint28006.exact_count
    JointExactSieve204778727327At5894.prime_count JointExactSieve555157672301At8218.prime_count

def sieveResidue (x y modulus value : ℕ) : Prop :=
  ((Finset.Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card%modulus=value

private theorem convert_sieve (x y : ℕ) (h : SeventhEndpointSieve.criterion x y) :
    sieveResidue x y 9 1 →
      Nat.primeCounting x%9=7 :=
  h.2.1.mpr

theorem remaining_tests (seventh : sieveResidue 11092009835083 22301 9 1)
    (eighth : Nat.primeCounting 30110134441897 % 5 = 3) :
    ∀ e ∈ CandidateRankLimits.candidates, AbsoluteCandidateRanks.excluded e :=
  CandidateRankLimits.candidate_bounds.2.2.2
    (convert_sieve 11092009835083 22301 SeventhEndpointSieve.prime_count_and_residue seventh) eighth

end CandidateEndpointResidues
