import certificates.«sieve-change-204778727327-0-131»
import certificates.«sieve-change-204778727327-131-311»
import certificates.«sieve-change-204778727327-311-503»
import certificates.«sieve-change-204778727327-503-719»
import certificates.«sieve-change-204778727327-719-1163»
import certificates.«sieve-change-204778727327-1163-1423»
import certificates.«sieve-change-204778727327-1423-1619»
import certificates.«sieve-change-204778727327-1619-1877»
import certificates.«sieve-change-204778727327-1877-2129»
import certificates.«sieve-change-204778727327-2129-2377»
import certificates.«sieve-change-204778727327-2377-2657»
import certificates.«sieve-change-204778727327-2657-2861»
import certificates.«sieve-change-204778727327-2861-3167»
import certificates.«sieve-change-204778727327-3167-3413»
import certificates.«sieve-change-204778727327-3413-3671»
import certificates.«sieve-change-204778727327-3671-3923»
import certificates.«sieve-change-204778727327-3923-4211»
import certificates.«sieve-change-204778727327-4211-4481»
import certificates.«sieve-change-204778727327-4481-4751»
import certificates.«sieve-change-204778727327-4751-5011»
import certificates.«sieve-change-204778727327-5011-5309»
import certificates.«sieve-change-204778727327-5309-5573»
import certificates.«sieve-change-204778727327-5573-5743»
import certificates.«sieve-change-204778727327-5743-5894»
import certificates.«prime-count-204778727327-from-sieve»

/-!
# Exact sieve survivors through 5,894 at 204,778,727,327

Each imported interval proves the change in the count when its consecutive
primes are included. Chaining the intervals starts from all 204,778,727,327 integers.
-/
open Finset
namespace ExactSieve204778727327At5894

private theorem extend_count {before after removed old result : ℕ}
    (earlier : before=old) (interval : after=before-removed) (value : old-removed=result) :
    after=result := by rw [interval,earlier,value]

private theorem at0 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 0, ¬ p ∣ n)).card=204778727327 := by simp [Nat.primesLE]

private theorem at32 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 131, ¬ p ∣ n)).card=23139370842 :=
  extend_count (removed:=181639356485) at0 IndexedSlicedSieveA25From0To32.exact_change rfl

private theorem at64 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 311, ¬ p ∣ n)).card=19829341167 :=
  extend_count (removed:=3310029675) at32 IndexedSlicedSieveA25From32To64.exact_change rfl

private theorem at96 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 503, ¬ p ∣ n)).card=18312595695 :=
  extend_count (removed:=1516745472) at64 TracedLookup65536P127IndexedSlicedSieveA25From64To96.exact_change rfl

private theorem at128 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 719, ¬ p ∣ n)).card=17371230054 :=
  extend_count (removed:=941365641) at96 TracedLookup65536P127IndexedSlicedSieveA25From96To128.exact_change rfl

private theorem at192 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 1163, ¬ p ∣ n)).card=16202117024 :=
  extend_count (removed:=1169113030) at128 IndexedSlicedW17SieveA25From128To192.exact_change rfl

private theorem at224 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 1423, ¬ p ∣ n)).card=15802804278 :=
  extend_count (removed:=399312746) at192 Lookup16384P61IndexedSlicedSieveA25From192To224.exact_change rfl

private theorem at256 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 1619, ¬ p ∣ n)).card=15475920479 :=
  extend_count (removed:=326883799) at224 TracedLookup65536P127IndexedSlicedSieveA25From224To256.exact_change rfl

private theorem at288 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 1877, ¬ p ∣ n)).card=15200010270 :=
  extend_count (removed:=275910209) at256 TracedLookup65536P127IndexedSlicedSieveA25From256To288.exact_change rfl

private theorem at320 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 2129, ¬ p ∣ n)).card=14965298221 :=
  extend_count (removed:=234712049) at288 TracedLookup65536P127IndexedSlicedSieveA25From288To320.exact_change rfl

private theorem at352 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 2377, ¬ p ∣ n)).card=14761257544 :=
  extend_count (removed:=204040677) at320 TracedLookup65536P127IndexedSlicedSieveA25From320To352.exact_change rfl

private theorem at384 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 2657, ¬ p ∣ n)).card=14581299507 :=
  extend_count (removed:=179958037) at352 TracedLookup65536P127IndexedSlicedSieveA25From352To384.exact_change rfl

private theorem at416 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 2861, ¬ p ∣ n)).card=14420620501 :=
  extend_count (removed:=160679006) at384 TracedLookup65536P127IndexedSlicedSieveA25From384To416.exact_change rfl

private theorem at448 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 3167, ¬ p ∣ n)).card=14276376491 :=
  extend_count (removed:=144244010) at416 TracedLookup65536P127IndexedSlicedSieveA25From416To448.exact_change rfl

private theorem at480 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 3413, ¬ p ∣ n)).card=14146482200 :=
  extend_count (removed:=129894291) at448 TracedLookup65536P127IndexedSlicedSieveA25From448To480.exact_change rfl

private theorem at512 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 3671, ¬ p ∣ n)).card=14027669639 :=
  extend_count (removed:=118812561) at480 TracedLookup65536P127IndexedSlicedSieveA25From480To512.exact_change rfl

private theorem at544 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 3923, ¬ p ∣ n)).card=13918102275 :=
  extend_count (removed:=109567364) at512 TracedLookup65536P127IndexedSlicedSieveA25From512To544.exact_change rfl

private theorem at576 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 4211, ¬ p ∣ n)).card=13816740868 :=
  extend_count (removed:=101361407) at544 TracedLookup65536P127IndexedSlicedSieveA25From544To576.exact_change rfl

private theorem at608 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 4481, ¬ p ∣ n)).card=13722587164 :=
  extend_count (removed:=94153704) at576 TracedLookup65536P127IndexedSlicedSieveA25From576To608.exact_change rfl

private theorem at640 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 4751, ¬ p ∣ n)).card=13634766934 :=
  extend_count (removed:=87820230) at608 TracedLookup65536P127IndexedSlicedSieveA25From608To640.exact_change rfl

private theorem at672 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 5011, ¬ p ∣ n)).card=13552447922 :=
  extend_count (removed:=82319012) at640 TracedLookup65536P127IndexedSlicedSieveA25From640To672.exact_change rfl

private theorem at704 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 5309, ¬ p ∣ n)).card=13474647967 :=
  extend_count (removed:=77799955) at672 TracedLookup65536P127IndexedSlicedSieveA25From672To704.exact_change rfl

private theorem at736 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 5573, ¬ p ∣ n)).card=13401075222 :=
  extend_count (removed:=73572745) at704 TracedLookup65536P127IndexedSlicedSieveA25From704To736.exact_change rfl

private theorem at756 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 5743, ¬ p ∣ n)).card=13356843563 :=
  extend_count (removed:=44231659) at736 TracedLookup65536P127IndexedSlicedSieveA25From736To756.exact_change rfl

private theorem at775 : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 5894, ¬ p ∣ n)).card=13315926782 :=
  extend_count (removed:=40916781) at756 TracedLookup65536P127IndexedSlicedSieveA25From756To775.exact_change rfl

theorem survivors : ((Icc 1 204778727327).filter (fun n => ∀ p ∈ Nat.primesLE 5894, ¬ p ∣ n)).card=13315926782 := at775

theorem prime_count : Nat.primeCounting 204778727327=8190661670 := PrimeRank204778727327.from_sieve survivors

end ExactSieve204778727327At5894
