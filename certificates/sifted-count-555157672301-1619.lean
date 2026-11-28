import certificates.«sieve-change-555157672301-0-131»
import certificates.«sieve-change-555157672301-131-311»
import certificates.«sieve-change-555157672301-311-409»
import certificates.«sieve-change-555157672301-409-503»
import certificates.«sieve-change-555157672301-503-719»
import certificates.«sieve-change-555157672301-719-941»
import certificates.«sieve-change-555157672301-941-1163»
import certificates.«sieve-change-555157672301-1163-1423»
import certificates.«sieve-change-555157672301-1423-1619»

/-!
# Exact sieve survivors through 1,619 at 555,157,672,301

Each imported interval proves the change in the count when its consecutive
primes are included. Chaining the intervals starts from all 555,157,672,301 integers.
-/
open Finset
namespace ExactSieve555157672301At1619

private theorem extend_count {before after removed old result : ℕ}
    (earlier : before=old) (interval : after=before-removed) (value : old-removed=result) :
    after=result := by rw [interval,earlier,value]

private theorem at0 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 0, ¬ p ∣ n)).card=555157672301 := by simp [Nat.primesLE]

private theorem at32 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 131, ¬ p ∣ n)).card=62731150861 :=
  extend_count (removed:=492426521440) at0 IndexedSlicedSieveA26From0To32.exact_change rfl

private theorem at64 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 311, ¬ p ∣ n)).card=53756847382 :=
  extend_count (removed:=8974303479) at32 IndexedSlicedSieveA26From32To64.exact_change rfl

private theorem at80 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 409, ¬ p ∣ n)).card=51420691153 :=
  extend_count (removed:=2336156229) at64 IndexedSlicedSieveA26From64To80.exact_change rfl

private theorem at96 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 503, ¬ p ∣ n)).card=49650273037 :=
  extend_count (removed:=1770418116) at80 TracedLookup65536P127IndexedSlicedSieveA26From80To96.exact_change rfl

private theorem at128 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 719, ¬ p ∣ n)).card=47104688605 :=
  extend_count (removed:=2545584432) at96 TracedLookup65536P127IndexedSlicedSieveA26From96To128.exact_change rfl

private theorem at160 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 941, ¬ p ∣ n)).card=45302995644 :=
  extend_count (removed:=1801692961) at128 TracedLookup65536P127IndexedSlicedSieveA26From128To160.exact_change rfl

private theorem at192 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 1163, ¬ p ∣ n)).card=43930535270 :=
  extend_count (removed:=1372460374) at160 TracedLookup65536P127IndexedSlicedSieveA26From160To192.exact_change rfl

private theorem at224 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 1423, ¬ p ∣ n)).card=42839992537 :=
  extend_count (removed:=1090542733) at192 TracedLookup65536P127IndexedSlicedSieveA26From192To224.exact_change rfl

private theorem at256 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 1619, ¬ p ∣ n)).card=41944310304 :=
  extend_count (removed:=895682233) at224 TracedLookup65536P127IndexedSlicedSieveA26From224To256.exact_change rfl

theorem survivors : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 1619, ¬ p ∣ n)).card=41944310304 := at256

end ExactSieve555157672301At1619
