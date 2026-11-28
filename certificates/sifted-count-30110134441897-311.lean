import certificates.«sieve-change-30110134441897-0-53»
import certificates.«sieve-change-30110134441897-53-89-traced»
import certificates.«sieve-change-30110134441897-89-131-traced»
import certificates.«sieve-change-30110134441897-131-173-sides»
import certificates.«sieve-change-30110134441897-173-223-sides»
import certificates.«sieve-change-30110134441897-223-263-sides»
import certificates.«sieve-change-30110134441897-263-311-sides»

/-! Chains the consecutive verified sieve intervals at 30,110,134,441,897. -/
open Finset
namespace Sifted30110134441897At311

private theorem at24 : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 89, ¬ p ∣ n)).card=3660506971930 := by
  rw [TracedLookup65536P127IndexedSlicedSieveA30From16To24.exact_change,SieveA30From0To16.survivors]

private theorem at32 : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 131, ¬ p ∣ n)).card=3402359027723 := by
  rw [TracedLookup65536P127IndexedSlicedSieveA30From24To32.exact_change,at24]

private theorem at40 : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 173, ¬ p ∣ n)).card=3229080363077 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA30From32To40.exact_change,at32]

private theorem at48 : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 223, ¬ p ∣ n)).card=3099492687276 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA30From40To48.exact_change,at40]

private theorem at56 : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 263, ¬ p ∣ n)).card=2998445004991 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA30From48To56.exact_change,at48]

theorem survivors : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 311, ¬ p ∣ n)).card=2915518734708 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA30From56To64.exact_change,at56]

end Sifted30110134441897At311
