import certificates.«sieve-change-30110134441897-0-53»
import certificates.«sieve-change-30110134441897-53-89-traced»
import certificates.«sieve-change-30110134441897-89-131-traced»
import certificates.«sieve-change-30110134441897-131-173-sides»
import certificates.«sieve-change-30110134441897-173-223-sides»

/-! Chains the consecutive verified sieve intervals at 30,110,134,441,897. -/
open Finset
namespace Sifted30110134441897At223

private theorem at24 : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 89, ¬ p ∣ n)).card=3660506971930 := by
  rw [TracedLookup65536P127IndexedSlicedSieveA30From16To24.exact_change,SieveA30From0To16.survivors]

private theorem at32 : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 131, ¬ p ∣ n)).card=3402359027723 := by
  rw [TracedLookup65536P127IndexedSlicedSieveA30From24To32.exact_change,at24]

private theorem at40 : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 173, ¬ p ∣ n)).card=3229080363077 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA30From32To40.exact_change,at32]

theorem survivors : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 223, ¬ p ∣ n)).card=3099492687276 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA30From40To48.exact_change,at40]

end Sifted30110134441897At223
