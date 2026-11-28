import certificates.«sieve-change-30110134441897-0-53»
import certificates.«sieve-change-30110134441897-53-89-traced»
import certificates.«sieve-change-30110134441897-89-131-traced»

/-! Chains the consecutive verified sieve intervals at 30,110,134,441,897. -/
open Finset
namespace Sifted30110134441897At131

private theorem at24 : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 89, ¬ p ∣ n)).card=3660506971930 := by
  rw [TracedLookup65536P127IndexedSlicedSieveA30From16To24.exact_change,SieveA30From0To16.survivors]

theorem survivors : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 131, ¬ p ∣ n)).card=3402359027723 := by
  rw [TracedLookup65536P127IndexedSlicedSieveA30From24To32.exact_change,at24]

end Sifted30110134441897At131
