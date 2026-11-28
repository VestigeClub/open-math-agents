import certificates.«sieve-change-11092009835083-0-53»
import certificates.«sieve-change-11092009835083-53-131»
import certificates.«sieve-change-11092009835083-131-173-traced»
import certificates.«sieve-change-11092009835083-173-223-traced»

/-! Chains the consecutive verified sieve intervals at 11,092,009,835,083. -/
open Finset
namespace Sifted11092009835083At223

private theorem at32 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 131, ¬ p ∣ n)).card=1253365407809 := by
  rw [SieveA29From16To32.exact_change,SieveA29From0To16.survivors]

private theorem at40 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 173, ¬ p ∣ n)).card=1189532412562 := by
  rw [TracedLookup65536P127IndexedSlicedSieveA29From32To40.exact_change,at32]

theorem survivors : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 223, ¬ p ∣ n)).card=1141794024212 := by
  rw [TracedLookup65536P127IndexedSlicedSieveA29From40To48.exact_change,at40]

end Sifted11092009835083At223
