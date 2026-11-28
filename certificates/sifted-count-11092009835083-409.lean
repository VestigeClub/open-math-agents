import certificates.«sieve-change-11092009835083-0-53»
import certificates.«sieve-change-11092009835083-53-131»
import certificates.«sieve-change-11092009835083-131-173-traced»
import certificates.«sieve-change-11092009835083-173-223-traced»
import certificates.«sieve-change-11092009835083-223-263-sides»
import certificates.«sieve-change-11092009835083-263-311-sides»
import certificates.«sieve-change-11092009835083-311-359-sides»
import certificates.«sieve-change-11092009835083-359-409-sides»

/-! Chains the consecutive verified sieve intervals at 11,092,009,835,083. -/
open Finset
namespace Sifted11092009835083At409

private theorem at32 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 131, ¬ p ∣ n)).card=1253365407809 := by
  rw [SieveA29From16To32.exact_change,SieveA29From0To16.survivors]

private theorem at40 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 173, ¬ p ∣ n)).card=1189532412562 := by
  rw [TracedLookup65536P127IndexedSlicedSieveA29From32To40.exact_change,at32]

private theorem at48 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 223, ¬ p ∣ n)).card=1141794024212 := by
  rw [TracedLookup65536P127IndexedSlicedSieveA29From40To48.exact_change,at40]

private theorem at56 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 263, ¬ p ∣ n)).card=1104569774376 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From48To56.exact_change,at48]

private theorem at64 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 311, ¬ p ∣ n)).card=1074022348264 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From56To64.exact_change,at56]

private theorem at72 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 359, ¬ p ∣ n)).card=1048828523809 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From64To72.exact_change,at64]

theorem survivors : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 409, ¬ p ∣ n)).card=1027334740054 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From72To80.exact_change,at72]

end Sifted11092009835083At409
