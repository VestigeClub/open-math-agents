import certificates.«sieve-change-11092009835083-0-53»
import certificates.«sieve-change-11092009835083-53-131»
import certificates.«sieve-change-11092009835083-131-173-traced»
import certificates.«sieve-change-11092009835083-173-223-traced»
import certificates.«sieve-change-11092009835083-223-263-sides»
import certificates.«sieve-change-11092009835083-263-311-sides»
import certificates.«sieve-change-11092009835083-311-359-sides»
import certificates.«sieve-change-11092009835083-359-409-sides»
import certificates.«sieve-change-11092009835083-409-433-sides»
import certificates.«sieve-change-11092009835083-433-457-sides»
import certificates.«sieve-change-11092009835083-457-479-sides»
import certificates.«sieve-change-11092009835083-479-503-sides»
import certificates.«sieve-change-11092009835083-503-541-sides»
import certificates.«sieve-change-11092009835083-541-569-sides»
import certificates.«sieve-change-11092009835083-569-593-sides»
import certificates.«sieve-change-11092009835083-593-613-sides»

/-! Chains the consecutive verified sieve intervals at 11,092,009,835,083. -/
open Finset
namespace Sifted11092009835083At613

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

private theorem at80 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 409, ¬ p ∣ n)).card=1027334740054 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From72To80.exact_change,at72]

private theorem at84 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 433, ¬ p ∣ n)).card=1017723530861 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From80To84.exact_change,at80]

private theorem at88 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 457, ¬ p ∣ n)).card=1008648508526 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From84To88.exact_change,at84]

private theorem at92 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 479, ¬ p ∣ n)).card=1000048227487 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From88To92.exact_change,at88]

private theorem at96 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 503, ¬ p ∣ n)).card=991994563214 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From92To96.exact_change,at92]

private theorem at100 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 541, ¬ p ∣ n)).card=984437517230 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From96To100.exact_change,at96]

private theorem at104 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 569, ¬ p ∣ n)).card=977415163818 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From100To104.exact_change,at100]

private theorem at108 : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 593, ¬ p ∣ n)).card=970717876842 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From104To108.exact_change,at104]

theorem survivors : ((Icc 1 11092009835083).filter (fun n => ∀ p ∈ Nat.primesLE 613, ¬ p ∣ n)).card=964319646092 := by
  rw [SideCertificates65536P127IndexedSlicedSieveA29From108To112.exact_change,at108]

end Sifted11092009835083At613
