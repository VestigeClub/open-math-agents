import certificates.«tail-sieve-11092009835083-17747-17881»
import certificates.«tail-sieve-11092009835083-17881-17977»
import certificates.«tail-sieve-11092009835083-17977-18089»
import certificates.«tail-sieve-11092009835083-18089-18199»
import certificates.«tail-sieve-11092009835083-18199-18301»
import certificates.«tail-sieve-11092009835083-18301-18413»
import certificates.«tail-sieve-11092009835083-18413-18481»

/-! Exact changes for the consecutive sieve primes from 17,747 to 18,481. -/
namespace TailSeries11092009835083From17747To18481

private theorem to17977 : FinalSeventhSieve.rough 11092009835083 17977+789358890=FinalSeventhSieve.rough 11092009835083 17747 :=
  LargeQuotientSieve.combine Tail11092009835083From17747To17881.change Tail11092009835083From17881To17977.change rfl

private theorem to18089 : FinalSeventhSieve.rough 11092009835083 18089+1180155191=FinalSeventhSieve.rough 11092009835083 17747 :=
  LargeQuotientSieve.combine to17977 Tail11092009835083From17977To18089.change rfl

private theorem to18199 : FinalSeventhSieve.rough 11092009835083 18199+1568371391=FinalSeventhSieve.rough 11092009835083 17747 :=
  LargeQuotientSieve.combine to18089 Tail11092009835083From18089To18199.change rfl

private theorem to18301 : FinalSeventhSieve.rough 11092009835083 18301+1954162004=FinalSeventhSieve.rough 11092009835083 17747 :=
  LargeQuotientSieve.combine to18199 Tail11092009835083From18199To18301.change rfl

private theorem to18413 : FinalSeventhSieve.rough 11092009835083 18413+2337558413=FinalSeventhSieve.rough 11092009835083 17747 :=
  LargeQuotientSieve.combine to18301 Tail11092009835083From18301To18413.change rfl

theorem change : FinalSeventhSieve.rough 11092009835083 18481+2591779797=FinalSeventhSieve.rough 11092009835083 17747 :=
  LargeQuotientSieve.combine to18413 Tail11092009835083From18413To18481.change rfl

end TailSeries11092009835083From17747To18481
