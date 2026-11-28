import certificates.«tail-sieve-11092009835083-13049-13171»
import certificates.«tail-sieve-11092009835083-13171-13297»
import certificates.«tail-sieve-11092009835083-13297-13417»
import certificates.«tail-sieve-11092009835083-13417-13441»

/-! Exact changes for the consecutive sieve primes from 13,049 to 13,441. -/
namespace TailSeries11092009835083From13049To13441

private theorem to13297 : FinalSeventhSieve.rough 11092009835083 13297+1113608947=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine Tail11092009835083From13049To13171.change Tail11092009835083From13171To13297.change rfl

private theorem to13417 : FinalSeventhSieve.rough 11092009835083 13417+1661727096=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine to13297 Tail11092009835083From13297To13417.change rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13441+1752528242=FinalSeventhSieve.rough 11092009835083 13049 :=
  LargeQuotientSieve.combine to13417 Tail11092009835083From13417To13441.change rfl

end TailSeries11092009835083From13049To13441
