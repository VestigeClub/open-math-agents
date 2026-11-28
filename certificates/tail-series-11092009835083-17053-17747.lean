import certificates.«tail-sieve-11092009835083-17053-17191»
import certificates.«tail-sieve-11092009835083-17191-17327»
import certificates.«tail-sieve-11092009835083-17327-17419»
import certificates.«tail-sieve-11092009835083-17419-17519»
import certificates.«tail-sieve-11092009835083-17519-17657»
import certificates.«tail-sieve-11092009835083-17657-17747»

/-! Exact changes for the consecutive sieve primes from 17,053 to 17,747. -/
namespace TailSeries11092009835083From17053To17747

private theorem to17327 : FinalSeventhSieve.rough 11092009835083 17327+823137900=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine Tail11092009835083From17053To17191.change Tail11092009835083From17191To17327.change rfl

private theorem to17419 : FinalSeventhSieve.rough 11092009835083 17419+1230085345=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17327 Tail11092009835083From17327To17419.change rfl

private theorem to17519 : FinalSeventhSieve.rough 11092009835083 17519+1634490117=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17419 Tail11092009835083From17419To17519.change rfl

private theorem to17657 : FinalSeventhSieve.rough 11092009835083 17657+2036009003=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17519 Tail11092009835083From17519To17657.change rfl

theorem change : FinalSeventhSieve.rough 11092009835083 17747+2335106391=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17657 Tail11092009835083From17657To17747.change rfl

end TailSeries11092009835083From17053To17747
