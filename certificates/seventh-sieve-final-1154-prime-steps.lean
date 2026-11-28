import certificates.«seventh-sieve-last-381-prime-steps»
import certificates.«tail-series-11092009835083-11087-11369»
import certificates.«tail-series-11092009835083-11369-11657»
import certificates.«tail-series-11092009835083-11657-11987»
import certificates.«tail-series-11092009835083-11987-12323»
import certificates.«tail-series-11092009835083-12323-12671»
import certificates.«tail-series-11092009835083-12671-13049»
import certificates.«tail-series-11092009835083-13049-13441»
import certificates.«tail-series-11092009835083-13441-13859»
import certificates.«tail-series-11092009835083-13859-14303»
import certificates.«tail-series-11092009835083-14303-14783»
import certificates.«tail-series-11092009835083-14783-15299»
import certificates.«tail-series-11092009835083-15299-15823»
import certificates.«tail-series-11092009835083-15823-16427»
import certificates.«tail-series-11092009835083-16427-17053»
import certificates.«tail-series-11092009835083-17053-17747»
import certificates.«tail-series-11092009835083-17747-18481»

/-! The final 1154 prime removals in the seventh endpoint sieve, using separately kernel-checked interval proofs. -/

namespace FinalSeventhSieve

private theorem from11087to11657_by_intervals : rough 11092009835083 11657+3091103131=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine TailSeries11092009835083From11087To11369.change TailSeries11092009835083From11369To11657.change rfl

private theorem from11087to11987_by_intervals : rough 11092009835083 11987+5091165399=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to11657_by_intervals TailSeries11092009835083From11657To11987.change rfl

private theorem from11087to12323_by_intervals : rough 11092009835083 12323+6824441786=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to11987_by_intervals TailSeries11092009835083From11987To12323.change rfl

private theorem from11087to12671_by_intervals : rough 11092009835083 12671+8896694550=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to12323_by_intervals TailSeries11092009835083From12323To12671.change rfl

private theorem from11087to13049_by_intervals : rough 11092009835083 13049+10851108895=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to12671_by_intervals TailSeries11092009835083From12671To13049.change rfl

private theorem from11087to13441_by_intervals : rough 11092009835083 13441+12603637137=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to13049_by_intervals TailSeries11092009835083From13049To13441.change rfl

private theorem from11087to13859_by_intervals : rough 11092009835083 13859+14563512415=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to13441_by_intervals TailSeries11092009835083From13441To13859.change rfl

private theorem from11087to14303_by_intervals : rough 11092009835083 14303+16328600270=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to13859_by_intervals TailSeries11092009835083From13859To14303.change rfl

private theorem from11087to14783_by_intervals : rough 11092009835083 14783+18604664920=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to14303_by_intervals TailSeries11092009835083From14303To14783.change rfl

private theorem from11087to15299_by_intervals : rough 11092009835083 15299+20754977321=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to14783_by_intervals TailSeries11092009835083From14783To15299.change rfl

private theorem from11087to15823_by_intervals : rough 11092009835083 15823+23054183486=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to15299_by_intervals TailSeries11092009835083From15299To15823.change rfl

private theorem from11087to16427_by_intervals : rough 11092009835083 16427+25152962872=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to15823_by_intervals TailSeries11092009835083From15823To16427.change rfl

private theorem from11087to17053_by_intervals : rough 11092009835083 17053+27412289297=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to16427_by_intervals TailSeries11092009835083From16427To17053.change rfl

private theorem from11087to17747_by_intervals : rough 11092009835083 17747+29747395688=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to17053_by_intervals TailSeries11092009835083From17053To17747.change rfl

private theorem from11087to18481_by_intervals : rough 11092009835083 18481+32339175485=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to17747_by_intervals TailSeries11092009835083From17747To18481.change rfl

theorem last_1154_by_intervals : rough 11092009835083 22301+43257996514=rough 11092009835083 11087 :=
  LargeQuotientSieve.combine from11087to18481_by_intervals FinalSeventhSieve.last_381 rfl

end FinalSeventhSieve
