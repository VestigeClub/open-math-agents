import certificates.«tail-sieve-30110134441897-28669-28793»
import certificates.«tail-sieve-30110134441897-28793-28921»
import certificates.«tail-sieve-30110134441897-28921-29059»
import certificates.«tail-sieve-30110134441897-29059-29179»
import certificates.«tail-sieve-30110134441897-29179-29303»
import certificates.«tail-sieve-30110134441897-29303-29363»

/-! Exact changes for the consecutive sieve primes from 28,669 to 29,363. -/
namespace TailSeries30110134441897From28669To29363

private theorem to28921 : FinalSeventhSieve.rough 30110134441897 28921+1275763866=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine Tail30110134441897From28669To28793.change Tail30110134441897From28793To28921.change rfl

private theorem to29059 : FinalSeventhSieve.rough 30110134441897 29059+1909338255=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to28921 Tail30110134441897From28921To29059.change rfl

private theorem to29179 : FinalSeventhSieve.rough 30110134441897 29179+2539945940=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to29059 Tail30110134441897From29059To29179.change rfl

private theorem to29303 : FinalSeventhSieve.rough 30110134441897 29303+3168161838=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to29179 Tail30110134441897From29179To29303.change rfl

theorem change : FinalSeventhSieve.rough 30110134441897 29363+3481267290=FinalSeventhSieve.rough 30110134441897 28669 :=
  LargeQuotientSieve.combine to29303 Tail30110134441897From29303To29363.change rfl

end TailSeries30110134441897From28669To29363
