import certificates.«tail-sieve-30110134441897-27367-27509»
import certificates.«tail-sieve-30110134441897-27509-27653»
import certificates.«tail-sieve-30110134441897-27653-27763»
import certificates.«tail-sieve-30110134441897-27763-27847»
import certificates.«tail-sieve-30110134441897-27847-27967»
import certificates.«tail-sieve-30110134441897-27967-28001»

/-! Exact changes for the consecutive sieve primes from 27,367 to 28,001. -/
namespace TailSeries30110134441897From27367To28001

private theorem to27653 : FinalSeventhSieve.rough 30110134441897 27653+1336673432=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine Tail30110134441897From27367To27509.change Tail30110134441897From27509To27653.change rfl

private theorem to27763 : FinalSeventhSieve.rough 30110134441897 27763+1999897626=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27653 Tail30110134441897From27653To27763.change rfl

private theorem to27847 : FinalSeventhSieve.rough 30110134441897 27847+2661096460=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27763 Tail30110134441897From27763To27847.change rfl

private theorem to27967 : FinalSeventhSieve.rough 30110134441897 27967+3319357381=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27847 Tail30110134441897From27847To27967.change rfl

theorem change : FinalSeventhSieve.rough 30110134441897 28001+3483495352=FinalSeventhSieve.rough 30110134441897 27367 :=
  LargeQuotientSieve.combine to27967 Tail30110134441897From27967To28001.change rfl

end TailSeries30110134441897From27367To28001
