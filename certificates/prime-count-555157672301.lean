import certificates.«sieve-change-555157672301-0-131»
import certificates.«sieve-change-555157672301-131-311»
import certificates.«sieve-change-555157672301-311-409»
import certificates.«sieve-change-555157672301-409-503»
import certificates.«sieve-change-555157672301-503-719»
import certificates.«sieve-change-555157672301-719-941»
import certificates.«sieve-change-555157672301-941-1163»
import certificates.«sieve-change-555157672301-1163-1423»
import certificates.«sieve-change-555157672301-1423-1619»
import certificates.«sieve-change-555157672301-1619-1877»
import certificates.«sieve-change-555157672301-1877-2129»
import certificates.«sieve-change-555157672301-2129-2377»
import certificates.«sieve-change-555157672301-2377-2657»
import certificates.«sieve-change-555157672301-2657-2861»
import certificates.«sieve-change-555157672301-2861-3167»
import certificates.«sieve-change-555157672301-3167-3413»
import certificates.«sieve-change-555157672301-3413-3671»
import certificates.«sieve-change-555157672301-3671-3923»
import certificates.«sieve-change-555157672301-3923-4211»
import certificates.«sieve-change-555157672301-4211-4481»
import certificates.«sieve-change-555157672301-4481-4751»
import certificates.«sieve-change-555157672301-4751-5011»
import certificates.«sieve-change-555157672301-5011-5309»
import certificates.«sieve-change-555157672301-5309-5573»
import certificates.«sieve-change-555157672301-5573-5849»
import certificates.«sieve-change-555157672301-5849-6133»
import certificates.«sieve-change-555157672301-6133-6379»
import certificates.«sieve-change-555157672301-6379-6701»
import certificates.«sieve-change-555157672301-6701-6971»
import certificates.«sieve-change-555157672301-6971-7253»
import certificates.«sieve-change-555157672301-7253-7561»
import certificates.«sieve-change-555157672301-7561-7853»
import certificates.«sieve-change-555157672301-7853-8017»
import certificates.«sieve-change-555157672301-8017-8218»
import certificates.«prime-count-555157672301-from-sieve»

/-!
# Exact sieve survivors through 8,218 at 555,157,672,301

Each imported interval proves the change in the count when its consecutive
primes are included. Chaining the intervals starts from all 555,157,672,301 integers.
-/
open Finset
namespace ExactSieve555157672301At8218

private theorem extend_count {before after removed old result : ℕ}
    (earlier : before=old) (interval : after=before-removed) (value : old-removed=result) :
    after=result := by rw [interval,earlier,value]

private theorem at0 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 0, ¬ p ∣ n)).card=555157672301 := by simp [Nat.primesLE]

private theorem at32 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 131, ¬ p ∣ n)).card=62731150861 :=
  extend_count (removed:=492426521440) at0 IndexedSlicedSieveA26From0To32.exact_change rfl

private theorem at64 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 311, ¬ p ∣ n)).card=53756847382 :=
  extend_count (removed:=8974303479) at32 IndexedSlicedSieveA26From32To64.exact_change rfl

private theorem at80 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 409, ¬ p ∣ n)).card=51420691153 :=
  extend_count (removed:=2336156229) at64 IndexedSlicedSieveA26From64To80.exact_change rfl

private theorem at96 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 503, ¬ p ∣ n)).card=49650273037 :=
  extend_count (removed:=1770418116) at80 TracedLookup65536P127IndexedSlicedSieveA26From80To96.exact_change rfl

private theorem at128 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 719, ¬ p ∣ n)).card=47104688605 :=
  extend_count (removed:=2545584432) at96 TracedLookup65536P127IndexedSlicedSieveA26From96To128.exact_change rfl

private theorem at160 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 941, ¬ p ∣ n)).card=45302995644 :=
  extend_count (removed:=1801692961) at128 TracedLookup65536P127IndexedSlicedSieveA26From128To160.exact_change rfl

private theorem at192 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 1163, ¬ p ∣ n)).card=43930535270 :=
  extend_count (removed:=1372460374) at160 TracedLookup65536P127IndexedSlicedSieveA26From160To192.exact_change rfl

private theorem at224 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 1423, ¬ p ∣ n)).card=42839992537 :=
  extend_count (removed:=1090542733) at192 TracedLookup65536P127IndexedSlicedSieveA26From192To224.exact_change rfl

private theorem at256 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 1619, ¬ p ∣ n)).card=41944310304 :=
  extend_count (removed:=895682233) at224 TracedLookup65536P127IndexedSlicedSieveA26From224To256.exact_change rfl

private theorem at288 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 1877, ¬ p ∣ n)).card=41186107749 :=
  extend_count (removed:=758202555) at256 TracedLookup65536P127IndexedSlicedSieveA26From256To288.exact_change rfl

private theorem at320 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 2129, ¬ p ∣ n)).card=40539443591 :=
  extend_count (removed:=646664158) at288 TracedLookup65536P127IndexedSlicedSieveA26From288To320.exact_change rfl

private theorem at352 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 2377, ¬ p ∣ n)).card=39976090228 :=
  extend_count (removed:=563353363) at320 TracedLookup65536P127IndexedSlicedSieveA26From320To352.exact_change rfl

private theorem at384 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 2657, ¬ p ∣ n)).card=39478420820 :=
  extend_count (removed:=497669408) at352 TracedLookup65536P127IndexedSlicedSieveA26From352To384.exact_change rfl

private theorem at416 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 2861, ¬ p ∣ n)).card=39033578759 :=
  extend_count (removed:=444842061) at384 TracedLookup65536P127IndexedSlicedSieveA26From384To416.exact_change rfl

private theorem at448 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 3167, ¬ p ∣ n)).card=38633988006 :=
  extend_count (removed:=399590753) at416 TracedLookup65536P127IndexedSlicedSieveA26From416To448.exact_change rfl

private theorem at480 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 3413, ¬ p ∣ n)).card=38274184160 :=
  extend_count (removed:=359803846) at448 TracedLookup65536P127IndexedSlicedSieveA26From448To480.exact_change rfl

private theorem at512 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 3671, ¬ p ∣ n)).card=37945324760 :=
  extend_count (removed:=328859400) at480 TracedLookup65536P127IndexedSlicedSieveA26From480To512.exact_change rfl

private theorem at544 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 3923, ¬ p ∣ n)).card=37642491905 :=
  extend_count (removed:=302832855) at512 TracedLookup65536P127IndexedSlicedSieveA26From512To544.exact_change rfl

private theorem at576 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 4211, ¬ p ∣ n)).card=37362978589 :=
  extend_count (removed:=279513316) at544 TracedLookup65536P127IndexedSlicedSieveA26From544To576.exact_change rfl

private theorem at608 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 4481, ¬ p ∣ n)).card=37104157589 :=
  extend_count (removed:=258821000) at576 TracedLookup65536P127IndexedSlicedSieveA26From576To608.exact_change rfl

private theorem at640 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 4751, ¬ p ∣ n)).card=36863708679 :=
  extend_count (removed:=240448910) at608 TracedLookup65536P127IndexedSlicedSieveA26From608To640.exact_change rfl

private theorem at672 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 5011, ¬ p ∣ n)).card=36639460965 :=
  extend_count (removed:=224247714) at640 TracedLookup65536P127IndexedSlicedSieveA26From640To672.exact_change rfl

private theorem at704 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 5309, ¬ p ∣ n)).card=36428781775 :=
  extend_count (removed:=210679190) at672 TracedLookup65536P127IndexedSlicedSieveA26From672To704.exact_change rfl

private theorem at736 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 5573, ¬ p ∣ n)).card=36230944087 :=
  extend_count (removed:=197837688) at704 TracedLookup65536P127IndexedSlicedSieveA26From704To736.exact_change rfl

private theorem at768 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 5849, ¬ p ∣ n)).card=36043762937 :=
  extend_count (removed:=187181150) at736 TracedLookup65536P127IndexedSlicedSieveA26From736To768.exact_change rfl

private theorem at800 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 6133, ¬ p ∣ n)).card=35866200279 :=
  extend_count (removed:=177562658) at768 TracedLookup65536P127IndexedSlicedSieveA26From768To800.exact_change rfl

private theorem at832 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 6379, ¬ p ∣ n)).card=35697493669 :=
  extend_count (removed:=168706610) at800 TracedLookup65536P127IndexedSlicedSieveA26From800To832.exact_change rfl

private theorem at864 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 6701, ¬ p ∣ n)).card=35536860166 :=
  extend_count (removed:=160633503) at832 TracedLookup65536P127IndexedSlicedSieveA26From832To864.exact_change rfl

private theorem at896 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 6971, ¬ p ∣ n)).card=35383437456 :=
  extend_count (removed:=153422710) at864 TracedLookup65536P127IndexedSlicedSieveA26From864To896.exact_change rfl

private theorem at928 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 7253, ¬ p ∣ n)).card=35236346724 :=
  extend_count (removed:=147090732) at896 TracedLookup65536P127IndexedSlicedSieveA26From896To928.exact_change rfl

private theorem at960 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 7561, ¬ p ∣ n)).card=35095788557 :=
  extend_count (removed:=140558167) at928 TracedLookup65536P127IndexedSlicedSieveA26From928To960.exact_change rfl

private theorem at992 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 7853, ¬ p ∣ n)).card=34960057875 :=
  extend_count (removed:=135730682) at960 TracedLookup65536P127IndexedSlicedSieveA26From960To992.exact_change rfl

private theorem at1010 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 8017, ¬ p ∣ n)).card=34885927132 :=
  extend_count (removed:=74130743) at992 TracedLookup65536P127IndexedSlicedSieveA26From992To1010.exact_change rfl

private theorem at1029 : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 8218, ¬ p ∣ n)).card=34809393870 :=
  extend_count (removed:=76533262) at1010 TracedLookup65536P127IndexedSlicedSieveA26From1010To1029.exact_change rfl

theorem survivors : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 8218, ¬ p ∣ n)).card=34809393870 := at1029

theorem prime_count : Nat.primeCounting 555157672301=21351698638 := PrimeRank555157672301.from_sieve survivors

end ExactSieve555157672301At8218
