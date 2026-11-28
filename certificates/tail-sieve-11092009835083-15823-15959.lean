import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-675000000-700000000»

/-! Exact changes for sieve primes 1848 through 1859. -/
open Finset
namespace Tail11092009835083From15823To15959

set_option maxRecDepth 16000 in
private theorem row15859 :
    FinalSeventhSieve.rough 11092009835083 15859+37530993=FinalSeventhSieve.rough 11092009835083 15823 :=
  LargeQuotientSieve.row (p:=15859) (q:=699414202) (s:=26446) (rank:=36224213) (tiny:=1847) (pairs:=1308626)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 699414202 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row15877 :
    FinalSeventhSieve.rough 11092009835083 15877+37485385=FinalSeventhSieve.rough 11092009835083 15859 :=
  LargeQuotientSieve.row (p:=15877) (q:=698621265) (s:=26431) (rank:=36185210) (tiny:=1848) (pairs:=1302022)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 698621265 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15877 : FinalSeventhSieve.rough 11092009835083 15877+75016378=FinalSeventhSieve.rough 11092009835083 15823 :=
  LargeQuotientSieve.combine row15859 row15877 rfl

set_option maxRecDepth 16000 in
private theorem row15881 :
    FinalSeventhSieve.rough 11092009835083 15881+37473152=FinalSeventhSieve.rough 11092009835083 15877 :=
  LargeQuotientSieve.row (p:=15881) (q:=698445301) (s:=26428) (rank:=36176553) (tiny:=1849) (pairs:=1298447)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 698445301 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15881 : FinalSeventhSieve.rough 11092009835083 15881+112489530=FinalSeventhSieve.rough 11092009835083 15823 :=
  LargeQuotientSieve.combine to15877 row15881 rfl

set_option maxRecDepth 16000 in
private theorem row15887 :
    FinalSeventhSieve.rough 11092009835083 15887+37456209=FinalSeventhSieve.rough 11092009835083 15881 :=
  LargeQuotientSieve.row (p:=15887) (q:=698181521) (s:=26423) (rank:=36163648) (tiny:=1850) (pairs:=1294410)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 698181521 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15887 : FinalSeventhSieve.rough 11092009835083 15887+149945739=FinalSeventhSieve.rough 11092009835083 15823 :=
  LargeQuotientSieve.combine to15881 row15887 rfl

set_option maxRecDepth 16000 in
private theorem row15889 :
    FinalSeventhSieve.rough 11092009835083 15889+37448821=FinalSeventhSieve.rough 11092009835083 15887 :=
  LargeQuotientSieve.row (p:=15889) (q:=698093639) (s:=26421) (rank:=36159407) (tiny:=1851) (pairs:=1291264)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 698093639 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15889 : FinalSeventhSieve.rough 11092009835083 15889+187394560=FinalSeventhSieve.rough 11092009835083 15823 :=
  LargeQuotientSieve.combine to15887 row15889 rfl

set_option maxRecDepth 16000 in
private theorem row15901 :
    FinalSeventhSieve.rough 11092009835083 15901+37417667=FinalSeventhSieve.rough 11092009835083 15889 :=
  LargeQuotientSieve.row (p:=15901) (q:=697566809) (s:=26411) (rank:=36133538) (tiny:=1852) (pairs:=1285980)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 697566809 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15901 : FinalSeventhSieve.rough 11092009835083 15901+224812227=FinalSeventhSieve.rough 11092009835083 15823 :=
  LargeQuotientSieve.combine to15889 row15901 rfl

set_option maxRecDepth 16000 in
private theorem row15907 :
    FinalSeventhSieve.rough 11092009835083 15907+37400842=FinalSeventhSieve.rough 11092009835083 15901 :=
  LargeQuotientSieve.row (p:=15907) (q:=697303692) (s:=26406) (rank:=36120716) (tiny:=1853) (pairs:=1281978)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 697303692 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15907 : FinalSeventhSieve.rough 11092009835083 15907+262213069=FinalSeventhSieve.rough 11092009835083 15823 :=
  LargeQuotientSieve.combine to15901 row15907 rfl

set_option maxRecDepth 16000 in
private theorem row15913 :
    FinalSeventhSieve.rough 11092009835083 15913+37383987=FinalSeventhSieve.rough 11092009835083 15907 :=
  LargeQuotientSieve.row (p:=15913) (q:=697040773) (s:=26401) (rank:=36107845) (tiny:=1854) (pairs:=1277995)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 697040773 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15913 : FinalSeventhSieve.rough 11092009835083 15913+299597056=FinalSeventhSieve.rough 11092009835083 15823 :=
  LargeQuotientSieve.combine to15907 row15913 rfl

set_option maxRecDepth 16000 in
private theorem row15919 :
    FinalSeventhSieve.rough 11092009835083 15919+37367095=FinalSeventhSieve.rough 11092009835083 15913 :=
  LargeQuotientSieve.row (p:=15919) (q:=696778053) (s:=26396) (rank:=36094951) (tiny:=1855) (pairs:=1273998)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 696778053 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15919 : FinalSeventhSieve.rough 11092009835083 15919+336964151=FinalSeventhSieve.rough 11092009835083 15823 :=
  LargeQuotientSieve.combine to15913 row15919 rfl

set_option maxRecDepth 16000 in
private theorem row15923 :
    FinalSeventhSieve.rough 11092009835083 15923+37354869=FinalSeventhSieve.rough 11092009835083 15919 :=
  LargeQuotientSieve.row (p:=15923) (q:=696603016) (s:=26393) (rank:=36086256) (tiny:=1856) (pairs:=1270468)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 696603016 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15923 : FinalSeventhSieve.rough 11092009835083 15923+374319020=FinalSeventhSieve.rough 11092009835083 15823 :=
  LargeQuotientSieve.combine to15919 row15923 rfl

set_option maxRecDepth 16000 in
private theorem row15937 :
    FinalSeventhSieve.rough 11092009835083 15937+37319282=FinalSeventhSieve.rough 11092009835083 15923 :=
  LargeQuotientSieve.row (p:=15937) (q:=695991079) (s:=26381) (rank:=36056275) (tiny:=1857) (pairs:=1264863)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 695991079 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15937 : FinalSeventhSieve.rough 11092009835083 15937+411638302=FinalSeventhSieve.rough 11092009835083 15823 :=
  LargeQuotientSieve.combine to15923 row15937 rfl

set_option maxRecDepth 16000 in
private theorem row15959 :
    FinalSeventhSieve.rough 11092009835083 15959+37264713=FinalSeventhSieve.rough 11092009835083 15937 :=
  LargeQuotientSieve.row (p:=15959) (q:=695031633) (s:=26363) (rank:=36008998) (tiny:=1858) (pairs:=1257572)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 695031633 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15959 : FinalSeventhSieve.rough 11092009835083 15959+448903015=FinalSeventhSieve.rough 11092009835083 15823 :=
  LargeQuotientSieve.combine to15937 row15959 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 15959+448903015=FinalSeventhSieve.rough 11092009835083 15823 := to15959

end Tail11092009835083From15823To15959
