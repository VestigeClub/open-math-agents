import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-725000000-750000000»

/-! Exact changes for sieve primes 1734 through 1745. -/
open Finset
namespace Tail11092009835083From14783To14891

set_option maxRecDepth 16000 in
private theorem row14797 :
    FinalSeventhSieve.rough 11092009835083 14797+40613179=FinalSeventhSieve.rough 11092009835083 14783 :=
  LargeQuotientSieve.row (p:=14797) (q:=749612072) (s:=27379) (rank:=38684109) (tiny:=1733) (pairs:=1930802)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 749612072 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row14813 :
    FinalSeventhSieve.rough 11092009835083 14813+40565419=FinalSeventhSieve.rough 11092009835083 14797 :=
  LargeQuotientSieve.row (p:=14813) (q:=748802392) (s:=27364) (rank:=38644535) (tiny:=1734) (pairs:=1922617)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 748802392 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14813 : FinalSeventhSieve.rough 11092009835083 14813+81178598=FinalSeventhSieve.rough 11092009835083 14783 :=
  LargeQuotientSieve.combine row14797 row14813 rfl

set_option maxRecDepth 16000 in
private theorem row14821 :
    FinalSeventhSieve.rough 11092009835083 14821+40539967=FinalSeventhSieve.rough 11092009835083 14813 :=
  LargeQuotientSieve.row (p:=14821) (q:=748398207) (s:=27356) (rank:=38624923) (tiny:=1735) (pairs:=1916778)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 748398207 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14821 : FinalSeventhSieve.rough 11092009835083 14821+121718565=FinalSeventhSieve.rough 11092009835083 14783 :=
  LargeQuotientSieve.combine to14813 row14821 rfl

set_option maxRecDepth 16000 in
private theorem row14827 :
    FinalSeventhSieve.rough 11092009835083 14827+40519882=FinalSeventhSieve.rough 11092009835083 14821 :=
  LargeQuotientSieve.row (p:=14827) (q:=748095355) (s:=27351) (rank:=38610073) (tiny:=1736) (pairs:=1911544)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 748095355 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14827 : FinalSeventhSieve.rough 11092009835083 14827+162238447=FinalSeventhSieve.rough 11092009835083 14783 :=
  LargeQuotientSieve.combine to14821 row14827 rfl

set_option maxRecDepth 16000 in
private theorem row14831 :
    FinalSeventhSieve.rough 11092009835083 14831+40505384=FinalSeventhSieve.rough 11092009835083 14827 :=
  LargeQuotientSieve.row (p:=14831) (q:=747893590) (s:=27347) (rank:=38600208) (tiny:=1737) (pairs:=1906912)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 747893590 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14831 : FinalSeventhSieve.rough 11092009835083 14831+202743831=FinalSeventhSieve.rough 11092009835083 14783 :=
  LargeQuotientSieve.combine to14827 row14831 rfl

set_option maxRecDepth 16000 in
private theorem row14843 :
    FinalSeventhSieve.rough 11092009835083 14843+40468792=FinalSeventhSieve.rough 11092009835083 14831 :=
  LargeQuotientSieve.row (p:=14843) (q:=747288946) (s:=27336) (rank:=38570569) (tiny:=1738) (pairs:=1899960)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 747288946 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14843 : FinalSeventhSieve.rough 11092009835083 14843+243212623=FinalSeventhSieve.rough 11092009835083 14783 :=
  LargeQuotientSieve.combine to14831 row14843 rfl

set_option maxRecDepth 16000 in
private theorem row14851 :
    FinalSeventhSieve.rough 11092009835083 14851+40443379=FinalSeventhSieve.rough 11092009835083 14843 :=
  LargeQuotientSieve.row (p:=14851) (q:=746886393) (s:=27329) (rank:=38550902) (tiny:=1739) (pairs:=1894215)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 746886393 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14851 : FinalSeventhSieve.rough 11092009835083 14851+283656002=FinalSeventhSieve.rough 11092009835083 14783 :=
  LargeQuotientSieve.combine to14843 row14851 rfl

set_option maxRecDepth 16000 in
private theorem row14867 :
    FinalSeventhSieve.rough 11092009835083 14867+40396080=FinalSeventhSieve.rough 11092009835083 14851 :=
  LargeQuotientSieve.row (p:=14867) (q:=746082587) (s:=27314) (rank:=38511707) (tiny:=1740) (pairs:=1886112)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 746082587 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14867 : FinalSeventhSieve.rough 11092009835083 14867+324052082=FinalSeventhSieve.rough 11092009835083 14783 :=
  LargeQuotientSieve.combine to14851 row14867 rfl

set_option maxRecDepth 16000 in
private theorem row14869 :
    FinalSeventhSieve.rough 11092009835083 14869+40387162=FinalSeventhSieve.rough 11092009835083 14867 :=
  LargeQuotientSieve.row (p:=14869) (q:=745982233) (s:=27312) (rank:=38506812) (tiny:=1741) (pairs:=1882090)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 745982233 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14869 : FinalSeventhSieve.rough 11092009835083 14869+364439244=FinalSeventhSieve.rough 11092009835083 14783 :=
  LargeQuotientSieve.combine to14867 row14869 rfl

set_option maxRecDepth 16000 in
private theorem row14879 :
    FinalSeventhSieve.rough 11092009835083 14879+40356354=FinalSeventhSieve.rough 11092009835083 14869 :=
  LargeQuotientSieve.row (p:=14879) (q:=745480868) (s:=27303) (rank:=38482329) (tiny:=1742) (pairs:=1875766)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 745480868 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14879 : FinalSeventhSieve.rough 11092009835083 14879+404795598=FinalSeventhSieve.rough 11092009835083 14783 :=
  LargeQuotientSieve.combine to14869 row14879 rfl

set_option maxRecDepth 16000 in
private theorem row14887 :
    FinalSeventhSieve.rough 11092009835083 14887+40331050=FinalSeventhSieve.rough 11092009835083 14879 :=
  LargeQuotientSieve.row (p:=14887) (q:=745080260) (s:=27296) (rank:=38462748) (tiny:=1743) (pairs:=1870044)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 745080260 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14887 : FinalSeventhSieve.rough 11092009835083 14887+445126648=FinalSeventhSieve.rough 11092009835083 14783 :=
  LargeQuotientSieve.combine to14879 row14887 rfl

set_option maxRecDepth 16000 in
private theorem row14891 :
    FinalSeventhSieve.rough 11092009835083 14891+40316708=FinalSeventhSieve.rough 11092009835083 14887 :=
  LargeQuotientSieve.row (p:=14891) (q:=744880117) (s:=27292) (rank:=38452933) (tiny:=1744) (pairs:=1865518)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 744880117 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14891 : FinalSeventhSieve.rough 11092009835083 14891+485443356=FinalSeventhSieve.rough 11092009835083 14783 :=
  LargeQuotientSieve.combine to14887 row14891 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 14891+485443356=FinalSeventhSieve.rough 11092009835083 14783 := to14891

end Tail11092009835083From14783To14891
