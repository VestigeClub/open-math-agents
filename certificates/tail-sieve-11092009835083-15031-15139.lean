import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-725000000-750000000»

/-! Exact changes for sieve primes 1758 through 1769. -/
open Finset
namespace Tail11092009835083From15031To15139

set_option maxRecDepth 16000 in
private theorem row15053 :
    FinalSeventhSieve.rough 11092009835083 15053+39834835=FinalSeventhSieve.rough 11092009835083 15031 :=
  LargeQuotientSieve.row (p:=15053) (q:=736863737) (s:=27145) (rank:=38060291) (tiny:=1757) (pairs:=1776300)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 736863737 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row15061 :
    FinalSeventhSieve.rough 11092009835083 15061+39810163=FinalSeventhSieve.rough 11092009835083 15053 :=
  LargeQuotientSieve.row (p:=15061) (q:=736472334) (s:=27138) (rank:=38041055) (tiny:=1758) (pairs:=1770865)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 736472334 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15061 : FinalSeventhSieve.rough 11092009835083 15061+79644998=FinalSeventhSieve.rough 11092009835083 15031 :=
  LargeQuotientSieve.combine row15053 row15061 rfl

set_option maxRecDepth 16000 in
private theorem row15073 :
    FinalSeventhSieve.rough 11092009835083 15073+39774921=FinalSeventhSieve.rough 11092009835083 15061 :=
  LargeQuotientSieve.row (p:=15073) (q:=735886010) (s:=27127) (rank:=38012380) (tiny:=1759) (pairs:=1764299)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 735886010 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15073 : FinalSeventhSieve.rough 11092009835083 15073+119419919=FinalSeventhSieve.rough 11092009835083 15031 :=
  LargeQuotientSieve.combine to15061 row15073 rfl

set_option maxRecDepth 16000 in
private theorem row15077 :
    FinalSeventhSieve.rough 11092009835083 15077+39761005=FinalSeventhSieve.rough 11092009835083 15073 :=
  LargeQuotientSieve.row (p:=15077) (q:=735690776) (s:=27123) (rank:=38002813) (tiny:=1760) (pairs:=1759951)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 735690776 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15077 : FinalSeventhSieve.rough 11092009835083 15077+159180924=FinalSeventhSieve.rough 11092009835083 15031 :=
  LargeQuotientSieve.combine to15073 row15077 rfl

set_option maxRecDepth 16000 in
private theorem row15083 :
    FinalSeventhSieve.rough 11092009835083 15083+39741776=FinalSeventhSieve.rough 11092009835083 15077 :=
  LargeQuotientSieve.row (p:=15083) (q:=735398119) (s:=27118) (rank:=37988483) (tiny:=1761) (pairs:=1755053)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 735398119 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15083 : FinalSeventhSieve.rough 11092009835083 15083+198922700=FinalSeventhSieve.rough 11092009835083 15031 :=
  LargeQuotientSieve.combine to15077 row15083 rfl

set_option maxRecDepth 16000 in
private theorem row15091 :
    FinalSeventhSieve.rough 11092009835083 15091+39717240=FinalSeventhSieve.rough 11092009835083 15083 :=
  LargeQuotientSieve.row (p:=15091) (q:=735008272) (s:=27111) (rank:=37969376) (tiny:=1762) (pairs:=1749625)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 735008272 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15091 : FinalSeventhSieve.rough 11092009835083 15091+238639940=FinalSeventhSieve.rough 11092009835083 15031 :=
  LargeQuotientSieve.combine to15083 row15091 rfl

set_option maxRecDepth 16000 in
private theorem row15101 :
    FinalSeventhSieve.rough 11092009835083 15101+39687438=FinalSeventhSieve.rough 11092009835083 15091 :=
  LargeQuotientSieve.row (p:=15101) (q:=734521543) (s:=27102) (rank:=37945561) (tiny:=1763) (pairs:=1743639)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 734521543 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15101 : FinalSeventhSieve.rough 11092009835083 15101+278327378=FinalSeventhSieve.rough 11092009835083 15031 :=
  LargeQuotientSieve.combine to15091 row15101 rfl

set_option maxRecDepth 16000 in
private theorem row15107 :
    FinalSeventhSieve.rough 11092009835083 15107+39668289=FinalSeventhSieve.rough 11092009835083 15101 :=
  LargeQuotientSieve.row (p:=15107) (q:=734229816) (s:=27096) (rank:=37931287) (tiny:=1764) (pairs:=1738765)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 734229816 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15107 : FinalSeventhSieve.rough 11092009835083 15107+317995667=FinalSeventhSieve.rough 11092009835083 15031 :=
  LargeQuotientSieve.combine to15101 row15107 rfl

set_option maxRecDepth 16000 in
private theorem row15121 :
    FinalSeventhSieve.rough 11092009835083 15121+39628038=FinalSeventhSieve.rough 11092009835083 15107 :=
  LargeQuotientSieve.row (p:=15121) (q:=733550018) (s:=27084) (rank:=37898072) (tiny:=1765) (pairs:=1731730)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 733550018 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15121 : FinalSeventhSieve.rough 11092009835083 15121+357623705=FinalSeventhSieve.rough 11092009835083 15031 :=
  LargeQuotientSieve.combine to15107 row15121 rfl

set_option maxRecDepth 16000 in
private theorem row15131 :
    FinalSeventhSieve.rough 11092009835083 15131+39598288=FinalSeventhSieve.rough 11092009835083 15121 :=
  LargeQuotientSieve.row (p:=15131) (q:=733065219) (s:=27075) (rank:=37874279) (tiny:=1766) (pairs:=1725774)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 733065219 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15131 : FinalSeventhSieve.rough 11092009835083 15131+397221993=FinalSeventhSieve.rough 11092009835083 15031 :=
  LargeQuotientSieve.combine to15121 row15131 rfl

set_option maxRecDepth 16000 in
private theorem row15137 :
    FinalSeventhSieve.rough 11092009835083 15137+39579216=FinalSeventhSieve.rough 11092009835083 15131 :=
  LargeQuotientSieve.row (p:=15137) (q:=732774647) (s:=27069) (rank:=37860002) (tiny:=1767) (pairs:=1720980)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 732774647 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15137 : FinalSeventhSieve.rough 11092009835083 15137+436801209=FinalSeventhSieve.rough 11092009835083 15031 :=
  LargeQuotientSieve.combine to15131 row15137 rfl

set_option maxRecDepth 16000 in
private theorem row15139 :
    FinalSeventhSieve.rough 11092009835083 15139+39570737=FinalSeventhSieve.rough 11092009835083 15137 :=
  LargeQuotientSieve.row (p:=15139) (q:=732677841) (s:=27068) (rank:=37855280) (tiny:=1768) (pairs:=1717224)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ725000000To750000000.count_correct 732677841 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to15139 : FinalSeventhSieve.rough 11092009835083 15139+476371946=FinalSeventhSieve.rough 11092009835083 15031 :=
  LargeQuotientSieve.combine to15137 row15139 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 15139+476371946=FinalSeventhSieve.rough 11092009835083 15031 := to15139

end Tail11092009835083From15031To15139
