import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-1025000000-1050000000»

/-! Exact changes for sieve primes 1302 through 1313. -/
open Finset
namespace Tail11092009835083From10663To10781

set_option maxRecDepth 16000 in
private theorem row10667 :
    FinalSeventhSieve.rough 11092009835083 10667+59425836=FinalSeventhSieve.rough 11092009835083 10663 :=
  LargeQuotientSieve.row (p:=10667) (q:=1039843426) (s:=32246) (rank:=52768627) (tiny:=1301) (pairs:=6658509)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1039843426 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row10687 :
    FinalSeventhSieve.rough 11092009835083 10687+59304087=FinalSeventhSieve.rough 11092009835083 10667 :=
  LargeQuotientSieve.row (p:=10687) (q:=1037897430) (s:=32216) (rank:=52674697) (tiny:=1302) (pairs:=6630691)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1037897430 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10687 : FinalSeventhSieve.rough 11092009835083 10687+118729923=FinalSeventhSieve.rough 11092009835083 10663 :=
  LargeQuotientSieve.combine row10667 row10687 rfl

set_option maxRecDepth 16000 in
private theorem row10691 :
    FinalSeventhSieve.rough 11092009835083 10691+59273278=FinalSeventhSieve.rough 11092009835083 10687 :=
  LargeQuotientSieve.row (p:=10691) (q:=1037509104) (s:=32210) (rank:=52655944) (tiny:=1303) (pairs:=6618636)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1037509104 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10691 : FinalSeventhSieve.rough 11092009835083 10691+178003201=FinalSeventhSieve.rough 11092009835083 10663 :=
  LargeQuotientSieve.combine to10687 row10691 rfl

set_option maxRecDepth 16000 in
private theorem row10709 :
    FinalSeventhSieve.rough 11092009835083 10709+59163491=FinalSeventhSieve.rough 11092009835083 10691 :=
  LargeQuotientSieve.row (p:=10709) (q:=1035765228) (s:=32183) (rank:=52571947) (tiny:=1304) (pairs:=6592847)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1035765228 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10709 : FinalSeventhSieve.rough 11092009835083 10709+237166692=FinalSeventhSieve.rough 11092009835083 10663 :=
  LargeQuotientSieve.combine to10691 row10709 rfl

set_option maxRecDepth 16000 in
private theorem row10711 :
    FinalSeventhSieve.rough 11092009835083 10711+59144258=FinalSeventhSieve.rough 11092009835083 10709 :=
  LargeQuotientSieve.row (p:=10711) (q:=1035571826) (s:=32180) (rank:=52562700) (tiny:=1305) (pairs:=6582862)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1035571826 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10711 : FinalSeventhSieve.rough 11092009835083 10711+296310950=FinalSeventhSieve.rough 11092009835083 10663 :=
  LargeQuotientSieve.combine to10709 row10711 rfl

set_option maxRecDepth 16000 in
private theorem row10723 :
    FinalSeventhSieve.rough 11092009835083 10723+59068620=FinalSeventhSieve.rough 11092009835083 10711 :=
  LargeQuotientSieve.row (p:=10723) (q:=1034412928) (s:=32162) (rank:=52506847) (tiny:=1306) (pairs:=6563078)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1034412928 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10723 : FinalSeventhSieve.rough 11092009835083 10723+355379570=FinalSeventhSieve.rough 11092009835083 10663 :=
  LargeQuotientSieve.combine to10711 row10723 rfl

set_option maxRecDepth 16000 in
private theorem row10729 :
    FinalSeventhSieve.rough 11092009835083 10729+59026833=FinalSeventhSieve.rough 11092009835083 10723 :=
  LargeQuotientSieve.row (p:=10729) (q:=1033834451) (s:=32153) (rank:=52478954) (tiny:=1307) (pairs:=6549185)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1033834451 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10729 : FinalSeventhSieve.rough 11092009835083 10729+414406403=FinalSeventhSieve.rough 11092009835083 10663 :=
  LargeQuotientSieve.combine to10723 row10729 rfl

set_option maxRecDepth 16000 in
private theorem row10733 :
    FinalSeventhSieve.rough 11092009835083 10733+58996440=FinalSeventhSieve.rough 11092009835083 10729 :=
  LargeQuotientSieve.row (p:=10733) (q:=1033449160) (s:=32147) (rank:=52460438) (tiny:=1308) (pairs:=6537309)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1033449160 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10733 : FinalSeventhSieve.rough 11092009835083 10733+473402843=FinalSeventhSieve.rough 11092009835083 10663 :=
  LargeQuotientSieve.combine to10729 row10733 rfl

set_option maxRecDepth 16000 in
private theorem row10739 :
    FinalSeventhSieve.rough 11092009835083 10739+58954885=FinalSeventhSieve.rough 11092009835083 10733 :=
  LargeQuotientSieve.row (p:=10739) (q:=1032871760) (s:=32138) (rank:=52432737) (tiny:=1309) (pairs:=6523456)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1032871760 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10739 : FinalSeventhSieve.rough 11092009835083 10739+532357728=FinalSeventhSieve.rough 11092009835083 10663 :=
  LargeQuotientSieve.combine to10733 row10739 rfl

set_option maxRecDepth 16000 in
private theorem row10753 :
    FinalSeventhSieve.rough 11092009835083 10753+58868427=FinalSeventhSieve.rough 11092009835083 10739 :=
  LargeQuotientSieve.row (p:=10753) (q:=1031527000) (s:=32117) (rank:=52367892) (tiny:=1310) (pairs:=6501844)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1031527000 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10753 : FinalSeventhSieve.rough 11092009835083 10753+591226155=FinalSeventhSieve.rough 11092009835083 10663 :=
  LargeQuotientSieve.combine to10739 row10753 rfl

set_option maxRecDepth 16000 in
private theorem row10771 :
    FinalSeventhSieve.rough 11092009835083 10771+58760063=FinalSeventhSieve.rough 11092009835083 10753 :=
  LargeQuotientSieve.row (p:=10771) (q:=1029803159) (s:=32090) (rank:=52284876) (tiny:=1311) (pairs:=6476497)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1029803159 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10771 : FinalSeventhSieve.rough 11092009835083 10771+649986218=FinalSeventhSieve.rough 11092009835083 10663 :=
  LargeQuotientSieve.combine to10753 row10771 rfl

set_option maxRecDepth 16000 in
private theorem row10781 :
    FinalSeventhSieve.rough 11092009835083 10781+58696321=FinalSeventhSieve.rough 11092009835083 10771 :=
  LargeQuotientSieve.row (p:=10781) (q:=1028847957) (s:=32075) (rank:=52238714) (tiny:=1312) (pairs:=6458918)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ1025000000To1050000000.count_correct 1028847957 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to10781 : FinalSeventhSieve.rough 11092009835083 10781+708682539=FinalSeventhSieve.rough 11092009835083 10663 :=
  LargeQuotientSieve.combine to10771 row10781 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 10781+708682539=FinalSeventhSieve.rough 11092009835083 10663 := to10781

end Tail11092009835083From10663To10781
