import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-600000000-625000000»

/-! Exact changes for sieve primes 2062 through 2073. -/
open Finset
namespace Tail11092009835083From17977To18089

set_option maxRecDepth 16000 in
private theorem row17981 :
    FinalSeventhSieve.rough 11092009835083 17981+32674352=FinalSeventhSieve.rough 11092009835083 17977 :=
  LargeQuotientSieve.row (p:=17981) (q:=616873913) (s:=24836) (rank:=32159184) (tiny:=2061) (pairs:=517228)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 616873913 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row17987 :
    FinalSeventhSieve.rough 11092009835083 17987+32661984=FinalSeventhSieve.rough 11092009835083 17981 :=
  LargeQuotientSieve.row (p:=17987) (q:=616668140) (s:=24832) (rank:=32149083) (tiny:=2062) (pairs:=514962)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 616668140 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17987 : FinalSeventhSieve.rough 11092009835083 17987+65336336=FinalSeventhSieve.rough 11092009835083 17977 :=
  LargeQuotientSieve.combine row17981 row17987 rfl

set_option maxRecDepth 16000 in
private theorem row17989 :
    FinalSeventhSieve.rough 11092009835083 17989+32656790=FinalSeventhSieve.rough 11092009835083 17987 :=
  LargeQuotientSieve.row (p:=17989) (q:=616599579) (s:=24831) (rank:=32145680) (tiny:=2063) (pairs:=513172)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 616599579 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17989 : FinalSeventhSieve.rough 11092009835083 17989+97993126=FinalSeventhSieve.rough 11092009835083 17977 :=
  LargeQuotientSieve.combine to17987 row17989 rfl

set_option maxRecDepth 16000 in
private theorem row18013 :
    FinalSeventhSieve.rough 11092009835083 18013+32612100=FinalSeventhSieve.rough 11092009835083 17989 :=
  LargeQuotientSieve.row (p:=18013) (q:=615778040) (s:=24814) (rank:=32105172) (tiny:=2064) (pairs:=508991)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 615778040 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18013 : FinalSeventhSieve.rough 11092009835083 18013+130605226=FinalSeventhSieve.rough 11092009835083 17977 :=
  LargeQuotientSieve.combine to17989 row18013 rfl

set_option maxRecDepth 16000 in
private theorem row18041 :
    FinalSeventhSieve.rough 11092009835083 18041+32560205=FinalSeventhSieve.rough 11092009835083 18013 :=
  LargeQuotientSieve.row (p:=18041) (q:=614822339) (s:=24795) (rank:=32057816) (tiny:=2065) (pairs:=504453)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 614822339 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18041 : FinalSeventhSieve.rough 11092009835083 18041+163165431=FinalSeventhSieve.rough 11092009835083 17977 :=
  LargeQuotientSieve.combine to18013 row18041 rfl

set_option maxRecDepth 16000 in
private theorem row18043 :
    FinalSeventhSieve.rough 11092009835083 18043+32555007=FinalSeventhSieve.rough 11092009835083 18041 :=
  LargeQuotientSieve.row (p:=18043) (q:=614754189) (s:=24794) (rank:=32054426) (tiny:=2066) (pairs:=502646)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 614754189 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18043 : FinalSeventhSieve.rough 11092009835083 18043+195720438=FinalSeventhSieve.rough 11092009835083 17977 :=
  LargeQuotientSieve.combine to18041 row18043 rfl

set_option maxRecDepth 16000 in
private theorem row18047 :
    FinalSeventhSieve.rough 11092009835083 18047+32546212=FinalSeventhSieve.rough 11092009835083 18043 :=
  LargeQuotientSieve.row (p:=18047) (q:=614617932) (s:=24791) (rank:=32047644) (tiny:=2067) (pairs:=500634)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 614617932 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18047 : FinalSeventhSieve.rough 11092009835083 18047+228266650=FinalSeventhSieve.rough 11092009835083 17977 :=
  LargeQuotientSieve.combine to18043 row18047 rfl

set_option maxRecDepth 16000 in
private theorem row18049 :
    FinalSeventhSieve.rough 11092009835083 18049+32541068=FinalSeventhSieve.rough 11092009835083 18047 :=
  LargeQuotientSieve.row (p:=18049) (q:=614549827) (s:=24790) (rank:=32044290) (tiny:=2068) (pairs:=498845)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 614549827 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18049 : FinalSeventhSieve.rough 11092009835083 18049+260807718=FinalSeventhSieve.rough 11092009835083 17977 :=
  LargeQuotientSieve.combine to18047 row18049 rfl

set_option maxRecDepth 16000 in
private theorem row18059 :
    FinalSeventhSieve.rough 11092009835083 18059+32521774=FinalSeventhSieve.rough 11092009835083 18049 :=
  LargeQuotientSieve.row (p:=18059) (q:=614209526) (s:=24783) (rank:=32027581) (tiny:=2069) (pairs:=496261)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 614209526 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18059 : FinalSeventhSieve.rough 11092009835083 18059+293329492=FinalSeventhSieve.rough 11092009835083 17977 :=
  LargeQuotientSieve.combine to18049 row18059 rfl

set_option maxRecDepth 16000 in
private theorem row18061 :
    FinalSeventhSieve.rough 11092009835083 18061+32516575=FinalSeventhSieve.rough 11092009835083 18059 :=
  LargeQuotientSieve.row (p:=18061) (q:=614141511) (s:=24781) (rank:=32024164) (tiny:=2070) (pairs:=494480)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 614141511 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18061 : FinalSeventhSieve.rough 11092009835083 18061+325846067=FinalSeventhSieve.rough 11092009835083 17977 :=
  LargeQuotientSieve.combine to18059 row18061 rfl

set_option maxRecDepth 16000 in
private theorem row18077 :
    FinalSeventhSieve.rough 11092009835083 18077+32486574=FinalSeventhSieve.rough 11092009835083 18061 :=
  LargeQuotientSieve.row (p:=18077) (q:=613597933) (s:=24770) (rank:=31997412) (tiny:=2071) (pairs:=491232)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 613597933 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18077 : FinalSeventhSieve.rough 11092009835083 18077+358332641=FinalSeventhSieve.rough 11092009835083 17977 :=
  LargeQuotientSieve.combine to18061 row18077 rfl

set_option maxRecDepth 16000 in
private theorem row18089 :
    FinalSeventhSieve.rough 11092009835083 18089+32463660=FinalSeventhSieve.rough 11092009835083 18077 :=
  LargeQuotientSieve.row (p:=18089) (q:=613190880) (s:=24762) (rank:=31977302) (tiny:=2072) (pairs:=488429)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 613190880 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to18089 : FinalSeventhSieve.rough 11092009835083 18089+390796301=FinalSeventhSieve.rough 11092009835083 17977 :=
  LargeQuotientSieve.combine to18077 row18089 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 18089+390796301=FinalSeventhSieve.rough 11092009835083 17977 := to18089

end Tail11092009835083From17977To18089
