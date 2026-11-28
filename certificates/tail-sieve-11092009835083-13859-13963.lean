import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-775000000-800000000»

/-! Exact changes for sieve primes 1638 through 1649. -/
open Finset
namespace Tail11092009835083From13859To13963

set_option maxRecDepth 16000 in
private theorem row13873 :
    FinalSeventhSieve.rough 11092009835083 13873+43734004=FinalSeventhSieve.rough 11092009835083 13859 :=
  LargeQuotientSieve.row (p:=13873) (q:=799539381) (s:=28276) (rank:=41123757) (tiny:=1637) (pairs:=2611883)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 799539381 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row13877 :
    FinalSeventhSieve.rough 11092009835083 13877+43717171=FinalSeventhSieve.rough 11092009835083 13873 :=
  LargeQuotientSieve.row (p:=13877) (q:=799308916) (s:=28272) (rank:=41112706) (tiny:=1638) (pairs:=2606102)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 799308916 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13877 : FinalSeventhSieve.rough 11092009835083 13877+87451175=FinalSeventhSieve.rough 11092009835083 13859 :=
  LargeQuotientSieve.combine row13873 row13877 rfl

set_option maxRecDepth 16000 in
private theorem row13879 :
    FinalSeventhSieve.rough 11092009835083 13879+43706637=FinalSeventhSieve.rough 11092009835083 13877 :=
  LargeQuotientSieve.row (p:=13879) (q:=799193734) (s:=28270) (rank:=41107126) (tiny:=1639) (pairs:=2601149)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 799193734 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13879 : FinalSeventhSieve.rough 11092009835083 13879+131157812=FinalSeventhSieve.rough 11092009835083 13859 :=
  LargeQuotientSieve.combine to13877 row13879 rfl

set_option maxRecDepth 16000 in
private theorem row13883 :
    FinalSeventhSieve.rough 11092009835083 13883+43689701=FinalSeventhSieve.rough 11092009835083 13879 :=
  LargeQuotientSieve.row (p:=13883) (q:=798963468) (s:=28265) (rank:=41095948) (tiny:=1640) (pairs:=2595392)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 798963468 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13883 : FinalSeventhSieve.rough 11092009835083 13883+174847513=FinalSeventhSieve.rough 11092009835083 13859 :=
  LargeQuotientSieve.combine to13879 row13883 rfl

set_option maxRecDepth 16000 in
private theorem row13901 :
    FinalSeventhSieve.rough 11092009835083 13901+43628024=FinalSeventhSieve.rough 11092009835083 13883 :=
  LargeQuotientSieve.row (p:=13901) (q:=797928914) (s:=28247) (rank:=41045369) (tiny:=1641) (pairs:=2584295)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 797928914 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13901 : FinalSeventhSieve.rough 11092009835083 13901+218475537=FinalSeventhSieve.rough 11092009835083 13859 :=
  LargeQuotientSieve.combine to13883 row13901 rfl

set_option maxRecDepth 16000 in
private theorem row13903 :
    FinalSeventhSieve.rough 11092009835083 13903+43617452=FinalSeventhSieve.rough 11092009835083 13901 :=
  LargeQuotientSieve.row (p:=13903) (q:=797814128) (s:=28245) (rank:=41039736) (tiny:=1642) (pairs:=2579357)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 797814128 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13903 : FinalSeventhSieve.rough 11092009835083 13903+262092989=FinalSeventhSieve.rough 11092009835083 13859 :=
  LargeQuotientSieve.combine to13901 row13903 rfl

set_option maxRecDepth 16000 in
private theorem row13907 :
    FinalSeventhSieve.rough 11092009835083 13907+43600435=FinalSeventhSieve.rough 11092009835083 13903 :=
  LargeQuotientSieve.row (p:=13907) (q:=797584657) (s:=28241) (rank:=41028457) (tiny:=1643) (pairs:=2573620)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 797584657 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13907 : FinalSeventhSieve.rough 11092009835083 13907+305693424=FinalSeventhSieve.rough 11092009835083 13859 :=
  LargeQuotientSieve.combine to13903 row13907 rfl

set_option maxRecDepth 16000 in
private theorem row13913 :
    FinalSeventhSieve.rough 11092009835083 13913+43577160=FinalSeventhSieve.rough 11092009835083 13907 :=
  LargeQuotientSieve.row (p:=13913) (q:=797240698) (s:=28235) (rank:=41011676) (tiny:=1644) (pairs:=2567127)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 797240698 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13913 : FinalSeventhSieve.rough 11092009835083 13913+349270584=FinalSeventhSieve.rough 11092009835083 13859 :=
  LargeQuotientSieve.combine to13907 row13913 rfl

set_option maxRecDepth 16000 in
private theorem row13921 :
    FinalSeventhSieve.rough 11092009835083 13921+43547472=FinalSeventhSieve.rough 11092009835083 13913 :=
  LargeQuotientSieve.row (p:=13921) (q:=796782546) (s:=28227) (rank:=40989184) (tiny:=1645) (pairs:=2559932)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 796782546 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13921 : FinalSeventhSieve.rough 11092009835083 13921+392818056=FinalSeventhSieve.rough 11092009835083 13859 :=
  LargeQuotientSieve.combine to13913 row13921 rfl

set_option maxRecDepth 16000 in
private theorem row13931 :
    FinalSeventhSieve.rough 11092009835083 13931+43511578=FinalSeventhSieve.rough 11092009835083 13921 :=
  LargeQuotientSieve.row (p:=13931) (q:=796210597) (s:=28217) (rank:=40961240) (tiny:=1646) (pairs:=2551983)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 796210597 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13931 : FinalSeventhSieve.rough 11092009835083 13931+436329634=FinalSeventhSieve.rough 11092009835083 13859 :=
  LargeQuotientSieve.combine to13921 row13931 rfl

set_option maxRecDepth 16000 in
private theorem row13933 :
    FinalSeventhSieve.rough 11092009835083 13933+43501085=FinalSeventhSieve.rough 11092009835083 13931 :=
  LargeQuotientSieve.row (p:=13933) (q:=796096306) (s:=28215) (rank:=40955679) (tiny:=1647) (pairs:=2547052)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 796096306 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13933 : FinalSeventhSieve.rough 11092009835083 13933+479830719=FinalSeventhSieve.rough 11092009835083 13859 :=
  LargeQuotientSieve.combine to13931 row13933 rfl

set_option maxRecDepth 16000 in
private theorem row13963 :
    FinalSeventhSieve.rough 11092009835083 13963+43402227=FinalSeventhSieve.rough 11092009835083 13933 :=
  LargeQuotientSieve.row (p:=13963) (q:=794385865) (s:=28184) (rank:=40872360) (tiny:=1648) (pairs:=2531514)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 794385865 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13963 : FinalSeventhSieve.rough 11092009835083 13963+523232946=FinalSeventhSieve.rough 11092009835083 13859 :=
  LargeQuotientSieve.combine to13933 row13963 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13963+523232946=FinalSeventhSieve.rough 11092009835083 13859 := to13963

end Tail11092009835083From13859To13963
