import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-675000000-700000000»

/-! Exact changes for sieve primes 1872 through 1883. -/
open Finset
namespace Tail11092009835083From16073To16193

set_option maxRecDepth 16000 in
private theorem row16087 :
    FinalSeventhSieve.rough 11092009835083 16087+36932345=FinalSeventhSieve.rough 11092009835083 16073 :=
  LargeQuotientSieve.row (p:=16087) (q:=689501450) (s:=26258) (rank:=35737219) (tiny:=1871) (pairs:=1196996)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 689501450 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row16091 :
    FinalSeventhSieve.rough 11092009835083 16091+36920522=FinalSeventhSieve.rough 11092009835083 16087 :=
  LargeQuotientSieve.row (p:=16091) (q:=689330050) (s:=26255) (rank:=35728819) (tiny:=1872) (pairs:=1193574)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 689330050 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16091 : FinalSeventhSieve.rough 11092009835083 16091+73852867=FinalSeventhSieve.rough 11092009835083 16073 :=
  LargeQuotientSieve.combine row16087 row16091 rfl

set_option maxRecDepth 16000 in
private theorem row16097 :
    FinalSeventhSieve.rough 11092009835083 16097+36903975=FinalSeventhSieve.rough 11092009835083 16091 :=
  LargeQuotientSieve.row (p:=16097) (q:=689073108) (s:=26250) (rank:=35716128) (tiny:=1873) (pairs:=1189719)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 689073108 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16097 : FinalSeventhSieve.rough 11092009835083 16097+110756842=FinalSeventhSieve.rough 11092009835083 16073 :=
  LargeQuotientSieve.combine to16091 row16097 rfl

set_option maxRecDepth 16000 in
private theorem row16103 :
    FinalSeventhSieve.rough 11092009835083 16103+36887516=FinalSeventhSieve.rough 11092009835083 16097 :=
  LargeQuotientSieve.row (p:=16103) (q:=688816359) (s:=26245) (rank:=35703472) (tiny:=1874) (pairs:=1185917)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 688816359 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16103 : FinalSeventhSieve.rough 11092009835083 16103+147644358=FinalSeventhSieve.rough 11092009835083 16073 :=
  LargeQuotientSieve.combine to16097 row16103 rfl

set_option maxRecDepth 16000 in
private theorem row16111 :
    FinalSeventhSieve.rough 11092009835083 16111+36866537=FinalSeventhSieve.rough 11092009835083 16103 :=
  LargeQuotientSieve.row (p:=16111) (q:=688474324) (s:=26238) (rank:=35686683) (tiny:=1875) (pairs:=1181728)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 688474324 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16111 : FinalSeventhSieve.rough 11092009835083 16111+184510895=FinalSeventhSieve.rough 11092009835083 16073 :=
  LargeQuotientSieve.combine to16103 row16111 rfl

set_option maxRecDepth 16000 in
private theorem row16127 :
    FinalSeventhSieve.rough 11092009835083 16127+36827216=FinalSeventhSieve.rough 11092009835083 16111 :=
  LargeQuotientSieve.row (p:=16127) (q:=687791271) (s:=26225) (rank:=35653136) (tiny:=1876) (pairs:=1175955)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 687791271 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16127 : FinalSeventhSieve.rough 11092009835083 16127+221338111=FinalSeventhSieve.rough 11092009835083 16073 :=
  LargeQuotientSieve.combine to16111 row16127 rfl

set_option maxRecDepth 16000 in
private theorem row16139 :
    FinalSeventhSieve.rough 11092009835083 16139+36797189=FinalSeventhSieve.rough 11092009835083 16127 :=
  LargeQuotientSieve.row (p:=16139) (q:=687279870) (s:=26216) (rank:=35628012) (tiny:=1877) (pairs:=1171053)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 687279870 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16139 : FinalSeventhSieve.rough 11092009835083 16139+258135300=FinalSeventhSieve.rough 11092009835083 16073 :=
  LargeQuotientSieve.combine to16127 row16139 rfl

set_option maxRecDepth 16000 in
private theorem row16141 :
    FinalSeventhSieve.rough 11092009835083 16141+36789960=FinalSeventhSieve.rough 11092009835083 16139 :=
  LargeQuotientSieve.row (p:=16141) (q:=687194711) (s:=26214) (rank:=35623755) (tiny:=1878) (pairs:=1168082)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 687194711 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16141 : FinalSeventhSieve.rough 11092009835083 16141+294925260=FinalSeventhSieve.rough 11092009835083 16073 :=
  LargeQuotientSieve.combine to16139 row16141 rfl

set_option maxRecDepth 16000 in
private theorem row16183 :
    FinalSeventhSieve.rough 11092009835083 16183+36691308=FinalSeventhSieve.rough 11092009835083 16141 :=
  LargeQuotientSieve.row (p:=16183) (q:=685411223) (s:=26180) (rank:=35535939) (tiny:=1879) (pairs:=1157247)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 685411223 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16183 : FinalSeventhSieve.rough 11092009835083 16183+331616568=FinalSeventhSieve.rough 11092009835083 16073 :=
  LargeQuotientSieve.combine to16141 row16183 rfl

set_option maxRecDepth 16000 in
private theorem row16187 :
    FinalSeventhSieve.rough 11092009835083 16187+36679628=FinalSeventhSieve.rough 11092009835083 16183 :=
  LargeQuotientSieve.row (p:=16187) (q:=685241850) (s:=26177) (rank:=35527614) (tiny:=1880) (pairs:=1153893)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 685241850 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16187 : FinalSeventhSieve.rough 11092009835083 16187+368296196=FinalSeventhSieve.rough 11092009835083 16073 :=
  LargeQuotientSieve.combine to16183 row16187 rfl

set_option maxRecDepth 16000 in
private theorem row16189 :
    FinalSeventhSieve.rough 11092009835083 16189+36672611=FinalSeventhSieve.rough 11092009835083 16187 :=
  LargeQuotientSieve.row (p:=16189) (q:=685157195) (s:=26175) (rank:=35523536) (tiny:=1881) (pairs:=1150955)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 685157195 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16189 : FinalSeventhSieve.rough 11092009835083 16189+404968807=FinalSeventhSieve.rough 11092009835083 16073 :=
  LargeQuotientSieve.combine to16187 row16189 rfl

set_option maxRecDepth 16000 in
private theorem row16193 :
    FinalSeventhSieve.rough 11092009835083 16193+36660910=FinalSeventhSieve.rough 11092009835083 16189 :=
  LargeQuotientSieve.row (p:=16193) (q:=684987947) (s:=26172) (rank:=35515142) (tiny:=1882) (pairs:=1147649)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ675000000To700000000.count_correct 684987947 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16193 : FinalSeventhSieve.rough 11092009835083 16193+441629717=FinalSeventhSieve.rough 11092009835083 16073 :=
  LargeQuotientSieve.combine to16189 row16193 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 16193+441629717=FinalSeventhSieve.rough 11092009835083 16073 := to16193

end Tail11092009835083From16073To16193
