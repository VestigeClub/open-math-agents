import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-875000000-900000000»

/-! Exact changes for sieve primes 1473 through 1484. -/
open Finset
namespace Tail11092009835083From12323To12433

set_option maxRecDepth 16000 in
private theorem row12329 :
    FinalSeventhSieve.rough 11092009835083 12329+50177591=FinalSeventhSieve.rough 11092009835083 12323 :=
  LargeQuotientSieve.row (p:=12329) (q:=899668248) (s:=29994) (rank:=45993184) (tiny:=1472) (pairs:=4185878)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 899668248 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row12343 :
    FinalSeventhSieve.rough 11092009835083 12343+50113927=FinalSeventhSieve.rough 11092009835083 12329 :=
  LargeQuotientSieve.row (p:=12343) (q:=898647803) (s:=29977) (rank:=45943781) (tiny:=1473) (pairs:=4171618)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 898647803 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12343 : FinalSeventhSieve.rough 11092009835083 12343+100291518=FinalSeventhSieve.rough 11092009835083 12323 :=
  LargeQuotientSieve.combine row12329 row12343 rfl

set_option maxRecDepth 16000 in
private theorem row12347 :
    FinalSeventhSieve.rough 11092009835083 12347+50091632=FinalSeventhSieve.rough 11092009835083 12343 :=
  LargeQuotientSieve.row (p:=12347) (q:=898356672) (s:=29972) (rank:=45929640) (tiny:=1474) (pairs:=4163465)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 898356672 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12347 : FinalSeventhSieve.rough 11092009835083 12347+150383150=FinalSeventhSieve.rough 11092009835083 12323 :=
  LargeQuotientSieve.combine to12343 row12347 rfl

set_option maxRecDepth 16000 in
private theorem row12373 :
    FinalSeventhSieve.rough 11092009835083 12373+49978562=FinalSeventhSieve.rough 11092009835083 12347 :=
  LargeQuotientSieve.row (p:=12373) (q:=896468910) (s:=29941) (rank:=45838112) (tiny:=1475) (pairs:=4141924)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 896468910 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12373 : FinalSeventhSieve.rough 11092009835083 12373+200361712=FinalSeventhSieve.rough 11092009835083 12323 :=
  LargeQuotientSieve.combine to12347 row12373 rfl

set_option maxRecDepth 16000 in
private theorem row12377 :
    FinalSeventhSieve.rough 11092009835083 12377+49956440=FinalSeventhSieve.rough 11092009835083 12373 :=
  LargeQuotientSieve.row (p:=12377) (q:=896179190) (s:=29936) (rank:=45824074) (tiny:=1476) (pairs:=4133841)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 896179190 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12377 : FinalSeventhSieve.rough 11092009835083 12377+250318152=FinalSeventhSieve.rough 11092009835083 12323 :=
  LargeQuotientSieve.combine to12373 row12377 rfl

set_option maxRecDepth 16000 in
private theorem row12379 :
    FinalSeventhSieve.rough 11092009835083 12379+49942603=FinalSeventhSieve.rough 11092009835083 12377 :=
  LargeQuotientSieve.row (p:=12379) (q:=896034399) (s:=29933) (rank:=45817131) (tiny:=1477) (pairs:=4126948)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 896034399 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12379 : FinalSeventhSieve.rough 11092009835083 12379+300260755=FinalSeventhSieve.rough 11092009835083 12323 :=
  LargeQuotientSieve.combine to12377 row12379 rfl

set_option maxRecDepth 16000 in
private theorem row12391 :
    FinalSeventhSieve.rough 11092009835083 12391+49887593=FinalSeventhSieve.rough 11092009835083 12379 :=
  LargeQuotientSieve.row (p:=12391) (q:=895166639) (s:=29919) (rank:=45775023) (tiny:=1478) (pairs:=4114047)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 895166639 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12391 : FinalSeventhSieve.rough 11092009835083 12391+350148348=FinalSeventhSieve.rough 11092009835083 12323 :=
  LargeQuotientSieve.combine to12379 row12391 rfl

set_option maxRecDepth 16000 in
private theorem row12401 :
    FinalSeventhSieve.rough 11092009835083 12401+49841000=FinalSeventhSieve.rough 11092009835083 12391 :=
  LargeQuotientSieve.row (p:=12401) (q:=894444789) (s:=29907) (rank:=45740089) (tiny:=1479) (pairs:=4102389)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 894444789 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12401 : FinalSeventhSieve.rough 11092009835083 12401+399989348=FinalSeventhSieve.rough 11092009835083 12323 :=
  LargeQuotientSieve.combine to12391 row12401 rfl

set_option maxRecDepth 16000 in
private theorem row12409 :
    FinalSeventhSieve.rough 11092009835083 12409+49802571=FinalSeventhSieve.rough 11092009835083 12401 :=
  LargeQuotientSieve.row (p:=12409) (q:=893868146) (s:=29897) (rank:=45712133) (tiny:=1480) (pairs:=4091917)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 893868146 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12409 : FinalSeventhSieve.rough 11092009835083 12409+449791919=FinalSeventhSieve.rough 11092009835083 12323 :=
  LargeQuotientSieve.combine to12401 row12409 rfl

set_option maxRecDepth 16000 in
private theorem row12413 :
    FinalSeventhSieve.rough 11092009835083 12413+49780653=FinalSeventhSieve.rough 11092009835083 12409 :=
  LargeQuotientSieve.row (p:=12413) (q:=893580104) (s:=29892) (rank:=45698191) (tiny:=1481) (pairs:=4083942)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 893580104 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12413 : FinalSeventhSieve.rough 11092009835083 12413+499572572=FinalSeventhSieve.rough 11092009835083 12323 :=
  LargeQuotientSieve.combine to12409 row12413 rfl

set_option maxRecDepth 16000 in
private theorem row12421 :
    FinalSeventhSieve.rough 11092009835083 12421+49742244=FinalSeventhSieve.rough 11092009835083 12413 :=
  LargeQuotientSieve.row (p:=12421) (q:=893004575) (s:=29883) (rank:=45670178) (tiny:=1482) (pairs:=4073547)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 893004575 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12421 : FinalSeventhSieve.rough 11092009835083 12421+549314816=FinalSeventhSieve.rough 11092009835083 12323 :=
  LargeQuotientSieve.combine to12413 row12421 rfl

set_option maxRecDepth 16000 in
private theorem row12433 :
    FinalSeventhSieve.rough 11092009835083 12433+49687477=FinalSeventhSieve.rough 11092009835083 12421 :=
  LargeQuotientSieve.row (p:=12433) (q:=892142671) (s:=29868) (rank:=45628198) (tiny:=1483) (pairs:=4060761)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ875000000To900000000.count_correct 892142671 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12433 : FinalSeventhSieve.rough 11092009835083 12433+599002293=FinalSeventhSieve.rough 11092009835083 12323 :=
  LargeQuotientSieve.combine to12421 row12433 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 12433+599002293=FinalSeventhSieve.rough 11092009835083 12323 := to12433

end Tail11092009835083From12323To12433
