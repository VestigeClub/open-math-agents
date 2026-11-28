import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-775000000-800000000»

/-! Exact changes for sieve primes 1662 through 1673. -/
open Finset
namespace Tail11092009835083From14083To14243

set_option maxRecDepth 16000 in
private theorem row14087 :
    FinalSeventhSieve.rough 11092009835083 14087+42961787=FinalSeventhSieve.rough 11092009835083 14083 :=
  LargeQuotientSieve.row (p:=14087) (q:=787393329) (s:=28060) (rank:=40530804) (tiny:=1661) (pairs:=2432643)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 787393329 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row14107 :
    FinalSeventhSieve.rough 11092009835083 14107+42896063=FinalSeventhSieve.rough 11092009835083 14087 :=
  LargeQuotientSieve.row (p:=14107) (q:=786277013) (s:=28040) (rank:=40476396) (tiny:=1662) (pairs:=2421328)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 786277013 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14107 : FinalSeventhSieve.rough 11092009835083 14107+85857850=FinalSeventhSieve.rough 11092009835083 14083 :=
  LargeQuotientSieve.combine row14087 row14107 rfl

set_option maxRecDepth 16000 in
private theorem row14143 :
    FinalSeventhSieve.rough 11092009835083 14143+42781208=FinalSeventhSieve.rough 11092009835083 14107 :=
  LargeQuotientSieve.row (p:=14143) (q:=784275601) (s:=28004) (rank:=40378515) (tiny:=1663) (pairs:=2404355)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 784275601 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14143 : FinalSeventhSieve.rough 11092009835083 14143+128639058=FinalSeventhSieve.rough 11092009835083 14083 :=
  LargeQuotientSieve.combine to14107 row14143 rfl

set_option maxRecDepth 16000 in
private theorem row14149 :
    FinalSeventhSieve.rough 11092009835083 14149+42758810=FinalSeventhSieve.rough 11092009835083 14143 :=
  LargeQuotientSieve.row (p:=14149) (q:=783943023) (s:=27998) (rank:=40362287) (tiny:=1664) (pairs:=2398186)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 783943023 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14149 : FinalSeventhSieve.rough 11092009835083 14149+171397868=FinalSeventhSieve.rough 11092009835083 14083 :=
  LargeQuotientSieve.combine to14143 row14149 rfl

set_option maxRecDepth 16000 in
private theorem row14153 :
    FinalSeventhSieve.rough 11092009835083 14153+42742596=FinalSeventhSieve.rough 11092009835083 14149 :=
  LargeQuotientSieve.row (p:=14153) (q:=783721460) (s:=27995) (rank:=40351445) (tiny:=1665) (pairs:=2392815)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 783721460 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14153 : FinalSeventhSieve.rough 11092009835083 14153+214140464=FinalSeventhSieve.rough 11092009835083 14083 :=
  LargeQuotientSieve.combine to14149 row14153 rfl

set_option maxRecDepth 16000 in
private theorem row14159 :
    FinalSeventhSieve.rough 11092009835083 14159+42720268=FinalSeventhSieve.rough 11092009835083 14153 :=
  LargeQuotientSieve.row (p:=14159) (q:=783389352) (s:=27989) (rank:=40335204) (tiny:=1666) (pairs:=2386729)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 783389352 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14159 : FinalSeventhSieve.rough 11092009835083 14159+256860732=FinalSeventhSieve.rough 11092009835083 14083 :=
  LargeQuotientSieve.combine to14153 row14159 rfl

set_option maxRecDepth 16000 in
private theorem row14173 :
    FinalSeventhSieve.rough 11092009835083 14173+42673457=FinalSeventhSieve.rough 11092009835083 14159 :=
  LargeQuotientSieve.row (p:=14173) (q:=782615524) (s:=27975) (rank:=40297250) (tiny:=1667) (pairs:=2377873)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 782615524 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14173 : FinalSeventhSieve.rough 11092009835083 14173+299534189=FinalSeventhSieve.rough 11092009835083 14083 :=
  LargeQuotientSieve.combine to14159 row14173 rfl

set_option maxRecDepth 16000 in
private theorem row14177 :
    FinalSeventhSieve.rough 11092009835083 14177+42657374=FinalSeventhSieve.rough 11092009835083 14173 :=
  LargeQuotientSieve.row (p:=14177) (q:=782394712) (s:=27971) (rank:=40286540) (tiny:=1668) (pairs:=2372501)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 782394712 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14177 : FinalSeventhSieve.rough 11092009835083 14177+342191563=FinalSeventhSieve.rough 11092009835083 14083 :=
  LargeQuotientSieve.combine to14173 row14177 rfl

set_option maxRecDepth 16000 in
private theorem row14197 :
    FinalSeventhSieve.rough 11092009835083 14197+42592442=FinalSeventhSieve.rough 11092009835083 14177 :=
  LargeQuotientSieve.row (p:=14197) (q:=781292514) (s:=27951) (rank:=40232637) (tiny:=1669) (pairs:=2361473)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 781292514 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14197 : FinalSeventhSieve.rough 11092009835083 14197+384784005=FinalSeventhSieve.rough 11092009835083 14083 :=
  LargeQuotientSieve.combine to14177 row14197 rfl

set_option maxRecDepth 16000 in
private theorem row14207 :
    FinalSeventhSieve.rough 11092009835083 14207+42558080=FinalSeventhSieve.rough 11092009835083 14197 :=
  LargeQuotientSieve.row (p:=14207) (q:=780742580) (s:=27941) (rank:=40205727) (tiny:=1670) (pairs:=2354022)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 780742580 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14207 : FinalSeventhSieve.rough 11092009835083 14207+427342085=FinalSeventhSieve.rough 11092009835083 14083 :=
  LargeQuotientSieve.combine to14197 row14207 rfl

set_option maxRecDepth 16000 in
private theorem row14221 :
    FinalSeventhSieve.rough 11092009835083 14221+42511688=FinalSeventhSieve.rough 11092009835083 14207 :=
  LargeQuotientSieve.row (p:=14221) (q:=779973970) (s:=27928) (rank:=40168239) (tiny:=1671) (pairs:=2345119)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 779973970 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14221 : FinalSeventhSieve.rough 11092009835083 14221+469853773=FinalSeventhSieve.rough 11092009835083 14083 :=
  LargeQuotientSieve.combine to14207 row14221 rfl

set_option maxRecDepth 16000 in
private theorem row14243 :
    FinalSeventhSieve.rough 11092009835083 14243+42441153=FinalSeventhSieve.rough 11092009835083 14221 :=
  LargeQuotientSieve.row (p:=14243) (q:=778769208) (s:=27906) (rank:=40109352) (tiny:=1672) (pairs:=2333472)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ775000000To800000000.count_correct 778769208 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to14243 : FinalSeventhSieve.rough 11092009835083 14243+512294926=FinalSeventhSieve.rough 11092009835083 14083 :=
  LargeQuotientSieve.combine to14221 row14243 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 14243+512294926=FinalSeventhSieve.rough 11092009835083 14083 := to14243

end Tail11092009835083From14083To14243
