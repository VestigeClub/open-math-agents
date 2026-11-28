import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-650000000-675000000»

/-! Exact changes for sieve primes 1953 through 1964. -/
open Finset
namespace Tail11092009835083From16927To17029

set_option maxRecDepth 16000 in
private theorem row16931 :
    FinalSeventhSieve.rough 11092009835083 16931+34900885=FinalSeventhSieve.rough 11092009835083 16927 :=
  LargeQuotientSieve.row (p:=16931) (q:=655130224) (s:=25595) (rank:=34046208) (tiny:=1952) (pairs:=856628)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 655130224 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row16937 :
    FinalSeventhSieve.rough 11092009835083 16937+34886467=FinalSeventhSieve.rough 11092009835083 16931 :=
  LargeQuotientSieve.row (p:=16937) (q:=654898142) (s:=25590) (rank:=34034826) (tiny:=1953) (pairs:=853593)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 654898142 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16937 : FinalSeventhSieve.rough 11092009835083 16937+69787352=FinalSeventhSieve.rough 11092009835083 16927 :=
  LargeQuotientSieve.combine row16931 row16937 rfl

set_option maxRecDepth 16000 in
private theorem row16943 :
    FinalSeventhSieve.rough 11092009835083 16943+34872030=FinalSeventhSieve.rough 11092009835083 16937 :=
  LargeQuotientSieve.row (p:=16943) (q:=654666224) (s:=25586) (rank:=34023443) (tiny:=1954) (pairs:=850540)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 654666224 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16943 : FinalSeventhSieve.rough 11092009835083 16943+104659382=FinalSeventhSieve.rough 11092009835083 16927 :=
  LargeQuotientSieve.combine to16937 row16943 rfl

set_option maxRecDepth 16000 in
private theorem row16963 :
    FinalSeventhSieve.rough 11092009835083 16963+34828821=FinalSeventhSieve.rough 11092009835083 16943 :=
  LargeQuotientSieve.row (p:=16963) (q:=653894348) (s:=25571) (rank:=33985385) (tiny:=1955) (pairs:=845390)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 653894348 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16963 : FinalSeventhSieve.rough 11092009835083 16963+139488203=FinalSeventhSieve.rough 11092009835083 16927 :=
  LargeQuotientSieve.combine to16943 row16963 rfl

set_option maxRecDepth 16000 in
private theorem row16979 :
    FinalSeventhSieve.rough 11092009835083 16979+34793896=FinalSeventhSieve.rough 11092009835083 16963 :=
  LargeQuotientSieve.row (p:=16979) (q:=653278157) (s:=25559) (rank:=33954962) (tiny:=1956) (pairs:=840889)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 653278157 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16979 : FinalSeventhSieve.rough 11092009835083 16979+174282099=FinalSeventhSieve.rough 11092009835083 16927 :=
  LargeQuotientSieve.combine to16963 row16979 rfl

set_option maxRecDepth 16000 in
private theorem row16981 :
    FinalSeventhSieve.rough 11092009835083 16981+34787712=FinalSeventhSieve.rough 11092009835083 16979 :=
  LargeQuotientSieve.row (p:=16981) (q:=653201215) (s:=25557) (rank:=33951206) (tiny:=1957) (pairs:=838462)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 653201215 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16981 : FinalSeventhSieve.rough 11092009835083 16981+209069811=FinalSeventhSieve.rough 11092009835083 16927 :=
  LargeQuotientSieve.combine to16979 row16981 rfl

set_option maxRecDepth 16000 in
private theorem row16987 :
    FinalSeventhSieve.rough 11092009835083 16987+34773338=FinalSeventhSieve.rough 11092009835083 16981 :=
  LargeQuotientSieve.row (p:=16987) (q:=652970497) (s:=25553) (rank:=33939842) (tiny:=1958) (pairs:=835453)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 652970497 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16987 : FinalSeventhSieve.rough 11092009835083 16987+243843149=FinalSeventhSieve.rough 11092009835083 16927 :=
  LargeQuotientSieve.combine to16981 row16987 rfl

set_option maxRecDepth 16000 in
private theorem row16993 :
    FinalSeventhSieve.rough 11092009835083 16993+34758956=FinalSeventhSieve.rough 11092009835083 16987 :=
  LargeQuotientSieve.row (p:=16993) (q:=652739942) (s:=25548) (rank:=33928473) (tiny:=1959) (pairs:=832441)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 652739942 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16993 : FinalSeventhSieve.rough 11092009835083 16993+278602105=FinalSeventhSieve.rough 11092009835083 16927 :=
  LargeQuotientSieve.combine to16987 row16993 rfl

set_option maxRecDepth 16000 in
private theorem row17011 :
    FinalSeventhSieve.rough 11092009835083 17011+34720109=FinalSeventhSieve.rough 11092009835083 16993 :=
  LargeQuotientSieve.row (p:=17011) (q:=652049252) (s:=25535) (rank:=33894440) (tiny:=1960) (pairs:=827628)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 652049252 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17011 : FinalSeventhSieve.rough 11092009835083 17011+313322214=FinalSeventhSieve.rough 11092009835083 16927 :=
  LargeQuotientSieve.combine to16993 row17011 rfl

set_option maxRecDepth 16000 in
private theorem row17021 :
    FinalSeventhSieve.rough 11092009835083 17021+34697672=FinalSeventhSieve.rough 11092009835083 17011 :=
  LargeQuotientSieve.row (p:=17021) (q:=651666167) (s:=25527) (rank:=33875617) (tiny:=1961) (pairs:=824015)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 651666167 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17021 : FinalSeventhSieve.rough 11092009835083 17021+348019886=FinalSeventhSieve.rough 11092009835083 16927 :=
  LargeQuotientSieve.combine to17011 row17021 rfl

set_option maxRecDepth 16000 in
private theorem row17027 :
    FinalSeventhSieve.rough 11092009835083 17027+34683455=FinalSeventhSieve.rough 11092009835083 17021 :=
  LargeQuotientSieve.row (p:=17027) (q:=651436532) (s:=25523) (rank:=33864401) (tiny:=1962) (pairs:=821015)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 651436532 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17027 : FinalSeventhSieve.rough 11092009835083 17027+382703341=FinalSeventhSieve.rough 11092009835083 16927 :=
  LargeQuotientSieve.combine to17021 row17027 rfl

set_option maxRecDepth 16000 in
private theorem row17029 :
    FinalSeventhSieve.rough 11092009835083 17029+34677312=FinalSeventhSieve.rough 11092009835083 17027 :=
  LargeQuotientSieve.row (p:=17029) (q:=651360023) (s:=25521) (rank:=33860618) (tiny:=1963) (pairs:=818656)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 651360023 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17029 : FinalSeventhSieve.rough 11092009835083 17029+417380653=FinalSeventhSieve.rough 11092009835083 16927 :=
  LargeQuotientSieve.combine to17027 row17029 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 17029+417380653=FinalSeventhSieve.rough 11092009835083 16927 := to17029

end Tail11092009835083From16927To17029
