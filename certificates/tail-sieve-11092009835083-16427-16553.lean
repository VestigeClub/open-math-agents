import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-650000000-675000000»

/-! Exact changes for sieve primes 1905 through 1916. -/
open Finset
namespace Tail11092009835083From16427To16553

set_option maxRecDepth 16000 in
private theorem row16433 :
    FinalSeventhSieve.rough 11092009835083 16433+36070138=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.row (p:=16433) (q:=674983863) (s:=25980) (rank:=35023557) (tiny:=1904) (pairs:=1048484)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 674983863 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row16447 :
    FinalSeventhSieve.rough 11092009835083 16447+36036897=FinalSeventhSieve.rough 11092009835083 16433 :=
  LargeQuotientSieve.row (p:=16447) (q:=674409304) (s:=25969) (rank:=34995225) (tiny:=1905) (pairs:=1043576)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 674409304 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16447 : FinalSeventhSieve.rough 11092009835083 16447+72107035=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine row16433 row16447 rfl

set_option maxRecDepth 16000 in
private theorem row16451 :
    FinalSeventhSieve.rough 11092009835083 16451+36025737=FinalSeventhSieve.rough 11092009835083 16447 :=
  LargeQuotientSieve.row (p:=16451) (q:=674245324) (s:=25966) (rank:=34987190) (tiny:=1906) (pairs:=1040452)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 674245324 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16451 : FinalSeventhSieve.rough 11092009835083 16451+108132772=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16447 row16451 rfl

set_option maxRecDepth 16000 in
private theorem row16453 :
    FinalSeventhSieve.rough 11092009835083 16453+36019047=FinalSeventhSieve.rough 11092009835083 16451 :=
  LargeQuotientSieve.row (p:=16453) (q:=674163364) (s:=25964) (rank:=34983230) (tiny:=1907) (pairs:=1037723)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 674163364 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16453 : FinalSeventhSieve.rough 11092009835083 16453+144151819=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16451 row16453 rfl

set_option maxRecDepth 16000 in
private theorem row16477 :
    FinalSeventhSieve.rough 11092009835083 16477+35964141=FinalSeventhSieve.rough 11092009835083 16453 :=
  LargeQuotientSieve.row (p:=16477) (q:=673181394) (s:=25945) (rank:=34935003) (tiny:=1908) (pairs:=1031045)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 673181394 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16477 : FinalSeventhSieve.rough 11092009835083 16477+180115960=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16453 row16477 rfl

set_option maxRecDepth 16000 in
private theorem row16481 :
    FinalSeventhSieve.rough 11092009835083 16481+35952971=FinalSeventhSieve.rough 11092009835083 16477 :=
  LargeQuotientSieve.row (p:=16481) (q:=673018010) (s:=25942) (rank:=34926906) (tiny:=1909) (pairs:=1027973)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 673018010 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16481 : FinalSeventhSieve.rough 11092009835083 16481+216068931=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16477 row16481 rfl

set_option maxRecDepth 16000 in
private theorem row16487 :
    FinalSeventhSieve.rough 11092009835083 16487+35937491=FinalSeventhSieve.rough 11092009835083 16481 :=
  LargeQuotientSieve.row (p:=16487) (q:=672773083) (s:=25937) (rank:=34914847) (tiny:=1910) (pairs:=1024553)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 672773083 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16487 : FinalSeventhSieve.rough 11092009835083 16487+252006422=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16481 row16487 rfl

set_option maxRecDepth 16000 in
private theorem row16493 :
    FinalSeventhSieve.rough 11092009835083 16493+35921911=FinalSeventhSieve.rough 11092009835083 16487 :=
  LargeQuotientSieve.row (p:=16493) (q:=672528335) (s:=25933) (rank:=34902706) (tiny:=1911) (pairs:=1021115)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 672528335 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16493 : FinalSeventhSieve.rough 11092009835083 16493+287928333=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16487 row16493 rfl

set_option maxRecDepth 16000 in
private theorem row16519 :
    FinalSeventhSieve.rough 11092009835083 16519+35862935=FinalSeventhSieve.rough 11092009835083 16493 :=
  LargeQuotientSieve.row (p:=16519) (q:=671469812) (s:=25912) (rank:=34850723) (tiny:=1912) (pairs:=1014123)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 671469812 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16519 : FinalSeventhSieve.rough 11092009835083 16519+323791268=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16493 row16519 rfl

set_option maxRecDepth 16000 in
private theorem row16529 :
    FinalSeventhSieve.rough 11092009835083 16529+35838944=FinalSeventhSieve.rough 11092009835083 16519 :=
  LargeQuotientSieve.row (p:=16529) (q:=671063575) (s:=25904) (rank:=34830804) (tiny:=1913) (pairs:=1010052)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 671063575 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16529 : FinalSeventhSieve.rough 11092009835083 16529+359630212=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16519 row16529 rfl

set_option maxRecDepth 16000 in
private theorem row16547 :
    FinalSeventhSieve.rough 11092009835083 16547+35797500=FinalSeventhSieve.rough 11092009835083 16529 :=
  LargeQuotientSieve.row (p:=16547) (q:=670333585) (s:=25890) (rank:=34794858) (tiny:=1914) (pairs:=1004555)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 670333585 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16547 : FinalSeventhSieve.rough 11092009835083 16547+395427712=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16529 row16547 rfl

set_option maxRecDepth 16000 in
private theorem row16553 :
    FinalSeventhSieve.rough 11092009835083 16553+35782072=FinalSeventhSieve.rough 11092009835083 16547 :=
  LargeQuotientSieve.row (p:=16553) (q:=670090608) (s:=25886) (rank:=34782780) (tiny:=1915) (pairs:=1001206)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 670090608 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16553 : FinalSeventhSieve.rough 11092009835083 16553+431209784=FinalSeventhSieve.rough 11092009835083 16427 :=
  LargeQuotientSieve.combine to16547 row16553 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 16553+431209784=FinalSeventhSieve.rough 11092009835083 16427 := to16553

end Tail11092009835083From16427To16553
