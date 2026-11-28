import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-650000000-675000000»

/-! Exact changes for sieve primes 1941 through 1952. -/
open Finset
namespace Tail11092009835083From16811To16927

set_option maxRecDepth 16000 in
private theorem row16823 :
    FinalSeventhSieve.rough 11092009835083 16823+35151068=FinalSeventhSieve.rough 11092009835083 16811 :=
  LargeQuotientSieve.row (p:=16823) (q:=659336018) (s:=25677) (rank:=34253495) (tiny:=1940) (pairs:=899512)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 659336018 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row16829 :
    FinalSeventhSieve.rough 11092009835083 16829+35136206=FinalSeventhSieve.rough 11092009835083 16823 :=
  LargeQuotientSieve.row (p:=16829) (q:=659100946) (s:=25672) (rank:=34241791) (tiny:=1941) (pairs:=896355)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 659100946 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16829 : FinalSeventhSieve.rough 11092009835083 16829+70287274=FinalSeventhSieve.rough 11092009835083 16811 :=
  LargeQuotientSieve.combine row16823 row16829 rfl

set_option maxRecDepth 16000 in
private theorem row16831 :
    FinalSeventhSieve.rough 11092009835083 16831+35129884=FinalSeventhSieve.rough 11092009835083 16829 :=
  LargeQuotientSieve.row (p:=16831) (q:=659022627) (s:=25671) (rank:=34237967) (tiny:=1942) (pairs:=893858)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 659022627 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16831 : FinalSeventhSieve.rough 11092009835083 16831+105417158=FinalSeventhSieve.rough 11092009835083 16811 :=
  LargeQuotientSieve.combine to16829 row16831 rfl

set_option maxRecDepth 16000 in
private theorem row16843 :
    FinalSeventhSieve.rough 11092009835083 16843+35102579=FinalSeventhSieve.rough 11092009835083 16831 :=
  LargeQuotientSieve.row (p:=16843) (q:=658553098) (s:=25662) (rank:=34214789) (tiny:=1943) (pairs:=889732)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 658553098 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16843 : FinalSeventhSieve.rough 11092009835083 16843+140519737=FinalSeventhSieve.rough 11092009835083 16811 :=
  LargeQuotientSieve.combine to16831 row16843 rfl

set_option maxRecDepth 16000 in
private theorem row16871 :
    FinalSeventhSieve.rough 11092009835083 16871+35042287=FinalSeventhSieve.rough 11092009835083 16843 :=
  LargeQuotientSieve.row (p:=16871) (q:=657460128) (s:=25640) (rank:=34161080) (tiny:=1944) (pairs:=883150)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 657460128 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16871 : FinalSeventhSieve.rough 11092009835083 16871+175562024=FinalSeventhSieve.rough 11092009835083 16811 :=
  LargeQuotientSieve.combine to16843 row16871 rfl

set_option maxRecDepth 16000 in
private theorem row16879 :
    FinalSeventhSieve.rough 11092009835083 16879+35023463=FinalSeventhSieve.rough 11092009835083 16871 :=
  LargeQuotientSieve.row (p:=16879) (q:=657148517) (s:=25634) (rank:=34145669) (tiny:=1945) (pairs:=879738)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 657148517 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16879 : FinalSeventhSieve.rough 11092009835083 16879+210585487=FinalSeventhSieve.rough 11092009835083 16811 :=
  LargeQuotientSieve.combine to16871 row16879 rfl

set_option maxRecDepth 16000 in
private theorem row16883 :
    FinalSeventhSieve.rough 11092009835083 16883+35012975=FinalSeventhSieve.rough 11092009835083 16879 :=
  LargeQuotientSieve.row (p:=16883) (q:=656992823) (s:=25631) (rank:=34137974) (tiny:=1946) (pairs:=876946)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 656992823 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16883 : FinalSeventhSieve.rough 11092009835083 16883+245598462=FinalSeventhSieve.rough 11092009835083 16811 :=
  LargeQuotientSieve.combine to16879 row16883 rfl

set_option maxRecDepth 16000 in
private theorem row16889 :
    FinalSeventhSieve.rough 11092009835083 16889+34998401=FinalSeventhSieve.rough 11092009835083 16883 :=
  LargeQuotientSieve.row (p:=16889) (q:=656759419) (s:=25627) (rank:=34126491) (tiny:=1947) (pairs:=873856)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 656759419 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16889 : FinalSeventhSieve.rough 11092009835083 16889+280596863=FinalSeventhSieve.rough 11092009835083 16811 :=
  LargeQuotientSieve.combine to16883 row16889 rfl

set_option maxRecDepth 16000 in
private theorem row16901 :
    FinalSeventhSieve.rough 11092009835083 16901+34971350=FinalSeventhSieve.rough 11092009835083 16889 :=
  LargeQuotientSieve.row (p:=16901) (q:=656293108) (s:=25618) (rank:=34103485) (tiny:=1948) (pairs:=869812)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 656293108 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16901 : FinalSeventhSieve.rough 11092009835083 16901+315568213=FinalSeventhSieve.rough 11092009835083 16811 :=
  LargeQuotientSieve.combine to16889 row16901 rfl

set_option maxRecDepth 16000 in
private theorem row16903 :
    FinalSeventhSieve.rough 11092009835083 16903+34965078=FinalSeventhSieve.rough 11092009835083 16901 :=
  LargeQuotientSieve.row (p:=16903) (q:=656215454) (s:=25616) (rank:=34099654) (tiny:=1949) (pairs:=867372)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 656215454 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16903 : FinalSeventhSieve.rough 11092009835083 16903+350533291=FinalSeventhSieve.rough 11092009835083 16811 :=
  LargeQuotientSieve.combine to16901 row16903 rfl

set_option maxRecDepth 16000 in
private theorem row16921 :
    FinalSeventhSieve.rough 11092009835083 16921+34925743=FinalSeventhSieve.rough 11092009835083 16903 :=
  LargeQuotientSieve.row (p:=16921) (q:=655517394) (s:=25603) (rank:=34065251) (tiny:=1950) (pairs:=862441)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 655517394 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16921 : FinalSeventhSieve.rough 11092009835083 16921+385459034=FinalSeventhSieve.rough 11092009835083 16811 :=
  LargeQuotientSieve.combine to16903 row16921 rfl

set_option maxRecDepth 16000 in
private theorem row16927 :
    FinalSeventhSieve.rough 11092009835083 16927+34911285=FinalSeventhSieve.rough 11092009835083 16921 :=
  LargeQuotientSieve.row (p:=16927) (q:=655285037) (s:=25598) (rank:=34053867) (tiny:=1951) (pairs:=859368)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 655285037 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16927 : FinalSeventhSieve.rough 11092009835083 16927+420370319=FinalSeventhSieve.rough 11092009835083 16811 :=
  LargeQuotientSieve.combine to16921 row16927 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 16927+420370319=FinalSeventhSieve.rough 11092009835083 16811 := to16927

end Tail11092009835083From16811To16927
