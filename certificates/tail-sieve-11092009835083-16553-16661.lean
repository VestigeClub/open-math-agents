import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-650000000-675000000»

/-! Exact changes for sieve primes 1917 through 1928. -/
open Finset
namespace Tail11092009835083From16553To16661

set_option maxRecDepth 16000 in
private theorem row16561 :
    FinalSeventhSieve.rough 11092009835083 16561+35762420=FinalSeventhSieve.rough 11092009835083 16553 :=
  LargeQuotientSieve.row (p:=16561) (q:=669766912) (s:=25879) (rank:=34766860) (tiny:=1916) (pairs:=997475)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 669766912 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row16567 :
    FinalSeventhSieve.rough 11092009835083 16567+35747133=FinalSeventhSieve.rough 11092009835083 16561 :=
  LargeQuotientSieve.row (p:=16567) (q:=669524345) (s:=25875) (rank:=34754950) (tiny:=1917) (pairs:=994099)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 669524345 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16567 : FinalSeventhSieve.rough 11092009835083 16567+71509553=FinalSeventhSieve.rough 11092009835083 16553 :=
  LargeQuotientSieve.combine row16561 row16567 rfl

set_option maxRecDepth 16000 in
private theorem row16573 :
    FinalSeventhSieve.rough 11092009835083 16573+35731894=FinalSeventhSieve.rough 11092009835083 16567 :=
  LargeQuotientSieve.row (p:=16573) (q:=669281954) (s:=25870) (rank:=34743038) (tiny:=1918) (pairs:=990773)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 669281954 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16573 : FinalSeventhSieve.rough 11092009835083 16573+107241447=FinalSeventhSieve.rough 11092009835083 16553 :=
  LargeQuotientSieve.combine to16567 row16573 rfl

set_option maxRecDepth 16000 in
private theorem row16603 :
    FinalSeventhSieve.rough 11092009835083 16603+35664938=FinalSeventhSieve.rough 11092009835083 16573 :=
  LargeQuotientSieve.row (p:=16603) (q:=668072627) (s:=25847) (rank:=34683535) (tiny:=1919) (pairs:=983321)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 668072627 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16603 : FinalSeventhSieve.rough 11092009835083 16603+142906385=FinalSeventhSieve.rough 11092009835083 16553 :=
  LargeQuotientSieve.combine to16573 row16603 rfl

set_option maxRecDepth 16000 in
private theorem row16607 :
    FinalSeventhSieve.rough 11092009835083 16607+35654033=FinalSeventhSieve.rough 11092009835083 16603 :=
  LargeQuotientSieve.row (p:=16607) (q:=667911714) (s:=25843) (rank:=34675630) (tiny:=1920) (pairs:=980322)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 667911714 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16607 : FinalSeventhSieve.rough 11092009835083 16607+178560418=FinalSeventhSieve.rough 11092009835083 16553 :=
  LargeQuotientSieve.combine to16603 row16607 rfl

set_option maxRecDepth 16000 in
private theorem row16619 :
    FinalSeventhSieve.rough 11092009835083 16619+35626045=FinalSeventhSieve.rough 11092009835083 16607 :=
  LargeQuotientSieve.row (p:=16619) (q:=667429438) (s:=25834) (rank:=34652016) (tiny:=1921) (pairs:=975949)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 667429438 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16619 : FinalSeventhSieve.rough 11092009835083 16619+214186463=FinalSeventhSieve.rough 11092009835083 16553 :=
  LargeQuotientSieve.combine to16607 row16619 rfl

set_option maxRecDepth 16000 in
private theorem row16631 :
    FinalSeventhSieve.rough 11092009835083 16631+35597981=FinalSeventhSieve.rough 11092009835083 16619 :=
  LargeQuotientSieve.row (p:=16631) (q:=666947858) (s:=25825) (rank:=34628276) (tiny:=1922) (pairs:=971626)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 666947858 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16631 : FinalSeventhSieve.rough 11092009835083 16631+249784444=FinalSeventhSieve.rough 11092009835083 16553 :=
  LargeQuotientSieve.combine to16619 row16631 rfl

set_option maxRecDepth 16000 in
private theorem row16633 :
    FinalSeventhSieve.rough 11092009835083 16633+35591409=FinalSeventhSieve.rough 11092009835083 16631 :=
  LargeQuotientSieve.row (p:=16633) (q:=666867662) (s:=25823) (rank:=34624341) (tiny:=1923) (pairs:=968990)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 666867662 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16633 : FinalSeventhSieve.rough 11092009835083 16633+285375853=FinalSeventhSieve.rough 11092009835083 16553 :=
  LargeQuotientSieve.combine to16631 row16633 rfl

set_option maxRecDepth 16000 in
private theorem row16649 :
    FinalSeventhSieve.rough 11092009835083 16649+35554840=FinalSeventhSieve.rough 11092009835083 16633 :=
  LargeQuotientSieve.row (p:=16649) (q:=666226790) (s:=25811) (rank:=34592778) (tiny:=1924) (pairs:=963985)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 666226790 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16649 : FinalSeventhSieve.rough 11092009835083 16649+320930693=FinalSeventhSieve.rough 11092009835083 16553 :=
  LargeQuotientSieve.combine to16633 row16649 rfl

set_option maxRecDepth 16000 in
private theorem row16651 :
    FinalSeventhSieve.rough 11092009835083 16651+35548282=FinalSeventhSieve.rough 11092009835083 16649 :=
  LargeQuotientSieve.row (p:=16651) (q:=666146768) (s:=25809) (rank:=34588834) (tiny:=1925) (pairs:=961372)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 666146768 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16651 : FinalSeventhSieve.rough 11092009835083 16651+356478975=FinalSeventhSieve.rough 11092009835083 16553 :=
  LargeQuotientSieve.combine to16649 row16651 rfl

set_option maxRecDepth 16000 in
private theorem row16657 :
    FinalSeventhSieve.rough 11092009835083 16657+35533223=FinalSeventhSieve.rough 11092009835083 16651 :=
  LargeQuotientSieve.row (p:=16657) (q:=665906816) (s:=25805) (rank:=34577060) (tiny:=1926) (pairs:=958088)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 665906816 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16657 : FinalSeventhSieve.rough 11092009835083 16657+392012198=FinalSeventhSieve.rough 11092009835083 16553 :=
  LargeQuotientSieve.combine to16651 row16657 rfl

set_option maxRecDepth 16000 in
private theorem row16661 :
    FinalSeventhSieve.rough 11092009835083 16661+35522448=FinalSeventhSieve.rough 11092009835083 16657 :=
  LargeQuotientSieve.row (p:=16661) (q:=665746944) (s:=25802) (rank:=34569253) (tiny:=1927) (pairs:=955121)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ650000000To675000000.count_correct 665746944 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to16661 : FinalSeventhSieve.rough 11092009835083 16661+427534646=FinalSeventhSieve.rough 11092009835083 16553 :=
  LargeQuotientSieve.combine to16657 row16661 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 16661+427534646=FinalSeventhSieve.rough 11092009835083 16553 := to16661

end Tail11092009835083From16553To16661
