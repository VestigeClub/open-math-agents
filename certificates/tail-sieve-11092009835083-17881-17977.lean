import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-600000000-625000000»

/-! Exact changes for sieve primes 2050 through 2061. -/
open Finset
namespace Tail11092009835083From17881To17977

set_option maxRecDepth 16000 in
private theorem row17891 :
    FinalSeventhSieve.rough 11092009835083 17891+32856889=FinalSeventhSieve.rough 11092009835083 17881 :=
  LargeQuotientSieve.row (p:=17891) (q:=619977074) (s:=24899) (rank:=32312237) (tiny:=2049) (pairs:=546700)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 619977074 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row17903 :
    FinalSeventhSieve.rough 11092009835083 17903+32833335=FinalSeventhSieve.rough 11092009835083 17891 :=
  LargeQuotientSieve.row (p:=17903) (q:=619561516) (s:=24890) (rank:=32291676) (tiny:=2050) (pairs:=543708)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 619561516 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17903 : FinalSeventhSieve.rough 11092009835083 17903+65690224=FinalSeventhSieve.rough 11092009835083 17881 :=
  LargeQuotientSieve.combine row17891 row17903 rfl

set_option maxRecDepth 16000 in
private theorem row17909 :
    FinalSeventhSieve.rough 11092009835083 17909+32820730=FinalSeventhSieve.rough 11092009835083 17903 :=
  LargeQuotientSieve.row (p:=17909) (q:=619353946) (s:=24886) (rank:=32281382) (tiny:=2051) (pairs:=541398)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 619353946 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17909 : FinalSeventhSieve.rough 11092009835083 17909+98510954=FinalSeventhSieve.rough 11092009835083 17881 :=
  LargeQuotientSieve.combine to17903 row17909 rfl

set_option maxRecDepth 16000 in
private theorem row17911 :
    FinalSeventhSieve.rough 11092009835083 17911+32815417=FinalSeventhSieve.rough 11092009835083 17909 :=
  LargeQuotientSieve.row (p:=17911) (q:=619284787) (s:=24885) (rank:=32277926) (tiny:=2052) (pairs:=539542)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 619284787 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17911 : FinalSeventhSieve.rough 11092009835083 17911+131326371=FinalSeventhSieve.rough 11092009835083 17881 :=
  LargeQuotientSieve.combine to17909 row17911 rfl

set_option maxRecDepth 16000 in
private theorem row17921 :
    FinalSeventhSieve.rough 11092009835083 17921+32795653=FinalSeventhSieve.rough 11092009835083 17911 :=
  LargeQuotientSieve.row (p:=17921) (q:=618939224) (s:=24878) (rank:=32260911) (tiny:=2053) (pairs:=536794)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 618939224 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17921 : FinalSeventhSieve.rough 11092009835083 17921+164122024=FinalSeventhSieve.rough 11092009835083 17881 :=
  LargeQuotientSieve.combine to17911 row17921 rfl

set_option maxRecDepth 16000 in
private theorem row17923 :
    FinalSeventhSieve.rough 11092009835083 17923+32790396=FinalSeventhSieve.rough 11092009835083 17921 :=
  LargeQuotientSieve.row (p:=17923) (q:=618870157) (s:=24877) (rank:=32257512) (tiny:=2054) (pairs:=534937)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 618870157 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17923 : FinalSeventhSieve.rough 11092009835083 17923+196912420=FinalSeventhSieve.rough 11092009835083 17881 :=
  LargeQuotientSieve.combine to17921 row17923 rfl

set_option maxRecDepth 16000 in
private theorem row17929 :
    FinalSeventhSieve.rough 11092009835083 17929+32777938=FinalSeventhSieve.rough 11092009835083 17923 :=
  LargeQuotientSieve.row (p:=17929) (q:=618663050) (s:=24872) (rank:=32247372) (tiny:=2055) (pairs:=532620)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 618663050 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17929 : FinalSeventhSieve.rough 11092009835083 17929+229690358=FinalSeventhSieve.rough 11092009835083 17881 :=
  LargeQuotientSieve.combine to17923 row17929 rfl

set_option maxRecDepth 16000 in
private theorem row17939 :
    FinalSeventhSieve.rough 11092009835083 17939+32758035=FinalSeventhSieve.rough 11092009835083 17929 :=
  LargeQuotientSieve.row (p:=17939) (q:=618318180) (s:=24866) (rank:=32230208) (tiny:=2056) (pairs:=529882)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 618318180 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17939 : FinalSeventhSieve.rough 11092009835083 17939+262448393=FinalSeventhSieve.rough 11092009835083 17881 :=
  LargeQuotientSieve.combine to17929 row17939 rfl

set_option maxRecDepth 16000 in
private theorem row17957 :
    FinalSeventhSieve.rough 11092009835083 17957+32723784=FinalSeventhSieve.rough 11092009835083 17939 :=
  LargeQuotientSieve.row (p:=17957) (q:=617698381) (s:=24853) (rank:=32199548) (tiny:=2057) (pairs:=526292)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 617698381 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17957 : FinalSeventhSieve.rough 11092009835083 17957+295172177=FinalSeventhSieve.rough 11092009835083 17881 :=
  LargeQuotientSieve.combine to17939 row17957 rfl

set_option maxRecDepth 16000 in
private theorem row17959 :
    FinalSeventhSieve.rough 11092009835083 17959+32718552=FinalSeventhSieve.rough 11092009835083 17957 :=
  LargeQuotientSieve.row (p:=17959) (q:=617629591) (s:=24852) (rank:=32196146) (tiny:=2058) (pairs:=524463)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 617629591 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17959 : FinalSeventhSieve.rough 11092009835083 17959+327890729=FinalSeventhSieve.rough 11092009835083 17881 :=
  LargeQuotientSieve.combine to17957 row17959 rfl

set_option maxRecDepth 16000 in
private theorem row17971 :
    FinalSeventhSieve.rough 11092009835083 17971+32695496=FinalSeventhSieve.rough 11092009835083 17959 :=
  LargeQuotientSieve.row (p:=17971) (q:=617217174) (s:=24843) (rank:=32176008) (tiny:=2059) (pairs:=521546)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 617217174 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17971 : FinalSeventhSieve.rough 11092009835083 17971+360586225=FinalSeventhSieve.rough 11092009835083 17881 :=
  LargeQuotientSieve.combine to17959 row17971 rfl

set_option maxRecDepth 16000 in
private theorem row17977 :
    FinalSeventhSieve.rough 11092009835083 17977+32683160=FinalSeventhSieve.rough 11092009835083 17971 :=
  LargeQuotientSieve.row (p:=17977) (q:=617011171) (s:=24839) (rank:=32165948) (tiny:=2060) (pairs:=519271)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ600000000To625000000.count_correct 617011171 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17977 : FinalSeventhSieve.rough 11092009835083 17977+393269385=FinalSeventhSieve.rough 11092009835083 17881 :=
  LargeQuotientSieve.combine to17971 row17977 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 17977+393269385=FinalSeventhSieve.rough 11092009835083 17881 := to17977

end Tail11092009835083From17881To17977
