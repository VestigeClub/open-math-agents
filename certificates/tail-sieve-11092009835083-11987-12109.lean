import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-900000000-925000000»

/-! Exact changes for sieve primes 1439 through 1450. -/
open Finset
namespace Tail11092009835083From11987To12109

set_option maxRecDepth 16000 in
private theorem row12007 :
    FinalSeventhSieve.rough 11092009835083 12007+51755190=FinalSeventhSieve.rough 11092009835083 11987 :=
  LargeQuotientSieve.row (p:=12007) (q:=923795272) (s:=30394) (rank:=47163294) (tiny:=1438) (pairs:=4593333)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 923795272 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row12011 :
    FinalSeventhSieve.rough 11092009835083 12011+51731540=FinalSeventhSieve.rough 11092009835083 12007 :=
  LargeQuotientSieve.row (p:=12011) (q:=923487622) (s:=30388) (rank:=47148460) (tiny:=1439) (pairs:=4584518)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 923487622 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12011 : FinalSeventhSieve.rough 11092009835083 12011+103486730=FinalSeventhSieve.rough 11092009835083 11987 :=
  LargeQuotientSieve.combine row12007 row12011 rfl

set_option maxRecDepth 16000 in
private theorem row12037 :
    FinalSeventhSieve.rough 11092009835083 12037+51611522=FinalSeventhSieve.rough 11092009835083 12011 :=
  LargeQuotientSieve.row (p:=12037) (q:=921492883) (s:=30356) (rank:=47051945) (tiny:=1440) (pairs:=4561016)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 921492883 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12037 : FinalSeventhSieve.rough 11092009835083 12037+155098252=FinalSeventhSieve.rough 11092009835083 11987 :=
  LargeQuotientSieve.combine to12011 row12037 rfl

set_option maxRecDepth 16000 in
private theorem row12041 :
    FinalSeventhSieve.rough 11092009835083 12041+51588057=FinalSeventhSieve.rough 11092009835083 12037 :=
  LargeQuotientSieve.row (p:=12041) (q:=921186764) (s:=30351) (rank:=47037257) (tiny:=1441) (pairs:=4552240)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 921186764 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12041 : FinalSeventhSieve.rough 11092009835083 12041+206686309=FinalSeventhSieve.rough 11092009835083 11987 :=
  LargeQuotientSieve.combine to12037 row12041 rfl

set_option maxRecDepth 16000 in
private theorem row12043 :
    FinalSeventhSieve.rough 11092009835083 12043+51573242=FinalSeventhSieve.rough 11092009835083 12041 :=
  LargeQuotientSieve.row (p:=12043) (q:=921033781) (s:=30348) (rank:=47029850) (tiny:=1442) (pairs:=4544833)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 921033781 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12043 : FinalSeventhSieve.rough 11092009835083 12043+258259551=FinalSeventhSieve.rough 11092009835083 11987 :=
  LargeQuotientSieve.combine to12041 row12043 rfl

set_option maxRecDepth 16000 in
private theorem row12049 :
    FinalSeventhSieve.rough 11092009835083 12049+51540808=FinalSeventhSieve.rough 11092009835083 12043 :=
  LargeQuotientSieve.row (p:=12049) (q:=920575137) (s:=30340) (rank:=47007470) (tiny:=1443) (pairs:=4534780)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 920575137 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12049 : FinalSeventhSieve.rough 11092009835083 12049+309800359=FinalSeventhSieve.rough 11092009835083 11987 :=
  LargeQuotientSieve.combine to12043 row12049 rfl

set_option maxRecDepth 16000 in
private theorem row12071 :
    FinalSeventhSieve.rough 11092009835083 12071+51438869=FinalSeventhSieve.rough 11092009835083 12049 :=
  LargeQuotientSieve.row (p:=12071) (q:=918897343) (s:=30313) (rank:=46925972) (tiny:=1444) (pairs:=4514340)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 918897343 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12071 : FinalSeventhSieve.rough 11092009835083 12071+361239228=FinalSeventhSieve.rough 11092009835083 11987 :=
  LargeQuotientSieve.combine to12049 row12071 rfl

set_option maxRecDepth 16000 in
private theorem row12073 :
    FinalSeventhSieve.rough 11092009835083 12073+51424101=FinalSeventhSieve.rough 11092009835083 12071 :=
  LargeQuotientSieve.row (p:=12073) (q:=918745120) (s:=30310) (rank:=46918566) (tiny:=1445) (pairs:=4506979)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 918745120 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12073 : FinalSeventhSieve.rough 11092009835083 12073+412663329=FinalSeventhSieve.rough 11092009835083 11987 :=
  LargeQuotientSieve.combine to12071 row12073 rfl

set_option maxRecDepth 16000 in
private theorem row12097 :
    FinalSeventhSieve.rough 11092009835083 12097+51314141=FinalSeventhSieve.rough 11092009835083 12073 :=
  LargeQuotientSieve.row (p:=12097) (q:=916922363) (s:=30280) (rank:=46830413) (tiny:=1446) (pairs:=4485173)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 916922363 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12097 : FinalSeventhSieve.rough 11092009835083 12097+463977470=FinalSeventhSieve.rough 11092009835083 11987 :=
  LargeQuotientSieve.combine to12073 row12097 rfl

set_option maxRecDepth 16000 in
private theorem row12101 :
    FinalSeventhSieve.rough 11092009835083 12101+51290838=FinalSeventhSieve.rough 11092009835083 12097 :=
  LargeQuotientSieve.row (p:=12101) (q:=916619274) (s:=30275) (rank:=46815721) (tiny:=1447) (pairs:=4476563)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 916619274 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12101 : FinalSeventhSieve.rough 11092009835083 12101+515268308=FinalSeventhSieve.rough 11092009835083 11987 :=
  LargeQuotientSieve.combine to12097 row12101 rfl

set_option maxRecDepth 16000 in
private theorem row12107 :
    FinalSeventhSieve.rough 11092009835083 12107+51258930=FinalSeventhSieve.rough 11092009835083 12101 :=
  LargeQuotientSieve.row (p:=12107) (q:=916165014) (s:=30268) (rank:=46793741) (tiny:=1448) (pairs:=4466636)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 916165014 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12107 : FinalSeventhSieve.rough 11092009835083 12107+566527238=FinalSeventhSieve.rough 11092009835083 11987 :=
  LargeQuotientSieve.combine to12101 row12107 rfl

set_option maxRecDepth 16000 in
private theorem row12109 :
    FinalSeventhSieve.rough 11092009835083 12109+51244203=FinalSeventhSieve.rough 11092009835083 12107 :=
  LargeQuotientSieve.row (p:=12109) (q:=916013695) (s:=30265) (rank:=46786299) (tiny:=1449) (pairs:=4459352)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 916013695 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12109 : FinalSeventhSieve.rough 11092009835083 12109+617771441=FinalSeventhSieve.rough 11092009835083 11987 :=
  LargeQuotientSieve.combine to12107 row12109 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 12109+617771441=FinalSeventhSieve.rough 11092009835083 11987 := to12109

end Tail11092009835083From11987To12109
