import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-900000000-925000000»

/-! Exact changes for sieve primes 1463 through 1472. -/
open Finset
namespace Tail11092009835083From12239To12323

set_option maxRecDepth 16000 in
private theorem row12241 :
    FinalSeventhSieve.rough 11092009835083 12241+50603684=FinalSeventhSieve.rough 11092009835083 12239 :=
  LargeQuotientSieve.row (p:=12241) (q:=906135923) (s:=30102) (rank:=46306826) (tiny:=1462) (pairs:=4298319)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 906135923 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row12251 :
    FinalSeventhSieve.rough 11092009835083 12251+50555658=FinalSeventhSieve.rough 11092009835083 12241 :=
  LargeQuotientSieve.row (p:=12251) (q:=905396280) (s:=30089) (rank:=46270876) (tiny:=1463) (pairs:=4286244)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 905396280 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12251 : FinalSeventhSieve.rough 11092009835083 12251+101159342=FinalSeventhSieve.rough 11092009835083 12239 :=
  LargeQuotientSieve.combine row12241 row12251 rfl

set_option maxRecDepth 16000 in
private theorem row12253 :
    FinalSeventhSieve.rough 11092009835083 12253+50541349=FinalSeventhSieve.rough 11092009835083 12251 :=
  LargeQuotientSieve.row (p:=12253) (q:=905248497) (s:=30087) (rank:=46263658) (tiny:=1464) (pairs:=4279154)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 905248497 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12253 : FinalSeventhSieve.rough 11092009835083 12253+151700691=FinalSeventhSieve.rough 11092009835083 12239 :=
  LargeQuotientSieve.combine to12251 row12253 rfl

set_option maxRecDepth 16000 in
private theorem row12263 :
    FinalSeventhSieve.rough 11092009835083 12263+50493579=FinalSeventhSieve.rough 11092009835083 12253 :=
  LargeQuotientSieve.row (p:=12263) (q:=904510302) (s:=30075) (rank:=46227981) (tiny:=1465) (pairs:=4267062)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 904510302 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12263 : FinalSeventhSieve.rough 11092009835083 12263+202194270=FinalSeventhSieve.rough 11092009835083 12239 :=
  LargeQuotientSieve.combine to12253 row12263 rfl

set_option maxRecDepth 16000 in
private theorem row12269 :
    FinalSeventhSieve.rough 11092009835083 12269+50462523=FinalSeventhSieve.rough 11092009835083 12263 :=
  LargeQuotientSieve.row (p:=12269) (q:=904067962) (s:=30067) (rank:=46206533) (tiny:=1466) (pairs:=4257455)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 904067962 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12269 : FinalSeventhSieve.rough 11092009835083 12269+252656793=FinalSeventhSieve.rough 11092009835083 12239 :=
  LargeQuotientSieve.combine to12263 row12269 rfl

set_option maxRecDepth 16000 in
private theorem row12277 :
    FinalSeventhSieve.rough 11092009835083 12277+50423225=FinalSeventhSieve.rough 11092009835083 12269 :=
  LargeQuotientSieve.row (p:=12277) (q:=903478849) (s:=30057) (rank:=46178014) (tiny:=1467) (pairs:=4246677)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 903478849 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12277 : FinalSeventhSieve.rough 11092009835083 12277+303080018=FinalSeventhSieve.rough 11092009835083 12239 :=
  LargeQuotientSieve.combine to12269 row12277 rfl

set_option maxRecDepth 16000 in
private theorem row12281 :
    FinalSeventhSieve.rough 11092009835083 12281+50400561=FinalSeventhSieve.rough 11092009835083 12277 :=
  LargeQuotientSieve.row (p:=12281) (q:=903184580) (s:=30053) (rank:=46163616) (tiny:=1468) (pairs:=4238412)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 903184580 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12281 : FinalSeventhSieve.rough 11092009835083 12281+353480579=FinalSeventhSieve.rough 11092009835083 12239 :=
  LargeQuotientSieve.combine to12277 row12281 rfl

set_option maxRecDepth 16000 in
private theorem row12289 :
    FinalSeventhSieve.rough 11092009835083 12289+50361403=FinalSeventhSieve.rough 11092009835083 12281 :=
  LargeQuotientSieve.row (p:=12289) (q:=902596617) (s:=30043) (rank:=46135175) (tiny:=1469) (pairs:=4227696)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 902596617 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12289 : FinalSeventhSieve.rough 11092009835083 12289+403841982=FinalSeventhSieve.rough 11092009835083 12239 :=
  LargeQuotientSieve.combine to12281 row12289 rfl

set_option maxRecDepth 16000 in
private theorem row12301 :
    FinalSeventhSieve.rough 11092009835083 12301+50305626=FinalSeventhSieve.rough 11092009835083 12289 :=
  LargeQuotientSieve.row (p:=12301) (q:=901716107) (s:=30028) (rank:=46092641) (tiny:=1470) (pairs:=4214454)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 901716107 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12301 : FinalSeventhSieve.rough 11092009835083 12301+454147608=FinalSeventhSieve.rough 11092009835083 12239 :=
  LargeQuotientSieve.combine to12289 row12301 rfl

set_option maxRecDepth 16000 in
private theorem row12323 :
    FinalSeventhSieve.rough 11092009835083 12323+50208195=FinalSeventhSieve.rough 11092009835083 12301 :=
  LargeQuotientSieve.row (p:=12323) (q:=900106291) (s:=30001) (rank:=46014373) (tiny:=1471) (pairs:=4195292)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ900000000To925000000.count_correct 900106291 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to12323 : FinalSeventhSieve.rough 11092009835083 12323+504355803=FinalSeventhSieve.rough 11092009835083 12239 :=
  LargeQuotientSieve.combine to12301 row12323 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 12323+504355803=FinalSeventhSieve.rough 11092009835083 12239 := to12323

end Tail11092009835083From12239To12323
