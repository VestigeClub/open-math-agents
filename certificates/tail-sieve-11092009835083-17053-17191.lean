import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-625000000-650000000»

/-! Exact changes for sieve primes 1969 through 1980. -/
open Finset
namespace Tail11092009835083From17053To17191

set_option maxRecDepth 16000 in
private theorem row17077 :
    FinalSeventhSieve.rough 11092009835083 17077+34569469=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.row (p:=17077) (q:=649529181) (s:=25485) (rank:=33770212) (tiny:=1968) (pairs:=801224)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 649529181 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row17093 :
    FinalSeventhSieve.rough 11092009835083 17093+34535120=FinalSeventhSieve.rough 11092009835083 17077 :=
  LargeQuotientSieve.row (p:=17093) (q:=648921186) (s:=25473) (rank:=33740199) (tiny:=1969) (pairs:=796889)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 648921186 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17093 : FinalSeventhSieve.rough 11092009835083 17093+69104589=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine row17077 row17093 rfl

set_option maxRecDepth 16000 in
private theorem row17099 :
    FinalSeventhSieve.rough 11092009835083 17099+34521106=FinalSeventhSieve.rough 11092009835083 17093 :=
  LargeQuotientSieve.row (p:=17099) (q:=648693481) (s:=25469) (rank:=33729113) (tiny:=1970) (pairs:=793962)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 648693481 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17099 : FinalSeventhSieve.rough 11092009835083 17099+103625695=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17093 row17099 rfl

set_option maxRecDepth 16000 in
private theorem row17107 :
    FinalSeventhSieve.rough 11092009835083 17107+34502868=FinalSeventhSieve.rough 11092009835083 17099 :=
  LargeQuotientSieve.row (p:=17107) (q:=648390123) (s:=25463) (rank:=33714082) (tiny:=1971) (pairs:=790756)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 648390123 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17107 : FinalSeventhSieve.rough 11092009835083 17107+138128563=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17099 row17107 rfl

set_option maxRecDepth 16000 in
private theorem row17117 :
    FinalSeventhSieve.rough 11092009835083 17117+34480720=FinalSeventhSieve.rough 11092009835083 17107 :=
  LargeQuotientSieve.row (p:=17117) (q:=648011324) (s:=25456) (rank:=33695414) (tiny:=1972) (pairs:=787277)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 648011324 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17117 : FinalSeventhSieve.rough 11092009835083 17117+172609283=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17107 row17117 rfl

set_option maxRecDepth 16000 in
private theorem row17123 :
    FinalSeventhSieve.rough 11092009835083 17123+34466639=FinalSeventhSieve.rough 11092009835083 17117 :=
  LargeQuotientSieve.row (p:=17123) (q:=647784257) (s:=25451) (rank:=33684229) (tiny:=1973) (pairs:=784382)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 647784257 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17123 : FinalSeventhSieve.rough 11092009835083 17123+207075922=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17117 row17123 rfl

set_option maxRecDepth 16000 in
private theorem row17137 :
    FinalSeventhSieve.rough 11092009835083 17137+34436430=FinalSeventhSieve.rough 11092009835083 17123 :=
  LargeQuotientSieve.row (p:=17137) (q:=647255052) (s:=25441) (rank:=33658099) (tiny:=1974) (pairs:=780304)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 647255052 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17137 : FinalSeventhSieve.rough 11092009835083 17137+241512352=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17123 row17137 rfl

set_option maxRecDepth 16000 in
private theorem row17159 :
    FinalSeventhSieve.rough 11092009835083 17159+34390300=FinalSeventhSieve.rough 11092009835083 17137 :=
  LargeQuotientSieve.row (p:=17159) (q:=646425189) (s:=25424) (rank:=33617194) (tiny:=1975) (pairs:=775080)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 646425189 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17159 : FinalSeventhSieve.rough 11092009835083 17159+275902652=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17137 row17159 rfl

set_option maxRecDepth 16000 in
private theorem row17167 :
    FinalSeventhSieve.rough 11092009835083 17167+34372359=FinalSeventhSieve.rough 11092009835083 17159 :=
  LargeQuotientSieve.row (p:=17167) (q:=646123949) (s:=25418) (rank:=33602384) (tiny:=1976) (pairs:=771950)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 646123949 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17167 : FinalSeventhSieve.rough 11092009835083 17167+310275011=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17159 row17167 rfl

set_option maxRecDepth 16000 in
private theorem row17183 :
    FinalSeventhSieve.rough 11092009835083 17183+34338289=FinalSeventhSieve.rough 11092009835083 17167 :=
  LargeQuotientSieve.row (p:=17183) (q:=645522308) (s:=25407) (rank:=33572632) (tiny:=1977) (pairs:=767633)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 645522308 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17183 : FinalSeventhSieve.rough 11092009835083 17183+344613300=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17167 row17183 rfl

set_option maxRecDepth 16000 in
private theorem row17189 :
    FinalSeventhSieve.rough 11092009835083 17189+34324180=FinalSeventhSieve.rough 11092009835083 17183 :=
  LargeQuotientSieve.row (p:=17189) (q:=645296982) (s:=25402) (rank:=33561388) (tiny:=1978) (pairs:=764769)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 645296982 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17189 : FinalSeventhSieve.rough 11092009835083 17189+378937480=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17183 row17189 rfl

set_option maxRecDepth 16000 in
private theorem row17191 :
    FinalSeventhSieve.rough 11092009835083 17191+34318196=FinalSeventhSieve.rough 11092009835083 17189 :=
  LargeQuotientSieve.row (p:=17191) (q:=645221908) (s:=25401) (rank:=33557672) (tiny:=1979) (pairs:=762502)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ625000000To650000000.count_correct 645221908 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to17191 : FinalSeventhSieve.rough 11092009835083 17191+413255676=FinalSeventhSieve.rough 11092009835083 17053 :=
  LargeQuotientSieve.combine to17189 row17191 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 17191+413255676=FinalSeventhSieve.rough 11092009835083 17053 := to17191

end Tail11092009835083From17053To17191
