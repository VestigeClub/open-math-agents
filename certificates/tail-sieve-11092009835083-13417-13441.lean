import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-825000000-850000000»

/-! Exact changes for sieve primes 1592 through 1593. -/
open Finset
namespace Tail11092009835083From13417To13441

set_option maxRecDepth 16000 in
private theorem row13421 :
    FinalSeventhSieve.rough 11092009835083 13421+45437251=FinalSeventhSieve.rough 11092009835083 13417 :=
  LargeQuotientSieve.row (p:=13421) (q:=826466718) (s:=28748) (rank:=42436390) (tiny:=1591) (pairs:=3002451)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 826466718 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row13441 :
    FinalSeventhSieve.rough 11092009835083 13441+45363895=FinalSeventhSieve.rough 11092009835083 13421 :=
  LargeQuotientSieve.row (p:=13441) (q:=825236949) (s:=28726) (rank:=42376451) (tiny:=1592) (pairs:=2989035)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 825236949 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13441 : FinalSeventhSieve.rough 11092009835083 13441+90801146=FinalSeventhSieve.rough 11092009835083 13417 :=
  LargeQuotientSieve.combine row13421 row13441 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13441+90801146=FinalSeventhSieve.rough 11092009835083 13417 := to13441

end Tail11092009835083From13417To13441
