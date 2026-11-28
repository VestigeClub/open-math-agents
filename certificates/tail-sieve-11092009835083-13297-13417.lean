import certificates.«large-quotient-sieve-steps»
import certificates.«prime-table-825000000-850000000»

/-! Exact changes for sieve primes 1580 through 1591. -/
open Finset
namespace Tail11092009835083From13297To13417

set_option maxRecDepth 16000 in
private theorem row13309 :
    FinalSeventhSieve.rough 11092009835083 13309+45882215=FinalSeventhSieve.rough 11092009835083 13297 :=
  LargeQuotientSieve.row (p:=13309) (q:=833421732) (s:=28869) (rank:=42774982) (tiny:=1579) (pairs:=3108811)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 833421732 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

set_option maxRecDepth 16000 in
private theorem row13313 :
    FinalSeventhSieve.rough 11092009835083 13313+45863512=FinalSeventhSieve.rough 11092009835083 13309 :=
  LargeQuotientSieve.row (p:=13313) (q:=833171323) (s:=28864) (rank:=42762854) (tiny:=1580) (pairs:=3102237)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 833171323 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13313 : FinalSeventhSieve.rough 11092009835083 13313+91745727=FinalSeventhSieve.rough 11092009835083 13297 :=
  LargeQuotientSieve.combine row13309 row13313 rfl

set_option maxRecDepth 16000 in
private theorem row13327 :
    FinalSeventhSieve.rough 11092009835083 13327+45809802=FinalSeventhSieve.rough 11092009835083 13313 :=
  LargeQuotientSieve.row (p:=13327) (q:=832296078) (s:=28849) (rank:=42720194) (tiny:=1581) (pairs:=3091188)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 832296078 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13327 : FinalSeventhSieve.rough 11092009835083 13327+137555529=FinalSeventhSieve.rough 11092009835083 13297 :=
  LargeQuotientSieve.combine to13313 row13327 rfl

set_option maxRecDepth 16000 in
private theorem row13331 :
    FinalSeventhSieve.rough 11092009835083 13331+45791151=FinalSeventhSieve.rough 11092009835083 13327 :=
  LargeQuotientSieve.row (p:=13331) (q:=832046345) (s:=28845) (rank:=42708040) (tiny:=1582) (pairs:=3084692)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 832046345 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13331 : FinalSeventhSieve.rough 11092009835083 13331+183346680=FinalSeventhSieve.rough 11092009835083 13297 :=
  LargeQuotientSieve.combine to13327 row13331 rfl

set_option maxRecDepth 16000 in
private theorem row13337 :
    FinalSeventhSieve.rough 11092009835083 13337+45765471=FinalSeventhSieve.rough 11092009835083 13331 :=
  LargeQuotientSieve.row (p:=13337) (q:=831672027) (s:=28838) (rank:=42689805) (tiny:=1583) (pairs:=3077248)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 831672027 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13337 : FinalSeventhSieve.rough 11092009835083 13337+229112151=FinalSeventhSieve.rough 11092009835083 13297 :=
  LargeQuotientSieve.combine to13331 row13337 rfl

set_option maxRecDepth 16000 in
private theorem row13339 :
    FinalSeventhSieve.rough 11092009835083 13339+45753798=FinalSeventhSieve.rough 11092009835083 13337 :=
  LargeQuotientSieve.row (p:=13339) (q:=831547330) (s:=28836) (rank:=42683734) (tiny:=1584) (pairs:=3071647)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 831547330 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13339 : FinalSeventhSieve.rough 11092009835083 13339+274865949=FinalSeventhSieve.rough 11092009835083 13297 :=
  LargeQuotientSieve.combine to13337 row13339 rfl

set_option maxRecDepth 16000 in
private theorem row13367 :
    FinalSeventhSieve.rough 11092009835083 13367+45651735=FinalSeventhSieve.rough 11092009835083 13339 :=
  LargeQuotientSieve.row (p:=13367) (q:=829805478) (s:=28806) (rank:=42598921) (tiny:=1585) (pairs:=3054398)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 829805478 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13367 : FinalSeventhSieve.rough 11092009835083 13367+320517684=FinalSeventhSieve.rough 11092009835083 13297 :=
  LargeQuotientSieve.combine to13339 row13367 rfl

set_option maxRecDepth 16000 in
private theorem row13381 :
    FinalSeventhSieve.rough 11092009835083 13381+45598442=FinalSeventhSieve.rough 11092009835083 13367 :=
  LargeQuotientSieve.row (p:=13381) (q:=828937286) (s:=28791) (rank:=42556627) (tiny:=1586) (pairs:=3043400)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 828937286 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13381 : FinalSeventhSieve.rough 11092009835083 13381+366116126=FinalSeventhSieve.rough 11092009835083 13297 :=
  LargeQuotientSieve.combine to13367 row13381 rfl

set_option maxRecDepth 16000 in
private theorem row13397 :
    FinalSeventhSieve.rough 11092009835083 13397+45538454=FinalSeventhSieve.rough 11092009835083 13381 :=
  LargeQuotientSieve.row (p:=13397) (q:=827947289) (s:=28774) (rank:=42508379) (tiny:=1587) (pairs:=3031661)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 827947289 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13397 : FinalSeventhSieve.rough 11092009835083 13397+411654580=FinalSeventhSieve.rough 11092009835083 13297 :=
  LargeQuotientSieve.combine to13381 row13397 rfl

set_option maxRecDepth 16000 in
private theorem row13399 :
    FinalSeventhSieve.rough 11092009835083 13399+45526993=FinalSeventhSieve.rough 11092009835083 13397 :=
  LargeQuotientSieve.row (p:=13399) (q:=827823705) (s:=28771) (rank:=42502440) (tiny:=1588) (pairs:=3026140)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 827823705 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13399 : FinalSeventhSieve.rough 11092009835083 13399+457181573=FinalSeventhSieve.rough 11092009835083 13297 :=
  LargeQuotientSieve.combine to13397 row13399 rfl

set_option maxRecDepth 16000 in
private theorem row13411 :
    FinalSeventhSieve.rough 11092009835083 13411+45480927=FinalSeventhSieve.rough 11092009835083 13399 :=
  LargeQuotientSieve.row (p:=13411) (q:=827082979) (s:=28759) (rank:=42466403) (tiny:=1589) (pairs:=3016112)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 827082979 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13411 : FinalSeventhSieve.rough 11092009835083 13411+502662500=FinalSeventhSieve.rough 11092009835083 13297 :=
  LargeQuotientSieve.combine to13399 row13411 rfl

set_option maxRecDepth 16000 in
private theorem row13417 :
    FinalSeventhSieve.rough 11092009835083 13417+45455649=FinalSeventhSieve.rough 11092009835083 13411 :=
  LargeQuotientSieve.row (p:=13417) (q:=826713112) (s:=28752) (rank:=42448402) (tiny:=1590) (pairs:=3008836)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((QuotientQ825000000To850000000.count_correct 826713112 (by decide) (by decide)).symm.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel) rfl

private theorem to13417 : FinalSeventhSieve.rough 11092009835083 13417+548118149=FinalSeventhSieve.rough 11092009835083 13297 :=
  LargeQuotientSieve.combine to13411 row13417 rfl

theorem change : FinalSeventhSieve.rough 11092009835083 13417+548118149=FinalSeventhSieve.rough 11092009835083 13297 := to13417

end Tail11092009835083From13297To13417
