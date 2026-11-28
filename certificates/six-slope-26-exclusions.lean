import certificates.«relative-prime-counts-82»
import certificates.«prime-count-555157672301»

/-!
# The six slope-26 candidates in the second reduction of OEIS A247824

Each index fails the prime-count equation. The right endpoint of every local
count is evaluated from the verified count at 555,157,672,301.
-/
namespace Slope26Candidates

private theorem exclude_at {m q delta : ℕ}
    (endpoint : 26*(m+1322164)-20868473=q)
    (local_count : Nat.primeCounting q=Nat.primeCounting 555157672301+delta)
    (different : 21351698638+delta≠m) :
    Nat.primeCounting (26*(m+1322164)-20868473)≠m := by
  rw [endpoint,local_count,ExactSieve555157672301At8218.prime_count]
  exact different

private theorem c0 : Nat.primeCounting (26*(21351698635+1322164)-20868473)≠21351698635 :=
  exclude_at (q:=555157672301) (delta:=0) rfl WindowRanks.a555157672301 (by decide)

private theorem c1 : Nat.primeCounting (26*(21351698651+1322164)-20868473)≠21351698651 :=
  exclude_at (q:=555157672717) (delta:=18) rfl WindowRanks.a555157672717 (by decide)

private theorem c2 : Nat.primeCounting (26*(21351698662+1322164)-20868473)≠21351698662 :=
  exclude_at (q:=555157673003) (delta:=26) rfl WindowRanks.a555157673003 (by decide)

private theorem c3 : Nat.primeCounting (26*(21351698668+1322164)-20868473)≠21351698668 :=
  exclude_at (q:=555157673159) (delta:=34) rfl WindowRanks.a555157673159 (by decide)

private theorem c4 : Nat.primeCounting (26*(21351698671+1322164)-20868473)≠21351698671 :=
  exclude_at (q:=555157673237) (delta:=36) rfl WindowRanks.a555157673237 (by decide)

private theorem c5 : Nat.primeCounting (26*(21351698672+1322164)-20868473)≠21351698672 :=
  exclude_at (q:=555157673263) (delta:=37) rfl WindowRanks.a555157673263 (by decide)

theorem excluded : ∀ m ∈ ([21351698635,21351698651,21351698662,21351698668,21351698671,21351698672] : List ℕ),
    Nat.primeCounting (26*(m+1322164)-20868473)≠m := by
  intro m hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | hnil
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · cases hnil

end Slope26Candidates
