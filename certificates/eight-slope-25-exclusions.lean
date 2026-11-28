import certificates.«relative-prime-counts-82»
import certificates.«prime-count-204778727327»

/-!
# The eight slope-25 candidates in the second reduction of OEIS A247824

Each index fails the prime-count equation. The right endpoint of every local
count is evaluated from the verified count at 204,778,727,327.
-/
namespace Slope25Candidates

private theorem exclude_at {m q delta : ℕ}
    (endpoint : 25*(m+1322164)-20868473=q)
    (local_count : Nat.primeCounting q=Nat.primeCounting 204778727327+delta)
    (different : 8190661670+delta≠m) :
    Nat.primeCounting (25*(m+1322164)-20868473)≠m := by
  rw [endpoint,local_count,ExactSieve204778727327At5894.prime_count]
  exact different

private theorem c0 : Nat.primeCounting (25*(8190661668+1322164)-20868473)≠8190661668 :=
  exclude_at (q:=204778727327) (delta:=0) rfl WindowRanks.a204778727327 (by decide)

private theorem c1 : Nat.primeCounting (25*(8190661680+1322164)-20868473)≠8190661680 :=
  exclude_at (q:=204778727627) (delta:=12) rfl WindowRanks.a204778727627 (by decide)

private theorem c2 : Nat.primeCounting (25*(8190661682+1322164)-20868473)≠8190661682 :=
  exclude_at (q:=204778727677) (delta:=15) rfl WindowRanks.a204778727677 (by decide)

private theorem c3 : Nat.primeCounting (25*(8190661694+1322164)-20868473)≠8190661694 :=
  exclude_at (q:=204778727977) (delta:=28) rfl WindowRanks.a204778727977 (by decide)

private theorem c4 : Nat.primeCounting (25*(8190661700+1322164)-20868473)≠8190661700 :=
  exclude_at (q:=204778728127) (delta:=34) rfl WindowRanks.a204778728127 (by decide)

private theorem c5 : Nat.primeCounting (25*(8190661718+1322164)-20868473)≠8190661718 :=
  exclude_at (q:=204778728577) (delta:=51) rfl WindowRanks.a204778728577 (by decide)

private theorem c6 : Nat.primeCounting (25*(8190661722+1322164)-20868473)≠8190661722 :=
  exclude_at (q:=204778728677) (delta:=56) rfl WindowRanks.a204778728677 (by decide)

private theorem c7 : Nat.primeCounting (25*(8190661752+1322164)-20868473)≠8190661752 :=
  exclude_at (q:=204778729427) (delta:=83) rfl WindowRanks.a204778729427 (by decide)

theorem excluded : ∀ m ∈ ([8190661668,8190661680,8190661682,8190661694,8190661700,8190661718,8190661722,8190661752] : List ℕ),
    Nat.primeCounting (25*(m+1322164)-20868473)≠m := by
  intro m hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hnil
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · exact c6
  · exact c7
  · cases hnil

end Slope25Candidates
