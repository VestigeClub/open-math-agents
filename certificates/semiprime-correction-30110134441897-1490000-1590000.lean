import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 1,490,000 through 1,590,000

The sum covers 6,993 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From1490000To1590000

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 30110134441897 1490000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 1490001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 1490000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r1490001 : blockSum term 1490001 390 38588557 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1490391 : blockSum term 1490391 391 30394015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1490782 : blockSum term 1490782 390 29217413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1491172 : blockSum term 1491172 391 28040538 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1491563 : blockSum term 1491563 390 36209303 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1491953 : blockSum term 1491953 391 40868752 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1492344 : blockSum term 1492344 391 28015422 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1492735 : blockSum term 1492735 391 28007829 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1493126 : blockSum term 1493126 390 37331261 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1493516 : blockSum term 1493516 391 38487208 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1493907 : blockSum term 1493907 390 30314089 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1494297 : blockSum term 1494297 391 37298546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1494688 : blockSum term 1494688 390 30296192 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1495078 : blockSum term 1495078 391 30287262 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1495469 : blockSum term 1495469 391 30278895 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1495860 : blockSum term 1495860 391 31434472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1496251 : blockSum term 1496251 390 36080960 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1496641 : blockSum term 1496641 391 27926173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1497032 : blockSum term 1497032 390 36060543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1497422 : blockSum term 1497422 391 29071865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1497813 : blockSum term 1497813 390 24414038 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1498203 : blockSum term 1498203 391 34866512 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1498594 : blockSum term 1498594 391 26723355 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1498985 : blockSum term 1498985 391 32522946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1499376 : blockSum term 1499376 390 26708137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1499766 : blockSum term 1499766 391 30181944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1500157 : blockSum term 1500157 390 35975743 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1500547 : blockSum term 1500547 391 39445120 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1500938 : blockSum term 1500938 390 22037111 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1501328 : blockSum term 1501328 391 35945042 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1501719 : blockSum term 1501719 391 35934017 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1502110 : blockSum term 1502110 391 26653685 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1502501 : blockSum term 1502501 390 30120921 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1502891 : blockSum term 1502891 391 35903257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1503282 : blockSum term 1503282 390 33576623 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1503672 : blockSum term 1503672 391 32409218 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1504063 : blockSum term 1504063 390 27771318 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1504453 : blockSum term 1504453 391 43957891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1504844 : blockSum term 1504844 391 39318896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1505235 : blockSum term 1505235 391 32371198 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1505626 : blockSum term 1505626 390 32361893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1506016 : blockSum term 1506016 391 30041424 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1506407 : blockSum term 1506407 390 36963130 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1506797 : blockSum term 1506797 391 36951876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1507188 : blockSum term 1507188 390 21933361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1507578 : blockSum term 1507578 391 28852710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1507969 : blockSum term 1507969 391 29997994 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1508360 : blockSum term 1508360 391 36909423 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1508751 : blockSum term 1508751 390 38051659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1509141 : blockSum term 1509141 391 27665531 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1509532 : blockSum term 1509532 390 27657799 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1509922 : blockSum term 1509922 391 35714519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1510313 : blockSum term 1510313 390 38007497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1510703 : blockSum term 1510703 391 31088116 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1511094 : blockSum term 1511094 391 32229858 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1511485 : blockSum term 1511485 391 28767789 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1511876 : blockSum term 1511876 390 33360996 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1512266 : blockSum term 1512266 391 29901337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1512657 : blockSum term 1512657 390 28742519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1513047 : blockSum term 1513047 391 36780192 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1513438 : blockSum term 1513438 390 36770238 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1513828 : blockSum term 1513828 391 29866794 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1514219 : blockSum term 1514219 391 32153876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1514610 : blockSum term 1514610 391 29849469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1515001 : blockSum term 1515001 390 22954229 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1515391 : blockSum term 1515391 391 28684378 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1515782 : blockSum term 1515782 390 34412012 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1516172 : blockSum term 1516172 391 30962244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1516563 : blockSum term 1516563 390 33246103 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1516953 : blockSum term 1516953 391 30943430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1517344 : blockSum term 1517344 391 35516760 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1517735 : blockSum term 1517735 391 30925338 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1518126 : blockSum term 1518126 390 27481707 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1518516 : blockSum term 1518516 391 33197781 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1518907 : blockSum term 1518907 390 29753977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1519297 : blockSum term 1519297 391 29745790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1519688 : blockSum term 1519688 390 28594565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1520078 : blockSum term 1520078 391 29729117 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1520469 : blockSum term 1520469 391 34293383 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1520860 : blockSum term 1520860 391 29711293 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1521251 : blockSum term 1521251 390 27417732 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1521641 : blockSum term 1521641 391 30836121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1522032 : blockSum term 1522032 390 26260322 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1522422 : blockSum term 1522422 391 31960089 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1522813 : blockSum term 1522813 390 26244722 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1523203 : blockSum term 1523203 391 37644802 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1523594 : blockSum term 1523594 391 30791662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1523985 : blockSum term 1523985 391 35343333 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1524376 : blockSum term 1524376 390 34193376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1524766 : blockSum term 1524766 391 31904136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1525157 : blockSum term 1525157 390 29616892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1525547 : blockSum term 1525547 391 30746633 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1525938 : blockSum term 1525938 390 29599607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1526328 : blockSum term 1526328 391 30729495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1526719 : blockSum term 1526719 391 23893248 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1527110 : blockSum term 1527110 391 26162783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1527501 : blockSum term 1527501 390 35252147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1527891 : blockSum term 1527891 391 34104793 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1528282 : blockSum term 1528282 390 29548136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1528672 : blockSum term 1528672 391 28403572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1529063 : blockSum term 1529063 390 34074262 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1529453 : blockSum term 1529453 391 28387526 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1529844 : blockSum term 1529844 391 36325378 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1530235 : blockSum term 1530235 391 24965858 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1530626 : blockSum term 1530626 390 29497887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1531016 : blockSum term 1531016 391 28354814 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1531407 : blockSum term 1531407 390 26078737 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1531797 : blockSum term 1531797 391 31738997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1532188 : blockSum term 1532188 390 20398377 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1532578 : blockSum term 1532578 391 33987866 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1532969 : blockSum term 1532969 391 26049572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1533360 : blockSum term 1533360 391 35100844 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1533751 : blockSum term 1533751 390 32826329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1534141 : blockSum term 1534141 391 28290817 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1534532 : blockSum term 1534532 390 27150662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1534922 : blockSum term 1534922 391 30535865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1535313 : blockSum term 1535313 390 35050129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1535703 : blockSum term 1535703 391 37300166 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1536094 : blockSum term 1536094 391 25989980 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1536485 : blockSum term 1536485 391 35019611 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1536876 : blockSum term 1536876 390 31620647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1537266 : blockSum term 1537266 391 28224987 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1537657 : blockSum term 1537657 390 34988664 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1538047 : blockSum term 1538047 391 32722972 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1538438 : blockSum term 1538438 390 30457982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1538828 : blockSum term 1538828 391 27065627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1539219 : blockSum term 1539219 391 27058035 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1539610 : blockSum term 1539610 391 34940095 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1540001 : blockSum term 1540001 390 31550431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1540391 : blockSum term 1540391 391 29288009 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1540782 : blockSum term 1540782 390 33785606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1541172 : blockSum term 1541172 391 29271638 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1541563 : blockSum term 1541563 390 32639626 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1541953 : blockSum term 1541953 391 28130543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1542344 : blockSum term 1542344 391 31497099 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1542735 : blockSum term 1542735 391 28113071 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1543126 : blockSum term 1543126 390 28105773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1543516 : blockSum term 1543516 391 23602347 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1543907 : blockSum term 1543907 390 30337635 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1544297 : blockSum term 1544297 391 30328484 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1544688 : blockSum term 1544688 390 25827451 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1545078 : blockSum term 1545078 391 34802621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1545469 : blockSum term 1545469 391 34792951 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1545860 : blockSum term 1545860 391 31415749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1546251 : blockSum term 1546251 390 29164718 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1546641 : blockSum term 1546641 391 32519902 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1547032 : blockSum term 1547032 390 25784874 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1547422 : blockSum term 1547422 391 36985247 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1547813 : blockSum term 1547813 390 35853651 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1548203 : blockSum term 1548203 391 30242653 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1548594 : blockSum term 1548594 391 32473127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1548985 : blockSum term 1548985 391 26866946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1549376 : blockSum term 1549376 390 32455209 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1549766 : blockSum term 1549766 391 29088988 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1550157 : blockSum term 1550157 390 36910635 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1550547 : blockSum term 1550547 391 26836283 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1550938 : blockSum term 1550938 390 29064724 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1551328 : blockSum term 1551328 391 25702203 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1551719 : blockSum term 1551719 391 30164642 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1552110 : blockSum term 1552110 391 27922411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1552501 : blockSum term 1552501 390 34614723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1552891 : blockSum term 1552891 391 31255465 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1553282 : blockSum term 1553282 390 34594206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1553672 : blockSum term 1553672 391 26774662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1554063 : blockSum term 1554063 390 32342692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1554453 : blockSum term 1554453 391 24528867 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1554844 : blockSum term 1554844 391 34553426 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1555235 : blockSum term 1555235 391 28972744 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1555626 : blockSum term 1555626 390 41218396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1556016 : blockSum term 1556016 391 26727716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1556407 : blockSum term 1556407 390 35627482 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1556797 : blockSum term 1556797 391 31164799 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1557188 : blockSum term 1557188 390 31156540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1557578 : blockSum term 1557578 391 25586113 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1557969 : blockSum term 1557969 391 32249983 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1558360 : blockSum term 1558360 391 28905690 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1558751 : blockSum term 1558751 390 35567599 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1559141 : blockSum term 1559141 391 35556118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1559532 : blockSum term 1559532 390 29992089 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1559922 : blockSum term 1559922 391 33314354 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1560313 : blockSum term 1560313 390 23313396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1560703 : blockSum term 1560703 391 28856583 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1561094 : blockSum term 1561094 391 29958218 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1561485 : blockSum term 1561485 391 29950036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1561876 : blockSum term 1561876 390 23287047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1562266 : blockSum term 1562266 391 28824413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1562657 : blockSum term 1562657 390 18840870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1563047 : blockSum term 1563047 391 40996422 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1563438 : blockSum term 1563438 390 29907768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1563828 : blockSum term 1563828 391 29898857 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1564219 : blockSum term 1564219 391 32104029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1564610 : blockSum term 1564610 391 27667659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1565001 : blockSum term 1565001 390 37618419 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1565391 : blockSum term 1565391 391 27652538 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1565782 : blockSum term 1565782 390 33174160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1566172 : blockSum term 1566172 391 29848290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1566563 : blockSum term 1566563 390 30944306 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1566953 : blockSum term 1566953 391 35355117 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1567344 : blockSum term 1567344 391 28717974 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1567735 : blockSum term 1567735 391 19876502 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1568126 : blockSum term 1568126 390 30910884 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1568516 : blockSum term 1568516 391 19865857 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1568907 : blockSum term 1568907 390 35306443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1569297 : blockSum term 1569297 391 31987479 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1569688 : blockSum term 1569688 390 26464185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1570078 : blockSum term 1570078 391 31969059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1570469 : blockSum term 1570469 391 28653739 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1570860 : blockSum term 1570860 391 36358737 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1571251 : blockSum term 1571251 390 24231940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1571641 : blockSum term 1571641 391 37439006 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1572032 : blockSum term 1572032 390 34124812 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1572422 : blockSum term 1572422 391 30814091 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1572813 : blockSum term 1572813 390 29704885 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1573203 : blockSum term 1573203 391 24197476 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1573594 : blockSum term 1573594 391 35185803 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1573985 : blockSum term 1573985 391 31878673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1574376 : blockSum term 1574376 390 27473999 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1574766 : blockSum term 1574766 391 27465287 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1575157 : blockSum term 1575157 390 30752774 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1575547 : blockSum term 1575547 391 29647022 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1575938 : blockSum term 1575938 390 27443133 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1576328 : blockSum term 1576328 391 30727495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1576719 : blockSum term 1576719 391 29622569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1577110 : blockSum term 1577110 391 30710994 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1577501 : blockSum term 1577501 390 31799094 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1577891 : blockSum term 1577891 391 28501077 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1578282 : blockSum term 1578282 390 20821913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1578672 : blockSum term 1578672 391 35057529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1579063 : blockSum term 1579063 390 27381067 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1579453 : blockSum term 1579453 391 29563895 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1579844 : blockSum term 1579844 391 29556099 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1580235 : blockSum term 1580235 391 30641647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1580626 : blockSum term 1580626 390 32821715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1581016 : blockSum term 1581016 391 26249977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1581407 : blockSum term 1581407 390 33896309 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1581797 : blockSum term 1581797 391 26233972 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1582188 : blockSum term 1582188 390 26226376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1582578 : blockSum term 1582578 391 26219476 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1582969 : blockSum term 1582969 391 36042001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1583360 : blockSum term 1583360 391 21837320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1583751 : blockSum term 1583751 390 36022437 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1584141 : blockSum term 1584141 391 29464164 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1584532 : blockSum term 1584532 390 27274653 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1584922 : blockSum term 1584922 391 28358225 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1585313 : blockSum term 1585313 390 38162351 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1585703 : blockSum term 1585703 391 21800694 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1586094 : blockSum term 1586094 391 23974346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1586485 : blockSum term 1586485 391 31593438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1586876 : blockSum term 1586876 390 21783233 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1587266 : blockSum term 1587266 391 29398282 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1587657 : blockSum term 1587657 390 31567489 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1588047 : blockSum term 1588047 391 31559503 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1588438 : blockSum term 1588438 390 30461706 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1588828 : blockSum term 1588828 391 29366730 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1589219 : blockSum term 1589219 391 34794395 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1589610 : blockSum term 1589610 391 33697378 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 1490001 100000 7884761009 := (join_sums term (lo:=1490001) (a:=50000) (b:=50000) (join_sums term (lo:=1490001) (a:=25000) (b:=25000) (join_sums term (lo:=1490001) (a:=12500) (b:=12500) (join_sums term (lo:=1490001) (a:=6250) (b:=6250) (join_sums term (lo:=1490001) (a:=3125) (b:=3125) (join_sums term (lo:=1490001) (a:=1562) (b:=1563) (join_sums term (lo:=1490001) (a:=781) (b:=781) (join_sums term (lo:=1490001) (a:=390) (b:=391) r1490001 r1490391) (join_sums term (lo:=1490782) (a:=390) (b:=391) r1490782 r1491172)) (join_sums term (lo:=1491563) (a:=781) (b:=782) (join_sums term (lo:=1491563) (a:=390) (b:=391) r1491563 r1491953) (join_sums term (lo:=1492344) (a:=391) (b:=391) r1492344 r1492735))) (join_sums term (lo:=1493126) (a:=1562) (b:=1563) (join_sums term (lo:=1493126) (a:=781) (b:=781) (join_sums term (lo:=1493126) (a:=390) (b:=391) r1493126 r1493516) (join_sums term (lo:=1493907) (a:=390) (b:=391) r1493907 r1494297)) (join_sums term (lo:=1494688) (a:=781) (b:=782) (join_sums term (lo:=1494688) (a:=390) (b:=391) r1494688 r1495078) (join_sums term (lo:=1495469) (a:=391) (b:=391) r1495469 r1495860)))) (join_sums term (lo:=1496251) (a:=3125) (b:=3125) (join_sums term (lo:=1496251) (a:=1562) (b:=1563) (join_sums term (lo:=1496251) (a:=781) (b:=781) (join_sums term (lo:=1496251) (a:=390) (b:=391) r1496251 r1496641) (join_sums term (lo:=1497032) (a:=390) (b:=391) r1497032 r1497422)) (join_sums term (lo:=1497813) (a:=781) (b:=782) (join_sums term (lo:=1497813) (a:=390) (b:=391) r1497813 r1498203) (join_sums term (lo:=1498594) (a:=391) (b:=391) r1498594 r1498985))) (join_sums term (lo:=1499376) (a:=1562) (b:=1563) (join_sums term (lo:=1499376) (a:=781) (b:=781) (join_sums term (lo:=1499376) (a:=390) (b:=391) r1499376 r1499766) (join_sums term (lo:=1500157) (a:=390) (b:=391) r1500157 r1500547)) (join_sums term (lo:=1500938) (a:=781) (b:=782) (join_sums term (lo:=1500938) (a:=390) (b:=391) r1500938 r1501328) (join_sums term (lo:=1501719) (a:=391) (b:=391) r1501719 r1502110))))) (join_sums term (lo:=1502501) (a:=6250) (b:=6250) (join_sums term (lo:=1502501) (a:=3125) (b:=3125) (join_sums term (lo:=1502501) (a:=1562) (b:=1563) (join_sums term (lo:=1502501) (a:=781) (b:=781) (join_sums term (lo:=1502501) (a:=390) (b:=391) r1502501 r1502891) (join_sums term (lo:=1503282) (a:=390) (b:=391) r1503282 r1503672)) (join_sums term (lo:=1504063) (a:=781) (b:=782) (join_sums term (lo:=1504063) (a:=390) (b:=391) r1504063 r1504453) (join_sums term (lo:=1504844) (a:=391) (b:=391) r1504844 r1505235))) (join_sums term (lo:=1505626) (a:=1562) (b:=1563) (join_sums term (lo:=1505626) (a:=781) (b:=781) (join_sums term (lo:=1505626) (a:=390) (b:=391) r1505626 r1506016) (join_sums term (lo:=1506407) (a:=390) (b:=391) r1506407 r1506797)) (join_sums term (lo:=1507188) (a:=781) (b:=782) (join_sums term (lo:=1507188) (a:=390) (b:=391) r1507188 r1507578) (join_sums term (lo:=1507969) (a:=391) (b:=391) r1507969 r1508360)))) (join_sums term (lo:=1508751) (a:=3125) (b:=3125) (join_sums term (lo:=1508751) (a:=1562) (b:=1563) (join_sums term (lo:=1508751) (a:=781) (b:=781) (join_sums term (lo:=1508751) (a:=390) (b:=391) r1508751 r1509141) (join_sums term (lo:=1509532) (a:=390) (b:=391) r1509532 r1509922)) (join_sums term (lo:=1510313) (a:=781) (b:=782) (join_sums term (lo:=1510313) (a:=390) (b:=391) r1510313 r1510703) (join_sums term (lo:=1511094) (a:=391) (b:=391) r1511094 r1511485))) (join_sums term (lo:=1511876) (a:=1562) (b:=1563) (join_sums term (lo:=1511876) (a:=781) (b:=781) (join_sums term (lo:=1511876) (a:=390) (b:=391) r1511876 r1512266) (join_sums term (lo:=1512657) (a:=390) (b:=391) r1512657 r1513047)) (join_sums term (lo:=1513438) (a:=781) (b:=782) (join_sums term (lo:=1513438) (a:=390) (b:=391) r1513438 r1513828) (join_sums term (lo:=1514219) (a:=391) (b:=391) r1514219 r1514610)))))) (join_sums term (lo:=1515001) (a:=12500) (b:=12500) (join_sums term (lo:=1515001) (a:=6250) (b:=6250) (join_sums term (lo:=1515001) (a:=3125) (b:=3125) (join_sums term (lo:=1515001) (a:=1562) (b:=1563) (join_sums term (lo:=1515001) (a:=781) (b:=781) (join_sums term (lo:=1515001) (a:=390) (b:=391) r1515001 r1515391) (join_sums term (lo:=1515782) (a:=390) (b:=391) r1515782 r1516172)) (join_sums term (lo:=1516563) (a:=781) (b:=782) (join_sums term (lo:=1516563) (a:=390) (b:=391) r1516563 r1516953) (join_sums term (lo:=1517344) (a:=391) (b:=391) r1517344 r1517735))) (join_sums term (lo:=1518126) (a:=1562) (b:=1563) (join_sums term (lo:=1518126) (a:=781) (b:=781) (join_sums term (lo:=1518126) (a:=390) (b:=391) r1518126 r1518516) (join_sums term (lo:=1518907) (a:=390) (b:=391) r1518907 r1519297)) (join_sums term (lo:=1519688) (a:=781) (b:=782) (join_sums term (lo:=1519688) (a:=390) (b:=391) r1519688 r1520078) (join_sums term (lo:=1520469) (a:=391) (b:=391) r1520469 r1520860)))) (join_sums term (lo:=1521251) (a:=3125) (b:=3125) (join_sums term (lo:=1521251) (a:=1562) (b:=1563) (join_sums term (lo:=1521251) (a:=781) (b:=781) (join_sums term (lo:=1521251) (a:=390) (b:=391) r1521251 r1521641) (join_sums term (lo:=1522032) (a:=390) (b:=391) r1522032 r1522422)) (join_sums term (lo:=1522813) (a:=781) (b:=782) (join_sums term (lo:=1522813) (a:=390) (b:=391) r1522813 r1523203) (join_sums term (lo:=1523594) (a:=391) (b:=391) r1523594 r1523985))) (join_sums term (lo:=1524376) (a:=1562) (b:=1563) (join_sums term (lo:=1524376) (a:=781) (b:=781) (join_sums term (lo:=1524376) (a:=390) (b:=391) r1524376 r1524766) (join_sums term (lo:=1525157) (a:=390) (b:=391) r1525157 r1525547)) (join_sums term (lo:=1525938) (a:=781) (b:=782) (join_sums term (lo:=1525938) (a:=390) (b:=391) r1525938 r1526328) (join_sums term (lo:=1526719) (a:=391) (b:=391) r1526719 r1527110))))) (join_sums term (lo:=1527501) (a:=6250) (b:=6250) (join_sums term (lo:=1527501) (a:=3125) (b:=3125) (join_sums term (lo:=1527501) (a:=1562) (b:=1563) (join_sums term (lo:=1527501) (a:=781) (b:=781) (join_sums term (lo:=1527501) (a:=390) (b:=391) r1527501 r1527891) (join_sums term (lo:=1528282) (a:=390) (b:=391) r1528282 r1528672)) (join_sums term (lo:=1529063) (a:=781) (b:=782) (join_sums term (lo:=1529063) (a:=390) (b:=391) r1529063 r1529453) (join_sums term (lo:=1529844) (a:=391) (b:=391) r1529844 r1530235))) (join_sums term (lo:=1530626) (a:=1562) (b:=1563) (join_sums term (lo:=1530626) (a:=781) (b:=781) (join_sums term (lo:=1530626) (a:=390) (b:=391) r1530626 r1531016) (join_sums term (lo:=1531407) (a:=390) (b:=391) r1531407 r1531797)) (join_sums term (lo:=1532188) (a:=781) (b:=782) (join_sums term (lo:=1532188) (a:=390) (b:=391) r1532188 r1532578) (join_sums term (lo:=1532969) (a:=391) (b:=391) r1532969 r1533360)))) (join_sums term (lo:=1533751) (a:=3125) (b:=3125) (join_sums term (lo:=1533751) (a:=1562) (b:=1563) (join_sums term (lo:=1533751) (a:=781) (b:=781) (join_sums term (lo:=1533751) (a:=390) (b:=391) r1533751 r1534141) (join_sums term (lo:=1534532) (a:=390) (b:=391) r1534532 r1534922)) (join_sums term (lo:=1535313) (a:=781) (b:=782) (join_sums term (lo:=1535313) (a:=390) (b:=391) r1535313 r1535703) (join_sums term (lo:=1536094) (a:=391) (b:=391) r1536094 r1536485))) (join_sums term (lo:=1536876) (a:=1562) (b:=1563) (join_sums term (lo:=1536876) (a:=781) (b:=781) (join_sums term (lo:=1536876) (a:=390) (b:=391) r1536876 r1537266) (join_sums term (lo:=1537657) (a:=390) (b:=391) r1537657 r1538047)) (join_sums term (lo:=1538438) (a:=781) (b:=782) (join_sums term (lo:=1538438) (a:=390) (b:=391) r1538438 r1538828) (join_sums term (lo:=1539219) (a:=391) (b:=391) r1539219 r1539610))))))) (join_sums term (lo:=1540001) (a:=25000) (b:=25000) (join_sums term (lo:=1540001) (a:=12500) (b:=12500) (join_sums term (lo:=1540001) (a:=6250) (b:=6250) (join_sums term (lo:=1540001) (a:=3125) (b:=3125) (join_sums term (lo:=1540001) (a:=1562) (b:=1563) (join_sums term (lo:=1540001) (a:=781) (b:=781) (join_sums term (lo:=1540001) (a:=390) (b:=391) r1540001 r1540391) (join_sums term (lo:=1540782) (a:=390) (b:=391) r1540782 r1541172)) (join_sums term (lo:=1541563) (a:=781) (b:=782) (join_sums term (lo:=1541563) (a:=390) (b:=391) r1541563 r1541953) (join_sums term (lo:=1542344) (a:=391) (b:=391) r1542344 r1542735))) (join_sums term (lo:=1543126) (a:=1562) (b:=1563) (join_sums term (lo:=1543126) (a:=781) (b:=781) (join_sums term (lo:=1543126) (a:=390) (b:=391) r1543126 r1543516) (join_sums term (lo:=1543907) (a:=390) (b:=391) r1543907 r1544297)) (join_sums term (lo:=1544688) (a:=781) (b:=782) (join_sums term (lo:=1544688) (a:=390) (b:=391) r1544688 r1545078) (join_sums term (lo:=1545469) (a:=391) (b:=391) r1545469 r1545860)))) (join_sums term (lo:=1546251) (a:=3125) (b:=3125) (join_sums term (lo:=1546251) (a:=1562) (b:=1563) (join_sums term (lo:=1546251) (a:=781) (b:=781) (join_sums term (lo:=1546251) (a:=390) (b:=391) r1546251 r1546641) (join_sums term (lo:=1547032) (a:=390) (b:=391) r1547032 r1547422)) (join_sums term (lo:=1547813) (a:=781) (b:=782) (join_sums term (lo:=1547813) (a:=390) (b:=391) r1547813 r1548203) (join_sums term (lo:=1548594) (a:=391) (b:=391) r1548594 r1548985))) (join_sums term (lo:=1549376) (a:=1562) (b:=1563) (join_sums term (lo:=1549376) (a:=781) (b:=781) (join_sums term (lo:=1549376) (a:=390) (b:=391) r1549376 r1549766) (join_sums term (lo:=1550157) (a:=390) (b:=391) r1550157 r1550547)) (join_sums term (lo:=1550938) (a:=781) (b:=782) (join_sums term (lo:=1550938) (a:=390) (b:=391) r1550938 r1551328) (join_sums term (lo:=1551719) (a:=391) (b:=391) r1551719 r1552110))))) (join_sums term (lo:=1552501) (a:=6250) (b:=6250) (join_sums term (lo:=1552501) (a:=3125) (b:=3125) (join_sums term (lo:=1552501) (a:=1562) (b:=1563) (join_sums term (lo:=1552501) (a:=781) (b:=781) (join_sums term (lo:=1552501) (a:=390) (b:=391) r1552501 r1552891) (join_sums term (lo:=1553282) (a:=390) (b:=391) r1553282 r1553672)) (join_sums term (lo:=1554063) (a:=781) (b:=782) (join_sums term (lo:=1554063) (a:=390) (b:=391) r1554063 r1554453) (join_sums term (lo:=1554844) (a:=391) (b:=391) r1554844 r1555235))) (join_sums term (lo:=1555626) (a:=1562) (b:=1563) (join_sums term (lo:=1555626) (a:=781) (b:=781) (join_sums term (lo:=1555626) (a:=390) (b:=391) r1555626 r1556016) (join_sums term (lo:=1556407) (a:=390) (b:=391) r1556407 r1556797)) (join_sums term (lo:=1557188) (a:=781) (b:=782) (join_sums term (lo:=1557188) (a:=390) (b:=391) r1557188 r1557578) (join_sums term (lo:=1557969) (a:=391) (b:=391) r1557969 r1558360)))) (join_sums term (lo:=1558751) (a:=3125) (b:=3125) (join_sums term (lo:=1558751) (a:=1562) (b:=1563) (join_sums term (lo:=1558751) (a:=781) (b:=781) (join_sums term (lo:=1558751) (a:=390) (b:=391) r1558751 r1559141) (join_sums term (lo:=1559532) (a:=390) (b:=391) r1559532 r1559922)) (join_sums term (lo:=1560313) (a:=781) (b:=782) (join_sums term (lo:=1560313) (a:=390) (b:=391) r1560313 r1560703) (join_sums term (lo:=1561094) (a:=391) (b:=391) r1561094 r1561485))) (join_sums term (lo:=1561876) (a:=1562) (b:=1563) (join_sums term (lo:=1561876) (a:=781) (b:=781) (join_sums term (lo:=1561876) (a:=390) (b:=391) r1561876 r1562266) (join_sums term (lo:=1562657) (a:=390) (b:=391) r1562657 r1563047)) (join_sums term (lo:=1563438) (a:=781) (b:=782) (join_sums term (lo:=1563438) (a:=390) (b:=391) r1563438 r1563828) (join_sums term (lo:=1564219) (a:=391) (b:=391) r1564219 r1564610)))))) (join_sums term (lo:=1565001) (a:=12500) (b:=12500) (join_sums term (lo:=1565001) (a:=6250) (b:=6250) (join_sums term (lo:=1565001) (a:=3125) (b:=3125) (join_sums term (lo:=1565001) (a:=1562) (b:=1563) (join_sums term (lo:=1565001) (a:=781) (b:=781) (join_sums term (lo:=1565001) (a:=390) (b:=391) r1565001 r1565391) (join_sums term (lo:=1565782) (a:=390) (b:=391) r1565782 r1566172)) (join_sums term (lo:=1566563) (a:=781) (b:=782) (join_sums term (lo:=1566563) (a:=390) (b:=391) r1566563 r1566953) (join_sums term (lo:=1567344) (a:=391) (b:=391) r1567344 r1567735))) (join_sums term (lo:=1568126) (a:=1562) (b:=1563) (join_sums term (lo:=1568126) (a:=781) (b:=781) (join_sums term (lo:=1568126) (a:=390) (b:=391) r1568126 r1568516) (join_sums term (lo:=1568907) (a:=390) (b:=391) r1568907 r1569297)) (join_sums term (lo:=1569688) (a:=781) (b:=782) (join_sums term (lo:=1569688) (a:=390) (b:=391) r1569688 r1570078) (join_sums term (lo:=1570469) (a:=391) (b:=391) r1570469 r1570860)))) (join_sums term (lo:=1571251) (a:=3125) (b:=3125) (join_sums term (lo:=1571251) (a:=1562) (b:=1563) (join_sums term (lo:=1571251) (a:=781) (b:=781) (join_sums term (lo:=1571251) (a:=390) (b:=391) r1571251 r1571641) (join_sums term (lo:=1572032) (a:=390) (b:=391) r1572032 r1572422)) (join_sums term (lo:=1572813) (a:=781) (b:=782) (join_sums term (lo:=1572813) (a:=390) (b:=391) r1572813 r1573203) (join_sums term (lo:=1573594) (a:=391) (b:=391) r1573594 r1573985))) (join_sums term (lo:=1574376) (a:=1562) (b:=1563) (join_sums term (lo:=1574376) (a:=781) (b:=781) (join_sums term (lo:=1574376) (a:=390) (b:=391) r1574376 r1574766) (join_sums term (lo:=1575157) (a:=390) (b:=391) r1575157 r1575547)) (join_sums term (lo:=1575938) (a:=781) (b:=782) (join_sums term (lo:=1575938) (a:=390) (b:=391) r1575938 r1576328) (join_sums term (lo:=1576719) (a:=391) (b:=391) r1576719 r1577110))))) (join_sums term (lo:=1577501) (a:=6250) (b:=6250) (join_sums term (lo:=1577501) (a:=3125) (b:=3125) (join_sums term (lo:=1577501) (a:=1562) (b:=1563) (join_sums term (lo:=1577501) (a:=781) (b:=781) (join_sums term (lo:=1577501) (a:=390) (b:=391) r1577501 r1577891) (join_sums term (lo:=1578282) (a:=390) (b:=391) r1578282 r1578672)) (join_sums term (lo:=1579063) (a:=781) (b:=782) (join_sums term (lo:=1579063) (a:=390) (b:=391) r1579063 r1579453) (join_sums term (lo:=1579844) (a:=391) (b:=391) r1579844 r1580235))) (join_sums term (lo:=1580626) (a:=1562) (b:=1563) (join_sums term (lo:=1580626) (a:=781) (b:=781) (join_sums term (lo:=1580626) (a:=390) (b:=391) r1580626 r1581016) (join_sums term (lo:=1581407) (a:=390) (b:=391) r1581407 r1581797)) (join_sums term (lo:=1582188) (a:=781) (b:=782) (join_sums term (lo:=1582188) (a:=390) (b:=391) r1582188 r1582578) (join_sums term (lo:=1582969) (a:=391) (b:=391) r1582969 r1583360)))) (join_sums term (lo:=1583751) (a:=3125) (b:=3125) (join_sums term (lo:=1583751) (a:=1562) (b:=1563) (join_sums term (lo:=1583751) (a:=781) (b:=781) (join_sums term (lo:=1583751) (a:=390) (b:=391) r1583751 r1584141) (join_sums term (lo:=1584532) (a:=390) (b:=391) r1584532 r1584922)) (join_sums term (lo:=1585313) (a:=781) (b:=782) (join_sums term (lo:=1585313) (a:=390) (b:=391) r1585313 r1585703) (join_sums term (lo:=1586094) (a:=391) (b:=391) r1586094 r1586485))) (join_sums term (lo:=1586876) (a:=1562) (b:=1563) (join_sums term (lo:=1586876) (a:=781) (b:=781) (join_sums term (lo:=1586876) (a:=390) (b:=391) r1586876 r1587266) (join_sums term (lo:=1587657) (a:=390) (b:=391) r1587657 r1588047)) (join_sums term (lo:=1588438) (a:=781) (b:=782) (join_sums term (lo:=1588438) (a:=390) (b:=391) r1588438 r1588828) (join_sums term (lo:=1589219) (a:=391) (b:=391) r1589219 r1589610))))))))

private theorem rows : blockSum term 0 1590001 7884761009 :=
  join_sums term (lo:=0) (a:=1490001) (b:=100000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 1590000).filter (1490000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=7884761009 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From1490000To1590000
