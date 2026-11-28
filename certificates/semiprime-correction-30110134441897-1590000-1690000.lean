import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 1,590,000 through 1,690,000

The sum covers 6,977 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From1590000To1690000

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


private abbrev term := contribution 30110134441897 1590000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 1590001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 1590000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r1590001 : blockSum term 1590001 390 31514148 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1590391 : blockSum term 1590391 391 23900470 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1590782 : blockSum term 1590782 390 24979441 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1591172 : blockSum term 1591172 391 28229761 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1591563 : blockSum term 1591563 390 24965133 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1591953 : blockSum term 1591953 391 28213670 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1592344 : blockSum term 1592344 391 26035577 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1592735 : blockSum term 1592735 391 29283738 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1593126 : blockSum term 1593126 390 32527856 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1593516 : blockSum term 1593516 391 28182597 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1593907 : blockSum term 1593907 390 32508768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1594297 : blockSum term 1594297 391 27084107 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1594688 : blockSum term 1594688 390 35741159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1595078 : blockSum term 1595078 391 32482741 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1595469 : blockSum term 1595469 391 30308361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1595860 : blockSum term 1595860 391 24889663 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1596251 : blockSum term 1596251 390 28128674 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1596641 : blockSum term 1596641 391 22713364 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1597032 : blockSum term 1597032 390 32437719 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1597422 : blockSum term 1597422 391 34589560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1597813 : blockSum term 1597813 390 29177207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1598203 : blockSum term 1598203 391 30249292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1598594 : blockSum term 1598594 391 28080277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1598985 : blockSum term 1598985 391 24833588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1599376 : blockSum term 1599376 390 24827028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1599766 : blockSum term 1599766 391 26978013 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1600157 : blockSum term 1600157 390 32365147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1600547 : blockSum term 1600547 391 29119670 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1600938 : blockSum term 1600938 390 31268160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1601328 : blockSum term 1601328 391 37727004 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1601719 : blockSum term 1601719 391 29096025 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1602110 : blockSum term 1602110 391 32319942 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1602501 : blockSum term 1602501 390 32310343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1602891 : blockSum term 1602891 391 33378888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1603282 : blockSum term 1603282 390 33369533 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1603672 : blockSum term 1603672 391 32284077 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1604063 : blockSum term 1604063 390 36578056 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1604453 : blockSum term 1604453 391 29039421 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1604844 : blockSum term 1604844 391 25804578 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1605235 : blockSum term 1605235 391 27947641 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1605626 : blockSum term 1605626 390 29014308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1606016 : blockSum term 1606016 391 26857147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1606407 : blockSum term 1606407 390 33294134 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1606797 : blockSum term 1606797 391 33284630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1607188 : blockSum term 1607188 390 24687846 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1607578 : blockSum term 1607578 391 30046636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1607969 : blockSum term 1607969 391 24673858 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1608360 : blockSum term 1608360 391 34319629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1608751 : blockSum term 1608751 390 22515974 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1609141 : blockSum term 1609141 391 26797361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1609532 : blockSum term 1609532 390 30004391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1609922 : blockSum term 1609922 391 27853682 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1610313 : blockSum term 1610313 390 33201327 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1610703 : blockSum term 1610703 391 31050371 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1611094 : blockSum term 1611094 391 33182622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1611485 : blockSum term 1611485 391 25683220 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1611876 : blockSum term 1611876 390 27816139 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1612266 : blockSum term 1612266 391 25669714 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1612657 : blockSum term 1612657 390 26731863 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1613047 : blockSum term 1613047 391 23517252 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1613438 : blockSum term 1613438 390 27785705 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1613828 : blockSum term 1613828 391 21367781 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1614219 : blockSum term 1614219 391 36315060 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1614610 : blockSum term 1614610 391 30965446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1615001 : blockSum term 1615001 390 27754245 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1615391 : blockSum term 1615391 391 32014465 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1615782 : blockSum term 1615782 390 28805079 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1616172 : blockSum term 1616172 391 24530893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1616563 : blockSum term 1616563 390 35187154 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1616953 : blockSum term 1616953 391 21319377 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1617344 : blockSum term 1617344 391 27707806 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1617735 : blockSum term 1617735 391 33026761 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1618126 : blockSum term 1618126 390 34082576 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1618516 : blockSum term 1618516 391 27684314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1618907 : blockSum term 1618907 390 29805591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1619297 : blockSum term 1619297 391 28732692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1619688 : blockSum term 1619688 390 28725001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1620078 : blockSum term 1620078 391 29779455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1620469 : blockSum term 1620469 391 27645551 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1620860 : blockSum term 1620860 391 29763654 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1621251 : blockSum term 1621251 390 30817623 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1621641 : blockSum term 1621641 391 27622594 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1622032 : blockSum term 1622032 390 25490602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1622422 : blockSum term 1622422 391 31854218 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1622813 : blockSum term 1622813 390 31845236 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1623203 : blockSum term 1623203 391 25469376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1623594 : blockSum term 1623594 391 28644667 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1623985 : blockSum term 1623985 391 30757821 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1624376 : blockSum term 1624376 390 27568573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1624766 : blockSum term 1624766 391 21200707 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1625157 : blockSum term 1625157 390 32852391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1625547 : blockSum term 1625547 391 32842462 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1625938 : blockSum term 1625938 390 36010890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1626328 : blockSum term 1626328 391 26471734 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1626719 : blockSum term 1626719 391 32815324 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1627110 : blockSum term 1627110 391 27515560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1627501 : blockSum term 1627501 390 40203362 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1627891 : blockSum term 1627891 391 26441933 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1628282 : blockSum term 1628282 390 29607858 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1628672 : blockSum term 1628672 391 25370742 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1629063 : blockSum term 1629063 390 34875645 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1629453 : blockSum term 1629453 391 23244285 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1629844 : blockSum term 1629844 391 26406685 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1630235 : blockSum term 1630235 391 33791725 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1630626 : blockSum term 1630626 390 23225394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1631016 : blockSum term 1631016 391 28496296 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1631407 : blockSum term 1631407 390 28488097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1631797 : blockSum term 1631797 391 31644724 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1632188 : blockSum term 1632188 390 28472448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1632578 : blockSum term 1632578 391 31627375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1632969 : blockSum term 1632969 391 33725933 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1633360 : blockSum term 1633360 391 27394264 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1633751 : blockSum term 1633751 390 31600632 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1634141 : blockSum term 1634141 391 33698539 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1634532 : blockSum term 1634532 390 28425315 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1634922 : blockSum term 1634922 391 31575294 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1635313 : blockSum term 1635313 390 28409474 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1635703 : blockSum term 1635703 391 30504738 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1636094 : blockSum term 1636094 391 27341433 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1636485 : blockSum term 1636485 391 33641773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1636876 : blockSum term 1636876 390 24173538 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1637266 : blockSum term 1637266 391 23115637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1637657 : blockSum term 1637657 390 24160787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1638047 : blockSum term 1638047 391 24154595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1638438 : blockSum term 1638438 390 24147024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1638828 : blockSum term 1638828 391 26239596 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1639219 : blockSum term 1639219 391 25183384 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1639610 : blockSum term 1639610 391 29372396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1640001 : blockSum term 1640001 390 26219274 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1640391 : blockSum term 1640391 391 30405919 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1640782 : blockSum term 1640782 390 25156801 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1641172 : blockSum term 1641172 391 20958299 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1641563 : blockSum term 1641563 390 31429390 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1641953 : blockSum term 1641953 391 28278307 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1642344 : blockSum term 1642344 391 29317832 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1642735 : blockSum term 1642735 391 29310265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1643126 : blockSum term 1643126 390 28255241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1643516 : blockSum term 1643516 391 36615949 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1643907 : blockSum term 1643907 390 25101068 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1644297 : blockSum term 1644297 391 28231395 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1644688 : blockSum term 1644688 390 26132777 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1645078 : blockSum term 1645078 391 28215347 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1645469 : blockSum term 1645469 391 30297588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1645860 : blockSum term 1645860 391 32378014 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1646251 : blockSum term 1646251 390 29236470 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1646641 : blockSum term 1646641 391 31315930 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1647032 : blockSum term 1647032 390 28176443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1647422 : blockSum term 1647422 391 22952027 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1647813 : blockSum term 1647813 390 26075723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1648203 : blockSum term 1648203 391 29195893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1648594 : blockSum term 1648594 391 19805777 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1648985 : blockSum term 1648985 391 29179387 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1649376 : blockSum term 1649376 390 32297074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1649766 : blockSum term 1649766 391 33330059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1650157 : blockSum term 1650157 390 27073394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1650547 : blockSum term 1650547 391 32270983 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1650938 : blockSum term 1650938 390 26016593 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1651328 : blockSum term 1651328 391 27049873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1651719 : blockSum term 1651719 391 23921947 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1652110 : blockSum term 1652110 391 24955223 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1652501 : blockSum term 1652501 390 34303394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1652891 : blockSum term 1652891 391 30138128 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1653282 : blockSum term 1653282 390 33246095 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1653672 : blockSum term 1653672 391 30120211 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1654063 : blockSum term 1654063 390 29073882 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1654453 : blockSum term 1654453 391 23875585 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1654844 : blockSum term 1654844 391 35284970 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1655235 : blockSum term 1655235 391 31125275 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1655626 : blockSum term 1655626 390 26968003 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1656016 : blockSum term 1656016 391 31109644 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1656407 : blockSum term 1656407 390 25916913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1656797 : blockSum term 1656797 391 36273958 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1657188 : blockSum term 1657188 390 20722147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1657578 : blockSum term 1657578 391 27967651 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1657969 : blockSum term 1657969 391 23817904 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1658360 : blockSum term 1658360 391 24847450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1658751 : blockSum term 1658751 390 30015347 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1659141 : blockSum term 1659141 391 23799119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1659532 : blockSum term 1659532 390 31033796 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1659922 : blockSum term 1659922 391 25853457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1660313 : blockSum term 1660313 390 26880447 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1660703 : blockSum term 1660703 391 24806681 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1661094 : blockSum term 1661094 391 25833167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1661485 : blockSum term 1661485 391 27892039 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1661876 : blockSum term 1661876 390 26851846 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1662266 : blockSum term 1662266 391 35104015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1662657 : blockSum term 1662657 390 30965916 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1663047 : blockSum term 1663047 391 26829701 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1663438 : blockSum term 1663438 390 27853914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1663828 : blockSum term 1663828 391 20627322 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1664219 : blockSum term 1664219 391 22683021 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1664610 : blockSum term 1664610 391 25769673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1665001 : blockSum term 1665001 390 28855371 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1665391 : blockSum term 1665391 391 30907358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1665782 : blockSum term 1665782 390 27808901 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1666172 : blockSum term 1666172 391 36038685 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1666563 : blockSum term 1666563 390 29852553 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1666953 : blockSum term 1666953 391 25728073 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1667344 : blockSum term 1667344 391 34981077 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1667735 : blockSum term 1667735 391 35999921 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1668126 : blockSum term 1668126 390 26734888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1668516 : blockSum term 1668516 391 27756416 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1668907 : blockSum term 1668907 390 31859228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1669297 : blockSum term 1669297 391 30823596 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1669688 : blockSum term 1669688 390 28760685 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1670078 : blockSum term 1670078 391 21564614 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1670469 : blockSum term 1670469 391 34905579 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1670860 : blockSum term 1670860 391 25658492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1671251 : blockSum term 1671251 390 25651602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1671641 : blockSum term 1671641 391 21541925 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1672032 : blockSum term 1672032 390 21536221 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1672422 : blockSum term 1672422 391 29733142 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1672813 : blockSum term 1672813 390 29724393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1673203 : blockSum term 1673203 391 28691514 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1673594 : blockSum term 1673594 391 31756680 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1673985 : blockSum term 1673985 391 24579324 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1674376 : blockSum term 1674376 390 28667862 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1674766 : blockSum term 1674766 391 34801423 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1675157 : blockSum term 1675157 390 25582504 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1675547 : blockSum term 1675547 391 32736409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1675938 : blockSum term 1675938 390 24545768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1676328 : blockSum term 1676328 391 28627944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1676719 : blockSum term 1676719 391 27598079 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1677110 : blockSum term 1677110 391 28612195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1677501 : blockSum term 1677501 390 26560682 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1677891 : blockSum term 1677891 391 29617084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1678282 : blockSum term 1678282 390 29609291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1678672 : blockSum term 1678672 391 35725170 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1679063 : blockSum term 1679063 390 27551787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1679453 : blockSum term 1679453 391 29584393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1679844 : blockSum term 1679844 391 23457038 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1680235 : blockSum term 1680235 391 30587839 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1680626 : blockSum term 1680626 390 30579260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1681016 : blockSum term 1681016 391 26495104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1681407 : blockSum term 1681407 390 25469339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1681797 : blockSum term 1681797 391 26481339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1682188 : blockSum term 1682188 390 31564394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1682578 : blockSum term 1682578 391 21376850 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1682969 : blockSum term 1682969 391 26459786 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1683360 : blockSum term 1683360 391 23400227 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1683751 : blockSum term 1683751 390 17291306 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1684141 : blockSum term 1684141 391 28472681 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1684532 : blockSum term 1684532 390 27448059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1684922 : blockSum term 1684922 391 28457264 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1685313 : blockSum term 1685313 390 30481388 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1685703 : blockSum term 1685703 391 32504254 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1686094 : blockSum term 1686094 391 29448514 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1686485 : blockSum term 1686485 391 28425495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1686876 : blockSum term 1686876 390 25372937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1687266 : blockSum term 1687266 391 25366137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1687657 : blockSum term 1687657 390 27388799 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1688047 : blockSum term 1688047 391 33465899 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1688438 : blockSum term 1688438 390 20276716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1688828 : blockSum term 1688828 391 26353122 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1689219 : blockSum term 1689219 391 22292751 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1689610 : blockSum term 1689610 391 26339161 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 1590001 100000 7320485227 := (join_sums term (lo:=1590001) (a:=50000) (b:=50000) (join_sums term (lo:=1590001) (a:=25000) (b:=25000) (join_sums term (lo:=1590001) (a:=12500) (b:=12500) (join_sums term (lo:=1590001) (a:=6250) (b:=6250) (join_sums term (lo:=1590001) (a:=3125) (b:=3125) (join_sums term (lo:=1590001) (a:=1562) (b:=1563) (join_sums term (lo:=1590001) (a:=781) (b:=781) (join_sums term (lo:=1590001) (a:=390) (b:=391) r1590001 r1590391) (join_sums term (lo:=1590782) (a:=390) (b:=391) r1590782 r1591172)) (join_sums term (lo:=1591563) (a:=781) (b:=782) (join_sums term (lo:=1591563) (a:=390) (b:=391) r1591563 r1591953) (join_sums term (lo:=1592344) (a:=391) (b:=391) r1592344 r1592735))) (join_sums term (lo:=1593126) (a:=1562) (b:=1563) (join_sums term (lo:=1593126) (a:=781) (b:=781) (join_sums term (lo:=1593126) (a:=390) (b:=391) r1593126 r1593516) (join_sums term (lo:=1593907) (a:=390) (b:=391) r1593907 r1594297)) (join_sums term (lo:=1594688) (a:=781) (b:=782) (join_sums term (lo:=1594688) (a:=390) (b:=391) r1594688 r1595078) (join_sums term (lo:=1595469) (a:=391) (b:=391) r1595469 r1595860)))) (join_sums term (lo:=1596251) (a:=3125) (b:=3125) (join_sums term (lo:=1596251) (a:=1562) (b:=1563) (join_sums term (lo:=1596251) (a:=781) (b:=781) (join_sums term (lo:=1596251) (a:=390) (b:=391) r1596251 r1596641) (join_sums term (lo:=1597032) (a:=390) (b:=391) r1597032 r1597422)) (join_sums term (lo:=1597813) (a:=781) (b:=782) (join_sums term (lo:=1597813) (a:=390) (b:=391) r1597813 r1598203) (join_sums term (lo:=1598594) (a:=391) (b:=391) r1598594 r1598985))) (join_sums term (lo:=1599376) (a:=1562) (b:=1563) (join_sums term (lo:=1599376) (a:=781) (b:=781) (join_sums term (lo:=1599376) (a:=390) (b:=391) r1599376 r1599766) (join_sums term (lo:=1600157) (a:=390) (b:=391) r1600157 r1600547)) (join_sums term (lo:=1600938) (a:=781) (b:=782) (join_sums term (lo:=1600938) (a:=390) (b:=391) r1600938 r1601328) (join_sums term (lo:=1601719) (a:=391) (b:=391) r1601719 r1602110))))) (join_sums term (lo:=1602501) (a:=6250) (b:=6250) (join_sums term (lo:=1602501) (a:=3125) (b:=3125) (join_sums term (lo:=1602501) (a:=1562) (b:=1563) (join_sums term (lo:=1602501) (a:=781) (b:=781) (join_sums term (lo:=1602501) (a:=390) (b:=391) r1602501 r1602891) (join_sums term (lo:=1603282) (a:=390) (b:=391) r1603282 r1603672)) (join_sums term (lo:=1604063) (a:=781) (b:=782) (join_sums term (lo:=1604063) (a:=390) (b:=391) r1604063 r1604453) (join_sums term (lo:=1604844) (a:=391) (b:=391) r1604844 r1605235))) (join_sums term (lo:=1605626) (a:=1562) (b:=1563) (join_sums term (lo:=1605626) (a:=781) (b:=781) (join_sums term (lo:=1605626) (a:=390) (b:=391) r1605626 r1606016) (join_sums term (lo:=1606407) (a:=390) (b:=391) r1606407 r1606797)) (join_sums term (lo:=1607188) (a:=781) (b:=782) (join_sums term (lo:=1607188) (a:=390) (b:=391) r1607188 r1607578) (join_sums term (lo:=1607969) (a:=391) (b:=391) r1607969 r1608360)))) (join_sums term (lo:=1608751) (a:=3125) (b:=3125) (join_sums term (lo:=1608751) (a:=1562) (b:=1563) (join_sums term (lo:=1608751) (a:=781) (b:=781) (join_sums term (lo:=1608751) (a:=390) (b:=391) r1608751 r1609141) (join_sums term (lo:=1609532) (a:=390) (b:=391) r1609532 r1609922)) (join_sums term (lo:=1610313) (a:=781) (b:=782) (join_sums term (lo:=1610313) (a:=390) (b:=391) r1610313 r1610703) (join_sums term (lo:=1611094) (a:=391) (b:=391) r1611094 r1611485))) (join_sums term (lo:=1611876) (a:=1562) (b:=1563) (join_sums term (lo:=1611876) (a:=781) (b:=781) (join_sums term (lo:=1611876) (a:=390) (b:=391) r1611876 r1612266) (join_sums term (lo:=1612657) (a:=390) (b:=391) r1612657 r1613047)) (join_sums term (lo:=1613438) (a:=781) (b:=782) (join_sums term (lo:=1613438) (a:=390) (b:=391) r1613438 r1613828) (join_sums term (lo:=1614219) (a:=391) (b:=391) r1614219 r1614610)))))) (join_sums term (lo:=1615001) (a:=12500) (b:=12500) (join_sums term (lo:=1615001) (a:=6250) (b:=6250) (join_sums term (lo:=1615001) (a:=3125) (b:=3125) (join_sums term (lo:=1615001) (a:=1562) (b:=1563) (join_sums term (lo:=1615001) (a:=781) (b:=781) (join_sums term (lo:=1615001) (a:=390) (b:=391) r1615001 r1615391) (join_sums term (lo:=1615782) (a:=390) (b:=391) r1615782 r1616172)) (join_sums term (lo:=1616563) (a:=781) (b:=782) (join_sums term (lo:=1616563) (a:=390) (b:=391) r1616563 r1616953) (join_sums term (lo:=1617344) (a:=391) (b:=391) r1617344 r1617735))) (join_sums term (lo:=1618126) (a:=1562) (b:=1563) (join_sums term (lo:=1618126) (a:=781) (b:=781) (join_sums term (lo:=1618126) (a:=390) (b:=391) r1618126 r1618516) (join_sums term (lo:=1618907) (a:=390) (b:=391) r1618907 r1619297)) (join_sums term (lo:=1619688) (a:=781) (b:=782) (join_sums term (lo:=1619688) (a:=390) (b:=391) r1619688 r1620078) (join_sums term (lo:=1620469) (a:=391) (b:=391) r1620469 r1620860)))) (join_sums term (lo:=1621251) (a:=3125) (b:=3125) (join_sums term (lo:=1621251) (a:=1562) (b:=1563) (join_sums term (lo:=1621251) (a:=781) (b:=781) (join_sums term (lo:=1621251) (a:=390) (b:=391) r1621251 r1621641) (join_sums term (lo:=1622032) (a:=390) (b:=391) r1622032 r1622422)) (join_sums term (lo:=1622813) (a:=781) (b:=782) (join_sums term (lo:=1622813) (a:=390) (b:=391) r1622813 r1623203) (join_sums term (lo:=1623594) (a:=391) (b:=391) r1623594 r1623985))) (join_sums term (lo:=1624376) (a:=1562) (b:=1563) (join_sums term (lo:=1624376) (a:=781) (b:=781) (join_sums term (lo:=1624376) (a:=390) (b:=391) r1624376 r1624766) (join_sums term (lo:=1625157) (a:=390) (b:=391) r1625157 r1625547)) (join_sums term (lo:=1625938) (a:=781) (b:=782) (join_sums term (lo:=1625938) (a:=390) (b:=391) r1625938 r1626328) (join_sums term (lo:=1626719) (a:=391) (b:=391) r1626719 r1627110))))) (join_sums term (lo:=1627501) (a:=6250) (b:=6250) (join_sums term (lo:=1627501) (a:=3125) (b:=3125) (join_sums term (lo:=1627501) (a:=1562) (b:=1563) (join_sums term (lo:=1627501) (a:=781) (b:=781) (join_sums term (lo:=1627501) (a:=390) (b:=391) r1627501 r1627891) (join_sums term (lo:=1628282) (a:=390) (b:=391) r1628282 r1628672)) (join_sums term (lo:=1629063) (a:=781) (b:=782) (join_sums term (lo:=1629063) (a:=390) (b:=391) r1629063 r1629453) (join_sums term (lo:=1629844) (a:=391) (b:=391) r1629844 r1630235))) (join_sums term (lo:=1630626) (a:=1562) (b:=1563) (join_sums term (lo:=1630626) (a:=781) (b:=781) (join_sums term (lo:=1630626) (a:=390) (b:=391) r1630626 r1631016) (join_sums term (lo:=1631407) (a:=390) (b:=391) r1631407 r1631797)) (join_sums term (lo:=1632188) (a:=781) (b:=782) (join_sums term (lo:=1632188) (a:=390) (b:=391) r1632188 r1632578) (join_sums term (lo:=1632969) (a:=391) (b:=391) r1632969 r1633360)))) (join_sums term (lo:=1633751) (a:=3125) (b:=3125) (join_sums term (lo:=1633751) (a:=1562) (b:=1563) (join_sums term (lo:=1633751) (a:=781) (b:=781) (join_sums term (lo:=1633751) (a:=390) (b:=391) r1633751 r1634141) (join_sums term (lo:=1634532) (a:=390) (b:=391) r1634532 r1634922)) (join_sums term (lo:=1635313) (a:=781) (b:=782) (join_sums term (lo:=1635313) (a:=390) (b:=391) r1635313 r1635703) (join_sums term (lo:=1636094) (a:=391) (b:=391) r1636094 r1636485))) (join_sums term (lo:=1636876) (a:=1562) (b:=1563) (join_sums term (lo:=1636876) (a:=781) (b:=781) (join_sums term (lo:=1636876) (a:=390) (b:=391) r1636876 r1637266) (join_sums term (lo:=1637657) (a:=390) (b:=391) r1637657 r1638047)) (join_sums term (lo:=1638438) (a:=781) (b:=782) (join_sums term (lo:=1638438) (a:=390) (b:=391) r1638438 r1638828) (join_sums term (lo:=1639219) (a:=391) (b:=391) r1639219 r1639610))))))) (join_sums term (lo:=1640001) (a:=25000) (b:=25000) (join_sums term (lo:=1640001) (a:=12500) (b:=12500) (join_sums term (lo:=1640001) (a:=6250) (b:=6250) (join_sums term (lo:=1640001) (a:=3125) (b:=3125) (join_sums term (lo:=1640001) (a:=1562) (b:=1563) (join_sums term (lo:=1640001) (a:=781) (b:=781) (join_sums term (lo:=1640001) (a:=390) (b:=391) r1640001 r1640391) (join_sums term (lo:=1640782) (a:=390) (b:=391) r1640782 r1641172)) (join_sums term (lo:=1641563) (a:=781) (b:=782) (join_sums term (lo:=1641563) (a:=390) (b:=391) r1641563 r1641953) (join_sums term (lo:=1642344) (a:=391) (b:=391) r1642344 r1642735))) (join_sums term (lo:=1643126) (a:=1562) (b:=1563) (join_sums term (lo:=1643126) (a:=781) (b:=781) (join_sums term (lo:=1643126) (a:=390) (b:=391) r1643126 r1643516) (join_sums term (lo:=1643907) (a:=390) (b:=391) r1643907 r1644297)) (join_sums term (lo:=1644688) (a:=781) (b:=782) (join_sums term (lo:=1644688) (a:=390) (b:=391) r1644688 r1645078) (join_sums term (lo:=1645469) (a:=391) (b:=391) r1645469 r1645860)))) (join_sums term (lo:=1646251) (a:=3125) (b:=3125) (join_sums term (lo:=1646251) (a:=1562) (b:=1563) (join_sums term (lo:=1646251) (a:=781) (b:=781) (join_sums term (lo:=1646251) (a:=390) (b:=391) r1646251 r1646641) (join_sums term (lo:=1647032) (a:=390) (b:=391) r1647032 r1647422)) (join_sums term (lo:=1647813) (a:=781) (b:=782) (join_sums term (lo:=1647813) (a:=390) (b:=391) r1647813 r1648203) (join_sums term (lo:=1648594) (a:=391) (b:=391) r1648594 r1648985))) (join_sums term (lo:=1649376) (a:=1562) (b:=1563) (join_sums term (lo:=1649376) (a:=781) (b:=781) (join_sums term (lo:=1649376) (a:=390) (b:=391) r1649376 r1649766) (join_sums term (lo:=1650157) (a:=390) (b:=391) r1650157 r1650547)) (join_sums term (lo:=1650938) (a:=781) (b:=782) (join_sums term (lo:=1650938) (a:=390) (b:=391) r1650938 r1651328) (join_sums term (lo:=1651719) (a:=391) (b:=391) r1651719 r1652110))))) (join_sums term (lo:=1652501) (a:=6250) (b:=6250) (join_sums term (lo:=1652501) (a:=3125) (b:=3125) (join_sums term (lo:=1652501) (a:=1562) (b:=1563) (join_sums term (lo:=1652501) (a:=781) (b:=781) (join_sums term (lo:=1652501) (a:=390) (b:=391) r1652501 r1652891) (join_sums term (lo:=1653282) (a:=390) (b:=391) r1653282 r1653672)) (join_sums term (lo:=1654063) (a:=781) (b:=782) (join_sums term (lo:=1654063) (a:=390) (b:=391) r1654063 r1654453) (join_sums term (lo:=1654844) (a:=391) (b:=391) r1654844 r1655235))) (join_sums term (lo:=1655626) (a:=1562) (b:=1563) (join_sums term (lo:=1655626) (a:=781) (b:=781) (join_sums term (lo:=1655626) (a:=390) (b:=391) r1655626 r1656016) (join_sums term (lo:=1656407) (a:=390) (b:=391) r1656407 r1656797)) (join_sums term (lo:=1657188) (a:=781) (b:=782) (join_sums term (lo:=1657188) (a:=390) (b:=391) r1657188 r1657578) (join_sums term (lo:=1657969) (a:=391) (b:=391) r1657969 r1658360)))) (join_sums term (lo:=1658751) (a:=3125) (b:=3125) (join_sums term (lo:=1658751) (a:=1562) (b:=1563) (join_sums term (lo:=1658751) (a:=781) (b:=781) (join_sums term (lo:=1658751) (a:=390) (b:=391) r1658751 r1659141) (join_sums term (lo:=1659532) (a:=390) (b:=391) r1659532 r1659922)) (join_sums term (lo:=1660313) (a:=781) (b:=782) (join_sums term (lo:=1660313) (a:=390) (b:=391) r1660313 r1660703) (join_sums term (lo:=1661094) (a:=391) (b:=391) r1661094 r1661485))) (join_sums term (lo:=1661876) (a:=1562) (b:=1563) (join_sums term (lo:=1661876) (a:=781) (b:=781) (join_sums term (lo:=1661876) (a:=390) (b:=391) r1661876 r1662266) (join_sums term (lo:=1662657) (a:=390) (b:=391) r1662657 r1663047)) (join_sums term (lo:=1663438) (a:=781) (b:=782) (join_sums term (lo:=1663438) (a:=390) (b:=391) r1663438 r1663828) (join_sums term (lo:=1664219) (a:=391) (b:=391) r1664219 r1664610)))))) (join_sums term (lo:=1665001) (a:=12500) (b:=12500) (join_sums term (lo:=1665001) (a:=6250) (b:=6250) (join_sums term (lo:=1665001) (a:=3125) (b:=3125) (join_sums term (lo:=1665001) (a:=1562) (b:=1563) (join_sums term (lo:=1665001) (a:=781) (b:=781) (join_sums term (lo:=1665001) (a:=390) (b:=391) r1665001 r1665391) (join_sums term (lo:=1665782) (a:=390) (b:=391) r1665782 r1666172)) (join_sums term (lo:=1666563) (a:=781) (b:=782) (join_sums term (lo:=1666563) (a:=390) (b:=391) r1666563 r1666953) (join_sums term (lo:=1667344) (a:=391) (b:=391) r1667344 r1667735))) (join_sums term (lo:=1668126) (a:=1562) (b:=1563) (join_sums term (lo:=1668126) (a:=781) (b:=781) (join_sums term (lo:=1668126) (a:=390) (b:=391) r1668126 r1668516) (join_sums term (lo:=1668907) (a:=390) (b:=391) r1668907 r1669297)) (join_sums term (lo:=1669688) (a:=781) (b:=782) (join_sums term (lo:=1669688) (a:=390) (b:=391) r1669688 r1670078) (join_sums term (lo:=1670469) (a:=391) (b:=391) r1670469 r1670860)))) (join_sums term (lo:=1671251) (a:=3125) (b:=3125) (join_sums term (lo:=1671251) (a:=1562) (b:=1563) (join_sums term (lo:=1671251) (a:=781) (b:=781) (join_sums term (lo:=1671251) (a:=390) (b:=391) r1671251 r1671641) (join_sums term (lo:=1672032) (a:=390) (b:=391) r1672032 r1672422)) (join_sums term (lo:=1672813) (a:=781) (b:=782) (join_sums term (lo:=1672813) (a:=390) (b:=391) r1672813 r1673203) (join_sums term (lo:=1673594) (a:=391) (b:=391) r1673594 r1673985))) (join_sums term (lo:=1674376) (a:=1562) (b:=1563) (join_sums term (lo:=1674376) (a:=781) (b:=781) (join_sums term (lo:=1674376) (a:=390) (b:=391) r1674376 r1674766) (join_sums term (lo:=1675157) (a:=390) (b:=391) r1675157 r1675547)) (join_sums term (lo:=1675938) (a:=781) (b:=782) (join_sums term (lo:=1675938) (a:=390) (b:=391) r1675938 r1676328) (join_sums term (lo:=1676719) (a:=391) (b:=391) r1676719 r1677110))))) (join_sums term (lo:=1677501) (a:=6250) (b:=6250) (join_sums term (lo:=1677501) (a:=3125) (b:=3125) (join_sums term (lo:=1677501) (a:=1562) (b:=1563) (join_sums term (lo:=1677501) (a:=781) (b:=781) (join_sums term (lo:=1677501) (a:=390) (b:=391) r1677501 r1677891) (join_sums term (lo:=1678282) (a:=390) (b:=391) r1678282 r1678672)) (join_sums term (lo:=1679063) (a:=781) (b:=782) (join_sums term (lo:=1679063) (a:=390) (b:=391) r1679063 r1679453) (join_sums term (lo:=1679844) (a:=391) (b:=391) r1679844 r1680235))) (join_sums term (lo:=1680626) (a:=1562) (b:=1563) (join_sums term (lo:=1680626) (a:=781) (b:=781) (join_sums term (lo:=1680626) (a:=390) (b:=391) r1680626 r1681016) (join_sums term (lo:=1681407) (a:=390) (b:=391) r1681407 r1681797)) (join_sums term (lo:=1682188) (a:=781) (b:=782) (join_sums term (lo:=1682188) (a:=390) (b:=391) r1682188 r1682578) (join_sums term (lo:=1682969) (a:=391) (b:=391) r1682969 r1683360)))) (join_sums term (lo:=1683751) (a:=3125) (b:=3125) (join_sums term (lo:=1683751) (a:=1562) (b:=1563) (join_sums term (lo:=1683751) (a:=781) (b:=781) (join_sums term (lo:=1683751) (a:=390) (b:=391) r1683751 r1684141) (join_sums term (lo:=1684532) (a:=390) (b:=391) r1684532 r1684922)) (join_sums term (lo:=1685313) (a:=781) (b:=782) (join_sums term (lo:=1685313) (a:=390) (b:=391) r1685313 r1685703) (join_sums term (lo:=1686094) (a:=391) (b:=391) r1686094 r1686485))) (join_sums term (lo:=1686876) (a:=1562) (b:=1563) (join_sums term (lo:=1686876) (a:=781) (b:=781) (join_sums term (lo:=1686876) (a:=390) (b:=391) r1686876 r1687266) (join_sums term (lo:=1687657) (a:=390) (b:=391) r1687657 r1688047)) (join_sums term (lo:=1688438) (a:=781) (b:=782) (join_sums term (lo:=1688438) (a:=390) (b:=391) r1688438 r1688828) (join_sums term (lo:=1689219) (a:=391) (b:=391) r1689219 r1689610))))))))

private theorem rows : blockSum term 0 1690001 7320485227 :=
  join_sums term (lo:=0) (a:=1590001) (b:=100000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 1690000).filter (1590000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=7320485227 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From1590000To1690000
