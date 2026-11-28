import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 1,690,000 through 1,790,000

The sum covers 6,931 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From1690000To1790000

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


private abbrev term := contribution 30110134441897 1690000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 1690001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 1690000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r1690001 : blockSum term 1690001 390 30383255 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1690391 : blockSum term 1690391 391 27337613 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1690782 : blockSum term 1690782 390 24293277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1691172 : blockSum term 1691172 391 31370325 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1691563 : blockSum term 1691563 390 29338761 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1691953 : blockSum term 1691953 391 29330821 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1692344 : blockSum term 1692344 391 24266612 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1692735 : blockSum term 1692735 391 27292581 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1693126 : blockSum term 1693126 390 25263966 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1693516 : blockSum term 1693516 391 30308944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1693907 : blockSum term 1693907 390 29289302 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1694297 : blockSum term 1694297 391 26253142 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1694688 : blockSum term 1694688 390 24227236 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1695078 : blockSum term 1695078 391 27247838 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1695469 : blockSum term 1695469 391 31276058 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1695860 : blockSum term 1695860 391 27232920 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1696251 : blockSum term 1696251 390 29242920 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1696641 : blockSum term 1696641 391 19154526 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1697032 : blockSum term 1697032 390 34267121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1697422 : blockSum term 1697422 391 28212509 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1697813 : blockSum term 1697813 390 31226970 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1698203 : blockSum term 1698203 391 26183429 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1698594 : blockSum term 1698594 391 29196059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1698985 : blockSum term 1698985 391 31201283 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1699376 : blockSum term 1699376 390 27168055 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1699766 : blockSum term 1699766 391 30179010 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1700157 : blockSum term 1700157 390 25142596 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1700547 : blockSum term 1700547 391 29157738 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1700938 : blockSum term 1700938 390 28144189 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1701328 : blockSum term 1701328 391 30146416 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1701719 : blockSum term 1701719 391 33152173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1702110 : blockSum term 1702110 391 21091081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1702501 : blockSum term 1702501 390 33133622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1702891 : blockSum term 1702891 391 25094606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1703282 : blockSum term 1703282 390 21073707 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1703672 : blockSum term 1703672 391 23075120 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1704063 : blockSum term 1704063 390 28083677 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1704453 : blockSum term 1704453 391 27073472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1704844 : blockSum term 1704844 391 30073722 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1705235 : blockSum term 1705235 391 25055174 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1705626 : blockSum term 1705626 390 26049849 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1706016 : blockSum term 1706016 391 26043414 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1706407 : blockSum term 1706407 390 29041216 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1706797 : blockSum term 1706797 391 26029878 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1707188 : blockSum term 1707188 390 28023746 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1707578 : blockSum term 1707578 391 29016725 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1707969 : blockSum term 1707969 391 24007951 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1708360 : blockSum term 1708360 391 29001833 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1708751 : blockSum term 1708751 390 27993406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1709141 : blockSum term 1709141 391 31983825 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1709532 : blockSum term 1709532 390 18985414 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1709922 : blockSum term 1709922 391 33965235 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1710313 : blockSum term 1710313 390 30959334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1710703 : blockSum term 1710703 391 24960735 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1711094 : blockSum term 1711094 391 22958294 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1711485 : blockSum term 1711485 391 24948278 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1711876 : blockSum term 1711876 390 29929773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1712266 : blockSum term 1712266 391 26929380 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1712657 : blockSum term 1712657 390 23930457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1713047 : blockSum term 1713047 391 19936741 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1713438 : blockSum term 1713438 390 27904089 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1713828 : blockSum term 1713828 391 28892346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1714219 : blockSum term 1714219 391 24900614 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1714610 : blockSum term 1714610 391 30868976 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1715001 : blockSum term 1715001 390 20905759 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1715391 : blockSum term 1715391 391 31847983 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1715782 : blockSum term 1715782 390 27859242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1716172 : blockSum term 1716172 391 31829808 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1716563 : blockSum term 1716563 390 27843413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1716953 : blockSum term 1716953 391 21871130 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1717344 : blockSum term 1717344 391 24847555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1717735 : blockSum term 1717735 391 21859532 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1718126 : blockSum term 1718126 390 34767354 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1718516 : blockSum term 1718516 391 29792353 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1718907 : blockSum term 1718907 390 18863813 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1719297 : blockSum term 1719297 391 25807148 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1719688 : blockSum term 1719688 390 29769681 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1720078 : blockSum term 1720078 391 30753817 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1720469 : blockSum term 1720469 391 23802282 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1720860 : blockSum term 1720860 391 23796016 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1721251 : blockSum term 1721251 390 29736630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1721641 : blockSum term 1721641 391 28737923 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1722032 : blockSum term 1722032 390 25758206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1722422 : blockSum term 1722422 391 24760631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1722813 : blockSum term 1722813 390 20793361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1723203 : blockSum term 1723203 391 22767218 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1723594 : blockSum term 1723594 391 24740493 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1723985 : blockSum term 1723985 391 25722507 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1724376 : blockSum term 1724376 390 33628924 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1724766 : blockSum term 1724766 391 27686702 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1725157 : blockSum term 1725157 390 24713842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1725547 : blockSum term 1725547 391 21742366 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1725938 : blockSum term 1725938 390 30629030 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1726328 : blockSum term 1726328 391 30620909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1726719 : blockSum term 1726719 391 29624649 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1727110 : blockSum term 1727110 391 25668168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1727501 : blockSum term 1727501 390 30596139 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1727891 : blockSum term 1727891 391 25654745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1728282 : blockSum term 1728282 390 20715750 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1728672 : blockSum term 1728672 391 29585856 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1729063 : blockSum term 1729063 390 27606032 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1729453 : blockSum term 1729453 391 28583300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1729844 : blockSum term 1729844 391 23648908 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1730235 : blockSum term 1730235 391 21672287 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1730626 : blockSum term 1730626 390 30529508 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1731016 : blockSum term 1731016 391 21660396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1731407 : blockSum term 1731407 390 23624036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1731797 : blockSum term 1731797 391 23617683 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1732188 : blockSum term 1732188 390 32465565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1732578 : blockSum term 1732578 391 28521806 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1732969 : blockSum term 1732969 391 30481048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1733360 : blockSum term 1733360 391 22608420 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1733751 : blockSum term 1733751 390 27516502 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1734141 : blockSum term 1734141 391 22597568 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1734532 : blockSum term 1734532 390 28484626 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1734922 : blockSum term 1734922 391 21603278 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1735313 : blockSum term 1735313 390 25524715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1735703 : blockSum term 1735703 391 25518530 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1736094 : blockSum term 1736094 391 29436470 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1736485 : blockSum term 1736485 391 25504183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1736876 : blockSum term 1736876 390 25498542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1737266 : blockSum term 1737266 391 26471087 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1737657 : blockSum term 1737657 390 23523745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1738047 : blockSum term 1738047 391 28416336 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1738438 : blockSum term 1738438 390 26449071 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1738828 : blockSum term 1738828 391 30359408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1739219 : blockSum term 1739219 391 31329576 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1739610 : blockSum term 1739610 391 28385299 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1740001 : blockSum term 1740001 390 30334159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1740391 : blockSum term 1740391 391 24456686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1740782 : blockSum term 1740782 390 26406093 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1741172 : blockSum term 1741172 391 25420655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1741563 : blockSum term 1741563 390 23459399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1741953 : blockSum term 1741953 391 19544399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1742344 : blockSum term 1742344 391 32239498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1742735 : blockSum term 1742735 391 23440524 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1743126 : blockSum term 1743126 390 23434293 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1743516 : blockSum term 1743516 391 31237914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1743907 : blockSum term 1743907 390 23421978 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1744297 : blockSum term 1744297 391 28294363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1744688 : blockSum term 1744688 390 20483675 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1745078 : blockSum term 1745078 391 27304119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1745469 : blockSum term 1745469 391 29246635 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1745860 : blockSum term 1745860 391 23391573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1746251 : blockSum term 1746251 390 33129387 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1746641 : blockSum term 1746641 391 31171560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1747032 : blockSum term 1747032 390 28241857 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1747422 : blockSum term 1747422 391 24339647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1747813 : blockSum term 1747813 390 27252521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1748203 : blockSum term 1748203 391 24326439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1748594 : blockSum term 1748594 391 28211236 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1748985 : blockSum term 1748985 391 38901136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1749376 : blockSum term 1749376 390 27224137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1749766 : blockSum term 1749766 391 25272332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1750157 : blockSum term 1750157 390 28181126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1750547 : blockSum term 1750547 391 27202352 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1750938 : blockSum term 1750938 390 25252869 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1751328 : blockSum term 1751328 391 28158532 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1751719 : blockSum term 1751719 391 24268847 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1752110 : blockSum term 1752110 391 30085487 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1752501 : blockSum term 1752501 390 29107102 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1752891 : blockSum term 1752891 391 26190578 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1753282 : blockSum term 1753282 390 28122166 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1753672 : blockSum term 1753672 391 27145654 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1754063 : blockSum term 1754063 390 25199919 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1754453 : blockSum term 1754453 391 26163036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1754844 : blockSum term 1754844 391 22281239 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1755235 : blockSum term 1755235 391 26148721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1755626 : blockSum term 1755626 390 27110933 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1756016 : blockSum term 1756016 391 25167056 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1756407 : blockSum term 1756407 390 24193073 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1756797 : blockSum term 1756797 391 24187387 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1757188 : blockSum term 1757188 390 26115433 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1757578 : blockSum term 1757578 391 24174001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1757969 : blockSum term 1757969 391 29001370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1758360 : blockSum term 1758360 391 23195396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1758751 : blockSum term 1758751 390 23189352 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1759141 : blockSum term 1759141 391 25114779 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1759532 : blockSum term 1759532 390 21246064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1759922 : blockSum term 1759922 391 23170783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1760313 : blockSum term 1760313 390 23164822 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1760703 : blockSum term 1760703 391 24124563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1761094 : blockSum term 1761094 391 21223865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1761485 : blockSum term 1761485 391 26039997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1761876 : blockSum term 1761876 390 23140501 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1762266 : blockSum term 1762266 391 26026172 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1762657 : blockSum term 1762657 390 22165176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1763047 : blockSum term 1763047 391 26976279 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1763438 : blockSum term 1763438 390 24079824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1763828 : blockSum term 1763828 391 30813998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1764219 : blockSum term 1764219 391 28880486 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1764610 : blockSum term 1764610 391 25985154 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1765001 : blockSum term 1765001 390 21167377 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1765391 : blockSum term 1765391 391 24047001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1765782 : blockSum term 1765782 390 29811109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1766172 : blockSum term 1766172 391 24996701 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1766563 : blockSum term 1766563 390 25951438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1766953 : blockSum term 1766953 391 25944491 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1767344 : blockSum term 1767344 391 27859104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1767735 : blockSum term 1767735 391 25931367 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1768126 : blockSum term 1768126 390 28804205 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1768516 : blockSum term 1768516 391 28796783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1768907 : blockSum term 1768907 390 25909766 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1769297 : blockSum term 1769297 391 23025183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1769688 : blockSum term 1769688 390 25896256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1770078 : blockSum term 1770078 391 23972002 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1770469 : blockSum term 1770469 391 26840852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1770860 : blockSum term 1770860 391 28750390 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1771251 : blockSum term 1771251 390 24910721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1771641 : blockSum term 1771641 391 19156791 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1772032 : blockSum term 1772032 390 24897184 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1772422 : blockSum term 1772422 391 28720437 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1772813 : blockSum term 1772813 390 22970260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1773203 : blockSum term 1773203 391 26791938 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1773594 : blockSum term 1773594 391 35393396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1773985 : blockSum term 1773985 391 28689122 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1774376 : blockSum term 1774376 390 25813424 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1774766 : blockSum term 1774766 391 20072748 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1775157 : blockSum term 1775157 390 26756368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1775547 : blockSum term 1775547 391 30569845 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1775938 : blockSum term 1775938 390 29605145 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1776328 : blockSum term 1776328 391 19095281 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1776719 : blockSum term 1776719 391 29589902 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1777110 : blockSum term 1777110 391 20993181 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1777501 : blockSum term 1777501 390 21941914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1777891 : blockSum term 1777891 391 33381512 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1778282 : blockSum term 1778282 390 27651683 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1778672 : blockSum term 1778672 391 27644197 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1779063 : blockSum term 1779063 390 25731034 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1779453 : blockSum term 1779453 391 22866284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1779844 : blockSum term 1779844 391 29527657 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1780235 : blockSum term 1780235 391 33328536 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1780626 : blockSum term 1780626 390 21896047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1781016 : blockSum term 1781016 391 24745353 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1781407 : blockSum term 1781407 390 27593212 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1781797 : blockSum term 1781797 391 21878772 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1782188 : blockSum term 1782188 390 29480414 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1782578 : blockSum term 1782578 391 26620379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1782969 : blockSum term 1782969 391 22811890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1783360 : blockSum term 1783360 391 29458030 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1783751 : blockSum term 1783751 390 21850758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1784141 : blockSum term 1784141 391 22794880 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1784532 : blockSum term 1784532 390 30384810 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1784922 : blockSum term 1784922 391 24681035 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1785313 : blockSum term 1785313 390 25623476 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1785703 : blockSum term 1785703 391 21821775 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1786094 : blockSum term 1786094 391 28455128 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1786485 : blockSum term 1786485 391 25603317 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1786876 : blockSum term 1786876 390 26544824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1787266 : blockSum term 1787266 391 28433989 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1787657 : blockSum term 1787657 390 23688462 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1788047 : blockSum term 1788047 391 21787663 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1788438 : blockSum term 1788438 390 26517408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1788828 : blockSum term 1788828 391 22722920 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1789219 : blockSum term 1789219 391 23663859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1789610 : blockSum term 1789610 391 21764943 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 1690001 100000 6786048431 := (join_sums term (lo:=1690001) (a:=50000) (b:=50000) (join_sums term (lo:=1690001) (a:=25000) (b:=25000) (join_sums term (lo:=1690001) (a:=12500) (b:=12500) (join_sums term (lo:=1690001) (a:=6250) (b:=6250) (join_sums term (lo:=1690001) (a:=3125) (b:=3125) (join_sums term (lo:=1690001) (a:=1562) (b:=1563) (join_sums term (lo:=1690001) (a:=781) (b:=781) (join_sums term (lo:=1690001) (a:=390) (b:=391) r1690001 r1690391) (join_sums term (lo:=1690782) (a:=390) (b:=391) r1690782 r1691172)) (join_sums term (lo:=1691563) (a:=781) (b:=782) (join_sums term (lo:=1691563) (a:=390) (b:=391) r1691563 r1691953) (join_sums term (lo:=1692344) (a:=391) (b:=391) r1692344 r1692735))) (join_sums term (lo:=1693126) (a:=1562) (b:=1563) (join_sums term (lo:=1693126) (a:=781) (b:=781) (join_sums term (lo:=1693126) (a:=390) (b:=391) r1693126 r1693516) (join_sums term (lo:=1693907) (a:=390) (b:=391) r1693907 r1694297)) (join_sums term (lo:=1694688) (a:=781) (b:=782) (join_sums term (lo:=1694688) (a:=390) (b:=391) r1694688 r1695078) (join_sums term (lo:=1695469) (a:=391) (b:=391) r1695469 r1695860)))) (join_sums term (lo:=1696251) (a:=3125) (b:=3125) (join_sums term (lo:=1696251) (a:=1562) (b:=1563) (join_sums term (lo:=1696251) (a:=781) (b:=781) (join_sums term (lo:=1696251) (a:=390) (b:=391) r1696251 r1696641) (join_sums term (lo:=1697032) (a:=390) (b:=391) r1697032 r1697422)) (join_sums term (lo:=1697813) (a:=781) (b:=782) (join_sums term (lo:=1697813) (a:=390) (b:=391) r1697813 r1698203) (join_sums term (lo:=1698594) (a:=391) (b:=391) r1698594 r1698985))) (join_sums term (lo:=1699376) (a:=1562) (b:=1563) (join_sums term (lo:=1699376) (a:=781) (b:=781) (join_sums term (lo:=1699376) (a:=390) (b:=391) r1699376 r1699766) (join_sums term (lo:=1700157) (a:=390) (b:=391) r1700157 r1700547)) (join_sums term (lo:=1700938) (a:=781) (b:=782) (join_sums term (lo:=1700938) (a:=390) (b:=391) r1700938 r1701328) (join_sums term (lo:=1701719) (a:=391) (b:=391) r1701719 r1702110))))) (join_sums term (lo:=1702501) (a:=6250) (b:=6250) (join_sums term (lo:=1702501) (a:=3125) (b:=3125) (join_sums term (lo:=1702501) (a:=1562) (b:=1563) (join_sums term (lo:=1702501) (a:=781) (b:=781) (join_sums term (lo:=1702501) (a:=390) (b:=391) r1702501 r1702891) (join_sums term (lo:=1703282) (a:=390) (b:=391) r1703282 r1703672)) (join_sums term (lo:=1704063) (a:=781) (b:=782) (join_sums term (lo:=1704063) (a:=390) (b:=391) r1704063 r1704453) (join_sums term (lo:=1704844) (a:=391) (b:=391) r1704844 r1705235))) (join_sums term (lo:=1705626) (a:=1562) (b:=1563) (join_sums term (lo:=1705626) (a:=781) (b:=781) (join_sums term (lo:=1705626) (a:=390) (b:=391) r1705626 r1706016) (join_sums term (lo:=1706407) (a:=390) (b:=391) r1706407 r1706797)) (join_sums term (lo:=1707188) (a:=781) (b:=782) (join_sums term (lo:=1707188) (a:=390) (b:=391) r1707188 r1707578) (join_sums term (lo:=1707969) (a:=391) (b:=391) r1707969 r1708360)))) (join_sums term (lo:=1708751) (a:=3125) (b:=3125) (join_sums term (lo:=1708751) (a:=1562) (b:=1563) (join_sums term (lo:=1708751) (a:=781) (b:=781) (join_sums term (lo:=1708751) (a:=390) (b:=391) r1708751 r1709141) (join_sums term (lo:=1709532) (a:=390) (b:=391) r1709532 r1709922)) (join_sums term (lo:=1710313) (a:=781) (b:=782) (join_sums term (lo:=1710313) (a:=390) (b:=391) r1710313 r1710703) (join_sums term (lo:=1711094) (a:=391) (b:=391) r1711094 r1711485))) (join_sums term (lo:=1711876) (a:=1562) (b:=1563) (join_sums term (lo:=1711876) (a:=781) (b:=781) (join_sums term (lo:=1711876) (a:=390) (b:=391) r1711876 r1712266) (join_sums term (lo:=1712657) (a:=390) (b:=391) r1712657 r1713047)) (join_sums term (lo:=1713438) (a:=781) (b:=782) (join_sums term (lo:=1713438) (a:=390) (b:=391) r1713438 r1713828) (join_sums term (lo:=1714219) (a:=391) (b:=391) r1714219 r1714610)))))) (join_sums term (lo:=1715001) (a:=12500) (b:=12500) (join_sums term (lo:=1715001) (a:=6250) (b:=6250) (join_sums term (lo:=1715001) (a:=3125) (b:=3125) (join_sums term (lo:=1715001) (a:=1562) (b:=1563) (join_sums term (lo:=1715001) (a:=781) (b:=781) (join_sums term (lo:=1715001) (a:=390) (b:=391) r1715001 r1715391) (join_sums term (lo:=1715782) (a:=390) (b:=391) r1715782 r1716172)) (join_sums term (lo:=1716563) (a:=781) (b:=782) (join_sums term (lo:=1716563) (a:=390) (b:=391) r1716563 r1716953) (join_sums term (lo:=1717344) (a:=391) (b:=391) r1717344 r1717735))) (join_sums term (lo:=1718126) (a:=1562) (b:=1563) (join_sums term (lo:=1718126) (a:=781) (b:=781) (join_sums term (lo:=1718126) (a:=390) (b:=391) r1718126 r1718516) (join_sums term (lo:=1718907) (a:=390) (b:=391) r1718907 r1719297)) (join_sums term (lo:=1719688) (a:=781) (b:=782) (join_sums term (lo:=1719688) (a:=390) (b:=391) r1719688 r1720078) (join_sums term (lo:=1720469) (a:=391) (b:=391) r1720469 r1720860)))) (join_sums term (lo:=1721251) (a:=3125) (b:=3125) (join_sums term (lo:=1721251) (a:=1562) (b:=1563) (join_sums term (lo:=1721251) (a:=781) (b:=781) (join_sums term (lo:=1721251) (a:=390) (b:=391) r1721251 r1721641) (join_sums term (lo:=1722032) (a:=390) (b:=391) r1722032 r1722422)) (join_sums term (lo:=1722813) (a:=781) (b:=782) (join_sums term (lo:=1722813) (a:=390) (b:=391) r1722813 r1723203) (join_sums term (lo:=1723594) (a:=391) (b:=391) r1723594 r1723985))) (join_sums term (lo:=1724376) (a:=1562) (b:=1563) (join_sums term (lo:=1724376) (a:=781) (b:=781) (join_sums term (lo:=1724376) (a:=390) (b:=391) r1724376 r1724766) (join_sums term (lo:=1725157) (a:=390) (b:=391) r1725157 r1725547)) (join_sums term (lo:=1725938) (a:=781) (b:=782) (join_sums term (lo:=1725938) (a:=390) (b:=391) r1725938 r1726328) (join_sums term (lo:=1726719) (a:=391) (b:=391) r1726719 r1727110))))) (join_sums term (lo:=1727501) (a:=6250) (b:=6250) (join_sums term (lo:=1727501) (a:=3125) (b:=3125) (join_sums term (lo:=1727501) (a:=1562) (b:=1563) (join_sums term (lo:=1727501) (a:=781) (b:=781) (join_sums term (lo:=1727501) (a:=390) (b:=391) r1727501 r1727891) (join_sums term (lo:=1728282) (a:=390) (b:=391) r1728282 r1728672)) (join_sums term (lo:=1729063) (a:=781) (b:=782) (join_sums term (lo:=1729063) (a:=390) (b:=391) r1729063 r1729453) (join_sums term (lo:=1729844) (a:=391) (b:=391) r1729844 r1730235))) (join_sums term (lo:=1730626) (a:=1562) (b:=1563) (join_sums term (lo:=1730626) (a:=781) (b:=781) (join_sums term (lo:=1730626) (a:=390) (b:=391) r1730626 r1731016) (join_sums term (lo:=1731407) (a:=390) (b:=391) r1731407 r1731797)) (join_sums term (lo:=1732188) (a:=781) (b:=782) (join_sums term (lo:=1732188) (a:=390) (b:=391) r1732188 r1732578) (join_sums term (lo:=1732969) (a:=391) (b:=391) r1732969 r1733360)))) (join_sums term (lo:=1733751) (a:=3125) (b:=3125) (join_sums term (lo:=1733751) (a:=1562) (b:=1563) (join_sums term (lo:=1733751) (a:=781) (b:=781) (join_sums term (lo:=1733751) (a:=390) (b:=391) r1733751 r1734141) (join_sums term (lo:=1734532) (a:=390) (b:=391) r1734532 r1734922)) (join_sums term (lo:=1735313) (a:=781) (b:=782) (join_sums term (lo:=1735313) (a:=390) (b:=391) r1735313 r1735703) (join_sums term (lo:=1736094) (a:=391) (b:=391) r1736094 r1736485))) (join_sums term (lo:=1736876) (a:=1562) (b:=1563) (join_sums term (lo:=1736876) (a:=781) (b:=781) (join_sums term (lo:=1736876) (a:=390) (b:=391) r1736876 r1737266) (join_sums term (lo:=1737657) (a:=390) (b:=391) r1737657 r1738047)) (join_sums term (lo:=1738438) (a:=781) (b:=782) (join_sums term (lo:=1738438) (a:=390) (b:=391) r1738438 r1738828) (join_sums term (lo:=1739219) (a:=391) (b:=391) r1739219 r1739610))))))) (join_sums term (lo:=1740001) (a:=25000) (b:=25000) (join_sums term (lo:=1740001) (a:=12500) (b:=12500) (join_sums term (lo:=1740001) (a:=6250) (b:=6250) (join_sums term (lo:=1740001) (a:=3125) (b:=3125) (join_sums term (lo:=1740001) (a:=1562) (b:=1563) (join_sums term (lo:=1740001) (a:=781) (b:=781) (join_sums term (lo:=1740001) (a:=390) (b:=391) r1740001 r1740391) (join_sums term (lo:=1740782) (a:=390) (b:=391) r1740782 r1741172)) (join_sums term (lo:=1741563) (a:=781) (b:=782) (join_sums term (lo:=1741563) (a:=390) (b:=391) r1741563 r1741953) (join_sums term (lo:=1742344) (a:=391) (b:=391) r1742344 r1742735))) (join_sums term (lo:=1743126) (a:=1562) (b:=1563) (join_sums term (lo:=1743126) (a:=781) (b:=781) (join_sums term (lo:=1743126) (a:=390) (b:=391) r1743126 r1743516) (join_sums term (lo:=1743907) (a:=390) (b:=391) r1743907 r1744297)) (join_sums term (lo:=1744688) (a:=781) (b:=782) (join_sums term (lo:=1744688) (a:=390) (b:=391) r1744688 r1745078) (join_sums term (lo:=1745469) (a:=391) (b:=391) r1745469 r1745860)))) (join_sums term (lo:=1746251) (a:=3125) (b:=3125) (join_sums term (lo:=1746251) (a:=1562) (b:=1563) (join_sums term (lo:=1746251) (a:=781) (b:=781) (join_sums term (lo:=1746251) (a:=390) (b:=391) r1746251 r1746641) (join_sums term (lo:=1747032) (a:=390) (b:=391) r1747032 r1747422)) (join_sums term (lo:=1747813) (a:=781) (b:=782) (join_sums term (lo:=1747813) (a:=390) (b:=391) r1747813 r1748203) (join_sums term (lo:=1748594) (a:=391) (b:=391) r1748594 r1748985))) (join_sums term (lo:=1749376) (a:=1562) (b:=1563) (join_sums term (lo:=1749376) (a:=781) (b:=781) (join_sums term (lo:=1749376) (a:=390) (b:=391) r1749376 r1749766) (join_sums term (lo:=1750157) (a:=390) (b:=391) r1750157 r1750547)) (join_sums term (lo:=1750938) (a:=781) (b:=782) (join_sums term (lo:=1750938) (a:=390) (b:=391) r1750938 r1751328) (join_sums term (lo:=1751719) (a:=391) (b:=391) r1751719 r1752110))))) (join_sums term (lo:=1752501) (a:=6250) (b:=6250) (join_sums term (lo:=1752501) (a:=3125) (b:=3125) (join_sums term (lo:=1752501) (a:=1562) (b:=1563) (join_sums term (lo:=1752501) (a:=781) (b:=781) (join_sums term (lo:=1752501) (a:=390) (b:=391) r1752501 r1752891) (join_sums term (lo:=1753282) (a:=390) (b:=391) r1753282 r1753672)) (join_sums term (lo:=1754063) (a:=781) (b:=782) (join_sums term (lo:=1754063) (a:=390) (b:=391) r1754063 r1754453) (join_sums term (lo:=1754844) (a:=391) (b:=391) r1754844 r1755235))) (join_sums term (lo:=1755626) (a:=1562) (b:=1563) (join_sums term (lo:=1755626) (a:=781) (b:=781) (join_sums term (lo:=1755626) (a:=390) (b:=391) r1755626 r1756016) (join_sums term (lo:=1756407) (a:=390) (b:=391) r1756407 r1756797)) (join_sums term (lo:=1757188) (a:=781) (b:=782) (join_sums term (lo:=1757188) (a:=390) (b:=391) r1757188 r1757578) (join_sums term (lo:=1757969) (a:=391) (b:=391) r1757969 r1758360)))) (join_sums term (lo:=1758751) (a:=3125) (b:=3125) (join_sums term (lo:=1758751) (a:=1562) (b:=1563) (join_sums term (lo:=1758751) (a:=781) (b:=781) (join_sums term (lo:=1758751) (a:=390) (b:=391) r1758751 r1759141) (join_sums term (lo:=1759532) (a:=390) (b:=391) r1759532 r1759922)) (join_sums term (lo:=1760313) (a:=781) (b:=782) (join_sums term (lo:=1760313) (a:=390) (b:=391) r1760313 r1760703) (join_sums term (lo:=1761094) (a:=391) (b:=391) r1761094 r1761485))) (join_sums term (lo:=1761876) (a:=1562) (b:=1563) (join_sums term (lo:=1761876) (a:=781) (b:=781) (join_sums term (lo:=1761876) (a:=390) (b:=391) r1761876 r1762266) (join_sums term (lo:=1762657) (a:=390) (b:=391) r1762657 r1763047)) (join_sums term (lo:=1763438) (a:=781) (b:=782) (join_sums term (lo:=1763438) (a:=390) (b:=391) r1763438 r1763828) (join_sums term (lo:=1764219) (a:=391) (b:=391) r1764219 r1764610)))))) (join_sums term (lo:=1765001) (a:=12500) (b:=12500) (join_sums term (lo:=1765001) (a:=6250) (b:=6250) (join_sums term (lo:=1765001) (a:=3125) (b:=3125) (join_sums term (lo:=1765001) (a:=1562) (b:=1563) (join_sums term (lo:=1765001) (a:=781) (b:=781) (join_sums term (lo:=1765001) (a:=390) (b:=391) r1765001 r1765391) (join_sums term (lo:=1765782) (a:=390) (b:=391) r1765782 r1766172)) (join_sums term (lo:=1766563) (a:=781) (b:=782) (join_sums term (lo:=1766563) (a:=390) (b:=391) r1766563 r1766953) (join_sums term (lo:=1767344) (a:=391) (b:=391) r1767344 r1767735))) (join_sums term (lo:=1768126) (a:=1562) (b:=1563) (join_sums term (lo:=1768126) (a:=781) (b:=781) (join_sums term (lo:=1768126) (a:=390) (b:=391) r1768126 r1768516) (join_sums term (lo:=1768907) (a:=390) (b:=391) r1768907 r1769297)) (join_sums term (lo:=1769688) (a:=781) (b:=782) (join_sums term (lo:=1769688) (a:=390) (b:=391) r1769688 r1770078) (join_sums term (lo:=1770469) (a:=391) (b:=391) r1770469 r1770860)))) (join_sums term (lo:=1771251) (a:=3125) (b:=3125) (join_sums term (lo:=1771251) (a:=1562) (b:=1563) (join_sums term (lo:=1771251) (a:=781) (b:=781) (join_sums term (lo:=1771251) (a:=390) (b:=391) r1771251 r1771641) (join_sums term (lo:=1772032) (a:=390) (b:=391) r1772032 r1772422)) (join_sums term (lo:=1772813) (a:=781) (b:=782) (join_sums term (lo:=1772813) (a:=390) (b:=391) r1772813 r1773203) (join_sums term (lo:=1773594) (a:=391) (b:=391) r1773594 r1773985))) (join_sums term (lo:=1774376) (a:=1562) (b:=1563) (join_sums term (lo:=1774376) (a:=781) (b:=781) (join_sums term (lo:=1774376) (a:=390) (b:=391) r1774376 r1774766) (join_sums term (lo:=1775157) (a:=390) (b:=391) r1775157 r1775547)) (join_sums term (lo:=1775938) (a:=781) (b:=782) (join_sums term (lo:=1775938) (a:=390) (b:=391) r1775938 r1776328) (join_sums term (lo:=1776719) (a:=391) (b:=391) r1776719 r1777110))))) (join_sums term (lo:=1777501) (a:=6250) (b:=6250) (join_sums term (lo:=1777501) (a:=3125) (b:=3125) (join_sums term (lo:=1777501) (a:=1562) (b:=1563) (join_sums term (lo:=1777501) (a:=781) (b:=781) (join_sums term (lo:=1777501) (a:=390) (b:=391) r1777501 r1777891) (join_sums term (lo:=1778282) (a:=390) (b:=391) r1778282 r1778672)) (join_sums term (lo:=1779063) (a:=781) (b:=782) (join_sums term (lo:=1779063) (a:=390) (b:=391) r1779063 r1779453) (join_sums term (lo:=1779844) (a:=391) (b:=391) r1779844 r1780235))) (join_sums term (lo:=1780626) (a:=1562) (b:=1563) (join_sums term (lo:=1780626) (a:=781) (b:=781) (join_sums term (lo:=1780626) (a:=390) (b:=391) r1780626 r1781016) (join_sums term (lo:=1781407) (a:=390) (b:=391) r1781407 r1781797)) (join_sums term (lo:=1782188) (a:=781) (b:=782) (join_sums term (lo:=1782188) (a:=390) (b:=391) r1782188 r1782578) (join_sums term (lo:=1782969) (a:=391) (b:=391) r1782969 r1783360)))) (join_sums term (lo:=1783751) (a:=3125) (b:=3125) (join_sums term (lo:=1783751) (a:=1562) (b:=1563) (join_sums term (lo:=1783751) (a:=781) (b:=781) (join_sums term (lo:=1783751) (a:=390) (b:=391) r1783751 r1784141) (join_sums term (lo:=1784532) (a:=390) (b:=391) r1784532 r1784922)) (join_sums term (lo:=1785313) (a:=781) (b:=782) (join_sums term (lo:=1785313) (a:=390) (b:=391) r1785313 r1785703) (join_sums term (lo:=1786094) (a:=391) (b:=391) r1786094 r1786485))) (join_sums term (lo:=1786876) (a:=1562) (b:=1563) (join_sums term (lo:=1786876) (a:=781) (b:=781) (join_sums term (lo:=1786876) (a:=390) (b:=391) r1786876 r1787266) (join_sums term (lo:=1787657) (a:=390) (b:=391) r1787657 r1788047)) (join_sums term (lo:=1788438) (a:=781) (b:=782) (join_sums term (lo:=1788438) (a:=390) (b:=391) r1788438 r1788828) (join_sums term (lo:=1789219) (a:=391) (b:=391) r1789219 r1789610))))))))

private theorem rows : blockSum term 0 1790001 6786048431 :=
  join_sums term (lo:=0) (a:=1690001) (b:=100000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 1790000).filter (1690000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=6786048431 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From1690000To1790000
