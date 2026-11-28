import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 1,790,000 through 1,890,000

The sum covers 6,979 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From1790000To1890000

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


private abbrev term := contribution 30110134441897 1790000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 1790001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 1790000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r1790001 : blockSum term 1790001 390 27435869 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1790391 : blockSum term 1790391 391 29320030 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1790782 : blockSum term 1790782 390 24584446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1791172 : blockSum term 1791172 391 26468243 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1791563 : blockSum term 1791563 390 25516549 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1791953 : blockSum term 1791953 391 33068513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1792344 : blockSum term 1792344 391 23614297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1792735 : blockSum term 1792735 391 24552011 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1793126 : blockSum term 1793126 390 27377625 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1793516 : blockSum term 1793516 391 20763673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1793907 : blockSum term 1793907 390 28306893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1794297 : blockSum term 1794297 391 25468948 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1794688 : blockSum term 1794688 390 29234990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1795078 : blockSum term 1795078 391 22627799 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1795469 : blockSum term 1795469 391 31104583 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1795860 : blockSum term 1795860 391 28269458 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1796251 : blockSum term 1796251 390 18841291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1796641 : blockSum term 1796641 391 24487277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1797032 : blockSum term 1797032 390 24480550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1797422 : blockSum term 1797422 391 17885268 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1797813 : blockSum term 1797813 390 32937830 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1798203 : blockSum term 1798203 391 26343686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1798594 : blockSum term 1798594 391 31980310 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1798985 : blockSum term 1798985 391 27270276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1799376 : blockSum term 1799376 390 25382136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1799766 : blockSum term 1799766 391 24435560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1800157 : blockSum term 1800157 390 26308521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1800547 : blockSum term 1800547 391 30058844 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1800938 : blockSum term 1800938 390 21599228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1801328 : blockSum term 1801328 391 21593648 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1801719 : blockSum term 1801719 391 28158329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1802110 : blockSum term 1802110 391 19705826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1802501 : blockSum term 1802501 390 26267431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1802891 : blockSum term 1802891 391 25322429 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1803282 : blockSum term 1803282 390 30942294 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1803672 : blockSum term 1803672 391 15936111 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1804063 : blockSum term 1804063 390 23428979 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1804453 : blockSum term 1804453 391 28107901 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1804844 : blockSum term 1804844 391 26226663 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1805235 : blockSum term 1805235 391 26219642 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1805626 : blockSum term 1805626 390 27149107 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1806016 : blockSum term 1806016 391 30885560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1806407 : blockSum term 1806407 390 24327800 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1806797 : blockSum term 1806797 391 27127770 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1807188 : blockSum term 1807188 390 27120801 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1807578 : blockSum term 1807578 391 25243444 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1807969 : blockSum term 1807969 391 24302866 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1808360 : blockSum term 1808360 391 23361411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1808751 : blockSum term 1808751 390 25223927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1809141 : blockSum term 1809141 391 33622643 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1809532 : blockSum term 1809532 390 25210042 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1809922 : blockSum term 1809922 391 27070754 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1810313 : blockSum term 1810313 390 26130207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1810703 : blockSum term 1810703 391 24257471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1811094 : blockSum term 1811094 391 21453220 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1811485 : blockSum term 1811485 391 26110750 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1811876 : blockSum term 1811876 390 23306905 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1812266 : blockSum term 1812266 391 26097037 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1812657 : blockSum term 1812657 390 25158263 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1813047 : blockSum term 1813047 391 21424852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1813438 : blockSum term 1813438 390 24213498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1813828 : blockSum term 1813828 391 27000550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1814219 : blockSum term 1814219 391 26062205 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1814610 : blockSum term 1814610 391 26055655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1815001 : blockSum term 1815001 390 27908307 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1815391 : blockSum term 1815391 391 25111320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1815782 : blockSum term 1815782 390 27894101 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1816172 : blockSum term 1816172 391 24168286 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1816563 : blockSum term 1816563 390 18586457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1816953 : blockSum term 1816953 391 26014572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1817344 : blockSum term 1817344 391 19505819 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1817735 : blockSum term 1817735 391 23215413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1818126 : blockSum term 1818126 390 25065806 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1818516 : blockSum term 1818516 391 22275852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1818907 : blockSum term 1818907 390 23197745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1819297 : blockSum term 1819297 391 22264124 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1819688 : blockSum term 1819688 390 26896491 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1820078 : blockSum term 1820078 391 26888959 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1820469 : blockSum term 1820469 391 31516546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1820860 : blockSum term 1820860 391 22241434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1821251 : blockSum term 1821251 390 22235814 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1821641 : blockSum term 1821641 391 26861116 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1822032 : blockSum term 1822032 390 20372260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1822422 : blockSum term 1822422 391 24996311 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1822813 : blockSum term 1822813 390 29616693 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1823203 : blockSum term 1823203 391 25908368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1823594 : blockSum term 1823594 391 26827405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1823985 : blockSum term 1823985 391 26819481 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1824376 : blockSum term 1824376 390 30510982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1824766 : blockSum term 1824766 391 24957155 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1825157 : blockSum term 1825157 390 27722926 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1825547 : blockSum term 1825547 391 26791516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1825938 : blockSum term 1825938 390 25860282 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1826328 : blockSum term 1826328 391 25853673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1826719 : blockSum term 1826719 391 25847140 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1827110 : blockSum term 1827110 391 25840694 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1827501 : blockSum term 1827501 390 24910516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1827891 : blockSum term 1827891 391 21214457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1828282 : blockSum term 1828282 390 33196894 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1828672 : blockSum term 1828672 391 23047418 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1829063 : blockSum term 1829063 390 19354827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1829453 : blockSum term 1829453 391 34092509 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1829844 : blockSum term 1829844 391 20266036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1830235 : blockSum term 1830235 391 30391489 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1830626 : blockSum term 1830626 390 24859232 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1831016 : blockSum term 1831016 391 24853048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1831407 : blockSum term 1831407 390 25767153 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1831797 : blockSum term 1831797 391 30360163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1832188 : blockSum term 1832188 390 25753442 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1832578 : blockSum term 1832578 391 18390473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1832969 : blockSum term 1832969 391 22982558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1833360 : blockSum term 1833360 391 28489881 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1833751 : blockSum term 1833751 390 24807446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1834141 : blockSum term 1834141 391 25719619 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1834532 : blockSum term 1834532 390 25712497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1834922 : blockSum term 1834922 391 22952035 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1835313 : blockSum term 1835313 390 21110579 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1835703 : blockSum term 1835703 391 25692592 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1836094 : blockSum term 1836094 391 19264228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1836485 : blockSum term 1836485 391 18342933 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1836876 : blockSum term 1836876 390 23839988 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1837266 : blockSum term 1837266 391 22000459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1837657 : blockSum term 1837657 390 24744051 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1838047 : blockSum term 1838047 391 24737777 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1838438 : blockSum term 1838438 390 22898871 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1838828 : blockSum term 1838828 391 18314897 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1839219 : blockSum term 1839219 391 24718375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1839610 : blockSum term 1839610 391 28373196 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1840001 : blockSum term 1840001 390 21045854 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1840391 : blockSum term 1840391 391 26528870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1840782 : blockSum term 1840782 390 22863790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1841172 : blockSum term 1841172 391 23772750 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1841563 : blockSum term 1841563 390 25594472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1841953 : blockSum term 1841953 391 24673765 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1842344 : blockSum term 1842344 391 26494873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1842735 : blockSum term 1842735 391 30141887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1843126 : blockSum term 1843126 390 25568815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1843516 : blockSum term 1843516 391 23736249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1843907 : blockSum term 1843907 390 26467986 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1844297 : blockSum term 1844297 391 25549196 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1844688 : blockSum term 1844688 390 24630174 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1845078 : blockSum term 1845078 391 24624385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1845469 : blockSum term 1845469 391 23706730 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1845860 : blockSum term 1845860 391 25523332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1846251 : blockSum term 1846251 390 26428283 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1846641 : blockSum term 1846641 391 23687959 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1847032 : blockSum term 1847032 390 27324478 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1847422 : blockSum term 1847422 391 24586152 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1847813 : blockSum term 1847813 390 22759444 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1848203 : blockSum term 1848203 391 22753548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1848594 : blockSum term 1848594 391 23657084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1848985 : blockSum term 1848985 391 30928310 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1849376 : blockSum term 1849376 390 24554501 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1849766 : blockSum term 1849766 391 20911634 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1850157 : blockSum term 1850157 390 20906366 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1850547 : blockSum term 1850547 391 17266422 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1850938 : blockSum term 1850938 390 26346675 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1851328 : blockSum term 1851328 391 29972953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1851719 : blockSum term 1851719 391 31780847 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1852110 : blockSum term 1852110 391 26325768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1852501 : blockSum term 1852501 390 20873463 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1852891 : blockSum term 1852891 391 20868142 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1853282 : blockSum term 1853282 390 28119564 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1853672 : blockSum term 1853672 391 21764927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1854063 : blockSum term 1854063 390 29918449 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1854453 : blockSum term 1854453 391 25378155 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1854844 : blockSum term 1854844 391 28996563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1855235 : blockSum term 1855235 391 27176907 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1855626 : blockSum term 1855626 390 28075408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1856016 : blockSum term 1856016 391 27163544 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1856407 : blockSum term 1856407 390 14483331 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1856797 : blockSum term 1856797 391 27149303 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1857188 : blockSum term 1857188 390 25332548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1857578 : blockSum term 1857578 391 26230487 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1857969 : blockSum term 1857969 391 25319012 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1858360 : blockSum term 1858360 391 24407946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1858751 : blockSum term 1858751 390 22594760 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1859141 : blockSum term 1859141 391 28009845 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1859532 : blockSum term 1859532 390 23486120 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1859922 : blockSum term 1859922 391 24382966 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1860313 : blockSum term 1860313 390 23474111 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1860703 : blockSum term 1860703 391 28883861 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1861094 : blockSum term 1861094 391 18950163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1861485 : blockSum term 1861485 391 26163029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1861876 : blockSum term 1861876 390 24352294 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1862266 : blockSum term 1862266 391 22542512 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1862657 : blockSum term 1862657 390 20734001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1863047 : blockSum term 1863047 391 26136546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1863438 : blockSum term 1863438 390 28833245 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1863828 : blockSum term 1863828 391 23421141 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1864219 : blockSum term 1864219 391 25215865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1864610 : blockSum term 1864610 391 23409012 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1865001 : blockSum term 1865001 390 27003357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1865391 : blockSum term 1865391 391 29696162 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1865782 : blockSum term 1865782 390 26989035 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1866172 : blockSum term 1866172 391 27881655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1866563 : blockSum term 1866563 390 21580018 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1866953 : blockSum term 1866953 391 29665156 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1867344 : blockSum term 1867344 391 18872643 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1867735 : blockSum term 1867735 391 28751465 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1868126 : blockSum term 1868126 390 22456231 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1868516 : blockSum term 1868516 391 28736786 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1868907 : blockSum term 1868907 390 22444120 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1869297 : blockSum term 1869297 391 19746571 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1869688 : blockSum term 1869688 390 19741669 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1870078 : blockSum term 1870078 391 26913473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1870469 : blockSum term 1870469 391 25112280 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1870860 : blockSum term 1870860 391 22416296 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1871251 : blockSum term 1871251 390 25996150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1871641 : blockSum term 1871641 391 25093474 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1872032 : blockSum term 1872032 390 22398990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1872422 : blockSum term 1872422 391 24185388 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1872813 : blockSum term 1872813 390 24178830 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1873203 : blockSum term 1873203 391 25067650 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1873594 : blockSum term 1873594 391 18796068 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1873985 : blockSum term 1873985 391 18791160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1874376 : blockSum term 1874376 390 24153603 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1874766 : blockSum term 1874766 391 29513410 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1875157 : blockSum term 1875157 390 26823686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1875547 : blockSum term 1875547 391 18772213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1875938 : blockSum term 1875938 390 31279129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1876328 : blockSum term 1876328 391 26803587 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1876719 : blockSum term 1876719 391 20543750 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1877110 : blockSum term 1877110 391 27683166 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1877501 : blockSum term 1877501 390 20533900 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1877891 : blockSum term 1877891 391 26776504 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1878282 : blockSum term 1878282 390 24985108 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1878672 : blockSum term 1878672 391 22302432 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1879063 : blockSum term 1879063 390 21404875 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1879453 : blockSum term 1879453 391 20508038 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1879844 : blockSum term 1879844 391 23177031 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1880235 : blockSum term 1880235 391 24953258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1880626 : blockSum term 1880626 390 30292382 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1881016 : blockSum term 1881016 391 28503217 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1881407 : blockSum term 1881407 390 21372127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1881797 : blockSum term 1881797 391 28488950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1882188 : blockSum term 1882188 390 22251279 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1882578 : blockSum term 1882578 391 16016969 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1882969 : blockSum term 1882969 391 25798394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1883360 : blockSum term 1883360 391 29349511 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1883751 : blockSum term 1883751 390 18671558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1884141 : blockSum term 1884141 391 23111393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1884532 : blockSum term 1884532 390 26660565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1884922 : blockSum term 1884922 391 21322885 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1885313 : blockSum term 1885313 390 26647366 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1885703 : blockSum term 1885703 391 24864660 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1886094 : blockSum term 1886094 391 23082356 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1886485 : blockSum term 1886485 391 23964048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1886876 : blockSum term 1886876 390 28394249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1887266 : blockSum term 1887266 391 21290120 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1887657 : blockSum term 1887657 390 19511451 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1888047 : blockSum term 1888047 391 27486525 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1888438 : blockSum term 1888438 390 18615301 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1888828 : blockSum term 1888828 391 26586719 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1889219 : blockSum term 1889219 391 31895629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1889610 : blockSum term 1889610 391 18601438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 1790001 100000 6388951563 := (join_sums term (lo:=1790001) (a:=50000) (b:=50000) (join_sums term (lo:=1790001) (a:=25000) (b:=25000) (join_sums term (lo:=1790001) (a:=12500) (b:=12500) (join_sums term (lo:=1790001) (a:=6250) (b:=6250) (join_sums term (lo:=1790001) (a:=3125) (b:=3125) (join_sums term (lo:=1790001) (a:=1562) (b:=1563) (join_sums term (lo:=1790001) (a:=781) (b:=781) (join_sums term (lo:=1790001) (a:=390) (b:=391) r1790001 r1790391) (join_sums term (lo:=1790782) (a:=390) (b:=391) r1790782 r1791172)) (join_sums term (lo:=1791563) (a:=781) (b:=782) (join_sums term (lo:=1791563) (a:=390) (b:=391) r1791563 r1791953) (join_sums term (lo:=1792344) (a:=391) (b:=391) r1792344 r1792735))) (join_sums term (lo:=1793126) (a:=1562) (b:=1563) (join_sums term (lo:=1793126) (a:=781) (b:=781) (join_sums term (lo:=1793126) (a:=390) (b:=391) r1793126 r1793516) (join_sums term (lo:=1793907) (a:=390) (b:=391) r1793907 r1794297)) (join_sums term (lo:=1794688) (a:=781) (b:=782) (join_sums term (lo:=1794688) (a:=390) (b:=391) r1794688 r1795078) (join_sums term (lo:=1795469) (a:=391) (b:=391) r1795469 r1795860)))) (join_sums term (lo:=1796251) (a:=3125) (b:=3125) (join_sums term (lo:=1796251) (a:=1562) (b:=1563) (join_sums term (lo:=1796251) (a:=781) (b:=781) (join_sums term (lo:=1796251) (a:=390) (b:=391) r1796251 r1796641) (join_sums term (lo:=1797032) (a:=390) (b:=391) r1797032 r1797422)) (join_sums term (lo:=1797813) (a:=781) (b:=782) (join_sums term (lo:=1797813) (a:=390) (b:=391) r1797813 r1798203) (join_sums term (lo:=1798594) (a:=391) (b:=391) r1798594 r1798985))) (join_sums term (lo:=1799376) (a:=1562) (b:=1563) (join_sums term (lo:=1799376) (a:=781) (b:=781) (join_sums term (lo:=1799376) (a:=390) (b:=391) r1799376 r1799766) (join_sums term (lo:=1800157) (a:=390) (b:=391) r1800157 r1800547)) (join_sums term (lo:=1800938) (a:=781) (b:=782) (join_sums term (lo:=1800938) (a:=390) (b:=391) r1800938 r1801328) (join_sums term (lo:=1801719) (a:=391) (b:=391) r1801719 r1802110))))) (join_sums term (lo:=1802501) (a:=6250) (b:=6250) (join_sums term (lo:=1802501) (a:=3125) (b:=3125) (join_sums term (lo:=1802501) (a:=1562) (b:=1563) (join_sums term (lo:=1802501) (a:=781) (b:=781) (join_sums term (lo:=1802501) (a:=390) (b:=391) r1802501 r1802891) (join_sums term (lo:=1803282) (a:=390) (b:=391) r1803282 r1803672)) (join_sums term (lo:=1804063) (a:=781) (b:=782) (join_sums term (lo:=1804063) (a:=390) (b:=391) r1804063 r1804453) (join_sums term (lo:=1804844) (a:=391) (b:=391) r1804844 r1805235))) (join_sums term (lo:=1805626) (a:=1562) (b:=1563) (join_sums term (lo:=1805626) (a:=781) (b:=781) (join_sums term (lo:=1805626) (a:=390) (b:=391) r1805626 r1806016) (join_sums term (lo:=1806407) (a:=390) (b:=391) r1806407 r1806797)) (join_sums term (lo:=1807188) (a:=781) (b:=782) (join_sums term (lo:=1807188) (a:=390) (b:=391) r1807188 r1807578) (join_sums term (lo:=1807969) (a:=391) (b:=391) r1807969 r1808360)))) (join_sums term (lo:=1808751) (a:=3125) (b:=3125) (join_sums term (lo:=1808751) (a:=1562) (b:=1563) (join_sums term (lo:=1808751) (a:=781) (b:=781) (join_sums term (lo:=1808751) (a:=390) (b:=391) r1808751 r1809141) (join_sums term (lo:=1809532) (a:=390) (b:=391) r1809532 r1809922)) (join_sums term (lo:=1810313) (a:=781) (b:=782) (join_sums term (lo:=1810313) (a:=390) (b:=391) r1810313 r1810703) (join_sums term (lo:=1811094) (a:=391) (b:=391) r1811094 r1811485))) (join_sums term (lo:=1811876) (a:=1562) (b:=1563) (join_sums term (lo:=1811876) (a:=781) (b:=781) (join_sums term (lo:=1811876) (a:=390) (b:=391) r1811876 r1812266) (join_sums term (lo:=1812657) (a:=390) (b:=391) r1812657 r1813047)) (join_sums term (lo:=1813438) (a:=781) (b:=782) (join_sums term (lo:=1813438) (a:=390) (b:=391) r1813438 r1813828) (join_sums term (lo:=1814219) (a:=391) (b:=391) r1814219 r1814610)))))) (join_sums term (lo:=1815001) (a:=12500) (b:=12500) (join_sums term (lo:=1815001) (a:=6250) (b:=6250) (join_sums term (lo:=1815001) (a:=3125) (b:=3125) (join_sums term (lo:=1815001) (a:=1562) (b:=1563) (join_sums term (lo:=1815001) (a:=781) (b:=781) (join_sums term (lo:=1815001) (a:=390) (b:=391) r1815001 r1815391) (join_sums term (lo:=1815782) (a:=390) (b:=391) r1815782 r1816172)) (join_sums term (lo:=1816563) (a:=781) (b:=782) (join_sums term (lo:=1816563) (a:=390) (b:=391) r1816563 r1816953) (join_sums term (lo:=1817344) (a:=391) (b:=391) r1817344 r1817735))) (join_sums term (lo:=1818126) (a:=1562) (b:=1563) (join_sums term (lo:=1818126) (a:=781) (b:=781) (join_sums term (lo:=1818126) (a:=390) (b:=391) r1818126 r1818516) (join_sums term (lo:=1818907) (a:=390) (b:=391) r1818907 r1819297)) (join_sums term (lo:=1819688) (a:=781) (b:=782) (join_sums term (lo:=1819688) (a:=390) (b:=391) r1819688 r1820078) (join_sums term (lo:=1820469) (a:=391) (b:=391) r1820469 r1820860)))) (join_sums term (lo:=1821251) (a:=3125) (b:=3125) (join_sums term (lo:=1821251) (a:=1562) (b:=1563) (join_sums term (lo:=1821251) (a:=781) (b:=781) (join_sums term (lo:=1821251) (a:=390) (b:=391) r1821251 r1821641) (join_sums term (lo:=1822032) (a:=390) (b:=391) r1822032 r1822422)) (join_sums term (lo:=1822813) (a:=781) (b:=782) (join_sums term (lo:=1822813) (a:=390) (b:=391) r1822813 r1823203) (join_sums term (lo:=1823594) (a:=391) (b:=391) r1823594 r1823985))) (join_sums term (lo:=1824376) (a:=1562) (b:=1563) (join_sums term (lo:=1824376) (a:=781) (b:=781) (join_sums term (lo:=1824376) (a:=390) (b:=391) r1824376 r1824766) (join_sums term (lo:=1825157) (a:=390) (b:=391) r1825157 r1825547)) (join_sums term (lo:=1825938) (a:=781) (b:=782) (join_sums term (lo:=1825938) (a:=390) (b:=391) r1825938 r1826328) (join_sums term (lo:=1826719) (a:=391) (b:=391) r1826719 r1827110))))) (join_sums term (lo:=1827501) (a:=6250) (b:=6250) (join_sums term (lo:=1827501) (a:=3125) (b:=3125) (join_sums term (lo:=1827501) (a:=1562) (b:=1563) (join_sums term (lo:=1827501) (a:=781) (b:=781) (join_sums term (lo:=1827501) (a:=390) (b:=391) r1827501 r1827891) (join_sums term (lo:=1828282) (a:=390) (b:=391) r1828282 r1828672)) (join_sums term (lo:=1829063) (a:=781) (b:=782) (join_sums term (lo:=1829063) (a:=390) (b:=391) r1829063 r1829453) (join_sums term (lo:=1829844) (a:=391) (b:=391) r1829844 r1830235))) (join_sums term (lo:=1830626) (a:=1562) (b:=1563) (join_sums term (lo:=1830626) (a:=781) (b:=781) (join_sums term (lo:=1830626) (a:=390) (b:=391) r1830626 r1831016) (join_sums term (lo:=1831407) (a:=390) (b:=391) r1831407 r1831797)) (join_sums term (lo:=1832188) (a:=781) (b:=782) (join_sums term (lo:=1832188) (a:=390) (b:=391) r1832188 r1832578) (join_sums term (lo:=1832969) (a:=391) (b:=391) r1832969 r1833360)))) (join_sums term (lo:=1833751) (a:=3125) (b:=3125) (join_sums term (lo:=1833751) (a:=1562) (b:=1563) (join_sums term (lo:=1833751) (a:=781) (b:=781) (join_sums term (lo:=1833751) (a:=390) (b:=391) r1833751 r1834141) (join_sums term (lo:=1834532) (a:=390) (b:=391) r1834532 r1834922)) (join_sums term (lo:=1835313) (a:=781) (b:=782) (join_sums term (lo:=1835313) (a:=390) (b:=391) r1835313 r1835703) (join_sums term (lo:=1836094) (a:=391) (b:=391) r1836094 r1836485))) (join_sums term (lo:=1836876) (a:=1562) (b:=1563) (join_sums term (lo:=1836876) (a:=781) (b:=781) (join_sums term (lo:=1836876) (a:=390) (b:=391) r1836876 r1837266) (join_sums term (lo:=1837657) (a:=390) (b:=391) r1837657 r1838047)) (join_sums term (lo:=1838438) (a:=781) (b:=782) (join_sums term (lo:=1838438) (a:=390) (b:=391) r1838438 r1838828) (join_sums term (lo:=1839219) (a:=391) (b:=391) r1839219 r1839610))))))) (join_sums term (lo:=1840001) (a:=25000) (b:=25000) (join_sums term (lo:=1840001) (a:=12500) (b:=12500) (join_sums term (lo:=1840001) (a:=6250) (b:=6250) (join_sums term (lo:=1840001) (a:=3125) (b:=3125) (join_sums term (lo:=1840001) (a:=1562) (b:=1563) (join_sums term (lo:=1840001) (a:=781) (b:=781) (join_sums term (lo:=1840001) (a:=390) (b:=391) r1840001 r1840391) (join_sums term (lo:=1840782) (a:=390) (b:=391) r1840782 r1841172)) (join_sums term (lo:=1841563) (a:=781) (b:=782) (join_sums term (lo:=1841563) (a:=390) (b:=391) r1841563 r1841953) (join_sums term (lo:=1842344) (a:=391) (b:=391) r1842344 r1842735))) (join_sums term (lo:=1843126) (a:=1562) (b:=1563) (join_sums term (lo:=1843126) (a:=781) (b:=781) (join_sums term (lo:=1843126) (a:=390) (b:=391) r1843126 r1843516) (join_sums term (lo:=1843907) (a:=390) (b:=391) r1843907 r1844297)) (join_sums term (lo:=1844688) (a:=781) (b:=782) (join_sums term (lo:=1844688) (a:=390) (b:=391) r1844688 r1845078) (join_sums term (lo:=1845469) (a:=391) (b:=391) r1845469 r1845860)))) (join_sums term (lo:=1846251) (a:=3125) (b:=3125) (join_sums term (lo:=1846251) (a:=1562) (b:=1563) (join_sums term (lo:=1846251) (a:=781) (b:=781) (join_sums term (lo:=1846251) (a:=390) (b:=391) r1846251 r1846641) (join_sums term (lo:=1847032) (a:=390) (b:=391) r1847032 r1847422)) (join_sums term (lo:=1847813) (a:=781) (b:=782) (join_sums term (lo:=1847813) (a:=390) (b:=391) r1847813 r1848203) (join_sums term (lo:=1848594) (a:=391) (b:=391) r1848594 r1848985))) (join_sums term (lo:=1849376) (a:=1562) (b:=1563) (join_sums term (lo:=1849376) (a:=781) (b:=781) (join_sums term (lo:=1849376) (a:=390) (b:=391) r1849376 r1849766) (join_sums term (lo:=1850157) (a:=390) (b:=391) r1850157 r1850547)) (join_sums term (lo:=1850938) (a:=781) (b:=782) (join_sums term (lo:=1850938) (a:=390) (b:=391) r1850938 r1851328) (join_sums term (lo:=1851719) (a:=391) (b:=391) r1851719 r1852110))))) (join_sums term (lo:=1852501) (a:=6250) (b:=6250) (join_sums term (lo:=1852501) (a:=3125) (b:=3125) (join_sums term (lo:=1852501) (a:=1562) (b:=1563) (join_sums term (lo:=1852501) (a:=781) (b:=781) (join_sums term (lo:=1852501) (a:=390) (b:=391) r1852501 r1852891) (join_sums term (lo:=1853282) (a:=390) (b:=391) r1853282 r1853672)) (join_sums term (lo:=1854063) (a:=781) (b:=782) (join_sums term (lo:=1854063) (a:=390) (b:=391) r1854063 r1854453) (join_sums term (lo:=1854844) (a:=391) (b:=391) r1854844 r1855235))) (join_sums term (lo:=1855626) (a:=1562) (b:=1563) (join_sums term (lo:=1855626) (a:=781) (b:=781) (join_sums term (lo:=1855626) (a:=390) (b:=391) r1855626 r1856016) (join_sums term (lo:=1856407) (a:=390) (b:=391) r1856407 r1856797)) (join_sums term (lo:=1857188) (a:=781) (b:=782) (join_sums term (lo:=1857188) (a:=390) (b:=391) r1857188 r1857578) (join_sums term (lo:=1857969) (a:=391) (b:=391) r1857969 r1858360)))) (join_sums term (lo:=1858751) (a:=3125) (b:=3125) (join_sums term (lo:=1858751) (a:=1562) (b:=1563) (join_sums term (lo:=1858751) (a:=781) (b:=781) (join_sums term (lo:=1858751) (a:=390) (b:=391) r1858751 r1859141) (join_sums term (lo:=1859532) (a:=390) (b:=391) r1859532 r1859922)) (join_sums term (lo:=1860313) (a:=781) (b:=782) (join_sums term (lo:=1860313) (a:=390) (b:=391) r1860313 r1860703) (join_sums term (lo:=1861094) (a:=391) (b:=391) r1861094 r1861485))) (join_sums term (lo:=1861876) (a:=1562) (b:=1563) (join_sums term (lo:=1861876) (a:=781) (b:=781) (join_sums term (lo:=1861876) (a:=390) (b:=391) r1861876 r1862266) (join_sums term (lo:=1862657) (a:=390) (b:=391) r1862657 r1863047)) (join_sums term (lo:=1863438) (a:=781) (b:=782) (join_sums term (lo:=1863438) (a:=390) (b:=391) r1863438 r1863828) (join_sums term (lo:=1864219) (a:=391) (b:=391) r1864219 r1864610)))))) (join_sums term (lo:=1865001) (a:=12500) (b:=12500) (join_sums term (lo:=1865001) (a:=6250) (b:=6250) (join_sums term (lo:=1865001) (a:=3125) (b:=3125) (join_sums term (lo:=1865001) (a:=1562) (b:=1563) (join_sums term (lo:=1865001) (a:=781) (b:=781) (join_sums term (lo:=1865001) (a:=390) (b:=391) r1865001 r1865391) (join_sums term (lo:=1865782) (a:=390) (b:=391) r1865782 r1866172)) (join_sums term (lo:=1866563) (a:=781) (b:=782) (join_sums term (lo:=1866563) (a:=390) (b:=391) r1866563 r1866953) (join_sums term (lo:=1867344) (a:=391) (b:=391) r1867344 r1867735))) (join_sums term (lo:=1868126) (a:=1562) (b:=1563) (join_sums term (lo:=1868126) (a:=781) (b:=781) (join_sums term (lo:=1868126) (a:=390) (b:=391) r1868126 r1868516) (join_sums term (lo:=1868907) (a:=390) (b:=391) r1868907 r1869297)) (join_sums term (lo:=1869688) (a:=781) (b:=782) (join_sums term (lo:=1869688) (a:=390) (b:=391) r1869688 r1870078) (join_sums term (lo:=1870469) (a:=391) (b:=391) r1870469 r1870860)))) (join_sums term (lo:=1871251) (a:=3125) (b:=3125) (join_sums term (lo:=1871251) (a:=1562) (b:=1563) (join_sums term (lo:=1871251) (a:=781) (b:=781) (join_sums term (lo:=1871251) (a:=390) (b:=391) r1871251 r1871641) (join_sums term (lo:=1872032) (a:=390) (b:=391) r1872032 r1872422)) (join_sums term (lo:=1872813) (a:=781) (b:=782) (join_sums term (lo:=1872813) (a:=390) (b:=391) r1872813 r1873203) (join_sums term (lo:=1873594) (a:=391) (b:=391) r1873594 r1873985))) (join_sums term (lo:=1874376) (a:=1562) (b:=1563) (join_sums term (lo:=1874376) (a:=781) (b:=781) (join_sums term (lo:=1874376) (a:=390) (b:=391) r1874376 r1874766) (join_sums term (lo:=1875157) (a:=390) (b:=391) r1875157 r1875547)) (join_sums term (lo:=1875938) (a:=781) (b:=782) (join_sums term (lo:=1875938) (a:=390) (b:=391) r1875938 r1876328) (join_sums term (lo:=1876719) (a:=391) (b:=391) r1876719 r1877110))))) (join_sums term (lo:=1877501) (a:=6250) (b:=6250) (join_sums term (lo:=1877501) (a:=3125) (b:=3125) (join_sums term (lo:=1877501) (a:=1562) (b:=1563) (join_sums term (lo:=1877501) (a:=781) (b:=781) (join_sums term (lo:=1877501) (a:=390) (b:=391) r1877501 r1877891) (join_sums term (lo:=1878282) (a:=390) (b:=391) r1878282 r1878672)) (join_sums term (lo:=1879063) (a:=781) (b:=782) (join_sums term (lo:=1879063) (a:=390) (b:=391) r1879063 r1879453) (join_sums term (lo:=1879844) (a:=391) (b:=391) r1879844 r1880235))) (join_sums term (lo:=1880626) (a:=1562) (b:=1563) (join_sums term (lo:=1880626) (a:=781) (b:=781) (join_sums term (lo:=1880626) (a:=390) (b:=391) r1880626 r1881016) (join_sums term (lo:=1881407) (a:=390) (b:=391) r1881407 r1881797)) (join_sums term (lo:=1882188) (a:=781) (b:=782) (join_sums term (lo:=1882188) (a:=390) (b:=391) r1882188 r1882578) (join_sums term (lo:=1882969) (a:=391) (b:=391) r1882969 r1883360)))) (join_sums term (lo:=1883751) (a:=3125) (b:=3125) (join_sums term (lo:=1883751) (a:=1562) (b:=1563) (join_sums term (lo:=1883751) (a:=781) (b:=781) (join_sums term (lo:=1883751) (a:=390) (b:=391) r1883751 r1884141) (join_sums term (lo:=1884532) (a:=390) (b:=391) r1884532 r1884922)) (join_sums term (lo:=1885313) (a:=781) (b:=782) (join_sums term (lo:=1885313) (a:=390) (b:=391) r1885313 r1885703) (join_sums term (lo:=1886094) (a:=391) (b:=391) r1886094 r1886485))) (join_sums term (lo:=1886876) (a:=1562) (b:=1563) (join_sums term (lo:=1886876) (a:=781) (b:=781) (join_sums term (lo:=1886876) (a:=390) (b:=391) r1886876 r1887266) (join_sums term (lo:=1887657) (a:=390) (b:=391) r1887657 r1888047)) (join_sums term (lo:=1888438) (a:=781) (b:=782) (join_sums term (lo:=1888438) (a:=390) (b:=391) r1888438 r1888828) (join_sums term (lo:=1889219) (a:=391) (b:=391) r1889219 r1889610))))))))

private theorem rows : blockSum term 0 1890001 6388951563 :=
  join_sums term (lo:=0) (a:=1790001) (b:=100000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 1890000).filter (1790000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=6388951563 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From1790000To1890000
