import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 1,890,000 through 1,990,000

The sum covers 6,881 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From1890000To1990000

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


private abbrev term := contribution 30110134441897 1890000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 1890001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 1890000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r1890001 : blockSum term 1890001 390 28336940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1890391 : blockSum term 1890391 391 25673768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1890782 : blockSum term 1890782 390 21241663 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1891172 : blockSum term 1891172 391 25660403 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1891563 : blockSum term 1891563 390 23884406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1891953 : blockSum term 1891953 391 22109764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1892344 : blockSum term 1892344 391 28293213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1892735 : blockSum term 1892735 391 22099211 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1893126 : blockSum term 1893126 390 28279132 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1893516 : blockSum term 1893516 391 21204082 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1893907 : blockSum term 1893907 390 28264818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1894297 : blockSum term 1894297 391 18543969 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1894688 : blockSum term 1894688 390 21188163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1895078 : blockSum term 1895078 391 21183516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1895469 : blockSum term 1895469 391 26472126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1895860 : blockSum term 1895860 391 29110993 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1896251 : blockSum term 1896251 390 22048336 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1896641 : blockSum term 1896641 391 22042756 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1897032 : blockSum term 1897032 390 23800498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1897422 : blockSum term 1897422 391 24674790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1897813 : blockSum term 1897813 390 22906621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1898203 : blockSum term 1898203 391 25542839 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1898594 : blockSum term 1898594 391 22894884 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1898985 : blockSum term 1898985 391 23769178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1899376 : blockSum term 1899376 390 20242513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1899766 : blockSum term 1899766 391 18477354 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1900157 : blockSum term 1900157 390 29028323 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1900547 : blockSum term 1900547 391 22865060 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1900938 : blockSum term 1900938 390 14946408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1901328 : blockSum term 1901328 391 22854038 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1901719 : blockSum term 1901719 391 24605214 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1902110 : blockSum term 1902110 391 28112979 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1902501 : blockSum term 1902501 390 20200597 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1902891 : blockSum term 1902891 391 21951868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1903282 : blockSum term 1903282 390 22824173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1903672 : blockSum term 1903672 391 24573680 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1904063 : blockSum term 1904063 390 19303665 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1904453 : blockSum term 1904453 391 26316495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1904844 : blockSum term 1904844 391 23678376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1905235 : blockSum term 1905235 391 21042062 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1905626 : blockSum term 1905626 390 23666971 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1906016 : blockSum term 1906016 391 22784064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1906407 : blockSum term 1906407 390 25406664 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1906797 : blockSum term 1906797 391 19269663 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1907188 : blockSum term 1907188 390 25394541 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1907578 : blockSum term 1907578 391 27138782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1907969 : blockSum term 1907969 391 28882373 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1908360 : blockSum term 1908360 391 22749529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1908751 : blockSum term 1908751 390 26242954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1909141 : blockSum term 1909141 391 27111081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1909532 : blockSum term 1909532 390 19235341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1909922 : blockSum term 1909922 391 26223581 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1910313 : blockSum term 1910313 390 21847112 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1910703 : blockSum term 1910703 391 27956882 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1911094 : blockSum term 1911094 391 23583272 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1911485 : blockSum term 1911485 391 20084315 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1911876 : blockSum term 1911876 390 23571545 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1912266 : blockSum term 1912266 391 27928937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1912657 : blockSum term 1912657 390 24432020 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1913047 : blockSum term 1913047 391 21808513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1913438 : blockSum term 1913438 390 22675119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1913828 : blockSum term 1913828 391 27029038 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1914219 : blockSum term 1914219 391 22663208 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1914610 : blockSum term 1914610 391 24401047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1915001 : blockSum term 1915001 390 21781189 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1915391 : blockSum term 1915391 391 28744001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1915782 : blockSum term 1915782 390 23512193 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1916172 : blockSum term 1916172 391 22635378 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1916563 : blockSum term 1916563 390 26110493 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1916953 : blockSum term 1916953 391 26103503 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1917344 : blockSum term 1917344 391 26096977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1917735 : blockSum term 1917735 391 23481438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1918126 : blockSum term 1918126 390 21736497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1918516 : blockSum term 1918516 391 21731543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1918907 : blockSum term 1918907 390 17380820 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1919297 : blockSum term 1919297 391 22589547 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1919688 : blockSum term 1919688 390 20846489 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1920078 : blockSum term 1920078 391 24314659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1920469 : blockSum term 1920469 391 26913249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1920860 : blockSum term 1920860 391 23434712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1921251 : blockSum term 1921251 390 19958069 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1921641 : blockSum term 1921641 391 26893406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1922032 : blockSum term 1922032 390 15610927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1922422 : blockSum term 1922422 391 24277809 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1922813 : blockSum term 1922813 390 26871815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1923203 : blockSum term 1923203 391 21665865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1923594 : blockSum term 1923594 391 24259169 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1923985 : blockSum term 1923985 391 21654641 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1924376 : blockSum term 1924376 390 23380951 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1924766 : blockSum term 1924766 391 21643612 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1925157 : blockSum term 1925157 390 25100616 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1925547 : blockSum term 1925547 391 25959179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1925938 : blockSum term 1925938 390 22492324 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1926328 : blockSum term 1926328 391 29405930 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1926719 : blockSum term 1926719 391 25074574 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1927110 : blockSum term 1927110 391 25068369 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1927501 : blockSum term 1927501 390 25926717 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1927891 : blockSum term 1927891 391 24192063 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1928282 : blockSum term 1928282 390 25913237 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1928672 : blockSum term 1928672 391 21588665 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1929063 : blockSum term 1929063 390 20720187 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1929453 : blockSum term 1929453 391 28482817 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1929844 : blockSum term 1929844 391 22435381 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1930235 : blockSum term 1930235 391 25880791 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1930626 : blockSum term 1930626 390 19836796 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1931016 : blockSum term 1931016 391 24142615 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1931407 : blockSum term 1931407 390 24136262 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1931797 : blockSum term 1931797 391 24130157 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1932188 : blockSum term 1932188 390 23262778 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1932578 : blockSum term 1932578 391 21533526 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1932969 : blockSum term 1932969 391 18945146 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1933360 : blockSum term 1933360 391 20662385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1933751 : blockSum term 1933751 390 24100179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1934141 : blockSum term 1934141 391 24093773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1934532 : blockSum term 1934532 390 23227892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1934922 : blockSum term 1934922 391 22361644 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1935313 : blockSum term 1935313 390 19776751 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1935703 : blockSum term 1935703 391 22350684 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1936094 : blockSum term 1936094 391 24922776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1936485 : blockSum term 1936485 391 24916110 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1936876 : blockSum term 1936876 390 20614972 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1937266 : blockSum term 1937266 391 20610039 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1937657 : blockSum term 1937657 390 22322177 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1938047 : blockSum term 1938047 391 24033321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1938438 : blockSum term 1938438 390 21452457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1938828 : blockSum term 1938828 391 24879037 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1939219 : blockSum term 1939219 391 29160829 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1939610 : blockSum term 1939610 391 25723434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1940001 : blockSum term 1940001 390 20573491 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1940391 : blockSum term 1940391 391 27424262 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1940782 : blockSum term 1940782 390 19705777 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1941172 : blockSum term 1941172 391 28266151 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1941563 : blockSum term 1941563 390 17983194 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1941953 : blockSum term 1941953 391 25684029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1942344 : blockSum term 1942344 391 22253897 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1942735 : blockSum term 1942735 391 22247934 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1943126 : blockSum term 1943126 390 26519434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1943516 : blockSum term 1943516 391 23946963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1943907 : blockSum term 1943907 390 21375948 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1944297 : blockSum term 1944297 391 20515892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1944688 : blockSum term 1944688 390 26492888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1945078 : blockSum term 1945078 391 22214109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1945469 : blockSum term 1945469 391 29041976 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1945860 : blockSum term 1945860 391 21349010 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1946251 : blockSum term 1946251 390 23904288 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1946641 : blockSum term 1946641 391 26459854 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1947032 : blockSum term 1947032 390 23039173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1947422 : blockSum term 1947422 391 23886371 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1947813 : blockSum term 1947813 390 23027313 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1948203 : blockSum term 1948203 391 21316520 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1948594 : blockSum term 1948594 391 24720913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1948985 : blockSum term 1948985 391 17896724 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1949376 : blockSum term 1949376 390 17040629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1949766 : blockSum term 1949766 391 24702839 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1950157 : blockSum term 1950157 390 24696703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1950547 : blockSum term 1950547 391 18730790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1950938 : blockSum term 1950938 390 23833429 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1951328 : blockSum term 1951328 391 21274070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1951719 : blockSum term 1951719 391 22120007 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1952110 : blockSum term 1952110 391 22114673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1952501 : blockSum term 1952501 390 22109301 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1952891 : blockSum term 1952891 391 21253527 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1953282 : blockSum term 1953282 390 28047254 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1953672 : blockSum term 1953672 391 21242652 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1954063 : blockSum term 1954063 390 31430313 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1954453 : blockSum term 1954453 391 23779557 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1954844 : blockSum term 1954844 391 22075469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1955235 : blockSum term 1955235 391 22918929 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1955626 : blockSum term 1955626 390 22913473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1956016 : blockSum term 1956016 391 20362583 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1956407 : blockSum term 1956407 390 22902296 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1956797 : blockSum term 1956797 391 23744302 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1957188 : blockSum term 1957188 390 16956060 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1957578 : blockSum term 1957578 391 23733034 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1957969 : blockSum term 1957969 391 17795342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1958360 : blockSum term 1958360 391 22874316 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1958751 : blockSum term 1958751 390 21174912 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1959141 : blockSum term 1959141 391 23710724 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1959532 : blockSum term 1959532 390 23704591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1959922 : blockSum term 1959922 391 26237645 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1960313 : blockSum term 1960313 390 16923263 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1960703 : blockSum term 1960703 391 27916110 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1961094 : blockSum term 1961094 391 21988726 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1961485 : blockSum term 1961485 391 24520182 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1961876 : blockSum term 1961876 390 23668943 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1962266 : blockSum term 1962266 391 23662633 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1962657 : blockSum term 1962657 390 22811199 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1963047 : blockSum term 1963047 391 25340043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1963438 : blockSum term 1963438 390 21111029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1963828 : blockSum term 1963828 391 21105751 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1964219 : blockSum term 1964219 391 19412723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1964610 : blockSum term 1964610 391 23627115 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1965001 : blockSum term 1965001 390 15185055 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1965391 : blockSum term 1965391 391 28676542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1965782 : blockSum term 1965782 390 19393588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1966172 : blockSum term 1966172 391 21074513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1966563 : blockSum term 1966563 390 25283191 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1966953 : blockSum term 1966953 391 21064408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1967344 : blockSum term 1967344 391 21059101 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1967735 : blockSum term 1967735 391 20211748 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1968126 : blockSum term 1968126 390 23574817 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1968516 : blockSum term 1968516 391 21885283 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1968907 : blockSum term 1968907 390 21879499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1969297 : blockSum term 1969297 391 18508950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1969688 : blockSum term 1969688 390 19345634 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1970078 : blockSum term 1970078 391 25226946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1970469 : blockSum term 1970469 391 20176937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1970860 : blockSum term 1970860 391 20171533 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1971251 : blockSum term 1971251 390 21847045 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1971641 : blockSum term 1971641 391 16801298 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1972032 : blockSum term 1972032 390 25195829 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1972422 : blockSum term 1972422 391 21830528 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1972813 : blockSum term 1972813 390 22664644 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1973203 : blockSum term 1973203 391 26015584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1973594 : blockSum term 1973594 391 21814058 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1973985 : blockSum term 1973985 391 16775678 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1974376 : blockSum term 1974376 390 17610403 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1974766 : blockSum term 1974766 391 24312879 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1975157 : blockSum term 1975157 390 21792242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1975547 : blockSum term 1975547 391 18435044 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1975938 : blockSum term 1975938 390 20106154 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1976328 : blockSum term 1976328 391 25126097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1976719 : blockSum term 1976719 391 27632074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1977110 : blockSum term 1977110 391 17579248 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1977501 : blockSum term 1977501 390 26780847 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1977891 : blockSum term 1977891 391 20917333 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1978282 : blockSum term 1978282 390 22585258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1978672 : blockSum term 1978672 391 20906954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1979063 : blockSum term 1979063 390 30934364 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1979453 : blockSum term 1979453 391 19224703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1979844 : blockSum term 1979844 391 21726594 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1980235 : blockSum term 1980235 391 24228081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1980626 : blockSum term 1980626 390 26727550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1981016 : blockSum term 1981016 391 16700354 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1981407 : blockSum term 1981407 390 26714573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1981797 : blockSum term 1981797 391 23369301 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1982188 : blockSum term 1982188 390 21694584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1982578 : blockSum term 1982578 391 28362947 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1982969 : blockSum term 1982969 391 20016148 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1983360 : blockSum term 1983360 391 24180368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1983751 : blockSum term 1983751 390 24173883 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1984141 : blockSum term 1984141 391 22501827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1984532 : blockSum term 1984532 390 23328826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1984922 : blockSum term 1984922 391 19158167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1985313 : blockSum term 1985313 390 19986222 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1985703 : blockSum term 1985703 391 19981121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1986094 : blockSum term 1986094 391 21640869 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1986485 : blockSum term 1986485 391 21635408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1986876 : blockSum term 1986876 390 25789731 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1987266 : blockSum term 1987266 391 22456268 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1987657 : blockSum term 1987657 390 22450659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1988047 : blockSum term 1988047 391 24938876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1988438 : blockSum term 1988438 390 22439572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1988828 : blockSum term 1988828 391 21603409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1989219 : blockSum term 1989219 391 16613902 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1989610 : blockSum term 1989610 391 19101030 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 1890001 100000 5901940495 := (join_sums term (lo:=1890001) (a:=50000) (b:=50000) (join_sums term (lo:=1890001) (a:=25000) (b:=25000) (join_sums term (lo:=1890001) (a:=12500) (b:=12500) (join_sums term (lo:=1890001) (a:=6250) (b:=6250) (join_sums term (lo:=1890001) (a:=3125) (b:=3125) (join_sums term (lo:=1890001) (a:=1562) (b:=1563) (join_sums term (lo:=1890001) (a:=781) (b:=781) (join_sums term (lo:=1890001) (a:=390) (b:=391) r1890001 r1890391) (join_sums term (lo:=1890782) (a:=390) (b:=391) r1890782 r1891172)) (join_sums term (lo:=1891563) (a:=781) (b:=782) (join_sums term (lo:=1891563) (a:=390) (b:=391) r1891563 r1891953) (join_sums term (lo:=1892344) (a:=391) (b:=391) r1892344 r1892735))) (join_sums term (lo:=1893126) (a:=1562) (b:=1563) (join_sums term (lo:=1893126) (a:=781) (b:=781) (join_sums term (lo:=1893126) (a:=390) (b:=391) r1893126 r1893516) (join_sums term (lo:=1893907) (a:=390) (b:=391) r1893907 r1894297)) (join_sums term (lo:=1894688) (a:=781) (b:=782) (join_sums term (lo:=1894688) (a:=390) (b:=391) r1894688 r1895078) (join_sums term (lo:=1895469) (a:=391) (b:=391) r1895469 r1895860)))) (join_sums term (lo:=1896251) (a:=3125) (b:=3125) (join_sums term (lo:=1896251) (a:=1562) (b:=1563) (join_sums term (lo:=1896251) (a:=781) (b:=781) (join_sums term (lo:=1896251) (a:=390) (b:=391) r1896251 r1896641) (join_sums term (lo:=1897032) (a:=390) (b:=391) r1897032 r1897422)) (join_sums term (lo:=1897813) (a:=781) (b:=782) (join_sums term (lo:=1897813) (a:=390) (b:=391) r1897813 r1898203) (join_sums term (lo:=1898594) (a:=391) (b:=391) r1898594 r1898985))) (join_sums term (lo:=1899376) (a:=1562) (b:=1563) (join_sums term (lo:=1899376) (a:=781) (b:=781) (join_sums term (lo:=1899376) (a:=390) (b:=391) r1899376 r1899766) (join_sums term (lo:=1900157) (a:=390) (b:=391) r1900157 r1900547)) (join_sums term (lo:=1900938) (a:=781) (b:=782) (join_sums term (lo:=1900938) (a:=390) (b:=391) r1900938 r1901328) (join_sums term (lo:=1901719) (a:=391) (b:=391) r1901719 r1902110))))) (join_sums term (lo:=1902501) (a:=6250) (b:=6250) (join_sums term (lo:=1902501) (a:=3125) (b:=3125) (join_sums term (lo:=1902501) (a:=1562) (b:=1563) (join_sums term (lo:=1902501) (a:=781) (b:=781) (join_sums term (lo:=1902501) (a:=390) (b:=391) r1902501 r1902891) (join_sums term (lo:=1903282) (a:=390) (b:=391) r1903282 r1903672)) (join_sums term (lo:=1904063) (a:=781) (b:=782) (join_sums term (lo:=1904063) (a:=390) (b:=391) r1904063 r1904453) (join_sums term (lo:=1904844) (a:=391) (b:=391) r1904844 r1905235))) (join_sums term (lo:=1905626) (a:=1562) (b:=1563) (join_sums term (lo:=1905626) (a:=781) (b:=781) (join_sums term (lo:=1905626) (a:=390) (b:=391) r1905626 r1906016) (join_sums term (lo:=1906407) (a:=390) (b:=391) r1906407 r1906797)) (join_sums term (lo:=1907188) (a:=781) (b:=782) (join_sums term (lo:=1907188) (a:=390) (b:=391) r1907188 r1907578) (join_sums term (lo:=1907969) (a:=391) (b:=391) r1907969 r1908360)))) (join_sums term (lo:=1908751) (a:=3125) (b:=3125) (join_sums term (lo:=1908751) (a:=1562) (b:=1563) (join_sums term (lo:=1908751) (a:=781) (b:=781) (join_sums term (lo:=1908751) (a:=390) (b:=391) r1908751 r1909141) (join_sums term (lo:=1909532) (a:=390) (b:=391) r1909532 r1909922)) (join_sums term (lo:=1910313) (a:=781) (b:=782) (join_sums term (lo:=1910313) (a:=390) (b:=391) r1910313 r1910703) (join_sums term (lo:=1911094) (a:=391) (b:=391) r1911094 r1911485))) (join_sums term (lo:=1911876) (a:=1562) (b:=1563) (join_sums term (lo:=1911876) (a:=781) (b:=781) (join_sums term (lo:=1911876) (a:=390) (b:=391) r1911876 r1912266) (join_sums term (lo:=1912657) (a:=390) (b:=391) r1912657 r1913047)) (join_sums term (lo:=1913438) (a:=781) (b:=782) (join_sums term (lo:=1913438) (a:=390) (b:=391) r1913438 r1913828) (join_sums term (lo:=1914219) (a:=391) (b:=391) r1914219 r1914610)))))) (join_sums term (lo:=1915001) (a:=12500) (b:=12500) (join_sums term (lo:=1915001) (a:=6250) (b:=6250) (join_sums term (lo:=1915001) (a:=3125) (b:=3125) (join_sums term (lo:=1915001) (a:=1562) (b:=1563) (join_sums term (lo:=1915001) (a:=781) (b:=781) (join_sums term (lo:=1915001) (a:=390) (b:=391) r1915001 r1915391) (join_sums term (lo:=1915782) (a:=390) (b:=391) r1915782 r1916172)) (join_sums term (lo:=1916563) (a:=781) (b:=782) (join_sums term (lo:=1916563) (a:=390) (b:=391) r1916563 r1916953) (join_sums term (lo:=1917344) (a:=391) (b:=391) r1917344 r1917735))) (join_sums term (lo:=1918126) (a:=1562) (b:=1563) (join_sums term (lo:=1918126) (a:=781) (b:=781) (join_sums term (lo:=1918126) (a:=390) (b:=391) r1918126 r1918516) (join_sums term (lo:=1918907) (a:=390) (b:=391) r1918907 r1919297)) (join_sums term (lo:=1919688) (a:=781) (b:=782) (join_sums term (lo:=1919688) (a:=390) (b:=391) r1919688 r1920078) (join_sums term (lo:=1920469) (a:=391) (b:=391) r1920469 r1920860)))) (join_sums term (lo:=1921251) (a:=3125) (b:=3125) (join_sums term (lo:=1921251) (a:=1562) (b:=1563) (join_sums term (lo:=1921251) (a:=781) (b:=781) (join_sums term (lo:=1921251) (a:=390) (b:=391) r1921251 r1921641) (join_sums term (lo:=1922032) (a:=390) (b:=391) r1922032 r1922422)) (join_sums term (lo:=1922813) (a:=781) (b:=782) (join_sums term (lo:=1922813) (a:=390) (b:=391) r1922813 r1923203) (join_sums term (lo:=1923594) (a:=391) (b:=391) r1923594 r1923985))) (join_sums term (lo:=1924376) (a:=1562) (b:=1563) (join_sums term (lo:=1924376) (a:=781) (b:=781) (join_sums term (lo:=1924376) (a:=390) (b:=391) r1924376 r1924766) (join_sums term (lo:=1925157) (a:=390) (b:=391) r1925157 r1925547)) (join_sums term (lo:=1925938) (a:=781) (b:=782) (join_sums term (lo:=1925938) (a:=390) (b:=391) r1925938 r1926328) (join_sums term (lo:=1926719) (a:=391) (b:=391) r1926719 r1927110))))) (join_sums term (lo:=1927501) (a:=6250) (b:=6250) (join_sums term (lo:=1927501) (a:=3125) (b:=3125) (join_sums term (lo:=1927501) (a:=1562) (b:=1563) (join_sums term (lo:=1927501) (a:=781) (b:=781) (join_sums term (lo:=1927501) (a:=390) (b:=391) r1927501 r1927891) (join_sums term (lo:=1928282) (a:=390) (b:=391) r1928282 r1928672)) (join_sums term (lo:=1929063) (a:=781) (b:=782) (join_sums term (lo:=1929063) (a:=390) (b:=391) r1929063 r1929453) (join_sums term (lo:=1929844) (a:=391) (b:=391) r1929844 r1930235))) (join_sums term (lo:=1930626) (a:=1562) (b:=1563) (join_sums term (lo:=1930626) (a:=781) (b:=781) (join_sums term (lo:=1930626) (a:=390) (b:=391) r1930626 r1931016) (join_sums term (lo:=1931407) (a:=390) (b:=391) r1931407 r1931797)) (join_sums term (lo:=1932188) (a:=781) (b:=782) (join_sums term (lo:=1932188) (a:=390) (b:=391) r1932188 r1932578) (join_sums term (lo:=1932969) (a:=391) (b:=391) r1932969 r1933360)))) (join_sums term (lo:=1933751) (a:=3125) (b:=3125) (join_sums term (lo:=1933751) (a:=1562) (b:=1563) (join_sums term (lo:=1933751) (a:=781) (b:=781) (join_sums term (lo:=1933751) (a:=390) (b:=391) r1933751 r1934141) (join_sums term (lo:=1934532) (a:=390) (b:=391) r1934532 r1934922)) (join_sums term (lo:=1935313) (a:=781) (b:=782) (join_sums term (lo:=1935313) (a:=390) (b:=391) r1935313 r1935703) (join_sums term (lo:=1936094) (a:=391) (b:=391) r1936094 r1936485))) (join_sums term (lo:=1936876) (a:=1562) (b:=1563) (join_sums term (lo:=1936876) (a:=781) (b:=781) (join_sums term (lo:=1936876) (a:=390) (b:=391) r1936876 r1937266) (join_sums term (lo:=1937657) (a:=390) (b:=391) r1937657 r1938047)) (join_sums term (lo:=1938438) (a:=781) (b:=782) (join_sums term (lo:=1938438) (a:=390) (b:=391) r1938438 r1938828) (join_sums term (lo:=1939219) (a:=391) (b:=391) r1939219 r1939610))))))) (join_sums term (lo:=1940001) (a:=25000) (b:=25000) (join_sums term (lo:=1940001) (a:=12500) (b:=12500) (join_sums term (lo:=1940001) (a:=6250) (b:=6250) (join_sums term (lo:=1940001) (a:=3125) (b:=3125) (join_sums term (lo:=1940001) (a:=1562) (b:=1563) (join_sums term (lo:=1940001) (a:=781) (b:=781) (join_sums term (lo:=1940001) (a:=390) (b:=391) r1940001 r1940391) (join_sums term (lo:=1940782) (a:=390) (b:=391) r1940782 r1941172)) (join_sums term (lo:=1941563) (a:=781) (b:=782) (join_sums term (lo:=1941563) (a:=390) (b:=391) r1941563 r1941953) (join_sums term (lo:=1942344) (a:=391) (b:=391) r1942344 r1942735))) (join_sums term (lo:=1943126) (a:=1562) (b:=1563) (join_sums term (lo:=1943126) (a:=781) (b:=781) (join_sums term (lo:=1943126) (a:=390) (b:=391) r1943126 r1943516) (join_sums term (lo:=1943907) (a:=390) (b:=391) r1943907 r1944297)) (join_sums term (lo:=1944688) (a:=781) (b:=782) (join_sums term (lo:=1944688) (a:=390) (b:=391) r1944688 r1945078) (join_sums term (lo:=1945469) (a:=391) (b:=391) r1945469 r1945860)))) (join_sums term (lo:=1946251) (a:=3125) (b:=3125) (join_sums term (lo:=1946251) (a:=1562) (b:=1563) (join_sums term (lo:=1946251) (a:=781) (b:=781) (join_sums term (lo:=1946251) (a:=390) (b:=391) r1946251 r1946641) (join_sums term (lo:=1947032) (a:=390) (b:=391) r1947032 r1947422)) (join_sums term (lo:=1947813) (a:=781) (b:=782) (join_sums term (lo:=1947813) (a:=390) (b:=391) r1947813 r1948203) (join_sums term (lo:=1948594) (a:=391) (b:=391) r1948594 r1948985))) (join_sums term (lo:=1949376) (a:=1562) (b:=1563) (join_sums term (lo:=1949376) (a:=781) (b:=781) (join_sums term (lo:=1949376) (a:=390) (b:=391) r1949376 r1949766) (join_sums term (lo:=1950157) (a:=390) (b:=391) r1950157 r1950547)) (join_sums term (lo:=1950938) (a:=781) (b:=782) (join_sums term (lo:=1950938) (a:=390) (b:=391) r1950938 r1951328) (join_sums term (lo:=1951719) (a:=391) (b:=391) r1951719 r1952110))))) (join_sums term (lo:=1952501) (a:=6250) (b:=6250) (join_sums term (lo:=1952501) (a:=3125) (b:=3125) (join_sums term (lo:=1952501) (a:=1562) (b:=1563) (join_sums term (lo:=1952501) (a:=781) (b:=781) (join_sums term (lo:=1952501) (a:=390) (b:=391) r1952501 r1952891) (join_sums term (lo:=1953282) (a:=390) (b:=391) r1953282 r1953672)) (join_sums term (lo:=1954063) (a:=781) (b:=782) (join_sums term (lo:=1954063) (a:=390) (b:=391) r1954063 r1954453) (join_sums term (lo:=1954844) (a:=391) (b:=391) r1954844 r1955235))) (join_sums term (lo:=1955626) (a:=1562) (b:=1563) (join_sums term (lo:=1955626) (a:=781) (b:=781) (join_sums term (lo:=1955626) (a:=390) (b:=391) r1955626 r1956016) (join_sums term (lo:=1956407) (a:=390) (b:=391) r1956407 r1956797)) (join_sums term (lo:=1957188) (a:=781) (b:=782) (join_sums term (lo:=1957188) (a:=390) (b:=391) r1957188 r1957578) (join_sums term (lo:=1957969) (a:=391) (b:=391) r1957969 r1958360)))) (join_sums term (lo:=1958751) (a:=3125) (b:=3125) (join_sums term (lo:=1958751) (a:=1562) (b:=1563) (join_sums term (lo:=1958751) (a:=781) (b:=781) (join_sums term (lo:=1958751) (a:=390) (b:=391) r1958751 r1959141) (join_sums term (lo:=1959532) (a:=390) (b:=391) r1959532 r1959922)) (join_sums term (lo:=1960313) (a:=781) (b:=782) (join_sums term (lo:=1960313) (a:=390) (b:=391) r1960313 r1960703) (join_sums term (lo:=1961094) (a:=391) (b:=391) r1961094 r1961485))) (join_sums term (lo:=1961876) (a:=1562) (b:=1563) (join_sums term (lo:=1961876) (a:=781) (b:=781) (join_sums term (lo:=1961876) (a:=390) (b:=391) r1961876 r1962266) (join_sums term (lo:=1962657) (a:=390) (b:=391) r1962657 r1963047)) (join_sums term (lo:=1963438) (a:=781) (b:=782) (join_sums term (lo:=1963438) (a:=390) (b:=391) r1963438 r1963828) (join_sums term (lo:=1964219) (a:=391) (b:=391) r1964219 r1964610)))))) (join_sums term (lo:=1965001) (a:=12500) (b:=12500) (join_sums term (lo:=1965001) (a:=6250) (b:=6250) (join_sums term (lo:=1965001) (a:=3125) (b:=3125) (join_sums term (lo:=1965001) (a:=1562) (b:=1563) (join_sums term (lo:=1965001) (a:=781) (b:=781) (join_sums term (lo:=1965001) (a:=390) (b:=391) r1965001 r1965391) (join_sums term (lo:=1965782) (a:=390) (b:=391) r1965782 r1966172)) (join_sums term (lo:=1966563) (a:=781) (b:=782) (join_sums term (lo:=1966563) (a:=390) (b:=391) r1966563 r1966953) (join_sums term (lo:=1967344) (a:=391) (b:=391) r1967344 r1967735))) (join_sums term (lo:=1968126) (a:=1562) (b:=1563) (join_sums term (lo:=1968126) (a:=781) (b:=781) (join_sums term (lo:=1968126) (a:=390) (b:=391) r1968126 r1968516) (join_sums term (lo:=1968907) (a:=390) (b:=391) r1968907 r1969297)) (join_sums term (lo:=1969688) (a:=781) (b:=782) (join_sums term (lo:=1969688) (a:=390) (b:=391) r1969688 r1970078) (join_sums term (lo:=1970469) (a:=391) (b:=391) r1970469 r1970860)))) (join_sums term (lo:=1971251) (a:=3125) (b:=3125) (join_sums term (lo:=1971251) (a:=1562) (b:=1563) (join_sums term (lo:=1971251) (a:=781) (b:=781) (join_sums term (lo:=1971251) (a:=390) (b:=391) r1971251 r1971641) (join_sums term (lo:=1972032) (a:=390) (b:=391) r1972032 r1972422)) (join_sums term (lo:=1972813) (a:=781) (b:=782) (join_sums term (lo:=1972813) (a:=390) (b:=391) r1972813 r1973203) (join_sums term (lo:=1973594) (a:=391) (b:=391) r1973594 r1973985))) (join_sums term (lo:=1974376) (a:=1562) (b:=1563) (join_sums term (lo:=1974376) (a:=781) (b:=781) (join_sums term (lo:=1974376) (a:=390) (b:=391) r1974376 r1974766) (join_sums term (lo:=1975157) (a:=390) (b:=391) r1975157 r1975547)) (join_sums term (lo:=1975938) (a:=781) (b:=782) (join_sums term (lo:=1975938) (a:=390) (b:=391) r1975938 r1976328) (join_sums term (lo:=1976719) (a:=391) (b:=391) r1976719 r1977110))))) (join_sums term (lo:=1977501) (a:=6250) (b:=6250) (join_sums term (lo:=1977501) (a:=3125) (b:=3125) (join_sums term (lo:=1977501) (a:=1562) (b:=1563) (join_sums term (lo:=1977501) (a:=781) (b:=781) (join_sums term (lo:=1977501) (a:=390) (b:=391) r1977501 r1977891) (join_sums term (lo:=1978282) (a:=390) (b:=391) r1978282 r1978672)) (join_sums term (lo:=1979063) (a:=781) (b:=782) (join_sums term (lo:=1979063) (a:=390) (b:=391) r1979063 r1979453) (join_sums term (lo:=1979844) (a:=391) (b:=391) r1979844 r1980235))) (join_sums term (lo:=1980626) (a:=1562) (b:=1563) (join_sums term (lo:=1980626) (a:=781) (b:=781) (join_sums term (lo:=1980626) (a:=390) (b:=391) r1980626 r1981016) (join_sums term (lo:=1981407) (a:=390) (b:=391) r1981407 r1981797)) (join_sums term (lo:=1982188) (a:=781) (b:=782) (join_sums term (lo:=1982188) (a:=390) (b:=391) r1982188 r1982578) (join_sums term (lo:=1982969) (a:=391) (b:=391) r1982969 r1983360)))) (join_sums term (lo:=1983751) (a:=3125) (b:=3125) (join_sums term (lo:=1983751) (a:=1562) (b:=1563) (join_sums term (lo:=1983751) (a:=781) (b:=781) (join_sums term (lo:=1983751) (a:=390) (b:=391) r1983751 r1984141) (join_sums term (lo:=1984532) (a:=390) (b:=391) r1984532 r1984922)) (join_sums term (lo:=1985313) (a:=781) (b:=782) (join_sums term (lo:=1985313) (a:=390) (b:=391) r1985313 r1985703) (join_sums term (lo:=1986094) (a:=391) (b:=391) r1986094 r1986485))) (join_sums term (lo:=1986876) (a:=1562) (b:=1563) (join_sums term (lo:=1986876) (a:=781) (b:=781) (join_sums term (lo:=1986876) (a:=390) (b:=391) r1986876 r1987266) (join_sums term (lo:=1987657) (a:=390) (b:=391) r1987657 r1988047)) (join_sums term (lo:=1988438) (a:=781) (b:=782) (join_sums term (lo:=1988438) (a:=390) (b:=391) r1988438 r1988828) (join_sums term (lo:=1989219) (a:=391) (b:=391) r1989219 r1989610))))))))

private theorem rows : blockSum term 0 1990001 5901940495 :=
  join_sums term (lo:=0) (a:=1890001) (b:=100000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 1990000).filter (1890000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=5901940495 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From1890000To1990000
