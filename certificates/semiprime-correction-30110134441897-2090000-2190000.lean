import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 2,090,000 through 2,190,000

The sum covers 6,867 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From2090000To2190000

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


private abbrev term := contribution 30110134441897 2090000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 2090001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 2090000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r2090001 : blockSum term 2090001 390 25727229 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2090391 : blockSum term 2090391 391 15588338 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2090782 : blockSum term 2090782 390 13247486 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2091172 : blockSum term 2091172 391 25709031 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2091563 : blockSum term 2091563 390 23365927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2091953 : blockSum term 2091953 391 20245560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2092344 : blockSum term 2092344 391 22575613 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2092735 : blockSum term 2092735 391 20235439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2093126 : blockSum term 2093126 390 26454525 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2093516 : blockSum term 2093516 391 17890931 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2093907 : blockSum term 2093907 390 17109211 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2094297 : blockSum term 2094297 391 17105183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2094688 : blockSum term 2094688 390 18655873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2095078 : blockSum term 2095078 391 22536661 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2095469 : blockSum term 2095469 391 22531196 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2095860 : blockSum term 2095860 391 19418678 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2096251 : blockSum term 2096251 390 16307837 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2096641 : blockSum term 2096641 391 22514938 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2097032 : blockSum term 2097032 390 18628659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2097422 : blockSum term 2097422 391 24831986 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2097813 : blockSum term 2097813 390 18618818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2098203 : blockSum term 2098203 391 17838433 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2098594 : blockSum term 2098594 391 24812546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2098985 : blockSum term 2098985 391 19379940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2099376 : blockSum term 2099376 390 21700384 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2099766 : blockSum term 2099766 391 18595954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2100157 : blockSum term 2100157 390 21690040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2100547 : blockSum term 2100547 391 21684639 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2100938 : blockSum term 2100938 390 27098642 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2101328 : blockSum term 2101328 391 18577123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2101719 : blockSum term 2101719 391 17799245 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2102110 : blockSum term 2102110 391 23984391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2102501 : blockSum term 2102501 390 24752086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2102891 : blockSum term 2102891 391 17786242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2103282 : blockSum term 2103282 390 17008463 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2103672 : blockSum term 2103672 391 24733673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2104063 : blockSum term 2104063 390 22409518 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2104453 : blockSum term 2104453 391 19313491 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2104844 : blockSum term 2104844 391 20081718 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2105235 : blockSum term 2105235 391 21621175 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2105626 : blockSum term 2105626 390 22387658 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2106016 : blockSum term 2106016 391 22381912 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2106407 : blockSum term 2106407 390 20062245 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2106797 : blockSum term 2106797 391 25457419 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2107188 : blockSum term 2107188 390 13882578 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2107578 : blockSum term 2107578 391 21589527 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2107969 : blockSum term 2107969 391 20042657 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2108360 : blockSum term 2108360 391 24661767 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2108751 : blockSum term 2108751 390 23114165 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2109141 : blockSum term 2109141 391 14635515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2109532 : blockSum term 2109532 390 21562600 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2109922 : blockSum term 2109922 391 22327400 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2110313 : blockSum term 2110313 390 20012862 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2110703 : blockSum term 2110703 391 22316342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2111094 : blockSum term 2111094 391 18464102 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2111485 : blockSum term 2111485 391 21536453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2111876 : blockSum term 2111876 390 19224275 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2112266 : blockSum term 2112266 391 15375612 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2112657 : blockSum term 2112657 390 22289363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2113047 : blockSum term 2113047 391 19978438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2113438 : blockSum term 2113438 390 20741934 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2113828 : blockSum term 2113828 391 19969120 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2114219 : blockSum term 2114219 391 19964505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2114610 : blockSum term 2114610 391 20726915 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2115001 : blockSum term 2115001 390 23791997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2115391 : blockSum term 2115391 391 22251024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2115782 : blockSum term 2115782 390 18410125 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2116172 : blockSum term 2116172 391 20706121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2116563 : blockSum term 2116563 390 24535521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2116953 : blockSum term 2116953 391 19930158 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2117344 : blockSum term 2117344 391 25289216 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2117735 : blockSum term 2117735 391 21452013 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2118126 : blockSum term 2118126 390 19149088 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2118516 : blockSum term 2118516 391 18378874 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2118907 : blockSum term 2118907 390 14546391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2119297 : blockSum term 2119297 391 22962236 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2119688 : blockSum term 2119688 390 17600187 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2120078 : blockSum term 2120078 391 24481583 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2120469 : blockSum term 2120469 391 16062023 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2120860 : blockSum term 2120860 391 21411187 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2121251 : blockSum term 2121251 390 16819034 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2121641 : blockSum term 2121641 391 22929866 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2122032 : blockSum term 2122032 390 19103704 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2122422 : blockSum term 2122422 391 21391261 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2122813 : blockSum term 2122813 390 19858465 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2123203 : blockSum term 2123203 391 17563411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2123594 : blockSum term 2123594 391 22902565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2123985 : blockSum term 2123985 391 20607463 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2124376 : blockSum term 2124376 390 16787591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2124766 : blockSum term 2124766 391 19071939 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2125157 : blockSum term 2125157 390 19067109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2125547 : blockSum term 2125547 391 25162913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2125938 : blockSum term 2125938 390 22107156 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2126328 : blockSum term 2126328 391 20577815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2126719 : blockSum term 2126719 391 22858727 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2127110 : blockSum term 2127110 391 19805587 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2127501 : blockSum term 2127501 390 19800889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2127891 : blockSum term 2127891 391 20557830 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2128282 : blockSum term 2128282 390 24358673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2128672 : blockSum term 2128672 391 19025954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2129063 : blockSum term 2129063 390 23586081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2129453 : blockSum term 2129453 391 23580028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2129844 : blockSum term 2129844 391 15970202 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2130235 : blockSum term 2130235 391 21287846 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2130626 : blockSum term 2130626 390 17482426 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2131016 : blockSum term 2131016 391 18238136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2131407 : blockSum term 2131407 390 22032324 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2131797 : blockSum term 2131797 391 20507867 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2132188 : blockSum term 2132188 390 22781100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2132578 : blockSum term 2132578 391 19738471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2132969 : blockSum term 2132969 391 18975246 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2133360 : blockSum term 2133360 391 22764693 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2133751 : blockSum term 2133751 390 15931126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2134141 : blockSum term 2134141 391 19719288 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2134532 : blockSum term 2134532 390 15923145 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2134922 : blockSum term 2134922 391 20467977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2135313 : blockSum term 2135313 390 19704978 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2135703 : blockSum term 2135703 391 21973709 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2136094 : blockSum term 2136094 391 27270795 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2136485 : blockSum term 2136485 391 19690469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2136876 : blockSum term 2136876 390 20442845 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2137266 : blockSum term 2137266 391 19681243 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2137657 : blockSum term 2137657 390 23460095 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2138047 : blockSum term 2138047 391 18157731 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2138438 : blockSum term 2138438 390 19666376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2138828 : blockSum term 2138828 391 17393159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2139219 : blockSum term 2139219 391 19657054 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2139610 : blockSum term 2139610 391 19651889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2140001 : blockSum term 2140001 390 22670051 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2140391 : blockSum term 2140391 391 20398067 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2140782 : blockSum term 2140782 390 19637965 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2141172 : blockSum term 2141172 391 18123016 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2141563 : blockSum term 2141563 390 24912419 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2141953 : blockSum term 2141953 391 21887741 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2142344 : blockSum term 2142344 391 21127964 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2142735 : blockSum term 2142735 391 17350822 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2143126 : blockSum term 2143126 390 21117831 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2143516 : blockSum term 2143516 391 19604819 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2143907 : blockSum term 2143907 390 24123087 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2144297 : blockSum term 2144297 391 23363482 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2144688 : blockSum term 2144688 390 21097989 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2145078 : blockSum term 2145078 391 24859357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2145469 : blockSum term 2145469 391 18828026 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2145860 : blockSum term 2145860 391 15811240 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2146251 : blockSum term 2146251 390 20324535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2146641 : blockSum term 2146641 391 18061750 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2147032 : blockSum term 2147032 390 22571863 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2147422 : blockSum term 2147422 391 17300563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2147813 : blockSum term 2147813 390 18800693 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2148203 : blockSum term 2148203 391 21051629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2148594 : blockSum term 2148594 391 20295215 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2148985 : blockSum term 2148985 391 21793294 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2149376 : blockSum term 2149376 390 16528650 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2149766 : blockSum term 2149766 391 17275759 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2150157 : blockSum term 2150157 390 18022605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2150547 : blockSum term 2150547 391 21021511 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2150938 : blockSum term 2150938 390 21016311 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2151328 : blockSum term 2151328 391 22512042 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2151719 : blockSum term 2151719 391 17254780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2152110 : blockSum term 2152110 391 22501265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2152501 : blockSum term 2152501 390 22495871 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2152891 : blockSum term 2152891 391 18742390 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2153282 : blockSum term 2153282 390 18738055 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2153672 : blockSum term 2153672 391 22479685 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2154063 : blockSum term 2154063 390 17230715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2154453 : blockSum term 2154453 391 18724477 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2154844 : blockSum term 2154844 391 23961992 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2155235 : blockSum term 2155235 391 21710238 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2155626 : blockSum term 2155626 390 17214389 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2156016 : blockSum term 2156016 391 23944362 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2156407 : blockSum term 2156407 390 18702234 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2156797 : blockSum term 2156797 391 22437161 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2157188 : blockSum term 2157188 390 24674672 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2157578 : blockSum term 2157578 391 21678589 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2157969 : blockSum term 2157969 391 20179132 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2158360 : blockSum term 2158360 391 23910179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2158751 : blockSum term 2158751 390 20916657 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2159141 : blockSum term 2159141 391 21658005 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2159532 : blockSum term 2159532 390 20906228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2159922 : blockSum term 2159922 391 20900963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2160313 : blockSum term 2160313 390 16418596 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2160703 : blockSum term 2160703 391 17160845 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2161094 : blockSum term 2161094 391 20886399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2161485 : blockSum term 2161485 391 18643827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2161876 : blockSum term 2161876 390 23113222 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2162266 : blockSum term 2162266 391 20125955 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2162657 : blockSum term 2162657 390 18630586 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2163047 : blockSum term 2163047 391 20861453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2163438 : blockSum term 2163438 390 21600976 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2163828 : blockSum term 2163828 391 17872652 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2164219 : blockSum term 2164219 391 20845917 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2164610 : blockSum term 2164610 391 14142096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2165001 : blockSum term 2165001 390 19348168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2165391 : blockSum term 2165391 391 20831120 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2165782 : blockSum term 2165782 390 20825774 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2166172 : blockSum term 2166172 391 16358733 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2166563 : blockSum term 2166563 390 15611707 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2166953 : blockSum term 2166953 391 17837936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2167344 : blockSum term 2167344 391 19319873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2167735 : blockSum term 2167735 391 20800874 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2168126 : blockSum term 2168126 390 20052899 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2168516 : blockSum term 2168516 391 27473182 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2168907 : blockSum term 2168907 390 17073650 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2169297 : blockSum term 2169297 391 19295723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2169688 : blockSum term 2169688 390 16323585 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2170078 : blockSum term 2170078 391 22253842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2170469 : blockSum term 2170469 391 21506960 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2170860 : blockSum term 2170860 391 17794297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2171251 : blockSum term 2171251 390 18530903 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2171641 : blockSum term 2171641 391 19268185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2172032 : blockSum term 2172032 390 22227189 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2172422 : blockSum term 2172422 391 21480773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2172813 : blockSum term 2172813 390 25919281 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2173203 : blockSum term 2173203 391 17768532 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2173594 : blockSum term 2173594 391 17024296 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2173985 : blockSum term 2173985 391 18500461 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2174376 : blockSum term 2174376 390 22194597 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2174766 : blockSum term 2174766 391 14792689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2175157 : blockSum term 2175157 390 17746873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2175547 : blockSum term 2175547 391 22178077 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2175938 : blockSum term 2175938 390 19955341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2176328 : blockSum term 2176328 391 24384144 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2176719 : blockSum term 2176719 391 21423655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2177110 : blockSum term 2177110 391 17725137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2177501 : blockSum term 2177501 390 22152102 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2177891 : blockSum term 2177891 391 19931562 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2178282 : blockSum term 2178282 390 21402902 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2178672 : blockSum term 2178672 391 18446502 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2179063 : blockSum term 2179063 390 16228929 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2179453 : blockSum term 2179453 391 20649710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2179844 : blockSum term 2179844 391 21382269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2180235 : blockSum term 2180235 391 17691467 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2180626 : blockSum term 2180626 390 18424467 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2181016 : blockSum term 2181016 391 21366700 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2181407 : blockSum term 2181407 390 17678718 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2181797 : blockSum term 2181797 391 19883941 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2182188 : blockSum term 2182188 390 16934211 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2182578 : blockSum term 2182578 391 16194328 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2182969 : blockSum term 2182969 391 16926103 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2183360 : blockSum term 2183360 391 21336777 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2183751 : blockSum term 2183751 390 19860330 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2184141 : blockSum term 2184141 391 22061312 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2184532 : blockSum term 2184532 390 20585102 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2184922 : blockSum term 2184922 391 17640175 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2185313 : blockSum term 2185313 390 19840303 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2185703 : blockSum term 2185703 391 20570213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2186094 : blockSum term 2186094 391 16893159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2186485 : blockSum term 2186485 391 24232323 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2186876 : blockSum term 2186876 390 16884999 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2187266 : blockSum term 2187266 391 16147242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2187657 : blockSum term 2187657 390 22013420 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2188047 : blockSum term 2188047 391 22008385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2188438 : blockSum term 2188438 390 19803067 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2188828 : blockSum term 2188828 391 19065093 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2189219 : blockSum term 2189219 391 24192176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2189610 : blockSum term 2189610 391 16123819 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 2090001 100000 5191059302 := (join_sums term (lo:=2090001) (a:=50000) (b:=50000) (join_sums term (lo:=2090001) (a:=25000) (b:=25000) (join_sums term (lo:=2090001) (a:=12500) (b:=12500) (join_sums term (lo:=2090001) (a:=6250) (b:=6250) (join_sums term (lo:=2090001) (a:=3125) (b:=3125) (join_sums term (lo:=2090001) (a:=1562) (b:=1563) (join_sums term (lo:=2090001) (a:=781) (b:=781) (join_sums term (lo:=2090001) (a:=390) (b:=391) r2090001 r2090391) (join_sums term (lo:=2090782) (a:=390) (b:=391) r2090782 r2091172)) (join_sums term (lo:=2091563) (a:=781) (b:=782) (join_sums term (lo:=2091563) (a:=390) (b:=391) r2091563 r2091953) (join_sums term (lo:=2092344) (a:=391) (b:=391) r2092344 r2092735))) (join_sums term (lo:=2093126) (a:=1562) (b:=1563) (join_sums term (lo:=2093126) (a:=781) (b:=781) (join_sums term (lo:=2093126) (a:=390) (b:=391) r2093126 r2093516) (join_sums term (lo:=2093907) (a:=390) (b:=391) r2093907 r2094297)) (join_sums term (lo:=2094688) (a:=781) (b:=782) (join_sums term (lo:=2094688) (a:=390) (b:=391) r2094688 r2095078) (join_sums term (lo:=2095469) (a:=391) (b:=391) r2095469 r2095860)))) (join_sums term (lo:=2096251) (a:=3125) (b:=3125) (join_sums term (lo:=2096251) (a:=1562) (b:=1563) (join_sums term (lo:=2096251) (a:=781) (b:=781) (join_sums term (lo:=2096251) (a:=390) (b:=391) r2096251 r2096641) (join_sums term (lo:=2097032) (a:=390) (b:=391) r2097032 r2097422)) (join_sums term (lo:=2097813) (a:=781) (b:=782) (join_sums term (lo:=2097813) (a:=390) (b:=391) r2097813 r2098203) (join_sums term (lo:=2098594) (a:=391) (b:=391) r2098594 r2098985))) (join_sums term (lo:=2099376) (a:=1562) (b:=1563) (join_sums term (lo:=2099376) (a:=781) (b:=781) (join_sums term (lo:=2099376) (a:=390) (b:=391) r2099376 r2099766) (join_sums term (lo:=2100157) (a:=390) (b:=391) r2100157 r2100547)) (join_sums term (lo:=2100938) (a:=781) (b:=782) (join_sums term (lo:=2100938) (a:=390) (b:=391) r2100938 r2101328) (join_sums term (lo:=2101719) (a:=391) (b:=391) r2101719 r2102110))))) (join_sums term (lo:=2102501) (a:=6250) (b:=6250) (join_sums term (lo:=2102501) (a:=3125) (b:=3125) (join_sums term (lo:=2102501) (a:=1562) (b:=1563) (join_sums term (lo:=2102501) (a:=781) (b:=781) (join_sums term (lo:=2102501) (a:=390) (b:=391) r2102501 r2102891) (join_sums term (lo:=2103282) (a:=390) (b:=391) r2103282 r2103672)) (join_sums term (lo:=2104063) (a:=781) (b:=782) (join_sums term (lo:=2104063) (a:=390) (b:=391) r2104063 r2104453) (join_sums term (lo:=2104844) (a:=391) (b:=391) r2104844 r2105235))) (join_sums term (lo:=2105626) (a:=1562) (b:=1563) (join_sums term (lo:=2105626) (a:=781) (b:=781) (join_sums term (lo:=2105626) (a:=390) (b:=391) r2105626 r2106016) (join_sums term (lo:=2106407) (a:=390) (b:=391) r2106407 r2106797)) (join_sums term (lo:=2107188) (a:=781) (b:=782) (join_sums term (lo:=2107188) (a:=390) (b:=391) r2107188 r2107578) (join_sums term (lo:=2107969) (a:=391) (b:=391) r2107969 r2108360)))) (join_sums term (lo:=2108751) (a:=3125) (b:=3125) (join_sums term (lo:=2108751) (a:=1562) (b:=1563) (join_sums term (lo:=2108751) (a:=781) (b:=781) (join_sums term (lo:=2108751) (a:=390) (b:=391) r2108751 r2109141) (join_sums term (lo:=2109532) (a:=390) (b:=391) r2109532 r2109922)) (join_sums term (lo:=2110313) (a:=781) (b:=782) (join_sums term (lo:=2110313) (a:=390) (b:=391) r2110313 r2110703) (join_sums term (lo:=2111094) (a:=391) (b:=391) r2111094 r2111485))) (join_sums term (lo:=2111876) (a:=1562) (b:=1563) (join_sums term (lo:=2111876) (a:=781) (b:=781) (join_sums term (lo:=2111876) (a:=390) (b:=391) r2111876 r2112266) (join_sums term (lo:=2112657) (a:=390) (b:=391) r2112657 r2113047)) (join_sums term (lo:=2113438) (a:=781) (b:=782) (join_sums term (lo:=2113438) (a:=390) (b:=391) r2113438 r2113828) (join_sums term (lo:=2114219) (a:=391) (b:=391) r2114219 r2114610)))))) (join_sums term (lo:=2115001) (a:=12500) (b:=12500) (join_sums term (lo:=2115001) (a:=6250) (b:=6250) (join_sums term (lo:=2115001) (a:=3125) (b:=3125) (join_sums term (lo:=2115001) (a:=1562) (b:=1563) (join_sums term (lo:=2115001) (a:=781) (b:=781) (join_sums term (lo:=2115001) (a:=390) (b:=391) r2115001 r2115391) (join_sums term (lo:=2115782) (a:=390) (b:=391) r2115782 r2116172)) (join_sums term (lo:=2116563) (a:=781) (b:=782) (join_sums term (lo:=2116563) (a:=390) (b:=391) r2116563 r2116953) (join_sums term (lo:=2117344) (a:=391) (b:=391) r2117344 r2117735))) (join_sums term (lo:=2118126) (a:=1562) (b:=1563) (join_sums term (lo:=2118126) (a:=781) (b:=781) (join_sums term (lo:=2118126) (a:=390) (b:=391) r2118126 r2118516) (join_sums term (lo:=2118907) (a:=390) (b:=391) r2118907 r2119297)) (join_sums term (lo:=2119688) (a:=781) (b:=782) (join_sums term (lo:=2119688) (a:=390) (b:=391) r2119688 r2120078) (join_sums term (lo:=2120469) (a:=391) (b:=391) r2120469 r2120860)))) (join_sums term (lo:=2121251) (a:=3125) (b:=3125) (join_sums term (lo:=2121251) (a:=1562) (b:=1563) (join_sums term (lo:=2121251) (a:=781) (b:=781) (join_sums term (lo:=2121251) (a:=390) (b:=391) r2121251 r2121641) (join_sums term (lo:=2122032) (a:=390) (b:=391) r2122032 r2122422)) (join_sums term (lo:=2122813) (a:=781) (b:=782) (join_sums term (lo:=2122813) (a:=390) (b:=391) r2122813 r2123203) (join_sums term (lo:=2123594) (a:=391) (b:=391) r2123594 r2123985))) (join_sums term (lo:=2124376) (a:=1562) (b:=1563) (join_sums term (lo:=2124376) (a:=781) (b:=781) (join_sums term (lo:=2124376) (a:=390) (b:=391) r2124376 r2124766) (join_sums term (lo:=2125157) (a:=390) (b:=391) r2125157 r2125547)) (join_sums term (lo:=2125938) (a:=781) (b:=782) (join_sums term (lo:=2125938) (a:=390) (b:=391) r2125938 r2126328) (join_sums term (lo:=2126719) (a:=391) (b:=391) r2126719 r2127110))))) (join_sums term (lo:=2127501) (a:=6250) (b:=6250) (join_sums term (lo:=2127501) (a:=3125) (b:=3125) (join_sums term (lo:=2127501) (a:=1562) (b:=1563) (join_sums term (lo:=2127501) (a:=781) (b:=781) (join_sums term (lo:=2127501) (a:=390) (b:=391) r2127501 r2127891) (join_sums term (lo:=2128282) (a:=390) (b:=391) r2128282 r2128672)) (join_sums term (lo:=2129063) (a:=781) (b:=782) (join_sums term (lo:=2129063) (a:=390) (b:=391) r2129063 r2129453) (join_sums term (lo:=2129844) (a:=391) (b:=391) r2129844 r2130235))) (join_sums term (lo:=2130626) (a:=1562) (b:=1563) (join_sums term (lo:=2130626) (a:=781) (b:=781) (join_sums term (lo:=2130626) (a:=390) (b:=391) r2130626 r2131016) (join_sums term (lo:=2131407) (a:=390) (b:=391) r2131407 r2131797)) (join_sums term (lo:=2132188) (a:=781) (b:=782) (join_sums term (lo:=2132188) (a:=390) (b:=391) r2132188 r2132578) (join_sums term (lo:=2132969) (a:=391) (b:=391) r2132969 r2133360)))) (join_sums term (lo:=2133751) (a:=3125) (b:=3125) (join_sums term (lo:=2133751) (a:=1562) (b:=1563) (join_sums term (lo:=2133751) (a:=781) (b:=781) (join_sums term (lo:=2133751) (a:=390) (b:=391) r2133751 r2134141) (join_sums term (lo:=2134532) (a:=390) (b:=391) r2134532 r2134922)) (join_sums term (lo:=2135313) (a:=781) (b:=782) (join_sums term (lo:=2135313) (a:=390) (b:=391) r2135313 r2135703) (join_sums term (lo:=2136094) (a:=391) (b:=391) r2136094 r2136485))) (join_sums term (lo:=2136876) (a:=1562) (b:=1563) (join_sums term (lo:=2136876) (a:=781) (b:=781) (join_sums term (lo:=2136876) (a:=390) (b:=391) r2136876 r2137266) (join_sums term (lo:=2137657) (a:=390) (b:=391) r2137657 r2138047)) (join_sums term (lo:=2138438) (a:=781) (b:=782) (join_sums term (lo:=2138438) (a:=390) (b:=391) r2138438 r2138828) (join_sums term (lo:=2139219) (a:=391) (b:=391) r2139219 r2139610))))))) (join_sums term (lo:=2140001) (a:=25000) (b:=25000) (join_sums term (lo:=2140001) (a:=12500) (b:=12500) (join_sums term (lo:=2140001) (a:=6250) (b:=6250) (join_sums term (lo:=2140001) (a:=3125) (b:=3125) (join_sums term (lo:=2140001) (a:=1562) (b:=1563) (join_sums term (lo:=2140001) (a:=781) (b:=781) (join_sums term (lo:=2140001) (a:=390) (b:=391) r2140001 r2140391) (join_sums term (lo:=2140782) (a:=390) (b:=391) r2140782 r2141172)) (join_sums term (lo:=2141563) (a:=781) (b:=782) (join_sums term (lo:=2141563) (a:=390) (b:=391) r2141563 r2141953) (join_sums term (lo:=2142344) (a:=391) (b:=391) r2142344 r2142735))) (join_sums term (lo:=2143126) (a:=1562) (b:=1563) (join_sums term (lo:=2143126) (a:=781) (b:=781) (join_sums term (lo:=2143126) (a:=390) (b:=391) r2143126 r2143516) (join_sums term (lo:=2143907) (a:=390) (b:=391) r2143907 r2144297)) (join_sums term (lo:=2144688) (a:=781) (b:=782) (join_sums term (lo:=2144688) (a:=390) (b:=391) r2144688 r2145078) (join_sums term (lo:=2145469) (a:=391) (b:=391) r2145469 r2145860)))) (join_sums term (lo:=2146251) (a:=3125) (b:=3125) (join_sums term (lo:=2146251) (a:=1562) (b:=1563) (join_sums term (lo:=2146251) (a:=781) (b:=781) (join_sums term (lo:=2146251) (a:=390) (b:=391) r2146251 r2146641) (join_sums term (lo:=2147032) (a:=390) (b:=391) r2147032 r2147422)) (join_sums term (lo:=2147813) (a:=781) (b:=782) (join_sums term (lo:=2147813) (a:=390) (b:=391) r2147813 r2148203) (join_sums term (lo:=2148594) (a:=391) (b:=391) r2148594 r2148985))) (join_sums term (lo:=2149376) (a:=1562) (b:=1563) (join_sums term (lo:=2149376) (a:=781) (b:=781) (join_sums term (lo:=2149376) (a:=390) (b:=391) r2149376 r2149766) (join_sums term (lo:=2150157) (a:=390) (b:=391) r2150157 r2150547)) (join_sums term (lo:=2150938) (a:=781) (b:=782) (join_sums term (lo:=2150938) (a:=390) (b:=391) r2150938 r2151328) (join_sums term (lo:=2151719) (a:=391) (b:=391) r2151719 r2152110))))) (join_sums term (lo:=2152501) (a:=6250) (b:=6250) (join_sums term (lo:=2152501) (a:=3125) (b:=3125) (join_sums term (lo:=2152501) (a:=1562) (b:=1563) (join_sums term (lo:=2152501) (a:=781) (b:=781) (join_sums term (lo:=2152501) (a:=390) (b:=391) r2152501 r2152891) (join_sums term (lo:=2153282) (a:=390) (b:=391) r2153282 r2153672)) (join_sums term (lo:=2154063) (a:=781) (b:=782) (join_sums term (lo:=2154063) (a:=390) (b:=391) r2154063 r2154453) (join_sums term (lo:=2154844) (a:=391) (b:=391) r2154844 r2155235))) (join_sums term (lo:=2155626) (a:=1562) (b:=1563) (join_sums term (lo:=2155626) (a:=781) (b:=781) (join_sums term (lo:=2155626) (a:=390) (b:=391) r2155626 r2156016) (join_sums term (lo:=2156407) (a:=390) (b:=391) r2156407 r2156797)) (join_sums term (lo:=2157188) (a:=781) (b:=782) (join_sums term (lo:=2157188) (a:=390) (b:=391) r2157188 r2157578) (join_sums term (lo:=2157969) (a:=391) (b:=391) r2157969 r2158360)))) (join_sums term (lo:=2158751) (a:=3125) (b:=3125) (join_sums term (lo:=2158751) (a:=1562) (b:=1563) (join_sums term (lo:=2158751) (a:=781) (b:=781) (join_sums term (lo:=2158751) (a:=390) (b:=391) r2158751 r2159141) (join_sums term (lo:=2159532) (a:=390) (b:=391) r2159532 r2159922)) (join_sums term (lo:=2160313) (a:=781) (b:=782) (join_sums term (lo:=2160313) (a:=390) (b:=391) r2160313 r2160703) (join_sums term (lo:=2161094) (a:=391) (b:=391) r2161094 r2161485))) (join_sums term (lo:=2161876) (a:=1562) (b:=1563) (join_sums term (lo:=2161876) (a:=781) (b:=781) (join_sums term (lo:=2161876) (a:=390) (b:=391) r2161876 r2162266) (join_sums term (lo:=2162657) (a:=390) (b:=391) r2162657 r2163047)) (join_sums term (lo:=2163438) (a:=781) (b:=782) (join_sums term (lo:=2163438) (a:=390) (b:=391) r2163438 r2163828) (join_sums term (lo:=2164219) (a:=391) (b:=391) r2164219 r2164610)))))) (join_sums term (lo:=2165001) (a:=12500) (b:=12500) (join_sums term (lo:=2165001) (a:=6250) (b:=6250) (join_sums term (lo:=2165001) (a:=3125) (b:=3125) (join_sums term (lo:=2165001) (a:=1562) (b:=1563) (join_sums term (lo:=2165001) (a:=781) (b:=781) (join_sums term (lo:=2165001) (a:=390) (b:=391) r2165001 r2165391) (join_sums term (lo:=2165782) (a:=390) (b:=391) r2165782 r2166172)) (join_sums term (lo:=2166563) (a:=781) (b:=782) (join_sums term (lo:=2166563) (a:=390) (b:=391) r2166563 r2166953) (join_sums term (lo:=2167344) (a:=391) (b:=391) r2167344 r2167735))) (join_sums term (lo:=2168126) (a:=1562) (b:=1563) (join_sums term (lo:=2168126) (a:=781) (b:=781) (join_sums term (lo:=2168126) (a:=390) (b:=391) r2168126 r2168516) (join_sums term (lo:=2168907) (a:=390) (b:=391) r2168907 r2169297)) (join_sums term (lo:=2169688) (a:=781) (b:=782) (join_sums term (lo:=2169688) (a:=390) (b:=391) r2169688 r2170078) (join_sums term (lo:=2170469) (a:=391) (b:=391) r2170469 r2170860)))) (join_sums term (lo:=2171251) (a:=3125) (b:=3125) (join_sums term (lo:=2171251) (a:=1562) (b:=1563) (join_sums term (lo:=2171251) (a:=781) (b:=781) (join_sums term (lo:=2171251) (a:=390) (b:=391) r2171251 r2171641) (join_sums term (lo:=2172032) (a:=390) (b:=391) r2172032 r2172422)) (join_sums term (lo:=2172813) (a:=781) (b:=782) (join_sums term (lo:=2172813) (a:=390) (b:=391) r2172813 r2173203) (join_sums term (lo:=2173594) (a:=391) (b:=391) r2173594 r2173985))) (join_sums term (lo:=2174376) (a:=1562) (b:=1563) (join_sums term (lo:=2174376) (a:=781) (b:=781) (join_sums term (lo:=2174376) (a:=390) (b:=391) r2174376 r2174766) (join_sums term (lo:=2175157) (a:=390) (b:=391) r2175157 r2175547)) (join_sums term (lo:=2175938) (a:=781) (b:=782) (join_sums term (lo:=2175938) (a:=390) (b:=391) r2175938 r2176328) (join_sums term (lo:=2176719) (a:=391) (b:=391) r2176719 r2177110))))) (join_sums term (lo:=2177501) (a:=6250) (b:=6250) (join_sums term (lo:=2177501) (a:=3125) (b:=3125) (join_sums term (lo:=2177501) (a:=1562) (b:=1563) (join_sums term (lo:=2177501) (a:=781) (b:=781) (join_sums term (lo:=2177501) (a:=390) (b:=391) r2177501 r2177891) (join_sums term (lo:=2178282) (a:=390) (b:=391) r2178282 r2178672)) (join_sums term (lo:=2179063) (a:=781) (b:=782) (join_sums term (lo:=2179063) (a:=390) (b:=391) r2179063 r2179453) (join_sums term (lo:=2179844) (a:=391) (b:=391) r2179844 r2180235))) (join_sums term (lo:=2180626) (a:=1562) (b:=1563) (join_sums term (lo:=2180626) (a:=781) (b:=781) (join_sums term (lo:=2180626) (a:=390) (b:=391) r2180626 r2181016) (join_sums term (lo:=2181407) (a:=390) (b:=391) r2181407 r2181797)) (join_sums term (lo:=2182188) (a:=781) (b:=782) (join_sums term (lo:=2182188) (a:=390) (b:=391) r2182188 r2182578) (join_sums term (lo:=2182969) (a:=391) (b:=391) r2182969 r2183360)))) (join_sums term (lo:=2183751) (a:=3125) (b:=3125) (join_sums term (lo:=2183751) (a:=1562) (b:=1563) (join_sums term (lo:=2183751) (a:=781) (b:=781) (join_sums term (lo:=2183751) (a:=390) (b:=391) r2183751 r2184141) (join_sums term (lo:=2184532) (a:=390) (b:=391) r2184532 r2184922)) (join_sums term (lo:=2185313) (a:=781) (b:=782) (join_sums term (lo:=2185313) (a:=390) (b:=391) r2185313 r2185703) (join_sums term (lo:=2186094) (a:=391) (b:=391) r2186094 r2186485))) (join_sums term (lo:=2186876) (a:=1562) (b:=1563) (join_sums term (lo:=2186876) (a:=781) (b:=781) (join_sums term (lo:=2186876) (a:=390) (b:=391) r2186876 r2187266) (join_sums term (lo:=2187657) (a:=390) (b:=391) r2187657 r2188047)) (join_sums term (lo:=2188438) (a:=781) (b:=782) (join_sums term (lo:=2188438) (a:=390) (b:=391) r2188438 r2188828) (join_sums term (lo:=2189219) (a:=391) (b:=391) r2189219 r2189610))))))))

private theorem rows : blockSum term 0 2190001 5191059302 :=
  join_sums term (lo:=0) (a:=2090001) (b:=100000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 2190000).filter (2090000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=5191059302 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From2090000To2190000
