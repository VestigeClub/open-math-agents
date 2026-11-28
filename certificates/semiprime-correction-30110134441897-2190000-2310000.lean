import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 2,190,000 through 2,310,000

The sum covers 8,203 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From2190000To2310000

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


private abbrev term := contribution 30110134441897 2190000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 2190001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 2190000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r2190001 : blockSum term 2190001 468 26377178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2190469 : blockSum term 2190469 469 22707362 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2190938 : blockSum term 2190938 469 22700704 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2191407 : blockSum term 2191407 469 21962591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2191876 : blockSum term 2191876 468 24882981 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2192344 : blockSum term 2192344 469 21949606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2192813 : blockSum term 2192813 469 26332335 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2193282 : blockSum term 2193282 469 27786584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2193751 : blockSum term 2193751 468 20469021 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2194219 : blockSum term 2194219 469 24117175 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2194688 : blockSum term 2194688 469 21187438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2195157 : blockSum term 2195157 469 20450975 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2195626 : blockSum term 2195626 468 25556399 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2196094 : blockSum term 2196094 469 22629348 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2196563 : blockSum term 2196563 469 25542192 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2197032 : blockSum term 2197032 469 21156349 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2197501 : blockSum term 2197501 468 22609818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2197969 : blockSum term 2197969 469 20415438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2198438 : blockSum term 2198438 469 22596852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2198907 : blockSum term 2198907 469 18218052 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2199376 : blockSum term 2199376 468 17484782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2199844 : blockSum term 2199844 469 21121366 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2200313 : blockSum term 2200313 469 26939891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2200782 : blockSum term 2200782 469 26204711 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2201251 : blockSum term 2201251 468 23285877 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2201719 : blockSum term 2201719 469 20369524 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2202188 : blockSum term 2202188 469 22545193 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2202657 : blockSum term 2202657 469 25446596 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2203126 : blockSum term 2203126 468 22531751 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2203594 : blockSum term 2203594 469 26158172 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2204063 : blockSum term 2204063 469 21792604 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2204532 : blockSum term 2204532 469 23964878 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2205001 : blockSum term 2205001 468 21780009 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2205469 : blockSum term 2205469 469 23224963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2205938 : blockSum term 2205938 469 18864776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2206407 : blockSum term 2206407 469 29740254 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2206876 : blockSum term 2206876 468 29005816 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2207344 : blockSum term 2207344 469 19573927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2207813 : blockSum term 2207813 469 25365939 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2208282 : blockSum term 2208282 469 21011223 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2208751 : blockSum term 2208751 468 24626878 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2209219 : blockSum term 2209219 469 21722519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2209688 : blockSum term 2209688 469 30403561 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2210157 : blockSum term 2210157 469 32565745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2210626 : blockSum term 2210626 468 20257090 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2211094 : blockSum term 2211094 469 18805024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2211563 : blockSum term 2211563 469 20968690 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2212032 : blockSum term 2212032 469 26745569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2212501 : blockSum term 2212501 468 21679153 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2212969 : blockSum term 2212969 469 21672077 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2213438 : blockSum term 2213438 469 17333084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2213907 : blockSum term 2213907 469 19494209 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2214376 : blockSum term 2214376 468 18045234 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2214844 : blockSum term 2214844 469 25977815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2215313 : blockSum term 2215313 469 23085367 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2215782 : blockSum term 2215782 469 24520504 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2216251 : blockSum term 2216251 468 22350143 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2216719 : blockSum term 2216719 469 23785249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2217188 : blockSum term 2217188 469 25219468 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2217657 : blockSum term 2217657 469 17288181 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2218126 : blockSum term 2218126 468 21604649 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2218594 : blockSum term 2218594 469 21598206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2219063 : blockSum term 2219063 469 23031462 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2219532 : blockSum term 2219532 469 21585901 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2220001 : blockSum term 2220001 468 23737657 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2220469 : blockSum term 2220469 469 17978190 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2220938 : blockSum term 2220938 469 23724341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2221407 : blockSum term 2221407 469 20842617 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2221876 : blockSum term 2221876 468 25865958 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2222344 : blockSum term 2222344 469 24421703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2222813 : blockSum term 2222813 469 21542534 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2223282 : blockSum term 2223282 469 24408665 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2223751 : blockSum term 2223751 468 20813485 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2224219 : blockSum term 2224219 469 24394176 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2224688 : blockSum term 2224688 469 23669901 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2225157 : blockSum term 2225157 469 24380429 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2225626 : blockSum term 2225626 468 20072772 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2226094 : blockSum term 2226094 469 26516278 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2226563 : blockSum term 2226563 469 23643223 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2227032 : blockSum term 2227032 469 25068720 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2227501 : blockSum term 2227501 468 26493704 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2227969 : blockSum term 2227969 469 25769555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2228438 : blockSum term 2228438 469 20753275 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2228907 : blockSum term 2228907 469 22178563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2229376 : blockSum term 2229376 468 24317863 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2229844 : blockSum term 2229844 469 23595963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2230313 : blockSum term 2230313 469 22874117 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2230782 : blockSum term 2230782 469 17151072 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2231251 : blockSum term 2231251 468 27147953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2231719 : blockSum term 2231719 469 20712127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2232188 : blockSum term 2232188 469 19992738 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2232657 : blockSum term 2232657 469 24269439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2233126 : blockSum term 2233126 468 25689179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2233594 : blockSum term 2233594 469 23542168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2234063 : blockSum term 2234063 469 22822127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2234532 : blockSum term 2234532 469 24241706 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2235001 : blockSum term 2235001 468 22808902 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2235469 : blockSum term 2235469 469 26365097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2235938 : blockSum term 2235938 469 25645256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2236407 : blockSum term 2236407 469 20652851 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2236876 : blockSum term 2236876 468 19223304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2237344 : blockSum term 2237344 469 24200203 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2237813 : blockSum term 2237813 469 20634998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2238282 : blockSum term 2238282 469 22763975 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2238751 : blockSum term 2238751 468 23468631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2239219 : blockSum term 2239219 469 21329105 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2239688 : blockSum term 2239688 469 21323286 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2240157 : blockSum term 2240157 469 20606952 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2240626 : blockSum term 2240626 468 26994524 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2241094 : blockSum term 2241094 469 25565535 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2241563 : blockSum term 2241563 469 17748686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2242032 : blockSum term 2242032 469 19873277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2242501 : blockSum term 2242501 468 22705421 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2242969 : blockSum term 2242969 469 23408329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2243438 : blockSum term 2243438 469 24110925 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2243907 : blockSum term 2243907 469 17014508 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2244376 : blockSum term 2244376 468 26932485 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2244844 : blockSum term 2244844 469 23381946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2245313 : blockSum term 2245313 469 24083899 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2245782 : blockSum term 2245782 469 23368906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2246251 : blockSum term 2246251 468 22654659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2246719 : blockSum term 2246719 469 19817013 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2247188 : blockSum term 2247188 469 21226599 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2247657 : blockSum term 2247657 469 26171750 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2248126 : blockSum term 2248126 468 24042593 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2248594 : blockSum term 2248594 469 24036036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2249063 : blockSum term 2249063 469 21908857 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2249532 : blockSum term 2249532 469 20489274 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2250001 : blockSum term 2250001 468 18364591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2250469 : blockSum term 2250469 469 19065607 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2250938 : blockSum term 2250938 469 20472445 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2251407 : blockSum term 2251407 469 22583609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2251876 : blockSum term 2251876 468 21872119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2252344 : blockSum term 2252344 469 21160361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2252813 : blockSum term 2252813 469 24679681 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2253282 : blockSum term 2253282 469 25377107 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2253751 : blockSum term 2253751 468 23255730 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2254219 : blockSum term 2254219 469 21135199 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2254688 : blockSum term 2254688 469 24651008 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2255157 : blockSum term 2255157 469 23235573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2255626 : blockSum term 2255626 468 23932859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2256094 : blockSum term 2256094 469 26037169 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2256563 : blockSum term 2256563 469 25326164 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2257032 : blockSum term 2257032 469 20395688 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2257501 : blockSum term 2257501 468 27420982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2257969 : blockSum term 2257969 469 25303472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2258438 : blockSum term 2258438 469 23188228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2258907 : blockSum term 2258907 469 20371879 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2259376 : blockSum term 2259376 468 19664092 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2259844 : blockSum term 2259844 469 24573521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2260313 : blockSum term 2260313 469 28778047 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2260782 : blockSum term 2260782 469 21752482 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2261251 : blockSum term 2261251 468 21044231 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2261719 : blockSum term 2261719 469 18233643 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2262188 : blockSum term 2262188 469 22434728 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2262657 : blockSum term 2262657 469 20325348 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2263126 : blockSum term 2263126 468 23823148 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2263594 : blockSum term 2263594 469 22415503 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2264063 : blockSum term 2264063 469 24509573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2264532 : blockSum term 2264532 469 27302647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2265001 : blockSum term 2265001 468 17496408 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2265469 : blockSum term 2265469 469 21690396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2265938 : blockSum term 2265938 469 24482384 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2266407 : blockSum term 2266407 469 25174240 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2266876 : blockSum term 2266876 468 24468014 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2267344 : blockSum term 2267344 469 21665124 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2267813 : blockSum term 2267813 469 25151974 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2268282 : blockSum term 2268282 469 20954048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2268751 : blockSum term 2268751 468 23042666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2269219 : blockSum term 2269219 469 21640336 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2269688 : blockSum term 2269688 469 23727549 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2270157 : blockSum term 2270157 469 24418712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2270626 : blockSum term 2270626 468 25109135 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2271094 : blockSum term 2271094 469 26496420 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2271563 : blockSum term 2271563 469 23003467 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2272032 : blockSum term 2272032 469 25783996 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2272501 : blockSum term 2272501 468 20203869 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2272969 : blockSum term 2272969 469 22287282 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2273438 : blockSum term 2273438 469 23673837 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2273907 : blockSum term 2273907 469 24362846 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2274376 : blockSum term 2274376 468 25051813 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2274844 : blockSum term 2274844 469 20870297 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2275313 : blockSum term 2275313 469 25733097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2275782 : blockSum term 2275782 469 18772621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2276251 : blockSum term 2276251 468 19462667 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2276719 : blockSum term 2276719 469 20152273 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2277188 : blockSum term 2277188 469 22229912 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2277657 : blockSum term 2277657 469 25696294 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2278126 : blockSum term 2278126 468 20134960 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2278594 : blockSum term 2278594 469 21516965 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2279063 : blockSum term 2279063 469 21510917 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2279532 : blockSum term 2279532 469 19424027 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2280001 : blockSum term 2280001 468 22192558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2280469 : blockSum term 2280469 469 19413118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2280938 : blockSum term 2280938 469 25645475 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2281407 : blockSum term 2281407 469 19401287 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2281876 : blockSum term 2281876 468 20088841 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2282344 : blockSum term 2282344 469 20083283 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2282813 : blockSum term 2282813 469 14539326 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2283282 : blockSum term 2283282 469 24224476 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2283751 : blockSum term 2283751 468 20757950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2284219 : blockSum term 2284219 469 20060532 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2284688 : blockSum term 2284688 469 17980033 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2285157 : blockSum term 2285157 469 25580070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2285626 : blockSum term 2285626 468 24189896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2286094 : blockSum term 2286094 469 19346181 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2286563 : blockSum term 2286563 469 22794653 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2287032 : blockSum term 2287032 469 24169396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2287501 : blockSum term 2287501 468 20710973 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2287969 : blockSum term 2287969 469 22085915 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2288438 : blockSum term 2288438 469 24838744 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2288907 : blockSum term 2288907 469 19313903 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2289376 : blockSum term 2289376 468 23445690 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2289844 : blockSum term 2289844 469 24128765 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2290313 : blockSum term 2290313 469 19986789 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2290782 : blockSum term 2290782 469 22737232 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2291251 : blockSum term 2291251 468 22041780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2291719 : blockSum term 2291719 469 21346736 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2292188 : blockSum term 2292188 469 25470971 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2292657 : blockSum term 2292657 469 19269916 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2293126 : blockSum term 2293126 468 21328439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2293594 : blockSum term 2293594 469 26824555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2294063 : blockSum term 2294063 469 18565342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2294532 : blockSum term 2294532 469 18559937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2295001 : blockSum term 2295001 468 21304193 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2295469 : blockSum term 2295469 469 24046484 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2295938 : blockSum term 2295938 469 19231962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2296407 : blockSum term 2296407 469 20599284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2296876 : blockSum term 2296876 468 21966915 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2297344 : blockSum term 2297344 469 23332626 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2297813 : blockSum term 2297813 469 25384484 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2298282 : blockSum term 2298282 469 21947417 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2298751 : blockSum term 2298751 468 21255782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2299219 : blockSum term 2299219 469 22620405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2299688 : blockSum term 2299688 469 24670272 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2300157 : blockSum term 2300157 469 21923362 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2300626 : blockSum term 2300626 468 24656484 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2301094 : blockSum term 2301094 469 23964795 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2301563 : blockSum term 2301563 469 23958209 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2302032 : blockSum term 2302032 469 21898231 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2302501 : blockSum term 2302501 468 15735191 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2302969 : blockSum term 2302969 469 21202191 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2303438 : blockSum term 2303438 469 23247333 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2303907 : blockSum term 2303907 469 24607601 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2304376 : blockSum term 2304376 468 21867136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2304844 : blockSum term 2304844 469 15712979 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2305313 : blockSum term 2305313 469 22538646 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2305782 : blockSum term 2305782 469 19118422 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2306251 : blockSum term 2306251 468 21844096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2306719 : blockSum term 2306719 469 21154649 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2307188 : blockSum term 2307188 469 24560100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2307657 : blockSum term 2307657 469 21142630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2308126 : blockSum term 2308126 468 24546040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2308594 : blockSum term 2308594 469 23857719 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2309063 : blockSum term 2309063 469 23169358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r2309532 : blockSum term 2309532 469 21799893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 2190001 120000 5795679039 := (join_sums term (lo:=2190001) (a:=60000) (b:=60000) (join_sums term (lo:=2190001) (a:=30000) (b:=30000) (join_sums term (lo:=2190001) (a:=15000) (b:=15000) (join_sums term (lo:=2190001) (a:=7500) (b:=7500) (join_sums term (lo:=2190001) (a:=3750) (b:=3750) (join_sums term (lo:=2190001) (a:=1875) (b:=1875) (join_sums term (lo:=2190001) (a:=937) (b:=938) (join_sums term (lo:=2190001) (a:=468) (b:=469) r2190001 r2190469) (join_sums term (lo:=2190938) (a:=469) (b:=469) r2190938 r2191407)) (join_sums term (lo:=2191876) (a:=937) (b:=938) (join_sums term (lo:=2191876) (a:=468) (b:=469) r2191876 r2192344) (join_sums term (lo:=2192813) (a:=469) (b:=469) r2192813 r2193282))) (join_sums term (lo:=2193751) (a:=1875) (b:=1875) (join_sums term (lo:=2193751) (a:=937) (b:=938) (join_sums term (lo:=2193751) (a:=468) (b:=469) r2193751 r2194219) (join_sums term (lo:=2194688) (a:=469) (b:=469) r2194688 r2195157)) (join_sums term (lo:=2195626) (a:=937) (b:=938) (join_sums term (lo:=2195626) (a:=468) (b:=469) r2195626 r2196094) (join_sums term (lo:=2196563) (a:=469) (b:=469) r2196563 r2197032)))) (join_sums term (lo:=2197501) (a:=3750) (b:=3750) (join_sums term (lo:=2197501) (a:=1875) (b:=1875) (join_sums term (lo:=2197501) (a:=937) (b:=938) (join_sums term (lo:=2197501) (a:=468) (b:=469) r2197501 r2197969) (join_sums term (lo:=2198438) (a:=469) (b:=469) r2198438 r2198907)) (join_sums term (lo:=2199376) (a:=937) (b:=938) (join_sums term (lo:=2199376) (a:=468) (b:=469) r2199376 r2199844) (join_sums term (lo:=2200313) (a:=469) (b:=469) r2200313 r2200782))) (join_sums term (lo:=2201251) (a:=1875) (b:=1875) (join_sums term (lo:=2201251) (a:=937) (b:=938) (join_sums term (lo:=2201251) (a:=468) (b:=469) r2201251 r2201719) (join_sums term (lo:=2202188) (a:=469) (b:=469) r2202188 r2202657)) (join_sums term (lo:=2203126) (a:=937) (b:=938) (join_sums term (lo:=2203126) (a:=468) (b:=469) r2203126 r2203594) (join_sums term (lo:=2204063) (a:=469) (b:=469) r2204063 r2204532))))) (join_sums term (lo:=2205001) (a:=7500) (b:=7500) (join_sums term (lo:=2205001) (a:=3750) (b:=3750) (join_sums term (lo:=2205001) (a:=1875) (b:=1875) (join_sums term (lo:=2205001) (a:=937) (b:=938) (join_sums term (lo:=2205001) (a:=468) (b:=469) r2205001 r2205469) (join_sums term (lo:=2205938) (a:=469) (b:=469) r2205938 r2206407)) (join_sums term (lo:=2206876) (a:=937) (b:=938) (join_sums term (lo:=2206876) (a:=468) (b:=469) r2206876 r2207344) (join_sums term (lo:=2207813) (a:=469) (b:=469) r2207813 r2208282))) (join_sums term (lo:=2208751) (a:=1875) (b:=1875) (join_sums term (lo:=2208751) (a:=937) (b:=938) (join_sums term (lo:=2208751) (a:=468) (b:=469) r2208751 r2209219) (join_sums term (lo:=2209688) (a:=469) (b:=469) r2209688 r2210157)) (join_sums term (lo:=2210626) (a:=937) (b:=938) (join_sums term (lo:=2210626) (a:=468) (b:=469) r2210626 r2211094) (join_sums term (lo:=2211563) (a:=469) (b:=469) r2211563 r2212032)))) (join_sums term (lo:=2212501) (a:=3750) (b:=3750) (join_sums term (lo:=2212501) (a:=1875) (b:=1875) (join_sums term (lo:=2212501) (a:=937) (b:=938) (join_sums term (lo:=2212501) (a:=468) (b:=469) r2212501 r2212969) (join_sums term (lo:=2213438) (a:=469) (b:=469) r2213438 r2213907)) (join_sums term (lo:=2214376) (a:=937) (b:=938) (join_sums term (lo:=2214376) (a:=468) (b:=469) r2214376 r2214844) (join_sums term (lo:=2215313) (a:=469) (b:=469) r2215313 r2215782))) (join_sums term (lo:=2216251) (a:=1875) (b:=1875) (join_sums term (lo:=2216251) (a:=937) (b:=938) (join_sums term (lo:=2216251) (a:=468) (b:=469) r2216251 r2216719) (join_sums term (lo:=2217188) (a:=469) (b:=469) r2217188 r2217657)) (join_sums term (lo:=2218126) (a:=937) (b:=938) (join_sums term (lo:=2218126) (a:=468) (b:=469) r2218126 r2218594) (join_sums term (lo:=2219063) (a:=469) (b:=469) r2219063 r2219532)))))) (join_sums term (lo:=2220001) (a:=15000) (b:=15000) (join_sums term (lo:=2220001) (a:=7500) (b:=7500) (join_sums term (lo:=2220001) (a:=3750) (b:=3750) (join_sums term (lo:=2220001) (a:=1875) (b:=1875) (join_sums term (lo:=2220001) (a:=937) (b:=938) (join_sums term (lo:=2220001) (a:=468) (b:=469) r2220001 r2220469) (join_sums term (lo:=2220938) (a:=469) (b:=469) r2220938 r2221407)) (join_sums term (lo:=2221876) (a:=937) (b:=938) (join_sums term (lo:=2221876) (a:=468) (b:=469) r2221876 r2222344) (join_sums term (lo:=2222813) (a:=469) (b:=469) r2222813 r2223282))) (join_sums term (lo:=2223751) (a:=1875) (b:=1875) (join_sums term (lo:=2223751) (a:=937) (b:=938) (join_sums term (lo:=2223751) (a:=468) (b:=469) r2223751 r2224219) (join_sums term (lo:=2224688) (a:=469) (b:=469) r2224688 r2225157)) (join_sums term (lo:=2225626) (a:=937) (b:=938) (join_sums term (lo:=2225626) (a:=468) (b:=469) r2225626 r2226094) (join_sums term (lo:=2226563) (a:=469) (b:=469) r2226563 r2227032)))) (join_sums term (lo:=2227501) (a:=3750) (b:=3750) (join_sums term (lo:=2227501) (a:=1875) (b:=1875) (join_sums term (lo:=2227501) (a:=937) (b:=938) (join_sums term (lo:=2227501) (a:=468) (b:=469) r2227501 r2227969) (join_sums term (lo:=2228438) (a:=469) (b:=469) r2228438 r2228907)) (join_sums term (lo:=2229376) (a:=937) (b:=938) (join_sums term (lo:=2229376) (a:=468) (b:=469) r2229376 r2229844) (join_sums term (lo:=2230313) (a:=469) (b:=469) r2230313 r2230782))) (join_sums term (lo:=2231251) (a:=1875) (b:=1875) (join_sums term (lo:=2231251) (a:=937) (b:=938) (join_sums term (lo:=2231251) (a:=468) (b:=469) r2231251 r2231719) (join_sums term (lo:=2232188) (a:=469) (b:=469) r2232188 r2232657)) (join_sums term (lo:=2233126) (a:=937) (b:=938) (join_sums term (lo:=2233126) (a:=468) (b:=469) r2233126 r2233594) (join_sums term (lo:=2234063) (a:=469) (b:=469) r2234063 r2234532))))) (join_sums term (lo:=2235001) (a:=7500) (b:=7500) (join_sums term (lo:=2235001) (a:=3750) (b:=3750) (join_sums term (lo:=2235001) (a:=1875) (b:=1875) (join_sums term (lo:=2235001) (a:=937) (b:=938) (join_sums term (lo:=2235001) (a:=468) (b:=469) r2235001 r2235469) (join_sums term (lo:=2235938) (a:=469) (b:=469) r2235938 r2236407)) (join_sums term (lo:=2236876) (a:=937) (b:=938) (join_sums term (lo:=2236876) (a:=468) (b:=469) r2236876 r2237344) (join_sums term (lo:=2237813) (a:=469) (b:=469) r2237813 r2238282))) (join_sums term (lo:=2238751) (a:=1875) (b:=1875) (join_sums term (lo:=2238751) (a:=937) (b:=938) (join_sums term (lo:=2238751) (a:=468) (b:=469) r2238751 r2239219) (join_sums term (lo:=2239688) (a:=469) (b:=469) r2239688 r2240157)) (join_sums term (lo:=2240626) (a:=937) (b:=938) (join_sums term (lo:=2240626) (a:=468) (b:=469) r2240626 r2241094) (join_sums term (lo:=2241563) (a:=469) (b:=469) r2241563 r2242032)))) (join_sums term (lo:=2242501) (a:=3750) (b:=3750) (join_sums term (lo:=2242501) (a:=1875) (b:=1875) (join_sums term (lo:=2242501) (a:=937) (b:=938) (join_sums term (lo:=2242501) (a:=468) (b:=469) r2242501 r2242969) (join_sums term (lo:=2243438) (a:=469) (b:=469) r2243438 r2243907)) (join_sums term (lo:=2244376) (a:=937) (b:=938) (join_sums term (lo:=2244376) (a:=468) (b:=469) r2244376 r2244844) (join_sums term (lo:=2245313) (a:=469) (b:=469) r2245313 r2245782))) (join_sums term (lo:=2246251) (a:=1875) (b:=1875) (join_sums term (lo:=2246251) (a:=937) (b:=938) (join_sums term (lo:=2246251) (a:=468) (b:=469) r2246251 r2246719) (join_sums term (lo:=2247188) (a:=469) (b:=469) r2247188 r2247657)) (join_sums term (lo:=2248126) (a:=937) (b:=938) (join_sums term (lo:=2248126) (a:=468) (b:=469) r2248126 r2248594) (join_sums term (lo:=2249063) (a:=469) (b:=469) r2249063 r2249532))))))) (join_sums term (lo:=2250001) (a:=30000) (b:=30000) (join_sums term (lo:=2250001) (a:=15000) (b:=15000) (join_sums term (lo:=2250001) (a:=7500) (b:=7500) (join_sums term (lo:=2250001) (a:=3750) (b:=3750) (join_sums term (lo:=2250001) (a:=1875) (b:=1875) (join_sums term (lo:=2250001) (a:=937) (b:=938) (join_sums term (lo:=2250001) (a:=468) (b:=469) r2250001 r2250469) (join_sums term (lo:=2250938) (a:=469) (b:=469) r2250938 r2251407)) (join_sums term (lo:=2251876) (a:=937) (b:=938) (join_sums term (lo:=2251876) (a:=468) (b:=469) r2251876 r2252344) (join_sums term (lo:=2252813) (a:=469) (b:=469) r2252813 r2253282))) (join_sums term (lo:=2253751) (a:=1875) (b:=1875) (join_sums term (lo:=2253751) (a:=937) (b:=938) (join_sums term (lo:=2253751) (a:=468) (b:=469) r2253751 r2254219) (join_sums term (lo:=2254688) (a:=469) (b:=469) r2254688 r2255157)) (join_sums term (lo:=2255626) (a:=937) (b:=938) (join_sums term (lo:=2255626) (a:=468) (b:=469) r2255626 r2256094) (join_sums term (lo:=2256563) (a:=469) (b:=469) r2256563 r2257032)))) (join_sums term (lo:=2257501) (a:=3750) (b:=3750) (join_sums term (lo:=2257501) (a:=1875) (b:=1875) (join_sums term (lo:=2257501) (a:=937) (b:=938) (join_sums term (lo:=2257501) (a:=468) (b:=469) r2257501 r2257969) (join_sums term (lo:=2258438) (a:=469) (b:=469) r2258438 r2258907)) (join_sums term (lo:=2259376) (a:=937) (b:=938) (join_sums term (lo:=2259376) (a:=468) (b:=469) r2259376 r2259844) (join_sums term (lo:=2260313) (a:=469) (b:=469) r2260313 r2260782))) (join_sums term (lo:=2261251) (a:=1875) (b:=1875) (join_sums term (lo:=2261251) (a:=937) (b:=938) (join_sums term (lo:=2261251) (a:=468) (b:=469) r2261251 r2261719) (join_sums term (lo:=2262188) (a:=469) (b:=469) r2262188 r2262657)) (join_sums term (lo:=2263126) (a:=937) (b:=938) (join_sums term (lo:=2263126) (a:=468) (b:=469) r2263126 r2263594) (join_sums term (lo:=2264063) (a:=469) (b:=469) r2264063 r2264532))))) (join_sums term (lo:=2265001) (a:=7500) (b:=7500) (join_sums term (lo:=2265001) (a:=3750) (b:=3750) (join_sums term (lo:=2265001) (a:=1875) (b:=1875) (join_sums term (lo:=2265001) (a:=937) (b:=938) (join_sums term (lo:=2265001) (a:=468) (b:=469) r2265001 r2265469) (join_sums term (lo:=2265938) (a:=469) (b:=469) r2265938 r2266407)) (join_sums term (lo:=2266876) (a:=937) (b:=938) (join_sums term (lo:=2266876) (a:=468) (b:=469) r2266876 r2267344) (join_sums term (lo:=2267813) (a:=469) (b:=469) r2267813 r2268282))) (join_sums term (lo:=2268751) (a:=1875) (b:=1875) (join_sums term (lo:=2268751) (a:=937) (b:=938) (join_sums term (lo:=2268751) (a:=468) (b:=469) r2268751 r2269219) (join_sums term (lo:=2269688) (a:=469) (b:=469) r2269688 r2270157)) (join_sums term (lo:=2270626) (a:=937) (b:=938) (join_sums term (lo:=2270626) (a:=468) (b:=469) r2270626 r2271094) (join_sums term (lo:=2271563) (a:=469) (b:=469) r2271563 r2272032)))) (join_sums term (lo:=2272501) (a:=3750) (b:=3750) (join_sums term (lo:=2272501) (a:=1875) (b:=1875) (join_sums term (lo:=2272501) (a:=937) (b:=938) (join_sums term (lo:=2272501) (a:=468) (b:=469) r2272501 r2272969) (join_sums term (lo:=2273438) (a:=469) (b:=469) r2273438 r2273907)) (join_sums term (lo:=2274376) (a:=937) (b:=938) (join_sums term (lo:=2274376) (a:=468) (b:=469) r2274376 r2274844) (join_sums term (lo:=2275313) (a:=469) (b:=469) r2275313 r2275782))) (join_sums term (lo:=2276251) (a:=1875) (b:=1875) (join_sums term (lo:=2276251) (a:=937) (b:=938) (join_sums term (lo:=2276251) (a:=468) (b:=469) r2276251 r2276719) (join_sums term (lo:=2277188) (a:=469) (b:=469) r2277188 r2277657)) (join_sums term (lo:=2278126) (a:=937) (b:=938) (join_sums term (lo:=2278126) (a:=468) (b:=469) r2278126 r2278594) (join_sums term (lo:=2279063) (a:=469) (b:=469) r2279063 r2279532)))))) (join_sums term (lo:=2280001) (a:=15000) (b:=15000) (join_sums term (lo:=2280001) (a:=7500) (b:=7500) (join_sums term (lo:=2280001) (a:=3750) (b:=3750) (join_sums term (lo:=2280001) (a:=1875) (b:=1875) (join_sums term (lo:=2280001) (a:=937) (b:=938) (join_sums term (lo:=2280001) (a:=468) (b:=469) r2280001 r2280469) (join_sums term (lo:=2280938) (a:=469) (b:=469) r2280938 r2281407)) (join_sums term (lo:=2281876) (a:=937) (b:=938) (join_sums term (lo:=2281876) (a:=468) (b:=469) r2281876 r2282344) (join_sums term (lo:=2282813) (a:=469) (b:=469) r2282813 r2283282))) (join_sums term (lo:=2283751) (a:=1875) (b:=1875) (join_sums term (lo:=2283751) (a:=937) (b:=938) (join_sums term (lo:=2283751) (a:=468) (b:=469) r2283751 r2284219) (join_sums term (lo:=2284688) (a:=469) (b:=469) r2284688 r2285157)) (join_sums term (lo:=2285626) (a:=937) (b:=938) (join_sums term (lo:=2285626) (a:=468) (b:=469) r2285626 r2286094) (join_sums term (lo:=2286563) (a:=469) (b:=469) r2286563 r2287032)))) (join_sums term (lo:=2287501) (a:=3750) (b:=3750) (join_sums term (lo:=2287501) (a:=1875) (b:=1875) (join_sums term (lo:=2287501) (a:=937) (b:=938) (join_sums term (lo:=2287501) (a:=468) (b:=469) r2287501 r2287969) (join_sums term (lo:=2288438) (a:=469) (b:=469) r2288438 r2288907)) (join_sums term (lo:=2289376) (a:=937) (b:=938) (join_sums term (lo:=2289376) (a:=468) (b:=469) r2289376 r2289844) (join_sums term (lo:=2290313) (a:=469) (b:=469) r2290313 r2290782))) (join_sums term (lo:=2291251) (a:=1875) (b:=1875) (join_sums term (lo:=2291251) (a:=937) (b:=938) (join_sums term (lo:=2291251) (a:=468) (b:=469) r2291251 r2291719) (join_sums term (lo:=2292188) (a:=469) (b:=469) r2292188 r2292657)) (join_sums term (lo:=2293126) (a:=937) (b:=938) (join_sums term (lo:=2293126) (a:=468) (b:=469) r2293126 r2293594) (join_sums term (lo:=2294063) (a:=469) (b:=469) r2294063 r2294532))))) (join_sums term (lo:=2295001) (a:=7500) (b:=7500) (join_sums term (lo:=2295001) (a:=3750) (b:=3750) (join_sums term (lo:=2295001) (a:=1875) (b:=1875) (join_sums term (lo:=2295001) (a:=937) (b:=938) (join_sums term (lo:=2295001) (a:=468) (b:=469) r2295001 r2295469) (join_sums term (lo:=2295938) (a:=469) (b:=469) r2295938 r2296407)) (join_sums term (lo:=2296876) (a:=937) (b:=938) (join_sums term (lo:=2296876) (a:=468) (b:=469) r2296876 r2297344) (join_sums term (lo:=2297813) (a:=469) (b:=469) r2297813 r2298282))) (join_sums term (lo:=2298751) (a:=1875) (b:=1875) (join_sums term (lo:=2298751) (a:=937) (b:=938) (join_sums term (lo:=2298751) (a:=468) (b:=469) r2298751 r2299219) (join_sums term (lo:=2299688) (a:=469) (b:=469) r2299688 r2300157)) (join_sums term (lo:=2300626) (a:=937) (b:=938) (join_sums term (lo:=2300626) (a:=468) (b:=469) r2300626 r2301094) (join_sums term (lo:=2301563) (a:=469) (b:=469) r2301563 r2302032)))) (join_sums term (lo:=2302501) (a:=3750) (b:=3750) (join_sums term (lo:=2302501) (a:=1875) (b:=1875) (join_sums term (lo:=2302501) (a:=937) (b:=938) (join_sums term (lo:=2302501) (a:=468) (b:=469) r2302501 r2302969) (join_sums term (lo:=2303438) (a:=469) (b:=469) r2303438 r2303907)) (join_sums term (lo:=2304376) (a:=937) (b:=938) (join_sums term (lo:=2304376) (a:=468) (b:=469) r2304376 r2304844) (join_sums term (lo:=2305313) (a:=469) (b:=469) r2305313 r2305782))) (join_sums term (lo:=2306251) (a:=1875) (b:=1875) (join_sums term (lo:=2306251) (a:=937) (b:=938) (join_sums term (lo:=2306251) (a:=468) (b:=469) r2306251 r2306719) (join_sums term (lo:=2307188) (a:=469) (b:=469) r2307188 r2307657)) (join_sums term (lo:=2308126) (a:=937) (b:=938) (join_sums term (lo:=2308126) (a:=468) (b:=469) r2308126 r2308594) (join_sums term (lo:=2309063) (a:=469) (b:=469) r2309063 r2309532))))))))

private theorem rows : blockSum term 0 2310001 5795679039 :=
  join_sums term (lo:=0) (a:=2190001) (b:=120000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 2310000).filter (2190000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=5795679039 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From2190000To2310000
