import certificates.«semiprime-correction-555157672301-middle»

/-! The low semiprime correction at 204,778,727,327 uses the same prime-count table as the other endpoint proofs. -/
open Finset
namespace SharedCorrectionLow25

private def contribution (x y : ℕ) (tab : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then tab (x/p) - tab (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z b value : ℕ} (tab : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, n≤b → tab n = Nat.primeCounting n)
    (prime_ok : ∀ n, n≤b → (prime n=true ↔ n.Prime))
    (hz : z≤b) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y tab prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y tab prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p≤b := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ (le_trans ub hq),ok _ (by omega : p-1≤b)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y tab prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y tab prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result

private abbrev tab := SparsePrimeA204.fast

private abbrev prime := SparsePrimeA204.prime
private theorem prime_ok (n : ℕ) (hn : n≤34751024) : prime n=true ↔ n.Prime := SparsePrimeA204.prime_ok n hn

private abbrev term := contribution 204778727327 5894 tab prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))

private theorem before : blockSum term 0 5895 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 5894 < p := by omega
  simp [term,contribution,no]

private theorem block5895 : blockSum term 5895 288 60350510 := by unfold blockSum; decide +kernel

private theorem block6183 : blockSum term 6183 289 69906134 := by unfold blockSum; decide +kernel

private theorem block6472 : blockSum term 6472 289 57377774 := by unfold blockSum; decide +kernel

private theorem block6761 : blockSum term 6761 289 67987422 := by unfold blockSum; decide +kernel

private theorem block7050 : blockSum term 7050 289 51204256 := by unfold blockSum; decide +kernel

private theorem block7339 : blockSum term 7339 289 56071173 := by unfold blockSum; decide +kernel

private theorem block7628 : blockSum term 7628 289 50984998 := by unfold blockSum; decide +kernel

private theorem block7917 : blockSum term 7917 289 46094817 := by unfold blockSum; decide +kernel

private theorem block8206 : blockSum term 8206 289 47748917 := by unfold blockSum; decide +kernel

private theorem block8495 : blockSum term 8495 289 53545845 := by unfold blockSum; decide +kernel

private theorem block8784 : blockSum term 8784 289 46164651 := by unfold blockSum; decide +kernel

private theorem block9073 : blockSum term 9073 289 43397342 := by unfold blockSum; decide +kernel

private theorem block9362 : blockSum term 9362 289 46293447 := by unfold blockSum; decide +kernel

private theorem block9651 : blockSum term 9651 289 43643310 := by unfold blockSum; decide +kernel

private theorem block9940 : blockSum term 9940 289 37307252 := by unfold blockSum; decide +kernel

private theorem block10229 : blockSum term 10229 289 40143707 := by unfold blockSum; decide +kernel

private theorem block10518 : blockSum term 10518 289 35425058 := by unfold blockSum; decide +kernel

private theorem block10807 : blockSum term 10807 289 35733655 := by unfold blockSum; decide +kernel

private theorem block11096 : blockSum term 11096 289 33725319 := by unfold blockSum; decide +kernel

private theorem block11385 : blockSum term 11385 289 29563053 := by unfold blockSum; decide +kernel

private theorem block11674 : blockSum term 11674 289 37714317 := by unfold blockSum; decide +kernel

private theorem block11963 : blockSum term 11963 289 32540183 := by unfold blockSum; decide +kernel

private theorem block12252 : blockSum term 12252 289 34996702 := by unfold blockSum; decide +kernel

private theorem block12541 : blockSum term 12541 289 34271674 := by unfold blockSum; decide +kernel

private theorem block12830 : blockSum term 12830 289 30486569 := by unfold blockSum; decide +kernel

private theorem block13119 : blockSum term 13119 289 28895477 := by unfold blockSum; decide +kernel

private theorem block13408 : blockSum term 13408 289 29265960 := by unfold blockSum; decide +kernel

private theorem block13697 : blockSum term 13697 289 29682360 := by unfold blockSum; decide +kernel

private theorem block13986 : blockSum term 13986 289 23478952 := by unfold blockSum; decide +kernel

private theorem block14275 : blockSum term 14275 289 30351048 := by unfold blockSum; decide +kernel

private theorem block14564 : blockSum term 14564 289 28887913 := by unfold blockSum; decide +kernel

private theorem block14853 : blockSum term 14853 289 25720989 := by unfold blockSum; decide +kernel

private theorem block15142 : blockSum term 15142 289 28752585 := by unfold blockSum; decide +kernel

private theorem block15431 : blockSum term 15431 289 24843026 := by unfold blockSum; decide +kernel

private theorem block15720 : blockSum term 15720 289 27800121 := by unfold blockSum; decide +kernel

private theorem block16009 : blockSum term 16009 289 22353606 := by unfold blockSum; decide +kernel

private theorem block16298 : blockSum term 16298 289 22794106 := by unfold blockSum; decide +kernel

private theorem block16587 : blockSum term 16587 289 20834511 := by unfold blockSum; decide +kernel

private theorem block16876 : blockSum term 16876 289 24448080 := by unfold blockSum; decide +kernel

private theorem block17165 : blockSum term 17165 289 24036970 := by unfold blockSum; decide +kernel

private theorem block17454 : blockSum term 17454 289 22158336 := by unfold blockSum; decide +kernel

private theorem block17743 : blockSum term 17743 289 21811671 := by unfold blockSum; decide +kernel

private theorem block18032 : blockSum term 18032 289 25930099 := by unfold blockSum; decide +kernel

private theorem block18321 : blockSum term 18321 289 20443844 := by unfold blockSum; decide +kernel

private theorem block18610 : blockSum term 18610 289 15116223 := by unfold blockSum; decide +kernel

private theorem block18899 : blockSum term 18899 289 19151590 := by unfold blockSum; decide +kernel

private theorem block19188 : blockSum term 19188 289 23052831 := by unfold blockSum; decide +kernel

private theorem block19477 : blockSum term 19477 289 19992288 := by unfold blockSum; decide +kernel

private theorem block19766 : blockSum term 19766 289 20386657 := by unfold blockSum; decide +kernel

private theorem block20055 : blockSum term 20055 289 19460877 := by unfold blockSum; decide +kernel

private theorem block20344 : blockSum term 20344 289 18548708 := by unfold blockSum; decide +kernel

private theorem block20633 : blockSum term 20633 289 18292221 := by unfold blockSum; decide +kernel

private theorem block20922 : blockSum term 20922 289 19993505 := by unfold blockSum; decide +kernel

private theorem block21211 : blockSum term 21211 289 17822247 := by unfold blockSum; decide +kernel

private theorem block21500 : blockSum term 21500 289 20126169 := by unfold blockSum; decide +kernel

private theorem block21789 : blockSum term 21789 289 18624856 := by unfold blockSum; decide +kernel

private theorem block22078 : blockSum term 22078 289 17186952 := by unfold blockSum; decide +kernel

private theorem block22367 : blockSum term 22367 289 17572539 := by unfold blockSum; decide +kernel

private theorem block22656 : blockSum term 22656 289 17368771 := by unfold blockSum; decide +kernel

private theorem block22945 : blockSum term 22945 289 18937170 := by unfold blockSum; decide +kernel

private theorem block23234 : blockSum term 23234 289 12873531 := by unfold blockSum; decide +kernel

private theorem block23523 : blockSum term 23523 289 19088277 := by unfold blockSum; decide +kernel

private theorem block23812 : blockSum term 23812 289 19432001 := by unfold blockSum; decide +kernel

private theorem block24101 : blockSum term 24101 289 14703318 := by unfold blockSum; decide +kernel

private theorem block24390 : blockSum term 24390 289 13976606 := by unfold blockSum; decide +kernel

private theorem block24679 : blockSum term 24679 289 14368410 := by unfold blockSum; decide +kernel

private theorem block24968 : blockSum term 24968 289 15850475 := by unfold blockSum; decide +kernel

private theorem block25257 : blockSum term 25257 289 14063446 := by unfold blockSum; decide +kernel

private theorem block25546 : blockSum term 25546 289 15524344 := by unfold blockSum; decide +kernel

private theorem block25835 : blockSum term 25835 289 15886693 := by unfold blockSum; decide +kernel

private theorem block26124 : blockSum term 26124 289 15194465 := by unfold blockSum; decide +kernel

private theorem block26413 : blockSum term 26413 289 14517753 := by unfold blockSum; decide +kernel

private theorem block26702 : blockSum term 26702 289 15917010 := by unfold blockSum; decide +kernel

private theorem block26991 : blockSum term 26991 289 13215372 := by unfold blockSum; decide +kernel

private theorem block27280 : blockSum term 27280 289 12074659 := by unfold blockSum; decide +kernel

private theorem block27569 : blockSum term 27569 289 15933643 := by unfold blockSum; decide +kernel

private theorem block27858 : blockSum term 27858 289 13320711 := by unfold blockSum; decide +kernel

private theorem block28147 : blockSum term 28147 289 12213627 := by unfold blockSum; decide +kernel

private theorem block28436 : blockSum term 28436 289 16934670 := by unfold blockSum; decide +kernel

private theorem block28725 : blockSum term 28725 289 11991217 := by unfold blockSum; decide +kernel

private theorem block29014 : blockSum term 29014 289 13776988 := by unfold blockSum; decide +kernel

private theorem block29303 : blockSum term 29303 289 13648008 := by unfold blockSum; decide +kernel

private theorem block29592 : blockSum term 29592 289 11651074 := by unfold blockSum; decide +kernel

private theorem block29881 : blockSum term 29881 289 12001823 := by unfold blockSum; decide +kernel

private theorem block30170 : blockSum term 30170 289 11447973 := by unfold blockSum; decide +kernel

private theorem block30459 : blockSum term 30459 289 12250649 := by unfold blockSum; decide +kernel

private theorem block30748 : blockSum term 30748 289 12593943 := by unfold blockSum; decide +kernel

private theorem block31037 : blockSum term 31037 289 14707215 := by unfold blockSum; decide +kernel

private theorem block31326 : blockSum term 31326 289 11044459 := by unfold blockSum; decide +kernel

private theorem block31615 : blockSum term 31615 289 10952753 := by unfold blockSum; decide +kernel

private theorem block31904 : blockSum term 31904 289 12154019 := by unfold blockSum; decide +kernel

private theorem block32193 : blockSum term 32193 289 13348993 := by unfold blockSum; decide +kernel

private theorem block32482 : blockSum term 32482 289 11536559 := by unfold blockSum; decide +kernel

private theorem block32771 : blockSum term 32771 289 13551894 := by unfold blockSum; decide +kernel

private theorem block33060 : blockSum term 33060 289 11338901 := by unfold blockSum; decide +kernel

private theorem block33349 : blockSum term 33349 289 14156142 := by unfold blockSum; decide +kernel

private theorem block33638 : blockSum term 33638 289 11153561 := by unfold blockSum; decide +kernel

private theorem block33927 : blockSum term 33927 289 9426242 := by unfold blockSum; decide +kernel

private theorem block34216 : blockSum term 34216 289 12605804 := by unfold blockSum; decide +kernel

private theorem block34505 : blockSum term 34505 289 11698794 := by unfold blockSum; decide +kernel

private theorem block34794 : blockSum term 34794 289 9604376 := by unfold blockSum; decide +kernel

private theorem block35083 : blockSum term 35083 289 11120921 := by unfold blockSum; decide +kernel

private theorem block35372 : blockSum term 35372 289 10248869 := by unfold blockSum; decide +kernel

private theorem block35661 : blockSum term 35661 289 9382458 := by unfold blockSum; decide +kernel

private theorem block35950 : blockSum term 35950 289 10870514 := by unfold blockSum; decide +kernel

private theorem block36239 : blockSum term 36239 289 10399734 := by unfold blockSum; decide +kernel

private theorem block36528 : blockSum term 36528 289 12232461 := by unfold blockSum; decide +kernel

private theorem block36817 : blockSum term 36817 289 11005723 := by unfold blockSum; decide +kernel

private theorem block37106 : blockSum term 37106 289 9791688 := by unfold blockSum; decide +kernel

private theorem block37395 : blockSum term 37395 289 11591747 := by unfold blockSum; decide +kernel

private theorem block37684 : blockSum term 37684 289 8536541 := by unfold blockSum; decide +kernel

private theorem block37973 : blockSum term 37973 289 9212189 := by unfold blockSum; decide +kernel

private theorem block38262 : blockSum term 38262 289 8055851 := by unfold blockSum; decide +kernel

private theorem block38551 : blockSum term 38551 289 11627450 := by unfold blockSum; decide +kernel

private theorem block38840 : blockSum term 38840 289 9739429 := by unfold blockSum; decide +kernel

private theorem block39129 : blockSum term 39129 289 10747381 := by unfold blockSum; decide +kernel

private theorem block39418 : blockSum term 39418 289 8537771 := by unfold blockSum; decide +kernel

private theorem block39707 : blockSum term 39707 289 10599251 := by unfold blockSum; decide +kernel

private theorem block39996 : blockSum term 39996 289 9472159 := by unfold blockSum; decide +kernel

private theorem block40285 : blockSum term 40285 289 7662729 := by unfold blockSum; decide +kernel

private theorem block40574 : blockSum term 40574 289 9342809 := by unfold blockSum; decide +kernel

private theorem block40863 : blockSum term 40863 289 9282085 := by unfold blockSum; decide +kernel

private theorem block41152 : blockSum term 41152 289 9565835 := by unfold blockSum; decide +kernel

private theorem block41441 : blockSum term 41441 289 10176460 := by unfold blockSum; decide +kernel

private theorem block41730 : blockSum term 41730 289 10105629 := by unfold blockSum; decide +kernel

private theorem block42019 : blockSum term 42019 289 9705838 := by unfold blockSum; decide +kernel

private theorem block42308 : blockSum term 42308 289 10309761 := by unfold blockSum; decide +kernel

private theorem block42597 : blockSum term 42597 289 9581031 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem after_cut : blockSum term 5895 36991 2727436055 := (join_sums term (lo:=5895) (a:=18495) (b:=18496) (join_sums term (lo:=5895) (a:=9247) (b:=9248) (join_sums term (lo:=5895) (a:=4623) (b:=4624) (join_sums term (lo:=5895) (a:=2311) (b:=2312) (join_sums term (lo:=5895) (a:=1155) (b:=1156) (join_sums term (lo:=5895) (a:=577) (b:=578) (join_sums term (lo:=5895) (a:=288) (b:=289) block5895 block6183) (join_sums term (lo:=6472) (a:=289) (b:=289) block6472 block6761)) (join_sums term (lo:=7050) (a:=578) (b:=578) (join_sums term (lo:=7050) (a:=289) (b:=289) block7050 block7339) (join_sums term (lo:=7628) (a:=289) (b:=289) block7628 block7917))) (join_sums term (lo:=8206) (a:=1156) (b:=1156) (join_sums term (lo:=8206) (a:=578) (b:=578) (join_sums term (lo:=8206) (a:=289) (b:=289) block8206 block8495) (join_sums term (lo:=8784) (a:=289) (b:=289) block8784 block9073)) (join_sums term (lo:=9362) (a:=578) (b:=578) (join_sums term (lo:=9362) (a:=289) (b:=289) block9362 block9651) (join_sums term (lo:=9940) (a:=289) (b:=289) block9940 block10229)))) (join_sums term (lo:=10518) (a:=2312) (b:=2312) (join_sums term (lo:=10518) (a:=1156) (b:=1156) (join_sums term (lo:=10518) (a:=578) (b:=578) (join_sums term (lo:=10518) (a:=289) (b:=289) block10518 block10807) (join_sums term (lo:=11096) (a:=289) (b:=289) block11096 block11385)) (join_sums term (lo:=11674) (a:=578) (b:=578) (join_sums term (lo:=11674) (a:=289) (b:=289) block11674 block11963) (join_sums term (lo:=12252) (a:=289) (b:=289) block12252 block12541))) (join_sums term (lo:=12830) (a:=1156) (b:=1156) (join_sums term (lo:=12830) (a:=578) (b:=578) (join_sums term (lo:=12830) (a:=289) (b:=289) block12830 block13119) (join_sums term (lo:=13408) (a:=289) (b:=289) block13408 block13697)) (join_sums term (lo:=13986) (a:=578) (b:=578) (join_sums term (lo:=13986) (a:=289) (b:=289) block13986 block14275) (join_sums term (lo:=14564) (a:=289) (b:=289) block14564 block14853))))) (join_sums term (lo:=15142) (a:=4624) (b:=4624) (join_sums term (lo:=15142) (a:=2312) (b:=2312) (join_sums term (lo:=15142) (a:=1156) (b:=1156) (join_sums term (lo:=15142) (a:=578) (b:=578) (join_sums term (lo:=15142) (a:=289) (b:=289) block15142 block15431) (join_sums term (lo:=15720) (a:=289) (b:=289) block15720 block16009)) (join_sums term (lo:=16298) (a:=578) (b:=578) (join_sums term (lo:=16298) (a:=289) (b:=289) block16298 block16587) (join_sums term (lo:=16876) (a:=289) (b:=289) block16876 block17165))) (join_sums term (lo:=17454) (a:=1156) (b:=1156) (join_sums term (lo:=17454) (a:=578) (b:=578) (join_sums term (lo:=17454) (a:=289) (b:=289) block17454 block17743) (join_sums term (lo:=18032) (a:=289) (b:=289) block18032 block18321)) (join_sums term (lo:=18610) (a:=578) (b:=578) (join_sums term (lo:=18610) (a:=289) (b:=289) block18610 block18899) (join_sums term (lo:=19188) (a:=289) (b:=289) block19188 block19477)))) (join_sums term (lo:=19766) (a:=2312) (b:=2312) (join_sums term (lo:=19766) (a:=1156) (b:=1156) (join_sums term (lo:=19766) (a:=578) (b:=578) (join_sums term (lo:=19766) (a:=289) (b:=289) block19766 block20055) (join_sums term (lo:=20344) (a:=289) (b:=289) block20344 block20633)) (join_sums term (lo:=20922) (a:=578) (b:=578) (join_sums term (lo:=20922) (a:=289) (b:=289) block20922 block21211) (join_sums term (lo:=21500) (a:=289) (b:=289) block21500 block21789))) (join_sums term (lo:=22078) (a:=1156) (b:=1156) (join_sums term (lo:=22078) (a:=578) (b:=578) (join_sums term (lo:=22078) (a:=289) (b:=289) block22078 block22367) (join_sums term (lo:=22656) (a:=289) (b:=289) block22656 block22945)) (join_sums term (lo:=23234) (a:=578) (b:=578) (join_sums term (lo:=23234) (a:=289) (b:=289) block23234 block23523) (join_sums term (lo:=23812) (a:=289) (b:=289) block23812 block24101)))))) (join_sums term (lo:=24390) (a:=9248) (b:=9248) (join_sums term (lo:=24390) (a:=4624) (b:=4624) (join_sums term (lo:=24390) (a:=2312) (b:=2312) (join_sums term (lo:=24390) (a:=1156) (b:=1156) (join_sums term (lo:=24390) (a:=578) (b:=578) (join_sums term (lo:=24390) (a:=289) (b:=289) block24390 block24679) (join_sums term (lo:=24968) (a:=289) (b:=289) block24968 block25257)) (join_sums term (lo:=25546) (a:=578) (b:=578) (join_sums term (lo:=25546) (a:=289) (b:=289) block25546 block25835) (join_sums term (lo:=26124) (a:=289) (b:=289) block26124 block26413))) (join_sums term (lo:=26702) (a:=1156) (b:=1156) (join_sums term (lo:=26702) (a:=578) (b:=578) (join_sums term (lo:=26702) (a:=289) (b:=289) block26702 block26991) (join_sums term (lo:=27280) (a:=289) (b:=289) block27280 block27569)) (join_sums term (lo:=27858) (a:=578) (b:=578) (join_sums term (lo:=27858) (a:=289) (b:=289) block27858 block28147) (join_sums term (lo:=28436) (a:=289) (b:=289) block28436 block28725)))) (join_sums term (lo:=29014) (a:=2312) (b:=2312) (join_sums term (lo:=29014) (a:=1156) (b:=1156) (join_sums term (lo:=29014) (a:=578) (b:=578) (join_sums term (lo:=29014) (a:=289) (b:=289) block29014 block29303) (join_sums term (lo:=29592) (a:=289) (b:=289) block29592 block29881)) (join_sums term (lo:=30170) (a:=578) (b:=578) (join_sums term (lo:=30170) (a:=289) (b:=289) block30170 block30459) (join_sums term (lo:=30748) (a:=289) (b:=289) block30748 block31037))) (join_sums term (lo:=31326) (a:=1156) (b:=1156) (join_sums term (lo:=31326) (a:=578) (b:=578) (join_sums term (lo:=31326) (a:=289) (b:=289) block31326 block31615) (join_sums term (lo:=31904) (a:=289) (b:=289) block31904 block32193)) (join_sums term (lo:=32482) (a:=578) (b:=578) (join_sums term (lo:=32482) (a:=289) (b:=289) block32482 block32771) (join_sums term (lo:=33060) (a:=289) (b:=289) block33060 block33349))))) (join_sums term (lo:=33638) (a:=4624) (b:=4624) (join_sums term (lo:=33638) (a:=2312) (b:=2312) (join_sums term (lo:=33638) (a:=1156) (b:=1156) (join_sums term (lo:=33638) (a:=578) (b:=578) (join_sums term (lo:=33638) (a:=289) (b:=289) block33638 block33927) (join_sums term (lo:=34216) (a:=289) (b:=289) block34216 block34505)) (join_sums term (lo:=34794) (a:=578) (b:=578) (join_sums term (lo:=34794) (a:=289) (b:=289) block34794 block35083) (join_sums term (lo:=35372) (a:=289) (b:=289) block35372 block35661))) (join_sums term (lo:=35950) (a:=1156) (b:=1156) (join_sums term (lo:=35950) (a:=578) (b:=578) (join_sums term (lo:=35950) (a:=289) (b:=289) block35950 block36239) (join_sums term (lo:=36528) (a:=289) (b:=289) block36528 block36817)) (join_sums term (lo:=37106) (a:=578) (b:=578) (join_sums term (lo:=37106) (a:=289) (b:=289) block37106 block37395) (join_sums term (lo:=37684) (a:=289) (b:=289) block37684 block37973)))) (join_sums term (lo:=38262) (a:=2312) (b:=2312) (join_sums term (lo:=38262) (a:=1156) (b:=1156) (join_sums term (lo:=38262) (a:=578) (b:=578) (join_sums term (lo:=38262) (a:=289) (b:=289) block38262 block38551) (join_sums term (lo:=38840) (a:=289) (b:=289) block38840 block39129)) (join_sums term (lo:=39418) (a:=578) (b:=578) (join_sums term (lo:=39418) (a:=289) (b:=289) block39418 block39707) (join_sums term (lo:=39996) (a:=289) (b:=289) block39996 block40285))) (join_sums term (lo:=40574) (a:=1156) (b:=1156) (join_sums term (lo:=40574) (a:=578) (b:=578) (join_sums term (lo:=40574) (a:=289) (b:=289) block40574 block40863) (join_sums term (lo:=41152) (a:=289) (b:=289) block41152 block41441)) (join_sums term (lo:=41730) (a:=578) (b:=578) (join_sums term (lo:=41730) (a:=289) (b:=289) block41730 block42019) (join_sums term (lo:=42308) (a:=289) (b:=289) block42308 block42597)))))))

private theorem rows : blockSum term 0 42886 2727436055 :=
  join_sums term (lo:=0) (a:=5895) (b:=36991) before after_cut

theorem exact_lower_sum :
    (∑ p ∈ (Nat.primesLE 42885).filter (5894 < ·),
      (Nat.primeCounting (204778727327/p) - Nat.primeCounting (p-1))) = 2727436055 :=
  right_from_blocks tab prime SparsePrimeA204.fast_correct prime_ok (by decide) (by decide) rows

end SharedCorrectionLow25
