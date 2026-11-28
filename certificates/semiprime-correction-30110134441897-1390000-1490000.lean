import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 1,390,000 through 1,490,000

The sum covers 7,073 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From1390000To1490000

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


private abbrev term := contribution 30110134441897 1390000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 1390001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 1390000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r1390001 : blockSum term 1390001 390 32827032 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1390391 : blockSum term 1390391 391 39127739 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1390782 : blockSum term 1390782 390 37854717 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1391172 : blockSum term 1391172 391 35319831 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1391563 : blockSum term 1391563 390 30265796 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1391953 : blockSum term 1391953 391 25213150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1392344 : blockSum term 1392344 391 35288136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1392735 : blockSum term 1392735 391 35276715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1393126 : blockSum term 1393126 390 34007083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1393516 : blockSum term 1393516 391 33996203 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1393907 : blockSum term 1393907 390 41539674 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1394297 : blockSum term 1394297 391 33975230 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1394688 : blockSum term 1394688 390 37738369 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1395078 : blockSum term 1395078 391 30181498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1395469 : blockSum term 1395469 391 40229412 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1395860 : blockSum term 1395860 391 40216721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1396251 : blockSum term 1396251 390 35178833 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1396641 : blockSum term 1396641 391 41448279 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1397032 : blockSum term 1397032 390 36414265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1397422 : blockSum term 1397422 391 33892260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1397813 : blockSum term 1397813 390 41409918 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1398203 : blockSum term 1398203 391 43906597 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1398594 : blockSum term 1398594 391 31352083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1398985 : blockSum term 1398985 391 37610693 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1399376 : blockSum term 1399376 390 47626551 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1399766 : blockSum term 1399766 391 33829450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1400157 : blockSum term 1400157 390 31314292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1400547 : blockSum term 1400547 391 31304555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1400938 : blockSum term 1400938 390 31295723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1401328 : blockSum term 1401328 391 31286192 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1401719 : blockSum term 1401719 391 32528077 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1402110 : blockSum term 1402110 391 35018886 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1402501 : blockSum term 1402501 390 32507280 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1402891 : blockSum term 1402891 391 24997696 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1403282 : blockSum term 1403282 390 42483249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1403672 : blockSum term 1403672 391 34974892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1404063 : blockSum term 1404063 390 27471424 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1404453 : blockSum term 1404453 391 32456927 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1404844 : blockSum term 1404844 391 37438986 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1405235 : blockSum term 1405235 391 32437556 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1405626 : blockSum term 1405626 390 29933707 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1406016 : blockSum term 1406016 391 26184112 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1406407 : blockSum term 1406407 390 34901125 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1406797 : blockSum term 1406797 391 37382934 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1407188 : blockSum term 1407188 390 41108192 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1407578 : blockSum term 1407578 391 32379108 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1407969 : blockSum term 1407969 391 29878950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1408360 : blockSum term 1408360 391 36091798 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1408751 : blockSum term 1408751 390 34837152 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1409141 : blockSum term 1409141 391 33582488 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1409532 : blockSum term 1409532 390 36059129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1409922 : blockSum term 1409922 391 34804439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1410313 : blockSum term 1410313 390 29824357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1410703 : blockSum term 1410703 391 39753705 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1411094 : blockSum term 1411094 391 32289846 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1411485 : blockSum term 1411485 391 33521506 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1411876 : blockSum term 1411876 390 37234832 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1412266 : blockSum term 1412266 391 40946003 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1412657 : blockSum term 1412657 390 40933280 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1413047 : blockSum term 1413047 391 28521255 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1413438 : blockSum term 1413438 390 35950709 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1413828 : blockSum term 1413828 391 26025127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1414219 : blockSum term 1414219 391 29734142 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1414610 : blockSum term 1414610 391 26009509 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1415001 : blockSum term 1415001 390 32191647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1415391 : blockSum term 1415391 391 27230626 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1415782 : blockSum term 1415782 390 39595638 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1416172 : blockSum term 1416172 391 24740142 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1416563 : blockSum term 1416563 390 33388652 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1416953 : blockSum term 1416953 391 33377702 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1417344 : blockSum term 1417344 391 34604770 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1417735 : blockSum term 1417735 391 37064396 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1418126 : blockSum term 1418126 390 28408301 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1418516 : blockSum term 1418516 391 27164824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1418907 : blockSum term 1418907 390 33328658 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1419297 : blockSum term 1419297 391 34552943 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1419688 : blockSum term 1419688 390 35776532 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1420078 : blockSum term 1420078 391 29599843 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1420469 : blockSum term 1420469 391 35754669 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1420860 : blockSum term 1420860 391 35743995 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1421251 : blockSum term 1421251 390 33268727 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1421641 : blockSum term 1421641 391 34491019 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1422032 : blockSum term 1422032 390 27091972 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1422422 : blockSum term 1422422 391 32007715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1422813 : blockSum term 1422813 390 33228618 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1423203 : blockSum term 1423203 391 44292589 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1423594 : blockSum term 1423594 391 34439073 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1423985 : blockSum term 1423985 391 28280639 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1424376 : blockSum term 1424376 390 36877184 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1424766 : blockSum term 1424766 391 38095228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1425157 : blockSum term 1425157 390 34397488 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1425547 : blockSum term 1425547 391 33158487 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1425938 : blockSum term 1425938 390 41742354 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1426328 : blockSum term 1426328 391 36820859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1426719 : blockSum term 1426719 391 36809844 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1427110 : blockSum term 1427110 391 30665006 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1427501 : blockSum term 1427501 390 34335858 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1427891 : blockSum term 1427891 391 36776793 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1428282 : blockSum term 1428282 390 22058892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1428672 : blockSum term 1428672 391 34305186 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1429063 : blockSum term 1429063 390 34294715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1429453 : blockSum term 1429453 391 40406444 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1429844 : blockSum term 1429844 391 28154230 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1430235 : blockSum term 1430235 391 28145537 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1430626 : blockSum term 1430626 390 41593224 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1431016 : blockSum term 1431016 391 39134145 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1431407 : blockSum term 1431407 390 35454940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1431797 : blockSum term 1431797 391 34222405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1432188 : blockSum term 1432188 390 34210984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1432578 : blockSum term 1432578 391 34201591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1432969 : blockSum term 1432969 391 36633357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1433360 : blockSum term 1433360 391 36620674 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1433751 : blockSum term 1433751 390 31728894 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1434141 : blockSum term 1434141 391 35379647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1434532 : blockSum term 1434532 390 37808157 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1434922 : blockSum term 1434922 391 41453501 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1435313 : blockSum term 1435313 390 34127274 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1435703 : blockSum term 1435703 391 30461805 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1436094 : blockSum term 1436094 391 37761959 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1436485 : blockSum term 1436485 391 26790934 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1436876 : blockSum term 1436876 390 34087006 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1437266 : blockSum term 1437266 391 36511222 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1437657 : blockSum term 1437657 390 32850455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1438047 : blockSum term 1438047 391 34058302 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1438438 : blockSum term 1438438 390 29182880 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1438828 : blockSum term 1438828 391 41330900 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1439219 : blockSum term 1439219 391 34026906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1439610 : blockSum term 1439610 391 30371658 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1440001 : blockSum term 1440001 390 24290012 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1440391 : blockSum term 1440391 391 40067339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1440782 : blockSum term 1440782 390 32772492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1441172 : blockSum term 1441172 391 35189711 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1441563 : blockSum term 1441563 390 35179311 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1441953 : blockSum term 1441953 391 30317114 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1442344 : blockSum term 1442344 391 32732609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1442735 : blockSum term 1442735 391 31510894 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1443126 : blockSum term 1443126 390 32713247 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1443516 : blockSum term 1443516 391 32703898 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1443907 : blockSum term 1443907 390 30271833 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1444297 : blockSum term 1444297 391 29051693 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1444688 : blockSum term 1444688 390 39934122 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1445078 : blockSum term 1445078 391 35082716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1445469 : blockSum term 1445469 391 30235891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1445860 : blockSum term 1445860 391 41108192 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1446251 : blockSum term 1446251 390 30217897 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1446641 : blockSum term 1446641 391 35041978 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1447032 : blockSum term 1447032 390 39863592 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1447422 : blockSum term 1447422 391 31398832 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1447813 : blockSum term 1447813 390 32596993 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1448203 : blockSum term 1448203 391 25345453 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1448594 : blockSum term 1448594 391 31370620 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1448985 : blockSum term 1448985 391 32567831 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1449376 : blockSum term 1449376 390 34969734 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1449766 : blockSum term 1449766 391 34959566 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1450157 : blockSum term 1450157 390 37358950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1450547 : blockSum term 1450547 391 37347479 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1450938 : blockSum term 1450938 390 31314659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1451328 : blockSum term 1451328 391 26488915 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1451719 : blockSum term 1451719 391 27685936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1452110 : blockSum term 1452110 391 39710390 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1452501 : blockSum term 1452501 390 32480594 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1452891 : blockSum term 1452891 391 30066041 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1453282 : blockSum term 1453282 390 36068221 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1453672 : blockSum term 1453672 391 34854729 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1454063 : blockSum term 1454063 390 30038498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1454453 : blockSum term 1454453 391 37236631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1454844 : blockSum term 1454844 391 45630775 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1455235 : blockSum term 1455235 391 33613107 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1455626 : blockSum term 1455626 390 38401855 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1456016 : blockSum term 1456016 391 27593018 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1456407 : blockSum term 1456407 390 29983092 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1456797 : blockSum term 1456797 391 32371835 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1457188 : blockSum term 1457188 390 31164349 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1457578 : blockSum term 1457578 391 29956086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1457969 : blockSum term 1457969 391 33541452 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1458360 : blockSum term 1458360 391 37123945 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1458751 : blockSum term 1458751 390 23943891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1459141 : blockSum term 1459141 391 28724957 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1459532 : blockSum term 1459532 390 28716235 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1459922 : blockSum term 1459922 391 40669303 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1460313 : blockSum term 1460313 390 29894303 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1460703 : blockSum term 1460703 391 32276670 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1461094 : blockSum term 1461094 391 37047376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1461485 : blockSum term 1461485 391 39426703 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1461876 : blockSum term 1461876 390 37025998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1462266 : blockSum term 1462266 391 34625887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1462657 : blockSum term 1462657 390 32228872 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1463047 : blockSum term 1463047 391 28639921 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1463438 : blockSum term 1463438 390 31017921 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1463828 : blockSum term 1463828 391 34585547 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1464219 : blockSum term 1464219 391 33383290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1464610 : blockSum term 1464610 391 32180569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1465001 : blockSum term 1465001 390 34554658 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1465391 : blockSum term 1465391 391 39309138 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1465782 : blockSum term 1465782 390 33342742 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1466172 : blockSum term 1466172 391 33333285 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1466563 : blockSum term 1466563 390 33323689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1466953 : blockSum term 1466953 391 38072510 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1467344 : blockSum term 1467344 391 26167523 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1467735 : blockSum term 1467735 391 23781784 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1468126 : blockSum term 1468126 390 24962557 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1468516 : blockSum term 1468516 391 34462973 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1468907 : blockSum term 1468907 390 33264132 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1469297 : blockSum term 1469297 391 34441259 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1469688 : blockSum term 1469688 390 35618829 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1470078 : blockSum term 1470078 391 27299498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1470469 : blockSum term 1470469 391 23732508 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1470860 : blockSum term 1470860 391 28470918 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1471251 : blockSum term 1471251 390 41507139 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1471641 : blockSum term 1471641 391 32010773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1472032 : blockSum term 1472032 390 30815523 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1472422 : blockSum term 1472422 391 35545979 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1472813 : blockSum term 1472813 390 39088788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1473203 : blockSum term 1473203 391 30788205 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1473594 : blockSum term 1473594 391 30779378 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1473985 : blockSum term 1473985 391 36687650 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1474376 : blockSum term 1474376 390 27211651 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1474766 : blockSum term 1474766 391 26021394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1475157 : blockSum term 1475157 390 28379194 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1475547 : blockSum term 1475547 391 29552830 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1475938 : blockSum term 1475938 390 31907760 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1476328 : blockSum term 1476328 391 30717201 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1476719 : blockSum term 1476719 391 43699699 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1477110 : blockSum term 1477110 391 30699023 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1477501 : blockSum term 1477501 390 34231515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1477891 : blockSum term 1477891 391 38941216 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1478282 : blockSum term 1478282 390 28312590 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1478672 : blockSum term 1478672 391 36558711 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1479063 : blockSum term 1479063 390 35369516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1479453 : blockSum term 1479453 391 35358322 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1479844 : blockSum term 1479844 391 29457305 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1480235 : blockSum term 1480235 391 34159633 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1480626 : blockSum term 1480626 390 34150301 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1481016 : blockSum term 1481016 391 30608494 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1481407 : blockSum term 1481407 390 29422461 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1481797 : blockSum term 1481797 391 35297274 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1482188 : blockSum term 1482188 390 31757873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1482578 : blockSum term 1482578 391 35275773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1482969 : blockSum term 1482969 391 37615731 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1483360 : blockSum term 1483360 391 31729023 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1483751 : blockSum term 1483751 390 29370720 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1484141 : blockSum term 1484141 391 39932750 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1484532 : blockSum term 1484532 390 23483337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1484922 : blockSum term 1484922 391 31692690 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1485313 : blockSum term 1485313 390 24642928 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1485703 : blockSum term 1485703 391 29328935 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1486094 : blockSum term 1486094 391 34010906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1486485 : blockSum term 1486485 391 37517788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1486876 : blockSum term 1486876 390 32818487 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1487266 : blockSum term 1487266 391 31636853 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1487657 : blockSum term 1487657 390 29284576 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1488047 : blockSum term 1488047 391 30447330 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1488438 : blockSum term 1488438 390 32779364 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1488828 : blockSum term 1488828 391 36281207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1489219 : blockSum term 1489219 391 35101104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1489610 : blockSum term 1489610 391 35091490 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 1390001 100000 8594927953 := (join_sums term (lo:=1390001) (a:=50000) (b:=50000) (join_sums term (lo:=1390001) (a:=25000) (b:=25000) (join_sums term (lo:=1390001) (a:=12500) (b:=12500) (join_sums term (lo:=1390001) (a:=6250) (b:=6250) (join_sums term (lo:=1390001) (a:=3125) (b:=3125) (join_sums term (lo:=1390001) (a:=1562) (b:=1563) (join_sums term (lo:=1390001) (a:=781) (b:=781) (join_sums term (lo:=1390001) (a:=390) (b:=391) r1390001 r1390391) (join_sums term (lo:=1390782) (a:=390) (b:=391) r1390782 r1391172)) (join_sums term (lo:=1391563) (a:=781) (b:=782) (join_sums term (lo:=1391563) (a:=390) (b:=391) r1391563 r1391953) (join_sums term (lo:=1392344) (a:=391) (b:=391) r1392344 r1392735))) (join_sums term (lo:=1393126) (a:=1562) (b:=1563) (join_sums term (lo:=1393126) (a:=781) (b:=781) (join_sums term (lo:=1393126) (a:=390) (b:=391) r1393126 r1393516) (join_sums term (lo:=1393907) (a:=390) (b:=391) r1393907 r1394297)) (join_sums term (lo:=1394688) (a:=781) (b:=782) (join_sums term (lo:=1394688) (a:=390) (b:=391) r1394688 r1395078) (join_sums term (lo:=1395469) (a:=391) (b:=391) r1395469 r1395860)))) (join_sums term (lo:=1396251) (a:=3125) (b:=3125) (join_sums term (lo:=1396251) (a:=1562) (b:=1563) (join_sums term (lo:=1396251) (a:=781) (b:=781) (join_sums term (lo:=1396251) (a:=390) (b:=391) r1396251 r1396641) (join_sums term (lo:=1397032) (a:=390) (b:=391) r1397032 r1397422)) (join_sums term (lo:=1397813) (a:=781) (b:=782) (join_sums term (lo:=1397813) (a:=390) (b:=391) r1397813 r1398203) (join_sums term (lo:=1398594) (a:=391) (b:=391) r1398594 r1398985))) (join_sums term (lo:=1399376) (a:=1562) (b:=1563) (join_sums term (lo:=1399376) (a:=781) (b:=781) (join_sums term (lo:=1399376) (a:=390) (b:=391) r1399376 r1399766) (join_sums term (lo:=1400157) (a:=390) (b:=391) r1400157 r1400547)) (join_sums term (lo:=1400938) (a:=781) (b:=782) (join_sums term (lo:=1400938) (a:=390) (b:=391) r1400938 r1401328) (join_sums term (lo:=1401719) (a:=391) (b:=391) r1401719 r1402110))))) (join_sums term (lo:=1402501) (a:=6250) (b:=6250) (join_sums term (lo:=1402501) (a:=3125) (b:=3125) (join_sums term (lo:=1402501) (a:=1562) (b:=1563) (join_sums term (lo:=1402501) (a:=781) (b:=781) (join_sums term (lo:=1402501) (a:=390) (b:=391) r1402501 r1402891) (join_sums term (lo:=1403282) (a:=390) (b:=391) r1403282 r1403672)) (join_sums term (lo:=1404063) (a:=781) (b:=782) (join_sums term (lo:=1404063) (a:=390) (b:=391) r1404063 r1404453) (join_sums term (lo:=1404844) (a:=391) (b:=391) r1404844 r1405235))) (join_sums term (lo:=1405626) (a:=1562) (b:=1563) (join_sums term (lo:=1405626) (a:=781) (b:=781) (join_sums term (lo:=1405626) (a:=390) (b:=391) r1405626 r1406016) (join_sums term (lo:=1406407) (a:=390) (b:=391) r1406407 r1406797)) (join_sums term (lo:=1407188) (a:=781) (b:=782) (join_sums term (lo:=1407188) (a:=390) (b:=391) r1407188 r1407578) (join_sums term (lo:=1407969) (a:=391) (b:=391) r1407969 r1408360)))) (join_sums term (lo:=1408751) (a:=3125) (b:=3125) (join_sums term (lo:=1408751) (a:=1562) (b:=1563) (join_sums term (lo:=1408751) (a:=781) (b:=781) (join_sums term (lo:=1408751) (a:=390) (b:=391) r1408751 r1409141) (join_sums term (lo:=1409532) (a:=390) (b:=391) r1409532 r1409922)) (join_sums term (lo:=1410313) (a:=781) (b:=782) (join_sums term (lo:=1410313) (a:=390) (b:=391) r1410313 r1410703) (join_sums term (lo:=1411094) (a:=391) (b:=391) r1411094 r1411485))) (join_sums term (lo:=1411876) (a:=1562) (b:=1563) (join_sums term (lo:=1411876) (a:=781) (b:=781) (join_sums term (lo:=1411876) (a:=390) (b:=391) r1411876 r1412266) (join_sums term (lo:=1412657) (a:=390) (b:=391) r1412657 r1413047)) (join_sums term (lo:=1413438) (a:=781) (b:=782) (join_sums term (lo:=1413438) (a:=390) (b:=391) r1413438 r1413828) (join_sums term (lo:=1414219) (a:=391) (b:=391) r1414219 r1414610)))))) (join_sums term (lo:=1415001) (a:=12500) (b:=12500) (join_sums term (lo:=1415001) (a:=6250) (b:=6250) (join_sums term (lo:=1415001) (a:=3125) (b:=3125) (join_sums term (lo:=1415001) (a:=1562) (b:=1563) (join_sums term (lo:=1415001) (a:=781) (b:=781) (join_sums term (lo:=1415001) (a:=390) (b:=391) r1415001 r1415391) (join_sums term (lo:=1415782) (a:=390) (b:=391) r1415782 r1416172)) (join_sums term (lo:=1416563) (a:=781) (b:=782) (join_sums term (lo:=1416563) (a:=390) (b:=391) r1416563 r1416953) (join_sums term (lo:=1417344) (a:=391) (b:=391) r1417344 r1417735))) (join_sums term (lo:=1418126) (a:=1562) (b:=1563) (join_sums term (lo:=1418126) (a:=781) (b:=781) (join_sums term (lo:=1418126) (a:=390) (b:=391) r1418126 r1418516) (join_sums term (lo:=1418907) (a:=390) (b:=391) r1418907 r1419297)) (join_sums term (lo:=1419688) (a:=781) (b:=782) (join_sums term (lo:=1419688) (a:=390) (b:=391) r1419688 r1420078) (join_sums term (lo:=1420469) (a:=391) (b:=391) r1420469 r1420860)))) (join_sums term (lo:=1421251) (a:=3125) (b:=3125) (join_sums term (lo:=1421251) (a:=1562) (b:=1563) (join_sums term (lo:=1421251) (a:=781) (b:=781) (join_sums term (lo:=1421251) (a:=390) (b:=391) r1421251 r1421641) (join_sums term (lo:=1422032) (a:=390) (b:=391) r1422032 r1422422)) (join_sums term (lo:=1422813) (a:=781) (b:=782) (join_sums term (lo:=1422813) (a:=390) (b:=391) r1422813 r1423203) (join_sums term (lo:=1423594) (a:=391) (b:=391) r1423594 r1423985))) (join_sums term (lo:=1424376) (a:=1562) (b:=1563) (join_sums term (lo:=1424376) (a:=781) (b:=781) (join_sums term (lo:=1424376) (a:=390) (b:=391) r1424376 r1424766) (join_sums term (lo:=1425157) (a:=390) (b:=391) r1425157 r1425547)) (join_sums term (lo:=1425938) (a:=781) (b:=782) (join_sums term (lo:=1425938) (a:=390) (b:=391) r1425938 r1426328) (join_sums term (lo:=1426719) (a:=391) (b:=391) r1426719 r1427110))))) (join_sums term (lo:=1427501) (a:=6250) (b:=6250) (join_sums term (lo:=1427501) (a:=3125) (b:=3125) (join_sums term (lo:=1427501) (a:=1562) (b:=1563) (join_sums term (lo:=1427501) (a:=781) (b:=781) (join_sums term (lo:=1427501) (a:=390) (b:=391) r1427501 r1427891) (join_sums term (lo:=1428282) (a:=390) (b:=391) r1428282 r1428672)) (join_sums term (lo:=1429063) (a:=781) (b:=782) (join_sums term (lo:=1429063) (a:=390) (b:=391) r1429063 r1429453) (join_sums term (lo:=1429844) (a:=391) (b:=391) r1429844 r1430235))) (join_sums term (lo:=1430626) (a:=1562) (b:=1563) (join_sums term (lo:=1430626) (a:=781) (b:=781) (join_sums term (lo:=1430626) (a:=390) (b:=391) r1430626 r1431016) (join_sums term (lo:=1431407) (a:=390) (b:=391) r1431407 r1431797)) (join_sums term (lo:=1432188) (a:=781) (b:=782) (join_sums term (lo:=1432188) (a:=390) (b:=391) r1432188 r1432578) (join_sums term (lo:=1432969) (a:=391) (b:=391) r1432969 r1433360)))) (join_sums term (lo:=1433751) (a:=3125) (b:=3125) (join_sums term (lo:=1433751) (a:=1562) (b:=1563) (join_sums term (lo:=1433751) (a:=781) (b:=781) (join_sums term (lo:=1433751) (a:=390) (b:=391) r1433751 r1434141) (join_sums term (lo:=1434532) (a:=390) (b:=391) r1434532 r1434922)) (join_sums term (lo:=1435313) (a:=781) (b:=782) (join_sums term (lo:=1435313) (a:=390) (b:=391) r1435313 r1435703) (join_sums term (lo:=1436094) (a:=391) (b:=391) r1436094 r1436485))) (join_sums term (lo:=1436876) (a:=1562) (b:=1563) (join_sums term (lo:=1436876) (a:=781) (b:=781) (join_sums term (lo:=1436876) (a:=390) (b:=391) r1436876 r1437266) (join_sums term (lo:=1437657) (a:=390) (b:=391) r1437657 r1438047)) (join_sums term (lo:=1438438) (a:=781) (b:=782) (join_sums term (lo:=1438438) (a:=390) (b:=391) r1438438 r1438828) (join_sums term (lo:=1439219) (a:=391) (b:=391) r1439219 r1439610))))))) (join_sums term (lo:=1440001) (a:=25000) (b:=25000) (join_sums term (lo:=1440001) (a:=12500) (b:=12500) (join_sums term (lo:=1440001) (a:=6250) (b:=6250) (join_sums term (lo:=1440001) (a:=3125) (b:=3125) (join_sums term (lo:=1440001) (a:=1562) (b:=1563) (join_sums term (lo:=1440001) (a:=781) (b:=781) (join_sums term (lo:=1440001) (a:=390) (b:=391) r1440001 r1440391) (join_sums term (lo:=1440782) (a:=390) (b:=391) r1440782 r1441172)) (join_sums term (lo:=1441563) (a:=781) (b:=782) (join_sums term (lo:=1441563) (a:=390) (b:=391) r1441563 r1441953) (join_sums term (lo:=1442344) (a:=391) (b:=391) r1442344 r1442735))) (join_sums term (lo:=1443126) (a:=1562) (b:=1563) (join_sums term (lo:=1443126) (a:=781) (b:=781) (join_sums term (lo:=1443126) (a:=390) (b:=391) r1443126 r1443516) (join_sums term (lo:=1443907) (a:=390) (b:=391) r1443907 r1444297)) (join_sums term (lo:=1444688) (a:=781) (b:=782) (join_sums term (lo:=1444688) (a:=390) (b:=391) r1444688 r1445078) (join_sums term (lo:=1445469) (a:=391) (b:=391) r1445469 r1445860)))) (join_sums term (lo:=1446251) (a:=3125) (b:=3125) (join_sums term (lo:=1446251) (a:=1562) (b:=1563) (join_sums term (lo:=1446251) (a:=781) (b:=781) (join_sums term (lo:=1446251) (a:=390) (b:=391) r1446251 r1446641) (join_sums term (lo:=1447032) (a:=390) (b:=391) r1447032 r1447422)) (join_sums term (lo:=1447813) (a:=781) (b:=782) (join_sums term (lo:=1447813) (a:=390) (b:=391) r1447813 r1448203) (join_sums term (lo:=1448594) (a:=391) (b:=391) r1448594 r1448985))) (join_sums term (lo:=1449376) (a:=1562) (b:=1563) (join_sums term (lo:=1449376) (a:=781) (b:=781) (join_sums term (lo:=1449376) (a:=390) (b:=391) r1449376 r1449766) (join_sums term (lo:=1450157) (a:=390) (b:=391) r1450157 r1450547)) (join_sums term (lo:=1450938) (a:=781) (b:=782) (join_sums term (lo:=1450938) (a:=390) (b:=391) r1450938 r1451328) (join_sums term (lo:=1451719) (a:=391) (b:=391) r1451719 r1452110))))) (join_sums term (lo:=1452501) (a:=6250) (b:=6250) (join_sums term (lo:=1452501) (a:=3125) (b:=3125) (join_sums term (lo:=1452501) (a:=1562) (b:=1563) (join_sums term (lo:=1452501) (a:=781) (b:=781) (join_sums term (lo:=1452501) (a:=390) (b:=391) r1452501 r1452891) (join_sums term (lo:=1453282) (a:=390) (b:=391) r1453282 r1453672)) (join_sums term (lo:=1454063) (a:=781) (b:=782) (join_sums term (lo:=1454063) (a:=390) (b:=391) r1454063 r1454453) (join_sums term (lo:=1454844) (a:=391) (b:=391) r1454844 r1455235))) (join_sums term (lo:=1455626) (a:=1562) (b:=1563) (join_sums term (lo:=1455626) (a:=781) (b:=781) (join_sums term (lo:=1455626) (a:=390) (b:=391) r1455626 r1456016) (join_sums term (lo:=1456407) (a:=390) (b:=391) r1456407 r1456797)) (join_sums term (lo:=1457188) (a:=781) (b:=782) (join_sums term (lo:=1457188) (a:=390) (b:=391) r1457188 r1457578) (join_sums term (lo:=1457969) (a:=391) (b:=391) r1457969 r1458360)))) (join_sums term (lo:=1458751) (a:=3125) (b:=3125) (join_sums term (lo:=1458751) (a:=1562) (b:=1563) (join_sums term (lo:=1458751) (a:=781) (b:=781) (join_sums term (lo:=1458751) (a:=390) (b:=391) r1458751 r1459141) (join_sums term (lo:=1459532) (a:=390) (b:=391) r1459532 r1459922)) (join_sums term (lo:=1460313) (a:=781) (b:=782) (join_sums term (lo:=1460313) (a:=390) (b:=391) r1460313 r1460703) (join_sums term (lo:=1461094) (a:=391) (b:=391) r1461094 r1461485))) (join_sums term (lo:=1461876) (a:=1562) (b:=1563) (join_sums term (lo:=1461876) (a:=781) (b:=781) (join_sums term (lo:=1461876) (a:=390) (b:=391) r1461876 r1462266) (join_sums term (lo:=1462657) (a:=390) (b:=391) r1462657 r1463047)) (join_sums term (lo:=1463438) (a:=781) (b:=782) (join_sums term (lo:=1463438) (a:=390) (b:=391) r1463438 r1463828) (join_sums term (lo:=1464219) (a:=391) (b:=391) r1464219 r1464610)))))) (join_sums term (lo:=1465001) (a:=12500) (b:=12500) (join_sums term (lo:=1465001) (a:=6250) (b:=6250) (join_sums term (lo:=1465001) (a:=3125) (b:=3125) (join_sums term (lo:=1465001) (a:=1562) (b:=1563) (join_sums term (lo:=1465001) (a:=781) (b:=781) (join_sums term (lo:=1465001) (a:=390) (b:=391) r1465001 r1465391) (join_sums term (lo:=1465782) (a:=390) (b:=391) r1465782 r1466172)) (join_sums term (lo:=1466563) (a:=781) (b:=782) (join_sums term (lo:=1466563) (a:=390) (b:=391) r1466563 r1466953) (join_sums term (lo:=1467344) (a:=391) (b:=391) r1467344 r1467735))) (join_sums term (lo:=1468126) (a:=1562) (b:=1563) (join_sums term (lo:=1468126) (a:=781) (b:=781) (join_sums term (lo:=1468126) (a:=390) (b:=391) r1468126 r1468516) (join_sums term (lo:=1468907) (a:=390) (b:=391) r1468907 r1469297)) (join_sums term (lo:=1469688) (a:=781) (b:=782) (join_sums term (lo:=1469688) (a:=390) (b:=391) r1469688 r1470078) (join_sums term (lo:=1470469) (a:=391) (b:=391) r1470469 r1470860)))) (join_sums term (lo:=1471251) (a:=3125) (b:=3125) (join_sums term (lo:=1471251) (a:=1562) (b:=1563) (join_sums term (lo:=1471251) (a:=781) (b:=781) (join_sums term (lo:=1471251) (a:=390) (b:=391) r1471251 r1471641) (join_sums term (lo:=1472032) (a:=390) (b:=391) r1472032 r1472422)) (join_sums term (lo:=1472813) (a:=781) (b:=782) (join_sums term (lo:=1472813) (a:=390) (b:=391) r1472813 r1473203) (join_sums term (lo:=1473594) (a:=391) (b:=391) r1473594 r1473985))) (join_sums term (lo:=1474376) (a:=1562) (b:=1563) (join_sums term (lo:=1474376) (a:=781) (b:=781) (join_sums term (lo:=1474376) (a:=390) (b:=391) r1474376 r1474766) (join_sums term (lo:=1475157) (a:=390) (b:=391) r1475157 r1475547)) (join_sums term (lo:=1475938) (a:=781) (b:=782) (join_sums term (lo:=1475938) (a:=390) (b:=391) r1475938 r1476328) (join_sums term (lo:=1476719) (a:=391) (b:=391) r1476719 r1477110))))) (join_sums term (lo:=1477501) (a:=6250) (b:=6250) (join_sums term (lo:=1477501) (a:=3125) (b:=3125) (join_sums term (lo:=1477501) (a:=1562) (b:=1563) (join_sums term (lo:=1477501) (a:=781) (b:=781) (join_sums term (lo:=1477501) (a:=390) (b:=391) r1477501 r1477891) (join_sums term (lo:=1478282) (a:=390) (b:=391) r1478282 r1478672)) (join_sums term (lo:=1479063) (a:=781) (b:=782) (join_sums term (lo:=1479063) (a:=390) (b:=391) r1479063 r1479453) (join_sums term (lo:=1479844) (a:=391) (b:=391) r1479844 r1480235))) (join_sums term (lo:=1480626) (a:=1562) (b:=1563) (join_sums term (lo:=1480626) (a:=781) (b:=781) (join_sums term (lo:=1480626) (a:=390) (b:=391) r1480626 r1481016) (join_sums term (lo:=1481407) (a:=390) (b:=391) r1481407 r1481797)) (join_sums term (lo:=1482188) (a:=781) (b:=782) (join_sums term (lo:=1482188) (a:=390) (b:=391) r1482188 r1482578) (join_sums term (lo:=1482969) (a:=391) (b:=391) r1482969 r1483360)))) (join_sums term (lo:=1483751) (a:=3125) (b:=3125) (join_sums term (lo:=1483751) (a:=1562) (b:=1563) (join_sums term (lo:=1483751) (a:=781) (b:=781) (join_sums term (lo:=1483751) (a:=390) (b:=391) r1483751 r1484141) (join_sums term (lo:=1484532) (a:=390) (b:=391) r1484532 r1484922)) (join_sums term (lo:=1485313) (a:=781) (b:=782) (join_sums term (lo:=1485313) (a:=390) (b:=391) r1485313 r1485703) (join_sums term (lo:=1486094) (a:=391) (b:=391) r1486094 r1486485))) (join_sums term (lo:=1486876) (a:=1562) (b:=1563) (join_sums term (lo:=1486876) (a:=781) (b:=781) (join_sums term (lo:=1486876) (a:=390) (b:=391) r1486876 r1487266) (join_sums term (lo:=1487657) (a:=390) (b:=391) r1487657 r1488047)) (join_sums term (lo:=1488438) (a:=781) (b:=782) (join_sums term (lo:=1488438) (a:=390) (b:=391) r1488438 r1488828) (join_sums term (lo:=1489219) (a:=391) (b:=391) r1489219 r1489610))))))))

private theorem rows : blockSum term 0 1490001 8594927953 :=
  join_sums term (lo:=0) (a:=1390001) (b:=100000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 1490000).filter (1390000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=8594927953 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From1390000To1490000
