import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 1,290,000 through 1,390,000

The sum covers 7,053 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From1290000To1390000

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


private abbrev term := contribution 30110134441897 1290000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 1290001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 1290000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r1290001 : blockSum term 1290001 390 35589564 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1290391 : blockSum term 1290391 391 35578752 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1290782 : blockSum term 1290782 390 34198721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1291172 : blockSum term 1291172 391 39657974 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1291563 : blockSum term 1291563 390 25973895 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1291953 : blockSum term 1291953 391 40998376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1292344 : blockSum term 1292344 391 42349985 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1292735 : blockSum term 1292735 391 30046024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1293126 : blockSum term 1293126 390 40958735 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1293516 : blockSum term 1293516 391 32755897 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1293907 : blockSum term 1293907 390 40932096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1294297 : blockSum term 1294297 391 35462136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1294688 : blockSum term 1294688 390 32723043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1295078 : blockSum term 1295078 391 39528493 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1295469 : blockSum term 1295469 391 39515624 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1295860 : blockSum term 1295860 391 35416346 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1296251 : blockSum term 1296251 390 42212840 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1296641 : blockSum term 1296641 391 35392839 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1297032 : blockSum term 1297032 390 48989163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1297422 : blockSum term 1297422 391 38091672 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1297813 : blockSum term 1297813 390 32638320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1298203 : blockSum term 1298203 391 25831468 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1298594 : blockSum term 1298594 391 33978152 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1298985 : blockSum term 1298985 391 43478285 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1299376 : blockSum term 1299376 390 32598589 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1299766 : blockSum term 1299766 391 43449188 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1300157 : blockSum term 1300157 390 35290639 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1300547 : blockSum term 1300547 391 36636623 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1300938 : blockSum term 1300938 390 40694082 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1301328 : blockSum term 1301328 391 39324792 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1301719 : blockSum term 1301719 391 35245109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1302110 : blockSum term 1302110 391 43365748 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1302501 : blockSum term 1302501 390 27094548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1302891 : blockSum term 1302891 391 46045919 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1303282 : blockSum term 1303282 390 40615764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1303672 : blockSum term 1303672 391 37895936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1304063 : blockSum term 1304063 390 37884781 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1304453 : blockSum term 1304453 391 32462148 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1304844 : blockSum term 1304844 391 32451585 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1305235 : blockSum term 1305235 391 36495782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1305626 : blockSum term 1305626 390 35133745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1306016 : blockSum term 1306016 391 43226872 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1306407 : blockSum term 1306407 390 36461241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1306797 : blockSum term 1306797 391 41849105 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1307188 : blockSum term 1307188 390 32388794 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1307578 : blockSum term 1307578 391 32378870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1307969 : blockSum term 1307969 391 33716553 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1308360 : blockSum term 1308360 391 43143160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1308751 : blockSum term 1308751 390 36389300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1309141 : blockSum term 1309141 391 32336272 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1309532 : blockSum term 1309532 390 43100418 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1309922 : blockSum term 1309922 391 41740651 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1310313 : blockSum term 1310313 390 40381204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1310703 : blockSum term 1310703 391 34985716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1311094 : blockSum term 1311094 391 43045641 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1311485 : blockSum term 1311485 391 37652879 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1311876 : blockSum term 1311876 390 30918965 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1312266 : blockSum term 1312266 391 37628955 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1312657 : blockSum term 1312657 390 37617462 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1313047 : blockSum term 1313047 391 30889733 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1313438 : blockSum term 1313438 390 34907862 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1313828 : blockSum term 1313828 391 42949305 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1314219 : blockSum term 1314219 391 34884734 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1314610 : blockSum term 1314610 391 26826234 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1315001 : blockSum term 1315001 390 34863360 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1315391 : blockSum term 1315391 391 42894596 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1315782 : blockSum term 1315782 390 33501189 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1316172 : blockSum term 1316172 391 37508510 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1316563 : blockSum term 1316563 390 37496817 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1316953 : blockSum term 1316953 391 40161936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1317344 : blockSum term 1317344 391 41487534 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1317735 : blockSum term 1317735 391 37460172 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1318126 : blockSum term 1318126 390 34772947 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1318516 : blockSum term 1318516 391 40108540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1318907 : blockSum term 1318907 390 36087812 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1319297 : blockSum term 1319297 391 30731930 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1319688 : blockSum term 1319688 390 36065443 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1320078 : blockSum term 1320078 391 41394400 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1320469 : blockSum term 1320469 391 21357459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1320860 : blockSum term 1320860 391 40034452 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1321251 : blockSum term 1321251 390 48026088 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1321641 : blockSum term 1321641 391 40008701 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1322032 : blockSum term 1322032 390 43995109 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1322422 : blockSum term 1322422 391 39984098 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1322813 : blockSum term 1322813 390 47964635 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1323203 : blockSum term 1323203 391 37293250 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1323594 : blockSum term 1323594 391 31955968 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1323985 : blockSum term 1323985 391 31946379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1324376 : blockSum term 1324376 390 42580531 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1324766 : blockSum term 1324766 391 33255057 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1325157 : blockSum term 1325157 390 33245056 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1325547 : blockSum term 1325547 391 31905649 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1325938 : blockSum term 1325938 390 41197569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1326328 : blockSum term 1326328 391 41184100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1326719 : blockSum term 1326719 391 38514686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1327110 : blockSum term 1327110 391 33191656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1327501 : blockSum term 1327501 390 27871161 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1327891 : blockSum term 1327891 391 35823241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1328282 : blockSum term 1328282 390 38465329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1328672 : blockSum term 1328672 391 35801502 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1329063 : blockSum term 1329063 390 35790072 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1329453 : blockSum term 1329453 391 37103889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1329844 : blockSum term 1329844 391 34443011 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1330235 : blockSum term 1330235 391 34432074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1330626 : blockSum term 1330626 390 29125913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1331016 : blockSum term 1331016 391 39703677 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1331407 : blockSum term 1331407 390 44983050 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1331797 : blockSum term 1331797 391 30419920 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1332188 : blockSum term 1332188 390 39665937 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1332578 : blockSum term 1332578 391 38332057 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1332969 : blockSum term 1332969 391 35676815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1333360 : blockSum term 1333360 391 36985450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1333751 : blockSum term 1333751 390 38295015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1334141 : blockSum term 1334141 391 35641760 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1334532 : blockSum term 1334532 390 29033620 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1334922 : blockSum term 1334922 391 29023434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1335313 : blockSum term 1335313 390 38246747 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1335703 : blockSum term 1335703 391 35596923 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1336094 : blockSum term 1336094 391 42176157 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1336485 : blockSum term 1336485 391 34257767 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1336876 : blockSum term 1336876 390 34247081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1337266 : blockSum term 1337266 391 42135605 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1337657 : blockSum term 1337657 390 35540696 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1338047 : blockSum term 1338047 391 31580822 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1338438 : blockSum term 1338438 390 44726311 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1338828 : blockSum term 1338828 391 36821625 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1339219 : blockSum term 1339219 391 32866224 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1339610 : blockSum term 1339610 391 39427446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1340001 : blockSum term 1340001 390 39414459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1340391 : blockSum term 1340391 391 40715153 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1340782 : blockSum term 1340782 390 35450476 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1341172 : blockSum term 1341172 391 36751195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1341563 : blockSum term 1341563 390 35427926 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1341953 : blockSum term 1341953 391 44599009 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1342344 : blockSum term 1342344 391 35406007 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1342735 : blockSum term 1342735 391 36706565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1343126 : blockSum term 1343126 390 35383780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1343516 : blockSum term 1343516 391 36683289 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1343907 : blockSum term 1343907 390 32743291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1344297 : blockSum term 1344297 391 35350701 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1344688 : blockSum term 1344688 390 36648866 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1345078 : blockSum term 1345078 391 32712025 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1345469 : blockSum term 1345469 391 35318436 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1345860 : blockSum term 1345860 391 35306987 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1346251 : blockSum term 1346251 390 33988328 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1346641 : blockSum term 1346641 391 36591200 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1347032 : blockSum term 1347032 390 33966833 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1347422 : blockSum term 1347422 391 35262854 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1347813 : blockSum term 1347813 390 30029812 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1348203 : blockSum term 1348203 391 41767093 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1348594 : blockSum term 1348594 391 33925174 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1348985 : blockSum term 1348985 391 33914911 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1349376 : blockSum term 1349376 390 23471706 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1349766 : blockSum term 1349766 391 36500300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1350157 : blockSum term 1350157 390 37791444 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1350547 : blockSum term 1350547 391 37780449 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1350938 : blockSum term 1350938 390 45582129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1351328 : blockSum term 1351328 391 28642999 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1351719 : blockSum term 1351719 391 33840713 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1352110 : blockSum term 1352110 391 40336032 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1352501 : blockSum term 1352501 390 31216876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1352891 : blockSum term 1352891 391 42910912 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1353282 : blockSum term 1353282 390 25998736 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1353672 : blockSum term 1353672 391 42883671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1354063 : blockSum term 1354063 390 32477972 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1354453 : blockSum term 1354453 391 32468197 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1354844 : blockSum term 1354844 391 31160044 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1355235 : blockSum term 1355235 391 44130343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1355626 : blockSum term 1355626 390 44115211 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1356016 : blockSum term 1356016 391 36319472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1356407 : blockSum term 1356407 390 42791812 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1356797 : blockSum term 1356797 391 33704765 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1357188 : blockSum term 1357188 390 23325874 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1357578 : blockSum term 1357578 391 31092764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1357969 : blockSum term 1357969 391 42738577 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1358360 : blockSum term 1358360 391 34957592 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1358751 : blockSum term 1358751 390 34947273 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1359141 : blockSum term 1359141 391 36229474 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1359532 : blockSum term 1359532 390 31044106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1359922 : blockSum term 1359922 391 42672290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1360313 : blockSum term 1360313 390 33610435 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1360703 : blockSum term 1360703 391 42645733 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1361094 : blockSum term 1361094 391 33588982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1361485 : blockSum term 1361485 391 32286957 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1361876 : blockSum term 1361876 390 30986662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1362266 : blockSum term 1362266 391 42593671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1362657 : blockSum term 1362657 390 29676831 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1363047 : blockSum term 1363047 391 42567092 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1363438 : blockSum term 1363438 390 32237989 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1363828 : blockSum term 1363828 391 39963352 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1364219 : blockSum term 1364219 391 36085460 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1364610 : blockSum term 1364610 391 29632419 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1365001 : blockSum term 1365001 390 45079001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1365391 : blockSum term 1365391 391 25751196 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1365782 : blockSum term 1365782 390 30891763 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1366172 : blockSum term 1366172 391 34741478 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1366563 : blockSum term 1366563 390 42449130 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1366953 : blockSum term 1366953 391 34719994 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1367344 : blockSum term 1367344 391 32137947 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1367735 : blockSum term 1367735 391 35983524 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1368126 : blockSum term 1368126 390 46249736 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1368516 : blockSum term 1368516 391 29538926 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1368907 : blockSum term 1368907 390 35950516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1369297 : blockSum term 1369297 391 33372149 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1369688 : blockSum term 1369688 390 37210409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1370078 : blockSum term 1370078 391 34633718 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1370469 : blockSum term 1370469 391 37187877 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1370860 : blockSum term 1370860 391 38458416 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1371251 : blockSum term 1371251 390 29474909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1371641 : blockSum term 1371641 391 33310523 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1372032 : blockSum term 1372032 390 37141178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1372422 : blockSum term 1372422 391 29447446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1372813 : blockSum term 1372813 390 40956777 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1373203 : blockSum term 1373203 391 33266889 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1373594 : blockSum term 1373594 391 28140840 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1373985 : blockSum term 1373985 391 34525719 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1374376 : blockSum term 1374376 390 42184179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1374766 : blockSum term 1374766 391 35781009 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1375157 : blockSum term 1375157 390 29383746 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1375547 : blockSum term 1375547 391 40868562 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1375938 : blockSum term 1375938 390 33195354 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1376328 : blockSum term 1376328 391 38290772 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1376719 : blockSum term 1376719 391 33174887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1377110 : blockSum term 1377110 391 40817072 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1377501 : blockSum term 1377501 390 36978744 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1377891 : blockSum term 1377891 391 45890990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1378282 : blockSum term 1378282 390 31858397 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1378672 : blockSum term 1378672 391 40767093 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1379063 : blockSum term 1379063 390 34386537 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1379453 : blockSum term 1379453 391 36922321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1379844 : blockSum term 1379844 391 34365112 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1380235 : blockSum term 1380235 391 38171559 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1380626 : blockSum term 1380626 390 34343395 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1381016 : blockSum term 1381016 391 38147868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1381407 : blockSum term 1381407 390 40679770 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1381797 : blockSum term 1381797 391 35582168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1382188 : blockSum term 1382188 390 29219767 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1382578 : blockSum term 1382578 391 25400436 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1382969 : blockSum term 1382969 391 27932415 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1383360 : blockSum term 1383360 391 33000631 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1383751 : blockSum term 1383751 390 39334204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1384141 : blockSum term 1384141 391 29175130 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1384532 : blockSum term 1384532 390 34237418 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1384922 : blockSum term 1384922 391 41833646 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1385313 : blockSum term 1385313 390 35484670 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1385703 : blockSum term 1385703 391 41807157 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1386094 : blockSum term 1386094 391 34195390 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1386485 : blockSum term 1386485 391 35450609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1386876 : blockSum term 1386876 390 35439940 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1387266 : blockSum term 1387266 391 27837200 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1387657 : blockSum term 1387657 390 36682910 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1388047 : blockSum term 1388047 391 36671640 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1388438 : blockSum term 1388438 390 32867986 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1388828 : blockSum term 1388828 391 29065724 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1389219 : blockSum term 1389219 391 37900970 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1389610 : blockSum term 1389610 391 34100024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 1290001 100000 9271938413 := (join_sums term (lo:=1290001) (a:=50000) (b:=50000) (join_sums term (lo:=1290001) (a:=25000) (b:=25000) (join_sums term (lo:=1290001) (a:=12500) (b:=12500) (join_sums term (lo:=1290001) (a:=6250) (b:=6250) (join_sums term (lo:=1290001) (a:=3125) (b:=3125) (join_sums term (lo:=1290001) (a:=1562) (b:=1563) (join_sums term (lo:=1290001) (a:=781) (b:=781) (join_sums term (lo:=1290001) (a:=390) (b:=391) r1290001 r1290391) (join_sums term (lo:=1290782) (a:=390) (b:=391) r1290782 r1291172)) (join_sums term (lo:=1291563) (a:=781) (b:=782) (join_sums term (lo:=1291563) (a:=390) (b:=391) r1291563 r1291953) (join_sums term (lo:=1292344) (a:=391) (b:=391) r1292344 r1292735))) (join_sums term (lo:=1293126) (a:=1562) (b:=1563) (join_sums term (lo:=1293126) (a:=781) (b:=781) (join_sums term (lo:=1293126) (a:=390) (b:=391) r1293126 r1293516) (join_sums term (lo:=1293907) (a:=390) (b:=391) r1293907 r1294297)) (join_sums term (lo:=1294688) (a:=781) (b:=782) (join_sums term (lo:=1294688) (a:=390) (b:=391) r1294688 r1295078) (join_sums term (lo:=1295469) (a:=391) (b:=391) r1295469 r1295860)))) (join_sums term (lo:=1296251) (a:=3125) (b:=3125) (join_sums term (lo:=1296251) (a:=1562) (b:=1563) (join_sums term (lo:=1296251) (a:=781) (b:=781) (join_sums term (lo:=1296251) (a:=390) (b:=391) r1296251 r1296641) (join_sums term (lo:=1297032) (a:=390) (b:=391) r1297032 r1297422)) (join_sums term (lo:=1297813) (a:=781) (b:=782) (join_sums term (lo:=1297813) (a:=390) (b:=391) r1297813 r1298203) (join_sums term (lo:=1298594) (a:=391) (b:=391) r1298594 r1298985))) (join_sums term (lo:=1299376) (a:=1562) (b:=1563) (join_sums term (lo:=1299376) (a:=781) (b:=781) (join_sums term (lo:=1299376) (a:=390) (b:=391) r1299376 r1299766) (join_sums term (lo:=1300157) (a:=390) (b:=391) r1300157 r1300547)) (join_sums term (lo:=1300938) (a:=781) (b:=782) (join_sums term (lo:=1300938) (a:=390) (b:=391) r1300938 r1301328) (join_sums term (lo:=1301719) (a:=391) (b:=391) r1301719 r1302110))))) (join_sums term (lo:=1302501) (a:=6250) (b:=6250) (join_sums term (lo:=1302501) (a:=3125) (b:=3125) (join_sums term (lo:=1302501) (a:=1562) (b:=1563) (join_sums term (lo:=1302501) (a:=781) (b:=781) (join_sums term (lo:=1302501) (a:=390) (b:=391) r1302501 r1302891) (join_sums term (lo:=1303282) (a:=390) (b:=391) r1303282 r1303672)) (join_sums term (lo:=1304063) (a:=781) (b:=782) (join_sums term (lo:=1304063) (a:=390) (b:=391) r1304063 r1304453) (join_sums term (lo:=1304844) (a:=391) (b:=391) r1304844 r1305235))) (join_sums term (lo:=1305626) (a:=1562) (b:=1563) (join_sums term (lo:=1305626) (a:=781) (b:=781) (join_sums term (lo:=1305626) (a:=390) (b:=391) r1305626 r1306016) (join_sums term (lo:=1306407) (a:=390) (b:=391) r1306407 r1306797)) (join_sums term (lo:=1307188) (a:=781) (b:=782) (join_sums term (lo:=1307188) (a:=390) (b:=391) r1307188 r1307578) (join_sums term (lo:=1307969) (a:=391) (b:=391) r1307969 r1308360)))) (join_sums term (lo:=1308751) (a:=3125) (b:=3125) (join_sums term (lo:=1308751) (a:=1562) (b:=1563) (join_sums term (lo:=1308751) (a:=781) (b:=781) (join_sums term (lo:=1308751) (a:=390) (b:=391) r1308751 r1309141) (join_sums term (lo:=1309532) (a:=390) (b:=391) r1309532 r1309922)) (join_sums term (lo:=1310313) (a:=781) (b:=782) (join_sums term (lo:=1310313) (a:=390) (b:=391) r1310313 r1310703) (join_sums term (lo:=1311094) (a:=391) (b:=391) r1311094 r1311485))) (join_sums term (lo:=1311876) (a:=1562) (b:=1563) (join_sums term (lo:=1311876) (a:=781) (b:=781) (join_sums term (lo:=1311876) (a:=390) (b:=391) r1311876 r1312266) (join_sums term (lo:=1312657) (a:=390) (b:=391) r1312657 r1313047)) (join_sums term (lo:=1313438) (a:=781) (b:=782) (join_sums term (lo:=1313438) (a:=390) (b:=391) r1313438 r1313828) (join_sums term (lo:=1314219) (a:=391) (b:=391) r1314219 r1314610)))))) (join_sums term (lo:=1315001) (a:=12500) (b:=12500) (join_sums term (lo:=1315001) (a:=6250) (b:=6250) (join_sums term (lo:=1315001) (a:=3125) (b:=3125) (join_sums term (lo:=1315001) (a:=1562) (b:=1563) (join_sums term (lo:=1315001) (a:=781) (b:=781) (join_sums term (lo:=1315001) (a:=390) (b:=391) r1315001 r1315391) (join_sums term (lo:=1315782) (a:=390) (b:=391) r1315782 r1316172)) (join_sums term (lo:=1316563) (a:=781) (b:=782) (join_sums term (lo:=1316563) (a:=390) (b:=391) r1316563 r1316953) (join_sums term (lo:=1317344) (a:=391) (b:=391) r1317344 r1317735))) (join_sums term (lo:=1318126) (a:=1562) (b:=1563) (join_sums term (lo:=1318126) (a:=781) (b:=781) (join_sums term (lo:=1318126) (a:=390) (b:=391) r1318126 r1318516) (join_sums term (lo:=1318907) (a:=390) (b:=391) r1318907 r1319297)) (join_sums term (lo:=1319688) (a:=781) (b:=782) (join_sums term (lo:=1319688) (a:=390) (b:=391) r1319688 r1320078) (join_sums term (lo:=1320469) (a:=391) (b:=391) r1320469 r1320860)))) (join_sums term (lo:=1321251) (a:=3125) (b:=3125) (join_sums term (lo:=1321251) (a:=1562) (b:=1563) (join_sums term (lo:=1321251) (a:=781) (b:=781) (join_sums term (lo:=1321251) (a:=390) (b:=391) r1321251 r1321641) (join_sums term (lo:=1322032) (a:=390) (b:=391) r1322032 r1322422)) (join_sums term (lo:=1322813) (a:=781) (b:=782) (join_sums term (lo:=1322813) (a:=390) (b:=391) r1322813 r1323203) (join_sums term (lo:=1323594) (a:=391) (b:=391) r1323594 r1323985))) (join_sums term (lo:=1324376) (a:=1562) (b:=1563) (join_sums term (lo:=1324376) (a:=781) (b:=781) (join_sums term (lo:=1324376) (a:=390) (b:=391) r1324376 r1324766) (join_sums term (lo:=1325157) (a:=390) (b:=391) r1325157 r1325547)) (join_sums term (lo:=1325938) (a:=781) (b:=782) (join_sums term (lo:=1325938) (a:=390) (b:=391) r1325938 r1326328) (join_sums term (lo:=1326719) (a:=391) (b:=391) r1326719 r1327110))))) (join_sums term (lo:=1327501) (a:=6250) (b:=6250) (join_sums term (lo:=1327501) (a:=3125) (b:=3125) (join_sums term (lo:=1327501) (a:=1562) (b:=1563) (join_sums term (lo:=1327501) (a:=781) (b:=781) (join_sums term (lo:=1327501) (a:=390) (b:=391) r1327501 r1327891) (join_sums term (lo:=1328282) (a:=390) (b:=391) r1328282 r1328672)) (join_sums term (lo:=1329063) (a:=781) (b:=782) (join_sums term (lo:=1329063) (a:=390) (b:=391) r1329063 r1329453) (join_sums term (lo:=1329844) (a:=391) (b:=391) r1329844 r1330235))) (join_sums term (lo:=1330626) (a:=1562) (b:=1563) (join_sums term (lo:=1330626) (a:=781) (b:=781) (join_sums term (lo:=1330626) (a:=390) (b:=391) r1330626 r1331016) (join_sums term (lo:=1331407) (a:=390) (b:=391) r1331407 r1331797)) (join_sums term (lo:=1332188) (a:=781) (b:=782) (join_sums term (lo:=1332188) (a:=390) (b:=391) r1332188 r1332578) (join_sums term (lo:=1332969) (a:=391) (b:=391) r1332969 r1333360)))) (join_sums term (lo:=1333751) (a:=3125) (b:=3125) (join_sums term (lo:=1333751) (a:=1562) (b:=1563) (join_sums term (lo:=1333751) (a:=781) (b:=781) (join_sums term (lo:=1333751) (a:=390) (b:=391) r1333751 r1334141) (join_sums term (lo:=1334532) (a:=390) (b:=391) r1334532 r1334922)) (join_sums term (lo:=1335313) (a:=781) (b:=782) (join_sums term (lo:=1335313) (a:=390) (b:=391) r1335313 r1335703) (join_sums term (lo:=1336094) (a:=391) (b:=391) r1336094 r1336485))) (join_sums term (lo:=1336876) (a:=1562) (b:=1563) (join_sums term (lo:=1336876) (a:=781) (b:=781) (join_sums term (lo:=1336876) (a:=390) (b:=391) r1336876 r1337266) (join_sums term (lo:=1337657) (a:=390) (b:=391) r1337657 r1338047)) (join_sums term (lo:=1338438) (a:=781) (b:=782) (join_sums term (lo:=1338438) (a:=390) (b:=391) r1338438 r1338828) (join_sums term (lo:=1339219) (a:=391) (b:=391) r1339219 r1339610))))))) (join_sums term (lo:=1340001) (a:=25000) (b:=25000) (join_sums term (lo:=1340001) (a:=12500) (b:=12500) (join_sums term (lo:=1340001) (a:=6250) (b:=6250) (join_sums term (lo:=1340001) (a:=3125) (b:=3125) (join_sums term (lo:=1340001) (a:=1562) (b:=1563) (join_sums term (lo:=1340001) (a:=781) (b:=781) (join_sums term (lo:=1340001) (a:=390) (b:=391) r1340001 r1340391) (join_sums term (lo:=1340782) (a:=390) (b:=391) r1340782 r1341172)) (join_sums term (lo:=1341563) (a:=781) (b:=782) (join_sums term (lo:=1341563) (a:=390) (b:=391) r1341563 r1341953) (join_sums term (lo:=1342344) (a:=391) (b:=391) r1342344 r1342735))) (join_sums term (lo:=1343126) (a:=1562) (b:=1563) (join_sums term (lo:=1343126) (a:=781) (b:=781) (join_sums term (lo:=1343126) (a:=390) (b:=391) r1343126 r1343516) (join_sums term (lo:=1343907) (a:=390) (b:=391) r1343907 r1344297)) (join_sums term (lo:=1344688) (a:=781) (b:=782) (join_sums term (lo:=1344688) (a:=390) (b:=391) r1344688 r1345078) (join_sums term (lo:=1345469) (a:=391) (b:=391) r1345469 r1345860)))) (join_sums term (lo:=1346251) (a:=3125) (b:=3125) (join_sums term (lo:=1346251) (a:=1562) (b:=1563) (join_sums term (lo:=1346251) (a:=781) (b:=781) (join_sums term (lo:=1346251) (a:=390) (b:=391) r1346251 r1346641) (join_sums term (lo:=1347032) (a:=390) (b:=391) r1347032 r1347422)) (join_sums term (lo:=1347813) (a:=781) (b:=782) (join_sums term (lo:=1347813) (a:=390) (b:=391) r1347813 r1348203) (join_sums term (lo:=1348594) (a:=391) (b:=391) r1348594 r1348985))) (join_sums term (lo:=1349376) (a:=1562) (b:=1563) (join_sums term (lo:=1349376) (a:=781) (b:=781) (join_sums term (lo:=1349376) (a:=390) (b:=391) r1349376 r1349766) (join_sums term (lo:=1350157) (a:=390) (b:=391) r1350157 r1350547)) (join_sums term (lo:=1350938) (a:=781) (b:=782) (join_sums term (lo:=1350938) (a:=390) (b:=391) r1350938 r1351328) (join_sums term (lo:=1351719) (a:=391) (b:=391) r1351719 r1352110))))) (join_sums term (lo:=1352501) (a:=6250) (b:=6250) (join_sums term (lo:=1352501) (a:=3125) (b:=3125) (join_sums term (lo:=1352501) (a:=1562) (b:=1563) (join_sums term (lo:=1352501) (a:=781) (b:=781) (join_sums term (lo:=1352501) (a:=390) (b:=391) r1352501 r1352891) (join_sums term (lo:=1353282) (a:=390) (b:=391) r1353282 r1353672)) (join_sums term (lo:=1354063) (a:=781) (b:=782) (join_sums term (lo:=1354063) (a:=390) (b:=391) r1354063 r1354453) (join_sums term (lo:=1354844) (a:=391) (b:=391) r1354844 r1355235))) (join_sums term (lo:=1355626) (a:=1562) (b:=1563) (join_sums term (lo:=1355626) (a:=781) (b:=781) (join_sums term (lo:=1355626) (a:=390) (b:=391) r1355626 r1356016) (join_sums term (lo:=1356407) (a:=390) (b:=391) r1356407 r1356797)) (join_sums term (lo:=1357188) (a:=781) (b:=782) (join_sums term (lo:=1357188) (a:=390) (b:=391) r1357188 r1357578) (join_sums term (lo:=1357969) (a:=391) (b:=391) r1357969 r1358360)))) (join_sums term (lo:=1358751) (a:=3125) (b:=3125) (join_sums term (lo:=1358751) (a:=1562) (b:=1563) (join_sums term (lo:=1358751) (a:=781) (b:=781) (join_sums term (lo:=1358751) (a:=390) (b:=391) r1358751 r1359141) (join_sums term (lo:=1359532) (a:=390) (b:=391) r1359532 r1359922)) (join_sums term (lo:=1360313) (a:=781) (b:=782) (join_sums term (lo:=1360313) (a:=390) (b:=391) r1360313 r1360703) (join_sums term (lo:=1361094) (a:=391) (b:=391) r1361094 r1361485))) (join_sums term (lo:=1361876) (a:=1562) (b:=1563) (join_sums term (lo:=1361876) (a:=781) (b:=781) (join_sums term (lo:=1361876) (a:=390) (b:=391) r1361876 r1362266) (join_sums term (lo:=1362657) (a:=390) (b:=391) r1362657 r1363047)) (join_sums term (lo:=1363438) (a:=781) (b:=782) (join_sums term (lo:=1363438) (a:=390) (b:=391) r1363438 r1363828) (join_sums term (lo:=1364219) (a:=391) (b:=391) r1364219 r1364610)))))) (join_sums term (lo:=1365001) (a:=12500) (b:=12500) (join_sums term (lo:=1365001) (a:=6250) (b:=6250) (join_sums term (lo:=1365001) (a:=3125) (b:=3125) (join_sums term (lo:=1365001) (a:=1562) (b:=1563) (join_sums term (lo:=1365001) (a:=781) (b:=781) (join_sums term (lo:=1365001) (a:=390) (b:=391) r1365001 r1365391) (join_sums term (lo:=1365782) (a:=390) (b:=391) r1365782 r1366172)) (join_sums term (lo:=1366563) (a:=781) (b:=782) (join_sums term (lo:=1366563) (a:=390) (b:=391) r1366563 r1366953) (join_sums term (lo:=1367344) (a:=391) (b:=391) r1367344 r1367735))) (join_sums term (lo:=1368126) (a:=1562) (b:=1563) (join_sums term (lo:=1368126) (a:=781) (b:=781) (join_sums term (lo:=1368126) (a:=390) (b:=391) r1368126 r1368516) (join_sums term (lo:=1368907) (a:=390) (b:=391) r1368907 r1369297)) (join_sums term (lo:=1369688) (a:=781) (b:=782) (join_sums term (lo:=1369688) (a:=390) (b:=391) r1369688 r1370078) (join_sums term (lo:=1370469) (a:=391) (b:=391) r1370469 r1370860)))) (join_sums term (lo:=1371251) (a:=3125) (b:=3125) (join_sums term (lo:=1371251) (a:=1562) (b:=1563) (join_sums term (lo:=1371251) (a:=781) (b:=781) (join_sums term (lo:=1371251) (a:=390) (b:=391) r1371251 r1371641) (join_sums term (lo:=1372032) (a:=390) (b:=391) r1372032 r1372422)) (join_sums term (lo:=1372813) (a:=781) (b:=782) (join_sums term (lo:=1372813) (a:=390) (b:=391) r1372813 r1373203) (join_sums term (lo:=1373594) (a:=391) (b:=391) r1373594 r1373985))) (join_sums term (lo:=1374376) (a:=1562) (b:=1563) (join_sums term (lo:=1374376) (a:=781) (b:=781) (join_sums term (lo:=1374376) (a:=390) (b:=391) r1374376 r1374766) (join_sums term (lo:=1375157) (a:=390) (b:=391) r1375157 r1375547)) (join_sums term (lo:=1375938) (a:=781) (b:=782) (join_sums term (lo:=1375938) (a:=390) (b:=391) r1375938 r1376328) (join_sums term (lo:=1376719) (a:=391) (b:=391) r1376719 r1377110))))) (join_sums term (lo:=1377501) (a:=6250) (b:=6250) (join_sums term (lo:=1377501) (a:=3125) (b:=3125) (join_sums term (lo:=1377501) (a:=1562) (b:=1563) (join_sums term (lo:=1377501) (a:=781) (b:=781) (join_sums term (lo:=1377501) (a:=390) (b:=391) r1377501 r1377891) (join_sums term (lo:=1378282) (a:=390) (b:=391) r1378282 r1378672)) (join_sums term (lo:=1379063) (a:=781) (b:=782) (join_sums term (lo:=1379063) (a:=390) (b:=391) r1379063 r1379453) (join_sums term (lo:=1379844) (a:=391) (b:=391) r1379844 r1380235))) (join_sums term (lo:=1380626) (a:=1562) (b:=1563) (join_sums term (lo:=1380626) (a:=781) (b:=781) (join_sums term (lo:=1380626) (a:=390) (b:=391) r1380626 r1381016) (join_sums term (lo:=1381407) (a:=390) (b:=391) r1381407 r1381797)) (join_sums term (lo:=1382188) (a:=781) (b:=782) (join_sums term (lo:=1382188) (a:=390) (b:=391) r1382188 r1382578) (join_sums term (lo:=1382969) (a:=391) (b:=391) r1382969 r1383360)))) (join_sums term (lo:=1383751) (a:=3125) (b:=3125) (join_sums term (lo:=1383751) (a:=1562) (b:=1563) (join_sums term (lo:=1383751) (a:=781) (b:=781) (join_sums term (lo:=1383751) (a:=390) (b:=391) r1383751 r1384141) (join_sums term (lo:=1384532) (a:=390) (b:=391) r1384532 r1384922)) (join_sums term (lo:=1385313) (a:=781) (b:=782) (join_sums term (lo:=1385313) (a:=390) (b:=391) r1385313 r1385703) (join_sums term (lo:=1386094) (a:=391) (b:=391) r1386094 r1386485))) (join_sums term (lo:=1386876) (a:=1562) (b:=1563) (join_sums term (lo:=1386876) (a:=781) (b:=781) (join_sums term (lo:=1386876) (a:=390) (b:=391) r1386876 r1387266) (join_sums term (lo:=1387657) (a:=390) (b:=391) r1387657 r1388047)) (join_sums term (lo:=1388438) (a:=781) (b:=782) (join_sums term (lo:=1388438) (a:=390) (b:=391) r1388438 r1388828) (join_sums term (lo:=1389219) (a:=391) (b:=391) r1389219 r1389610))))))))

private theorem rows : blockSum term 0 1390001 9271938413 :=
  join_sums term (lo:=0) (a:=1290001) (b:=100000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 1390000).filter (1290000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=9271938413 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From1290000To1390000
