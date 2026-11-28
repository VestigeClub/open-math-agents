import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 1,190,000 through 1,290,000

The sum covers 7,107 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From1190000To1290000

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


private abbrev term := contribution 30110134441897 1190000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 1190001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 1190000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r1190001 : blockSum term 1190001 390 34295896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1190391 : blockSum term 1190391 391 41736874 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1190782 : blockSum term 1190782 390 49173362 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1191172 : blockSum term 1191172 391 37239942 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1191563 : blockSum term 1191563 390 44672345 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1191953 : blockSum term 1191953 391 46144258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1192344 : blockSum term 1192344 391 37201065 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1192735 : blockSum term 1192735 391 43138211 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1193126 : blockSum term 1193126 390 43123589 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1193516 : blockSum term 1193516 391 44595498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1193907 : blockSum term 1193907 390 38637145 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1194297 : blockSum term 1194297 391 40109138 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1194688 : blockSum term 1194688 390 46036081 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1195078 : blockSum term 1195078 391 34145040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1195469 : blockSum term 1195469 391 43036441 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1195860 : blockSum term 1195860 391 35604161 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1196251 : blockSum term 1196251 390 43007071 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1196641 : blockSum term 1196641 391 40026542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1197032 : blockSum term 1197032 390 50387808 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1197422 : blockSum term 1197422 391 31111862 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1197813 : blockSum term 1197813 390 44430409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1198203 : blockSum term 1198203 391 41454983 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1198594 : blockSum term 1198594 391 35520498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1198985 : blockSum term 1198985 391 35508102 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1199376 : blockSum term 1199376 390 48806438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1199766 : blockSum term 1199766 391 38440901 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1200157 : blockSum term 1200157 390 41382542 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1200547 : blockSum term 1200547 391 38412537 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1200938 : blockSum term 1200938 390 48738608 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1201328 : blockSum term 1201328 391 35432725 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1201719 : blockSum term 1201719 391 39847716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1202110 : blockSum term 1202110 391 42785629 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1202501 : blockSum term 1202501 390 41295993 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1202891 : blockSum term 1202891 391 32436377 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1203282 : blockSum term 1203282 390 38321831 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1203672 : blockSum term 1203672 391 47149426 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1204063 : blockSum term 1204063 390 35349241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1204453 : blockSum term 1204453 391 36810186 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1204844 : blockSum term 1204844 391 33853543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1205235 : blockSum term 1205235 391 33842000 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1205626 : blockSum term 1205626 390 44127816 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1206016 : blockSum term 1206016 391 44111138 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1206407 : blockSum term 1206407 390 47034239 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1206797 : blockSum term 1206797 391 32324932 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1207188 : blockSum term 1207188 390 42597406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1207578 : blockSum term 1207578 391 27898804 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1207969 : blockSum term 1207969 391 41100994 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1208360 : blockSum term 1208360 391 33750198 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1208751 : blockSum term 1208751 390 38139507 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1209141 : blockSum term 1209141 391 41060049 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1209532 : blockSum term 1209532 390 41045882 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1209922 : blockSum term 1209922 391 41032235 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1210313 : blockSum term 1210313 390 38089008 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1210703 : blockSum term 1210703 391 51254291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1211094 : blockSum term 1211094 391 32205543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1211485 : blockSum term 1211485 391 55608949 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1211876 : blockSum term 1211876 390 38034908 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1212266 : blockSum term 1212266 391 38022866 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1212657 : blockSum term 1212657 390 51167307 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1213047 : blockSum term 1213047 391 37998572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1213438 : blockSum term 1213438 390 43828551 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1213828 : blockSum term 1213828 391 45273963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1214219 : blockSum term 1214219 391 40879162 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1214610 : blockSum term 1214610 391 46703337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1215001 : blockSum term 1215001 390 36474258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1215391 : blockSum term 1215391 391 45212971 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1215782 : blockSum term 1215782 390 33532724 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1216172 : blockSum term 1216172 391 37893067 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1216563 : blockSum term 1216563 390 43708563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1216953 : blockSum term 1216953 391 53889783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1217344 : blockSum term 1217344 391 39311892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1217735 : blockSum term 1217735 391 34932505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1218126 : blockSum term 1218126 390 42195332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1218516 : blockSum term 1218516 391 36362627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1218907 : blockSum term 1218907 390 33442757 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1219297 : blockSum term 1219297 391 45059048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1219688 : blockSum term 1219688 390 58120581 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1220078 : blockSum term 1220078 391 27596635 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1220469 : blockSum term 1220469 391 37750495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1220860 : blockSum term 1220860 391 42092806 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1221251 : blockSum term 1221251 390 39176004 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1221641 : blockSum term 1221641 391 34812621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1222032 : blockSum term 1222032 390 34800954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1222422 : blockSum term 1222422 391 44935221 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1222813 : blockSum term 1222813 390 39123991 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1223203 : blockSum term 1223203 391 42007883 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1223594 : blockSum term 1223594 391 33305493 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1223985 : blockSum term 1223985 391 46323144 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1224376 : blockSum term 1224376 390 28942289 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1224766 : blockSum term 1224766 391 52077715 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1225157 : blockSum term 1225157 390 33260724 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1225547 : blockSum term 1225547 391 46260560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1225938 : blockSum term 1225938 390 40464559 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1226328 : blockSum term 1226328 391 46228892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1226719 : blockSum term 1226719 391 34661087 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1227110 : blockSum term 1227110 391 37536074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1227501 : blockSum term 1227501 390 31749931 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1227891 : blockSum term 1227891 391 41838861 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1228282 : blockSum term 1228282 390 44709427 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1228672 : blockSum term 1228672 391 37485106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1229063 : blockSum term 1229063 390 47561487 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1229453 : blockSum term 1229453 391 34579242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1229844 : blockSum term 1229844 391 36006990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1230235 : blockSum term 1230235 391 41754333 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1230626 : blockSum term 1230626 390 34543385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1231016 : blockSum term 1231016 391 50359209 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1231407 : blockSum term 1231407 390 46027817 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1231797 : blockSum term 1231797 391 33072627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1232188 : blockSum term 1232188 390 40247695 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1232578 : blockSum term 1232578 391 31612569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1232969 : blockSum term 1232969 391 34475972 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1233360 : blockSum term 1233360 391 43080373 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1233751 : blockSum term 1233751 390 33016265 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1234141 : blockSum term 1234141 391 31570074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1234532 : blockSum term 1234532 390 40166417 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1234922 : blockSum term 1234922 391 41586125 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1235313 : blockSum term 1235313 390 37272868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1235703 : blockSum term 1235703 391 34394208 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1236094 : blockSum term 1236094 391 30084104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1236485 : blockSum term 1236485 391 44395468 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1236876 : blockSum term 1236876 390 40085540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1237266 : blockSum term 1237266 391 42935291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1237657 : blockSum term 1237657 390 37197394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1238047 : blockSum term 1238047 391 44336337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1238438 : blockSum term 1238438 390 41461503 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1238828 : blockSum term 1238828 391 34302267 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1239219 : blockSum term 1239219 391 50006691 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1239610 : blockSum term 1239610 391 37134803 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1240001 : blockSum term 1240001 390 41406374 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1240391 : blockSum term 1240391 391 38536192 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1240782 : blockSum term 1240782 390 31390347 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1241172 : blockSum term 1241172 391 48495633 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1241563 : blockSum term 1241563 390 35646000 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1241953 : blockSum term 1241953 391 38486484 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1242344 : blockSum term 1242344 391 29924517 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1242735 : blockSum term 1242735 391 39885131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1243126 : blockSum term 1243126 390 39870574 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1243516 : blockSum term 1243516 391 41280552 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1243907 : blockSum term 1243907 390 48382541 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1244297 : blockSum term 1244297 391 41253378 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1244688 : blockSum term 1244688 390 39817569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1245078 : blockSum term 1245078 391 28431915 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1245469 : blockSum term 1245469 391 39790778 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1245860 : blockSum term 1245860 391 39777668 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1246251 : blockSum term 1246251 390 58226097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1246641 : blockSum term 1246641 391 32651984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1247032 : blockSum term 1247032 390 39736413 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1247422 : blockSum term 1247422 391 42560893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1247813 : blockSum term 1247813 390 41128369 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1248203 : blockSum term 1248203 391 46786298 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1248594 : blockSum term 1248594 391 35431809 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1248985 : blockSum term 1248985 391 46755411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1249376 : blockSum term 1249376 390 42490027 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1249766 : blockSum term 1249766 391 39645122 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1250157 : blockSum term 1250157 390 38216270 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1250547 : blockSum term 1250547 391 35373805 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1250938 : blockSum term 1250938 390 36776993 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1251328 : blockSum term 1251328 391 31107693 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1251719 : blockSum term 1251719 391 42405932 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1252110 : blockSum term 1252110 391 39566477 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1252501 : blockSum term 1252501 390 31076800 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1252891 : blockSum term 1252891 391 38128782 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1253282 : blockSum term 1253282 390 28233772 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1253672 : blockSum term 1253672 391 47980861 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1254063 : blockSum term 1254063 390 38090755 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1254453 : blockSum term 1254453 391 49359531 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1254844 : blockSum term 1254844 391 42292267 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1255235 : blockSum term 1255235 391 40870619 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1255626 : blockSum term 1255626 390 39447271 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1256016 : blockSum term 1256016 391 29575718 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1256407 : blockSum term 1256407 390 35197501 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1256797 : blockSum term 1256797 391 49262186 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1257188 : blockSum term 1257188 390 45024521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1257578 : blockSum term 1257578 391 32350080 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1257969 : blockSum term 1257969 391 46400214 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1258360 : blockSum term 1258360 391 44979357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1258751 : blockSum term 1258751 390 49179506 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1259141 : blockSum term 1259141 391 28093742 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1259532 : blockSum term 1259532 390 40722298 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1259922 : blockSum term 1259922 391 35093199 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1260313 : blockSum term 1260313 390 40694653 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1260703 : blockSum term 1260703 391 40681255 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1261094 : blockSum term 1261094 391 35058157 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1261485 : blockSum term 1261485 391 37849563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1261876 : blockSum term 1261876 390 36436238 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1262266 : blockSum term 1262266 391 40626864 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1262657 : blockSum term 1262657 390 37813817 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1263047 : blockSum term 1263047 391 46201276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1263438 : blockSum term 1263438 390 39188597 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1263828 : blockSum term 1263828 391 34978248 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1264219 : blockSum term 1264219 391 32168770 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1264610 : blockSum term 1264610 391 43343716 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1265001 : blockSum term 1265001 390 41932343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1265391 : blockSum term 1265391 391 40521407 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1265782 : blockSum term 1265782 390 48888574 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1266172 : blockSum term 1266172 391 46079304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1266563 : blockSum term 1266563 390 43271457 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1266953 : blockSum term 1266953 391 30699097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1267344 : blockSum term 1267344 391 37663574 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1267735 : blockSum term 1267735 391 39046095 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1268126 : blockSum term 1268126 390 37639438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1268516 : blockSum term 1268516 391 41807529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1268907 : blockSum term 1268907 390 43186800 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1269297 : blockSum term 1269297 391 33424763 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1269688 : blockSum term 1269688 390 34805938 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1270078 : blockSum term 1270078 391 41754251 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1270469 : blockSum term 1270469 391 41741185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1270860 : blockSum term 1270860 391 44507644 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1271251 : blockSum term 1271251 390 38932196 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1271641 : blockSum term 1271641 391 37529482 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1272032 : blockSum term 1272032 390 47243417 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1272422 : blockSum term 1272422 391 25003048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1272813 : blockSum term 1272813 390 45824100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1273203 : blockSum term 1273203 391 43031800 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1273594 : blockSum term 1273594 391 38854847 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1273985 : blockSum term 1273985 391 34680602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1274376 : blockSum term 1274376 390 30509005 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1274766 : blockSum term 1274766 391 27726776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1275157 : blockSum term 1275157 390 33261001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1275547 : blockSum term 1275547 391 44333646 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1275938 : blockSum term 1275938 390 41549152 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1276328 : blockSum term 1276328 391 34612058 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1276719 : blockSum term 1276719 391 44289732 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1277110 : blockSum term 1277110 391 31822825 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1277501 : blockSum term 1277501 390 37344874 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1277891 : blockSum term 1277891 391 33185126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1278282 : blockSum term 1278282 390 42850296 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1278672 : blockSum term 1278672 391 34545342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1279063 : blockSum term 1279063 390 37297469 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1279453 : blockSum term 1279453 391 46950519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1279844 : blockSum term 1279844 391 37271626 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1280235 : blockSum term 1280235 391 31739745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1280626 : blockSum term 1280626 390 35868818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1281016 : blockSum term 1281016 391 38615563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1281407 : blockSum term 1281407 390 39981189 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1281797 : blockSum term 1281797 391 44103269 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1282188 : blockSum term 1282188 390 42710473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1282578 : blockSum term 1282578 391 41319820 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1282969 : blockSum term 1282969 391 35798824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1283360 : blockSum term 1283360 391 33033521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1283751 : blockSum term 1283751 390 34399156 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1284141 : blockSum term 1284141 391 35762807 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1284532 : blockSum term 1284532 390 38501404 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1284922 : blockSum term 1284922 391 45360950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1285313 : blockSum term 1285313 390 32979439 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1285703 : blockSum term 1285703 391 43959138 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1286094 : blockSum term 1286094 391 34332341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1286485 : blockSum term 1286485 391 46676097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1286876 : blockSum term 1286876 390 37053953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1287266 : blockSum term 1287266 391 38414625 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1287657 : blockSum term 1287657 390 49374572 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1288047 : blockSum term 1288047 391 37019393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1288438 : blockSum term 1288438 390 37006513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1288828 : blockSum term 1288828 391 43846861 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1289219 : blockSum term 1289219 391 36982143 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1289610 : blockSum term 1289610 391 36970497 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 1190001 100000 10152140134 := (join_sums term (lo:=1190001) (a:=50000) (b:=50000) (join_sums term (lo:=1190001) (a:=25000) (b:=25000) (join_sums term (lo:=1190001) (a:=12500) (b:=12500) (join_sums term (lo:=1190001) (a:=6250) (b:=6250) (join_sums term (lo:=1190001) (a:=3125) (b:=3125) (join_sums term (lo:=1190001) (a:=1562) (b:=1563) (join_sums term (lo:=1190001) (a:=781) (b:=781) (join_sums term (lo:=1190001) (a:=390) (b:=391) r1190001 r1190391) (join_sums term (lo:=1190782) (a:=390) (b:=391) r1190782 r1191172)) (join_sums term (lo:=1191563) (a:=781) (b:=782) (join_sums term (lo:=1191563) (a:=390) (b:=391) r1191563 r1191953) (join_sums term (lo:=1192344) (a:=391) (b:=391) r1192344 r1192735))) (join_sums term (lo:=1193126) (a:=1562) (b:=1563) (join_sums term (lo:=1193126) (a:=781) (b:=781) (join_sums term (lo:=1193126) (a:=390) (b:=391) r1193126 r1193516) (join_sums term (lo:=1193907) (a:=390) (b:=391) r1193907 r1194297)) (join_sums term (lo:=1194688) (a:=781) (b:=782) (join_sums term (lo:=1194688) (a:=390) (b:=391) r1194688 r1195078) (join_sums term (lo:=1195469) (a:=391) (b:=391) r1195469 r1195860)))) (join_sums term (lo:=1196251) (a:=3125) (b:=3125) (join_sums term (lo:=1196251) (a:=1562) (b:=1563) (join_sums term (lo:=1196251) (a:=781) (b:=781) (join_sums term (lo:=1196251) (a:=390) (b:=391) r1196251 r1196641) (join_sums term (lo:=1197032) (a:=390) (b:=391) r1197032 r1197422)) (join_sums term (lo:=1197813) (a:=781) (b:=782) (join_sums term (lo:=1197813) (a:=390) (b:=391) r1197813 r1198203) (join_sums term (lo:=1198594) (a:=391) (b:=391) r1198594 r1198985))) (join_sums term (lo:=1199376) (a:=1562) (b:=1563) (join_sums term (lo:=1199376) (a:=781) (b:=781) (join_sums term (lo:=1199376) (a:=390) (b:=391) r1199376 r1199766) (join_sums term (lo:=1200157) (a:=390) (b:=391) r1200157 r1200547)) (join_sums term (lo:=1200938) (a:=781) (b:=782) (join_sums term (lo:=1200938) (a:=390) (b:=391) r1200938 r1201328) (join_sums term (lo:=1201719) (a:=391) (b:=391) r1201719 r1202110))))) (join_sums term (lo:=1202501) (a:=6250) (b:=6250) (join_sums term (lo:=1202501) (a:=3125) (b:=3125) (join_sums term (lo:=1202501) (a:=1562) (b:=1563) (join_sums term (lo:=1202501) (a:=781) (b:=781) (join_sums term (lo:=1202501) (a:=390) (b:=391) r1202501 r1202891) (join_sums term (lo:=1203282) (a:=390) (b:=391) r1203282 r1203672)) (join_sums term (lo:=1204063) (a:=781) (b:=782) (join_sums term (lo:=1204063) (a:=390) (b:=391) r1204063 r1204453) (join_sums term (lo:=1204844) (a:=391) (b:=391) r1204844 r1205235))) (join_sums term (lo:=1205626) (a:=1562) (b:=1563) (join_sums term (lo:=1205626) (a:=781) (b:=781) (join_sums term (lo:=1205626) (a:=390) (b:=391) r1205626 r1206016) (join_sums term (lo:=1206407) (a:=390) (b:=391) r1206407 r1206797)) (join_sums term (lo:=1207188) (a:=781) (b:=782) (join_sums term (lo:=1207188) (a:=390) (b:=391) r1207188 r1207578) (join_sums term (lo:=1207969) (a:=391) (b:=391) r1207969 r1208360)))) (join_sums term (lo:=1208751) (a:=3125) (b:=3125) (join_sums term (lo:=1208751) (a:=1562) (b:=1563) (join_sums term (lo:=1208751) (a:=781) (b:=781) (join_sums term (lo:=1208751) (a:=390) (b:=391) r1208751 r1209141) (join_sums term (lo:=1209532) (a:=390) (b:=391) r1209532 r1209922)) (join_sums term (lo:=1210313) (a:=781) (b:=782) (join_sums term (lo:=1210313) (a:=390) (b:=391) r1210313 r1210703) (join_sums term (lo:=1211094) (a:=391) (b:=391) r1211094 r1211485))) (join_sums term (lo:=1211876) (a:=1562) (b:=1563) (join_sums term (lo:=1211876) (a:=781) (b:=781) (join_sums term (lo:=1211876) (a:=390) (b:=391) r1211876 r1212266) (join_sums term (lo:=1212657) (a:=390) (b:=391) r1212657 r1213047)) (join_sums term (lo:=1213438) (a:=781) (b:=782) (join_sums term (lo:=1213438) (a:=390) (b:=391) r1213438 r1213828) (join_sums term (lo:=1214219) (a:=391) (b:=391) r1214219 r1214610)))))) (join_sums term (lo:=1215001) (a:=12500) (b:=12500) (join_sums term (lo:=1215001) (a:=6250) (b:=6250) (join_sums term (lo:=1215001) (a:=3125) (b:=3125) (join_sums term (lo:=1215001) (a:=1562) (b:=1563) (join_sums term (lo:=1215001) (a:=781) (b:=781) (join_sums term (lo:=1215001) (a:=390) (b:=391) r1215001 r1215391) (join_sums term (lo:=1215782) (a:=390) (b:=391) r1215782 r1216172)) (join_sums term (lo:=1216563) (a:=781) (b:=782) (join_sums term (lo:=1216563) (a:=390) (b:=391) r1216563 r1216953) (join_sums term (lo:=1217344) (a:=391) (b:=391) r1217344 r1217735))) (join_sums term (lo:=1218126) (a:=1562) (b:=1563) (join_sums term (lo:=1218126) (a:=781) (b:=781) (join_sums term (lo:=1218126) (a:=390) (b:=391) r1218126 r1218516) (join_sums term (lo:=1218907) (a:=390) (b:=391) r1218907 r1219297)) (join_sums term (lo:=1219688) (a:=781) (b:=782) (join_sums term (lo:=1219688) (a:=390) (b:=391) r1219688 r1220078) (join_sums term (lo:=1220469) (a:=391) (b:=391) r1220469 r1220860)))) (join_sums term (lo:=1221251) (a:=3125) (b:=3125) (join_sums term (lo:=1221251) (a:=1562) (b:=1563) (join_sums term (lo:=1221251) (a:=781) (b:=781) (join_sums term (lo:=1221251) (a:=390) (b:=391) r1221251 r1221641) (join_sums term (lo:=1222032) (a:=390) (b:=391) r1222032 r1222422)) (join_sums term (lo:=1222813) (a:=781) (b:=782) (join_sums term (lo:=1222813) (a:=390) (b:=391) r1222813 r1223203) (join_sums term (lo:=1223594) (a:=391) (b:=391) r1223594 r1223985))) (join_sums term (lo:=1224376) (a:=1562) (b:=1563) (join_sums term (lo:=1224376) (a:=781) (b:=781) (join_sums term (lo:=1224376) (a:=390) (b:=391) r1224376 r1224766) (join_sums term (lo:=1225157) (a:=390) (b:=391) r1225157 r1225547)) (join_sums term (lo:=1225938) (a:=781) (b:=782) (join_sums term (lo:=1225938) (a:=390) (b:=391) r1225938 r1226328) (join_sums term (lo:=1226719) (a:=391) (b:=391) r1226719 r1227110))))) (join_sums term (lo:=1227501) (a:=6250) (b:=6250) (join_sums term (lo:=1227501) (a:=3125) (b:=3125) (join_sums term (lo:=1227501) (a:=1562) (b:=1563) (join_sums term (lo:=1227501) (a:=781) (b:=781) (join_sums term (lo:=1227501) (a:=390) (b:=391) r1227501 r1227891) (join_sums term (lo:=1228282) (a:=390) (b:=391) r1228282 r1228672)) (join_sums term (lo:=1229063) (a:=781) (b:=782) (join_sums term (lo:=1229063) (a:=390) (b:=391) r1229063 r1229453) (join_sums term (lo:=1229844) (a:=391) (b:=391) r1229844 r1230235))) (join_sums term (lo:=1230626) (a:=1562) (b:=1563) (join_sums term (lo:=1230626) (a:=781) (b:=781) (join_sums term (lo:=1230626) (a:=390) (b:=391) r1230626 r1231016) (join_sums term (lo:=1231407) (a:=390) (b:=391) r1231407 r1231797)) (join_sums term (lo:=1232188) (a:=781) (b:=782) (join_sums term (lo:=1232188) (a:=390) (b:=391) r1232188 r1232578) (join_sums term (lo:=1232969) (a:=391) (b:=391) r1232969 r1233360)))) (join_sums term (lo:=1233751) (a:=3125) (b:=3125) (join_sums term (lo:=1233751) (a:=1562) (b:=1563) (join_sums term (lo:=1233751) (a:=781) (b:=781) (join_sums term (lo:=1233751) (a:=390) (b:=391) r1233751 r1234141) (join_sums term (lo:=1234532) (a:=390) (b:=391) r1234532 r1234922)) (join_sums term (lo:=1235313) (a:=781) (b:=782) (join_sums term (lo:=1235313) (a:=390) (b:=391) r1235313 r1235703) (join_sums term (lo:=1236094) (a:=391) (b:=391) r1236094 r1236485))) (join_sums term (lo:=1236876) (a:=1562) (b:=1563) (join_sums term (lo:=1236876) (a:=781) (b:=781) (join_sums term (lo:=1236876) (a:=390) (b:=391) r1236876 r1237266) (join_sums term (lo:=1237657) (a:=390) (b:=391) r1237657 r1238047)) (join_sums term (lo:=1238438) (a:=781) (b:=782) (join_sums term (lo:=1238438) (a:=390) (b:=391) r1238438 r1238828) (join_sums term (lo:=1239219) (a:=391) (b:=391) r1239219 r1239610))))))) (join_sums term (lo:=1240001) (a:=25000) (b:=25000) (join_sums term (lo:=1240001) (a:=12500) (b:=12500) (join_sums term (lo:=1240001) (a:=6250) (b:=6250) (join_sums term (lo:=1240001) (a:=3125) (b:=3125) (join_sums term (lo:=1240001) (a:=1562) (b:=1563) (join_sums term (lo:=1240001) (a:=781) (b:=781) (join_sums term (lo:=1240001) (a:=390) (b:=391) r1240001 r1240391) (join_sums term (lo:=1240782) (a:=390) (b:=391) r1240782 r1241172)) (join_sums term (lo:=1241563) (a:=781) (b:=782) (join_sums term (lo:=1241563) (a:=390) (b:=391) r1241563 r1241953) (join_sums term (lo:=1242344) (a:=391) (b:=391) r1242344 r1242735))) (join_sums term (lo:=1243126) (a:=1562) (b:=1563) (join_sums term (lo:=1243126) (a:=781) (b:=781) (join_sums term (lo:=1243126) (a:=390) (b:=391) r1243126 r1243516) (join_sums term (lo:=1243907) (a:=390) (b:=391) r1243907 r1244297)) (join_sums term (lo:=1244688) (a:=781) (b:=782) (join_sums term (lo:=1244688) (a:=390) (b:=391) r1244688 r1245078) (join_sums term (lo:=1245469) (a:=391) (b:=391) r1245469 r1245860)))) (join_sums term (lo:=1246251) (a:=3125) (b:=3125) (join_sums term (lo:=1246251) (a:=1562) (b:=1563) (join_sums term (lo:=1246251) (a:=781) (b:=781) (join_sums term (lo:=1246251) (a:=390) (b:=391) r1246251 r1246641) (join_sums term (lo:=1247032) (a:=390) (b:=391) r1247032 r1247422)) (join_sums term (lo:=1247813) (a:=781) (b:=782) (join_sums term (lo:=1247813) (a:=390) (b:=391) r1247813 r1248203) (join_sums term (lo:=1248594) (a:=391) (b:=391) r1248594 r1248985))) (join_sums term (lo:=1249376) (a:=1562) (b:=1563) (join_sums term (lo:=1249376) (a:=781) (b:=781) (join_sums term (lo:=1249376) (a:=390) (b:=391) r1249376 r1249766) (join_sums term (lo:=1250157) (a:=390) (b:=391) r1250157 r1250547)) (join_sums term (lo:=1250938) (a:=781) (b:=782) (join_sums term (lo:=1250938) (a:=390) (b:=391) r1250938 r1251328) (join_sums term (lo:=1251719) (a:=391) (b:=391) r1251719 r1252110))))) (join_sums term (lo:=1252501) (a:=6250) (b:=6250) (join_sums term (lo:=1252501) (a:=3125) (b:=3125) (join_sums term (lo:=1252501) (a:=1562) (b:=1563) (join_sums term (lo:=1252501) (a:=781) (b:=781) (join_sums term (lo:=1252501) (a:=390) (b:=391) r1252501 r1252891) (join_sums term (lo:=1253282) (a:=390) (b:=391) r1253282 r1253672)) (join_sums term (lo:=1254063) (a:=781) (b:=782) (join_sums term (lo:=1254063) (a:=390) (b:=391) r1254063 r1254453) (join_sums term (lo:=1254844) (a:=391) (b:=391) r1254844 r1255235))) (join_sums term (lo:=1255626) (a:=1562) (b:=1563) (join_sums term (lo:=1255626) (a:=781) (b:=781) (join_sums term (lo:=1255626) (a:=390) (b:=391) r1255626 r1256016) (join_sums term (lo:=1256407) (a:=390) (b:=391) r1256407 r1256797)) (join_sums term (lo:=1257188) (a:=781) (b:=782) (join_sums term (lo:=1257188) (a:=390) (b:=391) r1257188 r1257578) (join_sums term (lo:=1257969) (a:=391) (b:=391) r1257969 r1258360)))) (join_sums term (lo:=1258751) (a:=3125) (b:=3125) (join_sums term (lo:=1258751) (a:=1562) (b:=1563) (join_sums term (lo:=1258751) (a:=781) (b:=781) (join_sums term (lo:=1258751) (a:=390) (b:=391) r1258751 r1259141) (join_sums term (lo:=1259532) (a:=390) (b:=391) r1259532 r1259922)) (join_sums term (lo:=1260313) (a:=781) (b:=782) (join_sums term (lo:=1260313) (a:=390) (b:=391) r1260313 r1260703) (join_sums term (lo:=1261094) (a:=391) (b:=391) r1261094 r1261485))) (join_sums term (lo:=1261876) (a:=1562) (b:=1563) (join_sums term (lo:=1261876) (a:=781) (b:=781) (join_sums term (lo:=1261876) (a:=390) (b:=391) r1261876 r1262266) (join_sums term (lo:=1262657) (a:=390) (b:=391) r1262657 r1263047)) (join_sums term (lo:=1263438) (a:=781) (b:=782) (join_sums term (lo:=1263438) (a:=390) (b:=391) r1263438 r1263828) (join_sums term (lo:=1264219) (a:=391) (b:=391) r1264219 r1264610)))))) (join_sums term (lo:=1265001) (a:=12500) (b:=12500) (join_sums term (lo:=1265001) (a:=6250) (b:=6250) (join_sums term (lo:=1265001) (a:=3125) (b:=3125) (join_sums term (lo:=1265001) (a:=1562) (b:=1563) (join_sums term (lo:=1265001) (a:=781) (b:=781) (join_sums term (lo:=1265001) (a:=390) (b:=391) r1265001 r1265391) (join_sums term (lo:=1265782) (a:=390) (b:=391) r1265782 r1266172)) (join_sums term (lo:=1266563) (a:=781) (b:=782) (join_sums term (lo:=1266563) (a:=390) (b:=391) r1266563 r1266953) (join_sums term (lo:=1267344) (a:=391) (b:=391) r1267344 r1267735))) (join_sums term (lo:=1268126) (a:=1562) (b:=1563) (join_sums term (lo:=1268126) (a:=781) (b:=781) (join_sums term (lo:=1268126) (a:=390) (b:=391) r1268126 r1268516) (join_sums term (lo:=1268907) (a:=390) (b:=391) r1268907 r1269297)) (join_sums term (lo:=1269688) (a:=781) (b:=782) (join_sums term (lo:=1269688) (a:=390) (b:=391) r1269688 r1270078) (join_sums term (lo:=1270469) (a:=391) (b:=391) r1270469 r1270860)))) (join_sums term (lo:=1271251) (a:=3125) (b:=3125) (join_sums term (lo:=1271251) (a:=1562) (b:=1563) (join_sums term (lo:=1271251) (a:=781) (b:=781) (join_sums term (lo:=1271251) (a:=390) (b:=391) r1271251 r1271641) (join_sums term (lo:=1272032) (a:=390) (b:=391) r1272032 r1272422)) (join_sums term (lo:=1272813) (a:=781) (b:=782) (join_sums term (lo:=1272813) (a:=390) (b:=391) r1272813 r1273203) (join_sums term (lo:=1273594) (a:=391) (b:=391) r1273594 r1273985))) (join_sums term (lo:=1274376) (a:=1562) (b:=1563) (join_sums term (lo:=1274376) (a:=781) (b:=781) (join_sums term (lo:=1274376) (a:=390) (b:=391) r1274376 r1274766) (join_sums term (lo:=1275157) (a:=390) (b:=391) r1275157 r1275547)) (join_sums term (lo:=1275938) (a:=781) (b:=782) (join_sums term (lo:=1275938) (a:=390) (b:=391) r1275938 r1276328) (join_sums term (lo:=1276719) (a:=391) (b:=391) r1276719 r1277110))))) (join_sums term (lo:=1277501) (a:=6250) (b:=6250) (join_sums term (lo:=1277501) (a:=3125) (b:=3125) (join_sums term (lo:=1277501) (a:=1562) (b:=1563) (join_sums term (lo:=1277501) (a:=781) (b:=781) (join_sums term (lo:=1277501) (a:=390) (b:=391) r1277501 r1277891) (join_sums term (lo:=1278282) (a:=390) (b:=391) r1278282 r1278672)) (join_sums term (lo:=1279063) (a:=781) (b:=782) (join_sums term (lo:=1279063) (a:=390) (b:=391) r1279063 r1279453) (join_sums term (lo:=1279844) (a:=391) (b:=391) r1279844 r1280235))) (join_sums term (lo:=1280626) (a:=1562) (b:=1563) (join_sums term (lo:=1280626) (a:=781) (b:=781) (join_sums term (lo:=1280626) (a:=390) (b:=391) r1280626 r1281016) (join_sums term (lo:=1281407) (a:=390) (b:=391) r1281407 r1281797)) (join_sums term (lo:=1282188) (a:=781) (b:=782) (join_sums term (lo:=1282188) (a:=390) (b:=391) r1282188 r1282578) (join_sums term (lo:=1282969) (a:=391) (b:=391) r1282969 r1283360)))) (join_sums term (lo:=1283751) (a:=3125) (b:=3125) (join_sums term (lo:=1283751) (a:=1562) (b:=1563) (join_sums term (lo:=1283751) (a:=781) (b:=781) (join_sums term (lo:=1283751) (a:=390) (b:=391) r1283751 r1284141) (join_sums term (lo:=1284532) (a:=390) (b:=391) r1284532 r1284922)) (join_sums term (lo:=1285313) (a:=781) (b:=782) (join_sums term (lo:=1285313) (a:=390) (b:=391) r1285313 r1285703) (join_sums term (lo:=1286094) (a:=391) (b:=391) r1286094 r1286485))) (join_sums term (lo:=1286876) (a:=1562) (b:=1563) (join_sums term (lo:=1286876) (a:=781) (b:=781) (join_sums term (lo:=1286876) (a:=390) (b:=391) r1286876 r1287266) (join_sums term (lo:=1287657) (a:=390) (b:=391) r1287657 r1288047)) (join_sums term (lo:=1288438) (a:=781) (b:=782) (join_sums term (lo:=1288438) (a:=390) (b:=391) r1288438 r1288828) (join_sums term (lo:=1289219) (a:=391) (b:=391) r1289219 r1289610))))))))

private theorem rows : blockSum term 0 1290001 10152140134 :=
  join_sums term (lo:=0) (a:=1190001) (b:=100000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 1290000).filter (1190000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=10152140134 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From1190000To1290000
