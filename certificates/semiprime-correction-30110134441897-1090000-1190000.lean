import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 1,090,000 through 1,190,000

The sum covers 7,249 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From1090000To1190000

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


private abbrev term := contribution 30110134441897 1090000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 1090001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 1090000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r1090001 : blockSum term 1090001 390 42490593 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1090391 : blockSum term 1090391 391 42475447 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1090782 : blockSum term 1090782 390 62055866 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1091172 : blockSum term 1091172 391 57134391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1091563 : blockSum term 1091563 390 42426823 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1091953 : blockSum term 1091953 391 47303689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1092344 : blockSum term 1092344 391 45656595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1092735 : blockSum term 1092735 391 48898137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1093126 : blockSum term 1093126 390 45622539 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1093516 : blockSum term 1093516 391 55377892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1093907 : blockSum term 1093907 390 48845201 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1094297 : blockSum term 1094297 391 53707563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1094688 : blockSum term 1094688 390 52060814 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1095078 : blockSum term 1095078 391 42283481 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1095469 : blockSum term 1095469 391 53647757 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1095860 : blockSum term 1095860 391 34127406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1096251 : blockSum term 1096251 390 48735173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1096641 : blockSum term 1096641 391 43845633 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1097032 : blockSum term 1097032 390 43830771 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1097422 : blockSum term 1097422 391 43814502 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1097813 : blockSum term 1097813 390 45420290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1098203 : blockSum term 1098203 391 42160084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1098594 : blockSum term 1098594 391 32419667 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1098985 : blockSum term 1098985 391 43748626 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1099376 : blockSum term 1099376 390 56690963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1099766 : blockSum term 1099766 391 48573859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1100157 : blockSum term 1100157 390 48556836 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1100547 : blockSum term 1100547 391 43683876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1100938 : blockSum term 1100938 390 32346254 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1101328 : blockSum term 1101328 391 53353640 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1101719 : blockSum term 1101719 391 42021144 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1102110 : blockSum term 1102110 391 53314623 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1102501 : blockSum term 1102501 390 45219445 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1102891 : blockSum term 1102891 391 51661645 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1103282 : blockSum term 1103282 390 45185438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1103672 : blockSum term 1103672 391 33877387 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1104063 : blockSum term 1104063 390 51604853 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1104453 : blockSum term 1104453 391 53196416 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1104844 : blockSum term 1104844 391 45120435 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1105235 : blockSum term 1105235 391 48325341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1105626 : blockSum term 1105626 390 45088999 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1106016 : blockSum term 1106016 391 43462084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1106407 : blockSum term 1106407 390 49883185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1106797 : blockSum term 1106797 391 46647942 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1107188 : blockSum term 1107188 390 41805861 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1107578 : blockSum term 1107578 391 45006495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1107969 : blockSum term 1107969 391 44990195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1108360 : blockSum term 1108360 391 62641636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1108751 : blockSum term 1108751 390 36929845 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1109141 : blockSum term 1109141 391 49755381 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1109532 : blockSum term 1109532 390 46526693 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1109922 : blockSum term 1109922 391 36887586 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1110313 : blockSum term 1110313 390 44891592 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1110703 : blockSum term 1110703 391 60900615 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1111094 : blockSum term 1111094 391 41653928 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1111485 : blockSum term 1111485 391 48044901 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1111876 : blockSum term 1111876 390 44824614 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1112266 : blockSum term 1112266 391 52809160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1112657 : blockSum term 1112657 390 49590391 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1113047 : blockSum term 1113047 391 41576860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1113438 : blockSum term 1113438 390 39963124 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1113828 : blockSum term 1113828 391 39949776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1114219 : blockSum term 1114219 391 46323850 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1114610 : blockSum term 1114610 391 49500790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1115001 : blockSum term 1115001 390 41501353 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1115391 : blockSum term 1115391 391 55846914 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1115782 : blockSum term 1115782 390 31901495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1116172 : blockSum term 1116172 391 44645598 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1116563 : blockSum term 1116563 390 39847501 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1116953 : blockSum term 1116953 391 46206015 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1117344 : blockSum term 1117344 391 44596130 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1117735 : blockSum term 1117735 391 57317678 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1118126 : blockSum term 1118126 390 36606312 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1118516 : blockSum term 1118516 391 46137664 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1118907 : blockSum term 1118907 390 36580159 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1119297 : blockSum term 1119297 391 36565981 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1119688 : blockSum term 1119688 390 38143233 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1120078 : blockSum term 1120078 391 42894662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1120469 : blockSum term 1120469 391 63524020 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1120860 : blockSum term 1120860 391 49212868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1121251 : blockSum term 1121251 390 39674040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1121641 : blockSum term 1121641 391 34899970 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1122032 : blockSum term 1122032 390 42816697 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1122422 : blockSum term 1122422 391 41216368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1122813 : blockSum term 1122813 390 26939043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1123203 : blockSum term 1123203 391 52274872 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1123594 : blockSum term 1123594 391 52255790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1123985 : blockSum term 1123985 391 42738389 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1124376 : blockSum term 1124376 390 41140985 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1124766 : blockSum term 1124766 391 42707790 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1125157 : blockSum term 1125157 390 45855589 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1125547 : blockSum term 1125547 391 44258354 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1125938 : blockSum term 1125938 390 31602066 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1126328 : blockSum term 1126328 391 52125390 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1126719 : blockSum term 1126719 391 39475291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1127110 : blockSum term 1127110 391 52088584 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1127501 : blockSum term 1127501 390 44180223 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1127891 : blockSum term 1127891 391 37854749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1128282 : blockSum term 1128282 390 53608184 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1128672 : blockSum term 1128672 391 52013430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1129063 : blockSum term 1129063 390 40964710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1129453 : blockSum term 1129453 391 47250229 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1129844 : blockSum term 1129844 391 34638883 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1130235 : blockSum term 1130235 391 45643359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1130626 : blockSum term 1130626 390 45626635 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1131016 : blockSum term 1131016 391 48754578 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1131407 : blockSum term 1131407 390 45592870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1131797 : blockSum term 1131797 391 44006600 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1132188 : blockSum term 1132188 390 42417320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1132578 : blockSum term 1132578 391 45544680 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1132969 : blockSum term 1132969 391 51807740 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1133360 : blockSum term 1133360 391 42372194 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1133751 : blockSum term 1133751 390 45494936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1134141 : blockSum term 1134141 391 45478580 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1134532 : blockSum term 1134532 390 42326648 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1134922 : blockSum term 1134922 391 51713343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1135313 : blockSum term 1135313 390 36030135 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1135703 : blockSum term 1135703 391 50110299 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1136094 : blockSum term 1136094 391 46960687 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1136485 : blockSum term 1136485 391 42249019 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1136876 : blockSum term 1136876 390 42234060 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1137266 : blockSum term 1137266 391 34401003 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1137657 : blockSum term 1137657 390 46893911 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1138047 : blockSum term 1138047 391 35938025 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1138438 : blockSum term 1138438 390 42173681 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1138828 : blockSum term 1138828 391 42160596 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1139219 : blockSum term 1139219 391 48389257 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1139610 : blockSum term 1139610 391 42129171 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1140001 : blockSum term 1140001 390 40553084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1140391 : blockSum term 1140391 391 37421330 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1140782 : blockSum term 1140782 390 52992885 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1141172 : blockSum term 1141172 391 46742595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1141563 : blockSum term 1141563 390 34265329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1141953 : blockSum term 1141953 391 45151932 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1142344 : blockSum term 1142344 391 35797771 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1142735 : blockSum term 1142735 391 54454347 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1143126 : blockSum term 1143126 390 35772591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1143516 : blockSum term 1143516 391 37314352 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1143907 : blockSum term 1143907 390 43516289 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1144297 : blockSum term 1144297 391 46609357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1144688 : blockSum term 1144688 390 43486087 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1145078 : blockSum term 1145078 391 46575815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1145469 : blockSum term 1145469 391 40350786 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1145860 : blockSum term 1145860 391 27925622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1146251 : blockSum term 1146251 390 37221137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1146641 : blockSum term 1146641 391 55812080 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1147032 : blockSum term 1147032 390 51143241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1147422 : blockSum term 1147422 391 43380506 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1147813 : blockSum term 1147813 390 34071865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1148203 : blockSum term 1148203 391 35607830 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1148594 : blockSum term 1148594 391 46427818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1148985 : blockSum term 1148985 391 41770292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1149376 : blockSum term 1149376 390 43302630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1149766 : blockSum term 1149766 391 46379042 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1150157 : blockSum term 1150157 390 41726796 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1150547 : blockSum term 1150547 391 52525965 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1150938 : blockSum term 1150938 390 47873988 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1151328 : blockSum term 1151328 391 49400799 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1151719 : blockSum term 1151719 391 37037300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1152110 : blockSum term 1152110 391 35483003 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1152501 : blockSum term 1152501 390 43179650 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1152891 : blockSum term 1152891 391 53953753 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1153282 : blockSum term 1153282 390 40066681 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1153672 : blockSum term 1153672 391 36972118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1154063 : blockSum term 1154063 390 43117776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1154453 : blockSum term 1154453 391 38485660 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1154844 : blockSum term 1154844 391 43088505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1155235 : blockSum term 1155235 391 41534023 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1155626 : blockSum term 1155626 390 50745553 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1156016 : blockSum term 1156016 391 47654505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1156407 : blockSum term 1156407 390 44563726 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1156797 : blockSum term 1156797 391 41475536 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1157188 : blockSum term 1157188 390 46069328 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1157578 : blockSum term 1157578 391 44517671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1157969 : blockSum term 1157969 391 41432292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1158360 : blockSum term 1158360 391 52155827 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1158751 : blockSum term 1158751 390 44469445 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1159141 : blockSum term 1159141 391 41387545 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1159532 : blockSum term 1159532 390 36775086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1159922 : blockSum term 1159922 391 42889606 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1160313 : blockSum term 1160313 390 42876268 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1160703 : blockSum term 1160703 391 42859922 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1161094 : blockSum term 1161094 391 45905633 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1161485 : blockSum term 1161485 391 48949058 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1161876 : blockSum term 1161876 390 39756639 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1162266 : blockSum term 1162266 391 50442062 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1162657 : blockSum term 1162657 390 55008829 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1163047 : blockSum term 1163047 391 47352785 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1163438 : blockSum term 1163438 390 50388839 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1163828 : blockSum term 1163828 391 42739218 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1164219 : blockSum term 1164219 391 39671119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1164610 : blockSum term 1164610 391 41184059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1165001 : blockSum term 1165001 390 47269323 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1165391 : blockSum term 1165391 391 32009227 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1165782 : blockSum term 1165782 390 51806816 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1166172 : blockSum term 1166172 391 36555513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1166563 : blockSum term 1166563 390 45679810 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1166953 : blockSum term 1166953 391 39574064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1167344 : blockSum term 1167344 391 45645766 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1167735 : blockSum term 1167735 391 39547543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1168126 : blockSum term 1168126 390 44094296 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1168516 : blockSum term 1168516 391 39518026 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1168907 : blockSum term 1168907 390 44063614 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1169297 : blockSum term 1169297 391 47084975 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1169688 : blockSum term 1169688 390 36439739 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1170078 : blockSum term 1170078 391 42499492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1170469 : blockSum term 1170469 391 51587931 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1170860 : blockSum term 1170860 391 37917813 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1171251 : blockSum term 1171251 390 39420775 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1171641 : blockSum term 1171641 391 45468581 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1172032 : blockSum term 1172032 390 34847892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1172422 : blockSum term 1172422 391 43923732 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1172813 : blockSum term 1172813 390 40880180 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1173203 : blockSum term 1173203 391 40865597 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1173594 : blockSum term 1173594 391 34799350 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1173985 : blockSum term 1173985 391 42350918 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1174376 : blockSum term 1174376 390 46871981 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1174766 : blockSum term 1174766 391 42321345 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1175157 : blockSum term 1175157 390 36262252 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1175547 : blockSum term 1175547 391 46823368 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1175938 : blockSum term 1175938 390 42278411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1176328 : blockSum term 1176328 391 45281299 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1176719 : blockSum term 1176719 391 40738579 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1177110 : blockSum term 1177110 391 40724707 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1177501 : blockSum term 1177501 390 45234006 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1177891 : blockSum term 1177891 391 54260361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1178282 : blockSum term 1178282 390 37667728 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1178672 : blockSum term 1178672 391 46692872 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1179063 : blockSum term 1179063 390 46674781 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1179453 : blockSum term 1179453 391 34618589 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1179844 : blockSum term 1179844 391 52662316 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1180235 : blockSum term 1180235 391 40611400 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1180626 : blockSum term 1180626 390 55632642 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1181016 : blockSum term 1181016 391 39080701 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1181407 : blockSum term 1181407 390 46579286 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1181797 : blockSum term 1181797 391 33044843 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1182188 : blockSum term 1182188 390 45044561 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1182578 : blockSum term 1182578 391 43527637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1182969 : blockSum term 1182969 391 45012565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1183360 : blockSum term 1183360 391 38997250 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1183751 : blockSum term 1183751 390 49479385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1184141 : blockSum term 1184141 391 47962989 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1184532 : blockSum term 1184532 390 34462348 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1184922 : blockSum term 1184922 391 37447185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1185313 : blockSum term 1185313 390 52406381 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1185703 : blockSum term 1185703 391 44903828 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1186094 : blockSum term 1186094 391 34415028 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1186485 : blockSum term 1186485 391 37393452 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1186876 : blockSum term 1186876 390 35885507 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1187266 : blockSum term 1187266 391 47832512 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1187657 : blockSum term 1187657 390 53792075 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1188047 : blockSum term 1188047 391 43317904 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1188438 : blockSum term 1188438 390 37330147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1188828 : blockSum term 1188828 391 44780202 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1189219 : blockSum term 1189219 391 35811745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1189610 : blockSum term 1189610 391 47733609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 1090001 100000 11316245065 := (join_sums term (lo:=1090001) (a:=50000) (b:=50000) (join_sums term (lo:=1090001) (a:=25000) (b:=25000) (join_sums term (lo:=1090001) (a:=12500) (b:=12500) (join_sums term (lo:=1090001) (a:=6250) (b:=6250) (join_sums term (lo:=1090001) (a:=3125) (b:=3125) (join_sums term (lo:=1090001) (a:=1562) (b:=1563) (join_sums term (lo:=1090001) (a:=781) (b:=781) (join_sums term (lo:=1090001) (a:=390) (b:=391) r1090001 r1090391) (join_sums term (lo:=1090782) (a:=390) (b:=391) r1090782 r1091172)) (join_sums term (lo:=1091563) (a:=781) (b:=782) (join_sums term (lo:=1091563) (a:=390) (b:=391) r1091563 r1091953) (join_sums term (lo:=1092344) (a:=391) (b:=391) r1092344 r1092735))) (join_sums term (lo:=1093126) (a:=1562) (b:=1563) (join_sums term (lo:=1093126) (a:=781) (b:=781) (join_sums term (lo:=1093126) (a:=390) (b:=391) r1093126 r1093516) (join_sums term (lo:=1093907) (a:=390) (b:=391) r1093907 r1094297)) (join_sums term (lo:=1094688) (a:=781) (b:=782) (join_sums term (lo:=1094688) (a:=390) (b:=391) r1094688 r1095078) (join_sums term (lo:=1095469) (a:=391) (b:=391) r1095469 r1095860)))) (join_sums term (lo:=1096251) (a:=3125) (b:=3125) (join_sums term (lo:=1096251) (a:=1562) (b:=1563) (join_sums term (lo:=1096251) (a:=781) (b:=781) (join_sums term (lo:=1096251) (a:=390) (b:=391) r1096251 r1096641) (join_sums term (lo:=1097032) (a:=390) (b:=391) r1097032 r1097422)) (join_sums term (lo:=1097813) (a:=781) (b:=782) (join_sums term (lo:=1097813) (a:=390) (b:=391) r1097813 r1098203) (join_sums term (lo:=1098594) (a:=391) (b:=391) r1098594 r1098985))) (join_sums term (lo:=1099376) (a:=1562) (b:=1563) (join_sums term (lo:=1099376) (a:=781) (b:=781) (join_sums term (lo:=1099376) (a:=390) (b:=391) r1099376 r1099766) (join_sums term (lo:=1100157) (a:=390) (b:=391) r1100157 r1100547)) (join_sums term (lo:=1100938) (a:=781) (b:=782) (join_sums term (lo:=1100938) (a:=390) (b:=391) r1100938 r1101328) (join_sums term (lo:=1101719) (a:=391) (b:=391) r1101719 r1102110))))) (join_sums term (lo:=1102501) (a:=6250) (b:=6250) (join_sums term (lo:=1102501) (a:=3125) (b:=3125) (join_sums term (lo:=1102501) (a:=1562) (b:=1563) (join_sums term (lo:=1102501) (a:=781) (b:=781) (join_sums term (lo:=1102501) (a:=390) (b:=391) r1102501 r1102891) (join_sums term (lo:=1103282) (a:=390) (b:=391) r1103282 r1103672)) (join_sums term (lo:=1104063) (a:=781) (b:=782) (join_sums term (lo:=1104063) (a:=390) (b:=391) r1104063 r1104453) (join_sums term (lo:=1104844) (a:=391) (b:=391) r1104844 r1105235))) (join_sums term (lo:=1105626) (a:=1562) (b:=1563) (join_sums term (lo:=1105626) (a:=781) (b:=781) (join_sums term (lo:=1105626) (a:=390) (b:=391) r1105626 r1106016) (join_sums term (lo:=1106407) (a:=390) (b:=391) r1106407 r1106797)) (join_sums term (lo:=1107188) (a:=781) (b:=782) (join_sums term (lo:=1107188) (a:=390) (b:=391) r1107188 r1107578) (join_sums term (lo:=1107969) (a:=391) (b:=391) r1107969 r1108360)))) (join_sums term (lo:=1108751) (a:=3125) (b:=3125) (join_sums term (lo:=1108751) (a:=1562) (b:=1563) (join_sums term (lo:=1108751) (a:=781) (b:=781) (join_sums term (lo:=1108751) (a:=390) (b:=391) r1108751 r1109141) (join_sums term (lo:=1109532) (a:=390) (b:=391) r1109532 r1109922)) (join_sums term (lo:=1110313) (a:=781) (b:=782) (join_sums term (lo:=1110313) (a:=390) (b:=391) r1110313 r1110703) (join_sums term (lo:=1111094) (a:=391) (b:=391) r1111094 r1111485))) (join_sums term (lo:=1111876) (a:=1562) (b:=1563) (join_sums term (lo:=1111876) (a:=781) (b:=781) (join_sums term (lo:=1111876) (a:=390) (b:=391) r1111876 r1112266) (join_sums term (lo:=1112657) (a:=390) (b:=391) r1112657 r1113047)) (join_sums term (lo:=1113438) (a:=781) (b:=782) (join_sums term (lo:=1113438) (a:=390) (b:=391) r1113438 r1113828) (join_sums term (lo:=1114219) (a:=391) (b:=391) r1114219 r1114610)))))) (join_sums term (lo:=1115001) (a:=12500) (b:=12500) (join_sums term (lo:=1115001) (a:=6250) (b:=6250) (join_sums term (lo:=1115001) (a:=3125) (b:=3125) (join_sums term (lo:=1115001) (a:=1562) (b:=1563) (join_sums term (lo:=1115001) (a:=781) (b:=781) (join_sums term (lo:=1115001) (a:=390) (b:=391) r1115001 r1115391) (join_sums term (lo:=1115782) (a:=390) (b:=391) r1115782 r1116172)) (join_sums term (lo:=1116563) (a:=781) (b:=782) (join_sums term (lo:=1116563) (a:=390) (b:=391) r1116563 r1116953) (join_sums term (lo:=1117344) (a:=391) (b:=391) r1117344 r1117735))) (join_sums term (lo:=1118126) (a:=1562) (b:=1563) (join_sums term (lo:=1118126) (a:=781) (b:=781) (join_sums term (lo:=1118126) (a:=390) (b:=391) r1118126 r1118516) (join_sums term (lo:=1118907) (a:=390) (b:=391) r1118907 r1119297)) (join_sums term (lo:=1119688) (a:=781) (b:=782) (join_sums term (lo:=1119688) (a:=390) (b:=391) r1119688 r1120078) (join_sums term (lo:=1120469) (a:=391) (b:=391) r1120469 r1120860)))) (join_sums term (lo:=1121251) (a:=3125) (b:=3125) (join_sums term (lo:=1121251) (a:=1562) (b:=1563) (join_sums term (lo:=1121251) (a:=781) (b:=781) (join_sums term (lo:=1121251) (a:=390) (b:=391) r1121251 r1121641) (join_sums term (lo:=1122032) (a:=390) (b:=391) r1122032 r1122422)) (join_sums term (lo:=1122813) (a:=781) (b:=782) (join_sums term (lo:=1122813) (a:=390) (b:=391) r1122813 r1123203) (join_sums term (lo:=1123594) (a:=391) (b:=391) r1123594 r1123985))) (join_sums term (lo:=1124376) (a:=1562) (b:=1563) (join_sums term (lo:=1124376) (a:=781) (b:=781) (join_sums term (lo:=1124376) (a:=390) (b:=391) r1124376 r1124766) (join_sums term (lo:=1125157) (a:=390) (b:=391) r1125157 r1125547)) (join_sums term (lo:=1125938) (a:=781) (b:=782) (join_sums term (lo:=1125938) (a:=390) (b:=391) r1125938 r1126328) (join_sums term (lo:=1126719) (a:=391) (b:=391) r1126719 r1127110))))) (join_sums term (lo:=1127501) (a:=6250) (b:=6250) (join_sums term (lo:=1127501) (a:=3125) (b:=3125) (join_sums term (lo:=1127501) (a:=1562) (b:=1563) (join_sums term (lo:=1127501) (a:=781) (b:=781) (join_sums term (lo:=1127501) (a:=390) (b:=391) r1127501 r1127891) (join_sums term (lo:=1128282) (a:=390) (b:=391) r1128282 r1128672)) (join_sums term (lo:=1129063) (a:=781) (b:=782) (join_sums term (lo:=1129063) (a:=390) (b:=391) r1129063 r1129453) (join_sums term (lo:=1129844) (a:=391) (b:=391) r1129844 r1130235))) (join_sums term (lo:=1130626) (a:=1562) (b:=1563) (join_sums term (lo:=1130626) (a:=781) (b:=781) (join_sums term (lo:=1130626) (a:=390) (b:=391) r1130626 r1131016) (join_sums term (lo:=1131407) (a:=390) (b:=391) r1131407 r1131797)) (join_sums term (lo:=1132188) (a:=781) (b:=782) (join_sums term (lo:=1132188) (a:=390) (b:=391) r1132188 r1132578) (join_sums term (lo:=1132969) (a:=391) (b:=391) r1132969 r1133360)))) (join_sums term (lo:=1133751) (a:=3125) (b:=3125) (join_sums term (lo:=1133751) (a:=1562) (b:=1563) (join_sums term (lo:=1133751) (a:=781) (b:=781) (join_sums term (lo:=1133751) (a:=390) (b:=391) r1133751 r1134141) (join_sums term (lo:=1134532) (a:=390) (b:=391) r1134532 r1134922)) (join_sums term (lo:=1135313) (a:=781) (b:=782) (join_sums term (lo:=1135313) (a:=390) (b:=391) r1135313 r1135703) (join_sums term (lo:=1136094) (a:=391) (b:=391) r1136094 r1136485))) (join_sums term (lo:=1136876) (a:=1562) (b:=1563) (join_sums term (lo:=1136876) (a:=781) (b:=781) (join_sums term (lo:=1136876) (a:=390) (b:=391) r1136876 r1137266) (join_sums term (lo:=1137657) (a:=390) (b:=391) r1137657 r1138047)) (join_sums term (lo:=1138438) (a:=781) (b:=782) (join_sums term (lo:=1138438) (a:=390) (b:=391) r1138438 r1138828) (join_sums term (lo:=1139219) (a:=391) (b:=391) r1139219 r1139610))))))) (join_sums term (lo:=1140001) (a:=25000) (b:=25000) (join_sums term (lo:=1140001) (a:=12500) (b:=12500) (join_sums term (lo:=1140001) (a:=6250) (b:=6250) (join_sums term (lo:=1140001) (a:=3125) (b:=3125) (join_sums term (lo:=1140001) (a:=1562) (b:=1563) (join_sums term (lo:=1140001) (a:=781) (b:=781) (join_sums term (lo:=1140001) (a:=390) (b:=391) r1140001 r1140391) (join_sums term (lo:=1140782) (a:=390) (b:=391) r1140782 r1141172)) (join_sums term (lo:=1141563) (a:=781) (b:=782) (join_sums term (lo:=1141563) (a:=390) (b:=391) r1141563 r1141953) (join_sums term (lo:=1142344) (a:=391) (b:=391) r1142344 r1142735))) (join_sums term (lo:=1143126) (a:=1562) (b:=1563) (join_sums term (lo:=1143126) (a:=781) (b:=781) (join_sums term (lo:=1143126) (a:=390) (b:=391) r1143126 r1143516) (join_sums term (lo:=1143907) (a:=390) (b:=391) r1143907 r1144297)) (join_sums term (lo:=1144688) (a:=781) (b:=782) (join_sums term (lo:=1144688) (a:=390) (b:=391) r1144688 r1145078) (join_sums term (lo:=1145469) (a:=391) (b:=391) r1145469 r1145860)))) (join_sums term (lo:=1146251) (a:=3125) (b:=3125) (join_sums term (lo:=1146251) (a:=1562) (b:=1563) (join_sums term (lo:=1146251) (a:=781) (b:=781) (join_sums term (lo:=1146251) (a:=390) (b:=391) r1146251 r1146641) (join_sums term (lo:=1147032) (a:=390) (b:=391) r1147032 r1147422)) (join_sums term (lo:=1147813) (a:=781) (b:=782) (join_sums term (lo:=1147813) (a:=390) (b:=391) r1147813 r1148203) (join_sums term (lo:=1148594) (a:=391) (b:=391) r1148594 r1148985))) (join_sums term (lo:=1149376) (a:=1562) (b:=1563) (join_sums term (lo:=1149376) (a:=781) (b:=781) (join_sums term (lo:=1149376) (a:=390) (b:=391) r1149376 r1149766) (join_sums term (lo:=1150157) (a:=390) (b:=391) r1150157 r1150547)) (join_sums term (lo:=1150938) (a:=781) (b:=782) (join_sums term (lo:=1150938) (a:=390) (b:=391) r1150938 r1151328) (join_sums term (lo:=1151719) (a:=391) (b:=391) r1151719 r1152110))))) (join_sums term (lo:=1152501) (a:=6250) (b:=6250) (join_sums term (lo:=1152501) (a:=3125) (b:=3125) (join_sums term (lo:=1152501) (a:=1562) (b:=1563) (join_sums term (lo:=1152501) (a:=781) (b:=781) (join_sums term (lo:=1152501) (a:=390) (b:=391) r1152501 r1152891) (join_sums term (lo:=1153282) (a:=390) (b:=391) r1153282 r1153672)) (join_sums term (lo:=1154063) (a:=781) (b:=782) (join_sums term (lo:=1154063) (a:=390) (b:=391) r1154063 r1154453) (join_sums term (lo:=1154844) (a:=391) (b:=391) r1154844 r1155235))) (join_sums term (lo:=1155626) (a:=1562) (b:=1563) (join_sums term (lo:=1155626) (a:=781) (b:=781) (join_sums term (lo:=1155626) (a:=390) (b:=391) r1155626 r1156016) (join_sums term (lo:=1156407) (a:=390) (b:=391) r1156407 r1156797)) (join_sums term (lo:=1157188) (a:=781) (b:=782) (join_sums term (lo:=1157188) (a:=390) (b:=391) r1157188 r1157578) (join_sums term (lo:=1157969) (a:=391) (b:=391) r1157969 r1158360)))) (join_sums term (lo:=1158751) (a:=3125) (b:=3125) (join_sums term (lo:=1158751) (a:=1562) (b:=1563) (join_sums term (lo:=1158751) (a:=781) (b:=781) (join_sums term (lo:=1158751) (a:=390) (b:=391) r1158751 r1159141) (join_sums term (lo:=1159532) (a:=390) (b:=391) r1159532 r1159922)) (join_sums term (lo:=1160313) (a:=781) (b:=782) (join_sums term (lo:=1160313) (a:=390) (b:=391) r1160313 r1160703) (join_sums term (lo:=1161094) (a:=391) (b:=391) r1161094 r1161485))) (join_sums term (lo:=1161876) (a:=1562) (b:=1563) (join_sums term (lo:=1161876) (a:=781) (b:=781) (join_sums term (lo:=1161876) (a:=390) (b:=391) r1161876 r1162266) (join_sums term (lo:=1162657) (a:=390) (b:=391) r1162657 r1163047)) (join_sums term (lo:=1163438) (a:=781) (b:=782) (join_sums term (lo:=1163438) (a:=390) (b:=391) r1163438 r1163828) (join_sums term (lo:=1164219) (a:=391) (b:=391) r1164219 r1164610)))))) (join_sums term (lo:=1165001) (a:=12500) (b:=12500) (join_sums term (lo:=1165001) (a:=6250) (b:=6250) (join_sums term (lo:=1165001) (a:=3125) (b:=3125) (join_sums term (lo:=1165001) (a:=1562) (b:=1563) (join_sums term (lo:=1165001) (a:=781) (b:=781) (join_sums term (lo:=1165001) (a:=390) (b:=391) r1165001 r1165391) (join_sums term (lo:=1165782) (a:=390) (b:=391) r1165782 r1166172)) (join_sums term (lo:=1166563) (a:=781) (b:=782) (join_sums term (lo:=1166563) (a:=390) (b:=391) r1166563 r1166953) (join_sums term (lo:=1167344) (a:=391) (b:=391) r1167344 r1167735))) (join_sums term (lo:=1168126) (a:=1562) (b:=1563) (join_sums term (lo:=1168126) (a:=781) (b:=781) (join_sums term (lo:=1168126) (a:=390) (b:=391) r1168126 r1168516) (join_sums term (lo:=1168907) (a:=390) (b:=391) r1168907 r1169297)) (join_sums term (lo:=1169688) (a:=781) (b:=782) (join_sums term (lo:=1169688) (a:=390) (b:=391) r1169688 r1170078) (join_sums term (lo:=1170469) (a:=391) (b:=391) r1170469 r1170860)))) (join_sums term (lo:=1171251) (a:=3125) (b:=3125) (join_sums term (lo:=1171251) (a:=1562) (b:=1563) (join_sums term (lo:=1171251) (a:=781) (b:=781) (join_sums term (lo:=1171251) (a:=390) (b:=391) r1171251 r1171641) (join_sums term (lo:=1172032) (a:=390) (b:=391) r1172032 r1172422)) (join_sums term (lo:=1172813) (a:=781) (b:=782) (join_sums term (lo:=1172813) (a:=390) (b:=391) r1172813 r1173203) (join_sums term (lo:=1173594) (a:=391) (b:=391) r1173594 r1173985))) (join_sums term (lo:=1174376) (a:=1562) (b:=1563) (join_sums term (lo:=1174376) (a:=781) (b:=781) (join_sums term (lo:=1174376) (a:=390) (b:=391) r1174376 r1174766) (join_sums term (lo:=1175157) (a:=390) (b:=391) r1175157 r1175547)) (join_sums term (lo:=1175938) (a:=781) (b:=782) (join_sums term (lo:=1175938) (a:=390) (b:=391) r1175938 r1176328) (join_sums term (lo:=1176719) (a:=391) (b:=391) r1176719 r1177110))))) (join_sums term (lo:=1177501) (a:=6250) (b:=6250) (join_sums term (lo:=1177501) (a:=3125) (b:=3125) (join_sums term (lo:=1177501) (a:=1562) (b:=1563) (join_sums term (lo:=1177501) (a:=781) (b:=781) (join_sums term (lo:=1177501) (a:=390) (b:=391) r1177501 r1177891) (join_sums term (lo:=1178282) (a:=390) (b:=391) r1178282 r1178672)) (join_sums term (lo:=1179063) (a:=781) (b:=782) (join_sums term (lo:=1179063) (a:=390) (b:=391) r1179063 r1179453) (join_sums term (lo:=1179844) (a:=391) (b:=391) r1179844 r1180235))) (join_sums term (lo:=1180626) (a:=1562) (b:=1563) (join_sums term (lo:=1180626) (a:=781) (b:=781) (join_sums term (lo:=1180626) (a:=390) (b:=391) r1180626 r1181016) (join_sums term (lo:=1181407) (a:=390) (b:=391) r1181407 r1181797)) (join_sums term (lo:=1182188) (a:=781) (b:=782) (join_sums term (lo:=1182188) (a:=390) (b:=391) r1182188 r1182578) (join_sums term (lo:=1182969) (a:=391) (b:=391) r1182969 r1183360)))) (join_sums term (lo:=1183751) (a:=3125) (b:=3125) (join_sums term (lo:=1183751) (a:=1562) (b:=1563) (join_sums term (lo:=1183751) (a:=781) (b:=781) (join_sums term (lo:=1183751) (a:=390) (b:=391) r1183751 r1184141) (join_sums term (lo:=1184532) (a:=390) (b:=391) r1184532 r1184922)) (join_sums term (lo:=1185313) (a:=781) (b:=782) (join_sums term (lo:=1185313) (a:=390) (b:=391) r1185313 r1185703) (join_sums term (lo:=1186094) (a:=391) (b:=391) r1186094 r1186485))) (join_sums term (lo:=1186876) (a:=1562) (b:=1563) (join_sums term (lo:=1186876) (a:=781) (b:=781) (join_sums term (lo:=1186876) (a:=390) (b:=391) r1186876 r1187266) (join_sums term (lo:=1187657) (a:=390) (b:=391) r1187657 r1188047)) (join_sums term (lo:=1188438) (a:=781) (b:=782) (join_sums term (lo:=1188438) (a:=390) (b:=391) r1188438 r1188828) (join_sums term (lo:=1189219) (a:=391) (b:=391) r1189219 r1189610))))))))

private theorem rows : blockSum term 0 1190001 11316245065 :=
  join_sums term (lo:=0) (a:=1090001) (b:=100000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 1190000).filter (1090000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=11316245065 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From1090000To1190000
