import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 1,085,000 through 1,202,598

The sum covers 8,481 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction11092009835083From1085000To1202598

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


private abbrev term := contribution 11092009835083 1085000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 1085001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 1085000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r1085001 : blockSum term 1085001 459 18995143 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1085460 : blockSum term 1085460 459 17798546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1085919 : blockSum term 1085919 459 21347712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1086378 : blockSum term 1086378 460 18374529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1086838 : blockSum term 1086838 459 16588284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1087297 : blockSum term 1087297 459 20131994 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1087756 : blockSum term 1087756 459 19530753 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1088215 : blockSum term 1088215 460 22478031 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1088675 : blockSum term 1088675 459 18328747 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1089134 : blockSum term 1089134 459 15955506 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1089593 : blockSum term 1089593 459 15357111 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1090052 : blockSum term 1090052 460 18301111 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1090512 : blockSum term 1090512 459 21241828 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1090971 : blockSum term 1090971 460 25360386 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1091431 : blockSum term 1091431 459 20042405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1091890 : blockSum term 1091890 460 18853344 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1092350 : blockSum term 1092350 459 17667430 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1092809 : blockSum term 1092809 459 22366645 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1093268 : blockSum term 1093268 459 21766529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1093727 : blockSum term 1093727 460 23518822 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1094187 : blockSum term 1094187 459 19392147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1094646 : blockSum term 1094646 460 21733063 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1095106 : blockSum term 1095106 459 19373279 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1095565 : blockSum term 1095565 460 18776970 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1096025 : blockSum term 1096025 459 17594348 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1096484 : blockSum term 1096484 459 18758440 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1096943 : blockSum term 1096943 459 19920872 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1097402 : blockSum term 1097402 460 19324726 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1097862 : blockSum term 1097862 459 19315340 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1098321 : blockSum term 1098321 460 16380548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1098781 : blockSum term 1098781 459 14617944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1099240 : blockSum term 1099240 460 22793205 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1099700 : blockSum term 1099700 459 21613407 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1100159 : blockSum term 1100159 459 20434315 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1100618 : blockSum term 1100618 459 14588708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1101077 : blockSum term 1101077 460 20996438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1101537 : blockSum term 1101537 459 19820796 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1101996 : blockSum term 1101996 460 20393358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1102456 : blockSum term 1102456 459 20382591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1102915 : blockSum term 1102915 460 20372755 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1103375 : blockSum term 1103375 459 16871620 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1103834 : blockSum term 1103834 459 18607586 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1104293 : blockSum term 1104293 459 21503526 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1104752 : blockSum term 1104752 460 20331303 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1105212 : blockSum term 1105212 459 22642011 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1105671 : blockSum term 1105671 460 16248168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1106131 : blockSum term 1106131 459 21460452 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1106590 : blockSum term 1106590 460 20868953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1107050 : blockSum term 1107050 459 16223031 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1107509 : blockSum term 1107509 459 19689912 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1107968 : blockSum term 1107968 459 19101182 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1108427 : blockSum term 1108427 460 24877312 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1108887 : blockSum term 1108887 459 16768749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1109346 : blockSum term 1109346 460 18494954 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1109806 : blockSum term 1109806 459 17908183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1110265 : blockSum term 1110265 460 20786059 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1110725 : blockSum term 1110725 459 23083657 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1111184 : blockSum term 1111184 459 19035019 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1111643 : blockSum term 1111643 459 19602177 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1112102 : blockSum term 1112102 460 20744868 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1112562 : blockSum term 1112562 459 21886393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1113021 : blockSum term 1113021 460 17270062 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1113481 : blockSum term 1113481 459 16686145 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1113940 : blockSum term 1113940 460 18403558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1114400 : blockSum term 1114400 459 20118438 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1114859 : blockSum term 1114859 459 18385178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1115318 : blockSum term 1115318 459 23544200 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1115777 : blockSum term 1115777 460 14348924 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1116237 : blockSum term 1116237 459 18931296 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1116696 : blockSum term 1116696 460 17774286 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1117156 : blockSum term 1117156 459 19484705 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1117615 : blockSum term 1117615 460 22339142 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1118075 : blockSum term 1118075 459 16603395 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1118534 : blockSum term 1118534 459 19455527 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1118993 : blockSum term 1118993 459 14299132 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1119452 : blockSum term 1119452 460 17150416 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1119912 : blockSum term 1119912 459 17713170 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1120371 : blockSum term 1120371 460 23415886 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1120831 : blockSum term 1120831 459 20550317 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1121290 : blockSum term 1121290 460 17687195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1121750 : blockSum term 1121750 459 15966796 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1122209 : blockSum term 1122209 459 17099601 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1122668 : blockSum term 1122668 459 12533941 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1123127 : blockSum term 1123127 460 20499596 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1123587 : blockSum term 1123587 459 21058816 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1124046 : blockSum term 1124046 460 17635308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1124506 : blockSum term 1124506 459 17058172 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1124965 : blockSum term 1124965 460 21027123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1125425 : blockSum term 1125425 459 17040578 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1125884 : blockSum term 1125884 459 14761888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1126343 : blockSum term 1126343 459 21564167 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1126802 : blockSum term 1126802 460 18717302 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1127262 : blockSum term 1127262 459 20976510 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1127721 : blockSum term 1127721 460 15866177 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1128181 : blockSum term 1128181 459 20955277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1128640 : blockSum term 1128640 460 20945385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1129100 : blockSum term 1129100 459 19237431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1129559 : blockSum term 1129559 459 18661910 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1130018 : blockSum term 1130018 459 18086791 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1130477 : blockSum term 1130477 460 16948600 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1130937 : blockSum term 1130937 459 20893136 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1131396 : blockSum term 1131396 460 19753291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1131856 : blockSum term 1131856 459 16923366 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1132315 : blockSum term 1132315 460 20297091 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1132775 : blockSum term 1132775 459 20286595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1133234 : blockSum term 1133234 459 20275934 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1133693 : blockSum term 1133693 459 18577052 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1134152 : blockSum term 1134152 460 18568183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1134612 : blockSum term 1134612 459 17996788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1135071 : blockSum term 1135071 460 19674995 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1135531 : blockSum term 1135531 459 17978953 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1135990 : blockSum term 1135990 460 19655706 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1136450 : blockSum term 1136450 459 17961799 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1136909 : blockSum term 1136909 459 17953236 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1137368 : blockSum term 1137368 459 16822529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1137827 : blockSum term 1137827 460 16254775 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1138287 : blockSum term 1138287 459 17926215 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1138746 : blockSum term 1138746 460 17918228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1139206 : blockSum term 1139206 459 17909377 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1139665 : blockSum term 1139665 460 16781847 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1140125 : blockSum term 1140125 459 20127240 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1140584 : blockSum term 1140584 459 18439764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1141043 : blockSum term 1141043 459 20107120 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1141502 : blockSum term 1141502 460 15073405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1141962 : blockSum term 1141962 459 18972121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1142421 : blockSum term 1142421 460 16731330 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1142881 : blockSum term 1142881 459 20068161 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1143340 : blockSum term 1143340 460 15043625 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1143800 : blockSum term 1143800 459 16707236 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1144259 : blockSum term 1144259 459 20039494 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1144718 : blockSum term 1144718 459 18916608 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1145177 : blockSum term 1145177 460 18351434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1145637 : blockSum term 1145637 459 15563022 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1146096 : blockSum term 1146096 459 14999341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1146555 : blockSum term 1146555 459 21100392 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1147014 : blockSum term 1147014 460 22754769 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1147474 : blockSum term 1147474 459 16086700 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1147933 : blockSum term 1147933 459 14969689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1148392 : blockSum term 1148392 459 16070805 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1148851 : blockSum term 1148851 460 18832813 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1149311 : blockSum term 1149311 459 18269933 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1149770 : blockSum term 1149770 460 20473372 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1150230 : blockSum term 1150230 459 17144595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1150689 : blockSum term 1150689 460 21006553 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1151149 : blockSum term 1151149 459 20443506 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1151608 : blockSum term 1151608 459 16568029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1152067 : blockSum term 1152067 459 16560130 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1152526 : blockSum term 1152526 460 16551339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1152986 : blockSum term 1152986 459 21506799 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1153445 : blockSum term 1153445 460 17637491 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1153905 : blockSum term 1153905 459 17627885 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1154364 : blockSum term 1154364 460 16518958 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1154824 : blockSum term 1154824 459 17061361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1155283 : blockSum term 1155283 459 18703133 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1155742 : blockSum term 1155742 459 20343635 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1156201 : blockSum term 1156201 460 19784290 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1156661 : blockSum term 1156661 459 17577328 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1157120 : blockSum term 1157120 460 19764541 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1157580 : blockSum term 1157580 459 18656284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1158039 : blockSum term 1158039 460 18646148 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1158499 : blockSum term 1158499 459 19185905 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1158958 : blockSum term 1158958 459 18080441 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1159417 : blockSum term 1159417 459 15333513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1159876 : blockSum term 1159876 460 18610370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1160336 : blockSum term 1160336 459 16960541 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1160795 : blockSum term 1160795 460 20232062 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1161255 : blockSum term 1161255 459 20222324 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1161714 : blockSum term 1161714 460 16935005 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1162174 : blockSum term 1162174 459 21293891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1162633 : blockSum term 1162633 459 22374692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1163092 : blockSum term 1163092 459 19091865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1163551 : blockSum term 1163551 460 21262511 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1164011 : blockSum term 1164011 459 14712846 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1164470 : blockSum term 1164470 460 17974342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1164930 : blockSum term 1164930 459 20687116 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1165389 : blockSum term 1165389 460 14691337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1165849 : blockSum term 1165849 459 17948615 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1166308 : blockSum term 1166308 459 19026287 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1166767 : blockSum term 1166767 459 16843543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1167226 : blockSum term 1167226 460 17377991 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1167686 : blockSum term 1167686 459 18455944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1168145 : blockSum term 1168145 460 16818872 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1168605 : blockSum term 1168605 459 20605802 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1169064 : blockSum term 1169064 460 17885216 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1169524 : blockSum term 1169524 459 15168740 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1169983 : blockSum term 1169983 459 17869213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1170442 : blockSum term 1170442 459 21107557 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1170901 : blockSum term 1170901 460 15687331 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1171361 : blockSum term 1171361 459 16760789 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1171820 : blockSum term 1171820 460 17833929 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1172280 : blockSum term 1172280 459 17284760 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1172739 : blockSum term 1172739 460 17276730 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1173199 : blockSum term 1173199 459 16189300 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1173658 : blockSum term 1173658 459 16181044 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1174117 : blockSum term 1174117 459 18868983 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1174576 : blockSum term 1174576 460 18859986 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1175036 : blockSum term 1175036 459 15618907 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1175495 : blockSum term 1175495 460 19379800 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1175955 : blockSum term 1175955 459 18294609 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1176414 : blockSum term 1176414 460 17210022 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1176874 : blockSum term 1176874 459 18277086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1177333 : blockSum term 1177333 459 18805065 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1177792 : blockSum term 1177792 459 20406731 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1178251 : blockSum term 1178251 460 17176266 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1178711 : blockSum term 1178711 459 16632315 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1179170 : blockSum term 1179170 460 20914052 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1179630 : blockSum term 1179630 459 19295066 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1180089 : blockSum term 1180089 460 18214850 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1180549 : blockSum term 1180549 459 21418086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1181008 : blockSum term 1181008 459 16591773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1181467 : blockSum term 1181467 459 17653285 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1181926 : blockSum term 1181926 460 14971013 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1182386 : blockSum term 1182386 459 19239670 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1182845 : blockSum term 1182845 460 19764213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1183305 : blockSum term 1183305 459 16551279 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1183764 : blockSum term 1183764 460 19745210 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1184224 : blockSum term 1184224 459 18668970 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1184683 : blockSum term 1184683 459 17059917 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1185142 : blockSum term 1185142 459 15452996 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1185601 : blockSum term 1185601 460 21304819 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1186061 : blockSum term 1186061 459 15438494 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1186520 : blockSum term 1186520 460 14366282 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1186980 : blockSum term 1186980 459 19676751 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1187439 : blockSum term 1187439 460 19136112 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1187899 : blockSum term 1187899 459 19658244 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1188358 : blockSum term 1188358 459 16462321 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1188817 : blockSum term 1188817 459 17515939 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1189276 : blockSum term 1189276 460 17507219 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1189736 : blockSum term 1189736 459 16969052 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1190195 : blockSum term 1190195 460 15900684 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1190655 : blockSum term 1190655 459 20131068 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1191114 : blockSum term 1191114 460 16414729 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1191574 : blockSum term 1191574 459 17465512 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1192033 : blockSum term 1192033 459 19573304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1192492 : blockSum term 1192492 459 16390434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1192951 : blockSum term 1192951 460 16382862 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1193411 : blockSum term 1193411 459 20599984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1193870 : blockSum term 1193870 460 15310854 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1194330 : blockSum term 1194330 459 17414500 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1194789 : blockSum term 1194789 460 20043366 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1195249 : blockSum term 1195249 459 13179478 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1195708 : blockSum term 1195708 459 15808897 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1196167 : blockSum term 1196167 459 17907796 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1196626 : blockSum term 1196626 460 17372099 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1197086 : blockSum term 1197086 459 18942899 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1197545 : blockSum term 1197545 460 14200330 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1198005 : blockSum term 1198005 459 19976163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1198464 : blockSum term 1198464 460 14186783 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1198924 : blockSum term 1198924 459 15230258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1199383 : blockSum term 1199383 459 20996618 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1199842 : blockSum term 1199842 459 13117212 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1200301 : blockSum term 1200301 460 17830666 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1200761 : blockSum term 1200761 459 19917923 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1201220 : blockSum term 1201220 460 14145620 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1201680 : blockSum term 1201680 459 17280473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r1202139 : blockSum term 1202139 460 17272234 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 1085001 117598 4728403590 := (join_sums term (lo:=1085001) (a:=58799) (b:=58799) (join_sums term (lo:=1085001) (a:=29399) (b:=29400) (join_sums term (lo:=1085001) (a:=14699) (b:=14700) (join_sums term (lo:=1085001) (a:=7349) (b:=7350) (join_sums term (lo:=1085001) (a:=3674) (b:=3675) (join_sums term (lo:=1085001) (a:=1837) (b:=1837) (join_sums term (lo:=1085001) (a:=918) (b:=919) (join_sums term (lo:=1085001) (a:=459) (b:=459) r1085001 r1085460) (join_sums term (lo:=1085919) (a:=459) (b:=460) r1085919 r1086378)) (join_sums term (lo:=1086838) (a:=918) (b:=919) (join_sums term (lo:=1086838) (a:=459) (b:=459) r1086838 r1087297) (join_sums term (lo:=1087756) (a:=459) (b:=460) r1087756 r1088215))) (join_sums term (lo:=1088675) (a:=1837) (b:=1838) (join_sums term (lo:=1088675) (a:=918) (b:=919) (join_sums term (lo:=1088675) (a:=459) (b:=459) r1088675 r1089134) (join_sums term (lo:=1089593) (a:=459) (b:=460) r1089593 r1090052)) (join_sums term (lo:=1090512) (a:=919) (b:=919) (join_sums term (lo:=1090512) (a:=459) (b:=460) r1090512 r1090971) (join_sums term (lo:=1091431) (a:=459) (b:=460) r1091431 r1091890)))) (join_sums term (lo:=1092350) (a:=3675) (b:=3675) (join_sums term (lo:=1092350) (a:=1837) (b:=1838) (join_sums term (lo:=1092350) (a:=918) (b:=919) (join_sums term (lo:=1092350) (a:=459) (b:=459) r1092350 r1092809) (join_sums term (lo:=1093268) (a:=459) (b:=460) r1093268 r1093727)) (join_sums term (lo:=1094187) (a:=919) (b:=919) (join_sums term (lo:=1094187) (a:=459) (b:=460) r1094187 r1094646) (join_sums term (lo:=1095106) (a:=459) (b:=460) r1095106 r1095565))) (join_sums term (lo:=1096025) (a:=1837) (b:=1838) (join_sums term (lo:=1096025) (a:=918) (b:=919) (join_sums term (lo:=1096025) (a:=459) (b:=459) r1096025 r1096484) (join_sums term (lo:=1096943) (a:=459) (b:=460) r1096943 r1097402)) (join_sums term (lo:=1097862) (a:=919) (b:=919) (join_sums term (lo:=1097862) (a:=459) (b:=460) r1097862 r1098321) (join_sums term (lo:=1098781) (a:=459) (b:=460) r1098781 r1099240))))) (join_sums term (lo:=1099700) (a:=7350) (b:=7350) (join_sums term (lo:=1099700) (a:=3675) (b:=3675) (join_sums term (lo:=1099700) (a:=1837) (b:=1838) (join_sums term (lo:=1099700) (a:=918) (b:=919) (join_sums term (lo:=1099700) (a:=459) (b:=459) r1099700 r1100159) (join_sums term (lo:=1100618) (a:=459) (b:=460) r1100618 r1101077)) (join_sums term (lo:=1101537) (a:=919) (b:=919) (join_sums term (lo:=1101537) (a:=459) (b:=460) r1101537 r1101996) (join_sums term (lo:=1102456) (a:=459) (b:=460) r1102456 r1102915))) (join_sums term (lo:=1103375) (a:=1837) (b:=1838) (join_sums term (lo:=1103375) (a:=918) (b:=919) (join_sums term (lo:=1103375) (a:=459) (b:=459) r1103375 r1103834) (join_sums term (lo:=1104293) (a:=459) (b:=460) r1104293 r1104752)) (join_sums term (lo:=1105212) (a:=919) (b:=919) (join_sums term (lo:=1105212) (a:=459) (b:=460) r1105212 r1105671) (join_sums term (lo:=1106131) (a:=459) (b:=460) r1106131 r1106590)))) (join_sums term (lo:=1107050) (a:=3675) (b:=3675) (join_sums term (lo:=1107050) (a:=1837) (b:=1838) (join_sums term (lo:=1107050) (a:=918) (b:=919) (join_sums term (lo:=1107050) (a:=459) (b:=459) r1107050 r1107509) (join_sums term (lo:=1107968) (a:=459) (b:=460) r1107968 r1108427)) (join_sums term (lo:=1108887) (a:=919) (b:=919) (join_sums term (lo:=1108887) (a:=459) (b:=460) r1108887 r1109346) (join_sums term (lo:=1109806) (a:=459) (b:=460) r1109806 r1110265))) (join_sums term (lo:=1110725) (a:=1837) (b:=1838) (join_sums term (lo:=1110725) (a:=918) (b:=919) (join_sums term (lo:=1110725) (a:=459) (b:=459) r1110725 r1111184) (join_sums term (lo:=1111643) (a:=459) (b:=460) r1111643 r1112102)) (join_sums term (lo:=1112562) (a:=919) (b:=919) (join_sums term (lo:=1112562) (a:=459) (b:=460) r1112562 r1113021) (join_sums term (lo:=1113481) (a:=459) (b:=460) r1113481 r1113940)))))) (join_sums term (lo:=1114400) (a:=14700) (b:=14700) (join_sums term (lo:=1114400) (a:=7350) (b:=7350) (join_sums term (lo:=1114400) (a:=3675) (b:=3675) (join_sums term (lo:=1114400) (a:=1837) (b:=1838) (join_sums term (lo:=1114400) (a:=918) (b:=919) (join_sums term (lo:=1114400) (a:=459) (b:=459) r1114400 r1114859) (join_sums term (lo:=1115318) (a:=459) (b:=460) r1115318 r1115777)) (join_sums term (lo:=1116237) (a:=919) (b:=919) (join_sums term (lo:=1116237) (a:=459) (b:=460) r1116237 r1116696) (join_sums term (lo:=1117156) (a:=459) (b:=460) r1117156 r1117615))) (join_sums term (lo:=1118075) (a:=1837) (b:=1838) (join_sums term (lo:=1118075) (a:=918) (b:=919) (join_sums term (lo:=1118075) (a:=459) (b:=459) r1118075 r1118534) (join_sums term (lo:=1118993) (a:=459) (b:=460) r1118993 r1119452)) (join_sums term (lo:=1119912) (a:=919) (b:=919) (join_sums term (lo:=1119912) (a:=459) (b:=460) r1119912 r1120371) (join_sums term (lo:=1120831) (a:=459) (b:=460) r1120831 r1121290)))) (join_sums term (lo:=1121750) (a:=3675) (b:=3675) (join_sums term (lo:=1121750) (a:=1837) (b:=1838) (join_sums term (lo:=1121750) (a:=918) (b:=919) (join_sums term (lo:=1121750) (a:=459) (b:=459) r1121750 r1122209) (join_sums term (lo:=1122668) (a:=459) (b:=460) r1122668 r1123127)) (join_sums term (lo:=1123587) (a:=919) (b:=919) (join_sums term (lo:=1123587) (a:=459) (b:=460) r1123587 r1124046) (join_sums term (lo:=1124506) (a:=459) (b:=460) r1124506 r1124965))) (join_sums term (lo:=1125425) (a:=1837) (b:=1838) (join_sums term (lo:=1125425) (a:=918) (b:=919) (join_sums term (lo:=1125425) (a:=459) (b:=459) r1125425 r1125884) (join_sums term (lo:=1126343) (a:=459) (b:=460) r1126343 r1126802)) (join_sums term (lo:=1127262) (a:=919) (b:=919) (join_sums term (lo:=1127262) (a:=459) (b:=460) r1127262 r1127721) (join_sums term (lo:=1128181) (a:=459) (b:=460) r1128181 r1128640))))) (join_sums term (lo:=1129100) (a:=7350) (b:=7350) (join_sums term (lo:=1129100) (a:=3675) (b:=3675) (join_sums term (lo:=1129100) (a:=1837) (b:=1838) (join_sums term (lo:=1129100) (a:=918) (b:=919) (join_sums term (lo:=1129100) (a:=459) (b:=459) r1129100 r1129559) (join_sums term (lo:=1130018) (a:=459) (b:=460) r1130018 r1130477)) (join_sums term (lo:=1130937) (a:=919) (b:=919) (join_sums term (lo:=1130937) (a:=459) (b:=460) r1130937 r1131396) (join_sums term (lo:=1131856) (a:=459) (b:=460) r1131856 r1132315))) (join_sums term (lo:=1132775) (a:=1837) (b:=1838) (join_sums term (lo:=1132775) (a:=918) (b:=919) (join_sums term (lo:=1132775) (a:=459) (b:=459) r1132775 r1133234) (join_sums term (lo:=1133693) (a:=459) (b:=460) r1133693 r1134152)) (join_sums term (lo:=1134612) (a:=919) (b:=919) (join_sums term (lo:=1134612) (a:=459) (b:=460) r1134612 r1135071) (join_sums term (lo:=1135531) (a:=459) (b:=460) r1135531 r1135990)))) (join_sums term (lo:=1136450) (a:=3675) (b:=3675) (join_sums term (lo:=1136450) (a:=1837) (b:=1838) (join_sums term (lo:=1136450) (a:=918) (b:=919) (join_sums term (lo:=1136450) (a:=459) (b:=459) r1136450 r1136909) (join_sums term (lo:=1137368) (a:=459) (b:=460) r1137368 r1137827)) (join_sums term (lo:=1138287) (a:=919) (b:=919) (join_sums term (lo:=1138287) (a:=459) (b:=460) r1138287 r1138746) (join_sums term (lo:=1139206) (a:=459) (b:=460) r1139206 r1139665))) (join_sums term (lo:=1140125) (a:=1837) (b:=1838) (join_sums term (lo:=1140125) (a:=918) (b:=919) (join_sums term (lo:=1140125) (a:=459) (b:=459) r1140125 r1140584) (join_sums term (lo:=1141043) (a:=459) (b:=460) r1141043 r1141502)) (join_sums term (lo:=1141962) (a:=919) (b:=919) (join_sums term (lo:=1141962) (a:=459) (b:=460) r1141962 r1142421) (join_sums term (lo:=1142881) (a:=459) (b:=460) r1142881 r1143340))))))) (join_sums term (lo:=1143800) (a:=29399) (b:=29400) (join_sums term (lo:=1143800) (a:=14699) (b:=14700) (join_sums term (lo:=1143800) (a:=7349) (b:=7350) (join_sums term (lo:=1143800) (a:=3674) (b:=3675) (join_sums term (lo:=1143800) (a:=1837) (b:=1837) (join_sums term (lo:=1143800) (a:=918) (b:=919) (join_sums term (lo:=1143800) (a:=459) (b:=459) r1143800 r1144259) (join_sums term (lo:=1144718) (a:=459) (b:=460) r1144718 r1145177)) (join_sums term (lo:=1145637) (a:=918) (b:=919) (join_sums term (lo:=1145637) (a:=459) (b:=459) r1145637 r1146096) (join_sums term (lo:=1146555) (a:=459) (b:=460) r1146555 r1147014))) (join_sums term (lo:=1147474) (a:=1837) (b:=1838) (join_sums term (lo:=1147474) (a:=918) (b:=919) (join_sums term (lo:=1147474) (a:=459) (b:=459) r1147474 r1147933) (join_sums term (lo:=1148392) (a:=459) (b:=460) r1148392 r1148851)) (join_sums term (lo:=1149311) (a:=919) (b:=919) (join_sums term (lo:=1149311) (a:=459) (b:=460) r1149311 r1149770) (join_sums term (lo:=1150230) (a:=459) (b:=460) r1150230 r1150689)))) (join_sums term (lo:=1151149) (a:=3675) (b:=3675) (join_sums term (lo:=1151149) (a:=1837) (b:=1838) (join_sums term (lo:=1151149) (a:=918) (b:=919) (join_sums term (lo:=1151149) (a:=459) (b:=459) r1151149 r1151608) (join_sums term (lo:=1152067) (a:=459) (b:=460) r1152067 r1152526)) (join_sums term (lo:=1152986) (a:=919) (b:=919) (join_sums term (lo:=1152986) (a:=459) (b:=460) r1152986 r1153445) (join_sums term (lo:=1153905) (a:=459) (b:=460) r1153905 r1154364))) (join_sums term (lo:=1154824) (a:=1837) (b:=1838) (join_sums term (lo:=1154824) (a:=918) (b:=919) (join_sums term (lo:=1154824) (a:=459) (b:=459) r1154824 r1155283) (join_sums term (lo:=1155742) (a:=459) (b:=460) r1155742 r1156201)) (join_sums term (lo:=1156661) (a:=919) (b:=919) (join_sums term (lo:=1156661) (a:=459) (b:=460) r1156661 r1157120) (join_sums term (lo:=1157580) (a:=459) (b:=460) r1157580 r1158039))))) (join_sums term (lo:=1158499) (a:=7350) (b:=7350) (join_sums term (lo:=1158499) (a:=3675) (b:=3675) (join_sums term (lo:=1158499) (a:=1837) (b:=1838) (join_sums term (lo:=1158499) (a:=918) (b:=919) (join_sums term (lo:=1158499) (a:=459) (b:=459) r1158499 r1158958) (join_sums term (lo:=1159417) (a:=459) (b:=460) r1159417 r1159876)) (join_sums term (lo:=1160336) (a:=919) (b:=919) (join_sums term (lo:=1160336) (a:=459) (b:=460) r1160336 r1160795) (join_sums term (lo:=1161255) (a:=459) (b:=460) r1161255 r1161714))) (join_sums term (lo:=1162174) (a:=1837) (b:=1838) (join_sums term (lo:=1162174) (a:=918) (b:=919) (join_sums term (lo:=1162174) (a:=459) (b:=459) r1162174 r1162633) (join_sums term (lo:=1163092) (a:=459) (b:=460) r1163092 r1163551)) (join_sums term (lo:=1164011) (a:=919) (b:=919) (join_sums term (lo:=1164011) (a:=459) (b:=460) r1164011 r1164470) (join_sums term (lo:=1164930) (a:=459) (b:=460) r1164930 r1165389)))) (join_sums term (lo:=1165849) (a:=3675) (b:=3675) (join_sums term (lo:=1165849) (a:=1837) (b:=1838) (join_sums term (lo:=1165849) (a:=918) (b:=919) (join_sums term (lo:=1165849) (a:=459) (b:=459) r1165849 r1166308) (join_sums term (lo:=1166767) (a:=459) (b:=460) r1166767 r1167226)) (join_sums term (lo:=1167686) (a:=919) (b:=919) (join_sums term (lo:=1167686) (a:=459) (b:=460) r1167686 r1168145) (join_sums term (lo:=1168605) (a:=459) (b:=460) r1168605 r1169064))) (join_sums term (lo:=1169524) (a:=1837) (b:=1838) (join_sums term (lo:=1169524) (a:=918) (b:=919) (join_sums term (lo:=1169524) (a:=459) (b:=459) r1169524 r1169983) (join_sums term (lo:=1170442) (a:=459) (b:=460) r1170442 r1170901)) (join_sums term (lo:=1171361) (a:=919) (b:=919) (join_sums term (lo:=1171361) (a:=459) (b:=460) r1171361 r1171820) (join_sums term (lo:=1172280) (a:=459) (b:=460) r1172280 r1172739)))))) (join_sums term (lo:=1173199) (a:=14700) (b:=14700) (join_sums term (lo:=1173199) (a:=7350) (b:=7350) (join_sums term (lo:=1173199) (a:=3675) (b:=3675) (join_sums term (lo:=1173199) (a:=1837) (b:=1838) (join_sums term (lo:=1173199) (a:=918) (b:=919) (join_sums term (lo:=1173199) (a:=459) (b:=459) r1173199 r1173658) (join_sums term (lo:=1174117) (a:=459) (b:=460) r1174117 r1174576)) (join_sums term (lo:=1175036) (a:=919) (b:=919) (join_sums term (lo:=1175036) (a:=459) (b:=460) r1175036 r1175495) (join_sums term (lo:=1175955) (a:=459) (b:=460) r1175955 r1176414))) (join_sums term (lo:=1176874) (a:=1837) (b:=1838) (join_sums term (lo:=1176874) (a:=918) (b:=919) (join_sums term (lo:=1176874) (a:=459) (b:=459) r1176874 r1177333) (join_sums term (lo:=1177792) (a:=459) (b:=460) r1177792 r1178251)) (join_sums term (lo:=1178711) (a:=919) (b:=919) (join_sums term (lo:=1178711) (a:=459) (b:=460) r1178711 r1179170) (join_sums term (lo:=1179630) (a:=459) (b:=460) r1179630 r1180089)))) (join_sums term (lo:=1180549) (a:=3675) (b:=3675) (join_sums term (lo:=1180549) (a:=1837) (b:=1838) (join_sums term (lo:=1180549) (a:=918) (b:=919) (join_sums term (lo:=1180549) (a:=459) (b:=459) r1180549 r1181008) (join_sums term (lo:=1181467) (a:=459) (b:=460) r1181467 r1181926)) (join_sums term (lo:=1182386) (a:=919) (b:=919) (join_sums term (lo:=1182386) (a:=459) (b:=460) r1182386 r1182845) (join_sums term (lo:=1183305) (a:=459) (b:=460) r1183305 r1183764))) (join_sums term (lo:=1184224) (a:=1837) (b:=1838) (join_sums term (lo:=1184224) (a:=918) (b:=919) (join_sums term (lo:=1184224) (a:=459) (b:=459) r1184224 r1184683) (join_sums term (lo:=1185142) (a:=459) (b:=460) r1185142 r1185601)) (join_sums term (lo:=1186061) (a:=919) (b:=919) (join_sums term (lo:=1186061) (a:=459) (b:=460) r1186061 r1186520) (join_sums term (lo:=1186980) (a:=459) (b:=460) r1186980 r1187439))))) (join_sums term (lo:=1187899) (a:=7350) (b:=7350) (join_sums term (lo:=1187899) (a:=3675) (b:=3675) (join_sums term (lo:=1187899) (a:=1837) (b:=1838) (join_sums term (lo:=1187899) (a:=918) (b:=919) (join_sums term (lo:=1187899) (a:=459) (b:=459) r1187899 r1188358) (join_sums term (lo:=1188817) (a:=459) (b:=460) r1188817 r1189276)) (join_sums term (lo:=1189736) (a:=919) (b:=919) (join_sums term (lo:=1189736) (a:=459) (b:=460) r1189736 r1190195) (join_sums term (lo:=1190655) (a:=459) (b:=460) r1190655 r1191114))) (join_sums term (lo:=1191574) (a:=1837) (b:=1838) (join_sums term (lo:=1191574) (a:=918) (b:=919) (join_sums term (lo:=1191574) (a:=459) (b:=459) r1191574 r1192033) (join_sums term (lo:=1192492) (a:=459) (b:=460) r1192492 r1192951)) (join_sums term (lo:=1193411) (a:=919) (b:=919) (join_sums term (lo:=1193411) (a:=459) (b:=460) r1193411 r1193870) (join_sums term (lo:=1194330) (a:=459) (b:=460) r1194330 r1194789)))) (join_sums term (lo:=1195249) (a:=3675) (b:=3675) (join_sums term (lo:=1195249) (a:=1837) (b:=1838) (join_sums term (lo:=1195249) (a:=918) (b:=919) (join_sums term (lo:=1195249) (a:=459) (b:=459) r1195249 r1195708) (join_sums term (lo:=1196167) (a:=459) (b:=460) r1196167 r1196626)) (join_sums term (lo:=1197086) (a:=919) (b:=919) (join_sums term (lo:=1197086) (a:=459) (b:=460) r1197086 r1197545) (join_sums term (lo:=1198005) (a:=459) (b:=460) r1198005 r1198464))) (join_sums term (lo:=1198924) (a:=1837) (b:=1838) (join_sums term (lo:=1198924) (a:=918) (b:=919) (join_sums term (lo:=1198924) (a:=459) (b:=459) r1198924 r1199383) (join_sums term (lo:=1199842) (a:=459) (b:=460) r1199842 r1200301)) (join_sums term (lo:=1200761) (a:=919) (b:=919) (join_sums term (lo:=1200761) (a:=459) (b:=460) r1200761 r1201220) (join_sums term (lo:=1201680) (a:=459) (b:=460) r1201680 r1202139))))))))

private theorem rows : blockSum term 0 1202599 4728403590 :=
  join_sums term (lo:=0) (a:=1085001) (b:=117598) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 1202598).filter (1085000 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=4728403590 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From1085000To1202598
