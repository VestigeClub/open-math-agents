import certificates.«prime-table-94085731-120000000»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 92,433 through 117,892

The sum covers 2,195 primes. Their quotient counts are checked by the
certified prime-counting table through 120,000,000.
-/
open Finset
namespace Correction11092009835083From92433To117892

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


private abbrev term := contribution 11092009835083 92433 RangePrimeQ94085731To120000000.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 92434 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 92433 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r92434 : blockSum term 92434 397 259070096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r92831 : blockSum term 92831 398 230933926 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r93229 : blockSum term 93229 398 257082974 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r93627 : blockSum term 93627 398 215520697 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r94025 : blockSum term 94025 397 221425892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r94422 : blockSum term 94422 398 247309848 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r94820 : blockSum term 94820 398 239643686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r95218 : blockSum term 95218 398 251994873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r95616 : blockSum term 95616 397 244370525 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r96013 : blockSum term 96013 398 203948207 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r96411 : blockSum term 96411 398 235912020 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r96809 : blockSum term 96809 398 215421418 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r97207 : blockSum term 97207 397 214550197 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r97604 : blockSum term 97604 398 207271794 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r98002 : blockSum term 98002 398 193573363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r98400 : blockSum term 98400 398 218603516 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r98798 : blockSum term 98798 397 268977828 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r99195 : blockSum term 99195 398 204124913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r99593 : blockSum term 99593 398 222459520 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r99991 : blockSum term 99991 398 196275529 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r100389 : blockSum term 100389 397 208219381 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r100786 : blockSum term 100786 398 226229343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r101184 : blockSum term 101184 398 237915039 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r101582 : blockSum term 101582 398 218329216 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r101980 : blockSum term 101980 397 248646103 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r102377 : blockSum term 102377 398 204361149 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r102775 : blockSum term 102775 398 185093179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r103173 : blockSum term 103173 398 178247846 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r103571 : blockSum term 103571 398 189893358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r103969 : blockSum term 103969 398 231964776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r104367 : blockSum term 104367 398 231041908 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r104765 : blockSum term 104765 398 181814911 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r105163 : blockSum term 105163 397 235449672 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r105560 : blockSum term 105560 398 174466242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r105958 : blockSum term 105958 398 215791093 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r106356 : blockSum term 106356 398 232949630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r106754 : blockSum term 106754 397 208333104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r107151 : blockSum term 107151 398 148321214 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r107549 : blockSum term 107549 398 200957286 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r107947 : blockSum term 107947 398 212061135 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r108345 : blockSum term 108345 397 181986450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r108742 : blockSum term 108742 398 233989132 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r109140 : blockSum term 109140 398 209856682 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r109538 : blockSum term 109538 398 209128171 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r109936 : blockSum term 109936 398 162093726 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r110334 : blockSum term 110334 398 196147123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r110732 : blockSum term 110732 398 206997139 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r111130 : blockSum term 111130 398 177641342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r111528 : blockSum term 111528 397 205598849 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r111925 : blockSum term 111925 398 204900229 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r112323 : blockSum term 112323 398 164553632 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r112721 : blockSum term 112721 398 209176353 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r113119 : blockSum term 113119 397 202939721 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r113516 : blockSum term 113516 398 162877873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r113914 : blockSum term 113914 398 201552844 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r114312 : blockSum term 114312 398 172952209 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r114710 : blockSum term 114710 397 178002235 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r115107 : blockSum term 115107 398 182973196 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r115505 : blockSum term 115505 398 243083241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r115903 : blockSum term 115903 398 170731887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r116301 : blockSum term 116301 398 164706227 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r116699 : blockSum term 116699 398 186062358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r117097 : blockSum term 117097 398 174585083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r117495 : blockSum term 117495 398 222925146 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 92434 25459 13344017255 := (join_sums term (lo:=92434) (a:=12729) (b:=12730) (join_sums term (lo:=92434) (a:=6364) (b:=6365) (join_sums term (lo:=92434) (a:=3182) (b:=3182) (join_sums term (lo:=92434) (a:=1591) (b:=1591) (join_sums term (lo:=92434) (a:=795) (b:=796) (join_sums term (lo:=92434) (a:=397) (b:=398) r92434 r92831) (join_sums term (lo:=93229) (a:=398) (b:=398) r93229 r93627)) (join_sums term (lo:=94025) (a:=795) (b:=796) (join_sums term (lo:=94025) (a:=397) (b:=398) r94025 r94422) (join_sums term (lo:=94820) (a:=398) (b:=398) r94820 r95218))) (join_sums term (lo:=95616) (a:=1591) (b:=1591) (join_sums term (lo:=95616) (a:=795) (b:=796) (join_sums term (lo:=95616) (a:=397) (b:=398) r95616 r96013) (join_sums term (lo:=96411) (a:=398) (b:=398) r96411 r96809)) (join_sums term (lo:=97207) (a:=795) (b:=796) (join_sums term (lo:=97207) (a:=397) (b:=398) r97207 r97604) (join_sums term (lo:=98002) (a:=398) (b:=398) r98002 r98400)))) (join_sums term (lo:=98798) (a:=3182) (b:=3183) (join_sums term (lo:=98798) (a:=1591) (b:=1591) (join_sums term (lo:=98798) (a:=795) (b:=796) (join_sums term (lo:=98798) (a:=397) (b:=398) r98798 r99195) (join_sums term (lo:=99593) (a:=398) (b:=398) r99593 r99991)) (join_sums term (lo:=100389) (a:=795) (b:=796) (join_sums term (lo:=100389) (a:=397) (b:=398) r100389 r100786) (join_sums term (lo:=101184) (a:=398) (b:=398) r101184 r101582))) (join_sums term (lo:=101980) (a:=1591) (b:=1592) (join_sums term (lo:=101980) (a:=795) (b:=796) (join_sums term (lo:=101980) (a:=397) (b:=398) r101980 r102377) (join_sums term (lo:=102775) (a:=398) (b:=398) r102775 r103173)) (join_sums term (lo:=103571) (a:=796) (b:=796) (join_sums term (lo:=103571) (a:=398) (b:=398) r103571 r103969) (join_sums term (lo:=104367) (a:=398) (b:=398) r104367 r104765))))) (join_sums term (lo:=105163) (a:=6365) (b:=6365) (join_sums term (lo:=105163) (a:=3182) (b:=3183) (join_sums term (lo:=105163) (a:=1591) (b:=1591) (join_sums term (lo:=105163) (a:=795) (b:=796) (join_sums term (lo:=105163) (a:=397) (b:=398) r105163 r105560) (join_sums term (lo:=105958) (a:=398) (b:=398) r105958 r106356)) (join_sums term (lo:=106754) (a:=795) (b:=796) (join_sums term (lo:=106754) (a:=397) (b:=398) r106754 r107151) (join_sums term (lo:=107549) (a:=398) (b:=398) r107549 r107947))) (join_sums term (lo:=108345) (a:=1591) (b:=1592) (join_sums term (lo:=108345) (a:=795) (b:=796) (join_sums term (lo:=108345) (a:=397) (b:=398) r108345 r108742) (join_sums term (lo:=109140) (a:=398) (b:=398) r109140 r109538)) (join_sums term (lo:=109936) (a:=796) (b:=796) (join_sums term (lo:=109936) (a:=398) (b:=398) r109936 r110334) (join_sums term (lo:=110732) (a:=398) (b:=398) r110732 r111130)))) (join_sums term (lo:=111528) (a:=3182) (b:=3183) (join_sums term (lo:=111528) (a:=1591) (b:=1591) (join_sums term (lo:=111528) (a:=795) (b:=796) (join_sums term (lo:=111528) (a:=397) (b:=398) r111528 r111925) (join_sums term (lo:=112323) (a:=398) (b:=398) r112323 r112721)) (join_sums term (lo:=113119) (a:=795) (b:=796) (join_sums term (lo:=113119) (a:=397) (b:=398) r113119 r113516) (join_sums term (lo:=113914) (a:=398) (b:=398) r113914 r114312))) (join_sums term (lo:=114710) (a:=1591) (b:=1592) (join_sums term (lo:=114710) (a:=795) (b:=796) (join_sums term (lo:=114710) (a:=397) (b:=398) r114710 r115107) (join_sums term (lo:=115505) (a:=398) (b:=398) r115505 r115903)) (join_sums term (lo:=116301) (a:=796) (b:=796) (join_sums term (lo:=116301) (a:=398) (b:=398) r116301 r116699) (join_sums term (lo:=117097) (a:=398) (b:=398) r117097 r117495))))))

private theorem rows : blockSum term 0 117893 13344017255 :=
  join_sums term (lo:=0) (a:=92434) (b:=25459) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 117892).filter (92433 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=13344017255 :=
  right_from_blocks (l:=94085731) (b:=120000000) (small:=745089)
    RangePrimeQ94085731To120000000.fast FastDenseA26.fast FastDenseA26.prime QuotientQ94085731To120000000.count_correct
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From92433To117892
