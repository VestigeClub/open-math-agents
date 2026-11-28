import certificates.«semiprime-correction-555157672301-small»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 164,215 through 240,000

The sum covers 6,188 primes. Their quotient counts are checked by the
certified prime-counting table through 67,545,646.
-/
open Finset
namespace Correction11092009835083From164215To240000

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


private abbrev term := contribution 11092009835083 164215 RangePrimeA26.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 164216 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 164215 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r164216 : blockSum term 164216 592 190120106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r164808 : blockSum term 164808 592 173634852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r165400 : blockSum term 165400 592 188816246 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r165992 : blockSum term 165992 592 164651911 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r166584 : blockSum term 166584 592 230511665 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r167176 : blockSum term 167176 592 179125939 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r167768 : blockSum term 167768 592 174632068 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r168360 : blockSum term 168360 592 166302861 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r168952 : blockSum term 168952 592 185039240 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r169544 : blockSum term 169544 592 199796699 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r170136 : blockSum term 170136 592 199155118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r170728 : blockSum term 170728 592 190870826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r171320 : blockSum term 171320 592 190209447 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r171912 : blockSum term 171912 592 185819052 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r172504 : blockSum term 172504 592 196577254 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r173096 : blockSum term 173096 593 169530839 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r173689 : blockSum term 173689 592 191537019 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r174281 : blockSum term 174281 592 179690621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r174873 : blockSum term 174873 592 156717797 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r175465 : blockSum term 175465 592 189650934 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r176057 : blockSum term 176057 592 218727045 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r176649 : blockSum term 176649 592 173702268 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r177241 : blockSum term 177241 592 147366086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r177833 : blockSum term 177833 592 183629495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r178425 : blockSum term 178425 592 197699388 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r179017 : blockSum term 179017 592 204357679 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r179609 : blockSum term 179609 592 185557780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r180201 : blockSum term 180201 592 174117984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r180793 : blockSum term 180793 592 137390066 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r181385 : blockSum term 181385 592 176611010 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r181977 : blockSum term 181977 592 190462683 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r182569 : blockSum term 182569 593 179137302 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r183162 : blockSum term 183162 592 182136990 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r183754 : blockSum term 183754 592 174441700 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r184346 : blockSum term 184346 592 159724903 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r184938 : blockSum term 184938 592 176957148 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r185530 : blockSum term 185530 592 215210923 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r186122 : blockSum term 186122 592 165310579 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r186714 : blockSum term 186714 592 175326749 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r187306 : blockSum term 187306 592 164340227 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r187898 : blockSum term 187898 592 160341087 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r188490 : blockSum term 188490 592 173764124 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r189082 : blockSum term 189082 592 180162483 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r189674 : blockSum term 189674 592 152030913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r190266 : blockSum term 190266 592 175667085 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r190858 : blockSum term 190858 592 140827085 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r191450 : blockSum term 191450 592 181527110 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r192042 : blockSum term 192042 593 184375917 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r192635 : blockSum term 192635 592 166823581 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r193227 : blockSum term 193227 592 169722329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r193819 : blockSum term 193819 592 145578659 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r194411 : blockSum term 194411 592 158620486 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r195003 : blockSum term 195003 592 171646852 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r195595 : blockSum term 195595 592 167761865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r196187 : blockSum term 196187 592 150554514 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r196779 : blockSum term 196779 592 166804503 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r197371 : blockSum term 197371 592 163015162 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r197963 : blockSum term 197963 592 165870504 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r198555 : blockSum term 198555 592 155492592 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r199147 : blockSum term 199147 592 151737708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r199739 : blockSum term 199739 592 164489780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r200331 : blockSum term 200331 592 144331382 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r200923 : blockSum term 200923 592 150466581 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r201515 : blockSum term 201515 593 182661773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r202108 : blockSum term 202108 592 139870091 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r202700 : blockSum term 202700 592 142745665 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r203292 : blockSum term 203292 592 158534426 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r203884 : blockSum term 203884 592 154851450 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r204476 : blockSum term 204476 592 144780005 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r205068 : blockSum term 205068 592 176457172 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r205660 : blockSum term 205660 592 153549755 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r206252 : blockSum term 206252 592 146797588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r206844 : blockSum term 206844 592 152744735 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r207436 : blockSum term 207436 592 171399476 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r208028 : blockSum term 208028 592 167748494 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r208620 : blockSum term 208620 592 135734251 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r209212 : blockSum term 209212 592 173161259 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r209804 : blockSum term 209804 592 175824615 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r210396 : blockSum term 210396 592 147168780 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r210988 : blockSum term 210988 593 153023756 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r211581 : blockSum term 211581 592 149509373 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r212173 : blockSum term 212173 592 118049988 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r212765 : blockSum term 212765 592 161098384 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r213357 : blockSum term 213357 592 135960042 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r213949 : blockSum term 213949 592 160263651 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r214541 : blockSum term 214541 592 135269710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r215133 : blockSum term 215133 592 144099145 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r215725 : blockSum term 215725 592 131491519 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r216317 : blockSum term 216317 592 146384734 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r216909 : blockSum term 216909 592 158163451 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r217501 : blockSum term 217501 592 130459447 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r218093 : blockSum term 218093 592 148268985 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r218685 : blockSum term 218685 592 141878473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r219277 : blockSum term 219277 592 168588763 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r219869 : blockSum term 219869 592 144151455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r220461 : blockSum term 220461 593 140781146 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r221054 : blockSum term 221054 592 143417226 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r221646 : blockSum term 221646 592 151991009 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r222238 : blockSum term 222238 592 130795760 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r222830 : blockSum term 222830 592 160111985 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r223422 : blockSum term 223422 592 127182764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r224014 : blockSum term 224014 592 147507445 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r224606 : blockSum term 224606 592 141241406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r225198 : blockSum term 225198 592 152629364 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r225790 : blockSum term 225790 592 131751546 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r226382 : blockSum term 226382 592 134350764 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r226974 : blockSum term 226974 592 142738317 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r227566 : blockSum term 227566 592 124982591 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r228158 : blockSum term 228158 592 153648104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r228750 : blockSum term 228750 592 150384698 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r229342 : blockSum term 229342 592 155780958 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r229934 : blockSum term 229934 593 155401431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r230527 : blockSum term 230527 592 134916172 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r231119 : blockSum term 231119 592 137443103 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r231711 : blockSum term 231711 592 114278117 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r232303 : blockSum term 232303 592 139643357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r232895 : blockSum term 232895 592 119399455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r233487 : blockSum term 233487 592 113448129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r234079 : blockSum term 234079 592 147137553 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r234671 : blockSum term 234671 593 146780723 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r235264 : blockSum term 235264 592 115440464 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r235856 : blockSum term 235856 592 117983919 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r236448 : blockSum term 236448 592 131717746 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r237040 : blockSum term 237040 592 120231752 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r237632 : blockSum term 237632 592 142223926 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r238224 : blockSum term 238224 592 133561426 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r238816 : blockSum term 238816 592 127694364 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r239408 : blockSum term 239408 593 135701150 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 164216 75785 20399199082 := (join_sums term (lo:=164216) (a:=37892) (b:=37893) (join_sums term (lo:=164216) (a:=18946) (b:=18946) (join_sums term (lo:=164216) (a:=9473) (b:=9473) (join_sums term (lo:=164216) (a:=4736) (b:=4737) (join_sums term (lo:=164216) (a:=2368) (b:=2368) (join_sums term (lo:=164216) (a:=1184) (b:=1184) (join_sums term (lo:=164216) (a:=592) (b:=592) r164216 r164808) (join_sums term (lo:=165400) (a:=592) (b:=592) r165400 r165992)) (join_sums term (lo:=166584) (a:=1184) (b:=1184) (join_sums term (lo:=166584) (a:=592) (b:=592) r166584 r167176) (join_sums term (lo:=167768) (a:=592) (b:=592) r167768 r168360))) (join_sums term (lo:=168952) (a:=2368) (b:=2369) (join_sums term (lo:=168952) (a:=1184) (b:=1184) (join_sums term (lo:=168952) (a:=592) (b:=592) r168952 r169544) (join_sums term (lo:=170136) (a:=592) (b:=592) r170136 r170728)) (join_sums term (lo:=171320) (a:=1184) (b:=1185) (join_sums term (lo:=171320) (a:=592) (b:=592) r171320 r171912) (join_sums term (lo:=172504) (a:=592) (b:=593) r172504 r173096)))) (join_sums term (lo:=173689) (a:=4736) (b:=4737) (join_sums term (lo:=173689) (a:=2368) (b:=2368) (join_sums term (lo:=173689) (a:=1184) (b:=1184) (join_sums term (lo:=173689) (a:=592) (b:=592) r173689 r174281) (join_sums term (lo:=174873) (a:=592) (b:=592) r174873 r175465)) (join_sums term (lo:=176057) (a:=1184) (b:=1184) (join_sums term (lo:=176057) (a:=592) (b:=592) r176057 r176649) (join_sums term (lo:=177241) (a:=592) (b:=592) r177241 r177833))) (join_sums term (lo:=178425) (a:=2368) (b:=2369) (join_sums term (lo:=178425) (a:=1184) (b:=1184) (join_sums term (lo:=178425) (a:=592) (b:=592) r178425 r179017) (join_sums term (lo:=179609) (a:=592) (b:=592) r179609 r180201)) (join_sums term (lo:=180793) (a:=1184) (b:=1185) (join_sums term (lo:=180793) (a:=592) (b:=592) r180793 r181385) (join_sums term (lo:=181977) (a:=592) (b:=593) r181977 r182569))))) (join_sums term (lo:=183162) (a:=9473) (b:=9473) (join_sums term (lo:=183162) (a:=4736) (b:=4737) (join_sums term (lo:=183162) (a:=2368) (b:=2368) (join_sums term (lo:=183162) (a:=1184) (b:=1184) (join_sums term (lo:=183162) (a:=592) (b:=592) r183162 r183754) (join_sums term (lo:=184346) (a:=592) (b:=592) r184346 r184938)) (join_sums term (lo:=185530) (a:=1184) (b:=1184) (join_sums term (lo:=185530) (a:=592) (b:=592) r185530 r186122) (join_sums term (lo:=186714) (a:=592) (b:=592) r186714 r187306))) (join_sums term (lo:=187898) (a:=2368) (b:=2369) (join_sums term (lo:=187898) (a:=1184) (b:=1184) (join_sums term (lo:=187898) (a:=592) (b:=592) r187898 r188490) (join_sums term (lo:=189082) (a:=592) (b:=592) r189082 r189674)) (join_sums term (lo:=190266) (a:=1184) (b:=1185) (join_sums term (lo:=190266) (a:=592) (b:=592) r190266 r190858) (join_sums term (lo:=191450) (a:=592) (b:=593) r191450 r192042)))) (join_sums term (lo:=192635) (a:=4736) (b:=4737) (join_sums term (lo:=192635) (a:=2368) (b:=2368) (join_sums term (lo:=192635) (a:=1184) (b:=1184) (join_sums term (lo:=192635) (a:=592) (b:=592) r192635 r193227) (join_sums term (lo:=193819) (a:=592) (b:=592) r193819 r194411)) (join_sums term (lo:=195003) (a:=1184) (b:=1184) (join_sums term (lo:=195003) (a:=592) (b:=592) r195003 r195595) (join_sums term (lo:=196187) (a:=592) (b:=592) r196187 r196779))) (join_sums term (lo:=197371) (a:=2368) (b:=2369) (join_sums term (lo:=197371) (a:=1184) (b:=1184) (join_sums term (lo:=197371) (a:=592) (b:=592) r197371 r197963) (join_sums term (lo:=198555) (a:=592) (b:=592) r198555 r199147)) (join_sums term (lo:=199739) (a:=1184) (b:=1185) (join_sums term (lo:=199739) (a:=592) (b:=592) r199739 r200331) (join_sums term (lo:=200923) (a:=592) (b:=593) r200923 r201515)))))) (join_sums term (lo:=202108) (a:=18946) (b:=18947) (join_sums term (lo:=202108) (a:=9473) (b:=9473) (join_sums term (lo:=202108) (a:=4736) (b:=4737) (join_sums term (lo:=202108) (a:=2368) (b:=2368) (join_sums term (lo:=202108) (a:=1184) (b:=1184) (join_sums term (lo:=202108) (a:=592) (b:=592) r202108 r202700) (join_sums term (lo:=203292) (a:=592) (b:=592) r203292 r203884)) (join_sums term (lo:=204476) (a:=1184) (b:=1184) (join_sums term (lo:=204476) (a:=592) (b:=592) r204476 r205068) (join_sums term (lo:=205660) (a:=592) (b:=592) r205660 r206252))) (join_sums term (lo:=206844) (a:=2368) (b:=2369) (join_sums term (lo:=206844) (a:=1184) (b:=1184) (join_sums term (lo:=206844) (a:=592) (b:=592) r206844 r207436) (join_sums term (lo:=208028) (a:=592) (b:=592) r208028 r208620)) (join_sums term (lo:=209212) (a:=1184) (b:=1185) (join_sums term (lo:=209212) (a:=592) (b:=592) r209212 r209804) (join_sums term (lo:=210396) (a:=592) (b:=593) r210396 r210988)))) (join_sums term (lo:=211581) (a:=4736) (b:=4737) (join_sums term (lo:=211581) (a:=2368) (b:=2368) (join_sums term (lo:=211581) (a:=1184) (b:=1184) (join_sums term (lo:=211581) (a:=592) (b:=592) r211581 r212173) (join_sums term (lo:=212765) (a:=592) (b:=592) r212765 r213357)) (join_sums term (lo:=213949) (a:=1184) (b:=1184) (join_sums term (lo:=213949) (a:=592) (b:=592) r213949 r214541) (join_sums term (lo:=215133) (a:=592) (b:=592) r215133 r215725))) (join_sums term (lo:=216317) (a:=2368) (b:=2369) (join_sums term (lo:=216317) (a:=1184) (b:=1184) (join_sums term (lo:=216317) (a:=592) (b:=592) r216317 r216909) (join_sums term (lo:=217501) (a:=592) (b:=592) r217501 r218093)) (join_sums term (lo:=218685) (a:=1184) (b:=1185) (join_sums term (lo:=218685) (a:=592) (b:=592) r218685 r219277) (join_sums term (lo:=219869) (a:=592) (b:=593) r219869 r220461))))) (join_sums term (lo:=221054) (a:=9473) (b:=9474) (join_sums term (lo:=221054) (a:=4736) (b:=4737) (join_sums term (lo:=221054) (a:=2368) (b:=2368) (join_sums term (lo:=221054) (a:=1184) (b:=1184) (join_sums term (lo:=221054) (a:=592) (b:=592) r221054 r221646) (join_sums term (lo:=222238) (a:=592) (b:=592) r222238 r222830)) (join_sums term (lo:=223422) (a:=1184) (b:=1184) (join_sums term (lo:=223422) (a:=592) (b:=592) r223422 r224014) (join_sums term (lo:=224606) (a:=592) (b:=592) r224606 r225198))) (join_sums term (lo:=225790) (a:=2368) (b:=2369) (join_sums term (lo:=225790) (a:=1184) (b:=1184) (join_sums term (lo:=225790) (a:=592) (b:=592) r225790 r226382) (join_sums term (lo:=226974) (a:=592) (b:=592) r226974 r227566)) (join_sums term (lo:=228158) (a:=1184) (b:=1185) (join_sums term (lo:=228158) (a:=592) (b:=592) r228158 r228750) (join_sums term (lo:=229342) (a:=592) (b:=593) r229342 r229934)))) (join_sums term (lo:=230527) (a:=4737) (b:=4737) (join_sums term (lo:=230527) (a:=2368) (b:=2369) (join_sums term (lo:=230527) (a:=1184) (b:=1184) (join_sums term (lo:=230527) (a:=592) (b:=592) r230527 r231119) (join_sums term (lo:=231711) (a:=592) (b:=592) r231711 r232303)) (join_sums term (lo:=232895) (a:=1184) (b:=1185) (join_sums term (lo:=232895) (a:=592) (b:=592) r232895 r233487) (join_sums term (lo:=234079) (a:=592) (b:=593) r234079 r234671))) (join_sums term (lo:=235264) (a:=2368) (b:=2369) (join_sums term (lo:=235264) (a:=1184) (b:=1184) (join_sums term (lo:=235264) (a:=592) (b:=592) r235264 r235856) (join_sums term (lo:=236448) (a:=592) (b:=592) r236448 r237040)) (join_sums term (lo:=237632) (a:=1184) (b:=1185) (join_sums term (lo:=237632) (a:=592) (b:=592) r237632 r238224) (join_sums term (lo:=238816) (a:=592) (b:=593) r238816 r239408)))))))

private theorem rows : blockSum term 0 240001 20399199082 :=
  join_sums term (lo:=0) (a:=164216) (b:=75785) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 240000).filter (164215 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=20399199082 :=
  right_from_blocks (l:=34751024) (b:=67545646) (small:=745089)
    RangePrimeA26.fast FastDenseA26.fast FastDenseA26.prime (RangePrimeA26.fast_correct RankWheel34751.first_anchor)
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From164215To240000
