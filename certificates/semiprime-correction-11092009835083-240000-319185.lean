import certificates.«semiprime-correction-555157672301-small»
import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 240,000 through 319,185

The sum covers 6,319 primes. Their quotient counts are checked by the
certified prime-counting table through 67,545,646.
-/
open Finset
namespace Correction11092009835083From240000To319185

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


private abbrev term := contribution 11092009835083 240000 RangePrimeA26.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 240001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 240000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r240001 : blockSum term 240001 618 135384989 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r240619 : blockSum term 240619 619 135048566 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r241238 : blockSum term 241238 618 153964126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r241856 : blockSum term 241856 619 142620479 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r242475 : blockSum term 242475 618 125862936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r243093 : blockSum term 243093 619 147368962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r243712 : blockSum term 243712 619 122502787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r244331 : blockSum term 244331 619 160253256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r244950 : blockSum term 244950 618 124616589 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r245568 : blockSum term 245568 619 129744587 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r246187 : blockSum term 246187 618 145602043 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r246805 : blockSum term 246805 619 129118636 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r247424 : blockSum term 247424 618 139539550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r248042 : blockSum term 248042 619 149920492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r248661 : blockSum term 248661 619 133540238 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r249280 : blockSum term 249280 619 135884655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r249899 : blockSum term 249899 618 111654090 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r250517 : blockSum term 250517 619 127273563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r251136 : blockSum term 251136 618 148173066 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r251754 : blockSum term 251754 619 131974484 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r252373 : blockSum term 252373 618 129022781 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r252991 : blockSum term 252991 619 115571752 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r253610 : blockSum term 253610 619 144163035 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r254229 : blockSum term 254229 619 109820100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r254848 : blockSum term 254848 618 143508169 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r255466 : blockSum term 255466 619 143161097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r256085 : blockSum term 256085 618 122051610 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r256703 : blockSum term 256703 619 113983993 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r257322 : blockSum term 257322 618 118909470 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r257940 : blockSum term 257940 619 136688984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r258559 : blockSum term 258559 619 133816466 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r259178 : blockSum term 259178 619 123224808 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r259797 : blockSum term 259797 618 112711100 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r260415 : blockSum term 260415 619 132895649 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r261034 : blockSum term 261034 618 119834593 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r261652 : blockSum term 261652 619 114480493 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r262271 : blockSum term 262271 618 124387731 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r262889 : blockSum term 262889 619 124098540 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r263508 : blockSum term 263508 619 133932316 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r264127 : blockSum term 264127 619 110947341 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r264746 : blockSum term 264746 618 135864040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r265364 : blockSum term 265364 619 120493394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r265983 : blockSum term 265983 618 125247656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r266601 : blockSum term 266601 619 129957769 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r267220 : blockSum term 267220 618 167061633 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r267838 : blockSum term 267838 619 94564980 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r268457 : blockSum term 268457 619 141500876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r269076 : blockSum term 269076 619 123861695 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r269695 : blockSum term 269695 618 121104928 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r270313 : blockSum term 270313 619 125784119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r270932 : blockSum term 270932 618 118130067 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r271550 : blockSum term 271550 619 110512147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r272169 : blockSum term 272169 618 137232576 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r272787 : blockSum term 272787 619 117358700 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r273406 : blockSum term 273406 619 102454385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r274025 : blockSum term 274025 619 109561595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r274644 : blockSum term 274644 618 128753693 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r275262 : blockSum term 275262 619 118782328 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r275881 : blockSum term 275881 618 135460548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r276499 : blockSum term 276499 619 120678332 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r277118 : blockSum term 277118 618 108377342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r277736 : blockSum term 277736 619 115359375 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r278355 : blockSum term 278355 619 124704049 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r278974 : blockSum term 278974 619 105293188 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r279593 : blockSum term 279593 618 112241696 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r280211 : blockSum term 280211 619 121531891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r280830 : blockSum term 280830 618 128413434 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r281448 : blockSum term 281448 619 130504910 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r282067 : blockSum term 282067 618 111292079 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r282685 : blockSum term 282685 619 118146386 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r283304 : blockSum term 283304 619 99022573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r283923 : blockSum term 283923 619 124705505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r284542 : blockSum term 284542 618 129156355 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r285160 : blockSum term 285160 619 119491788 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r285779 : blockSum term 285779 618 81844843 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r286397 : blockSum term 286397 619 116691608 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r287016 : blockSum term 287016 618 109456334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r287634 : blockSum term 287634 619 95276445 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r288253 : blockSum term 288253 619 111317708 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r288872 : blockSum term 288872 619 136549013 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r289491 : blockSum term 289491 618 110849731 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r290109 : blockSum term 290109 619 122148277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r290728 : blockSum term 290728 618 108103699 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r291346 : blockSum term 291346 619 105596794 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r291965 : blockSum term 291965 618 114534707 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r292583 : blockSum term 292583 619 107447155 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r293202 : blockSum term 293202 619 95823428 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r293821 : blockSum term 293821 619 120666147 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r294440 : blockSum term 294440 618 109060307 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r295058 : blockSum term 295058 619 90719471 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r295677 : blockSum term 295677 618 122212742 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r296295 : blockSum term 296295 619 112927570 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r296914 : blockSum term 296914 618 101437596 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r297532 : blockSum term 297532 619 101240962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r298151 : blockSum term 298151 619 112267893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r298770 : blockSum term 298770 619 98589622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r299389 : blockSum term 299389 618 107345123 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r300007 : blockSum term 300007 619 109357652 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r300626 : blockSum term 300626 618 124743492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r301244 : blockSum term 301244 619 106708024 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r301863 : blockSum term 301863 618 93195166 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r302481 : blockSum term 302481 619 123997157 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r303100 : blockSum term 303100 619 119332050 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r303719 : blockSum term 303719 619 101465094 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r304338 : blockSum term 304338 618 127682844 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r304956 : blockSum term 304956 619 112051897 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r305575 : blockSum term 305575 618 103065548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r306193 : blockSum term 306193 619 107243836 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r306812 : blockSum term 306812 618 120143495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r307430 : blockSum term 307430 619 87208730 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r308049 : blockSum term 308049 619 106616936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r308668 : blockSum term 308668 619 106407260 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r309287 : blockSum term 309287 618 106216891 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r309905 : blockSum term 309905 619 99511291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r310524 : blockSum term 310524 618 101490583 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r311142 : blockSum term 311142 619 101289461 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r311761 : blockSum term 311761 618 105389650 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r312379 : blockSum term 312379 619 107347193 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r312998 : blockSum term 312998 619 107139637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r313617 : blockSum term 313617 619 115494241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r314236 : blockSum term 314236 618 104604994 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r314854 : blockSum term 314854 619 93745518 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r315473 : blockSum term 315473 619 106338613 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r316092 : blockSum term 316092 619 110377614 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r316711 : blockSum term 316711 618 105939021 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r317329 : blockSum term 317329 619 107856918 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r317948 : blockSum term 317948 619 109764870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r318567 : blockSum term 318567 619 113768055 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 240001 79185 15207465060 := (join_sums term (lo:=240001) (a:=39592) (b:=39593) (join_sums term (lo:=240001) (a:=19796) (b:=19796) (join_sums term (lo:=240001) (a:=9898) (b:=9898) (join_sums term (lo:=240001) (a:=4949) (b:=4949) (join_sums term (lo:=240001) (a:=2474) (b:=2475) (join_sums term (lo:=240001) (a:=1237) (b:=1237) (join_sums term (lo:=240001) (a:=618) (b:=619) r240001 r240619) (join_sums term (lo:=241238) (a:=618) (b:=619) r241238 r241856)) (join_sums term (lo:=242475) (a:=1237) (b:=1238) (join_sums term (lo:=242475) (a:=618) (b:=619) r242475 r243093) (join_sums term (lo:=243712) (a:=619) (b:=619) r243712 r244331))) (join_sums term (lo:=244950) (a:=2474) (b:=2475) (join_sums term (lo:=244950) (a:=1237) (b:=1237) (join_sums term (lo:=244950) (a:=618) (b:=619) r244950 r245568) (join_sums term (lo:=246187) (a:=618) (b:=619) r246187 r246805)) (join_sums term (lo:=247424) (a:=1237) (b:=1238) (join_sums term (lo:=247424) (a:=618) (b:=619) r247424 r248042) (join_sums term (lo:=248661) (a:=619) (b:=619) r248661 r249280)))) (join_sums term (lo:=249899) (a:=4949) (b:=4949) (join_sums term (lo:=249899) (a:=2474) (b:=2475) (join_sums term (lo:=249899) (a:=1237) (b:=1237) (join_sums term (lo:=249899) (a:=618) (b:=619) r249899 r250517) (join_sums term (lo:=251136) (a:=618) (b:=619) r251136 r251754)) (join_sums term (lo:=252373) (a:=1237) (b:=1238) (join_sums term (lo:=252373) (a:=618) (b:=619) r252373 r252991) (join_sums term (lo:=253610) (a:=619) (b:=619) r253610 r254229))) (join_sums term (lo:=254848) (a:=2474) (b:=2475) (join_sums term (lo:=254848) (a:=1237) (b:=1237) (join_sums term (lo:=254848) (a:=618) (b:=619) r254848 r255466) (join_sums term (lo:=256085) (a:=618) (b:=619) r256085 r256703)) (join_sums term (lo:=257322) (a:=1237) (b:=1238) (join_sums term (lo:=257322) (a:=618) (b:=619) r257322 r257940) (join_sums term (lo:=258559) (a:=619) (b:=619) r258559 r259178))))) (join_sums term (lo:=259797) (a:=9898) (b:=9898) (join_sums term (lo:=259797) (a:=4949) (b:=4949) (join_sums term (lo:=259797) (a:=2474) (b:=2475) (join_sums term (lo:=259797) (a:=1237) (b:=1237) (join_sums term (lo:=259797) (a:=618) (b:=619) r259797 r260415) (join_sums term (lo:=261034) (a:=618) (b:=619) r261034 r261652)) (join_sums term (lo:=262271) (a:=1237) (b:=1238) (join_sums term (lo:=262271) (a:=618) (b:=619) r262271 r262889) (join_sums term (lo:=263508) (a:=619) (b:=619) r263508 r264127))) (join_sums term (lo:=264746) (a:=2474) (b:=2475) (join_sums term (lo:=264746) (a:=1237) (b:=1237) (join_sums term (lo:=264746) (a:=618) (b:=619) r264746 r265364) (join_sums term (lo:=265983) (a:=618) (b:=619) r265983 r266601)) (join_sums term (lo:=267220) (a:=1237) (b:=1238) (join_sums term (lo:=267220) (a:=618) (b:=619) r267220 r267838) (join_sums term (lo:=268457) (a:=619) (b:=619) r268457 r269076)))) (join_sums term (lo:=269695) (a:=4949) (b:=4949) (join_sums term (lo:=269695) (a:=2474) (b:=2475) (join_sums term (lo:=269695) (a:=1237) (b:=1237) (join_sums term (lo:=269695) (a:=618) (b:=619) r269695 r270313) (join_sums term (lo:=270932) (a:=618) (b:=619) r270932 r271550)) (join_sums term (lo:=272169) (a:=1237) (b:=1238) (join_sums term (lo:=272169) (a:=618) (b:=619) r272169 r272787) (join_sums term (lo:=273406) (a:=619) (b:=619) r273406 r274025))) (join_sums term (lo:=274644) (a:=2474) (b:=2475) (join_sums term (lo:=274644) (a:=1237) (b:=1237) (join_sums term (lo:=274644) (a:=618) (b:=619) r274644 r275262) (join_sums term (lo:=275881) (a:=618) (b:=619) r275881 r276499)) (join_sums term (lo:=277118) (a:=1237) (b:=1238) (join_sums term (lo:=277118) (a:=618) (b:=619) r277118 r277736) (join_sums term (lo:=278355) (a:=619) (b:=619) r278355 r278974)))))) (join_sums term (lo:=279593) (a:=19796) (b:=19797) (join_sums term (lo:=279593) (a:=9898) (b:=9898) (join_sums term (lo:=279593) (a:=4949) (b:=4949) (join_sums term (lo:=279593) (a:=2474) (b:=2475) (join_sums term (lo:=279593) (a:=1237) (b:=1237) (join_sums term (lo:=279593) (a:=618) (b:=619) r279593 r280211) (join_sums term (lo:=280830) (a:=618) (b:=619) r280830 r281448)) (join_sums term (lo:=282067) (a:=1237) (b:=1238) (join_sums term (lo:=282067) (a:=618) (b:=619) r282067 r282685) (join_sums term (lo:=283304) (a:=619) (b:=619) r283304 r283923))) (join_sums term (lo:=284542) (a:=2474) (b:=2475) (join_sums term (lo:=284542) (a:=1237) (b:=1237) (join_sums term (lo:=284542) (a:=618) (b:=619) r284542 r285160) (join_sums term (lo:=285779) (a:=618) (b:=619) r285779 r286397)) (join_sums term (lo:=287016) (a:=1237) (b:=1238) (join_sums term (lo:=287016) (a:=618) (b:=619) r287016 r287634) (join_sums term (lo:=288253) (a:=619) (b:=619) r288253 r288872)))) (join_sums term (lo:=289491) (a:=4949) (b:=4949) (join_sums term (lo:=289491) (a:=2474) (b:=2475) (join_sums term (lo:=289491) (a:=1237) (b:=1237) (join_sums term (lo:=289491) (a:=618) (b:=619) r289491 r290109) (join_sums term (lo:=290728) (a:=618) (b:=619) r290728 r291346)) (join_sums term (lo:=291965) (a:=1237) (b:=1238) (join_sums term (lo:=291965) (a:=618) (b:=619) r291965 r292583) (join_sums term (lo:=293202) (a:=619) (b:=619) r293202 r293821))) (join_sums term (lo:=294440) (a:=2474) (b:=2475) (join_sums term (lo:=294440) (a:=1237) (b:=1237) (join_sums term (lo:=294440) (a:=618) (b:=619) r294440 r295058) (join_sums term (lo:=295677) (a:=618) (b:=619) r295677 r296295)) (join_sums term (lo:=296914) (a:=1237) (b:=1238) (join_sums term (lo:=296914) (a:=618) (b:=619) r296914 r297532) (join_sums term (lo:=298151) (a:=619) (b:=619) r298151 r298770))))) (join_sums term (lo:=299389) (a:=9898) (b:=9899) (join_sums term (lo:=299389) (a:=4949) (b:=4949) (join_sums term (lo:=299389) (a:=2474) (b:=2475) (join_sums term (lo:=299389) (a:=1237) (b:=1237) (join_sums term (lo:=299389) (a:=618) (b:=619) r299389 r300007) (join_sums term (lo:=300626) (a:=618) (b:=619) r300626 r301244)) (join_sums term (lo:=301863) (a:=1237) (b:=1238) (join_sums term (lo:=301863) (a:=618) (b:=619) r301863 r302481) (join_sums term (lo:=303100) (a:=619) (b:=619) r303100 r303719))) (join_sums term (lo:=304338) (a:=2474) (b:=2475) (join_sums term (lo:=304338) (a:=1237) (b:=1237) (join_sums term (lo:=304338) (a:=618) (b:=619) r304338 r304956) (join_sums term (lo:=305575) (a:=618) (b:=619) r305575 r306193)) (join_sums term (lo:=306812) (a:=1237) (b:=1238) (join_sums term (lo:=306812) (a:=618) (b:=619) r306812 r307430) (join_sums term (lo:=308049) (a:=619) (b:=619) r308049 r308668)))) (join_sums term (lo:=309287) (a:=4949) (b:=4950) (join_sums term (lo:=309287) (a:=2474) (b:=2475) (join_sums term (lo:=309287) (a:=1237) (b:=1237) (join_sums term (lo:=309287) (a:=618) (b:=619) r309287 r309905) (join_sums term (lo:=310524) (a:=618) (b:=619) r310524 r311142)) (join_sums term (lo:=311761) (a:=1237) (b:=1238) (join_sums term (lo:=311761) (a:=618) (b:=619) r311761 r312379) (join_sums term (lo:=312998) (a:=619) (b:=619) r312998 r313617))) (join_sums term (lo:=314236) (a:=2475) (b:=2475) (join_sums term (lo:=314236) (a:=1237) (b:=1238) (join_sums term (lo:=314236) (a:=618) (b:=619) r314236 r314854) (join_sums term (lo:=315473) (a:=619) (b:=619) r315473 r316092)) (join_sums term (lo:=316711) (a:=1237) (b:=1238) (join_sums term (lo:=316711) (a:=618) (b:=619) r316711 r317329) (join_sums term (lo:=317948) (a:=619) (b:=619) r317948 r318567)))))))

private theorem rows : blockSum term 0 319186 15207465060 :=
  join_sums term (lo:=0) (a:=240001) (b:=79185) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 319185).filter (240000 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=15207465060 :=
  right_from_blocks (l:=34751024) (b:=67545646) (small:=745089)
    RangePrimeA26.fast FastDenseA26.fast FastDenseA26.prime (RangePrimeA26.fast_correct RankWheel34751.first_anchor)
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From240000To319185
