import certificates.«sieve-change-11092009835083-0-53»
import certificates.«prime-table-495000000-500000000»

/-!
# Final sieve primes for the seventh endpoint

Near the cube root, a removed multiple is counted by a smaller sieve whose
survivors are one, a prime, or a product of two primes. The interval of possible
smaller factors of those products is short enough to enumerate.
-/
open Finset
namespace FinalSeventhSieve

def sifted (x y : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun n => ∀ r ∈ Nat.primesLE y, ¬ r ∣ n)

def rough (x y : ℕ) : ℕ := (sifted x y).card

private theorem member (x y n : ℕ) : n ∈ sifted x y ↔
    (1 ≤ n ∧ n ≤ x) ∧ (∀ r ∈ Nat.primesLE y, ¬ r ∣ n) := by simp [sifted]

private theorem one_step {x y z p : ℕ} (yp : y<p) (pz : p≤z) (hp : p.Prime)
    (gap : ∀ r ∈ Icc (y+1) z, r.Prime → r=p) :
    rough x z + rough (x/p) y = rough x y := by
  classical
  have split : sifted x z = (sifted x y).filter (fun n => ¬p ∣ n) := by
    ext n
    rw [member,mem_filter,member]
    constructor
    · rintro ⟨range,avoid⟩
      refine ⟨⟨range,fun r hr => avoid r ?_⟩,avoid p (Nat.mem_primesLE.mpr ⟨pz,hp⟩)⟩
      obtain ⟨low,pr⟩ := Nat.mem_primesLE.mp hr
      exact Nat.mem_primesLE.mpr ⟨by omega,pr⟩
    · rintro ⟨⟨range,avoid⟩,skip⟩
      refine ⟨range,fun r hr => ?_⟩
      obtain ⟨high,pr⟩ := Nat.mem_primesLE.mp hr
      by_cases low : r≤y
      · exact avoid r (Nat.mem_primesLE.mpr ⟨low,pr⟩)
      · have eq := gap r (mem_Icc.mpr ⟨by omega,high⟩) pr
        simpa only [eq] using skip
  have mult : (sifted x y).filter (fun n => p ∣ n) = (sifted (x/p) y).image (p * ·) := by
    ext n
    simp only [mem_filter,member,mem_image]
    constructor
    · rintro ⟨⟨⟨pos,ub⟩,avoid⟩,⟨m,rfl⟩⟩
      refine ⟨m,⟨⟨?_,(Nat.le_div_iff_mul_le hp.pos).mpr (by simpa [mul_comm] using ub)⟩,?_⟩,rfl⟩
      · by_contra! h
        have eq : m=0 := by omega
        simp [eq] at pos
      · intro r hr hd
        exact avoid r hr (dvd_mul_of_dvd_right hd p)
    · rintro ⟨m,⟨⟨pos,ub⟩,avoid⟩,rfl⟩
      refine ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero (by omega)),?_⟩,?_⟩,dvd_mul_right _ _⟩
      · simpa only [mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp ub
      · intro r hr hdiv
        obtain ⟨ub,pr⟩ := Nat.mem_primesLE.mp hr
        rcases pr.dvd_mul.mp hdiv with left | right
        · have eq := (Nat.prime_dvd_prime_iff_eq pr hp).mp left
          omega
        · exact avoid r hr right
  have partition := card_filter_add_card_filter_not (s:=sifted x y) (fun n => p ∣ n)
  rw [mult,card_image_of_injective _ (mul_right_injective₀ hp.ne_zero),←split] at partition
  simpa only [rough,Nat.add_comm] using partition

private theorem window (y z : ℕ) : (Nat.primesLE z).filter (y < ·) = (Icc (y+1) z).filter Nat.Prime := by
  ext p
  simp only [mem_filter,Nat.mem_primesLE,mem_Icc]
  constructor
  · rintro ⟨⟨top,pr⟩,above⟩
    exact ⟨⟨by omega,top⟩,pr⟩
  · rintro ⟨⟨above,top⟩,pr⟩
    exact ⟨⟨top,pr⟩,by omega⟩

private lemma prime_by_flag {p : ℕ} (cap : p≤25123)
    (flag : Sieve11092009835083From0To53.FastDenseControl.prime p=true) : p.Prime :=
  (Sieve11092009835083From0To53.FastDenseControl.prime_ok p cap).mp flag

private lemma gap_by_flags {y z p : ℕ} (cap : z≤25123)
    (flags : ∀ r ∈ Icc (y+1) z, Sieve11092009835083From0To53.FastDenseControl.prime r=true → r=p) :
    ∀ r ∈ Icc (y+1) z, r.Prime → r=p := by
  intro r hr pr
  exact flags r hr ((Sieve11092009835083From0To53.FastDenseControl.prime_ok r ((mem_Icc.mp hr).2.trans cap)).mpr pr)

private abbrev small := Sieve11092009835083From0To53.FastDenseControl.fast

def shortPairs (q y z : ℕ) : ℕ :=
  ∑ r ∈ (Icc (y+1) z).filter (fun r => Sieve11092009835083From0To53.FastDenseControl.prime r=true), (small (q/r)-small (r-1))

private theorem pair_values (q y z : ℕ) (high : z≤25123) (quot : q/(y+1)≤25123) :
    (∑ r ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (q/r)-Nat.primeCounting (r-1))) = shortPairs q y z := by
  rw [window]
  unfold shortPairs
  have flags : (Icc (y+1) z).filter Nat.Prime =
      (Icc (y+1) z).filter (fun r => Sieve11092009835083From0To53.FastDenseControl.prime r=true) := by
    ext r
    simp only [mem_filter]
    constructor
    · rintro ⟨hr,pr⟩
      exact ⟨hr,(Sieve11092009835083From0To53.FastDenseControl.prime_ok r ((mem_Icc.mp hr).2.trans high)).mpr pr⟩
    · rintro ⟨hr,fl⟩
      exact ⟨hr,prime_by_flag ((mem_Icc.mp hr).2.trans high) fl⟩
  rw [flags]
  apply sum_congr rfl
  intro r hr
  obtain ⟨low,top⟩ := mem_Icc.mp (mem_filter.mp hr).1
  have ub : q/r ≤ q/(y+1) := Nat.div_le_div_left low (by omega)
  unfold small
  rw [Sieve11092009835083From0To53.FastDenseControl.fast_correct _ (ub.trans quot),
    Sieve11092009835083From0To53.FastDenseControl.fast_correct _ (by omega : r-1≤25123)]

private theorem side {q y z rank tiny pairs result : ℕ} (pos : 1≤q) (yq : y≤q)
    (cub : q<(y+1)^3) (sq : q<(z+1)^2) (bottom : z*z≤q)
    (high : z≤25123) (quot : q/(y+1)≤25123)
    (qrank : Nat.primeCounting q=rank) (yrank : Nat.primeCounting y=tiny)
    (twos : shortPairs q y z=pairs) (sum : result+tiny=1+rank+pairs) :
    rough q y=result := by
  have h := SieveA29From0To16.meissel pos yq cub sq
  have row (r : ℕ) (hr : r ∈ (Nat.primesLE z).filter (y < ·)) := by
    have rb := Nat.le_of_mem_primesLE (mem_filter.mp hr).1
    have rp := (Nat.prime_of_mem_primesLE (mem_filter.mp hr).1).pos
    exact SieveA29From0To16.prime_row rp
      ((Nat.le_div_iff_mul_le rp).mpr ((Nat.mul_le_mul rb rb).trans bottom))
  rw [sum_congr rfl row,pair_values q y z high quot,twos,Nat.primesLE_card_eq_primeCounting q,
    Nat.primesLE_card_eq_primeCounting y,qrank,yrank] at h
  change rough q y+tiny = 1+rank+pairs at h
  omega

theorem subtract_row {x y z p q amount : ℕ} (yp : y<p) (pz : p≤z) (hp : p.Prime)
    (gap : ∀ r ∈ Icc (y+1) z, r.Prime → r=p)
    (division : x/p=q) (count : rough q y=amount) : rough x z+amount=rough x y := by
  have h:=one_step (x:=x) yp pz hp gap
  rwa [division,count] at h

private lemma join {a b c v w s : ℕ} (l : b+v=a) (r : c+w=b) (total : v+w=s) :
    c+s=a := by omega



set_option maxRecDepth 16000 in
private theorem count22189 : rough 499887774 22171=26347972 := by
  apply side (z:=22358) (rank:=26350216) (tiny:=2487) (pairs:=242)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (QuotientQ495000000To500000000.count_correct 499887774 (by decide) (by decide)).symm.trans
      (by decide +kernel)
  · exact (Sieve11092009835083From0To53.FastDenseControl.fast_correct 22171 (by decide)).symm.trans
      (by decide +kernel)
  · decide +kernel
  · rfl

set_option maxRecDepth 16000 in
private theorem drop22189 : rough 11092009835083 22189+26347972=rough 11092009835083 22171 :=
  subtract_row (p:=22189) (q:=499887774) (by decide) (by decide)
    (prime_by_flag (by decide) (by decide +kernel)) (gap_by_flags (by decide) (by decide +kernel))
    rfl count22189


set_option maxRecDepth 16000 in
private theorem count22193 : rough 499797676 22189=26343516 := by
  apply side (z:=22356) (rank:=26345796) (tiny:=2488) (pairs:=207)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (QuotientQ495000000To500000000.count_correct 499797676 (by decide) (by decide)).symm.trans
      (by decide +kernel)
  · exact (Sieve11092009835083From0To53.FastDenseControl.fast_correct 22189 (by decide)).symm.trans
      (by decide +kernel)
  · decide +kernel
  · rfl

set_option maxRecDepth 16000 in
private theorem drop22193 : rough 11092009835083 22193+26343516=rough 11092009835083 22189 :=
  subtract_row (p:=22193) (q:=499797676) (by decide) (by decide)
    (prime_by_flag (by decide) (by decide +kernel)) (gap_by_flags (by decide) (by decide +kernel))
    rfl count22193


private theorem through22193 : rough 11092009835083 22193+52691488=rough 11092009835083 22171 :=
  join drop22189 drop22193 rfl

set_option maxRecDepth 16000 in
private theorem count22229 : rough 498988251 22193=26303046 := by
  apply side (z:=22338) (rank:=26305394) (tiny:=2489) (pairs:=140)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (QuotientQ495000000To500000000.count_correct 498988251 (by decide) (by decide)).symm.trans
      (by decide +kernel)
  · exact (Sieve11092009835083From0To53.FastDenseControl.fast_correct 22193 (by decide)).symm.trans
      (by decide +kernel)
  · decide +kernel
  · rfl

set_option maxRecDepth 16000 in
private theorem drop22229 : rough 11092009835083 22229+26303046=rough 11092009835083 22193 :=
  subtract_row (p:=22229) (q:=498988251) (by decide) (by decide)
    (prime_by_flag (by decide) (by decide +kernel)) (gap_by_flags (by decide) (by decide +kernel))
    rfl count22229


private theorem through22229 : rough 11092009835083 22229+78994534=rough 11092009835083 22171 :=
  join through22193 drop22229 rfl

set_option maxRecDepth 16000 in
private theorem count22247 : rough 498584520 22229=26282936 := by
  apply side (z:=22329) (rank:=26285325) (tiny:=2490) (pairs:=100)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (QuotientQ495000000To500000000.count_correct 498584520 (by decide) (by decide)).symm.trans
      (by decide +kernel)
  · exact (Sieve11092009835083From0To53.FastDenseControl.fast_correct 22229 (by decide)).symm.trans
      (by decide +kernel)
  · decide +kernel
  · rfl

set_option maxRecDepth 16000 in
private theorem drop22247 : rough 11092009835083 22247+26282936=rough 11092009835083 22229 :=
  subtract_row (p:=22247) (q:=498584520) (by decide) (by decide)
    (prime_by_flag (by decide) (by decide +kernel)) (gap_by_flags (by decide) (by decide +kernel))
    rfl count22247


private theorem through22247 : rough 11092009835083 22247+105277470=rough 11092009835083 22171 :=
  join through22229 drop22247 rfl

set_option maxRecDepth 16000 in
private theorem count22259 : rough 498315730 22247=26269507 := by
  apply side (z:=22322) (rank:=26271928) (tiny:=2491) (pairs:=69)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (QuotientQ495000000To500000000.count_correct 498315730 (by decide) (by decide)).symm.trans
      (by decide +kernel)
  · exact (Sieve11092009835083From0To53.FastDenseControl.fast_correct 22247 (by decide)).symm.trans
      (by decide +kernel)
  · decide +kernel
  · rfl

set_option maxRecDepth 16000 in
private theorem drop22259 : rough 11092009835083 22259+26269507=rough 11092009835083 22247 :=
  subtract_row (p:=22259) (q:=498315730) (by decide) (by decide)
    (prime_by_flag (by decide) (by decide +kernel)) (gap_by_flags (by decide) (by decide +kernel))
    rfl count22259


private theorem through22259 : rough 11092009835083 22259+131546977=rough 11092009835083 22171 :=
  join through22247 drop22259 rfl

set_option maxRecDepth 16000 in
private theorem count22271 : rough 498047228 22259=26255973 := by
  apply side (z:=22316) (rank:=26258418) (tiny:=2492) (pairs:=46)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (QuotientQ495000000To500000000.count_correct 498047228 (by decide) (by decide)).symm.trans
      (by decide +kernel)
  · exact (Sieve11092009835083From0To53.FastDenseControl.fast_correct 22259 (by decide)).symm.trans
      (by decide +kernel)
  · decide +kernel
  · rfl

set_option maxRecDepth 16000 in
private theorem drop22271 : rough 11092009835083 22271+26255973=rough 11092009835083 22259 :=
  subtract_row (p:=22271) (q:=498047228) (by decide) (by decide)
    (prime_by_flag (by decide) (by decide +kernel)) (gap_by_flags (by decide) (by decide +kernel))
    rfl count22271


private theorem through22271 : rough 11092009835083 22271+157802950=rough 11092009835083 22171 :=
  join through22259 drop22271 rfl

set_option maxRecDepth 16000 in
private theorem count22273 : rough 498002506 22271=26253745 := by
  apply side (z:=22315) (rank:=26256202) (tiny:=2493) (pairs:=35)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (QuotientQ495000000To500000000.count_correct 498002506 (by decide) (by decide)).symm.trans
      (by decide +kernel)
  · exact (Sieve11092009835083From0To53.FastDenseControl.fast_correct 22271 (by decide)).symm.trans
      (by decide +kernel)
  · decide +kernel
  · rfl

set_option maxRecDepth 16000 in
private theorem drop22273 : rough 11092009835083 22273+26253745=rough 11092009835083 22271 :=
  subtract_row (p:=22273) (q:=498002506) (by decide) (by decide)
    (prime_by_flag (by decide) (by decide +kernel)) (gap_by_flags (by decide) (by decide +kernel))
    rfl count22273


private theorem through22273 : rough 11092009835083 22273+184056695=rough 11092009835083 22171 :=
  join through22271 drop22273 rfl

set_option maxRecDepth 16000 in
private theorem count22277 : rough 497913086 22273=26249297 := by
  apply side (z:=22313) (rank:=26251765) (tiny:=2494) (pairs:=25)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (QuotientQ495000000To500000000.count_correct 497913086 (by decide) (by decide)).symm.trans
      (by decide +kernel)
  · exact (Sieve11092009835083From0To53.FastDenseControl.fast_correct 22273 (by decide)).symm.trans
      (by decide +kernel)
  · decide +kernel
  · rfl

set_option maxRecDepth 16000 in
private theorem drop22277 : rough 11092009835083 22277+26249297=rough 11092009835083 22273 :=
  subtract_row (p:=22277) (q:=497913086) (by decide) (by decide)
    (prime_by_flag (by decide) (by decide +kernel)) (gap_by_flags (by decide) (by decide +kernel))
    rfl count22277


private theorem through22277 : rough 11092009835083 22277+210305992=rough 11092009835083 22171 :=
  join through22273 drop22277 rfl

set_option maxRecDepth 16000 in
private theorem count22279 : rough 497868388 22277=26247055 := by
  apply side (z:=22312) (rank:=26249533) (tiny:=2495) (pairs:=16)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (QuotientQ495000000To500000000.count_correct 497868388 (by decide) (by decide)).symm.trans
      (by decide +kernel)
  · exact (Sieve11092009835083From0To53.FastDenseControl.fast_correct 22277 (by decide)).symm.trans
      (by decide +kernel)
  · decide +kernel
  · rfl

set_option maxRecDepth 16000 in
private theorem drop22279 : rough 11092009835083 22279+26247055=rough 11092009835083 22277 :=
  subtract_row (p:=22279) (q:=497868388) (by decide) (by decide)
    (prime_by_flag (by decide) (by decide +kernel)) (gap_by_flags (by decide) (by decide +kernel))
    rfl count22279


private theorem through22279 : rough 11092009835083 22279+236553047=rough 11092009835083 22171 :=
  join through22277 drop22279 rfl

set_option maxRecDepth 16000 in
private theorem count22283 : rough 497779016 22279=26242631 := by
  apply side (z:=22310) (rank:=26245116) (tiny:=2496) (pairs:=10)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (QuotientQ495000000To500000000.count_correct 497779016 (by decide) (by decide)).symm.trans
      (by decide +kernel)
  · exact (Sieve11092009835083From0To53.FastDenseControl.fast_correct 22279 (by decide)).symm.trans
      (by decide +kernel)
  · decide +kernel
  · rfl

set_option maxRecDepth 16000 in
private theorem drop22283 : rough 11092009835083 22283+26242631=rough 11092009835083 22279 :=
  subtract_row (p:=22283) (q:=497779016) (by decide) (by decide)
    (prime_by_flag (by decide) (by decide +kernel)) (gap_by_flags (by decide) (by decide +kernel))
    rfl count22283


private theorem through22283 : rough 11092009835083 22283+262795678=rough 11092009835083 22171 :=
  join through22279 drop22283 rfl

set_option maxRecDepth 16000 in
private theorem count22291 : rough 497600369 22283=26233735 := by
  apply side (z:=22306) (rank:=26236226) (tiny:=2497) (pairs:=5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (QuotientQ495000000To500000000.count_correct 497600369 (by decide) (by decide)).symm.trans
      (by decide +kernel)
  · exact (Sieve11092009835083From0To53.FastDenseControl.fast_correct 22283 (by decide)).symm.trans
      (by decide +kernel)
  · decide +kernel
  · rfl

set_option maxRecDepth 16000 in
private theorem drop22291 : rough 11092009835083 22301+26233735=rough 11092009835083 22283 :=
  subtract_row (p:=22291) (q:=497600369) (by decide) (by decide)
    (prime_by_flag (by decide) (by decide +kernel)) (gap_by_flags (by decide) (by decide +kernel))
    rfl count22291


private theorem through22291 : rough 11092009835083 22301+289029413=rough 11092009835083 22171 :=
  join through22283 drop22291 rfl

/-- All eleven prime removals from 22,171 through the final sieve cutoff. -/
theorem last_eleven : rough 11092009835083 22301+289029413=rough 11092009835083 22171 := through22291

end FinalSeventhSieve
