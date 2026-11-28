import OMAReductions.R_oeis_a000330_R1

namespace PyramidalLocal
open OMA.S_oeis_a000330

theorem lift_linear (p d v b : ℤ) (f : ℤ → ℤ) (inv : v*d = 1+p*b)
    (shift : ∀ x s : ℤ, ∃ q : ℤ, f (x+s) = f x + s*(d+p*q))
    (k : ℕ) (z : ℤ) : ∃ x : ℤ, p^k ∣ z - f x := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨x, u, hu⟩ := ih
    obtain ⟨q, hq⟩ := shift x (p^k*u*v)
    refine ⟨x+p^k*u*v, -(u*b+u*v*q), ?_⟩
    rw [hq, pow_succ]
    linear_combination hu - p^k*u*inv

private theorem inverse_three (d : ℤ) (h : ¬ (3 : ℤ) ∣ d) :
    ∃ v b : ℤ, v*d = 1+3*b := by
  by_cases hd : d%3 = 1
  · exact ⟨1, d/3, by omega⟩
  · exact ⟨-1, -(d/3)-1, by omega⟩

def at_six (a t : ℤ) := (6*t+1)*(3*t+1)*(2*a*t+1)

theorem value_six (r : ℕ) (t : ℤ) :
    generalizedPolygonalPyramidal r (6*t+1) = at_six (r-2) t := by
  unfold generalizedPolygonalPyramidal at_six
  rw [show (6*t+1)*(6*t+1+1)*(((r:ℤ)-2)*(6*t+1)-((r:ℤ)-5)) =
      ((6*t+1)*(3*t+1)*(2*((r:ℤ)-2)*t+1))*6 by ring]
  simp

theorem two_power (r k : ℕ) (z : ℤ) : ∃ t : ℤ,
    generalizedPolygonalPyramidal r (6*t+1) ≡ z [ZMOD (2:ℤ)^k] := by
  let a : ℤ := r-2
  have shift (x s : ℤ) : ∃ q : ℤ, at_six a (x+s) = at_six a x+s*(1+2*q) := by
    refine ⟨18*a*(3*x^2+3*x*s+s^2)+(9+9*a)*(2*x+s)+a+4, ?_⟩
    unfold at_six
    ring
  obtain ⟨t, ht⟩ := lift_linear 2 1 1 0 (at_six a) (by norm_num) shift k z
  exact ⟨t, Int.modEq_iff_dvd.mpr (by simpa only [value_six, a] using ht)⟩

theorem three_power_nonexceptional (r k : ℕ) (z : ℤ) (h : ¬ (3:ℤ) ∣ (r:ℤ)-2) :
    ∃ t : ℤ, generalizedPolygonalPyramidal r (6*t+1) ≡ z [ZMOD (3:ℤ)^k] := by
  let a : ℤ := r-2
  have ha : ¬ (3:ℤ) ∣ a := h
  obtain ⟨v,b,hv⟩ := inverse_three (9+2*a) (by omega)
  have shift (x s : ℤ) : ∃ q : ℤ, at_six a (x+s) = at_six a x+s*(9+2*a+3*q) := by
    refine ⟨12*a*(3*x^2+3*x*s+s^2)+(6+6*a)*(2*x+s), ?_⟩
    unfold at_six
    ring
  obtain ⟨t,ht⟩ := lift_linear 3 (9+2*a) v b (at_six a) hv shift k z
  exact ⟨t, Int.modEq_iff_dvd.mpr (by simpa only [value_six, a] using ht)⟩

private def at_odd (c t : ℤ) := 4*c*t^3+(6*c+2)*t^2+(2*c+3)*t+1

private theorem value_odd (r : ℕ) (c t : ℤ) (h : (r:ℤ)-2 = 3*c) :
    generalizedPolygonalPyramidal r (2*t+1) = at_odd c t := by
  unfold generalizedPolygonalPyramidal
  rw [show (2*t+1)*(2*t+1+1)*(((r:ℤ)-2)*(2*t+1)-((r:ℤ)-5)) = at_odd c t*6 by
    unfold at_odd
    linear_combination (8*t^3+12*t^2+4*t)*h]
  simp

private theorem odd_disk (c b z : ℤ) (k : ℕ) (reg : ¬ (3:ℤ) ∣ b+2*c)
    (hz : (3:ℤ) ∣ z-at_odd c b) : ∃ t : ℤ, (3:ℤ)^k ∣ z-at_odd c t := by
  let d := 12*c*b^2+2*(6*c+2)*b+(2*c+3)
  let e := 12*c*b+6*c+2
  let q (x : ℤ) := 36*c*x^3+3*e*x^2+d*x
  have hd : d = b+2*c+3*(4*c*b^2+(4*c+1)*b+1) := by dsimp [d]; ring
  obtain ⟨v,j,hv⟩ := inverse_three d (by rw [hd]; omega)
  have shift (x s : ℤ) : ∃ y : ℤ, q (x+s) = q x+s*(d+3*y) := by
    refine ⟨12*c*(3*x^2+3*x*s+s^2)+e*(2*x+s), ?_⟩
    dsimp [q]
    ring
  obtain ⟨u,hu⟩ := hz
  obtain ⟨x,w,hw⟩ := lift_linear 3 d v j q hv shift k u
  have ex : at_odd c (b+3*x) = at_odd c b+3*q x := by
    dsimp [at_odd, q, d, e]
    ring
  refine ⟨b+3*x, 3*w, ?_⟩
  rw [ex]
  linear_combination hu+3*hw

private theorem exceptional_zero (r k : ℕ) (c z : ℤ) (h : (r:ℤ)-2 = 3*c)
    (hz : (3:ℤ) ∣ z) :
    ∃ a : ℤ, generalizedPolygonalPyramidal r a ≡ z [ZMOD (3:ℤ)^k] := by
  have exists_base : ∃ b : ℤ, (¬ (3:ℤ) ∣ b+2*c) ∧ (3:ℤ) ∣ z-at_odd c b := by
    by_cases h1 : (3:ℤ) ∣ 1+2*c
    · refine ⟨2, by omega, ?_⟩
      have h2 : at_odd c 2 = 60*c+15 := by unfold at_odd; ring
      rw [h2]
      omega
    · refine ⟨1, h1, ?_⟩
      have h2 : at_odd c 1 = 12*c+6 := by unfold at_odd; ring
      rw [h2]
      omega
  obtain ⟨b,hb,hz'⟩ := exists_base
  obtain ⟨t,ht⟩ := odd_disk c b z k hb hz'
  exact ⟨2*t+1, Int.modEq_iff_dvd.mpr (by rwa [value_odd r c t h])⟩

theorem three_power (r k : ℕ) (z : ℤ) : ∃ a b c : ℤ, z ≡
    generalizedPolygonalPyramidal r a + generalizedPolygonalPyramidal r b +
    generalizedPolygonalPyramidal r c [ZMOD (3:ℤ)^k] := by
  have h0 : generalizedPolygonalPyramidal r 0 = 0 := by simp [generalizedPolygonalPyramidal]
  have h1 : generalizedPolygonalPyramidal r 1 = 1 := by
    unfold generalizedPolygonalPyramidal
    rw [show (1:ℤ)*(1+1)*(((r:ℤ)-2)*1-((r:ℤ)-5)) = 6 by ring]
    decide
  by_cases hr : (3:ℤ) ∣ (r:ℤ)-2
  · obtain ⟨j,hj⟩ := hr
    obtain ⟨a,ha⟩ := exceptional_zero r k j (z-z%3) hj (by omega)
    have rep : ∃ b c : ℤ, generalizedPolygonalPyramidal r b + generalizedPolygonalPyramidal r c = z%3 := by
      rcases (show z%3 = 0 ∨ z%3 = 1 ∨ z%3 = 2 by omega) with h | h | h
      · exact ⟨0,0,by rw [h0,h]; decide⟩
      · exact ⟨0,1,by rw [h0,h1,h]; decide⟩
      · exact ⟨1,1,by rw [h1,h]; decide⟩
    obtain ⟨b,c,hh⟩ := rep
    refine ⟨a,b,c,?_⟩
    rw [add_assoc,hh]
    simpa using (ha.symm.add_right (z%3))
  · obtain ⟨t,ht⟩ := three_power_nonexceptional r k z hr
    exact ⟨6*t+1,0,0,by simpa only [h0, add_zero] using ht.symm⟩

end PyramidalLocal

namespace PyramidalCRT
open OMA.S_oeis_a000330

private def num (r : ℕ) (x : ℤ) := x*(x+1)*(((r:ℤ)-2)*x-((r:ℤ)-5))

private theorem denom (r : ℕ) (x : ℤ) : generalizedPolygonalPyramidal r x*6 = num r x := by
  let a : ℤ := r-2
  have two : (2:ℤ) ∣ x*(x+1) := by
    rcases (show (2:ℤ) ∣ x ∨ (2:ℤ) ∣ x+1 by omega) with h | h
    · exact dvd_mul_of_dvd_left h _
    · exact dvd_mul_of_dvd_right h _
  have two' : (2:ℤ) ∣ num r x := dvd_mul_of_dvd_left two _
  have three : (3:ℤ) ∣ num r x := by
    rcases (show (3:ℤ) ∣ x ∨ (3:ℤ) ∣ x+1 ∨ (3:ℤ) ∣ x-1 by omega) with h | h | h
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
    · obtain ⟨t,ht⟩ := h
      refine dvd_mul_of_dvd_right (show (3:ℤ) ∣ ((r:ℤ)-2)*x-((r:ℤ)-5) from ?_) _
      exact ⟨((r:ℤ)-2)*t+1, by linear_combination ((r:ℤ)-2)*ht⟩
  exact Int.ediv_mul_cancel (show (6:ℤ) ∣ num r x by omega)

theorem index_modEq (r : ℕ) (m x y : ℤ) (h : x ≡ y [ZMOD m^2]) :
    generalizedPolygonalPyramidal r x ≡ generalizedPolygonalPyramidal r y [ZMOD m] := by
  obtain ⟨t,ht⟩ := h.dvd
  let j := t*(((r:ℤ)-2)*(y^2+y*x+x^2)+3*(y+x)-((r:ℤ)-5))
  have dif : (generalizedPolygonalPyramidal r y-generalizedPolygonalPyramidal r x)*6 = m^2*j := by
    rw [sub_mul,denom,denom]
    dsimp [num,j]
    linear_combination (((r:ℤ)-2)*(y^2+y*x+x^2)+3*(y+x)-((r:ℤ)-5))*ht
  have divides : (6:ℤ) ∣ m^2*j :=
    ⟨generalizedPolygonalPyramidal r y-generalizedPolygonalPyramidal r x, by rw [←dif,mul_comm]⟩
  have sqfree (p : ℤ) (hp : Prime p) (hp6 : p ∣ 6) : p ∣ m*j := by
    have hd : p ∣ m*(m*j) := by simpa [pow_two, mul_assoc] using hp6.trans divides
    rcases hp.dvd_mul.mp hd with hm | hj
    · exact dvd_mul_of_dvd_left hm j
    · exact hj
  have h2 := sqfree 2 (by norm_num) (by norm_num)
  have h3 := sqfree 3 (by norm_num) (by norm_num)
  obtain ⟨u,hu⟩ := (show (6:ℤ) ∣ m*j by omega)
  refine Int.modEq_iff_dvd.mpr ⟨u,?_⟩
  have finalEq : (generalizedPolygonalPyramidal r y-generalizedPolygonalPyramidal r x)*6 =
      (m*u)*6 := by linear_combination dif+m*hu
  omega

private theorem crt_pair (m n : ℤ) (hc : IsCoprime m n) (x y : ℤ) :
    ∃ t : ℤ, t ≡ x [ZMOD m^2] ∧ t ≡ y [ZMOD n^2] := by
  obtain ⟨u,v,h⟩ := (show IsCoprime (m^2) (n^2) from hc.pow)
  refine ⟨y*(u*m^2)+x*(v*n^2),Int.modEq_iff_dvd.mpr ⟨(x-y)*u,?_⟩,
    Int.modEq_iff_dvd.mpr ⟨(y-x)*v,?_⟩⟩
  · linear_combination -x*h
  · linear_combination -y*h

def reps (r : ℕ) (z m : ℤ) : Prop := ∃ a b c : ℤ, z ≡
    generalizedPolygonalPyramidal r a + generalizedPolygonalPyramidal r b +
    generalizedPolygonalPyramidal r c [ZMOD m]

theorem all_of_prime_powers (r : ℕ) (z : ℤ)
    (hp : ∀ p k : ℕ, Nat.Prime p → reps r z ((p:ℤ)^k))
    (m : ℕ) (hm : 0 < m) : reps r z m := by
  induction m using Nat.recOnPrimeCoprime with
  | zero => omega
  | prime_pow p k h => simpa using hp p k h
  | coprime m n hm hn hc ih jh =>
    obtain ⟨a,b,c,habc⟩ := ih (by omega)
    obtain ⟨d,e,f,hdef⟩ := jh (by omega)
    obtain ⟨u,hu,hu'⟩ := crt_pair m n hc.isCoprime a d
    obtain ⟨v,hv,hv'⟩ := crt_pair m n hc.isCoprime b e
    obtain ⟨w,hw,hw'⟩ := crt_pair m n hc.isCoprime c f
    have mm := habc.trans (((index_modEq r _ _ _ hu).add (index_modEq r _ _ _ hv)).add
      (index_modEq r _ _ _ hw)).symm
    have nn := hdef.trans (((index_modEq r _ _ _ hu').add (index_modEq r _ _ _ hv')).add
      (index_modEq r _ _ _ hw')).symm
    refine ⟨u,v,w,Int.modEq_iff_dvd.mpr ?_⟩
    push_cast
    exact hc.isCoprime.mul_dvd mm.dvd nn.dvd

end PyramidalCRT

namespace PyramidalField

def val {K : Type*} [CommRing K] (a b c d x : K) := a*x^3+b*x^2+c*x+d
def slope {K : Type*} [CommRing K] (a b c x : K) := 3*a*x^2+2*b*x+c

private theorem regularize {K : Type*} [Field K] (a b c d z : K) (ha : a ≠ 0)
    (h3 : (3:K) ≠ 0) (h : ∃ x y u : K, val a b c d x+val a b c d y+val a b c d u=z) :
    ∃ x y u : K, val a b c d x+val a b c d y+val a b c d u=z ∧ slope a b c x ≠ 0 := by
  obtain ⟨x,y,u,hxyz⟩ := h
  by_cases hx : slope a b c x = 0
  · by_cases hy : slope a b c y = 0
    · by_cases hu : slope a b c u = 0
      · let s := -(3*a*x+b)/a
        have hs : a*s = -(3*a*x+b) := by dsimp [s]; field_simp
        by_cases hzero : s = 0
        · rw [hzero, mul_zero] at hs
          have centered : 3*a*x+b = 0 := by linear_combination hs
          have der (t : K) : slope a b c t = 3*a*(t-x)^2 := by
            unfold slope at hx ⊢
            linear_combination hx+2*(t-x)*centered
          have unique (t : K) (ht : slope a b c t = 0) : t=x := by
            rw [der, mul_eq_zero] at ht
            rcases ht with bad | good
            · exact (mul_ne_zero h3 ha bad).elim
            · by_contra hne
              exact (pow_ne_zero 2 (sub_ne_zero.mpr hne)) good
          rw [unique y hy, unique u hu] at hxyz
          refine ⟨x+1,x-1,x,?_,?_⟩
          · unfold val at hxyz ⊢
            linear_combination hxyz+2*centered
          · simpa [der] using mul_ne_zero h3 ha
        · have same : val a b c d (x+s) = val a b c d x := by
            unfold val
            unfold slope at hx
            linear_combination s*hx + s^2*hs
          have deriv : slope a b c (x+s) = a*s^2 := by
            unfold slope at hx ⊢
            linear_combination hx+2*s*hs
          exact ⟨x+s,y,u,by rwa [same], deriv.trans_ne (mul_ne_zero ha (pow_ne_zero _ hzero))⟩
      · exact ⟨u,y,x,by linear_combination hxyz,hu⟩
    · exact ⟨y,x,u,by linear_combination hxyz,hy⟩
  · exact ⟨x,y,u,hxyz,hx⟩

private theorem cube_onto {p : ℕ} [Fact p.Prime] (hp : p%3 = 2) (w : ZMod p) :
    ∃ x : ZMod p, x^3 = w := by
  by_cases hw : w = 0
  · exact ⟨0, by simp [hw]⟩
  refine ⟨w^(2*(p/3)+1),?_⟩
  rw [←pow_mul,show (2*(p/3)+1)*3=(p-1)*2+1 by omega,pow_succ,pow_mul,
    ZMod.pow_card_sub_one_eq_one hw,one_pow,one_mul]

private theorem cubic_two_mod_three {p : ℕ} [Fact p.Prime] (hp : p%3=2)
    (a b c d z : ZMod p) (ha : a ≠ 0) (h3 : (3:ZMod p) ≠ 0) (h6 : (6:ZMod p) ≠ 0) :
    ∃ x y u : ZMod p, val a b c d x+val a b c d y+val a b c d u=z := by
  let v := -b/(3*a)
  have hv : 3*a*v+b=0 := by dsimp [v]; field_simp; ring
  obtain ⟨s,hs⟩ := cube_onto hp ((3*val a b c d v-z)/(6*a))
  have hs' : s^3*(6*a)=3*val a b c d v-z := (eq_div_iff (mul_ne_zero h6 ha)).mp hs
  refine ⟨v+s,v+s,v-2*s,?_⟩
  unfold val at hs' ⊢
  linear_combination -hs'+6*s^2*hv

open Finset Polynomial
open scoped Pointwise

private theorem cubic_one_mod_three {p : ℕ} [f : Fact p.Prime] (hp : p%3=1)
    (a b c d z : ZMod p) (ha : a ≠ 0) :
    ∃ x y u : ZMod p, val a b c d x+val a b c d y+val a b c d u=z := by
  classical
  let I : Finset (ZMod p) := univ.image (val a b c d)
  let P : (ZMod p)[X] := C a*X^3+C b*X^2+C c*X+C d
  have hdeg : P.degree=3 := degree_cubic ha
  have hn : P.natDegree=3 := natDegree_cubic ha
  have evals (x : ZMod p) : P.eval x=val a b c d x := by simp [P,val]
  have bound := FiniteField.card_image_polynomial_eval (p:=P) (by rw [hdeg]; decide)
  simp only [ZMod.card,hn,evals] at bound
  change p ≤ 3*I.card at bound
  have i0 : I.Nonempty := univ_nonempty.image _
  have i1 := ZMod.cauchy_davenport f.out i0 i0
  have i2 := ZMod.cauchy_davenport f.out (i0.add i0) i0
  have pos := i0.card_pos
  have full : I+I+I=univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    rw [card_univ,ZMod.card]
    omega
  have hz : z ∈ I+I+I := by rw [full]; exact mem_univ _
  obtain ⟨v,hv,u,hu,hvu⟩ := mem_add.mp hz
  obtain ⟨x,hx,y,hy,hxy⟩ := mem_add.mp hv
  obtain ⟨x',_,hx'⟩ := mem_image.mp hx
  obtain ⟨y',_,hy'⟩ := mem_image.mp hy
  obtain ⟨u',_,hu'⟩ := mem_image.mp hu
  exact ⟨x',y',u',by rw [hx',hy',hu',hxy,hvu]⟩

private theorem quadratic {p : ℕ} [Fact p.Prime] (b c d z : ZMod p) (hb : b ≠ 0)
    (h2 : (2:ZMod p) ≠ 0) : ∃ x y u : ZMod p,
    val 0 b c d x+val 0 b c d y+val 0 b c d u=z ∧ slope 0 b c x ≠ 0 := by
  let h := -c/(2*b)
  have hh : 2*b*h+c=0 := by dsimp [h]; field_simp; ring
  obtain ⟨s,t,ht⟩ := ZMod.sq_add_sq p ((z-val 0 b c d (h+1)-2*val 0 b c d h)/b)
  have he := (eq_div_iff hb).mp ht
  refine ⟨h+1,h+s,h+t,?_,?_⟩
  · unfold val at he ⊢
    linear_combination he+(s+t)*hh
  · have der : slope 0 b c (h+1)=2*b := by unfold slope; linear_combination hh
    exact der.trans_ne (mul_ne_zero h2 hb)

theorem regular_cover {p : ℕ} [f : Fact p.Prime] (large : 5 ≤ p)
    (a b c d z : ZMod p) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ x y u : ZMod p, val a b c d x+val a b c d y+val a b c d u=z ∧ slope a b c x ≠ 0 := by
  have h2 : (2:ZMod p) ≠ 0 := by
    change ((2:ℕ):ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have h3 : (3:ZMod p) ≠ 0 := by
    change ((3:ℕ):ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have h6 : (6:ZMod p) ≠ 0 := by
    rw [show (6:ZMod p)=2*3 by norm_num]
    exact mul_ne_zero h2 h3
  by_cases ha : a = 0
  · subst a
    exact quadratic b c d z (hab.resolve_left (by simp)) h2
  · apply regularize a b c d z ha h3
    have nd : ¬ 3 ∣ p := by
      intro h
      rcases (Nat.dvd_prime f.out).mp h with h | h <;> omega
    rcases (show p%3=1 ∨ p%3=2 by omega) with h | h
    · exact cubic_one_mod_three h a b c d z ha
    · exact cubic_two_mod_three h a b c d z ha h3 h6

end PyramidalField

namespace PyramidalLift
open PyramidalField PyramidalLocal OMA.S_oeis_a000330

private theorem lift_seed {p : ℕ} [Fact p.Prime] (k : ℕ) (a b c d z : ℤ)
    (seed : ∃ x y u : ZMod p, val (a:ZMod p) b c d x + val (a:ZMod p) b c d y +
      val (a:ZMod p) b c d u = z ∧ PyramidalField.slope (a:ZMod p) b c x ≠ 0) :
    ∃ x y u : ℤ, (p:ℤ)^k ∣ z-(val a b c d x+val a b c d y+val a b c d u) := by
  obtain ⟨X,Y,U,equal,reg⟩ := seed
  obtain ⟨x,rfl⟩ := ZMod.intCast_surjective X
  obtain ⟨y,rfl⟩ := ZMod.intCast_surjective Y
  obtain ⟨u,rfl⟩ := ZMod.intCast_surjective U
  let D := PyramidalField.slope a b c x
  have unit : (D:ZMod p) ≠ 0 := by simpa [D,PyramidalField.slope] using reg
  obtain ⟨v,hv⟩ := ZMod.intCast_surjective ((D:ZMod p)⁻¹)
  obtain ⟨j,hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (v*D-1) p).mp (by
    push_cast
    rw [hv,inv_mul_cancel₀ unit,sub_self])
  have inv : v*D = 1+(p:ℤ)*j := by omega
  have cast_eq : ((val a b c d x+val a b c d y+val a b c d u:ℤ):ZMod p)=(z:ZMod p) := by
    simpa [val] using equal
  obtain ⟨w,hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mp cast_eq
  let q (t : ℤ) := (p:ℤ)^2*a*t^3 + (p:ℤ)*(3*a*x+b)*t^2+D*t
  have shift (t h : ℤ) : ∃ e : ℤ, q (t+h) = q t + h*(D+(p:ℤ)*e) := by
    refine ⟨(p:ℤ)*a*(3*t^2+3*t*h+h^2)+(3*a*x+b)*(2*t+h),?_⟩
    dsimp [q]
    ring
  obtain ⟨t,i,hi⟩ := lift_linear p D v j q inv shift k w
  have step : val a b c d (x+(p:ℤ)*t) = val a b c d x + (p:ℤ)*q t := by
    dsimp [q,D,val,PyramidalField.slope]
    ring
  refine ⟨x+(p:ℤ)*t,y,u,(p:ℤ)*i,?_⟩
  rw [step]
  linear_combination hw+(p:ℤ)*hi

theorem large_prime (r p k : ℕ) (prime : p.Prime) (large : 5 ≤ p) (z : ℤ) : ∃ x y u : ℤ,
    z ≡ generalizedPolygonalPyramidal r x+generalizedPolygonalPyramidal r y+
    generalizedPolygonalPyramidal r u [ZMOD (p:ℤ)^k] := by
  let : Fact p.Prime := ⟨prime⟩
  let s : ℤ := (r:ℤ)-2
  let a := 36*s
  let b := 18+18*s
  let c := 9+2*s
  have small (n : ℕ) (hn : 0<n) (hlt : n<p) : (n:ZMod p) ≠ 0 := by
    rw [Ne,ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hn hlt
  have h2 : (2:ZMod p) ≠ 0 := small 2 (by decide) (by omega)
  have h3 : (3:ZMod p) ≠ 0 := small 3 (by decide) (by omega)
  have hab : (a:ZMod p) ≠ 0 ∨ (b:ZMod p) ≠ 0 := by
    by_contra! bad
    have id : (2:ZMod p)*(b:ZMod p)-(a:ZMod p)=(2*3)^2 := by
      dsimp [a,b]
      push_cast
      ring
    rw [bad.1,bad.2,mul_zero,sub_zero] at id
    exact pow_ne_zero 2 (mul_ne_zero h2 h3) id.symm
  obtain ⟨x,y,u,h⟩ := lift_seed k a b c 1 z (by
    simpa only [Int.cast_one] using regular_cover large (a:ZMod p) b c 1 z hab)
  have value (t : ℤ) : generalizedPolygonalPyramidal r (6*t+1) = val a b c 1 t := by
    rw [value_six]
    dsimp [at_six,a,b,c,s,val]
    ring
  refine ⟨6*x+1,6*y+1,6*u+1,?_⟩
  rw [value,value,value]
  exact (Int.modEq_iff_dvd.mpr h).symm

end PyramidalLift

open OMA.S_oeis_a000330

theorem OMA.solution : OMA.R_oeis_a000330_R1.H1 := by
  intro r _ z m hm
  refine PyramidalCRT.all_of_prime_powers r z ?_ m hm
  intro p k hp
  by_cases h2 : p=2
  · subst p
    obtain ⟨t,ht⟩ := PyramidalLocal.two_power r k z
    exact ⟨6*t+1,0,0,by simpa [generalizedPolygonalPyramidal] using ht.symm⟩
  by_cases h3 : p=3
  · subst p
    exact PyramidalLocal.three_power r k z
  have large : 5 ≤ p := by
    have two := hp.two_le
    have four : p ≠ 4 := by rintro rfl; norm_num at hp
    omega
  exact PyramidalLift.large_prime r p k hp large z
