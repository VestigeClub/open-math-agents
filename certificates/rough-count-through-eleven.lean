import FormalConjectures.OEIS.«247824»

/-! Counting integers coprime to 2, 3, 5, 7 and 11 in complete periods of 2,310. -/
namespace ShortPeriod

open Finset

def cop (n : ℕ) : Bool := decide (n%2≠0 ∧ n%3≠0 ∧ n%5≠0 ∧ n%7≠0 ∧ n%11≠0)

private def pop (x : ℕ) : ℕ :=
  let a := x - ((x >>> 1) &&& 0x5555555555555555)
  let b := (a &&& 0x3333333333333333) + ((a >>> 2) &&& 0x3333333333333333)
  let c := (b+(b >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
  ((c*0x0101010101010101) >>> 56)%256

private def withinPeriod (n : ℕ) : ℕ :=
  let word := (0x1df000000000000002001d10228828228820a0801c4a08820228a20008801b628028208a20a00a201aa8008028a20a08820019c828228220808a208018f08200a20a082288201828228200a00a288200176228800a08a088200016828a2020882882820015a0a20a08a28028028014c820a082208282282013f20808a08808220a201330808228028228a000124a00a28808228820a011808808820228a2020010a8820828208a20a0800fba28028028220a08a00ef20820228200808a200e38808020a2020822800d5828220a00a00a28800c728228820a082088200ba0228a2020880882800ad208a20808a280280009f28a20a00a2080822009382208088288082200084a20a08220828208a007700a00a2882822802006a0a08a08820228a00005d208828828008a202005008a28028020a20a000438a208282280208080035228808220a20a082002808828228a00800a2001b8028228820a00a08000e800228a202088288000028208a20a08a2002 >>> (80*(n/64)))%(2^80)
  (word >>> 64)+pop (word%(2^(n%64+1)))

def wheel (n : ℕ) : ℕ := (n/2310)*480+withinPeriod (n%2310)

private def check (r : ℕ) : Bool :=
  wheel (r+1) == wheel r + (if cop (r+1) then 1 else 0)

private def valid (lo len : ℕ) : Prop := (List.range' lo len).all check=true
private theorem glue {lo a b : ℕ} (u : valid lo a) (v : valid (lo+a) b) : valid lo (a+b) := by
  unfold valid at *
  rw [← List.range'_append_1,List.all_append,u,v]
  rfl

private theorem b0 : valid 0 72 := by unfold valid; decide +kernel

private theorem b72 : valid 72 72 := by unfold valid; decide +kernel

private theorem b144 : valid 144 72 := by unfold valid; decide +kernel

private theorem b216 : valid 216 72 := by unfold valid; decide +kernel

private theorem b288 : valid 288 72 := by unfold valid; decide +kernel

private theorem b360 : valid 360 72 := by unfold valid; decide +kernel

private theorem b432 : valid 432 72 := by unfold valid; decide +kernel

private theorem b504 : valid 504 73 := by unfold valid; decide +kernel

private theorem b577 : valid 577 72 := by unfold valid; decide +kernel

private theorem b649 : valid 649 72 := by unfold valid; decide +kernel

private theorem b721 : valid 721 72 := by unfold valid; decide +kernel

private theorem b793 : valid 793 73 := by unfold valid; decide +kernel

private theorem b866 : valid 866 72 := by unfold valid; decide +kernel

private theorem b938 : valid 938 72 := by unfold valid; decide +kernel

private theorem b1010 : valid 1010 72 := by unfold valid; decide +kernel

private theorem b1082 : valid 1082 73 := by unfold valid; decide +kernel

private theorem b1155 : valid 1155 72 := by unfold valid; decide +kernel

private theorem b1227 : valid 1227 72 := by unfold valid; decide +kernel

private theorem b1299 : valid 1299 72 := by unfold valid; decide +kernel

private theorem b1371 : valid 1371 72 := by unfold valid; decide +kernel

private theorem b1443 : valid 1443 72 := by unfold valid; decide +kernel

private theorem b1515 : valid 1515 72 := by unfold valid; decide +kernel

private theorem b1587 : valid 1587 72 := by unfold valid; decide +kernel

private theorem b1659 : valid 1659 73 := by unfold valid; decide +kernel

private theorem b1732 : valid 1732 72 := by unfold valid; decide +kernel

private theorem b1804 : valid 1804 72 := by unfold valid; decide +kernel

private theorem b1876 : valid 1876 72 := by unfold valid; decide +kernel

private theorem b1948 : valid 1948 73 := by unfold valid; decide +kernel

private theorem b2021 : valid 2021 72 := by unfold valid; decide +kernel

private theorem b2093 : valid 2093 72 := by unfold valid; decide +kernel

private theorem b2165 : valid 2165 72 := by unfold valid; decide +kernel

private theorem b2237 : valid 2237 73 := by unfold valid; decide +kernel

private theorem allrows : valid 0 2310 := (glue (lo:=0) (a:=1155) (b:=1155) (glue (lo:=0) (a:=577) (b:=578) (glue (lo:=0) (a:=288) (b:=289) (glue (lo:=0) (a:=144) (b:=144) (glue (lo:=0) (a:=72) (b:=72) b0 b72) (glue (lo:=144) (a:=72) (b:=72) b144 b216)) (glue (lo:=288) (a:=144) (b:=145) (glue (lo:=288) (a:=72) (b:=72) b288 b360) (glue (lo:=432) (a:=72) (b:=73) b432 b504))) (glue (lo:=577) (a:=289) (b:=289) (glue (lo:=577) (a:=144) (b:=145) (glue (lo:=577) (a:=72) (b:=72) b577 b649) (glue (lo:=721) (a:=72) (b:=73) b721 b793)) (glue (lo:=866) (a:=144) (b:=145) (glue (lo:=866) (a:=72) (b:=72) b866 b938) (glue (lo:=1010) (a:=72) (b:=73) b1010 b1082)))) (glue (lo:=1155) (a:=577) (b:=578) (glue (lo:=1155) (a:=288) (b:=289) (glue (lo:=1155) (a:=144) (b:=144) (glue (lo:=1155) (a:=72) (b:=72) b1155 b1227) (glue (lo:=1299) (a:=72) (b:=72) b1299 b1371)) (glue (lo:=1443) (a:=144) (b:=145) (glue (lo:=1443) (a:=72) (b:=72) b1443 b1515) (glue (lo:=1587) (a:=72) (b:=73) b1587 b1659))) (glue (lo:=1732) (a:=289) (b:=289) (glue (lo:=1732) (a:=144) (b:=145) (glue (lo:=1732) (a:=72) (b:=72) b1732 b1804) (glue (lo:=1876) (a:=72) (b:=73) b1876 b1948)) (glue (lo:=2021) (a:=144) (b:=145) (glue (lo:=2021) (a:=72) (b:=72) b2021 b2093) (glue (lo:=2165) (a:=72) (b:=73) b2165 b2237)))))

private theorem wheel_shift (q r : ℕ) : wheel (2310*q+r)=q*480+wheel r := by
  simp [wheel,Nat.mul_add_div (by decide : 0<2310),Nat.add_mul,Nat.add_assoc]

private theorem cop_shift (q r : ℕ) : cop (2310*q+r)=cop r := by
  have m2 : (2310*q+r)%2 = r%2 := by rw [show 2310*q=2*(1155*q) by ring,Nat.mul_add_mod]
  have m3 : (2310*q+r)%3 = r%3 := by rw [show 2310*q=3*(770*q) by ring,Nat.mul_add_mod]
  have m5 : (2310*q+r)%5 = r%5 := by rw [show 2310*q=5*(462*q) by ring,Nat.mul_add_mod]
  have m7 : (2310*q+r)%7 = r%7 := by rw [show 2310*q=7*(330*q) by ring,Nat.mul_add_mod]
  have m11 : (2310*q+r)%11 = r%11 := by rw [show 2310*q=11*(210*q) by ring,Nat.mul_add_mod]
  simp only [cop,m2,m3,m5,m7,m11]

theorem wheel_succ (t : ℕ) :
    wheel (t+1)=wheel t+(if cop (t+1) then 1 else 0) := by
  let r := t%2310
  let q := t/2310
  have split : t=2310*q+r := (Nat.div_add_mod t 2310).symm
  have h : (List.range 2310).all check=true := by rw [List.range_eq_range'];exact allrows
  have item := List.all_eq_true.mp h r (List.mem_range.mpr (Nat.mod_lt t (by decide)))
  have step : wheel (r+1)=wheel r+(if cop (r+1) then 1 else 0) := beq_iff_eq.mp item
  rw [split,Nat.add_assoc,wheel_shift,wheel_shift,cop_shift,step,Nat.add_assoc]

private theorem cop_iff (n : ℕ) : cop n=true ↔ ∀ p ∈ Nat.primesLE 11, ¬ p ∣ n := by
  have ps : Nat.primesLE 11 = ({2,3,5,7,11} : Finset ℕ) := by decide +kernel
  rw [ps]
  simp [cop,Nat.dvd_iff_mod_eq_zero]

theorem count_rough (t : ℕ) :
    ((Icc 1 t).filter (fun n => ∀ p ∈ Nat.primesLE 11, ¬ p ∣ n)).card = wheel t := by
  induction t with
  | zero => decide +kernel
  | succ n ih =>
    have interval : Icc 1 (n+1) = insert (n+1) (Icc 1 n) := by
      ext k
      simp only [mem_Icc,mem_insert]
      omega
    have fresh : n+1 ∉ Icc 1 n := by simp
    rw [interval,Finset.filter_insert,wheel_succ,←ih]
    by_cases hp : ∀ p ∈ Nat.primesLE 11, ¬p ∣ n+1
    · rw [if_pos hp,(cop_iff _).mpr hp]
      exact Finset.card_insert_of_notMem (fun mem => fresh (Finset.mem_filter.mp mem).1)
    · have no : cop (n+1)=false := Bool.eq_false_iff.mpr (mt (cop_iff _).mp hp)
      rw [if_neg hp,no]
      simp

end ShortPeriod
