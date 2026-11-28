import OMAStatements.S_oeis_a380944
import Mathlib

/-!
# A380944: the binary recurrence at a block of ones

Credit: @VestigeClub.
Source: https://oeis.org/A380944 (Mikhail Kurkov).

We reverse each finite row into a finitely supported function. Appending a
zero to the binary index acts by Df(j)=(j+1)(f(j)+f(j+1)), with one boundary
correction. The initial binomial row is an eigenvector of D. On a delta
function, the zeroth coordinate of D^t is a factorial times a Stirling
number. Summing the boundary corrections proves the conjecture for all
nonnegative m and n, with the empty-range convention unchanged.
-/

namespace BinaryStirling
open OMA.S_oeis_a380944

lemma weight_zero : binaryWeight 0 = 0 := by decide

lemma weight_even (n : ℕ) : binaryWeight (2*n) = binaryWeight n := by
  by_cases hn : n=0
  · simp [hn,weight_zero]
  · have hd := Nat.digits_add 2 (by decide) 0 n (by decide) (Or.inr hn)
    simp only [Nat.zero_add] at hd
    change (Nat.digits 2 (2*n)).count 1 = _
    rw [hd]
    simp [binaryWeight]

lemma weight_odd (n : ℕ) : binaryWeight (2*n+1) = binaryWeight n+1 := by
  have hd := Nat.digits_add 2 (by decide) 1 n (by decide) (Or.inl (by decide))
  rw [Nat.add_comm] at hd
  change (Nat.digits 2 (2*n+1)).count 1 = _
  rw [hd]
  simp [binaryWeight]

lemma weight_pow_mul (m n : ℕ) : binaryWeight (2^m*n) = binaryWeight n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, show 2^m*2*n=2*(2^m*n) by ring,weight_even,ih]

lemma ones_succ (n : ℕ) : 2^(n+1)-1 = 2*(2^n-1)+1 := by
  rw [pow_succ]
  have hp : 0 < 2^n := pow_pos (by decide) n
  omega

lemma weight_ones (n : ℕ) : binaryWeight (2^n-1) = n := by
  induction n with
  | zero => exact weight_zero
  | succ n ih => rw [ones_succ,weight_odd,ih]

lemma weight_packed (m n : ℕ) : binaryWeight (2^m*(2^n-1)) = n := by
  rw [weight_pow_mul,weight_ones]

lemma b_col_zero (n : ℕ) : b n 0 = 1 := by rw [b]; simp
lemma b_row_zero (k : ℕ) : b 0 (k+1) = 0 := by rw [b]; simp

lemma b_odd (n k : ℕ) : b (2*n+1) (k+1) = b n (k+1)+b n k := by
  rw [b]
  simp [show (2*n+1)/2=n by omega, show (2*n+1)%2=1 by omega]

lemma b_even (n k : ℕ) (hn : 0<n) :
    b (2*n) (k+1) = ((binaryWeight n:ℤ)-(k:ℤ))*(b n (k+1)+b n k) := by
  rw [b]
  simp [show 2*n ≠ 0 by omega, show (2*n)/2=n by omega, show (2*n)%2=0 by omega,
    show (binaryWeight n:ℤ)-((k:ℤ)+1)+1=(binaryWeight n:ℤ)-k by ring]

lemma b_ones (n k : ℕ) : b (2^n-1) k = (n.choose k : ℤ) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rw [b_col_zero]; simp
    | succ k =>
      change b 0 (k+1)=_
      rw [b_row_zero]; simp
  | succ n ih =>
    cases k with
    | zero => rw [b_col_zero]; simp
    | succ k =>
      rw [ones_succ,b_odd,ih,ih,Nat.choose_succ_succ]
      push_cast
      ring

end BinaryStirling

namespace BinaryStirling
open OMA.S_oeis_a380944

abbrev V := ℕ → ℤ

def D : Module.End ℤ V where
  toFun f j := ((j:ℤ)+1)*(f j+f (j+1))
  map_add' f g := by funext j; simp; ring
  map_smul' c f := by funext j; simp; ring

def delta (n : ℕ) : V := fun j => if j=n then 1 else 0

def chooseVec (n : ℕ) : V := fun j => (n.choose j : ℤ)

lemma D_delta_zero : D (delta 0) = delta 0 := by
  funext j
  by_cases h : j=0 <;> simp [D,delta,h]

lemma D_delta_succ (n : ℕ) :
    D (delta (n+1)) = ((n:ℤ)+2) • delta (n+1) + ((n:ℤ)+1) • delta n := by
  funext j
  have he : (j+1=n+1) ↔ j=n := by omega
  by_cases h0 : j=n <;> by_cases h1 : j=n+1 <;>
    simp [D,delta,Pi.smul_apply,smul_eq_mul,he,h0,h1] <;> omega

lemma D_choose (n : ℕ) : D (chooseVec n) = ((n:ℤ)+1) • chooseVec n := by
  funext j
  have h := Nat.add_one_mul_choose_eq n j
  rw [Nat.choose_succ_succ] at h
  have hz := congrArg (fun k : ℕ => (k:ℤ)) h
  push_cast at hz
  simp only [D,chooseVec,LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,smul_eq_mul]
  nlinarith

lemma delta_iter (m n : ℕ) :
    ((D^m) (delta n)) 0 = (n.factorial:ℤ)*(Nat.stirlingSecond (m+1) (n+1):ℤ) := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => simp [delta,Nat.stirlingSecond]
    | succ n => simp [delta,Nat.stirlingSecond]
  | succ m ih =>
    rw [pow_succ,Module.End.mul_apply]
    cases n with
    | zero =>
      rw [D_delta_zero,ih]
      simp [Nat.stirlingSecond_one_right]
    | succ n =>
      rw [D_delta_succ,map_add,map_smul,map_smul]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,ih]
      rw [Nat.stirlingSecond_succ_succ (m+1) (n+1)]
      push_cast
      simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      ring

end BinaryStirling

namespace BinaryStirling
open OMA.S_oeis_a380944

def packed (n m : ℕ) : ℕ := 2^m*(2^n-1)
def row (n m : ℕ) : V := fun j => if j≤n then b (packed n m) (n-j) else 0

lemma packed_weight (n m : ℕ) : binaryWeight (packed n m)=n := weight_packed m n

lemma packed_pos (n m : ℕ) (hn : 0<n) : 0<packed n m := by
  have h := packed_weight n m
  by_contra hz
  have he : packed n m=0 := by omega
  rw [he,weight_zero] at h
  omega

lemma packed_succ (n m : ℕ) : packed n (m+1)=2*packed n m := by
  dsimp [packed]
  rw [pow_succ]
  ring

lemma row_initial (n : ℕ) : row n 0=chooseVec n := by
  funext j
  by_cases hj : j≤n
  · simp only [row,chooseVec,if_pos hj,packed,pow_zero,one_mul]
    rw [b_ones,Nat.choose_symm hj]
  · simp [row,chooseVec,hj,Nat.choose_eq_zero_of_lt (by omega : n<j)]

lemma row_top (n m : ℕ) : row n m 0=a (packed n m) := by
  simp [row,a,packed_weight]

lemma row_step (n m : ℕ) : row n (m+1)=D (row n m)-(n:ℤ) • delta n := by
  funext j
  rcases lt_trichotomy j n with hj | rfl | hj
  · have hle : j≤n := by omega
    have hnext : j+1≤n := by omega
    have hne : j≠n := by omega
    have hn : 0<n := by omega
    simp only [row,if_pos hle,if_pos hnext,D,LinearMap.coe_mk,AddHom.coe_mk,
      Pi.sub_apply,Pi.smul_apply,smul_eq_mul,delta,if_neg hne,mul_zero,sub_zero]
    rw [packed_succ,show n-j=(n-j-1)+1 by omega,b_even _ _ (packed_pos n m hn),packed_weight]
    have hk : ((n-j-1:ℕ):ℤ)=(n:ℤ)-(j:ℤ)-1 := by omega
    rw [hk]
    rw [show n-j-1=n-(j+1) by omega]
    ring
  · simp [row,D,delta,b_col_zero,Pi.smul_apply,smul_eq_mul]
  · have hle : ¬j≤n := by omega
    have hnext : ¬j+1≤n := by omega
    have hne : j≠n := by omega
    simp [row,D,delta,hle,hnext,hne,Pi.smul_apply,smul_eq_mul] <;> omega

end BinaryStirling

namespace BinaryStirling
open OMA.S_oeis_a380944

lemma driven_solution (n : ℕ) (R : ℕ → V) (hzero : R 0=chooseVec n)
    (hstep : ∀ m, R (m+1)=D (R m)-(n:ℤ) • delta n) (m : ℕ) :
    R m = (((n:ℤ)+1)^m) • chooseVec n -
      (n:ℤ) • ∑ t ∈ Finset.range m, (D^t) (delta n) := by
  induction m with
  | zero => simp [hzero]
  | succ m ih =>
    have hD : D (∑ t ∈ Finset.range m, (D^t) (delta n)) =
        ∑ t ∈ Finset.range m, (D^(t+1)) (delta n) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [pow_succ',Module.End.mul_apply]
    have hsum : (∑ t ∈ Finset.range (m+1), (D^t) (delta n)) =
        delta n + ∑ t ∈ Finset.range m, (D^(t+1)) (delta n) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero,Module.End.one_apply]
      abel
    rw [hstep,ih,map_sub,map_smul,map_smul,D_choose,hD,hsum]
    funext j
    simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,pow_succ]
    ring

lemma stirling_prefix (m n : ℕ) :
    (∑ t ∈ Finset.range m, (Nat.stirlingSecond (t+1) (n+1):ℤ)) = (c m (n+1):ℤ) := by
  simp only [c,Nat.cast_sum,show m+1-(n+1)=m-n by omega]
  by_cases hmn : m≤n
  · have he : m-n=0 := by omega
    rw [he]
    simp only [Finset.range_zero,Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro t ht
    have hlt := Finset.mem_range.mp ht
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]
    rfl
  · have hlt : n < m := by omega
    have hz : (∑ t ∈ Finset.range n, (Nat.stirlingSecond (t+1) (n+1):ℤ))=0 := by
      apply Finset.sum_eq_zero
      intro t ht
      rw [Nat.stirlingSecond_eq_zero_of_lt (by have := Finset.mem_range.mp ht; omega)]
      rfl
    conv_lhs => rw [show m=n+(m-n) by omega,Finset.sum_range_add]
    rw [hz,zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show n+i+1=n+1+i by omega]

theorem conjecture (m n : ℕ) :
    a (2^m*(2^n-1)) = ((n:ℤ)+1)^m-(n:ℤ)*(n.factorial:ℤ)*(c m (n+1):ℤ) := by
  have h := congrFun (driven_solution n (row n) (row_initial n) (row_step n) m) 0
  rw [row_top] at h
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,chooseVec,Nat.choose_zero_right,
    Nat.cast_one,mul_one,Finset.sum_apply,delta_iter] at h
  rw [← Finset.mul_sum,stirling_prefix] at h
  change a (2^m*(2^n-1)) = _ at h
  rw [h]
  ring

end BinaryStirling

theorem OMA.solution : type_of% @OMA.S_oeis_a380944.main :=
  BinaryStirling.conjecture
