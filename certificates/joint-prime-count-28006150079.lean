import certificates.«semiprime-correction-555157672301-small»
import certificates.«rough-count-through-eleven»
import certificates.«prime-table-through-9223368»

/-!
# A certified value of the prime-counting function at 28,006,150,079

Credit: @VestigeClub. A wheel sieve verifies a table of prime counts. Legendre's
recurrence stops when the remaining interval contains no composite with two
surviving prime factors. Meissel's semiprime correction gives the exact count.
Blocks of 2,310 count survivors of the first five primes, and a smaller bitmap
supplies the frequently used initial prime counts.

The Meissel identity comes from Physbuzz's published reduction for A247824.
The Legendre recursion adapts Daniel Veljjanoski's Palomar proof as formalized
by rleshner in OeisA100475.conjecture (Apache-2.0).
Palomar source: https://github.com/veljjanoski/oeis100475-palomar/tree/0968200356e449a24a023264821d4ea966091cf0
Reference: https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9315
-/

namespace HybridBound28006

def fast (n : ℕ) : ℕ :=
  if n≤206781 then WheelTableA94.fast n else CheckpointA28006Slim.fast n

theorem fast_correct (n : ℕ) (hn : n≤9223368) : fast n=Nat.primeCounting n := by
  unfold fast
  split_ifs with small
  · exact WheelTableA94.fast_correct n small
  · exact CheckpointA28006Slim.fast_correct n hn

end HybridBound28006


/- The Legendre and Meissel identities below are the public Physbuzz reduction
for OEIS A247824, itself crediting Daniel Veljjanoski and rleshner. The numerical proof below certifies one of the residual ranks. -/
open Finset
namespace JointEndpoint28006

lemma legendre {ps : List ℕ} (hsort : ps.Pairwise (· > ·)) (hprime : ∀ p ∈ ps, Nat.Prime p)
    (hcomp : ∀ p ∈ ps, ∀ q, Nat.Prime q → q < p → q ∈ ps) (x : ℕ) :
    ps.foldr (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) => if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id x =
      ((Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)).card := by
  let sieveSet (ps : List ℕ) (x : ℕ) := (Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)
  have mem_sieveSet {ps : List ℕ} {x n : ℕ} :
      n ∈ sieveSet ps x ↔ (1 ≤ n ∧ n ≤ x) ∧ ∀ p ∈ ps, ¬ p ∣ n := by
    simp [sieveSet]

  have sieveSet_nil (x : ℕ) : sieveSet [] x = Finset.Icc 1 x := by
    ext n; simp [sieveSet]

  /- Legendre's recursion step. -/
  have card_sieveSet_cons {p : ℕ} {ps : List ℕ} (hp : p.Prime) (hps : ∀ q ∈ ps, q.Prime ∧ q ≠ p)
      (x : ℕ) :
      (sieveSet (p :: ps) x).card = (sieveSet ps x).card - (sieveSet ps (x / p)).card := by
    have hsplit : sieveSet (p :: ps) x = (sieveSet ps x).filter (fun n => ¬ p ∣ n) := by
      ext n; simp [sieveSet, List.mem_cons]; tauto
    have himage : (sieveSet ps x).filter (fun n => p ∣ n) = (sieveSet ps (x / p)).image (p * ·) := by
      ext n
      simp only [Finset.mem_filter, mem_sieveSet, Finset.mem_image]
      constructor
      · rintro ⟨⟨⟨h1, hx⟩, hq⟩, ⟨m, rfl⟩⟩
        refine ⟨m, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos m with rfl | hm
          · simp at h1
          · exact hm
        · exact (Nat.le_div_iff_mul_le hp.pos).2 (by rw [mul_comm]; exact hx)
        · intro q hq' hdvd
          exact hq q hq' (dvd_mul_of_dvd_right hdvd p)
      · rintro ⟨m, ⟨⟨h1, hm⟩, hq⟩, rfl⟩
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right p m⟩
        · exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.ne_zero (by omega))
        · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hp.pos).1 hm
        · intro q hq' hdvd
          obtain ⟨hqp, hqne⟩ := hps q hq'
          rcases (Nat.Prime.dvd_mul hqp).1 hdvd with h | h
          · exact hqne ((Nat.prime_dvd_prime_iff_eq hqp hp).1 h)
          · exact hq q hq' h
    have hcard := Finset.card_filter_add_card_filter_not (s := sieveSet ps x) (fun n => p ∣ n)
    rw [himage, Finset.card_image_of_injective _ (mul_right_injective₀ hp.ne_zero)] at hcard
    rw [hsplit]
    omega

  /- Pruning: below `p`, only `1` survives the sieve by all primes less than `p`. -/
  have card_sieveSet_of_lt {p : ℕ} {ps : List ℕ} (hps : ∀ q ∈ ps, q.Prime)
      (hcomplete : ∀ q, q.Prime → q < p → q ∈ ps) {x : ℕ} (hx : x < p) :
      (sieveSet (p :: ps) x).card = if x = 0 then 0 else 1 := by
    split_ifs with h0
    · subst h0; simp [sieveSet]
    · have : sieveSet (p :: ps) x = {1} := by
        ext n
        simp only [mem_sieveSet, Finset.mem_singleton, List.mem_cons, forall_eq_or_imp]
        constructor
        · rintro ⟨⟨h1, hnx⟩, -, hq⟩
          by_contra hne
          have hn1 : n ≠ 1 := hne
          have hmf := Nat.minFac_prime hn1
          have hlt : Nat.minFac n < p := lt_of_le_of_lt (Nat.minFac_le (by omega)) (by omega)
          exact hq _ (hcomplete _ hmf hlt) (Nat.minFac_dvd n)
        · rintro rfl
          refine ⟨⟨le_rfl, by omega⟩, ?_, ?_⟩
          · intro h
            have := Nat.le_of_dvd one_pos h
            omega
          · intro q hq; exact Nat.Prime.not_dvd_one (hps q hq)
      rw [this, Finset.card_singleton]

  change _ = (sieveSet ps x).card
  induction ps generalizing x with
  | nil => simp [sieveSet_nil]
  | cons p ps ih =>
    obtain ⟨hgt,hs⟩ := List.pairwise_cons.mp hsort
    have hp := hprime p List.mem_cons_self
    have hq (q) (hq : q ∈ ps) := hprime q (List.mem_cons_of_mem p hq)
    have hc (q) (h : q.Prime) (lt : q < p) : q ∈ ps := by
      rcases List.mem_cons.mp (hcomp p List.mem_cons_self q h lt) with eq | hm
      · omega
      · exact hm
    have closed (r) (hr : r ∈ ps) (q) (h : q.Prime) (lt : q < r) := hc q h (lt.trans (hgt r hr))
    simp only [List.foldr_cons]
    split_ifs with lt zero
    · rw [card_sieveSet_of_lt hq hc lt, if_pos zero]
    · rw [card_sieveSet_of_lt hq hc lt, if_neg zero]
    · rw [card_sieveSet_cons hp (fun q h => ⟨hq q h, (hgt q h).ne⟩), ih hs hq closed, ih hs hq closed]

lemma legendre_range (y x : ℕ) :
    (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr
      (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) => if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id x) =
    ((Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card := by
  let ps := ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse
  have mem (p : ℕ) : p ∈ ps ↔ p ∈ Nat.primesLE y := by simp [ps, Nat.mem_primesLE]
  have hsort : ps.Pairwise (· > ·) := by
    apply List.pairwise_reverse.mpr
    exact List.pairwise_lt_range.filter _
  have e := legendre hsort (fun p hp => Nat.prime_of_mem_primesLE ((mem p).mp hp))
    (fun p hp q hq hlt => (mem q).mpr (Nat.mem_primesLE.mpr ⟨hlt.le.trans (Nat.le_of_mem_primesLE ((mem p).mp hp)), hq⟩)) x
  convert e using 1
  congr 1
  ext n
  simp only [mem_filter, mem_Icc, mem]

/-- At a cube-root cutoff, every surviving composite has exactly two prime factors,
with multiplicity. Sorting the factors makes this parametrization injective. -/
lemma meissel {x y z : ℕ} (hx : 1 ≤ x) (hy : y ≤ x) (cube : x < (y+1)^3)
    (sq : x < (z+1)^2) :
    ((Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card +
      (Nat.primesLE y).card = 1 + (Nat.primesLE x).card +
      ∑ p ∈ (Nat.primesLE z).filter (y < ·), ((Nat.primesLE (x/p)).filter (p ≤ ·)).card := by
  classical
  let R := (Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)
  let T := R.filter (fun n => n ≠ 1 ∧ ¬n.Prime)
  let B := (Nat.primesLE z).filter (y < ·)
  let Q (p : ℕ) := (Nat.primesLE (x/p)).filter (p ≤ ·)
  have memR (n) : n ∈ R ↔ (1 ≤ n ∧ n ≤ x) ∧ ∀ p ∈ Nat.primesLE y, ¬ p ∣ n := by simp [R]
  have memT (n) : n ∈ T ↔ n ∈ R ∧ n ≠ 1 ∧ ¬n.Prime := by simp [T]
  have memB (p) : p ∈ B ↔ (p ≤ z ∧ p.Prime) ∧ y < p := by simp [B, Nat.mem_primesLE]
  have memQ (p q) : q ∈ Q p ↔ (q ≤ x/p ∧ q.Prime) ∧ p ≤ q := by simp [Q, Nat.mem_primesLE]
  have least {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p ≤ q) : (p*q).minFac = p := by
    have hn : p*q ≠ 1 := by have := hp.two_le; have := hq.two_le; nlinarith
    have hm := Nat.minFac_prime hn
    apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q))
    rcases hm.dvd_mul.mp (Nat.minFac_dvd (p*q)) with a | b
    · exact ((Nat.prime_dvd_prime_iff_eq hm hp).mp a).symm.le
    · exact pq.trans_eq ((Nat.prime_dvd_prime_iff_eq hm hq).mp b).symm
  have pair : (B.sigma Q).card = T.card := by
    apply card_bij (fun a _ => a.1 * a.2)
    · intro ⟨p,q⟩ h
      obtain ⟨hb,hq⟩ := mem_sigma.mp h
      obtain ⟨⟨_,pp⟩,yp⟩ := (memB p).mp hb
      obtain ⟨⟨ub,qp⟩,ord⟩ := (memQ p q).mp hq
      have pos := Nat.mul_pos pp.pos qp.pos
      have bound : p*q ≤ x := by simpa [mul_comm] using (Nat.le_div_iff_mul_le pp.pos).mp ub
      apply (memT _).mpr
      refine ⟨(memR _).mpr ⟨⟨pos,bound⟩, ?_⟩, ?_, ?_⟩
      · intro r hr hd
        obtain ⟨ry,rp⟩ := Nat.mem_primesLE.mp hr
        rcases rp.dvd_mul.mp hd with a | b
        · have := (Nat.prime_dvd_prime_iff_eq rp pp).mp a; omega
        · have := (Nat.prime_dvd_prime_iff_eq rp qp).mp b; omega
      · have := pp.two_le; have := qp.two_le; dsimp; nlinarith
      · intro prime
        have := (Nat.prime_dvd_prime_iff_eq pp prime).mp (dvd_mul_right p q)
        have := pp.two_le; have := qp.two_le; dsimp at *; nlinarith
    · intro ⟨p,q⟩ ha ⟨r,s⟩ hb eq
      obtain ⟨ha,hq⟩ := mem_sigma.mp ha
      obtain ⟨hb,hs⟩ := mem_sigma.mp hb
      obtain ⟨⟨_,pp⟩,_⟩ := (memB p).mp ha
      obtain ⟨⟨_,rp⟩,_⟩ := (memB r).mp hb
      obtain ⟨⟨_,qp⟩,a⟩ := (memQ p q).mp hq
      obtain ⟨⟨_,sp⟩,b⟩ := (memQ r s).mp hs
      change p*q=r*s at eq
      have same := (least pp qp a).symm.trans ((congrArg Nat.minFac eq).trans (least rp sp b))
      subst r
      obtain rfl := Nat.eq_of_mul_eq_mul_left pp.pos eq
      rfl
    · intro n hn
      obtain ⟨hr,ne,np⟩ := (memT n).mp hn
      obtain ⟨⟨pos,bound⟩,rough⟩ := (memR n).mp hr
      let p := n.minFac
      let q := n / p
      have pp : p.Prime := Nat.minFac_prime ne
      have product : p*q = n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
      have ord : p ≤ q := Nat.minFac_le_div pos np
      have yp : y < p := by
        by_contra! h
        exact rough _ (Nat.mem_primesLE.mpr ⟨h,pp⟩) (Nat.minFac_dvd n)
      have qp : q.Prime := by
        by_contra hq
        have qpos : 0 < q := pp.pos.trans_le ord
        have qq := Nat.minFac_sq_le_self qpos hq
        have qne : q ≠ 1 := by have := pp.two_le; omega
        have rprime := Nat.minFac_prime qne
        have yr : y < q.minFac := by
          by_contra! h
          apply rough _ (Nat.mem_primesLE.mpr ⟨h,rprime⟩)
          rw [← product]
          exact dvd_mul_of_dvd_right (Nat.minFac_dvd q) _
        have b := Nat.mul_le_mul (show y+1 ≤ p by omega)
          (le_trans (Nat.pow_le_pow_left (show y+1 ≤ q.minFac by omega) 2) qq)
        nlinarith only [product,b,bound,cube]
      have pz : p ≤ z := by
        by_contra! h
        have a := Nat.mul_le_mul (show z+1≤p by omega) (show z+1≤q by omega)
        nlinarith only [product,a,sq,bound]
      refine ⟨⟨p,q⟩, mem_sigma.mpr ⟨(memB _).mpr ⟨⟨pz,pp⟩,yp⟩,
        (memQ _ _).mpr ⟨⟨(Nat.le_div_iff_mul_le pp.pos).mpr ?_,qp⟩,ord⟩⟩, product⟩
      simpa [mul_comm,product] using (product.le.trans bound)
  have primepart : R.filter Nat.Prime = (Nat.primesLE x).filter (fun n => ¬ n ≤ y) := by
    ext n
    simp only [mem_filter,memR,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨_,ub⟩,r⟩,np⟩
      exact ⟨⟨ub,np⟩,fun h => r n ⟨h,np⟩ (dvd_refl n)⟩
    · rintro ⟨⟨ub,np⟩,gt⟩
      refine ⟨⟨⟨np.one_le,ub⟩,fun p hp hd => ?_⟩, np⟩
      exact gt (((Nat.prime_dvd_prime_iff_eq hp.2 np).mp hd) ▸ hp.1)
  have low : (Nat.primesLE x).filter (· ≤ y) = Nat.primesLE y := by
    ext n
    simp only [mem_filter,Nat.mem_primesLE]
    exact ⟨fun h => ⟨h.2,h.1.2⟩, fun h => ⟨⟨h.1.trans hy,h.2⟩,h.1⟩⟩
  have other : R.filter (fun n => ¬n.Prime) = insert 1 T := by
    ext n
    simp only [mem_filter,mem_insert,memT]
    constructor
    · rintro ⟨hr,hp⟩; by_cases h : n=1
      · exact Or.inl h
      · exact Or.inr ⟨hr,h,hp⟩
    · rintro (rfl | ⟨hr,_,hp⟩)
      · exact ⟨(memR _).mpr ⟨⟨le_rfl,hx⟩,fun p hp => (Nat.prime_of_mem_primesLE hp).not_dvd_one⟩,Nat.not_prime_one⟩
      · exact ⟨hr,hp⟩
  have one : 1 ∉ T := fun h => ((memT 1).mp h).2.1 rfl
  have v := card_filter_add_card_filter_not (s:=R) Nat.Prime
  have w := card_filter_add_card_filter_not (s:=Nat.primesLE x) (· ≤ y)
  rw [primepart,other,card_insert_of_notMem one] at v
  rw [low] at w
  rw [card_sigma] at pair
  change R.card + _ = 1 + _ + ∑ p ∈ B, (Q p).card
  omega

/-- Interval subtraction evaluates each row of the semiprime count using only ordinary prime counts. -/
lemma prime_row {p t : ℕ} (pos : 0 < p) (le : p ≤ t) :
    ((Nat.primesLE t).filter (p ≤ ·)).card = Nat.primeCounting t - Nat.primeCounting (p-1) := by
  have eq : (Nat.primesLE t).filter (fun n => ¬p ≤ n) = Nat.primesLE (p-1) := by
    ext n
    simp only [mem_filter,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_,pr⟩,lt⟩; exact ⟨by omega,pr⟩
    · rintro ⟨ub,pr⟩; exact ⟨⟨by omega,pr⟩,by omega⟩
  have h := card_filter_add_card_filter_not (s:=Nat.primesLE t) (p ≤ ·)
  rw [eq, Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at h
  omega

lemma rank_of_parts {x y z a b r : ℕ} (hx : 1 ≤ x) (hy : y ≤ x) (cube : x < (y+1)^3)
    (sq : x < (z+1)^2) (zs : z*z ≤ x)
    (sieved : (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr
      (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) => if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id x) +
      (Nat.primesLE y).card = a)
    (pairs : (∑ p ∈ (Nat.primesLE z).filter (y < ·), (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = b)
    (result : 1+r+b = a) : Nat.primeCounting x = r := by
  have e := meissel hx hy cube sq
  have row (p : ℕ) (hp : p ∈ (Nat.primesLE z).filter (y < ·)) := by
    have bound := Nat.le_of_mem_primesLE (mem_filter.mp hp).1
    have pos := (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1).pos
    exact prime_row pos ((Nat.le_div_iff_mul_le pos).mpr ((Nat.mul_le_mul bound bound).trans zs))
  rw [legendre_range] at sieved
  rw [sum_congr rfl row, pairs, Nat.primesLE_card_eq_primeCounting x] at e
  omega

def advance (p : ℕ) (f : ℕ → ℕ) (x : ℕ) :=
  if x < p then (if x=0 then 0 else 1) else f x - f (x/p)

private def evalPhi (table : ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [], t => t
  | p :: ps, t => if p=11 then ShortPeriod.wheel t else if t < p then (if t=0 then 0 else 1) else
      if t < (p+1)^2 then 1 + table t - table p else
        evalPhi table ps t - evalPhi table ps (t/p)

private theorem square_cut {p t : ℕ} (hp : 0 < p) (pt : p ≤ t) (square : t < (p+1)^2) :
    (((List.range (p+1)).filter (fun n => decide n.Prime)).reverse.foldr advance id) t +
      Nat.primeCounting p = 1 + Nat.primeCounting t := by
  have cube : t < (p+1)^3 :=
    lt_of_lt_of_le square (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3))
  have empty : (Nat.primesLE p).filter (p < ·) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    exact (not_lt_of_ge (Nat.le_of_mem_primesLE (Finset.mem_filter.mp hn).1))
      (Finset.mem_filter.mp hn).2
  have h := meissel (x:=t) (y:=p) (z:=p) (by omega) pt cube square
  simp only [empty,Finset.sum_empty,Nat.add_zero,Nat.primesLE_card_eq_primeCounting] at h
  rw [←legendre_range] at h
  exact h

private theorem refine_row {bound p : ℕ} (tab : ℕ → ℕ) (ok : ∀ t, t ≤ bound → tab t = Nat.primeCounting t)
    (ps : List ℕ) (lst : ((List.range (p+1)).filter (fun n => decide n.Prime)).reverse = p::ps)
    (prev : ∀ t, ps.foldr advance id t = evalPhi tab ps t)
    (pos : 0 < p) (cap : (p+1)^2 ≤ bound+1) : ∀ t,
    (p::ps).foldr advance id t = evalPhi tab (p::ps) t := by
  intro t
  by_cases hbase : p=11
  · subst p
    have val : (11::ps).foldr advance id t = ShortPeriod.wheel t := by
      rw [←lst]
      exact (legendre_range 11 t).trans (ShortPeriod.count_rough t)
    simpa [evalPhi] using val
  by_cases sm : t < p
  · simp [List.foldr_cons,advance,evalPhi,hbase,sm]
  · by_cases short : t < (p+1)^2
    · have h := square_cut pos (by omega : p ≤ t) short
      rw [lst] at h
      rw [evalPhi,if_neg hbase,if_neg sm,if_pos short,ok t (by omega),ok p (by omega)]
      omega
    · simp only [List.foldr_cons,advance,evalPhi,if_neg hbase,if_neg sm,if_neg short,prev]

private theorem merge_filter (f : ℕ → Bool) (lo a b : ℕ) (l r : List ℕ)
    (hl : (List.range' lo a).filter f = l) (hr : (List.range' (lo+a) b).filter f = r) :
    (List.range' lo (a+b)).filter f = l++r := by
  rw [←List.range'_append_1,List.filter_append,hl,hr]

private theorem eval_delta (tab : ℕ → ℕ) (ps : List ℕ) (p n q old dec ans : ℕ)
    (notWheel : p≠11) (le : p ≤ n) (sq : (p+1)^2 ≤ n) (div : n/p = q)
    (base : evalPhi tab ps n = old) (cut : evalPhi tab ps q = dec) (sub : old-dec=ans) :
    evalPhi tab (p::ps) n = ans := by
  rw [evalPhi,if_neg notWheel,if_neg (not_lt.mpr le),if_neg (not_lt.mpr sq),div,base,cut,sub]

private theorem assemble {x y z a b r : ℕ} (hx : 1 ≤ x) (hy : y ≤ x) (cube : x < (y+1)^3)
    (sq : x < (z+1)^2) (zs : z*z ≤ x)
    (sieved : (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id x) +
      (Nat.primesLE y).card = a)
    (rows : (∑ p ∈ (Nat.primesLE z).filter (y < ·), (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = b)
    (total : 1+r+b=a) : Nat.primeCounting x=r := by
  exact rank_of_parts hx hy cube sq zs sieved rows total

private theorem agree_range {bound : ℕ} (table : ℕ → ℕ)
    (ok : ∀ t, t ≤ bound → table t = Nat.primeCounting t)
    (y : ℕ) (cap : (y+1)^2 ≤ bound+1) :
    ∀ t, (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id) t =
      evalPhi table ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse t := by
  induction y with
  | zero => simp [List.range_succ,evalPhi]
  | succ n ih =>
    have c : (n+1)^2 ≤ bound+1 :=
      le_trans (Nat.pow_le_pow_left (by omega : n+1 ≤ n+1+1) 2) cap
    by_cases hp : (n+1).Prime
    · have row : ((List.range (n+1+1)).filter (fun p => decide p.Prime)).reverse =
          (n+1) :: ((List.range (n+1)).filter (fun p => decide p.Prime)).reverse := by
        rw [List.range_succ (n:=n+1),List.filter_append,List.reverse_append]
        simp [hp]
      rw [row]
      exact refine_row table ok _ row (ih c) (by omega) cap
    · have row : ((List.range (n+1+1)).filter (fun p => decide p.Prime)).reverse =
          ((List.range (n+1)).filter (fun p => decide p.Prime)).reverse := by
        rw [List.range_succ (n:=n+1),List.filter_append,List.reverse_append]
        simp [hp]
      rw [row]
      exact ih c

private def contribution (x y : ℕ) (tab : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then tab (x/p) - tab (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z b value : ℕ} (tab : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, n≤b → tab n = Nat.primeCounting n)
    (prime_ok : ∀ n, n≤b → (prime n=true ↔ n.Prime))
    (hz : z≤b) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y tab prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y tab prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p≤b := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ (le_trans ub hq),ok _ (by omega : p-1≤b)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y tab prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y tab prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev tab := HybridBound28006.fast
private abbrev F := evalPhi tab

private abbrev prime := CheckpointA28006Slim.prime
private theorem prime_ok (n : ℕ) (hn : n≤9223368) : prime n=true ↔ n.Prime := CheckpointA28006Slim.prime_ok n hn


private theorem takeStep {ps : List ℕ} {p q prev cut ans : ℕ}
    (notWheel : p≠11) (base : F ps 28006150079=prev) (part : F ps q=cut) (div : 28006150079/p=q)
    (le : p≤28006150079) (sq : (p+1)^2≤28006150079) (sub : prev-cut=ans) :
    F (p::ps) 28006150079=ans := eval_delta tab ps p 28006150079 q prev cut ans notWheel le sq div base part sub


private def ps0 : List ℕ := []
private theorem v0 : F ps0 28006150079=28006150079 := rfl

private def ps1 : List ℕ := 2::ps0
private theorem c1 : F ps0 14003075039=14003075039 := by decide +kernel
private theorem v1 : F ps1 28006150079=14003075040 :=
  takeStep (p:=2) (by decide) v0 c1 rfl (by decide) (by decide) rfl

private def ps2 : List ℕ := 3::ps1
private theorem c2 : F ps1 9335383359=4667691680 := by decide +kernel
private theorem v2 : F ps2 28006150079=9335383360 :=
  takeStep (p:=3) (by decide) v1 c2 rfl (by decide) (by decide) rfl

private def ps3 : List ℕ := 5::ps2
private theorem c3 : F ps2 5601230015=1867076672 := by decide +kernel
private theorem v3 : F ps3 28006150079=7468306688 :=
  takeStep (p:=5) (by decide) v2 c3 rfl (by decide) (by decide) rfl

private def ps4 : List ℕ := 7::ps3
private theorem c4 : F ps3 4000878582=1066900955 := by decide +kernel
private theorem v4 : F ps4 28006150079=6401405733 :=
  takeStep (p:=7) (by decide) v3 c4 rfl (by decide) (by decide) rfl

private def ps5 : List ℕ := 11::ps4
private theorem c5 : F ps4 2546013643=581945976 := by decide +kernel
private theorem v5 : F ps5 28006150079=5819459757 := by decide +kernel

private def ps6 : List ℕ := 13::ps5
private theorem c6 : F ps5 2154319236=447650750 := by decide +kernel
private theorem v6 : F ps6 28006150079=5371809007 :=
  takeStep (p:=13) (by decide) v5 c6 rfl (by decide) (by decide) rfl

private def ps7 : List ℕ := 17::ps6
private theorem c7 : F ps6 1647420592=315988767 := by decide +kernel
private theorem v7 : F ps7 28006150079=5055820240 :=
  takeStep (p:=17) (by decide) v6 c7 rfl (by decide) (by decide) rfl

private def ps8 : List ℕ := 19::ps7
private theorem c8 : F ps7 1474007898=266095804 := by decide +kernel
private theorem v8 : F ps8 28006150079=4789724436 :=
  takeStep (p:=19) (by decide) v7 c8 rfl (by decide) (by decide) rfl

private def ps9 : List ℕ := 23::ps8
private theorem c9 : F ps8 1217658699=208248888 := by decide +kernel
private theorem v9 : F ps9 28006150079=4581475548 :=
  takeStep (p:=23) (by decide) v8 c9 rfl (by decide) (by decide) rfl

private def ps10 : List ℕ := 29::ps9
private theorem c10 : F ps9 965729313=157981915 := by decide +kernel
private theorem v10 : F ps10 28006150079=4423493633 :=
  takeStep (p:=29) (by decide) v9 c10 rfl (by decide) (by decide) rfl

private def ps11 : List ℕ := 31::ps10
private theorem c11 : F ps10 903424196=142693341 := by decide +kernel
private theorem v11 : F ps11 28006150079=4280800292 :=
  takeStep (p:=31) (by decide) v10 c11 rfl (by decide) (by decide) rfl

private def ps12 : List ℕ := 37::ps11
private theorem c12 : F ps11 756922975=115697293 := by decide +kernel
private theorem v12 : F ps12 28006150079=4165102999 :=
  takeStep (p:=37) (by decide) v11 c12 rfl (by decide) (by decide) rfl

private def ps13 : List ℕ := 41::ps12
private theorem c13 : F ps12 683076831=101587869 := by decide +kernel
private theorem v13 : F ps13 28006150079=4063515130 :=
  takeStep (p:=41) (by decide) v12 c13 rfl (by decide) (by decide) rfl

private def ps14 : List ℕ := 43::ps13
private theorem c14 : F ps13 651305815=94500331 := by decide +kernel
private theorem v14 : F ps14 28006150079=3969014799 :=
  takeStep (p:=43) (by decide) v13 c14 rfl (by decide) (by decide) rfl

private def ps15 : List ℕ := 47::ps14
private theorem c15 : F ps14 595875533=84447096 := by decide +kernel
private theorem v15 : F ps15 28006150079=3884567703 :=
  takeStep (p:=47) (by decide) v14 c15 rfl (by decide) (by decide) rfl

private def ps16 : List ℕ := 53::ps15
private theorem c16 : F ps15 528417926=73293780 := by decide +kernel
private theorem v16 : F ps16 28006150079=3811273923 :=
  takeStep (p:=53) (by decide) v15 c16 rfl (by decide) (by decide) rfl

private def ps17 : List ℕ := 59::ps16
private theorem c17 : F ps16 474680509=64598051 := by decide +kernel
private theorem v17 : F ps17 28006150079=3746675872 :=
  takeStep (p:=59) (by decide) v16 c17 rfl (by decide) (by decide) rfl

private def ps18 : List ℕ := 61::ps17
private theorem c18 : F ps17 459117214=61421253 := by decide +kernel
private theorem v18 : F ps18 28006150079=3685254619 :=
  takeStep (p:=61) (by decide) v17 c18 rfl (by decide) (by decide) rfl

private def ps19 : List ℕ := 67::ps18
private theorem c19 : F ps18 418002239=55004334 := by decide +kernel
private theorem v19 : F ps19 28006150079=3630250285 :=
  takeStep (p:=67) (by decide) v18 c19 rfl (by decide) (by decide) rfl

private def ps20 : List ℕ := 71::ps19
private theorem c20 : F ps19 394452818=51131007 := by decide +kernel
private theorem v20 : F ps20 28006150079=3579119278 :=
  takeStep (p:=71) (by decide) v19 c20 rfl (by decide) (by decide) rfl

private def ps21 : List ℕ := 73::ps20
private theorem c21 : F ps20 383645891=49029788 := by decide +kernel
private theorem v21 : F ps21 28006150079=3530089490 :=
  takeStep (p:=73) (by decide) v20 c21 rfl (by decide) (by decide) rfl

private def ps22 : List ℕ := 79::ps21
private theorem c22 : F ps21 354508228=44685355 := by decide +kernel
private theorem v22 : F ps22 28006150079=3485404135 :=
  takeStep (p:=79) (by decide) v21 c22 rfl (by decide) (by decide) rfl

private def ps23 : List ℕ := 83::ps22
private theorem c23 : F ps22 337423494=41993213 := by decide +kernel
private theorem v23 : F ps23 28006150079=3443410922 :=
  takeStep (p:=83) (by decide) v22 c23 rfl (by decide) (by decide) rfl

private def ps24 : List ℕ := 89::ps23
private theorem c24 : F ps23 314675843=38689986 := by decide +kernel
private theorem v24 : F ps24 28006150079=3404720936 :=
  takeStep (p:=89) (by decide) v23 c24 rfl (by decide) (by decide) rfl

private def ps25 : List ℕ := 97::ps24
private theorem c25 : F ps24 288723196=35099558 := by decide +kernel
private theorem v25 : F ps25 28006150079=3369621378 :=
  takeStep (p:=97) (by decide) v24 c25 rfl (by decide) (by decide) rfl

private def ps26 : List ℕ := 101::ps25
private theorem c26 : F ps25 277288614=33361194 := by decide +kernel
private theorem v26 : F ps26 28006150079=3336260184 :=
  takeStep (p:=101) (by decide) v25 c26 rfl (by decide) (by decide) rfl

private def ps27 : List ℕ := 103::ps26
private theorem c27 : F ps26 271904369=32388666 := by decide +kernel
private theorem v27 : F ps27 28006150079=3303871518 :=
  takeStep (p:=103) (by decide) v26 c27 rfl (by decide) (by decide) rfl

private def ps28 : List ℕ := 107::ps27
private theorem c28 : F ps27 261739720=30874184 := by decide +kernel
private theorem v28 : F ps28 28006150079=3272997334 :=
  takeStep (p:=107) (by decide) v27 c28 rfl (by decide) (by decide) rfl

private def ps29 : List ℕ := 109::ps28
private theorem c29 : F ps28 256937156=30023400 := by decide +kernel
private theorem v29 : F ps29 28006150079=3242973934 :=
  takeStep (p:=109) (by decide) v28 c29 rfl (by decide) (by decide) rfl

private def ps30 : List ℕ := 113::ps29
private theorem c30 : F ps29 247842036=28693756 := by decide +kernel
private theorem v30 : F ps30 28006150079=3214280178 :=
  takeStep (p:=113) (by decide) v29 c30 rfl (by decide) (by decide) rfl

private def ps31 : List ℕ := 127::ps30
private theorem c31 : F ps30 220520866=25303141 := by decide +kernel
private theorem v31 : F ps31 28006150079=3188977037 :=
  takeStep (p:=127) (by decide) v30 c31 rfl (by decide) (by decide) rfl

private def ps32 : List ℕ := 131::ps31
private theorem c32 : F ps31 213787405=24336421 := by decide +kernel
private theorem v32 : F ps32 28006150079=3164640616 :=
  takeStep (p:=131) (by decide) v31 c32 rfl (by decide) (by decide) rfl

private def ps33 : List ℕ := 137::ps32
private theorem c33 : F ps32 204424453=23091971 := by decide +kernel
private theorem v33 : F ps33 28006150079=3141548645 :=
  takeStep (p:=137) (by decide) v32 c33 rfl (by decide) (by decide) rfl

private def ps34 : List ℕ := 139::ps33
private theorem c34 : F ps33 201483094=22592917 := by decide +kernel
private theorem v34 : F ps34 28006150079=3118955728 :=
  takeStep (p:=139) (by decide) v33 c34 rfl (by decide) (by decide) rfl

private def ps35 : List ℕ := 149::ps34
private theorem c35 : F ps34 187960738=20924324 := by decide +kernel
private theorem v35 : F ps35 28006150079=3098031404 :=
  takeStep (p:=149) (by decide) v34 c35 rfl (by decide) (by decide) rfl

private def ps36 : List ℕ := 151::ps35
private theorem c36 : F ps35 185471192=20508307 := by decide +kernel
private theorem v36 : F ps36 28006150079=3077523097 :=
  takeStep (p:=151) (by decide) v35 c36 rfl (by decide) (by decide) rfl

private def ps37 : List ℕ := 157::ps36
private theorem c37 : F ps36 178383121=19593639 := by decide +kernel
private theorem v37 : F ps37 28006150079=3057929458 :=
  takeStep (p:=157) (by decide) v36 c37 rfl (by decide) (by decide) rfl

private def ps38 : List ℕ := 163::ps37
private theorem c38 : F ps37 171816871=18752257 := by decide +kernel
private theorem v38 : F ps38 28006150079=3039177201 :=
  takeStep (p:=163) (by decide) v37 c38 rfl (by decide) (by decide) rfl

private def ps39 : List ℕ := 167::ps38
private theorem c39 : F ps38 167701497=18191012 := by decide +kernel
private theorem v39 : F ps39 28006150079=3020986189 :=
  takeStep (p:=167) (by decide) v38 c39 rfl (by decide) (by decide) rfl

private def ps40 : List ℕ := 173::ps39
private theorem c40 : F ps39 161885260=17455378 := by decide +kernel
private theorem v40 : F ps40 28006150079=3003530811 :=
  takeStep (p:=173) (by decide) v39 c40 rfl (by decide) (by decide) rfl

private def ps41 : List ℕ := 179::ps40
private theorem c41 : F ps40 156458938=16773373 := by decide +kernel
private theorem v41 : F ps41 28006150079=2986757438 :=
  takeStep (p:=179) (by decide) v40 c41 rfl (by decide) (by decide) rfl

private def ps42 : List ℕ := 181::ps41
private theorem c42 : F ps41 154730110=16496023 := by decide +kernel
private theorem v42 : F ps42 28006150079=2970261415 :=
  takeStep (p:=181) (by decide) v41 c42 rfl (by decide) (by decide) rfl

private def ps43 : List ℕ := 191::ps42
private theorem c43 : F ps42 146629058=15547128 := by decide +kernel
private theorem v43 : F ps43 28006150079=2954714287 :=
  takeStep (p:=191) (by decide) v42 c43 rfl (by decide) (by decide) rfl

private def ps44 : List ℕ := 193::ps43
private theorem c44 : F ps43 145109585=15306387 := by decide +kernel
private theorem v44 : F ps44 28006150079=2939407900 :=
  takeStep (p:=193) (by decide) v43 c44 rfl (by decide) (by decide) rfl

private def ps45 : List ℕ := 197::ps44
private theorem c45 : F ps44 142163198=14919037 := by decide +kernel
private theorem v45 : F ps45 28006150079=2924488863 :=
  takeStep (p:=197) (by decide) v44 c45 rfl (by decide) (by decide) rfl

private def ps46 : List ℕ := 199::ps45
private theorem c46 : F ps45 140734422=14695313 := by decide +kernel
private theorem v46 : F ps46 28006150079=2909793550 :=
  takeStep (p:=199) (by decide) v45 c46 rfl (by decide) (by decide) rfl

private def ps47 : List ℕ := 211::ps46
private theorem c47 : F ps46 132730569=13791721 := by decide +kernel
private theorem v47 : F ps47 28006150079=2896001829 :=
  takeStep (p:=211) (by decide) v46 c47 rfl (by decide) (by decide) rfl

private def ps48 : List ℕ := 223::ps47
private theorem c48 : F ps47 125588116=12989710 := by decide +kernel
private theorem v48 : F ps48 28006150079=2883012119 :=
  takeStep (p:=223) (by decide) v47 c48 rfl (by decide) (by decide) rfl

private def ps49 : List ℕ := 227::ps48
private theorem c49 : F ps48 123375110=12705130 := by decide +kernel
private theorem v49 : F ps49 28006150079=2870306989 :=
  takeStep (p:=227) (by decide) v48 c49 rfl (by decide) (by decide) rfl

private def ps50 : List ℕ := 229::ps49
private theorem c50 : F ps49 122297598=12540155 := by decide +kernel
private theorem v50 : F ps50 28006150079=2857766834 :=
  takeStep (p:=229) (by decide) v49 c50 rfl (by decide) (by decide) rfl

private def ps51 : List ℕ := 233::ps50
private theorem c51 : F ps50 120198069=12272781 := by decide +kernel
private theorem v51 : F ps51 28006150079=2845494053 :=
  takeStep (p:=233) (by decide) v50 c51 rfl (by decide) (by decide) rfl

private def ps52 : List ℕ := 239::ps51
private theorem c52 : F ps51 117180544=11915255 := by decide +kernel
private theorem v52 : F ps52 28006150079=2833578798 :=
  takeStep (p:=239) (by decide) v51 c52 rfl (by decide) (by decide) rfl

private def ps53 : List ℕ := 241::ps52
private theorem c53 : F ps52 116208091=11768576 := by decide +kernel
private theorem v53 : F ps53 28006150079=2821810222 :=
  takeStep (p:=241) (by decide) v52 c53 rfl (by decide) (by decide) rfl

private def ps54 : List ℕ := 251::ps53
private theorem c54 : F ps53 111578287=11255216 := by decide +kernel
private theorem v54 : F ps54 28006150079=2810555006 :=
  takeStep (p:=251) (by decide) v53 c54 rfl (by decide) (by decide) rfl

private def ps55 : List ℕ := 257::ps54
private theorem c55 : F ps54 108973346=10950644 := by decide +kernel
private theorem v55 : F ps55 28006150079=2799604362 :=
  takeStep (p:=257) (by decide) v54 c55 rfl (by decide) (by decide) rfl

private def ps56 : List ℕ := 263::ps55
private theorem c56 : F ps55 106487262=10661186 := by decide +kernel
private theorem v56 : F ps56 28006150079=2788943176 :=
  takeStep (p:=263) (by decide) v55 c56 rfl (by decide) (by decide) rfl

private def ps57 : List ℕ := 269::ps56
private theorem c57 : F ps56 104112082=10385835 := by decide +kernel
private theorem v57 : F ps57 28006150079=2778557341 :=
  takeStep (p:=269) (by decide) v56 c57 rfl (by decide) (by decide) rfl

private def ps58 : List ℕ := 271::ps57
private theorem c58 : F ps57 103343727=10272630 := by decide +kernel
private theorem v58 : F ps58 28006150079=2768284711 :=
  takeStep (p:=271) (by decide) v57 c58 rfl (by decide) (by decide) rfl

private def ps59 : List ℕ := 277::ps58
private theorem c59 : F ps58 101105234=10015026 := by decide +kernel
private theorem v59 : F ps59 28006150079=2758269685 :=
  takeStep (p:=277) (by decide) v58 c59 rfl (by decide) (by decide) rfl

private def ps60 : List ℕ := 281::ps59
private theorem c60 : F ps59 99666014=9838706 := by decide +kernel
private theorem v60 : F ps60 28006150079=2748430979 :=
  takeStep (p:=281) (by decide) v59 c60 rfl (by decide) (by decide) rfl

private def ps61 : List ℕ := 283::ps60
private theorem c61 : F ps60 98961661=9736144 := by decide +kernel
private theorem v61 : F ps61 28006150079=2738694835 :=
  takeStep (p:=283) (by decide) v60 c61 rfl (by decide) (by decide) rfl

private def ps62 : List ℕ := 293::ps61
private theorem c62 : F ps61 95584129=9372988 := by decide +kernel
private theorem v62 : F ps62 28006150079=2729321847 :=
  takeStep (p:=293) (by decide) v61 c62 rfl (by decide) (by decide) rfl

private def ps63 : List ℕ := 307::ps62
private theorem c63 : F ps62 91225244=8917647 := by decide +kernel
private theorem v63 : F ps63 28006150079=2720404200 :=
  takeStep (p:=307) (by decide) v62 c63 rfl (by decide) (by decide) rfl

private def ps64 : List ℕ := 311::ps63
private theorem c64 : F ps63 90051929=8775977 := by decide +kernel
private theorem v64 : F ps64 28006150079=2711628223 :=
  takeStep (p:=311) (by decide) v63 c64 rfl (by decide) (by decide) rfl

private def ps65 : List ℕ := 313::ps64
private theorem c65 : F ps64 89476517=8693497 := by decide +kernel
private theorem v65 : F ps65 28006150079=2702934726 :=
  takeStep (p:=313) (by decide) v64 c65 rfl (by decide) (by decide) rfl

private def ps66 : List ℕ := 317::ps65
private theorem c66 : F ps65 88347476=8558089 := by decide +kernel
private theorem v66 : F ps66 28006150079=2694376637 :=
  takeStep (p:=317) (by decide) v65 c66 rfl (by decide) (by decide) rfl

private def ps67 : List ℕ := 331::ps66
private theorem c67 : F ps66 84610725=8172587 := by decide +kernel
private theorem v67 : F ps67 28006150079=2686204050 :=
  takeStep (p:=331) (by decide) v66 c67 rfl (by decide) (by decide) rfl

private def ps68 : List ℕ := 337::ps67
private theorem c68 : F ps67 83104302=8004472 := by decide +kernel
private theorem v68 : F ps68 28006150079=2678199578 :=
  takeStep (p:=337) (by decide) v67 c68 rfl (by decide) (by decide) rfl

private def ps69 : List ℕ := 347::ps68
private theorem c69 : F ps68 80709366=7752494 := by decide +kernel
private theorem v69 : F ps69 28006150079=2670447084 :=
  takeStep (p:=347) (by decide) v68 c69 rfl (by decide) (by decide) rfl

private def ps70 : List ℕ := 349::ps69
private theorem c70 : F ps69 80246848=7687118 := by decide +kernel
private theorem v70 : F ps70 28006150079=2662759966 :=
  takeStep (p:=349) (by decide) v69 c70 rfl (by decide) (by decide) rfl

private def ps71 : List ℕ := 353::ps70
private theorem c71 : F ps70 79337535=7579573 := by decide +kernel
private theorem v71 : F ps71 28006150079=2655180393 :=
  takeStep (p:=353) (by decide) v70 c71 rfl (by decide) (by decide) rfl

private def ps72 : List ℕ := 359::ps71
private theorem c72 : F ps71 78011560=7433179 := by decide +kernel
private theorem v72 : F ps72 28006150079=2647747214 :=
  takeStep (p:=359) (by decide) v71 c72 rfl (by decide) (by decide) rfl

private def ps73 : List ℕ := 367::ps72
private theorem c73 : F ps72 76311035=7252325 := by decide +kernel
private theorem v73 : F ps73 28006150079=2640494889 :=
  takeStep (p:=367) (by decide) v72 c73 rfl (by decide) (by decide) rfl

private def ps74 : List ℕ := 373::ps73
private theorem c74 : F ps73 75083512=7117438 := by decide +kernel
private theorem v74 : F ps74 28006150079=2633377451 :=
  takeStep (p:=373) (by decide) v73 c74 rfl (by decide) (by decide) rfl

private def ps75 : List ℕ := 379::ps74
private theorem c75 : F ps74 73894855=6987116 := by decide +kernel
private theorem v75 : F ps75 28006150079=2626390335 :=
  takeStep (p:=379) (by decide) v74 c75 rfl (by decide) (by decide) rfl

private def ps76 : List ℕ := 383::ps75
private theorem c76 : F ps75 73123107=6896778 := by decide +kernel
private theorem v76 : F ps76 28006150079=2619493557 :=
  takeStep (p:=383) (by decide) v75 c76 rfl (by decide) (by decide) rfl

private def ps77 : List ℕ := 389::ps76
private theorem c77 : F ps76 71995244=6773610 := by decide +kernel
private theorem v77 : F ps77 28006150079=2612719947 :=
  takeStep (p:=389) (by decide) v76 c77 rfl (by decide) (by decide) rfl

private def ps78 : List ℕ := 397::ps77
private theorem c78 : F ps77 70544458=6620994 := by decide +kernel
private theorem v78 : F ps78 28006150079=2606098953 :=
  takeStep (p:=397) (by decide) v77 c78 rfl (by decide) (by decide) rfl

private def ps79 : List ℕ := 401::ps78
private theorem c79 : F ps78 69840773=6539137 := by decide +kernel
private theorem v79 : F ps79 28006150079=2599559816 :=
  takeStep (p:=401) (by decide) v78 c79 rfl (by decide) (by decide) rfl

private def ps80 : List ℕ := 409::ps79
private theorem c80 : F ps79 68474694=6395895 := by decide +kernel
private theorem v80 : F ps80 28006150079=2593163921 :=
  takeStep (p:=409) (by decide) v79 c80 rfl (by decide) (by decide) rfl

private def ps81 : List ℕ := 419::ps80
private theorem c81 : F ps80 66840453=6228506 := by decide +kernel
private theorem v81 : F ps81 28006150079=2586935415 :=
  takeStep (p:=419) (by decide) v80 c81 rfl (by decide) (by decide) rfl

private def ps82 : List ℕ := 421::ps81
private theorem c82 : F ps81 66522921=6184478 := by decide +kernel
private theorem v82 : F ps82 28006150079=2580750937 :=
  takeStep (p:=421) (by decide) v81 c82 rfl (by decide) (by decide) rfl

private def ps83 : List ℕ := 431::ps82
private theorem c83 : F ps82 64979466=6026834 := by decide +kernel
private theorem v83 : F ps83 28006150079=2574724103 :=
  takeStep (p:=431) (by decide) v82 c83 rfl (by decide) (by decide) rfl

private def ps84 : List ℕ := 433::ps83
private theorem c84 : F ps83 64679330=5985251 := by decide +kernel
private theorem v84 : F ps84 28006150079=2568738852 :=
  takeStep (p:=433) (by decide) v83 c84 rfl (by decide) (by decide) rfl

private def ps85 : List ℕ := 439::ps84
private theorem c85 : F ps84 63795330=5889965 := by decide +kernel
private theorem v85 : F ps85 28006150079=2562848887 :=
  takeStep (p:=439) (by decide) v84 c85 rfl (by decide) (by decide) rfl

private def ps86 : List ℕ := 443::ps85
private theorem c86 : F ps85 63219300=5823527 := by decide +kernel
private theorem v86 : F ps86 28006150079=2557025360 :=
  takeStep (p:=443) (by decide) v85 c86 rfl (by decide) (by decide) rfl

private def ps87 : List ℕ := 449::ps86
private theorem c87 : F ps86 62374499=5732649 := by decide +kernel
private theorem v87 : F ps87 28006150079=2551292711 :=
  takeStep (p:=449) (by decide) v86 c87 rfl (by decide) (by decide) rfl

private def ps88 : List ℕ := 457::ps87
private theorem c88 : F ps87 61282604=5619631 := by decide +kernel
private theorem v88 : F ps88 28006150079=2545673080 :=
  takeStep (p:=457) (by decide) v87 c88 rfl (by decide) (by decide) rfl

private def ps89 : List ℕ := 461::ps88
private theorem c89 : F ps88 60750867=5558480 := by decide +kernel
private theorem v89 : F ps89 28006150079=2540114600 :=
  takeStep (p:=461) (by decide) v88 c89 rfl (by decide) (by decide) rfl

private def ps90 : List ℕ := 463::ps89
private theorem c90 : F ps89 60488445=5522271 := by decide +kernel
private theorem v90 : F ps90 28006150079=2534592329 :=
  takeStep (p:=463) (by decide) v89 c90 rfl (by decide) (by decide) rfl

private def ps91 : List ℕ := 467::ps90
private theorem c91 : F ps90 59970342=5462821 := by decide +kernel
private theorem v91 : F ps91 28006150079=2529129508 :=
  takeStep (p:=467) (by decide) v90 c91 rfl (by decide) (by decide) rfl

private def ps92 : List ℕ := 479::ps91
private theorem c92 : F ps91 58467954=5314108 := by decide +kernel
private theorem v92 : F ps92 28006150079=2523815400 :=
  takeStep (p:=479) (by decide) v91 c92 rfl (by decide) (by decide) rfl

private def ps93 : List ℕ := 487::ps92
private theorem c93 : F ps92 57507495=5215419 := by decide +kernel
private theorem v93 : F ps93 28006150079=2518599981 :=
  takeStep (p:=487) (by decide) v92 c93 rfl (by decide) (by decide) rfl

private def ps94 : List ℕ := 491::ps93
private theorem c94 : F ps93 57039002=5161899 := by decide +kernel
private theorem v94 : F ps94 28006150079=2513438082 :=
  takeStep (p:=491) (by decide) v93 c94 rfl (by decide) (by decide) rfl

private def ps95 : List ℕ := 499::ps94
private theorem c95 : F ps94 56124549=5068205 := by decide +kernel
private theorem v95 : F ps95 28006150079=2508369877 :=
  takeStep (p:=499) (by decide) v94 c95 rfl (by decide) (by decide) rfl

private def ps96 : List ℕ := 503::ps95
private theorem c96 : F ps95 55678230=5017298 := by decide +kernel
private theorem v96 : F ps96 28006150079=2503352579 :=
  takeStep (p:=503) (by decide) v95 c96 rfl (by decide) (by decide) rfl

private def ps97 : List ℕ := 509::ps96
private theorem c97 : F ps96 55021905=4947645 := by decide +kernel
private theorem v97 : F ps97 28006150079=2498404934 :=
  takeStep (p:=509) (by decide) v96 c97 rfl (by decide) (by decide) rfl

private def ps98 : List ℕ := 521::ps97
private theorem c98 : F ps97 53754606=4823367 := by decide +kernel
private theorem v98 : F ps98 28006150079=2493581567 :=
  takeStep (p:=521) (by decide) v97 c98 rfl (by decide) (by decide) rfl

private def ps99 : List ℕ := 523::ps98
private theorem c99 : F ps98 53549044=4795130 := by decide +kernel
private theorem v99 : F ps99 28006150079=2488786437 :=
  takeStep (p:=523) (by decide) v98 c99 rfl (by decide) (by decide) rfl

private def ps100 : List ℕ := 541::ps99
private theorem c100 : F ps99 51767375=4625563 := by decide +kernel
private theorem v100 : F ps100 28006150079=2484160874 :=
  takeStep (p:=541) (by decide) v99 c100 rfl (by decide) (by decide) rfl

private def ps101 : List ℕ := 547::ps100
private theorem c101 : F ps100 51199543=4565581 := by decide +kernel
private theorem v101 : F ps101 28006150079=2479595293 :=
  takeStep (p:=547) (by decide) v100 c101 rfl (by decide) (by decide) rfl

private def ps102 : List ℕ := 557::ps101
private theorem c102 : F ps101 50280341=4474483 := by decide +kernel
private theorem v102 : F ps102 28006150079=2475120810 :=
  takeStep (p:=557) (by decide) v101 c102 rfl (by decide) (by decide) rfl

private def ps103 : List ℕ := 563::ps102
private theorem c103 : F ps102 49744493=4418008 := by decide +kernel
private theorem v103 : F ps103 28006150079=2470702802 :=
  takeStep (p:=563) (by decide) v102 c103 rfl (by decide) (by decide) rfl

private def ps104 : List ℕ := 569::ps103
private theorem c104 : F ps103 49219947=4362790 := by decide +kernel
private theorem v104 : F ps104 28006150079=2466340012 :=
  takeStep (p:=569) (by decide) v103 c104 rfl (by decide) (by decide) rfl

private def ps105 : List ℕ := 571::ps104
private theorem c105 : F ps104 49047548=4339115 := by decide +kernel
private theorem v105 : F ps105 28006150079=2462000897 :=
  takeStep (p:=571) (by decide) v104 c105 rfl (by decide) (by decide) rfl

private def ps106 : List ℕ := 577::ps105
private theorem c106 : F ps105 48537521=4285600 := by decide +kernel
private theorem v106 : F ps106 28006150079=2457715297 :=
  takeStep (p:=577) (by decide) v105 c106 rfl (by decide) (by decide) rfl

private def ps107 : List ℕ := 587::ps106
private theorem c107 : F ps106 47710647=4204215 := by decide +kernel
private theorem v107 : F ps107 28006150079=2453511082 :=
  takeStep (p:=587) (by decide) v106 c107 rfl (by decide) (by decide) rfl

private def ps108 : List ℕ := 593::ps107
private theorem c108 : F ps107 47227909=4153747 := by decide +kernel
private theorem v108 : F ps108 28006150079=2449357335 :=
  takeStep (p:=593) (by decide) v107 c108 rfl (by decide) (by decide) rfl

private def ps109 : List ℕ := 599::ps108
private theorem c109 : F ps108 46754841=4104246 := by decide +kernel
private theorem v109 : F ps109 28006150079=2445253089 :=
  takeStep (p:=599) (by decide) v108 c109 rfl (by decide) (by decide) rfl

private def ps110 : List ℕ := 601::ps109
private theorem c110 : F ps109 46599251=4082930 := by decide +kernel
private theorem v110 : F ps110 28006150079=2441170159 :=
  takeStep (p:=601) (by decide) v109 c110 rfl (by decide) (by decide) rfl

private def ps111 : List ℕ := 607::ps110
private theorem c111 : F ps110 46138632=4034904 := by decide +kernel
private theorem v111 : F ps111 28006150079=2437135255 :=
  takeStep (p:=607) (by decide) v110 c111 rfl (by decide) (by decide) rfl

private def ps112 : List ℕ := 613::ps111
private theorem c112 : F ps111 45687031=3987840 := by decide +kernel
private theorem v112 : F ps112 28006150079=2433147415 :=
  takeStep (p:=613) (by decide) v111 c112 rfl (by decide) (by decide) rfl

private def ps113 : List ℕ := 617::ps112
private theorem c113 : F ps112 45390842=3954577 := by decide +kernel
private theorem v113 : F ps113 28006150079=2429192838 :=
  takeStep (p:=617) (by decide) v112 c113 rfl (by decide) (by decide) rfl

private def ps114 : List ℕ := 619::ps113
private theorem c114 : F ps113 45244184=3934553 := by decide +kernel
private theorem v114 : F ps114 28006150079=2425258285 :=
  takeStep (p:=619) (by decide) v113 c114 rfl (by decide) (by decide) rfl

private def ps115 : List ℕ := 631::ps114
private theorem c115 : F ps114 44383756=3852147 := by decide +kernel
private theorem v115 : F ps115 28006150079=2421406138 :=
  takeStep (p:=631) (by decide) v114 c115 rfl (by decide) (by decide) rfl

private def ps116 : List ℕ := 641::ps115
private theorem c116 : F ps115 43691341=3784858 := by decide +kernel
private theorem v116 : F ps116 28006150079=2417621280 :=
  takeStep (p:=641) (by decide) v115 c116 rfl (by decide) (by decide) rfl

private def ps117 : List ℕ := 643::ps116
private theorem c117 : F ps116 43555443=3766396 := by decide +kernel
private theorem v117 : F ps117 28006150079=2413854884 :=
  takeStep (p:=643) (by decide) v116 c117 rfl (by decide) (by decide) rfl

private def ps118 : List ℕ := 647::ps117
private theorem c118 : F ps117 43286167=3736300 := by decide +kernel
private theorem v118 : F ps118 28006150079=2410118584 :=
  takeStep (p:=647) (by decide) v117 c118 rfl (by decide) (by decide) rfl

private def ps119 : List ℕ := 653::ps118
private theorem c119 : F ps118 42888438=3695191 := by decide +kernel
private theorem v119 : F ps119 28006150079=2406423393 :=
  takeStep (p:=653) (by decide) v118 c119 rfl (by decide) (by decide) rfl

private def ps120 : List ℕ := 659::ps119
private theorem c120 : F ps119 42497951=3654931 := by decide +kernel
private theorem v120 : F ps120 28006150079=2402768462 :=
  takeStep (p:=659) (by decide) v119 c120 rfl (by decide) (by decide) rfl

private def ps121 : List ℕ := 661::ps120
private theorem c121 : F ps120 42369364=3637468 := by decide +kernel
private theorem v121 : F ps121 28006150079=2399130994 :=
  takeStep (p:=661) (by decide) v120 c121 rfl (by decide) (by decide) rfl

private def ps122 : List ℕ := 673::ps121
private theorem c122 : F ps121 41613893=3565794 := by decide +kernel
private theorem v122 : F ps122 28006150079=2395565200 :=
  takeStep (p:=673) (by decide) v121 c122 rfl (by decide) (by decide) rfl

private def ps123 : List ℕ := 677::ps122
private theorem c123 : F ps122 41368020=3538527 := by decide +kernel
private theorem v123 : F ps123 28006150079=2392026673 :=
  takeStep (p:=677) (by decide) v122 c123 rfl (by decide) (by decide) rfl

private def ps124 : List ℕ := 683::ps123
private theorem c124 : F ps123 41004612=3501114 := by decide +kernel
private theorem v124 : F ps124 28006150079=2388525559 :=
  takeStep (p:=683) (by decide) v123 c124 rfl (by decide) (by decide) rfl

private def ps125 : List ℕ := 691::ps124
private theorem c125 : F ps124 40529884=3454321 := by decide +kernel
private theorem v125 : F ps125 28006150079=2385071238 :=
  takeStep (p:=691) (by decide) v124 c125 rfl (by decide) (by decide) rfl

private def ps126 : List ℕ := 701::ps125
private theorem c126 : F ps125 39951711=3398814 := by decide +kernel
private theorem v126 : F ps126 28006150079=2381672424 :=
  takeStep (p:=701) (by decide) v125 c126 rfl (by decide) (by decide) rfl

private def ps127 : List ℕ := 709::ps126
private theorem c127 : F ps126 39500916=3354485 := by decide +kernel
private theorem v127 : F ps127 28006150079=2378317939 :=
  takeStep (p:=709) (by decide) v126 c127 rfl (by decide) (by decide) rfl

private def ps128 : List ℕ := 719::ps127
private theorem c128 : F ps127 38951530=3301873 := by decide +kernel
private theorem v128 : F ps128 28006150079=2375016066 :=
  takeStep (p:=719) (by decide) v127 c128 rfl (by decide) (by decide) rfl

private def ps129 : List ℕ := 727::ps128
private theorem c129 : F ps128 38522902=3259787 := by decide +kernel
private theorem v129 : F ps129 28006150079=2371756279 :=
  takeStep (p:=727) (by decide) v128 c129 rfl (by decide) (by decide) rfl

private def ps130 : List ℕ := 733::ps129
private theorem c130 : F ps129 38207571=3227551 := by decide +kernel
private theorem v130 : F ps130 28006150079=2368528728 :=
  takeStep (p:=733) (by decide) v129 c130 rfl (by decide) (by decide) rfl

private def ps131 : List ℕ := 739::ps130
private theorem c131 : F ps130 37897361=3195864 := by decide +kernel
private theorem v131 : F ps131 28006150079=2365332864 :=
  takeStep (p:=739) (by decide) v130 c131 rfl (by decide) (by decide) rfl

private def ps132 : List ℕ := 743::ps131
private theorem c132 : F ps131 37693337=3173391 := by decide +kernel
private theorem v132 : F ps132 28006150079=2362159473 :=
  takeStep (p:=743) (by decide) v131 c132 rfl (by decide) (by decide) rfl

private def ps133 : List ℕ := 751::ps132
private theorem c133 : F ps132 37291811=3134177 := by decide +kernel
private theorem v133 : F ps133 28006150079=2359025296 :=
  takeStep (p:=751) (by decide) v132 c133 rfl (by decide) (by decide) rfl

private def ps134 : List ℕ := 757::ps133
private theorem c134 : F ps133 36996235=3104091 := by decide +kernel
private theorem v134 : F ps134 28006150079=2355921205 :=
  takeStep (p:=757) (by decide) v133 c134 rfl (by decide) (by decide) rfl

private def ps135 : List ℕ := 761::ps134
private theorem c135 : F ps134 36801774=3082746 := by decide +kernel
private theorem v135 : F ps135 28006150079=2352838459 :=
  takeStep (p:=761) (by decide) v134 c135 rfl (by decide) (by decide) rfl

private def ps136 : List ℕ := 769::ps135
private theorem c136 : F ps135 36418920=3045494 := by decide +kernel
private theorem v136 : F ps136 28006150079=2349792965 :=
  takeStep (p:=769) (by decide) v135 c136 rfl (by decide) (by decide) rfl

private def ps137 : List ℕ := 773::ps136
private theorem c137 : F ps136 36230465=3024799 := by decide +kernel
private theorem v137 : F ps137 28006150079=2346768166 :=
  takeStep (p:=773) (by decide) v136 c137 rfl (by decide) (by decide) rfl

private def ps138 : List ℕ := 787::ps137
private theorem c138 : F ps137 35585959=2965712 := by decide +kernel
private theorem v138 : F ps138 28006150079=2343802454 :=
  takeStep (p:=787) (by decide) v137 c138 rfl (by decide) (by decide) rfl

private def ps139 : List ℕ := 797::ps138
private theorem c139 : F ps138 35139460=2923520 := by decide +kernel
private theorem v139 : F ps139 28006150079=2340878934 :=
  takeStep (p:=797) (by decide) v138 c139 rfl (by decide) (by decide) rfl

private def ps140 : List ℕ := 809::ps139
private theorem c140 : F ps139 34618232=2875260 := by decide +kernel
private theorem v140 : F ps140 28006150079=2338003674 :=
  takeStep (p:=809) (by decide) v139 c140 rfl (by decide) (by decide) rfl

private def ps141 : List ℕ := 811::ps140
private theorem c141 : F ps140 34532860=2863757 := by decide +kernel
private theorem v141 : F ps141 28006150079=2335139917 :=
  takeStep (p:=811) (by decide) v140 c141 rfl (by decide) (by decide) rfl

private def ps142 : List ℕ := 821::ps141
private theorem c142 : F ps141 34112241=2824202 := by decide +kernel
private theorem v142 : F ps142 28006150079=2332315715 :=
  takeStep (p:=821) (by decide) v141 c142 rfl (by decide) (by decide) rfl

private def ps143 : List ℕ := 823::ps142
private theorem c143 : F ps142 34029343=2813039 := by decide +kernel
private theorem v143 : F ps143 28006150079=2329502676 :=
  takeStep (p:=823) (by decide) v142 c143 rfl (by decide) (by decide) rfl

private def ps144 : List ℕ := 827::ps143
private theorem c144 : F ps143 33864752=2795138 := by decide +kernel
private theorem v144 : F ps144 28006150079=2326707538 :=
  takeStep (p:=827) (by decide) v143 c144 rfl (by decide) (by decide) rfl

private def ps145 : List ℕ := 829::ps144
private theorem c145 : F ps144 33783051=2784173 := by decide +kernel
private theorem v145 : F ps145 28006150079=2323923365 :=
  takeStep (p:=829) (by decide) v144 c145 rfl (by decide) (by decide) rfl

private def ps146 : List ℕ := 839::ps145
private theorem c146 : F ps145 33380393=2746438 := by decide +kernel
private theorem v146 : F ps146 28006150079=2321176927 :=
  takeStep (p:=839) (by decide) v145 c146 rfl (by decide) (by decide) rfl

private def ps147 : List ℕ := 853::ps146
private theorem c147 : F ps146 32832532=2696694 := by decide +kernel
private theorem v147 : F ps147 28006150079=2318480233 :=
  takeStep (p:=853) (by decide) v146 c147 rfl (by decide) (by decide) rfl

private def ps148 : List ℕ := 857::ps147
private theorem c148 : F ps147 32679288=2680053 := by decide +kernel
private theorem v148 : F ps148 28006150079=2315800180 :=
  takeStep (p:=857) (by decide) v147 c148 rfl (by decide) (by decide) rfl

private def ps149 : List ℕ := 859::ps148
private theorem c149 : F ps148 32603201=2669864 := by decide +kernel
private theorem v149 : F ps149 28006150079=2313130316 :=
  takeStep (p:=859) (by decide) v148 c149 rfl (by decide) (by decide) rfl

private def ps150 : List ℕ := 863::ps149
private theorem c150 : F ps149 32452085=2653413 := by decide +kernel
private theorem v150 : F ps150 28006150079=2310476903 :=
  takeStep (p:=863) (by decide) v149 c150 rfl (by decide) (by decide) rfl

private def ps151 : List ℕ := 877::ps150
private theorem c151 : F ps150 31934036=2606695 := by decide +kernel
private theorem v151 : F ps151 28006150079=2307870208 :=
  takeStep (p:=877) (by decide) v150 c151 rfl (by decide) (by decide) rfl

private def ps152 : List ℕ := 881::ps151
private theorem c152 : F ps151 31789046=2590959 := by decide +kernel
private theorem v152 : F ps152 28006150079=2305279249 :=
  takeStep (p:=881) (by decide) v151 c152 rfl (by decide) (by decide) rfl

private def ps153 : List ℕ := 883::ps152
private theorem c153 : F ps152 31717044=2581344 := by decide +kernel
private theorem v153 : F ps153 28006150079=2302697905 :=
  takeStep (p:=883) (by decide) v152 c153 rfl (by decide) (by decide) rfl

private def ps154 : List ℕ := 887::ps153
private theorem c154 : F ps153 31574013=2565882 := by decide +kernel
private theorem v154 : F ps154 28006150079=2300132023 :=
  takeStep (p:=887) (by decide) v153 c154 rfl (by decide) (by decide) rfl

private def ps155 : List ℕ := 907::ps154
private theorem c155 : F ps154 30877783=2504946 := by decide +kernel
private theorem v155 : F ps155 28006150079=2297627077 :=
  takeStep (p:=907) (by decide) v154 c155 rfl (by decide) (by decide) rfl

private def ps156 : List ℕ := 911::ps155
private theorem c156 : F ps155 30742206=2490304 := by decide +kernel
private theorem v156 : F ps156 28006150079=2295136773 :=
  takeStep (p:=911) (by decide) v155 c156 rfl (by decide) (by decide) rfl

private def ps157 : List ℕ := 919::ps156
private theorem c157 : F ps156 30474592=2464764 := by decide +kernel
private theorem v157 : F ps157 28006150079=2292672009 :=
  takeStep (p:=919) (by decide) v156 c157 rfl (by decide) (by decide) rfl

private def ps158 : List ℕ := 929::ps157
private theorem c158 : F ps157 30146555=2434482 := by decide +kernel
private theorem v158 : F ps158 28006150079=2290237527 :=
  takeStep (p:=929) (by decide) v157 c158 rfl (by decide) (by decide) rfl

private def ps159 : List ℕ := 937::ps158
private theorem c159 : F ps158 29889167=2410010 := by decide +kernel
private theorem v159 : F ps159 28006150079=2287827517 :=
  takeStep (p:=937) (by decide) v158 c159 rfl (by decide) (by decide) rfl

private def ps160 : List ℕ := 941::ps159
private theorem c160 : F ps159 29762114=2396329 := by decide +kernel
private theorem v160 : F ps160 28006150079=2285431188 :=
  takeStep (p:=941) (by decide) v159 c160 rfl (by decide) (by decide) rfl

private def ps161 : List ℕ := 947::ps160
private theorem c161 : F ps160 29573548=2377633 := by decide +kernel
private theorem v161 : F ps161 28006150079=2283053555 :=
  takeStep (p:=947) (by decide) v160 c161 rfl (by decide) (by decide) rfl

private def ps162 : List ℕ := 953::ps161
private theorem c162 : F ps161 29387355=2359303 := by decide +kernel
private theorem v162 : F ps162 28006150079=2280694252 :=
  takeStep (p:=953) (by decide) v161 c162 rfl (by decide) (by decide) rfl

private def ps163 : List ℕ := 967::ps162
private theorem c163 : F ps162 28961892=2321428 := by decide +kernel
private theorem v163 : F ps163 28006150079=2278372824 :=
  takeStep (p:=967) (by decide) v162 c163 rfl (by decide) (by decide) rfl

private def ps164 : List ℕ := 971::ps163
private theorem c164 : F ps163 28842585=2308616 := by decide +kernel
private theorem v164 : F ps164 28006150079=2276064208 :=
  takeStep (p:=971) (by decide) v163 c164 rfl (by decide) (by decide) rfl

private def ps165 : List ℕ := 977::ps164
private theorem c165 : F ps164 28665455=2291186 := by decide +kernel
private theorem v165 : F ps165 28006150079=2273773022 :=
  takeStep (p:=977) (by decide) v164 c165 rfl (by decide) (by decide) rfl

private def ps166 : List ℕ := 983::ps165
private theorem c166 : F ps165 28490488=2273933 := by decide +kernel
private theorem v166 : F ps166 28006150079=2271499089 :=
  takeStep (p:=983) (by decide) v165 c166 rfl (by decide) (by decide) rfl

private def ps167 : List ℕ := 991::ps166
private theorem c167 : F ps166 28260494=2252308 := by decide +kernel
private theorem v167 : F ps167 28006150079=2269246781 :=
  takeStep (p:=991) (by decide) v166 c167 rfl (by decide) (by decide) rfl

private def ps168 : List ℕ := 997::ps167
private theorem c168 : F ps167 28090421=2235592 := by decide +kernel
private theorem v168 : F ps168 28006150079=2267011189 :=
  takeStep (p:=997) (by decide) v167 c168 rfl (by decide) (by decide) rfl

private def ps169 : List ℕ := 1009::ps168
private theorem c169 : F ps168 27756342=2205672 := by decide +kernel
private theorem v169 : F ps169 28006150079=2264805517 :=
  takeStep (p:=1009) (by decide) v168 c169 rfl (by decide) (by decide) rfl

private def ps170 : List ℕ := 1013::ps169
private theorem c170 : F ps169 27646742=2193979 := by decide +kernel
private theorem v170 : F ps170 28006150079=2262611538 :=
  takeStep (p:=1013) (by decide) v169 c170 rfl (by decide) (by decide) rfl

private def ps171 : List ℕ := 1019::ps170
private theorem c171 : F ps170 27483954=2177998 := by decide +kernel
private theorem v171 : F ps171 28006150079=2260433540 :=
  takeStep (p:=1019) (by decide) v170 c171 rfl (by decide) (by decide) rfl

private def ps172 : List ℕ := 1021::ps171
private theorem c172 : F ps171 27430117=2170871 := by decide +kernel
private theorem v172 : F ps172 28006150079=2258262669 :=
  takeStep (p:=1021) (by decide) v171 c172 rfl (by decide) (by decide) rfl

private def ps173 : List ℕ := 1031::ps172
private theorem c173 : F ps172 27164064=2146749 := by decide +kernel
private theorem v173 : F ps173 28006150079=2256115920 :=
  takeStep (p:=1031) (by decide) v172 c173 rfl (by decide) (by decide) rfl

private def ps174 : List ℕ := 1033::ps173
private theorem c174 : F ps173 27111471=2139778 := by decide +kernel
private theorem v174 : F ps174 28006150079=2253976142 :=
  takeStep (p:=1033) (by decide) v173 c174 rfl (by decide) (by decide) rfl

private def ps175 : List ℕ := 1039::ps174
private theorem c175 : F ps174 26954908=2124492 := by decide +kernel
private theorem v175 : F ps175 28006150079=2251851650 :=
  takeStep (p:=1039) (by decide) v174 c175 rfl (by decide) (by decide) rfl

private def ps176 : List ℕ := 1049::ps175
private theorem c176 : F ps175 26697950=2101228 := by decide +kernel
private theorem v176 : F ps176 28006150079=2249750422 :=
  takeStep (p:=1049) (by decide) v175 c176 rfl (by decide) (by decide) rfl

private def ps177 : List ℕ := 1051::ps176
private theorem c177 : F ps176 26647145=2094535 := by decide +kernel
private theorem v177 : F ps177 28006150079=2247655887 :=
  takeStep (p:=1051) (by decide) v176 c177 rfl (by decide) (by decide) rfl

private def ps178 : List ℕ := 1061::ps177
private theorem c178 : F ps177 26395994=2071770 := by decide +kernel
private theorem v178 : F ps178 28006150079=2245584117 :=
  takeStep (p:=1061) (by decide) v177 c178 rfl (by decide) (by decide) rfl

private def ps179 : List ℕ := 1063::ps178
private theorem c179 : F ps178 26346331=2065236 := by decide +kernel
private theorem v179 : F ps179 28006150079=2243518881 :=
  takeStep (p:=1063) (by decide) v178 c179 rfl (by decide) (by decide) rfl

private def ps180 : List ℕ := 1069::ps179
private theorem c180 : F ps179 26198456=2050835 := by decide +kernel
private theorem v180 : F ps180 28006150079=2241468046 :=
  takeStep (p:=1069) (by decide) v179 c180 rfl (by decide) (by decide) rfl

private def ps181 : List ℕ := 1087::ps180
private theorem c181 : F ps180 25764627=2013687 := by decide +kernel
private theorem v181 : F ps181 28006150079=2239454359 :=
  takeStep (p:=1087) (by decide) v180 c181 rfl (by decide) (by decide) rfl

private def ps182 : List ℕ := 1091::ps181
private theorem c182 : F ps181 25670165=2003701 := by decide +kernel
private theorem v182 : F ps182 28006150079=2237450658 :=
  takeStep (p:=1091) (by decide) v181 c182 rfl (by decide) (by decide) rfl

private def ps183 : List ℕ := 1093::ps182
private theorem c183 : F ps182 25623193=1997538 := by decide +kernel
private theorem v183 : F ps183 28006150079=2235453120 :=
  takeStep (p:=1093) (by decide) v182 c183 rfl (by decide) (by decide) rfl

private def ps184 : List ℕ := 1097::ps183
private theorem c184 : F ps183 25529763=1987663 := by decide +kernel
private theorem v184 : F ps184 28006150079=2233465457 :=
  takeStep (p:=1097) (by decide) v183 c184 rfl (by decide) (by decide) rfl

private def ps185 : List ℕ := 1103::ps184
private theorem c185 : F ps184 25390888=1974261 := by decide +kernel
private theorem v185 : F ps185 28006150079=2231491196 :=
  takeStep (p:=1103) (by decide) v184 c185 rfl (by decide) (by decide) rfl

private def ps186 : List ℕ := 1109::ps185
private theorem c186 : F ps185 25253516=1960980 := by decide +kernel
private theorem v186 : F ps186 28006150079=2229530216 :=
  takeStep (p:=1109) (by decide) v185 c186 rfl (by decide) (by decide) rfl

private def ps187 : List ℕ := 1117::ps186
private theorem c187 : F ps186 25072650=1944403 := by decide +kernel
private theorem v187 : F ps187 28006150079=2227585813 :=
  takeStep (p:=1117) (by decide) v186 c187 rfl (by decide) (by decide) rfl

private def ps188 : List ℕ := 1123::ps187
private theorem c188 : F ps187 24938691=1931458 := by decide +kernel
private theorem v188 : F ps188 28006150079=2225654355 :=
  takeStep (p:=1123) (by decide) v187 c188 rfl (by decide) (by decide) rfl

private def ps189 : List ℕ := 1129::ps188
private theorem c189 : F ps188 24806155=1918735 := by decide +kernel
private theorem v189 : F ps189 28006150079=2223735620 :=
  takeStep (p:=1129) (by decide) v188 c189 rfl (by decide) (by decide) rfl

private def ps190 : List ℕ := 1151::ps189
private theorem c190 : F ps189 24332015=1879112 := by decide +kernel
private theorem v190 : F ps190 28006150079=2221856508 :=
  takeStep (p:=1151) (by decide) v189 c190 rfl (by decide) (by decide) rfl

private def ps191 : List ℕ := 1153::ps190
private theorem c191 : F ps190 24289809=1873608 := by decide +kernel
private theorem v191 : F ps191 28006150079=2219982900 :=
  takeStep (p:=1153) (by decide) v190 c191 rfl (by decide) (by decide) rfl

private def ps192 : List ℕ := 1163::ps191
private theorem c192 : F ps191 24080954=1854988 := by decide +kernel
private theorem v192 : F ps192 28006150079=2218127912 :=
  takeStep (p:=1163) (by decide) v191 c192 rfl (by decide) (by decide) rfl

private def ps193 : List ℕ := 1171::ps192
private theorem c193 : F ps192 23916439=1839922 := by decide +kernel
private theorem v193 : F ps193 28006150079=2216287990 :=
  takeStep (p:=1171) (by decide) v192 c193 rfl (by decide) (by decide) rfl

private def ps194 : List ℕ := 1181::ps193
private theorem c194 : F ps193 23713928=1821938 := by decide +kernel
private theorem v194 : F ps194 28006150079=2214466052 :=
  takeStep (p:=1181) (by decide) v193 c194 rfl (by decide) (by decide) rfl

private def ps195 : List ℕ := 1187::ps194
private theorem c195 : F ps194 23594060=1810465 := by decide +kernel
private theorem v195 : F ps195 28006150079=2212655587 :=
  takeStep (p:=1187) (by decide) v194 c195 rfl (by decide) (by decide) rfl

private def ps196 : List ℕ := 1193::ps195
private theorem c196 : F ps195 23475398=1799161 := by decide +kernel
private theorem v196 : F ps196 28006150079=2210856426 :=
  takeStep (p:=1193) (by decide) v195 c196 rfl (by decide) (by decide) rfl

private def ps197 : List ℕ := 1201::ps196
private theorem c197 : F ps196 23319025=1784894 := by decide +kernel
private theorem v197 : F ps197 28006150079=2209071532 :=
  takeStep (p:=1201) (by decide) v196 c197 rfl (by decide) (by decide) rfl

private def ps198 : List ℕ := 1213::ps197
private theorem c198 : F ps197 23088334=1764865 := by decide +kernel
private theorem v198 : F ps198 28006150079=2207306667 :=
  takeStep (p:=1213) (by decide) v197 c198 rfl (by decide) (by decide) rfl

private def ps199 : List ℕ := 1217::ps198
private theorem c199 : F ps198 23012448=1756995 := by decide +kernel
private theorem v199 : F ps199 28006150079=2205549672 :=
  takeStep (p:=1217) (by decide) v198 c199 rfl (by decide) (by decide) rfl

private def ps200 : List ℕ := 1223::ps199
private theorem c200 : F ps199 22899550=1746243 := by decide +kernel
private theorem v200 : F ps200 28006150079=2203803429 :=
  takeStep (p:=1223) (by decide) v199 c200 rfl (by decide) (by decide) rfl

private def ps201 : List ℕ := 1229::ps200
private theorem c201 : F ps200 22787754=1735588 := by decide +kernel
private theorem v201 : F ps201 28006150079=2202067841 :=
  takeStep (p:=1229) (by decide) v200 c201 rfl (by decide) (by decide) rfl

private def ps202 : List ℕ := 1231::ps201
private theorem c202 : F ps201 22750731=1730810 := by decide +kernel
private theorem v202 : F ps202 28006150079=2200337031 :=
  takeStep (p:=1231) (by decide) v201 c202 rfl (by decide) (by decide) rfl

private def ps203 : List ℕ := 1237::ps202
private theorem c203 : F ps202 22640380=1720309 := by decide +kernel
private theorem v203 : F ps203 28006150079=2198616722 :=
  takeStep (p:=1237) (by decide) v202 c203 rfl (by decide) (by decide) rfl

private def ps204 : List ℕ := 1249::ps203
private theorem c204 : F ps203 22422858=1701521 := by decide +kernel
private theorem v204 : F ps204 28006150079=2196915201 :=
  takeStep (p:=1249) (by decide) v203 c204 rfl (by decide) (by decide) rfl

private def ps205 : List ℕ := 1259::ps204
private theorem c205 : F ps204 22244757=1685887 := by decide +kernel
private theorem v205 : F ps205 28006150079=2195229314 :=
  takeStep (p:=1259) (by decide) v204 c205 rfl (by decide) (by decide) rfl

private def ps206 : List ℕ := 1277::ps205
private theorem c206 : F ps205 21931206=1659871 := by decide +kernel
private theorem v206 : F ps206 28006150079=2193569443 :=
  takeStep (p:=1277) (by decide) v205 c206 rfl (by decide) (by decide) rfl

private def ps207 : List ℕ := 1279::ps206
private theorem c207 : F ps206 21896911=1655435 := by decide +kernel
private theorem v207 : F ps207 28006150079=2191914008 :=
  takeStep (p:=1279) (by decide) v206 c207 rfl (by decide) (by decide) rfl

private def ps208 : List ℕ := 1283::ps207
private theorem c208 : F ps207 21828643=1648415 := by decide +kernel
private theorem v208 : F ps208 28006150079=2190265593 :=
  takeStep (p:=1283) (by decide) v207 c208 rfl (by decide) (by decide) rfl

private def ps209 : List ℕ := 1289::ps208
private theorem c209 : F ps208 21727036=1638799 := by decide +kernel
private theorem v209 : F ps209 28006150079=2188626794 :=
  takeStep (p:=1289) (by decide) v208 c209 rfl (by decide) (by decide) rfl

private def ps210 : List ℕ := 1291::ps209
private theorem c210 : F ps209 21693377=1634471 := by decide +kernel
private theorem v210 : F ps210 28006150079=2186992323 :=
  takeStep (p:=1291) (by decide) v209 c210 rfl (by decide) (by decide) rfl

private def ps211 : List ℕ := 1297::ps210
private theorem c211 : F ps210 21593022=1625024 := by decide +kernel
private theorem v211 : F ps211 28006150079=2185367299 :=
  takeStep (p:=1297) (by decide) v210 c211 rfl (by decide) (by decide) rfl

private def ps212 : List ℕ := 1301::ps211
private theorem c212 : F ps211 21526633=1618214 := by decide +kernel
private theorem v212 : F ps212 28006150079=2183749085 :=
  takeStep (p:=1301) (by decide) v211 c212 rfl (by decide) (by decide) rfl

private def ps213 : List ℕ := 1303::ps212
private theorem c213 : F ps212 21493591=1614000 := by decide +kernel
private theorem v213 : F ps213 28006150079=2182135085 :=
  takeStep (p:=1303) (by decide) v212 c213 rfl (by decide) (by decide) rfl

private def ps214 : List ℕ := 1307::ps213
private theorem c214 : F ps213 21427811=1607209 := by decide +kernel
private theorem v214 : F ps214 28006150079=2180527876 :=
  takeStep (p:=1307) (by decide) v213 c214 rfl (by decide) (by decide) rfl

private def ps215 : List ℕ := 1319::ps214
private theorem c215 : F ps214 21232865=1590587 := by decide +kernel
private theorem v215 : F ps215 28006150079=2178937289 :=
  takeStep (p:=1319) (by decide) v214 c215 rfl (by decide) (by decide) rfl

private def ps216 : List ℕ := 1321::ps215
private theorem c216 : F ps215 21200719=1586485 := by decide +kernel
private theorem v216 : F ps216 28006150079=2177350804 :=
  takeStep (p:=1321) (by decide) v215 c216 rfl (by decide) (by decide) rfl

private def ps217 : List ℕ := 1327::ps216
private theorem c217 : F ps216 21104860=1577530 := by decide +kernel
private theorem v217 : F ps217 28006150079=2175773274 :=
  takeStep (p:=1327) (by decide) v216 c217 rfl (by decide) (by decide) rfl

private def ps218 : List ℕ := 1361::ps217
private theorem c218 : F ps217 20577626=1535647 := by decide +kernel
private theorem v218 : F ps218 28006150079=2174237627 :=
  takeStep (p:=1361) (by decide) v217 c218 rfl (by decide) (by decide) rfl

private def ps219 : List ℕ := 1367::ps218
private theorem c219 : F ps218 20487308=1527170 := by decide +kernel
private theorem v219 : F ps219 28006150079=2172710457 :=
  takeStep (p:=1367) (by decide) v218 c219 rfl (by decide) (by decide) rfl

private def ps220 : List ℕ := 1373::ps219
private theorem c220 : F ps219 20397778=1518862 := by decide +kernel
private theorem v220 : F ps220 28006150079=2171191595 :=
  takeStep (p:=1373) (by decide) v219 c220 rfl (by decide) (by decide) rfl

private def ps221 : List ℕ := 1381::ps220
private theorem c221 : F ps220 20279616=1508375 := by decide +kernel
private theorem v221 : F ps221 28006150079=2169683220 :=
  takeStep (p:=1381) (by decide) v220 c221 rfl (by decide) (by decide) rfl

private def ps222 : List ℕ := 1399::ps221
private theorem c222 : F ps221 20018691=1487078 := by decide +kernel
private theorem v222 : F ps222 28006150079=2168196142 :=
  takeStep (p:=1399) (by decide) v221 c222 rfl (by decide) (by decide) rfl

private def ps223 : List ℕ := 1409::ps222
private theorem c223 : F ps222 19876614=1474826 := by decide +kernel
private theorem v223 : F ps223 28006150079=2166721316 :=
  takeStep (p:=1409) (by decide) v222 c223 rfl (by decide) (by decide) rfl

private def ps224 : List ℕ := 1423::ps223
private theorem c224 : F ps223 19681061=1458541 := by decide +kernel
private theorem v224 : F ps224 28006150079=2165262775 :=
  takeStep (p:=1423) (by decide) v223 c224 rfl (by decide) (by decide) rfl

private def ps225 : List ℕ := 1427::ps224
private theorem c225 : F ps224 19625893=1452978 := by decide +kernel
private theorem v225 : F ps225 28006150079=2163809797 :=
  takeStep (p:=1427) (by decide) v224 c225 rfl (by decide) (by decide) rfl

private def ps226 : List ℕ := 1429::ps225
private theorem c226 : F ps225 19598425=1449471 := by decide +kernel
private theorem v226 : F ps226 28006150079=2162360326 :=
  takeStep (p:=1429) (by decide) v225 c226 rfl (by decide) (by decide) rfl

private def ps227 : List ℕ := 1433::ps226
private theorem c227 : F ps226 19543719=1443978 := by decide +kernel
private theorem v227 : F ps227 28006150079=2160916348 :=
  takeStep (p:=1433) (by decide) v226 c227 rfl (by decide) (by decide) rfl

private def ps228 : List ℕ := 1439::ps227
private theorem c228 : F ps227 19462230=1436500 := by decide +kernel
private theorem v228 : F ps228 28006150079=2159479848 :=
  takeStep (p:=1439) (by decide) v227 c228 rfl (by decide) (by decide) rfl

private def ps229 : List ℕ := 1447::ps228
private theorem c229 : F ps228 19354630=1426962 := by decide +kernel
private theorem v229 : F ps229 28006150079=2158052886 :=
  takeStep (p:=1447) (by decide) v228 c229 rfl (by decide) (by decide) rfl

private def ps230 : List ℕ := 1451::ps229
private theorem c230 : F ps229 19301275=1421557 := by decide +kernel
private theorem v230 : F ps230 28006150079=2156631329 :=
  takeStep (p:=1451) (by decide) v229 c230 rfl (by decide) (by decide) rfl

private def ps231 : List ℕ := 1453::ps230
private theorem c231 : F ps230 19274707=1418222 := by decide +kernel
private theorem v231 : F ps231 28006150079=2155213107 :=
  takeStep (p:=1453) (by decide) v230 c231 rfl (by decide) (by decide) rfl

private def ps232 : List ℕ := 1459::ps231
private theorem c232 : F ps231 19195442=1410931 := by decide +kernel
private theorem v232 : F ps232 28006150079=2153802176 :=
  takeStep (p:=1459) (by decide) v231 c232 rfl (by decide) (by decide) rfl

private def ps233 : List ℕ := 1471::ps232
private theorem c233 : F ps232 19038851=1397854 := by decide +kernel
private theorem v233 : F ps233 28006150079=2152404322 :=
  takeStep (p:=1471) (by decide) v232 c233 rfl (by decide) (by decide) rfl

private def ps234 : List ℕ := 1481::ps233
private theorem c234 : F ps233 18910297=1386912 := by decide +kernel
private theorem v234 : F ps234 28006150079=2151017410 :=
  takeStep (p:=1481) (by decide) v233 c234 rfl (by decide) (by decide) rfl

private def ps235 : List ℕ := 1483::ps234
private theorem c235 : F ps234 18884794=1383742 := by decide +kernel
private theorem v235 : F ps235 28006150079=2149633668 :=
  takeStep (p:=1483) (by decide) v234 c235 rfl (by decide) (by decide) rfl

private def ps236 : List ℕ := 1487::ps235
private theorem c236 : F ps235 18833994=1378655 := by decide +kernel
private theorem v236 : F ps236 28006150079=2148255013 :=
  takeStep (p:=1487) (by decide) v235 c236 rfl (by decide) (by decide) rfl

private def ps237 : List ℕ := 1489::ps236
private theorem c237 : F ps236 18808697=1375490 := by decide +kernel
private theorem v237 : F ps237 28006150079=2146879523 :=
  takeStep (p:=1489) (by decide) v236 c237 rfl (by decide) (by decide) rfl

private def ps238 : List ℕ := 1493::ps237
private theorem c238 : F ps237 18758305=1370465 := by decide +kernel
private theorem v238 : F ps238 28006150079=2145509058 :=
  takeStep (p:=1493) (by decide) v237 c238 rfl (by decide) (by decide) rfl

private def ps239 : List ℕ := 1499::ps238
private theorem c239 : F ps238 18683222=1363608 := by decide +kernel
private theorem v239 : F ps239 28006150079=2144145450 :=
  takeStep (p:=1499) (by decide) v238 c239 rfl (by decide) (by decide) rfl

private def ps240 : List ℕ := 1511::ps239
private theorem c240 : F ps239 18534844=1351253 := by decide +kernel
private theorem v240 : F ps240 28006150079=2142794197 :=
  takeStep (p:=1511) (by decide) v239 c240 rfl (by decide) (by decide) rfl

private def ps241 : List ℕ := 1523::ps240
private theorem c241 : F ps240 18388805=1339200 := by decide +kernel
private theorem v241 : F ps241 28006150079=2141454997 :=
  takeStep (p:=1523) (by decide) v240 c241 rfl (by decide) (by decide) rfl

private def ps242 : List ℕ := 1531::ps241
private theorem c242 : F ps241 18292717=1330867 := by decide +kernel
private theorem v242 : F ps242 28006150079=2140124130 :=
  takeStep (p:=1531) (by decide) v241 c242 rfl (by decide) (by decide) rfl

private def ps243 : List ℕ := 1543::ps242
private theorem c243 : F ps242 18150453=1319105 := by decide +kernel
private theorem v243 : F ps243 28006150079=2138805025 :=
  takeStep (p:=1543) (by decide) v242 c243 rfl (by decide) (by decide) rfl

private def ps244 : List ℕ := 1549::ps243
private theorem c244 : F ps243 18080148=1312734 := by decide +kernel
private theorem v244 : F ps244 28006150079=2137492291 :=
  takeStep (p:=1549) (by decide) v243 c244 rfl (by decide) (by decide) rfl

private def ps245 : List ℕ := 1553::ps244
private theorem c245 : F ps244 18033580=1308137 := by decide +kernel
private theorem v245 : F ps245 28006150079=2136184154 :=
  takeStep (p:=1553) (by decide) v244 c245 rfl (by decide) (by decide) rfl

private def ps246 : List ℕ := 1559::ps245
private theorem c246 : F ps245 17964175=1301851 := by decide +kernel
private theorem v246 : F ps246 28006150079=2134882303 :=
  takeStep (p:=1559) (by decide) v245 c246 rfl (by decide) (by decide) rfl

private def ps247 : List ℕ := 1567::ps246
private theorem c247 : F ps246 17872463=1293888 := by decide +kernel
private theorem v247 : F ps247 28006150079=2133588415 :=
  takeStep (p:=1567) (by decide) v246 c247 rfl (by decide) (by decide) rfl

private def ps248 : List ℕ := 1571::ps247
private theorem c248 : F ps247 17826957=1289428 := by decide +kernel
private theorem v248 : F ps248 28006150079=2132298987 :=
  takeStep (p:=1571) (by decide) v247 c248 rfl (by decide) (by decide) rfl

private def ps249 : List ℕ := 1579::ps248
private theorem c249 : F ps248 17736637=1281654 := by decide +kernel
private theorem v249 : F ps249 28006150079=2131017333 :=
  takeStep (p:=1579) (by decide) v248 c249 rfl (by decide) (by decide) rfl

private def ps250 : List ℕ := 1583::ps249
private theorem c250 : F ps249 17691819=1277243 := by decide +kernel
private theorem v250 : F ps250 28006150079=2129740090 :=
  takeStep (p:=1583) (by decide) v249 c250 rfl (by decide) (by decide) rfl

private def ps251 : List ℕ := 1597::ps250
private theorem c251 : F ps250 17536725=1264719 := by decide +kernel
private theorem v251 : F ps251 28006150079=2128475371 :=
  takeStep (p:=1597) (by decide) v250 c251 rfl (by decide) (by decide) rfl

private def ps252 : List ℕ := 1601::ps251
private theorem c252 : F ps251 17492910=1260396 := by decide +kernel
private theorem v252 : F ps252 28006150079=2127214975 :=
  takeStep (p:=1601) (by decide) v251 c252 rfl (by decide) (by decide) rfl

private def ps253 : List ℕ := 1607::ps252
private theorem c253 : F ps252 17427598=1254485 := by decide +kernel
private theorem v253 : F ps253 28006150079=2125960490 :=
  takeStep (p:=1607) (by decide) v252 c253 rfl (by decide) (by decide) rfl

private def ps254 : List ℕ := 1609::ps253
private theorem c254 : F ps253 17405935=1251824 := by decide +kernel
private theorem v254 : F ps254 28006150079=2124708666 :=
  takeStep (p:=1609) (by decide) v253 c254 rfl (by decide) (by decide) rfl

private def ps255 : List ℕ := 1613::ps254
private theorem c255 : F ps254 17362771=1247577 := by decide +kernel
private theorem v255 : F ps255 28006150079=2123461089 :=
  takeStep (p:=1613) (by decide) v254 c255 rfl (by decide) (by decide) rfl

private def ps256 : List ℕ := 1619::ps255
private theorem c256 : F ps255 17298425=1241777 := by decide +kernel
private theorem v256 : F ps256 28006150079=2122219312 :=
  takeStep (p:=1619) (by decide) v255 c256 rfl (by decide) (by decide) rfl

private def ps257 : List ℕ := 1621::ps256
private theorem c257 : F ps256 17277082=1239141 := by decide +kernel
private theorem v257 : F ps257 28006150079=2120980171 :=
  takeStep (p:=1621) (by decide) v256 c257 rfl (by decide) (by decide) rfl

private def ps258 : List ℕ := 1627::ps257
private theorem c258 : F ps257 17213368=1233420 := by decide +kernel
private theorem v258 : F ps258 28006150079=2119746751 :=
  takeStep (p:=1627) (by decide) v257 c258 rfl (by decide) (by decide) rfl

private def ps259 : List ℕ := 1637::ps258
private theorem c259 : F ps258 17108216=1224792 := by decide +kernel
private theorem v259 : F ps259 28006150079=2118521959 :=
  takeStep (p:=1637) (by decide) v258 c259 rfl (by decide) (by decide) rfl

private def ps260 : List ℕ := 1657::ps259
private theorem c260 : F ps259 16901720=1208628 := by decide +kernel
private theorem v260 : F ps260 28006150079=2117313331 :=
  takeStep (p:=1657) (by decide) v259 c260 rfl (by decide) (by decide) rfl

private def ps261 : List ℕ := 1663::ps260
private theorem c261 : F ps260 16840739=1203195 := by decide +kernel
private theorem v261 : F ps261 28006150079=2116110136 :=
  takeStep (p:=1663) (by decide) v260 c261 rfl (by decide) (by decide) rfl

private def ps262 : List ℕ := 1667::ps261
private theorem c262 : F ps261 16800329=1199281 := by decide +kernel
private theorem v262 : F ps262 28006150079=2114910855 :=
  takeStep (p:=1667) (by decide) v261 c262 rfl (by decide) (by decide) rfl

private def ps263 : List ℕ := 1669::ps262
private theorem c263 : F ps262 16780197=1196818 := by decide +kernel
private theorem v263 : F ps263 28006150079=2113714037 :=
  takeStep (p:=1669) (by decide) v262 c263 rfl (by decide) (by decide) rfl

private def ps264 : List ℕ := 1693::ps263
private theorem c264 : F ps263 16542321=1178500 := by decide +kernel
private theorem v264 : F ps264 28006150079=2112535537 :=
  takeStep (p:=1693) (by decide) v263 c264 rfl (by decide) (by decide) rfl

private def ps265 : List ℕ := 1697::ps264
private theorem c265 : F ps264 16503329=1174760 := by decide +kernel
private theorem v265 : F ps265 28006150079=2111360777 :=
  takeStep (p:=1697) (by decide) v264 c265 rfl (by decide) (by decide) rfl

private def ps266 : List ℕ := 1699::ps265
private theorem c266 : F ps265 16483902=1172398 := by decide +kernel
private theorem v266 : F ps266 28006150079=2110188379 :=
  takeStep (p:=1699) (by decide) v265 c266 rfl (by decide) (by decide) rfl

private def ps267 : List ℕ := 1709::ps266
private theorem c267 : F ps266 16387448=1164435 := by decide +kernel
private theorem v267 : F ps267 28006150079=2109023944 :=
  takeStep (p:=1709) (by decide) v266 c267 rfl (by decide) (by decide) rfl

private def ps268 : List ℕ := 1721::ps267
private theorem c268 : F ps267 16273184=1155303 := by decide +kernel
private theorem v268 : F ps268 28006150079=2107868641 :=
  takeStep (p:=1721) (by decide) v267 c268 rfl (by decide) (by decide) rfl

private def ps269 : List ℕ := 1723::ps268
private theorem c269 : F ps268 16254294=1153023 := by decide +kernel
private theorem v269 : F ps269 28006150079=2106715618 :=
  takeStep (p:=1723) (by decide) v268 c269 rfl (by decide) (by decide) rfl

private def ps270 : List ℕ := 1733::ps269
private theorem c270 : F ps269 16160502=1145342 := by decide +kernel
private theorem v270 : F ps270 28006150079=2105570276 :=
  takeStep (p:=1733) (by decide) v269 c270 rfl (by decide) (by decide) rfl

private def ps271 : List ℕ := 1741::ps270
private theorem c271 : F ps270 16086243=1139112 := by decide +kernel
private theorem v271 : F ps271 28006150079=2104431164 :=
  takeStep (p:=1741) (by decide) v270 c271 rfl (by decide) (by decide) rfl

private def ps272 : List ℕ := 1747::ps271
private theorem c272 : F ps271 16030996=1134270 := by decide +kernel
private theorem v272 : F ps272 28006150079=2103296894 :=
  takeStep (p:=1747) (by decide) v271 c272 rfl (by decide) (by decide) rfl

private def ps273 : List ℕ := 1753::ps272
private theorem c273 : F ps272 15976126=1129463 := by decide +kernel
private theorem v273 : F ps273 28006150079=2102167431 :=
  takeStep (p:=1753) (by decide) v272 c273 rfl (by decide) (by decide) rfl

private def ps274 : List ℕ := 1759::ps273
private theorem c274 : F ps273 15921631=1124678 := by decide +kernel
private theorem v274 : F ps274 28006150079=2101042753 :=
  takeStep (p:=1759) (by decide) v273 c274 rfl (by decide) (by decide) rfl

private def ps275 : List ℕ := 1777::ps274
private theorem c275 : F ps274 15760354=1112232 := by decide +kernel
private theorem v275 : F ps275 28006150079=2099930521 :=
  takeStep (p:=1777) (by decide) v274 c275 rfl (by decide) (by decide) rfl

private def ps276 : List ℕ := 1783::ps275
private theorem c276 : F ps275 15707319=1107594 := by decide +kernel
private theorem v276 : F ps276 28006150079=2098822927 :=
  takeStep (p:=1783) (by decide) v275 c276 rfl (by decide) (by decide) rfl

private def ps277 : List ℕ := 1787::ps276
private theorem c277 : F ps276 15672160=1104256 := by decide +kernel
private theorem v277 : F ps277 28006150079=2097718671 :=
  takeStep (p:=1787) (by decide) v276 c277 rfl (by decide) (by decide) rfl

private def ps278 : List ℕ := 1789::ps277
private theorem c278 : F ps277 15654639=1102156 := by decide +kernel
private theorem v278 : F ps278 28006150079=2096616515 :=
  takeStep (p:=1789) (by decide) v277 c278 rfl (by decide) (by decide) rfl

private def ps279 : List ℕ := 1801::ps278
private theorem c279 : F ps278 15550333=1093859 := by decide +kernel
private theorem v279 : F ps279 28006150079=2095522656 :=
  takeStep (p:=1801) (by decide) v278 c279 rfl (by decide) (by decide) rfl

private def ps280 : List ℕ := 1811::ps279
private theorem c280 : F ps279 15464467=1086906 := by decide +kernel
private theorem v280 : F ps280 28006150079=2094435750 :=
  takeStep (p:=1811) (by decide) v279 c280 rfl (by decide) (by decide) rfl

private def ps281 : List ℕ := 1823::ps280
private theorem c281 : F ps280 15362671=1078909 := by decide +kernel
private theorem v281 : F ps281 28006150079=2093356841 :=
  takeStep (p:=1823) (by decide) v280 c281 rfl (by decide) (by decide) rfl

private def ps282 : List ℕ := 1831::ps281
private theorem c282 : F ps281 15295548=1073332 := by decide +kernel
private theorem v282 : F ps282 28006150079=2092283509 :=
  takeStep (p:=1831) (by decide) v281 c282 rfl (by decide) (by decide) rfl

private def ps283 : List ℕ := 1847::ps282
private theorem c283 : F ps282 15163048=1063125 := by decide +kernel
private theorem v283 : F ps283 28006150079=2091220384 :=
  takeStep (p:=1847) (by decide) v282 c283 rfl (by decide) (by decide) rfl

private def ps284 : List ℕ := 1861::ps283
private theorem c284 : F ps283 15048979=1054257 := by decide +kernel
private theorem v284 : F ps284 28006150079=2090166127 :=
  takeStep (p:=1861) (by decide) v283 c284 rfl (by decide) (by decide) rfl

private def ps285 : List ℕ := 1867::ps284
private theorem c285 : F ps284 15000616=1050086 := by decide +kernel
private theorem v285 : F ps285 28006150079=2089116041 :=
  takeStep (p:=1867) (by decide) v284 c285 rfl (by decide) (by decide) rfl

private def ps286 : List ℕ := 1871::ps285
private theorem c286 : F ps285 14968546=1047067 := by decide +kernel
private theorem v286 : F ps286 28006150079=2088068974 :=
  takeStep (p:=1871) (by decide) v285 c286 rfl (by decide) (by decide) rfl

private def ps287 : List ℕ := 1873::ps286
private theorem c287 : F ps286 14952562=1045245 := by decide +kernel
private theorem v287 : F ps287 28006150079=2087023729 :=
  takeStep (p:=1873) (by decide) v286 c287 rfl (by decide) (by decide) rfl

private def ps288 : List ℕ := 1877::ps287
private theorem c288 : F ps287 14920697=1042246 := by decide +kernel
private theorem v288 : F ps288 28006150079=2085981483 :=
  takeStep (p:=1877) (by decide) v287 c288 rfl (by decide) (by decide) rfl

private def ps289 : List ℕ := 1879::ps288
private theorem c289 : F ps288 14904816=1040416 := by decide +kernel
private theorem v289 : F ps289 28006150079=2084941067 :=
  takeStep (p:=1879) (by decide) v288 c289 rfl (by decide) (by decide) rfl

private def ps290 : List ℕ := 1889::ps289
private theorem c290 : F ps289 14825913=1034142 := by decide +kernel
private theorem v290 : F ps290 28006150079=2083906925 :=
  takeStep (p:=1889) (by decide) v289 c290 rfl (by decide) (by decide) rfl

private def ps291 : List ℕ := 1901::ps290
private theorem c291 : F ps290 14732325=1026789 := by decide +kernel
private theorem v291 : F ps291 28006150079=2082880136 :=
  takeStep (p:=1901) (by decide) v290 c291 rfl (by decide) (by decide) rfl

private def ps292 : List ℕ := 1907::ps291
private theorem c292 : F ps291 14685972=1022806 := by decide +kernel
private theorem v292 : F ps292 28006150079=2081857330 :=
  takeStep (p:=1907) (by decide) v291 c292 rfl (by decide) (by decide) rfl

private def ps293 : List ℕ := 1913::ps292
private theorem c293 : F ps292 14639911=1018883 := by decide +kernel
private theorem v293 : F ps293 28006150079=2080838447 :=
  takeStep (p:=1913) (by decide) v292 c293 rfl (by decide) (by decide) rfl

private def ps294 : List ℕ := 1931::ps293
private theorem c294 : F ps293 14503443=1008609 := by decide +kernel
private theorem v294 : F ps294 28006150079=2079829838 :=
  takeStep (p:=1931) (by decide) v293 c294 rfl (by decide) (by decide) rfl

private def ps295 : List ℕ := 1933::ps294
private theorem c295 : F ps294 14488437=1006887 := by decide +kernel
private theorem v295 : F ps295 28006150079=2078822951 :=
  takeStep (p:=1933) (by decide) v294 c295 rfl (by decide) (by decide) rfl

private def ps296 : List ℕ := 1949::ps295
private theorem c296 : F ps295 14369497=997855 := by decide +kernel
private theorem v296 : F ps296 28006150079=2077825096 :=
  takeStep (p:=1949) (by decide) v295 c296 rfl (by decide) (by decide) rfl

private def ps297 : List ℕ := 1951::ps296
private theorem c297 : F ps296 14354766=996176 := by decide +kernel
private theorem v297 : F ps297 28006150079=2076828920 :=
  takeStep (p:=1951) (by decide) v296 c297 rfl (by decide) (by decide) rfl

private def ps298 : List ℕ := 1973::ps297
private theorem c298 : F ps297 14194703=984225 := by decide +kernel
private theorem v298 : F ps298 28006150079=2075844695 :=
  takeStep (p:=1973) (by decide) v297 c298 rfl (by decide) (by decide) rfl

private def ps299 : List ℕ := 1979::ps298
private theorem c299 : F ps298 14151667=980615 := by decide +kernel
private theorem v299 : F ps299 28006150079=2074864080 :=
  takeStep (p:=1979) (by decide) v298 c299 rfl (by decide) (by decide) rfl

private def ps300 : List ℕ := 1987::ps299
private theorem c300 : F ps299 14094690=975995 := by decide +kernel
private theorem v300 : F ps300 28006150079=2073888085 :=
  takeStep (p:=1987) (by decide) v299 c300 rfl (by decide) (by decide) rfl

private def ps301 : List ℕ := 1993::ps300
private theorem c301 : F ps300 14052257=972409 := by decide +kernel
private theorem v301 : F ps301 28006150079=2072915676 :=
  takeStep (p:=1993) (by decide) v300 c301 rfl (by decide) (by decide) rfl

private def ps302 : List ℕ := 1997::ps301
private theorem c302 : F ps301 14024111=969846 := by decide +kernel
private theorem v302 : F ps302 28006150079=2071945830 :=
  takeStep (p:=1997) (by decide) v301 c302 rfl (by decide) (by decide) rfl

private def ps303 : List ℕ := 1999::ps302
private theorem c303 : F ps302 14010080=968255 := by decide +kernel
private theorem v303 : F ps303 28006150079=2070977575 :=
  takeStep (p:=1999) (by decide) v302 c303 rfl (by decide) (by decide) rfl

private def ps304 : List ℕ := 2003::ps303
private theorem c304 : F ps303 13982101=965714 := by decide +kernel
private theorem v304 : F ps304 28006150079=2070011861 :=
  takeStep (p:=2003) (by decide) v303 c304 rfl (by decide) (by decide) rfl

private def ps305 : List ℕ := 2011::ps304
private theorem c305 : F ps304 13926479=961298 := by decide +kernel
private theorem v305 : F ps305 28006150079=2069050563 :=
  takeStep (p:=2011) (by decide) v304 c305 rfl (by decide) (by decide) rfl

private def ps306 : List ℕ := 2017::ps305
private theorem c306 : F ps305 13885052=957779 := by decide +kernel
private theorem v306 : F ps306 28006150079=2068092784 :=
  takeStep (p:=2017) (by decide) v305 c306 rfl (by decide) (by decide) rfl

private def ps307 : List ℕ := 2027::ps306
private theorem c307 : F ps306 13816551=952395 := by decide +kernel
private theorem v307 : F ps307 28006150079=2067140389 :=
  takeStep (p:=2027) (by decide) v306 c307 rfl (by decide) (by decide) rfl

private def ps308 : List ℕ := 2029::ps307
private theorem c308 : F ps307 13802932=950872 := by decide +kernel
private theorem v308 : F ps308 28006150079=2066189517 :=
  takeStep (p:=2029) (by decide) v307 c308 rfl (by decide) (by decide) rfl

private def ps309 : List ℕ := 2039::ps308
private theorem c309 : F ps308 13735237=945588 := by decide +kernel
private theorem v309 : F ps309 28006150079=2065243929 :=
  takeStep (p:=2039) (by decide) v308 c309 rfl (by decide) (by decide) rfl

private def ps310 : List ℕ := 2053::ps309
private theorem c310 : F ps309 13641573=938511 := by decide +kernel
private theorem v310 : F ps310 28006150079=2064305418 :=
  takeStep (p:=2053) (by decide) v309 c310 rfl (by decide) (by decide) rfl

private def ps311 : List ℕ := 2063::ps310
private theorem c311 : F ps310 13575448=933341 := by decide +kernel
private theorem v311 : F ps311 28006150079=2063372077 :=
  takeStep (p:=2063) (by decide) v310 c311 rfl (by decide) (by decide) rfl

private def ps312 : List ℕ := 2069::ps311
private theorem c312 : F ps311 13536080=930084 := by decide +kernel
private theorem v312 : F ps312 28006150079=2062441993 :=
  takeStep (p:=2069) (by decide) v311 c312 rfl (by decide) (by decide) rfl

private def ps313 : List ℕ := 2081::ps312
private theorem c313 : F ps312 13458025=924155 := by decide +kernel
private theorem v313 : F ps313 28006150079=2061517838 :=
  takeStep (p:=2081) (by decide) v312 c313 rfl (by decide) (by decide) rfl

private def ps314 : List ℕ := 2083::ps313
private theorem c314 : F ps313 13445103=922750 := by decide +kernel
private theorem v314 : F ps314 28006150079=2060595088 :=
  takeStep (p:=2083) (by decide) v313 c314 rfl (by decide) (by decide) rfl

private def ps315 : List ℕ := 2087::ps314
private theorem c315 : F ps314 13419334=920444 := by decide +kernel
private theorem v315 : F ps315 28006150079=2059674644 :=
  takeStep (p:=2087) (by decide) v314 c315 rfl (by decide) (by decide) rfl

private def ps316 : List ℕ := 2089::ps315
private theorem c316 : F ps315 13406486=919058 := by decide +kernel
private theorem v316 : F ps316 28006150079=2058755586 :=
  takeStep (p:=2089) (by decide) v315 c316 rfl (by decide) (by decide) rfl

private def ps317 : List ℕ := 2099::ps316
private theorem c317 : F ps316 13342615=914099 := by decide +kernel
private theorem v317 : F ps317 28006150079=2057841487 :=
  takeStep (p:=2099) (by decide) v316 c317 rfl (by decide) (by decide) rfl

private def ps318 : List ℕ := 2111::ps317
private theorem c318 : F ps317 13266769=908344 := by decide +kernel
private theorem v318 : F ps318 28006150079=2056933143 :=
  takeStep (p:=2111) (by decide) v317 c318 rfl (by decide) (by decide) rfl

private def ps319 : List ℕ := 2113::ps318
private theorem c319 : F ps318 13254212=906984 := by decide +kernel
private theorem v319 : F ps319 28006150079=2056026159 :=
  takeStep (p:=2113) (by decide) v318 c319 rfl (by decide) (by decide) rfl

private def ps320 : List ℕ := 2129::ps319
private theorem c320 : F ps319 13154603=899620 := by decide +kernel
private theorem v320 : F ps320 28006150079=2055126539 :=
  takeStep (p:=2129) (by decide) v319 c320 rfl (by decide) (by decide) rfl

private def ps321 : List ℕ := 2131::ps320
private theorem c321 : F ps320 13142257=898295 := by decide +kernel
private theorem v321 : F ps321 28006150079=2054228244 :=
  takeStep (p:=2131) (by decide) v320 c321 rfl (by decide) (by decide) rfl

private def ps322 : List ℕ := 2137::ps321
private theorem c322 : F ps321 13105358=895275 := by decide +kernel
private theorem v322 : F ps322 28006150079=2053332969 :=
  takeStep (p:=2137) (by decide) v321 c322 rfl (by decide) (by decide) rfl

private def ps323 : List ℕ := 2141::ps322
private theorem c323 : F ps322 13080873=893150 := by decide +kernel
private theorem v323 : F ps323 28006150079=2052439819 :=
  takeStep (p:=2141) (by decide) v322 c323 rfl (by decide) (by decide) rfl

private def ps324 : List ℕ := 2143::ps323
private theorem c324 : F ps323 13068665=891830 := by decide +kernel
private theorem v324 : F ps324 28006150079=2051547989 :=
  takeStep (p:=2143) (by decide) v323 c324 rfl (by decide) (by decide) rfl

private def ps325 : List ℕ := 2153::ps324
private theorem c325 : F ps324 13007965=887232 := by decide +kernel
private theorem v325 : F ps325 28006150079=2050660757 :=
  takeStep (p:=2153) (by decide) v324 c325 rfl (by decide) (by decide) rfl

private def ps326 : List ℕ := 2161::ps325
private theorem c326 : F ps325 12959810=883469 := by decide +kernel
private theorem v326 : F ps326 28006150079=2049777288 :=
  takeStep (p:=2161) (by decide) v325 c326 rfl (by decide) (by decide) rfl

private def ps327 : List ℕ := 2179::ps326
private theorem c327 : F ps326 12852753=875734 := by decide +kernel
private theorem v327 : F ps327 28006150079=2048901554 :=
  takeStep (p:=2179) (by decide) v326 c327 rfl (by decide) (by decide) rfl

private def ps328 : List ℕ := 2203::ps327
private theorem c328 : F ps327 12712732=865644 := by decide +kernel
private theorem v328 : F ps328 28006150079=2048035910 :=
  takeStep (p:=2203) (by decide) v327 c328 rfl (by decide) (by decide) rfl

private def ps329 : List ℕ := 2207::ps328
private theorem c329 : F ps328 12689691=863650 := by decide +kernel
private theorem v329 : F ps329 28006150079=2047172260 :=
  takeStep (p:=2207) (by decide) v328 c329 rfl (by decide) (by decide) rfl

private def ps330 : List ℕ := 2213::ps329
private theorem c330 : F ps329 12655286=860877 := by decide +kernel
private theorem v330 : F ps330 28006150079=2046311383 :=
  takeStep (p:=2213) (by decide) v329 c330 rfl (by decide) (by decide) rfl

private def ps331 : List ℕ := 2221::ps330
private theorem c331 : F ps330 12609702=857339 := by decide +kernel
private theorem v331 : F ps331 28006150079=2045454044 :=
  takeStep (p:=2221) (by decide) v330 c331 rfl (by decide) (by decide) rfl

private def ps332 : List ℕ := 2237::ps331
private theorem c332 : F ps331 12519512=850802 := by decide +kernel
private theorem v332 : F ps332 28006150079=2044603242 :=
  takeStep (p:=2237) (by decide) v331 c332 rfl (by decide) (by decide) rfl

private def ps333 : List ℕ := 2239::ps332
private theorem c333 : F ps332 12508329=849610 := by decide +kernel
private theorem v333 : F ps333 28006150079=2043753632 :=
  takeStep (p:=2239) (by decide) v332 c333 rfl (by decide) (by decide) rfl

private def ps334 : List ℕ := 2243::ps333
private theorem c334 : F ps333 12486023=847737 := by decide +kernel
private theorem v334 : F ps334 28006150079=2042905895 :=
  takeStep (p:=2243) (by decide) v333 c334 rfl (by decide) (by decide) rfl

private def ps335 : List ℕ := 2251::ps334
private theorem c335 : F ps334 12441648=844311 := by decide +kernel
private theorem v335 : F ps335 28006150079=2042061584 :=
  takeStep (p:=2251) (by decide) v334 c335 rfl (by decide) (by decide) rfl

private def ps336 : List ℕ := 2267::ps335
private theorem c336 : F ps335 12353837=837917 := by decide +kernel
private theorem v336 : F ps336 28006150079=2041223667 :=
  takeStep (p:=2267) (by decide) v335 c336 rfl (by decide) (by decide) rfl

private def ps337 : List ℕ := 2269::ps336
private theorem c337 : F ps336 12342948=836773 := by decide +kernel
private theorem v337 : F ps337 28006150079=2040386894 :=
  takeStep (p:=2269) (by decide) v336 c337 rfl (by decide) (by decide) rfl

private def ps338 : List ℕ := 2273::ps337
private theorem c338 : F ps337 12321227=834971 := by decide +kernel
private theorem v338 : F ps338 28006150079=2039551923 :=
  takeStep (p:=2273) (by decide) v337 c338 rfl (by decide) (by decide) rfl

private def ps339 : List ℕ := 2281::ps338
private theorem c339 : F ps338 12278014=831649 := by decide +kernel
private theorem v339 : F ps339 28006150079=2038720274 :=
  takeStep (p:=2281) (by decide) v338 c339 rfl (by decide) (by decide) rfl

private def ps340 : List ℕ := 2287::ps339
private theorem c340 : F ps339 12245802=829101 := by decide +kernel
private theorem v340 : F ps340 28006150079=2037891173 :=
  takeStep (p:=2287) (by decide) v339 c340 rfl (by decide) (by decide) rfl

private def ps341 : List ℕ := 2293::ps340
private theorem c341 : F ps340 12213759=826556 := by decide +kernel
private theorem v341 : F ps341 28006150079=2037064617 :=
  takeStep (p:=2293) (by decide) v340 c341 rfl (by decide) (by decide) rfl

private def ps342 : List ℕ := 2297::ps341
private theorem c342 : F ps341 12192490=824751 := by decide +kernel
private theorem v342 : F ps342 28006150079=2036239866 :=
  takeStep (p:=2297) (by decide) v341 c342 rfl (by decide) (by decide) rfl

private def ps343 : List ℕ := 2309::ps342
private theorem c343 : F ps342 12129125=820124 := by decide +kernel
private theorem v343 : F ps343 28006150079=2035419742 :=
  takeStep (p:=2309) (by decide) v342 c343 rfl (by decide) (by decide) rfl

private def ps344 : List ℕ := 2311::ps343
private theorem c344 : F ps343 12118628=819070 := by decide +kernel
private theorem v344 : F ps344 28006150079=2034600672 :=
  takeStep (p:=2311) (by decide) v343 c344 rfl (by decide) (by decide) rfl

private def ps345 : List ℕ := 2333::ps344
private theorem c345 : F ps344 12004350=811023 := by decide +kernel
private theorem v345 : F ps345 28006150079=2033789649 :=
  takeStep (p:=2333) (by decide) v344 c345 rfl (by decide) (by decide) rfl

private def ps346 : List ℕ := 2339::ps345
private theorem c346 : F ps345 11973557=808626 := by decide +kernel
private theorem v346 : F ps346 28006150079=2032981023 :=
  takeStep (p:=2339) (by decide) v345 c346 rfl (by decide) (by decide) rfl

private def ps347 : List ℕ := 2341::ps346
private theorem c347 : F ps346 11963327=807622 := by decide +kernel
private theorem v347 : F ps347 28006150079=2032173401 :=
  takeStep (p:=2341) (by decide) v346 c347 rfl (by decide) (by decide) rfl

private def ps348 : List ℕ := 2347::ps347
private theorem c348 : F ps347 11932743=805204 := by decide +kernel
private theorem v348 : F ps348 28006150079=2031368197 :=
  takeStep (p:=2347) (by decide) v347 c348 rfl (by decide) (by decide) rfl

private def ps349 : List ℕ := 2351::ps348
private theorem c349 : F ps348 11912441=803501 := by decide +kernel
private theorem v349 : F ps349 28006150079=2030564696 :=
  takeStep (p:=2351) (by decide) v348 c349 rfl (by decide) (by decide) rfl

private def ps350 : List ℕ := 2357::ps349
private theorem c350 : F ps349 11882117=801137 := by decide +kernel
private theorem v350 : F ps350 28006150079=2029763559 :=
  takeStep (p:=2357) (by decide) v349 c350 rfl (by decide) (by decide) rfl

private def ps351 : List ℕ := 2371::ps350
private theorem c351 : F ps350 11811957=796110 := by decide +kernel
private theorem v351 : F ps351 28006150079=2028967449 :=
  takeStep (p:=2371) (by decide) v350 c351 rfl (by decide) (by decide) rfl

private def ps352 : List ℕ := 2377::ps351
private theorem c352 : F ps351 11782141=793764 := by decide +kernel
private theorem v352 : F ps352 28006150079=2028173685 :=
  takeStep (p:=2377) (by decide) v351 c352 rfl (by decide) (by decide) rfl

private def ps353 : List ℕ := 2381::ps352
private theorem c353 : F ps352 11762347=792139 := by decide +kernel
private theorem v353 : F ps353 28006150079=2027381546 :=
  takeStep (p:=2381) (by decide) v352 c353 rfl (by decide) (by decide) rfl

private def ps354 : List ℕ := 2383::ps353
private theorem c354 : F ps353 11752475=791182 := by decide +kernel
private theorem v354 : F ps354 28006150079=2026590364 :=
  takeStep (p:=2383) (by decide) v353 c354 rfl (by decide) (by decide) rfl

private def ps355 : List ℕ := 2389::ps354
private theorem c355 : F ps354 11722959=788918 := by decide +kernel
private theorem v355 : F ps355 28006150079=2025801446 :=
  takeStep (p:=2389) (by decide) v354 c355 rfl (by decide) (by decide) rfl

private def ps356 : List ℕ := 2393::ps355
private theorem c356 : F ps355 11703364=787326 := by decide +kernel
private theorem v356 : F ps356 28006150079=2025014120 :=
  takeStep (p:=2393) (by decide) v355 c356 rfl (by decide) (by decide) rfl

private def ps357 : List ℕ := 2399::ps356
private theorem c357 : F ps356 11674093=785081 := by decide +kernel
private theorem v357 : F ps357 28006150079=2024229039 :=
  takeStep (p:=2399) (by decide) v356 c357 rfl (by decide) (by decide) rfl

private def ps358 : List ℕ := 2411::ps357
private theorem c358 : F ps357 11615989=780920 := by decide +kernel
private theorem v358 : F ps358 28006150079=2023448119 :=
  takeStep (p:=2411) (by decide) v357 c358 rfl (by decide) (by decide) rfl

private def ps359 : List ℕ := 2417::ps358
private theorem c359 : F ps358 11587153=778672 := by decide +kernel
private theorem v359 : F ps359 28006150079=2022669447 :=
  takeStep (p:=2417) (by decide) v358 c359 rfl (by decide) (by decide) rfl

private def ps360 : List ℕ := 2423::ps359
private theorem c360 : F ps359 11558460=776489 := by decide +kernel
private theorem v360 : F ps360 28006150079=2021892958 :=
  takeStep (p:=2423) (by decide) v359 c360 rfl (by decide) (by decide) rfl

private def ps361 : List ℕ := 2437::ps360
private theorem c361 : F ps360 11492059=771764 := by decide +kernel
private theorem v361 : F ps361 28006150079=2021121194 :=
  takeStep (p:=2437) (by decide) v360 c361 rfl (by decide) (by decide) rfl

private def ps362 : List ℕ := 2441::ps361
private theorem c362 : F ps361 11473228=770267 := by decide +kernel
private theorem v362 : F ps362 28006150079=2020350927 :=
  takeStep (p:=2441) (by decide) v361 c362 rfl (by decide) (by decide) rfl

private def ps363 : List ℕ := 2447::ps362
private theorem c363 : F ps362 11445096=768079 := by decide +kernel
private theorem v363 : F ps363 28006150079=2019582848 :=
  takeStep (p:=2447) (by decide) v362 c363 rfl (by decide) (by decide) rfl

private def ps364 : List ℕ := 2459::ps363
private theorem c364 : F ps363 11389243=764111 := by decide +kernel
private theorem v364 : F ps364 28006150079=2018818737 :=
  takeStep (p:=2459) (by decide) v363 c364 rfl (by decide) (by decide) rfl

private def ps365 : List ℕ := 2467::ps364
private theorem c365 : F ps364 11352310=761436 := by decide +kernel
private theorem v365 : F ps365 28006150079=2018057301 :=
  takeStep (p:=2467) (by decide) v364 c365 rfl (by decide) (by decide) rfl

private def ps366 : List ℕ := 2473::ps365
private theorem c366 : F ps365 11324767=759361 := by decide +kernel
private theorem v366 : F ps366 28006150079=2017297940 :=
  takeStep (p:=2473) (by decide) v365 c366 rfl (by decide) (by decide) rfl

private def ps367 : List ℕ := 2477::ps366
private theorem c367 : F ps366 11306479=757890 := by decide +kernel
private theorem v367 : F ps367 28006150079=2016540050 :=
  takeStep (p:=2477) (by decide) v366 c367 rfl (by decide) (by decide) rfl

private def ps368 : List ℕ := 2503::ps367
private theorem c368 : F ps367 11189033=749924 := by decide +kernel
private theorem v368 : F ps368 28006150079=2015790126 :=
  takeStep (p:=2503) (by decide) v367 c368 rfl (by decide) (by decide) rfl

private def ps369 : List ℕ := 2521::ps368
private theorem c369 : F ps368 11109143=744429 := by decide +kernel
private theorem v369 : F ps369 28006150079=2015045697 :=
  takeStep (p:=2521) (by decide) v368 c369 rfl (by decide) (by decide) rfl

private def ps370 : List ℕ := 2531::ps369
private theorem c370 : F ps369 11065250=741283 := by decide +kernel
private theorem v370 : F ps370 28006150079=2014304414 :=
  takeStep (p:=2531) (by decide) v369 c370 rfl (by decide) (by decide) rfl

private def ps371 : List ℕ := 2539::ps370
private theorem c371 : F ps370 11030386=738728 := by decide +kernel
private theorem v371 : F ps371 28006150079=2013565686 :=
  takeStep (p:=2539) (by decide) v370 c371 rfl (by decide) (by decide) rfl

private def ps372 : List ℕ := 2543::ps371
private theorem c372 : F ps371 11013035=737372 := by decide +kernel
private theorem v372 : F ps372 28006150079=2012828314 :=
  takeStep (p:=2543) (by decide) v371 c372 rfl (by decide) (by decide) rfl

private def ps373 : List ℕ := 2549::ps372
private theorem c373 : F ps372 10987112=735471 := by decide +kernel
private theorem v373 : F ps373 28006150079=2012092843 :=
  takeStep (p:=2549) (by decide) v372 c373 rfl (by decide) (by decide) rfl

private def ps374 : List ℕ := 2551::ps373
private theorem c374 : F ps373 10978498=734677 := by decide +kernel
private theorem v374 : F ps374 28006150079=2011358166 :=
  takeStep (p:=2551) (by decide) v373 c374 rfl (by decide) (by decide) rfl

private def ps375 : List ℕ := 2557::ps374
private theorem c375 : F ps374 10952737=732777 := by decide +kernel
private theorem v375 : F ps375 28006150079=2010625389 :=
  takeStep (p:=2557) (by decide) v374 c375 rfl (by decide) (by decide) rfl

private def ps376 : List ℕ := 2579::ps375
private theorem c376 : F ps375 10859305=726423 := by decide +kernel
private theorem v376 : F ps376 28006150079=2009898966 :=
  takeStep (p:=2579) (by decide) v375 c376 rfl (by decide) (by decide) rfl

private def ps377 : List ℕ := 2591::ps376
private theorem c377 : F ps376 10809011=722925 := by decide +kernel
private theorem v377 : F ps377 28006150079=2009176041 :=
  takeStep (p:=2591) (by decide) v376 c377 rfl (by decide) (by decide) rfl

private def ps378 : List ℕ := 2593::ps377
private theorem c378 : F ps377 10800674=722181 := by decide +kernel
private theorem v378 : F ps378 28006150079=2008453860 :=
  takeStep (p:=2593) (by decide) v377 c378 rfl (by decide) (by decide) rfl

private def ps379 : List ℕ := 2609::ps378
private theorem c379 : F ps378 10734438=717683 := by decide +kernel
private theorem v379 : F ps379 28006150079=2007736177 :=
  takeStep (p:=2609) (by decide) v378 c379 rfl (by decide) (by decide) rfl

private def ps380 : List ℕ := 2617::ps379
private theorem c380 : F ps379 10701624=715338 := by decide +kernel
private theorem v380 : F ps380 28006150079=2007020839 :=
  takeStep (p:=2617) (by decide) v379 c380 rfl (by decide) (by decide) rfl

private def ps381 : List ℕ := 2621::ps380
private theorem c381 : F ps380 10685291=714098 := by decide +kernel
private theorem v381 : F ps381 28006150079=2006306741 :=
  takeStep (p:=2621) (by decide) v380 c381 rfl (by decide) (by decide) rfl

private def ps382 : List ℕ := 2633::ps381
private theorem c382 : F ps381 10636593=710693 := by decide +kernel
private theorem v382 : F ps382 28006150079=2005596048 :=
  takeStep (p:=2633) (by decide) v381 c382 rfl (by decide) (by decide) rfl

private def ps383 : List ℕ := 2647::ps382
private theorem c383 : F ps382 10580336=706862 := by decide +kernel
private theorem v383 : F ps383 28006150079=2004889186 :=
  takeStep (p:=2647) (by decide) v382 c383 rfl (by decide) (by decide) rfl

private def ps384 : List ℕ := 2657::ps383
private theorem c384 : F ps383 10540515=704091 := by decide +kernel
private theorem v384 : F ps384 28006150079=2004185095 :=
  takeStep (p:=2657) (by decide) v383 c384 rfl (by decide) (by decide) rfl

private def ps385 : List ℕ := 2659::ps384
private theorem c385 : F ps384 10532587=703403 := by decide +kernel
private theorem v385 : F ps385 28006150079=2003481692 :=
  takeStep (p:=2659) (by decide) v384 c385 rfl (by decide) (by decide) rfl

private def ps386 : List ℕ := 2663::ps385
private theorem c386 : F ps385 10516766=702235 := by decide +kernel
private theorem v386 : F ps386 28006150079=2002779457 :=
  takeStep (p:=2663) (by decide) v385 c386 rfl (by decide) (by decide) rfl

private def ps387 : List ℕ := 2671::ps386
private theorem c387 : F ps386 10485267=700001 := by decide +kernel
private theorem v387 : F ps387 28006150079=2002079456 :=
  takeStep (p:=2671) (by decide) v386 c387 rfl (by decide) (by decide) rfl

private def ps388 : List ℕ := 2677::ps387
private theorem c388 : F ps387 10461766=698307 := by decide +kernel
private theorem v388 : F ps388 28006150079=2001381149 :=
  takeStep (p:=2677) (by decide) v387 c388 rfl (by decide) (by decide) rfl

private def ps389 : List ℕ := 2683::ps388
private theorem c389 : F ps388 10438371=696635 := by decide +kernel
private theorem v389 : F ps389 28006150079=2000684514 :=
  takeStep (p:=2683) (by decide) v388 c389 rfl (by decide) (by decide) rfl

private def ps390 : List ℕ := 2687::ps389
private theorem c390 : F ps389 10422832=695469 := by decide +kernel
private theorem v390 : F ps390 28006150079=1999989045 :=
  takeStep (p:=2687) (by decide) v389 c390 rfl (by decide) (by decide) rfl

private def ps391 : List ℕ := 2689::ps390
private theorem c391 : F ps390 10415079=694823 := by decide +kernel
private theorem v391 : F ps391 28006150079=1999294222 :=
  takeStep (p:=2689) (by decide) v390 c391 rfl (by decide) (by decide) rfl

private def ps392 : List ℕ := 2693::ps391
private theorem c392 : F ps391 10399610=693671 := by decide +kernel
private theorem v392 : F ps392 28006150079=1998600551 :=
  takeStep (p:=2693) (by decide) v391 c392 rfl (by decide) (by decide) rfl

private def ps393 : List ℕ := 2699::ps392
private theorem c393 : F ps392 10376491=692012 := by decide +kernel
private theorem v393 : F ps393 28006150079=1997908539 :=
  takeStep (p:=2699) (by decide) v392 c393 rfl (by decide) (by decide) rfl

private def ps394 : List ℕ := 2707::ps393
private theorem c394 : F ps393 10345825=689891 := by decide +kernel
private theorem v394 : F ps394 28006150079=1997218648 :=
  takeStep (p:=2707) (by decide) v393 c394 rfl (by decide) (by decide) rfl

private def ps395 : List ℕ := 2711::ps394
private theorem c395 : F ps394 10330560=688778 := by decide +kernel
private theorem v395 : F ps395 28006150079=1996529870 :=
  takeStep (p:=2711) (by decide) v394 c395 rfl (by decide) (by decide) rfl

private def ps396 : List ℕ := 2713::ps395
private theorem c396 : F ps395 10322945=688143 := by decide +kernel
private theorem v396 : F ps396 28006150079=1995841727 :=
  takeStep (p:=2713) (by decide) v395 c396 rfl (by decide) (by decide) rfl

private def ps397 : List ℕ := 2719::ps396
private theorem c397 : F ps396 10300165=686542 := by decide +kernel
private theorem v397 : F ps397 28006150079=1995155185 :=
  takeStep (p:=2719) (by decide) v396 c397 rfl (by decide) (by decide) rfl

private def ps398 : List ℕ := 2729::ps397
private theorem c398 : F ps397 10262422=683996 := by decide +kernel
private theorem v398 : F ps398 28006150079=1994471189 :=
  takeStep (p:=2729) (by decide) v397 c398 rfl (by decide) (by decide) rfl

private def ps399 : List ℕ := 2731::ps398
private theorem c399 : F ps398 10254906=683375 := by decide +kernel
private theorem v399 : F ps399 28006150079=1993787814 :=
  takeStep (p:=2731) (by decide) v398 c399 rfl (by decide) (by decide) rfl

private def ps400 : List ℕ := 2741::ps399
private theorem c400 : F ps399 10217493=680826 := by decide +kernel
private theorem v400 : F ps400 28006150079=1993106988 :=
  takeStep (p:=2741) (by decide) v399 c400 rfl (by decide) (by decide) rfl

private def ps401 : List ℕ := 2749::ps400
private theorem c401 : F ps400 10187759=678833 := by decide +kernel
private theorem v401 : F ps401 28006150079=1992428155 :=
  takeStep (p:=2749) (by decide) v400 c401 rfl (by decide) (by decide) rfl

private def ps402 : List ℕ := 2753::ps401
private theorem c402 : F ps401 10172956=677767 := by decide +kernel
private theorem v402 : F ps402 28006150079=1991750388 :=
  takeStep (p:=2753) (by decide) v401 c402 rfl (by decide) (by decide) rfl

private def ps403 : List ℕ := 2767::ps402
private theorem c403 : F ps402 10121485=674366 := by decide +kernel
private theorem v403 : F ps403 28006150079=1991076022 :=
  takeStep (p:=2767) (by decide) v402 c403 rfl (by decide) (by decide) rfl

private def ps404 : List ℕ := 2777::ps403
private theorem c404 : F ps403 10085037=671934 := by decide +kernel
private theorem v404 : F ps404 28006150079=1990404088 :=
  takeStep (p:=2777) (by decide) v403 c404 rfl (by decide) (by decide) rfl

private def ps405 : List ℕ := 2789::ps404
private theorem c405 : F ps404 10041645=669027 := by decide +kernel
private theorem v405 : F ps405 28006150079=1989735061 :=
  takeStep (p:=2789) (by decide) v404 c405 rfl (by decide) (by decide) rfl

private def ps406 : List ℕ := 2791::ps405
private theorem c406 : F ps405 10034450=668464 := by decide +kernel
private theorem v406 : F ps406 28006150079=1989066597 :=
  takeStep (p:=2791) (by decide) v405 c406 rfl (by decide) (by decide) rfl

private def ps407 : List ℕ := 2797::ps406
private theorem c407 : F ps406 10012924=666970 := by decide +kernel
private theorem v407 : F ps407 28006150079=1988399627 :=
  takeStep (p:=2797) (by decide) v406 c407 rfl (by decide) (by decide) rfl

private def ps408 : List ℕ := 2801::ps407
private theorem c408 : F ps407 9998625=665973 := by decide +kernel
private theorem v408 : F ps408 28006150079=1987733654 :=
  takeStep (p:=2801) (by decide) v407 c408 rfl (by decide) (by decide) rfl

private def ps409 : List ℕ := 2803::ps408
private theorem c409 : F ps408 9991491=665423 := by decide +kernel
private theorem v409 : F ps409 28006150079=1987068231 :=
  takeStep (p:=2803) (by decide) v408 c409 rfl (by decide) (by decide) rfl

private def ps410 : List ℕ := 2819::ps409
private theorem c410 : F ps409 9934781=661775 := by decide +kernel
private theorem v410 : F ps410 28006150079=1986406456 :=
  takeStep (p:=2819) (by decide) v409 c410 rfl (by decide) (by decide) rfl

private def ps411 : List ℕ := 2833::ps410
private theorem c411 : F ps410 9885686=658582 := by decide +kernel
private theorem v411 : F ps411 28006150079=1985747874 :=
  takeStep (p:=2833) (by decide) v410 c411 rfl (by decide) (by decide) rfl

private def ps412 : List ℕ := 2837::ps411
private theorem c412 : F ps411 9871748=657627 := by decide +kernel
private theorem v412 : F ps412 28006150079=1985090247 :=
  takeStep (p:=2837) (by decide) v411 c412 rfl (by decide) (by decide) rfl

private def ps413 : List ℕ := 2843::ps412
private theorem c413 : F ps412 9850914=656239 := by decide +kernel
private theorem v413 : F ps413 28006150079=1984434008 :=
  takeStep (p:=2843) (by decide) v412 c413 rfl (by decide) (by decide) rfl

private def ps414 : List ℕ := 2851::ps413
private theorem c414 : F ps413 9823272=654443 := by decide +kernel
private theorem v414 : F ps414 28006150079=1983779565 :=
  takeStep (p:=2851) (by decide) v413 c414 rfl (by decide) (by decide) rfl

private def ps415 : List ℕ := 2857::ps414
private theorem c415 : F ps414 9802642=653057 := by decide +kernel
private theorem v415 : F ps415 28006150079=1983126508 :=
  takeStep (p:=2857) (by decide) v414 c415 rfl (by decide) (by decide) rfl

private def ps416 : List ℕ := 2861::ps415
private theorem c416 : F ps415 9788937=652098 := by decide +kernel
private theorem v416 : F ps416 28006150079=1982474410 :=
  takeStep (p:=2861) (by decide) v415 c416 rfl (by decide) (by decide) rfl

private def ps417 : List ℕ := 2879::ps416
private theorem c417 : F ps416 9727735=648170 := by decide +kernel
private theorem v417 : F ps417 28006150079=1981826240 :=
  takeStep (p:=2879) (by decide) v416 c417 rfl (by decide) (by decide) rfl

private def ps418 : List ℕ := 2887::ps417
private theorem c418 : F ps417 9700779=646415 := by decide +kernel
private theorem v418 : F ps418 28006150079=1981179825 :=
  takeStep (p:=2887) (by decide) v417 c418 rfl (by decide) (by decide) rfl

private def ps419 : List ℕ := 2897::ps418
private theorem c419 : F ps418 9667293=644257 := by decide +kernel
private theorem v419 : F ps419 28006150079=1980535568 :=
  takeStep (p:=2897) (by decide) v418 c419 rfl (by decide) (by decide) rfl

private def ps420 : List ℕ := 2903::ps419
private theorem c420 : F ps419 9647313=642934 := by decide +kernel
private theorem v420 : F ps420 28006150079=1979892634 :=
  takeStep (p:=2903) (by decide) v419 c420 rfl (by decide) (by decide) rfl

private def ps421 : List ℕ := 2909::ps420
private theorem c421 : F ps420 9627414=641629 := by decide +kernel
private theorem v421 : F ps421 28006150079=1979251005 :=
  takeStep (p:=2909) (by decide) v420 c421 rfl (by decide) (by decide) rfl

private def ps422 : List ℕ := 2917::ps421
private theorem c422 : F ps421 9601011=639923 := by decide +kernel
private theorem v422 : F ps422 28006150079=1978611082 :=
  takeStep (p:=2917) (by decide) v421 c422 rfl (by decide) (by decide) rfl

private def ps423 : List ℕ := 2927::ps422
private theorem c423 : F ps422 9568209=637770 := by decide +kernel
private theorem v423 : F ps423 28006150079=1977973312 :=
  takeStep (p:=2927) (by decide) v422 c423 rfl (by decide) (by decide) rfl

private def ps424 : List ℕ := 2939::ps423
private theorem c424 : F ps423 9529142=635269 := by decide +kernel
private theorem v424 : F ps424 28006150079=1977338043 :=
  takeStep (p:=2939) (by decide) v423 c424 rfl (by decide) (by decide) rfl

private def ps425 : List ℕ := 2953::ps424
private theorem c425 : F ps424 9483965=632401 := by decide +kernel
private theorem v425 : F ps425 28006150079=1976705642 :=
  takeStep (p:=2953) (by decide) v424 c425 rfl (by decide) (by decide) rfl

private def ps426 : List ℕ := 2957::ps425
private theorem c426 : F ps425 9471136=631575 := by decide +kernel
private theorem v426 : F ps426 28006150079=1976074067 :=
  takeStep (p:=2957) (by decide) v425 c426 rfl (by decide) (by decide) rfl

private def ps427 : List ℕ := 2963::ps426
private theorem c427 : F ps426 9451957=630364 := by decide +kernel
private theorem v427 : F ps427 28006150079=1975443703 :=
  takeStep (p:=2963) (by decide) v426 c427 rfl (by decide) (by decide) rfl

private def ps428 : List ℕ := 2969::ps427
private theorem c428 : F ps427 9432856=629139 := by decide +kernel
private theorem v428 : F ps428 28006150079=1974814564 :=
  takeStep (p:=2969) (by decide) v427 c428 rfl (by decide) (by decide) rfl

private def ps429 : List ℕ := 2971::ps428
private theorem c429 : F ps428 9426506=628722 := by decide +kernel
private theorem v429 : F ps429 28006150079=1974185842 :=
  takeStep (p:=2971) (by decide) v428 c429 rfl (by decide) (by decide) rfl

private def ps430 : List ℕ := 2999::ps429
private theorem c430 : F ps429 9338496=623214 := by decide +kernel
private theorem v430 : F ps430 28006150079=1973562628 :=
  takeStep (p:=2999) (by decide) v429 c430 rfl (by decide) (by decide) rfl

private def ps431 : List ℕ := 3001::ps430
private theorem c431 : F ps430 9332272=622796 := by decide +kernel
private theorem v431 : F ps431 28006150079=1972939832 :=
  takeStep (p:=3001) (by decide) v430 c431 rfl (by decide) (by decide) rfl

private def ps432 : List ℕ := 3011::ps431
private theorem c432 : F ps431 9301278=620856 := by decide +kernel
private theorem v432 : F ps432 28006150079=1972318976 :=
  takeStep (p:=3011) (by decide) v431 c432 rfl (by decide) (by decide) rfl

private def ps433 : List ℕ := 3019::ps432
private theorem c433 : F ps432 9276631=619303 := by decide +kernel
private theorem v433 : F ps433 28006150079=1971699673 :=
  takeStep (p:=3019) (by decide) v432 c433 rfl (by decide) (by decide) rfl

private def ps434 : List ℕ := 3023::ps433
private theorem c434 : F ps433 9264356=618523 := by decide +kernel
private theorem v434 : F ps434 28006150079=1971081150 :=
  takeStep (p:=3023) (by decide) v433 c434 rfl (by decide) (by decide) rfl

private theorem filter_from_test {bound : ℕ} (test : ℕ → Bool)
    (ok : ∀ n, n≤bound → (test n=true ↔ n.Prime)) (y : ℕ) (hy : y≤bound) :
    (List.range (y+1)).filter (fun n => decide n.Prime) =
      (List.range (y+1)).filter test := by
  apply List.filter_congr
  intro n member
  have nbound : n≤bound := by have := List.mem_range.mp member; omega
  by_cases hp : n.Prime
  · simp [hp,(ok n nbound).mpr hp]
  · have miss : test n=false := Bool.eq_false_iff.mpr (mt (ok n nbound).mp hp)
    simp [hp,miss]

private def l0_94 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89]
private theorem l0_94ok : (List.range' 0 94).filter prime = l0_94 :=
  by decide +kernel

private def l94_189 : List ℕ := [97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181]
private theorem l94_189ok : (List.range' 94 95).filter prime = l94_189 :=
  by decide +kernel

private def l0_189 : List ℕ := l0_94 ++ l94_189
private theorem l0_189ok : (List.range' 0 189).filter prime = l0_189 :=
  merge_filter _ 0 94 95 _ _ l0_94ok l94_189ok

private def l189_284 : List ℕ := [191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283]
private theorem l189_284ok : (List.range' 189 95).filter prime = l189_284 :=
  by decide +kernel

private def l284_379 : List ℕ := [293,307,311,313,317,331,337,347,349,353,359,367,373]
private theorem l284_379ok : (List.range' 284 95).filter prime = l284_379 :=
  by decide +kernel

private def l189_379 : List ℕ := l189_284 ++ l284_379
private theorem l189_379ok : (List.range' 189 190).filter prime = l189_379 :=
  merge_filter _ 189 95 95 _ _ l189_284ok l284_379ok

private def l0_379 : List ℕ := l0_189 ++ l189_379
private theorem l0_379ok : (List.range' 0 379).filter prime = l0_379 :=
  merge_filter _ 0 189 190 _ _ l0_189ok l189_379ok

private def l379_474 : List ℕ := [379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467]
private theorem l379_474ok : (List.range' 379 95).filter prime = l379_474 :=
  by decide +kernel

private def l474_569 : List ℕ := [479,487,491,499,503,509,521,523,541,547,557,563]
private theorem l474_569ok : (List.range' 474 95).filter prime = l474_569 :=
  by decide +kernel

private def l379_569 : List ℕ := l379_474 ++ l474_569
private theorem l379_569ok : (List.range' 379 190).filter prime = l379_569 :=
  merge_filter _ 379 95 95 _ _ l379_474ok l474_569ok

private def l569_664 : List ℕ := [569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661]
private theorem l569_664ok : (List.range' 569 95).filter prime = l569_664 :=
  by decide +kernel

private def l664_759 : List ℕ := [673,677,683,691,701,709,719,727,733,739,743,751,757]
private theorem l664_759ok : (List.range' 664 95).filter prime = l664_759 :=
  by decide +kernel

private def l569_759 : List ℕ := l569_664 ++ l664_759
private theorem l569_759ok : (List.range' 569 190).filter prime = l569_759 :=
  merge_filter _ 569 95 95 _ _ l569_664ok l664_759ok

private def l379_759 : List ℕ := l379_569 ++ l569_759
private theorem l379_759ok : (List.range' 379 380).filter prime = l379_759 :=
  merge_filter _ 379 190 190 _ _ l379_569ok l569_759ok

private def l0_759 : List ℕ := l0_379 ++ l379_759
private theorem l0_759ok : (List.range' 0 759).filter prime = l0_759 :=
  merge_filter _ 0 379 380 _ _ l0_379ok l379_759ok

private def l759_853 : List ℕ := [761,769,773,787,797,809,811,821,823,827,829,839]
private theorem l759_853ok : (List.range' 759 94).filter prime = l759_853 :=
  by decide +kernel

private def l853_948 : List ℕ := [853,857,859,863,877,881,883,887,907,911,919,929,937,941,947]
private theorem l853_948ok : (List.range' 853 95).filter prime = l853_948 :=
  by decide +kernel

private def l759_948 : List ℕ := l759_853 ++ l853_948
private theorem l759_948ok : (List.range' 759 189).filter prime = l759_948 :=
  merge_filter _ 759 94 95 _ _ l759_853ok l853_948ok

private def l948_1043 : List ℕ := [953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039]
private theorem l948_1043ok : (List.range' 948 95).filter prime = l948_1043 :=
  by decide +kernel

private def l1043_1138 : List ℕ := [1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129]
private theorem l1043_1138ok : (List.range' 1043 95).filter prime = l1043_1138 :=
  by decide +kernel

private def l948_1138 : List ℕ := l948_1043 ++ l1043_1138
private theorem l948_1138ok : (List.range' 948 190).filter prime = l948_1138 :=
  merge_filter _ 948 95 95 _ _ l948_1043ok l1043_1138ok

private def l759_1138 : List ℕ := l759_948 ++ l948_1138
private theorem l759_1138ok : (List.range' 759 379).filter prime = l759_1138 :=
  merge_filter _ 759 189 190 _ _ l759_948ok l948_1138ok

private def l1138_1233 : List ℕ := [1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231]
private theorem l1138_1233ok : (List.range' 1138 95).filter prime = l1138_1233 :=
  by decide +kernel

private def l1233_1328 : List ℕ := [1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327]
private theorem l1233_1328ok : (List.range' 1233 95).filter prime = l1233_1328 :=
  by decide +kernel

private def l1138_1328 : List ℕ := l1138_1233 ++ l1233_1328
private theorem l1138_1328ok : (List.range' 1138 190).filter prime = l1138_1328 :=
  merge_filter _ 1138 95 95 _ _ l1138_1233ok l1233_1328ok

private def l1328_1423 : List ℕ := [1361,1367,1373,1381,1399,1409]
private theorem l1328_1423ok : (List.range' 1328 95).filter prime = l1328_1423 :=
  by decide +kernel

private def l1423_1518 : List ℕ := [1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511]
private theorem l1423_1518ok : (List.range' 1423 95).filter prime = l1423_1518 :=
  by decide +kernel

private def l1328_1518 : List ℕ := l1328_1423 ++ l1423_1518
private theorem l1328_1518ok : (List.range' 1328 190).filter prime = l1328_1518 :=
  merge_filter _ 1328 95 95 _ _ l1328_1423ok l1423_1518ok

private def l1138_1518 : List ℕ := l1138_1328 ++ l1328_1518
private theorem l1138_1518ok : (List.range' 1138 380).filter prime = l1138_1518 :=
  merge_filter _ 1138 190 190 _ _ l1138_1328ok l1328_1518ok

private def l759_1518 : List ℕ := l759_1138 ++ l1138_1518
private theorem l759_1518ok : (List.range' 759 759).filter prime = l759_1518 :=
  merge_filter _ 759 379 380 _ _ l759_1138ok l1138_1518ok

private def l0_1518 : List ℕ := l0_759 ++ l759_1518
private theorem l0_1518ok : (List.range' 0 1518).filter prime = l0_1518 :=
  merge_filter _ 0 759 759 _ _ l0_759ok l759_1518ok

private def l1518_1612 : List ℕ := [1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609]
private theorem l1518_1612ok : (List.range' 1518 94).filter prime = l1518_1612 :=
  by decide +kernel

private def l1612_1707 : List ℕ := [1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699]
private theorem l1612_1707ok : (List.range' 1612 95).filter prime = l1612_1707 :=
  by decide +kernel

private def l1518_1707 : List ℕ := l1518_1612 ++ l1612_1707
private theorem l1518_1707ok : (List.range' 1518 189).filter prime = l1518_1707 :=
  merge_filter _ 1518 94 95 _ _ l1518_1612ok l1612_1707ok

private def l1707_1802 : List ℕ := [1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801]
private theorem l1707_1802ok : (List.range' 1707 95).filter prime = l1707_1802 :=
  by decide +kernel

private def l1802_1897 : List ℕ := [1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889]
private theorem l1802_1897ok : (List.range' 1802 95).filter prime = l1802_1897 :=
  by decide +kernel

private def l1707_1897 : List ℕ := l1707_1802 ++ l1802_1897
private theorem l1707_1897ok : (List.range' 1707 190).filter prime = l1707_1897 :=
  merge_filter _ 1707 95 95 _ _ l1707_1802ok l1802_1897ok

private def l1518_1897 : List ℕ := l1518_1707 ++ l1707_1897
private theorem l1518_1897ok : (List.range' 1518 379).filter prime = l1518_1897 :=
  merge_filter _ 1518 189 190 _ _ l1518_1707ok l1707_1897ok

private def l1897_1992 : List ℕ := [1901,1907,1913,1931,1933,1949,1951,1973,1979,1987]
private theorem l1897_1992ok : (List.range' 1897 95).filter prime = l1897_1992 :=
  by decide +kernel

private def l1992_2087 : List ℕ := [1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083]
private theorem l1992_2087ok : (List.range' 1992 95).filter prime = l1992_2087 :=
  by decide +kernel

private def l1897_2087 : List ℕ := l1897_1992 ++ l1992_2087
private theorem l1897_2087ok : (List.range' 1897 190).filter prime = l1897_2087 :=
  merge_filter _ 1897 95 95 _ _ l1897_1992ok l1992_2087ok

private def l2087_2182 : List ℕ := [2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179]
private theorem l2087_2182ok : (List.range' 2087 95).filter prime = l2087_2182 :=
  by decide +kernel

private def l2182_2277 : List ℕ := [2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273]
private theorem l2182_2277ok : (List.range' 2182 95).filter prime = l2182_2277 :=
  by decide +kernel

private def l2087_2277 : List ℕ := l2087_2182 ++ l2182_2277
private theorem l2087_2277ok : (List.range' 2087 190).filter prime = l2087_2277 :=
  merge_filter _ 2087 95 95 _ _ l2087_2182ok l2182_2277ok

private def l1897_2277 : List ℕ := l1897_2087 ++ l2087_2277
private theorem l1897_2277ok : (List.range' 1897 380).filter prime = l1897_2277 :=
  merge_filter _ 1897 190 190 _ _ l1897_2087ok l2087_2277ok

private def l1518_2277 : List ℕ := l1518_1897 ++ l1897_2277
private theorem l1518_2277ok : (List.range' 1518 759).filter prime = l1518_2277 :=
  merge_filter _ 1518 379 380 _ _ l1518_1897ok l1897_2277ok

private def l2277_2372 : List ℕ := [2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371]
private theorem l2277_2372ok : (List.range' 2277 95).filter prime = l2277_2372 :=
  by decide +kernel

private def l2372_2467 : List ℕ := [2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459]
private theorem l2372_2467ok : (List.range' 2372 95).filter prime = l2372_2467 :=
  by decide +kernel

private def l2277_2467 : List ℕ := l2277_2372 ++ l2372_2467
private theorem l2277_2467ok : (List.range' 2277 190).filter prime = l2277_2467 :=
  merge_filter _ 2277 95 95 _ _ l2277_2372ok l2372_2467ok

private def l2467_2562 : List ℕ := [2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557]
private theorem l2467_2562ok : (List.range' 2467 95).filter prime = l2467_2562 :=
  by decide +kernel

private def l2562_2657 : List ℕ := [2579,2591,2593,2609,2617,2621,2633,2647]
private theorem l2562_2657ok : (List.range' 2562 95).filter prime = l2562_2657 :=
  by decide +kernel

private def l2467_2657 : List ℕ := l2467_2562 ++ l2562_2657
private theorem l2467_2657ok : (List.range' 2467 190).filter prime = l2467_2657 :=
  merge_filter _ 2467 95 95 _ _ l2467_2562ok l2562_2657ok

private def l2277_2657 : List ℕ := l2277_2467 ++ l2467_2657
private theorem l2277_2657ok : (List.range' 2277 380).filter prime = l2277_2657 :=
  merge_filter _ 2277 190 190 _ _ l2277_2467ok l2467_2657ok

private def l2657_2752 : List ℕ := [2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749]
private theorem l2657_2752ok : (List.range' 2657 95).filter prime = l2657_2752 :=
  by decide +kernel

private def l2752_2847 : List ℕ := [2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843]
private theorem l2752_2847ok : (List.range' 2752 95).filter prime = l2752_2847 :=
  by decide +kernel

private def l2657_2847 : List ℕ := l2657_2752 ++ l2752_2847
private theorem l2657_2847ok : (List.range' 2657 190).filter prime = l2657_2847 :=
  merge_filter _ 2657 95 95 _ _ l2657_2752ok l2752_2847ok

private def l2847_2942 : List ℕ := [2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939]
private theorem l2847_2942ok : (List.range' 2847 95).filter prime = l2847_2942 :=
  by decide +kernel

private def l2942_3037 : List ℕ := [2953,2957,2963,2969,2971,2999,3001,3011,3019,3023]
private theorem l2942_3037ok : (List.range' 2942 95).filter prime = l2942_3037 :=
  by decide +kernel

private def l2847_3037 : List ℕ := l2847_2942 ++ l2942_3037
private theorem l2847_3037ok : (List.range' 2847 190).filter prime = l2847_3037 :=
  merge_filter _ 2847 95 95 _ _ l2847_2942ok l2942_3037ok

private def l2657_3037 : List ℕ := l2657_2847 ++ l2847_3037
private theorem l2657_3037ok : (List.range' 2657 380).filter prime = l2657_3037 :=
  merge_filter _ 2657 190 190 _ _ l2657_2847ok l2847_3037ok

private def l2277_3037 : List ℕ := l2277_2657 ++ l2657_3037
private theorem l2277_3037ok : (List.range' 2277 760).filter prime = l2277_3037 :=
  merge_filter _ 2277 380 380 _ _ l2277_2657ok l2657_3037ok

private def l1518_3037 : List ℕ := l1518_2277 ++ l2277_3037
private theorem l1518_3037ok : (List.range' 1518 1519).filter prime = l1518_3037 :=
  merge_filter _ 1518 759 760 _ _ l1518_2277ok l2277_3037ok

private def l0_3037 : List ℕ := l0_1518 ++ l1518_3037
private theorem l0_3037ok : (List.range' 0 3037).filter prime = l0_3037 :=
  merge_filter _ 0 1518 1519 _ _ l0_1518ok l1518_3037ok

set_option maxRecDepth 8000 in
private theorem last_row :
    ((List.range (3036+1)).filter (fun p => decide p.Prime)).reverse = ps434 := by
  rw [filter_from_test prime prime_ok 3036 (by decide),List.range_eq_range',l0_3037ok]
  rfl

private theorem left_from_rows {bound x y val total : ℕ} (tab : ℕ → ℕ)
    (ok : ∀ t, t ≤ bound → tab t = Nat.primeCounting t) (ps : List ℕ)
    (cap : (y+1)^2 ≤ bound+1) (yb : y ≤ bound)
    (row : ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse = ps)
    (value : evalPhi tab ps x = val) (sum : val+tab y=total) :
    (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id x) +
      (Nat.primesLE y).card = total := by
  rw [agree_range tab ok y cap,row,value,Nat.primesLE_card_eq_primeCounting,←ok y yb,sum]

set_option maxRecDepth 8000 in
private theorem left_part :
    (((List.range (3036+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id 28006150079) +
    (Nat.primesLE 3036).card = 1971081584 := by
  exact left_from_rows tab HybridBound28006.fast_correct ps434 (by decide) (by decide) last_row (show evalPhi tab ps434 28006150079 = 1971081150 from v434) (by decide +kernel)

private abbrev term := contribution 28006150079 3036 tab prime

private theorem s0 : blockSum term 0 326 0 := by unfold blockSum; decide +kernel

private theorem s326 : blockSum term 326 327 0 := by unfold blockSum; decide +kernel

private theorem s653 : blockSum term 653 327 0 := by unfold blockSum; decide +kernel

private theorem s980 : blockSum term 980 327 0 := by unfold blockSum; decide +kernel

private theorem s1307 : blockSum term 1307 326 0 := by unfold blockSum; decide +kernel

private theorem s1633 : blockSum term 1633 327 0 := by unfold blockSum; decide +kernel

private theorem s1960 : blockSum term 1960 327 0 := by unfold blockSum; decide +kernel

private theorem s2287 : blockSum term 2287 327 0 := by unfold blockSum; decide +kernel

private theorem s2614 : blockSum term 2614 326 0 := by unfold blockSum; decide +kernel

private theorem s2940 : blockSum term 2940 327 16060285 := by unfold blockSum; decide +kernel

private theorem s3267 : blockSum term 3267 327 23047323 := by unfold blockSum; decide +kernel

private theorem s3594 : blockSum term 3594 327 20188544 := by unfold blockSum; decide +kernel

private theorem s3921 : blockSum term 3921 327 18210648 := by unfold blockSum; decide +kernel

private theorem s4248 : blockSum term 4248 327 16087560 := by unfold blockSum; decide +kernel

private theorem s4575 : blockSum term 4575 327 14266142 := by unfold blockSum; decide +kernel

private theorem s4902 : blockSum term 4902 327 15332730 := by unfold blockSum; decide +kernel

private theorem s5229 : blockSum term 5229 326 13690123 := by unfold blockSum; decide +kernel

private theorem s5555 : blockSum term 5555 327 14638287 := by unfold blockSum; decide +kernel

private theorem s5882 : blockSum term 5882 327 10337525 := by unfold blockSum; decide +kernel

private theorem s6209 : blockSum term 6209 327 11441247 := by unfold blockSum; decide +kernel

private theorem s6536 : blockSum term 6536 327 11185023 := by unfold blockSum; decide +kernel

private theorem s6863 : blockSum term 6863 327 10149489 := by unfold blockSum; decide +kernel

private theorem s7190 : blockSum term 7190 327 8906521 := by unfold blockSum; decide +kernel

private theorem s7517 : blockSum term 7517 327 10381440 := by unfold blockSum; decide +kernel

private theorem s7844 : blockSum term 7844 326 8469585 := by unfold blockSum; decide +kernel

private theorem s8170 : blockSum term 8170 327 8170967 := by unfold blockSum; decide +kernel

private theorem s8497 : blockSum term 8497 327 9253702 := by unfold blockSum; decide +kernel

private theorem s8824 : blockSum term 8824 327 7604060 := by unfold blockSum; decide +kernel

private theorem s9151 : blockSum term 9151 327 8857443 := by unfold blockSum; decide +kernel

private theorem s9478 : blockSum term 9478 327 7317803 := by unfold blockSum; decide +kernel

private theorem s9805 : blockSum term 9805 327 6699409 := by unfold blockSum; decide +kernel

private theorem s10132 : blockSum term 10132 327 7288817 := by unfold blockSum; decide +kernel

private theorem s10459 : blockSum term 10459 326 6496056 := by unfold blockSum; decide +kernel

private theorem s10785 : blockSum term 10785 327 5942661 := by unfold blockSum; decide +kernel

private theorem s11112 : blockSum term 11112 327 6145776 := by unfold blockSum; decide +kernel

private theorem s11439 : blockSum term 11439 327 5280880 := by unfold blockSum; decide +kernel

private theorem s11766 : blockSum term 11766 326 6345765 := by unfold blockSum; decide +kernel

private theorem s12092 : blockSum term 12092 327 6016197 := by unfold blockSum; decide +kernel

private theorem s12419 : blockSum term 12419 327 6356615 := by unfold blockSum; decide +kernel

private theorem s12746 : blockSum term 12746 327 5563714 := by unfold blockSum; decide +kernel

private theorem s13073 : blockSum term 13073 326 4973051 := by unfold blockSum; decide +kernel

private theorem s13399 : blockSum term 13399 327 5461269 := by unfold blockSum; decide +kernel

private theorem s13726 : blockSum term 13726 327 4899239 := by unfold blockSum; decide +kernel

private theorem s14053 : blockSum term 14053 327 3921555 := by unfold blockSum; decide +kernel

private theorem s14380 : blockSum term 14380 327 5120078 := by unfold blockSum; decide +kernel

private theorem s14707 : blockSum term 14707 327 5154954 := by unfold blockSum; decide +kernel

private theorem s15034 : blockSum term 15034 327 5039214 := by unfold blockSum; decide +kernel

private theorem s15361 : blockSum term 15361 327 4938792 := by unfold blockSum; decide +kernel

private theorem s15688 : blockSum term 15688 326 4319863 := by unfold blockSum; decide +kernel

private theorem s16014 : blockSum term 16014 327 3982300 := by unfold blockSum; decide +kernel

private theorem s16341 : blockSum term 16341 327 4157473 := by unfold blockSum; decide +kernel

private theorem s16668 : blockSum term 16668 327 3954762 := by unfold blockSum; decide +kernel

private theorem s16995 : blockSum term 16995 327 3765223 := by unfold blockSum; decide +kernel

private theorem s17322 : blockSum term 17322 327 4295884 := by unfold blockSum; decide +kernel

private theorem s17649 : blockSum term 17649 327 3866028 := by unfold blockSum; decide +kernel

private theorem s17976 : blockSum term 17976 327 4260833 := by unfold blockSum; decide +kernel

private theorem s18303 : blockSum term 18303 326 3626389 := by unfold blockSum; decide +kernel

private theorem s18629 : blockSum term 18629 327 2895568 := by unfold blockSum; decide +kernel

private theorem s18956 : blockSum term 18956 327 3393760 := by unfold blockSum; decide +kernel

private theorem s19283 : blockSum term 19283 327 4198981 := by unfold blockSum; decide +kernel

private theorem s19610 : blockSum term 19610 327 2965711 := by unfold blockSum; decide +kernel

private theorem s19937 : blockSum term 19937 327 3863014 := by unfold blockSum; decide +kernel

private theorem s20264 : blockSum term 20264 327 3186036 := by unfold blockSum; decide +kernel

private theorem s20591 : blockSum term 20591 327 3136688 := by unfold blockSum; decide +kernel

private theorem s20918 : blockSum term 20918 326 3489324 := by unfold blockSum; decide +kernel

private theorem s21244 : blockSum term 21244 327 3336657 := by unfold blockSum; decide +kernel

private theorem s21571 : blockSum term 21571 327 3387380 := by unfold blockSum; decide +kernel

private theorem s21898 : blockSum term 21898 327 3147672 := by unfold blockSum; decide +kernel

private theorem s22225 : blockSum term 22225 326 3008818 := by unfold blockSum; decide +kernel

private theorem s22551 : blockSum term 22551 327 3151402 := by unfold blockSum; decide +kernel

private theorem s22878 : blockSum term 22878 327 3198838 := by unfold blockSum; decide +kernel

private theorem s23205 : blockSum term 23205 327 2256316 := by unfold blockSum; decide +kernel

private theorem s23532 : blockSum term 23532 326 3383514 := by unfold blockSum; decide +kernel

private theorem s23858 : blockSum term 23858 327 3423470 := by unfold blockSum; decide +kernel

private theorem s24185 : blockSum term 24185 327 2337727 := by unfold blockSum; decide +kernel

private theorem s24512 : blockSum term 24512 327 2223521 := by unfold blockSum; decide +kernel

private theorem s24839 : blockSum term 24839 327 2701827 := by unfold blockSum; decide +kernel

private theorem s25166 : blockSum term 25166 327 2750135 := by unfold blockSum; decide +kernel

private theorem s25493 : blockSum term 25493 327 2631907 := by unfold blockSum; decide +kernel

private theorem s25820 : blockSum term 25820 327 2519071 := by unfold blockSum; decide +kernel

private theorem s26147 : blockSum term 26147 326 2729405 := by unfold blockSum; decide +kernel

private theorem s26473 : blockSum term 26473 327 2537024 := by unfold blockSum; decide +kernel

private theorem s26800 : blockSum term 26800 327 2743018 := by unfold blockSum; decide +kernel

private theorem s27127 : blockSum term 27127 327 2012803 := by unfold blockSum; decide +kernel

private theorem s27454 : blockSum term 27454 327 2447147 := by unfold blockSum; decide +kernel

private theorem s27781 : blockSum term 27781 327 2571387 := by unfold blockSum; decide +kernel

private theorem s28108 : blockSum term 28108 327 2092289 := by unfold blockSum; decide +kernel

private theorem s28435 : blockSum term 28435 327 2881654 := by unfold blockSum; decide +kernel

private theorem s28762 : blockSum term 28762 326 2119474 := by unfold blockSum; decide +kernel

private theorem s29088 : blockSum term 29088 327 2456424 := by unfold blockSum; decide +kernel

private theorem s29415 : blockSum term 29415 327 2001609 := by unfold blockSum; decide +kernel

private theorem s29742 : blockSum term 29742 327 1838624 := by unfold blockSum; decide +kernel

private theorem s30069 : blockSum term 30069 327 2379064 := by unfold blockSum; decide +kernel

private theorem s30396 : blockSum term 30396 327 2074634 := by unfold blockSum; decide +kernel

private theorem s30723 : blockSum term 30723 327 2053413 := by unfold blockSum; decide +kernel

private theorem s31050 : blockSum term 31050 327 2438597 := by unfold blockSum; decide +kernel

private theorem s31377 : blockSum term 31377 326 1943134 := by unfold blockSum; decide +kernel

private theorem s31703 : blockSum term 31703 327 1790604 := by unfold blockSum; decide +kernel

private theorem s32030 : blockSum term 32030 327 2231503 := by unfold blockSum; decide +kernel

private theorem s32357 : blockSum term 32357 327 2274457 := by unfold blockSum; decide +kernel

private theorem s32684 : blockSum term 32684 327 2121331 := by unfold blockSum; decide +kernel

private theorem s33011 : blockSum term 33011 327 1973487 := by unfold blockSum; decide +kernel

private theorem s33338 : blockSum term 33338 327 2394089 := by unfold blockSum; decide +kernel

private theorem s33665 : blockSum term 33665 327 1871830 := by unfold blockSum; decide +kernel

private theorem s33992 : blockSum term 33992 326 1851873 := by unfold blockSum; decide +kernel

private theorem s34318 : blockSum term 34318 327 1957509 := by unfold blockSum; decide +kernel

private theorem s34645 : blockSum term 34645 327 1938943 := by unfold blockSum; decide +kernel

private theorem s34972 : blockSum term 34972 327 1739543 := by unfold blockSum; decide +kernel

private theorem s35299 : blockSum term 35299 327 1960450 := by unfold blockSum; decide +kernel

private theorem s35626 : blockSum term 35626 327 1469990 := by unfold blockSum; decide +kernel

private theorem s35953 : blockSum term 35953 327 1865960 := by unfold blockSum; decide +kernel

private theorem s36280 : blockSum term 36280 327 1789960 := by unfold blockSum; decide +kernel

private theorem s36607 : blockSum term 36607 326 2115947 := by unfold blockSum; decide +kernel

private theorem s36933 : blockSum term 36933 327 1586941 := by unfold blockSum; decide +kernel

private theorem s37260 : blockSum term 37260 327 1964563 := by unfold blockSum; decide +kernel

private theorem s37587 : blockSum term 37587 327 1558669 := by unfold blockSum; decide +kernel

private theorem s37914 : blockSum term 37914 327 1544046 := by unfold blockSum; decide +kernel

private theorem s38241 : blockSum term 38241 327 1421990 := by unfold blockSum; decide +kernel

private theorem s38568 : blockSum term 38568 327 1842590 := by unfold blockSum; decide +kernel

private theorem s38895 : blockSum term 38895 327 1718328 := by unfold blockSum; decide +kernel

private theorem s39222 : blockSum term 39222 326 1650984 := by unfold blockSum; decide +kernel

private theorem s39548 : blockSum term 39548 327 1687851 := by unfold blockSum; decide +kernel

private theorem s39875 : blockSum term 39875 327 1621086 := by unfold blockSum; decide +kernel

private theorem s40202 : blockSum term 40202 327 1295981 := by unfold blockSum; decide +kernel

private theorem s40529 : blockSum term 40529 327 1593343 := by unfold blockSum; decide +kernel

private theorem s40856 : blockSum term 40856 327 1528953 := by unfold blockSum; decide +kernel

private theorem s41183 : blockSum term 41183 327 1567347 := by unfold blockSum; decide +kernel

private theorem s41510 : blockSum term 41510 327 1604172 := by unfold blockSum; decide +kernel

private theorem s41837 : blockSum term 41837 326 1690165 := by unfold blockSum; decide +kernel

private theorem s42163 : blockSum term 42163 327 1921125 := by unfold blockSum; decide +kernel

private theorem s42490 : blockSum term 42490 327 1514142 := by unfold blockSum; decide +kernel

private theorem s42817 : blockSum term 42817 327 1453908 := by unfold blockSum; decide +kernel

private theorem s43144 : blockSum term 43144 326 1201339 := by unfold blockSum; decide +kernel

private theorem s43470 : blockSum term 43470 327 1524660 := by unfold blockSum; decide +kernel

private theorem s43797 : blockSum term 43797 327 1417759 := by unfold blockSum; decide +kernel

private theorem s44124 : blockSum term 44124 327 1267035 := by unfold blockSum; decide +kernel

private theorem s44451 : blockSum term 44451 326 1535902 := by unfold blockSum; decide +kernel

private theorem s44777 : blockSum term 44777 327 1293578 := by unfold blockSum; decide +kernel

private theorem s45104 : blockSum term 45104 327 1420536 := by unfold blockSum; decide +kernel

private theorem s45431 : blockSum term 45431 327 1272455 := by unfold blockSum; decide +kernel

private theorem s45758 : blockSum term 45758 327 1217725 := by unfold blockSum; decide +kernel

private theorem s46085 : blockSum term 46085 327 1342455 := by unfold blockSum; decide +kernel

private theorem s46412 : blockSum term 46412 327 1420276 := by unfold blockSum; decide +kernel

private theorem s46739 : blockSum term 46739 327 1189544 := by unfold blockSum; decide +kernel

private theorem s47066 : blockSum term 47066 326 1354317 := by unfold blockSum; decide +kernel

private theorem s47392 : blockSum term 47392 327 1430783 := by unfold blockSum; decide +kernel

private theorem s47719 : blockSum term 47719 327 1247718 := by unfold blockSum; decide +kernel

private theorem s48046 : blockSum term 48046 327 1152710 := by unfold blockSum; decide +kernel

private theorem s48373 : blockSum term 48373 327 1355836 := by unfold blockSum; decide +kernel

private theorem s48700 : blockSum term 48700 327 1261438 := by unfold blockSum; decide +kernel

private theorem s49027 : blockSum term 49027 327 1335344 := by unfold blockSum; decide +kernel

private theorem s49354 : blockSum term 49354 327 1325166 := by unfold blockSum; decide +kernel

private theorem s49681 : blockSum term 49681 326 1274134 := by unfold blockSum; decide +kernel

private theorem s50007 : blockSum term 50007 327 1346175 := by unfold blockSum; decide +kernel

private theorem s50334 : blockSum term 50334 327 1133723 := by unfold blockSum; decide +kernel

private theorem s50661 : blockSum term 50661 327 1044846 := by unfold blockSum; decide +kernel

private theorem s50988 : blockSum term 50988 327 1157030 := by unfold blockSum; decide +kernel

private theorem s51315 : blockSum term 51315 327 1426003 := by unfold blockSum; decide +kernel

private theorem s51642 : blockSum term 51642 327 1179648 := by unfold blockSum; decide +kernel

private theorem s51969 : blockSum term 51969 327 1210110 := by unfold blockSum; decide +kernel

private theorem s52296 : blockSum term 52296 326 1007511 := by unfold blockSum; decide +kernel

private theorem s52622 : blockSum term 52622 327 1116129 := by unfold blockSum; decide +kernel

private theorem s52949 : blockSum term 52949 327 1261019 := by unfold blockSum; decide +kernel

private theorem s53276 : blockSum term 53276 327 1024077 := by unfold blockSum; decide +kernel

private theorem s53603 : blockSum term 53603 327 1280165 := by unfold blockSum; decide +kernel

private theorem s53930 : blockSum term 53930 327 897245 := by unfold blockSum; decide +kernel

private theorem s54257 : blockSum term 54257 327 1372482 := by unfold blockSum; decide +kernel

private theorem s54584 : blockSum term 54584 327 957889 := by unfold blockSum; decide +kernel

private theorem s54911 : blockSum term 54911 326 1097471 := by unfold blockSum; decide +kernel

private theorem s55237 : blockSum term 55237 327 908318 := by unfold blockSum; decide +kernel

private theorem s55564 : blockSum term 55564 327 1262623 := by unfold blockSum; decide +kernel

private theorem s55891 : blockSum term 55891 327 1110535 := by unfold blockSum; decide +kernel

private theorem s56218 : blockSum term 56218 327 1173130 := by unfold blockSum; decide +kernel

private theorem s56545 : blockSum term 56545 327 1023772 := by unfold blockSum; decide +kernel

private theorem s56872 : blockSum term 56872 327 1262357 := by unfold blockSum; decide +kernel

private theorem s57199 : blockSum term 57199 327 940229 := by unfold blockSum; decide +kernel

private theorem s57526 : blockSum term 57526 326 1140735 := by unfold blockSum; decide +kernel

private theorem s57852 : blockSum term 57852 327 1030122 := by unfold blockSum; decide +kernel

private theorem s58179 : blockSum term 58179 327 1057373 := by unfold blockSum; decide +kernel

private theorem s58506 : blockSum term 58506 327 914512 := by unfold blockSum; decide +kernel

private theorem s58833 : blockSum term 58833 327 1109335 := by unfold blockSum; decide +kernel

private theorem s59160 : blockSum term 59160 327 1101808 := by unfold blockSum; decide +kernel

private theorem s59487 : blockSum term 59487 327 1027669 := by unfold blockSum; decide +kernel

private theorem s59814 : blockSum term 59814 327 855509 := by unfold blockSum; decide +kernel

private theorem s60141 : blockSum term 60141 326 850322 := by unfold blockSum; decide +kernel

private theorem s60467 : blockSum term 60467 327 1006699 := by unfold blockSum; decide +kernel

private theorem s60794 : blockSum term 60794 327 807052 := by unfold blockSum; decide +kernel

private theorem s61121 : blockSum term 61121 327 833861 := by unfold blockSum; decide +kernel

private theorem s61448 : blockSum term 61448 327 1083230 := by unfold blockSum; decide +kernel

private theorem s61775 : blockSum term 61775 327 886045 := by unfold blockSum; decide +kernel

private theorem s62102 : blockSum term 62102 327 848947 := by unfold blockSum; decide +kernel

private theorem s62429 : blockSum term 62429 327 905727 := by unfold blockSum; decide +kernel

private theorem s62756 : blockSum term 62756 326 869002 := by unfold blockSum; decide +kernel

private theorem s63082 : blockSum term 63082 327 862731 := by unfold blockSum; decide +kernel

private theorem s63409 : blockSum term 63409 327 1132505 := by unfold blockSum; decide +kernel

private theorem s63736 : blockSum term 63736 327 821268 := by unfold blockSum; decide +kernel

private theorem s64063 : blockSum term 64063 326 785820 := by unfold blockSum; decide +kernel

private theorem s64389 : blockSum term 64389 327 810223 := by unfold blockSum; decide +kernel

private theorem s64716 : blockSum term 64716 327 804609 := by unfold blockSum; decide +kernel

private theorem s65043 : blockSum term 65043 327 888323 := by unfold blockSum; decide +kernel

private theorem s65370 : blockSum term 65370 326 970447 := by unfold blockSum; decide +kernel

private theorem s65696 : blockSum term 65696 327 876915 := by unfold blockSum; decide +kernel

private theorem s66023 : blockSum term 66023 327 725952 := by unfold blockSum; decide +kernel

private theorem s66350 : blockSum term 66350 327 836500 := by unfold blockSum; decide +kernel

private theorem s66677 : blockSum term 66677 327 888199 := by unfold blockSum; decide +kernel

private theorem s67004 : blockSum term 67004 327 853852 := by unfold blockSum; decide +kernel

private theorem s67331 : blockSum term 67331 327 961248 := by unfold blockSum; decide +kernel

private theorem s67658 : blockSum term 67658 327 898546 := by unfold blockSum; decide +kernel

private theorem s67985 : blockSum term 67985 326 669757 := by unfold blockSum; decide +kernel

private theorem s68311 : blockSum term 68311 327 720739 := by unfold blockSum; decide +kernel

private theorem s68638 : blockSum term 68638 327 853787 := by unfold blockSum; decide +kernel

private theorem s68965 : blockSum term 68965 327 738865 := by unfold blockSum; decide +kernel

private theorem s69292 : blockSum term 69292 327 680255 := by unfold blockSum; decide +kernel

private theorem s69619 : blockSum term 69619 327 729869 := by unfold blockSum; decide +kernel

private theorem s69946 : blockSum term 69946 327 886492 := by unfold blockSum; decide +kernel

private theorem s70273 : blockSum term 70273 327 773962 := by unfold blockSum; decide +kernel

private theorem s70600 : blockSum term 70600 326 769118 := by unfold blockSum; decide +kernel

private theorem s70926 : blockSum term 70926 327 790784 := by unfold blockSum; decide +kernel

private theorem s71253 : blockSum term 71253 327 942330 := by unfold blockSum; decide +kernel

private theorem s71580 : blockSum term 71580 327 727597 := by unfold blockSum; decide +kernel

private theorem s71907 : blockSum term 71907 327 852092 := by unfold blockSum; decide +kernel

private theorem s72234 : blockSum term 72234 327 692888 := by unfold blockSum; decide +kernel

private theorem s72561 : blockSum term 72561 327 688547 := by unfold blockSum; decide +kernel

private theorem s72888 : blockSum term 72888 327 760476 := by unfold blockSum; decide +kernel

private theorem s73215 : blockSum term 73215 326 654530 := by unfold blockSum; decide +kernel

private theorem s73541 : blockSum term 73541 327 775782 := by unfold blockSum; decide +kernel

private theorem s73868 : blockSum term 73868 327 695935 := by unfold blockSum; decide +kernel

private theorem s74195 : blockSum term 74195 327 765906 := by unfold blockSum; decide +kernel

private theorem s74522 : blockSum term 74522 327 736165 := by unfold blockSum; decide +kernel

private theorem s74849 : blockSum term 74849 327 658450 := by unfold blockSum; decide +kernel

private theorem s75176 : blockSum term 75176 327 678633 := by unfold blockSum; decide +kernel

private theorem s75503 : blockSum term 75503 327 842974 := by unfold blockSum; decide +kernel

private theorem s75830 : blockSum term 75830 326 622393 := by unfold blockSum; decide +kernel

private theorem s76156 : blockSum term 76156 327 642391 := by unfold blockSum; decide +kernel

private theorem s76483 : blockSum term 76483 327 661916 := by unfold blockSum; decide +kernel

private theorem s76810 : blockSum term 76810 327 610801 := by unfold blockSum; decide +kernel

private theorem s77137 : blockSum term 77137 327 723596 := by unfold blockSum; decide +kernel

private theorem s77464 : blockSum term 77464 327 881080 := by unfold blockSum; decide +kernel

private theorem s77791 : blockSum term 77791 327 553197 := by unfold blockSum; decide +kernel

private theorem s78118 : blockSum term 78118 327 641360 := by unfold blockSum; decide +kernel

private theorem s78445 : blockSum term 78445 326 591934 := by unfold blockSum; decide +kernel

private theorem s78771 : blockSum term 78771 327 611137 := by unfold blockSum; decide +kernel

private theorem s79098 : blockSum term 79098 327 741569 := by unfold blockSum; decide +kernel

private theorem s79425 : blockSum term 79425 327 580523 := by unfold blockSum; decide +kernel

private theorem s79752 : blockSum term 79752 327 709950 := by unfold blockSum; decide +kernel

private theorem s80079 : blockSum term 80079 327 639216 := by unfold blockSum; decide +kernel

private theorem s80406 : blockSum term 80406 327 635003 := by unfold blockSum; decide +kernel

private theorem s80733 : blockSum term 80733 327 761400 := by unfold blockSum; decide +kernel

private theorem s81060 : blockSum term 81060 326 626774 := by unfold blockSum; decide +kernel

private theorem s81386 : blockSum term 81386 327 622590 := by unfold blockSum; decide +kernel

private theorem s81713 : blockSum term 81713 327 682580 := by unfold blockSum; decide +kernel

private theorem s82040 : blockSum term 82040 327 593485 := by unfold blockSum; decide +kernel

private theorem s82367 : blockSum term 82367 327 590018 := by unfold blockSum; decide +kernel

private theorem s82694 : blockSum term 82694 327 565612 := by unfold blockSum; decide +kernel

private theorem s83021 : blockSum term 83021 327 582569 := by unfold blockSum; decide +kernel

private theorem s83348 : blockSum term 83348 327 620263 := by unfold blockSum; decide +kernel

private theorem s83675 : blockSum term 83675 326 493058 := by unfold blockSum; decide +kernel

private theorem s84001 : blockSum term 84001 327 612447 := by unfold blockSum; decide +kernel

private theorem s84328 : blockSum term 84328 327 588416 := by unfold blockSum; decide +kernel

private theorem s84655 : blockSum term 84655 327 544286 := by unfold blockSum; decide +kernel

private theorem s84982 : blockSum term 84982 326 580842 := by unfold blockSum; decide +kernel

private theorem s85308 : blockSum term 85308 327 577048 := by unfold blockSum; decide +kernel

private theorem s85635 : blockSum term 85635 327 514234 := by unfold blockSum; decide +kernel

private theorem s85962 : blockSum term 85962 327 569568 := by unfold blockSum; decide +kernel

private theorem s86289 : blockSum term 86289 326 624567 := by unfold blockSum; decide +kernel

private theorem s86615 : blockSum term 86615 327 465377 := by unfold blockSum; decide +kernel

private theorem s86942 : blockSum term 86942 327 539594 := by unfold blockSum; decide +kernel

private theorem s87269 : blockSum term 87269 327 612566 := by unfold blockSum; decide +kernel

private theorem s87596 : blockSum term 87596 327 589536 := by unfold blockSum; decide +kernel

private theorem s87923 : blockSum term 87923 327 434555 := by unfold blockSum; decide +kernel

private theorem s88250 : blockSum term 88250 327 394192 := by unfold blockSum; decide +kernel

private theorem s88577 : blockSum term 88577 327 615146 := by unfold blockSum; decide +kernel

private theorem s88904 : blockSum term 88904 326 537212 := by unfold blockSum; decide +kernel

private theorem s89230 : blockSum term 89230 327 533602 := by unfold blockSum; decide +kernel

private theorem s89557 : blockSum term 89557 327 548506 := by unfold blockSum; decide +kernel

private theorem s89884 : blockSum term 89884 327 653788 := by unfold blockSum; decide +kernel

private theorem s90211 : blockSum term 90211 327 523123 := by unfold blockSum; decide +kernel

private theorem s90538 : blockSum term 90538 327 448043 := by unfold blockSum; decide +kernel

private theorem s90865 : blockSum term 90865 327 498804 := by unfold blockSum; decide +kernel

private theorem s91192 : blockSum term 91192 327 531022 := by unfold blockSum; decide +kernel

private theorem s91519 : blockSum term 91519 326 457132 := by unfold blockSum; decide +kernel

private theorem s91845 : blockSum term 91845 327 419246 := by unfold blockSum; decide +kernel

private theorem s92172 : blockSum term 92172 327 624577 := by unfold blockSum; decide +kernel

private theorem s92499 : blockSum term 92499 327 568357 := by unfold blockSum; decide +kernel

private theorem s92826 : blockSum term 92826 327 513326 := by unfold blockSum; decide +kernel

private theorem s93153 : blockSum term 93153 327 458937 := by unfold blockSum; decide +kernel

private theorem s93480 : blockSum term 93480 327 422466 := by unfold blockSum; decide +kernel

private theorem s93807 : blockSum term 93807 327 537047 := by unfold blockSum; decide +kernel

private theorem s94134 : blockSum term 94134 326 466763 := by unfold blockSum; decide +kernel

private theorem s94460 : blockSum term 94460 327 463841 := by unfold blockSum; decide +kernel

private theorem s94787 : blockSum term 94787 327 526598 := by unfold blockSum; decide +kernel

private theorem s95114 : blockSum term 95114 327 474019 := by unfold blockSum; decide +kernel

private theorem s95441 : blockSum term 95441 327 487406 := by unfold blockSum; decide +kernel

private theorem s95768 : blockSum term 95768 327 484214 := by unfold blockSum; decide +kernel

private theorem s96095 : blockSum term 96095 327 416850 := by unfold blockSum; decide +kernel

private theorem s96422 : blockSum term 96422 327 430039 := by unfold blockSum; decide +kernel

private theorem s96749 : blockSum term 96749 326 474550 := by unfold blockSum; decide +kernel

private theorem s97075 : blockSum term 97075 327 408408 := by unfold blockSum; decide +kernel

private theorem s97402 : blockSum term 97402 327 406086 := by unfold blockSum; decide +kernel

private theorem s97729 : blockSum term 97729 327 449973 := by unfold blockSum; decide +kernel

private theorem s98056 : blockSum term 98056 327 354556 := by unfold blockSum; decide +kernel

private theorem s98383 : blockSum term 98383 327 428871 := by unfold blockSum; decide +kernel

private theorem s98710 : blockSum term 98710 327 517120 := by unfold blockSum; decide +kernel

private theorem s99037 : blockSum term 99037 327 407998 := by unfold blockSum; decide +kernel

private theorem s99364 : blockSum term 99364 326 435030 := by unfold blockSum; decide +kernel

private theorem s99690 : blockSum term 99690 327 431962 := by unfold blockSum; decide +kernel

private theorem s100017 : blockSum term 100017 327 369831 := by unfold blockSum; decide +kernel

private theorem s100344 : blockSum term 100344 327 426340 := by unfold blockSum; decide +kernel

private theorem s100671 : blockSum term 100671 327 365017 := by unfold blockSum; decide +kernel

private theorem s100998 : blockSum term 100998 327 449657 := by unfold blockSum; decide +kernel

private theorem s101325 : blockSum term 101325 327 446418 := by unfold blockSum; decide +kernel

private theorem s101652 : blockSum term 101652 327 428815 := by unfold blockSum; decide +kernel

private theorem s101979 : blockSum term 101979 326 496740 := by unfold blockSum; decide +kernel

private theorem s102305 : blockSum term 102305 327 380609 := by unfold blockSum; decide +kernel

private theorem s102632 : blockSum term 102632 327 350106 := by unfold blockSum; decide +kernel

private theorem s102959 : blockSum term 102959 327 292222 := by unfold blockSum; decide +kernel

private theorem s103286 : blockSum term 103286 327 386933 := by unfold blockSum; decide +kernel

private theorem s103613 : blockSum term 103613 327 329395 := by unfold blockSum; decide +kernel

private theorem s103940 : blockSum term 103940 327 449731 := by unfold blockSum; decide +kernel

private theorem s104267 : blockSum term 104267 327 378801 := by unfold blockSum; decide +kernel

private theorem s104594 : blockSum term 104594 326 429506 := by unfold blockSum; decide +kernel

private theorem s104920 : blockSum term 104920 327 306476 := by unfold blockSum; decide +kernel

private theorem s105247 : blockSum term 105247 327 436566 := by unfold blockSum; decide +kernel

private theorem s105574 : blockSum term 105574 327 302109 := by unfold blockSum; decide +kernel

private theorem s105901 : blockSum term 105901 326 365228 := by unfold blockSum; decide +kernel

private theorem s106227 : blockSum term 106227 327 414356 := by unfold blockSum; decide +kernel

private theorem s106554 : blockSum term 106554 327 411133 := by unfold blockSum; decide +kernel

private theorem s106881 : blockSum term 106881 327 344497 := by unfold blockSum; decide +kernel

private theorem s107208 : blockSum term 107208 326 266261 := by unfold blockSum; decide +kernel

private theorem s107534 : blockSum term 107534 327 327310 := by unfold blockSum; decide +kernel

private theorem s107861 : blockSum term 107861 327 362607 := by unfold blockSum; decide +kernel

private theorem s108188 : blockSum term 108188 327 360006 := by unfold blockSum; decide +kernel

private theorem s108515 : blockSum term 108515 327 320298 := by unfold blockSum; decide +kernel

private theorem s108842 : blockSum term 108842 327 415862 := by unfold blockSum; decide +kernel

private theorem s109169 : blockSum term 109169 327 352097 := by unfold blockSum; decide +kernel

private theorem s109496 : blockSum term 109496 327 313430 := by unfold blockSum; decide +kernel

private theorem s109823 : blockSum term 109823 326 335008 := by unfold blockSum; decide +kernel

private theorem s110149 : blockSum term 110149 327 249434 := by unfold blockSum; decide +kernel

private theorem s110476 : blockSum term 110476 327 365573 := by unfold blockSum; decide +kernel

private theorem s110803 : blockSum term 110803 327 374511 := by unfold blockSum; decide +kernel

private theorem s111130 : blockSum term 111130 327 278754 := by unfold blockSum; decide +kernel

private theorem s111457 : blockSum term 111457 327 334119 := by unfold blockSum; decide +kernel

private theorem s111784 : blockSum term 111784 327 320429 := by unfold blockSum; decide +kernel

private theorem s112111 : blockSum term 112111 327 363432 := by unfold blockSum; decide +kernel

private theorem s112438 : blockSum term 112438 326 247887 := by unfold blockSum; decide +kernel

private theorem s112764 : blockSum term 112764 327 346423 := by unfold blockSum; decide +kernel

private theorem s113091 : blockSum term 113091 327 354929 := by unfold blockSum; decide +kernel

private theorem s113418 : blockSum term 113418 327 231065 := by unfold blockSum; decide +kernel

private theorem s113745 : blockSum term 113745 327 316741 := by unfold blockSum; decide +kernel

private theorem s114072 : blockSum term 114072 327 292658 := by unfold blockSum; decide +kernel

private theorem s114399 : blockSum term 114399 327 290186 := by unfold blockSum; decide +kernel

private theorem s114726 : blockSum term 114726 327 277411 := by unfold blockSum; decide +kernel

private theorem s115053 : blockSum term 115053 326 328086 := by unfold blockSum; decide +kernel

private theorem s115379 : blockSum term 115379 327 252014 := by unfold blockSum; decide +kernel

private theorem s115706 : blockSum term 115706 327 375064 := by unfold blockSum; decide +kernel

private theorem s116033 : blockSum term 116033 327 268428 := by unfold blockSum; decide +kernel

private theorem s116360 : blockSum term 116360 327 245978 := by unfold blockSum; decide +kernel

private theorem s116687 : blockSum term 116687 327 294777 := by unfold blockSum; decide +kernel

private theorem s117014 : blockSum term 117014 327 292408 := by unfold blockSum; decide +kernel

private theorem s117341 : blockSum term 117341 327 250074 := by unfold blockSum; decide +kernel

private theorem s117668 : blockSum term 117668 326 356961 := by unfold blockSum; decide +kernel

private theorem s117994 : blockSum term 117994 327 236091 := by unfold blockSum; decide +kernel

private theorem s118321 : blockSum term 118321 327 244045 := by unfold blockSum; decide +kernel

private theorem s118648 : blockSum term 118648 327 290606 := by unfold blockSum; decide +kernel

private theorem s118975 : blockSum term 118975 327 269022 := by unfold blockSum; decide +kernel

private theorem s119302 : blockSum term 119302 327 209575 := by unfold blockSum; decide +kernel

private theorem s119629 : blockSum term 119629 327 302490 := by unfold blockSum; decide +kernel

private theorem s119956 : blockSum term 119956 327 262580 := by unfold blockSum; decide +kernel

private theorem s120283 : blockSum term 120283 326 232544 := by unfold blockSum; decide +kernel

private theorem s120609 : blockSum term 120609 327 313658 := by unfold blockSum; decide +kernel

private theorem s120936 : blockSum term 120936 327 237885 := by unfold blockSum; decide +kernel

private theorem s121263 : blockSum term 121263 327 317364 := by unfold blockSum; decide +kernel

private theorem s121590 : blockSum term 121590 327 197745 := by unfold blockSum; decide +kernel

private theorem s121917 : blockSum term 121917 327 293746 := by unfold blockSum; decide +kernel

private theorem s122244 : blockSum term 122244 327 264458 := by unfold blockSum; decide +kernel

private theorem s122571 : blockSum term 122571 327 235721 := by unfold blockSum; decide +kernel

private theorem s122898 : blockSum term 122898 326 216546 := by unfold blockSum; decide +kernel

private theorem s123224 : blockSum term 123224 327 248895 := by unfold blockSum; decide +kernel

private theorem s123551 : blockSum term 123551 327 255269 := by unfold blockSum; decide +kernel

private theorem s123878 : blockSum term 123878 327 227633 := by unfold blockSum; decide +kernel

private theorem s124205 : blockSum term 124205 327 233938 := by unfold blockSum; decide +kernel

private theorem s124532 : blockSum term 124532 327 248275 := by unfold blockSum; decide +kernel

private theorem s124859 : blockSum term 124859 327 196815 := by unfold blockSum; decide +kernel

private theorem s125186 : blockSum term 125186 327 235855 := by unfold blockSum; decide +kernel

private theorem s125513 : blockSum term 125513 326 233448 := by unfold blockSum; decide +kernel

private theorem s125839 : blockSum term 125839 327 223401 := by unfold blockSum; decide +kernel

private theorem s126166 : blockSum term 126166 327 221244 := by unfold blockSum; decide +kernel

private theorem s126493 : blockSum term 126493 327 195782 := by unfold blockSum; decide +kernel

private theorem s126820 : blockSum term 126820 326 178462 := by unfold blockSum; decide +kernel

private theorem s127146 : blockSum term 127146 327 200001 := by unfold blockSum; decide +kernel

private theorem s127473 : blockSum term 127473 327 251036 := by unfold blockSum; decide +kernel

private theorem s127800 : blockSum term 127800 327 188376 := by unfold blockSum; decide +kernel

private theorem s128127 : blockSum term 128127 326 231111 := by unfold blockSum; decide +kernel

private theorem s128453 : blockSum term 128453 327 214224 := by unfold blockSum; decide +kernel

private theorem s128780 : blockSum term 128780 327 219253 := by unfold blockSum; decide +kernel

private theorem s129107 : blockSum term 129107 327 188184 := by unfold blockSum; decide +kernel

private theorem s129434 : blockSum term 129434 327 229430 := by unfold blockSum; decide +kernel

private theorem s129761 : blockSum term 129761 327 184455 := by unfold blockSum; decide +kernel

private theorem s130088 : blockSum term 130088 327 196783 := by unfold blockSum; decide +kernel

private theorem s130415 : blockSum term 130415 327 208706 := by unfold blockSum; decide +kernel

private theorem s130742 : blockSum term 130742 326 158339 := by unfold blockSum; decide +kernel

private theorem s131068 : blockSum term 131068 327 170462 := by unfold blockSum; decide +kernel

private theorem s131395 : blockSum term 131395 327 188934 := by unfold blockSum; decide +kernel

private theorem s131722 : blockSum term 131722 327 180502 := by unfold blockSum; decide +kernel

private theorem s132049 : blockSum term 132049 327 185254 := by unfold blockSum; decide +kernel

private theorem s132376 : blockSum term 132376 327 196277 := by unfold blockSum; decide +kernel

private theorem s132703 : blockSum term 132703 327 174812 := by unfold blockSum; decide +kernel

private theorem s133030 : blockSum term 133030 327 204832 := by unfold blockSum; decide +kernel

private theorem s133357 : blockSum term 133357 326 151799 := by unfold blockSum; decide +kernel

private theorem s133683 : blockSum term 133683 327 156405 := by unfold blockSum; decide +kernel

private theorem s134010 : blockSum term 134010 327 179452 := by unfold blockSum; decide +kernel

private theorem s134337 : blockSum term 134337 327 146914 := by unfold blockSum; decide +kernel

private theorem s134664 : blockSum term 134664 327 157326 := by unfold blockSum; decide +kernel

private theorem s134991 : blockSum term 134991 327 167352 := by unfold blockSum; decide +kernel

private theorem s135318 : blockSum term 135318 327 200819 := by unfold blockSum; decide +kernel

private theorem s135645 : blockSum term 135645 327 151792 := by unfold blockSum; decide +kernel

private theorem s135972 : blockSum term 135972 326 149962 := by unfold blockSum; decide +kernel

private theorem s136298 : blockSum term 136298 327 216384 := by unfold blockSum; decide +kernel

private theorem s136625 : blockSum term 136625 327 151773 := by unfold blockSum; decide +kernel

private theorem s136952 : blockSum term 136952 327 150012 := by unfold blockSum; decide +kernel

private theorem s137279 : blockSum term 137279 327 159200 := by unfold blockSum; decide +kernel

private theorem s137606 : blockSum term 137606 327 130199 := by unfold blockSum; decide +kernel

private theorem s137933 : blockSum term 137933 327 160787 := by unfold blockSum; decide +kernel

private theorem s138260 : blockSum term 138260 327 158755 := by unfold blockSum; decide +kernel

private theorem s138587 : blockSum term 138587 326 135850 := by unfold blockSum; decide +kernel

private theorem s138913 : blockSum term 138913 327 103211 := by unfold blockSum; decide +kernel

private theorem s139240 : blockSum term 139240 327 158081 := by unfold blockSum; decide +kernel

private theorem s139567 : blockSum term 139567 327 140978 := by unfold blockSum; decide +kernel

private theorem s139894 : blockSum term 139894 327 129241 := by unfold blockSum; decide +kernel

private theorem s140221 : blockSum term 140221 327 142215 := by unfold blockSum; decide +kernel

private theorem s140548 : blockSum term 140548 327 164444 := by unfold blockSum; decide +kernel

private theorem s140875 : blockSum term 140875 327 114445 := by unfold blockSum; decide +kernel

private theorem s141202 : blockSum term 141202 326 131760 := by unfold blockSum; decide +kernel

private theorem s141528 : blockSum term 141528 327 152948 := by unfold blockSum; decide +kernel

private theorem s141855 : blockSum term 141855 327 123273 := by unfold blockSum; decide +kernel

private theorem s142182 : blockSum term 142182 327 103644 := by unfold blockSum; decide +kernel

private theorem s142509 : blockSum term 142509 327 120047 := by unfold blockSum; decide +kernel

private theorem s142836 : blockSum term 142836 327 109552 := by unfold blockSum; decide +kernel

private theorem s143163 : blockSum term 143163 327 103690 := by unfold blockSum; decide +kernel

private theorem s143490 : blockSum term 143490 327 127735 := by unfold blockSum; decide +kernel

private theorem s143817 : blockSum term 143817 326 92306 := by unfold blockSum; decide +kernel

private theorem s144143 : blockSum term 144143 327 115940 := by unfold blockSum; decide +kernel

private theorem s144470 : blockSum term 144470 327 114032 := by unfold blockSum; decide +kernel

private theorem s144797 : blockSum term 144797 327 104270 := by unfold blockSum; decide +kernel

private theorem s145124 : blockSum term 145124 327 90799 := by unfold blockSum; decide +kernel

private theorem s145451 : blockSum term 145451 327 132031 := by unfold blockSum; decide +kernel

private theorem s145778 : blockSum term 145778 327 110587 := by unfold blockSum; decide +kernel

private theorem s146105 : blockSum term 146105 327 101197 := by unfold blockSum; decide +kernel

private theorem s146432 : blockSum term 146432 326 88601 := by unfold blockSum; decide +kernel

private theorem s146758 : blockSum term 146758 327 98020 := by unfold blockSum; decide +kernel

private theorem s147085 : blockSum term 147085 327 110640 := by unfold blockSum; decide +kernel

private theorem s147412 : blockSum term 147412 327 91199 := by unfold blockSum; decide +kernel

private theorem s147739 : blockSum term 147739 326 82758 := by unfold blockSum; decide +kernel

private theorem s148065 : blockSum term 148065 327 88035 := by unfold blockSum; decide +kernel

private theorem s148392 : blockSum term 148392 327 89747 := by unfold blockSum; decide +kernel

private theorem s148719 : blockSum term 148719 327 97878 := by unfold blockSum; decide +kernel

private theorem s149046 : blockSum term 149046 326 102498 := by unfold blockSum; decide +kernel

private theorem s149372 : blockSum term 149372 327 87962 := by unfold blockSum; decide +kernel

private theorem s149699 : blockSum term 149699 327 89150 := by unfold blockSum; decide +kernel

private theorem s150026 : blockSum term 150026 327 87380 := by unfold blockSum; decide +kernel

private theorem s150353 : blockSum term 150353 327 79695 := by unfold blockSum; decide +kernel

private theorem s150680 : blockSum term 150680 327 77806 := by unfold blockSum; decide +kernel

private theorem s151007 : blockSum term 151007 327 76217 := by unfold blockSum; decide +kernel

private theorem s151334 : blockSum term 151334 327 93726 := by unfold blockSum; decide +kernel

private theorem s151661 : blockSum term 151661 326 78132 := by unfold blockSum; decide +kernel

private theorem s151987 : blockSum term 151987 327 73687 := by unfold blockSum; decide +kernel

private theorem s152314 : blockSum term 152314 327 69479 := by unfold blockSum; decide +kernel

private theorem s152641 : blockSum term 152641 327 75255 := by unfold blockSum; decide +kernel

private theorem s152968 : blockSum term 152968 327 56436 := by unfold blockSum; decide +kernel

private theorem s153295 : blockSum term 153295 327 71761 := by unfold blockSum; decide +kernel

private theorem s153622 : blockSum term 153622 327 53604 := by unfold blockSum; decide +kernel

private theorem s153949 : blockSum term 153949 327 63586 := by unfold blockSum; decide +kernel

private theorem s154276 : blockSum term 154276 326 59811 := by unfold blockSum; decide +kernel

private theorem s154602 : blockSum term 154602 327 60500 := by unfold blockSum; decide +kernel

private theorem s154929 : blockSum term 154929 327 56928 := by unfold blockSum; decide +kernel

private theorem s155256 : blockSum term 155256 327 57370 := by unfold blockSum; decide +kernel

private theorem s155583 : blockSum term 155583 327 67477 := by unfold blockSum; decide +kernel

private theorem s155910 : blockSum term 155910 327 36449 := by unfold blockSum; decide +kernel

private theorem s156237 : blockSum term 156237 327 41145 := by unfold blockSum; decide +kernel

private theorem s156564 : blockSum term 156564 327 50685 := by unfold blockSum; decide +kernel

private theorem s156891 : blockSum term 156891 326 48909 := by unfold blockSum; decide +kernel

private theorem s157217 : blockSum term 157217 327 55706 := by unfold blockSum; decide +kernel

private theorem s157544 : blockSum term 157544 327 40724 := by unfold blockSum; decide +kernel

private theorem s157871 : blockSum term 157871 327 36357 := by unfold blockSum; decide +kernel

private theorem s158198 : blockSum term 158198 327 39736 := by unfold blockSum; decide +kernel

private theorem s158525 : blockSum term 158525 327 41111 := by unfold blockSum; decide +kernel

private theorem s158852 : blockSum term 158852 327 32266 := by unfold blockSum; decide +kernel

private theorem s159179 : blockSum term 159179 327 38948 := by unfold blockSum; decide +kernel

private theorem s159506 : blockSum term 159506 326 39848 := by unfold blockSum; decide +kernel

private theorem s159832 : blockSum term 159832 327 32128 := by unfold blockSum; decide +kernel

private theorem s160159 : blockSum term 160159 327 30720 := by unfold blockSum; decide +kernel

private theorem s160486 : blockSum term 160486 327 33709 := by unfold blockSum; decide +kernel

private theorem s160813 : blockSum term 160813 327 28794 := by unfold blockSum; decide +kernel

private theorem s161140 : blockSum term 161140 327 25188 := by unfold blockSum; decide +kernel

private theorem s161467 : blockSum term 161467 327 28622 := by unfold blockSum; decide +kernel

private theorem s161794 : blockSum term 161794 327 23381 := by unfold blockSum; decide +kernel

private theorem s162121 : blockSum term 162121 326 16060 := by unfold blockSum; decide +kernel

private theorem s162447 : blockSum term 162447 327 25276 := by unfold blockSum; decide +kernel

private theorem s162774 : blockSum term 162774 327 19819 := by unfold blockSum; decide +kernel

private theorem s163101 : blockSum term 163101 327 19523 := by unfold blockSum; decide +kernel

private theorem s163428 : blockSum term 163428 327 16094 := by unfold blockSum; decide +kernel

private theorem s163755 : blockSum term 163755 327 15814 := by unfold blockSum; decide +kernel

private theorem s164082 : blockSum term 164082 327 14230 := by unfold blockSum; decide +kernel

private theorem s164409 : blockSum term 164409 327 12150 := by unfold blockSum; decide +kernel

private theorem s164736 : blockSum term 164736 326 8664 := by unfold blockSum; decide +kernel

private theorem s165062 : blockSum term 165062 327 8195 := by unfold blockSum; decide +kernel

private theorem s165389 : blockSum term 165389 327 8886 := by unfold blockSum; decide +kernel

private theorem s165716 : blockSum term 165716 327 5372 := by unfold blockSum; decide +kernel

private theorem s166043 : blockSum term 166043 327 4595 := by unfold blockSum; decide +kernel

private theorem s166370 : blockSum term 166370 327 3617 := by unfold blockSum; decide +kernel

private theorem s166697 : blockSum term 166697 327 2373 := by unfold blockSum; decide +kernel

private theorem s167024 : blockSum term 167024 327 897 := by unfold blockSum; decide +kernel

private theorem rows : blockSum term 0 167351 753837725 := (join_sums term (lo:=0) (a:=83675) (b:=83676) (join_sums term (lo:=0) (a:=41837) (b:=41838) (join_sums term (lo:=0) (a:=20918) (b:=20919) (join_sums term (lo:=0) (a:=10459) (b:=10459) (join_sums term (lo:=0) (a:=5229) (b:=5230) (join_sums term (lo:=0) (a:=2614) (b:=2615) (join_sums term (lo:=0) (a:=1307) (b:=1307) (join_sums term (lo:=0) (a:=653) (b:=654) (join_sums term (lo:=0) (a:=326) (b:=327) s0 s326) (join_sums term (lo:=653) (a:=327) (b:=327) s653 s980)) (join_sums term (lo:=1307) (a:=653) (b:=654) (join_sums term (lo:=1307) (a:=326) (b:=327) s1307 s1633) (join_sums term (lo:=1960) (a:=327) (b:=327) s1960 s2287))) (join_sums term (lo:=2614) (a:=1307) (b:=1308) (join_sums term (lo:=2614) (a:=653) (b:=654) (join_sums term (lo:=2614) (a:=326) (b:=327) s2614 s2940) (join_sums term (lo:=3267) (a:=327) (b:=327) s3267 s3594)) (join_sums term (lo:=3921) (a:=654) (b:=654) (join_sums term (lo:=3921) (a:=327) (b:=327) s3921 s4248) (join_sums term (lo:=4575) (a:=327) (b:=327) s4575 s4902)))) (join_sums term (lo:=5229) (a:=2615) (b:=2615) (join_sums term (lo:=5229) (a:=1307) (b:=1308) (join_sums term (lo:=5229) (a:=653) (b:=654) (join_sums term (lo:=5229) (a:=326) (b:=327) s5229 s5555) (join_sums term (lo:=5882) (a:=327) (b:=327) s5882 s6209)) (join_sums term (lo:=6536) (a:=654) (b:=654) (join_sums term (lo:=6536) (a:=327) (b:=327) s6536 s6863) (join_sums term (lo:=7190) (a:=327) (b:=327) s7190 s7517))) (join_sums term (lo:=7844) (a:=1307) (b:=1308) (join_sums term (lo:=7844) (a:=653) (b:=654) (join_sums term (lo:=7844) (a:=326) (b:=327) s7844 s8170) (join_sums term (lo:=8497) (a:=327) (b:=327) s8497 s8824)) (join_sums term (lo:=9151) (a:=654) (b:=654) (join_sums term (lo:=9151) (a:=327) (b:=327) s9151 s9478) (join_sums term (lo:=9805) (a:=327) (b:=327) s9805 s10132))))) (join_sums term (lo:=10459) (a:=5229) (b:=5230) (join_sums term (lo:=10459) (a:=2614) (b:=2615) (join_sums term (lo:=10459) (a:=1307) (b:=1307) (join_sums term (lo:=10459) (a:=653) (b:=654) (join_sums term (lo:=10459) (a:=326) (b:=327) s10459 s10785) (join_sums term (lo:=11112) (a:=327) (b:=327) s11112 s11439)) (join_sums term (lo:=11766) (a:=653) (b:=654) (join_sums term (lo:=11766) (a:=326) (b:=327) s11766 s12092) (join_sums term (lo:=12419) (a:=327) (b:=327) s12419 s12746))) (join_sums term (lo:=13073) (a:=1307) (b:=1308) (join_sums term (lo:=13073) (a:=653) (b:=654) (join_sums term (lo:=13073) (a:=326) (b:=327) s13073 s13399) (join_sums term (lo:=13726) (a:=327) (b:=327) s13726 s14053)) (join_sums term (lo:=14380) (a:=654) (b:=654) (join_sums term (lo:=14380) (a:=327) (b:=327) s14380 s14707) (join_sums term (lo:=15034) (a:=327) (b:=327) s15034 s15361)))) (join_sums term (lo:=15688) (a:=2615) (b:=2615) (join_sums term (lo:=15688) (a:=1307) (b:=1308) (join_sums term (lo:=15688) (a:=653) (b:=654) (join_sums term (lo:=15688) (a:=326) (b:=327) s15688 s16014) (join_sums term (lo:=16341) (a:=327) (b:=327) s16341 s16668)) (join_sums term (lo:=16995) (a:=654) (b:=654) (join_sums term (lo:=16995) (a:=327) (b:=327) s16995 s17322) (join_sums term (lo:=17649) (a:=327) (b:=327) s17649 s17976))) (join_sums term (lo:=18303) (a:=1307) (b:=1308) (join_sums term (lo:=18303) (a:=653) (b:=654) (join_sums term (lo:=18303) (a:=326) (b:=327) s18303 s18629) (join_sums term (lo:=18956) (a:=327) (b:=327) s18956 s19283)) (join_sums term (lo:=19610) (a:=654) (b:=654) (join_sums term (lo:=19610) (a:=327) (b:=327) s19610 s19937) (join_sums term (lo:=20264) (a:=327) (b:=327) s20264 s20591)))))) (join_sums term (lo:=20918) (a:=10459) (b:=10460) (join_sums term (lo:=20918) (a:=5229) (b:=5230) (join_sums term (lo:=20918) (a:=2614) (b:=2615) (join_sums term (lo:=20918) (a:=1307) (b:=1307) (join_sums term (lo:=20918) (a:=653) (b:=654) (join_sums term (lo:=20918) (a:=326) (b:=327) s20918 s21244) (join_sums term (lo:=21571) (a:=327) (b:=327) s21571 s21898)) (join_sums term (lo:=22225) (a:=653) (b:=654) (join_sums term (lo:=22225) (a:=326) (b:=327) s22225 s22551) (join_sums term (lo:=22878) (a:=327) (b:=327) s22878 s23205))) (join_sums term (lo:=23532) (a:=1307) (b:=1308) (join_sums term (lo:=23532) (a:=653) (b:=654) (join_sums term (lo:=23532) (a:=326) (b:=327) s23532 s23858) (join_sums term (lo:=24185) (a:=327) (b:=327) s24185 s24512)) (join_sums term (lo:=24839) (a:=654) (b:=654) (join_sums term (lo:=24839) (a:=327) (b:=327) s24839 s25166) (join_sums term (lo:=25493) (a:=327) (b:=327) s25493 s25820)))) (join_sums term (lo:=26147) (a:=2615) (b:=2615) (join_sums term (lo:=26147) (a:=1307) (b:=1308) (join_sums term (lo:=26147) (a:=653) (b:=654) (join_sums term (lo:=26147) (a:=326) (b:=327) s26147 s26473) (join_sums term (lo:=26800) (a:=327) (b:=327) s26800 s27127)) (join_sums term (lo:=27454) (a:=654) (b:=654) (join_sums term (lo:=27454) (a:=327) (b:=327) s27454 s27781) (join_sums term (lo:=28108) (a:=327) (b:=327) s28108 s28435))) (join_sums term (lo:=28762) (a:=1307) (b:=1308) (join_sums term (lo:=28762) (a:=653) (b:=654) (join_sums term (lo:=28762) (a:=326) (b:=327) s28762 s29088) (join_sums term (lo:=29415) (a:=327) (b:=327) s29415 s29742)) (join_sums term (lo:=30069) (a:=654) (b:=654) (join_sums term (lo:=30069) (a:=327) (b:=327) s30069 s30396) (join_sums term (lo:=30723) (a:=327) (b:=327) s30723 s31050))))) (join_sums term (lo:=31377) (a:=5230) (b:=5230) (join_sums term (lo:=31377) (a:=2615) (b:=2615) (join_sums term (lo:=31377) (a:=1307) (b:=1308) (join_sums term (lo:=31377) (a:=653) (b:=654) (join_sums term (lo:=31377) (a:=326) (b:=327) s31377 s31703) (join_sums term (lo:=32030) (a:=327) (b:=327) s32030 s32357)) (join_sums term (lo:=32684) (a:=654) (b:=654) (join_sums term (lo:=32684) (a:=327) (b:=327) s32684 s33011) (join_sums term (lo:=33338) (a:=327) (b:=327) s33338 s33665))) (join_sums term (lo:=33992) (a:=1307) (b:=1308) (join_sums term (lo:=33992) (a:=653) (b:=654) (join_sums term (lo:=33992) (a:=326) (b:=327) s33992 s34318) (join_sums term (lo:=34645) (a:=327) (b:=327) s34645 s34972)) (join_sums term (lo:=35299) (a:=654) (b:=654) (join_sums term (lo:=35299) (a:=327) (b:=327) s35299 s35626) (join_sums term (lo:=35953) (a:=327) (b:=327) s35953 s36280)))) (join_sums term (lo:=36607) (a:=2615) (b:=2615) (join_sums term (lo:=36607) (a:=1307) (b:=1308) (join_sums term (lo:=36607) (a:=653) (b:=654) (join_sums term (lo:=36607) (a:=326) (b:=327) s36607 s36933) (join_sums term (lo:=37260) (a:=327) (b:=327) s37260 s37587)) (join_sums term (lo:=37914) (a:=654) (b:=654) (join_sums term (lo:=37914) (a:=327) (b:=327) s37914 s38241) (join_sums term (lo:=38568) (a:=327) (b:=327) s38568 s38895))) (join_sums term (lo:=39222) (a:=1307) (b:=1308) (join_sums term (lo:=39222) (a:=653) (b:=654) (join_sums term (lo:=39222) (a:=326) (b:=327) s39222 s39548) (join_sums term (lo:=39875) (a:=327) (b:=327) s39875 s40202)) (join_sums term (lo:=40529) (a:=654) (b:=654) (join_sums term (lo:=40529) (a:=327) (b:=327) s40529 s40856) (join_sums term (lo:=41183) (a:=327) (b:=327) s41183 s41510))))))) (join_sums term (lo:=41837) (a:=20919) (b:=20919) (join_sums term (lo:=41837) (a:=10459) (b:=10460) (join_sums term (lo:=41837) (a:=5229) (b:=5230) (join_sums term (lo:=41837) (a:=2614) (b:=2615) (join_sums term (lo:=41837) (a:=1307) (b:=1307) (join_sums term (lo:=41837) (a:=653) (b:=654) (join_sums term (lo:=41837) (a:=326) (b:=327) s41837 s42163) (join_sums term (lo:=42490) (a:=327) (b:=327) s42490 s42817)) (join_sums term (lo:=43144) (a:=653) (b:=654) (join_sums term (lo:=43144) (a:=326) (b:=327) s43144 s43470) (join_sums term (lo:=43797) (a:=327) (b:=327) s43797 s44124))) (join_sums term (lo:=44451) (a:=1307) (b:=1308) (join_sums term (lo:=44451) (a:=653) (b:=654) (join_sums term (lo:=44451) (a:=326) (b:=327) s44451 s44777) (join_sums term (lo:=45104) (a:=327) (b:=327) s45104 s45431)) (join_sums term (lo:=45758) (a:=654) (b:=654) (join_sums term (lo:=45758) (a:=327) (b:=327) s45758 s46085) (join_sums term (lo:=46412) (a:=327) (b:=327) s46412 s46739)))) (join_sums term (lo:=47066) (a:=2615) (b:=2615) (join_sums term (lo:=47066) (a:=1307) (b:=1308) (join_sums term (lo:=47066) (a:=653) (b:=654) (join_sums term (lo:=47066) (a:=326) (b:=327) s47066 s47392) (join_sums term (lo:=47719) (a:=327) (b:=327) s47719 s48046)) (join_sums term (lo:=48373) (a:=654) (b:=654) (join_sums term (lo:=48373) (a:=327) (b:=327) s48373 s48700) (join_sums term (lo:=49027) (a:=327) (b:=327) s49027 s49354))) (join_sums term (lo:=49681) (a:=1307) (b:=1308) (join_sums term (lo:=49681) (a:=653) (b:=654) (join_sums term (lo:=49681) (a:=326) (b:=327) s49681 s50007) (join_sums term (lo:=50334) (a:=327) (b:=327) s50334 s50661)) (join_sums term (lo:=50988) (a:=654) (b:=654) (join_sums term (lo:=50988) (a:=327) (b:=327) s50988 s51315) (join_sums term (lo:=51642) (a:=327) (b:=327) s51642 s51969))))) (join_sums term (lo:=52296) (a:=5230) (b:=5230) (join_sums term (lo:=52296) (a:=2615) (b:=2615) (join_sums term (lo:=52296) (a:=1307) (b:=1308) (join_sums term (lo:=52296) (a:=653) (b:=654) (join_sums term (lo:=52296) (a:=326) (b:=327) s52296 s52622) (join_sums term (lo:=52949) (a:=327) (b:=327) s52949 s53276)) (join_sums term (lo:=53603) (a:=654) (b:=654) (join_sums term (lo:=53603) (a:=327) (b:=327) s53603 s53930) (join_sums term (lo:=54257) (a:=327) (b:=327) s54257 s54584))) (join_sums term (lo:=54911) (a:=1307) (b:=1308) (join_sums term (lo:=54911) (a:=653) (b:=654) (join_sums term (lo:=54911) (a:=326) (b:=327) s54911 s55237) (join_sums term (lo:=55564) (a:=327) (b:=327) s55564 s55891)) (join_sums term (lo:=56218) (a:=654) (b:=654) (join_sums term (lo:=56218) (a:=327) (b:=327) s56218 s56545) (join_sums term (lo:=56872) (a:=327) (b:=327) s56872 s57199)))) (join_sums term (lo:=57526) (a:=2615) (b:=2615) (join_sums term (lo:=57526) (a:=1307) (b:=1308) (join_sums term (lo:=57526) (a:=653) (b:=654) (join_sums term (lo:=57526) (a:=326) (b:=327) s57526 s57852) (join_sums term (lo:=58179) (a:=327) (b:=327) s58179 s58506)) (join_sums term (lo:=58833) (a:=654) (b:=654) (join_sums term (lo:=58833) (a:=327) (b:=327) s58833 s59160) (join_sums term (lo:=59487) (a:=327) (b:=327) s59487 s59814))) (join_sums term (lo:=60141) (a:=1307) (b:=1308) (join_sums term (lo:=60141) (a:=653) (b:=654) (join_sums term (lo:=60141) (a:=326) (b:=327) s60141 s60467) (join_sums term (lo:=60794) (a:=327) (b:=327) s60794 s61121)) (join_sums term (lo:=61448) (a:=654) (b:=654) (join_sums term (lo:=61448) (a:=327) (b:=327) s61448 s61775) (join_sums term (lo:=62102) (a:=327) (b:=327) s62102 s62429)))))) (join_sums term (lo:=62756) (a:=10459) (b:=10460) (join_sums term (lo:=62756) (a:=5229) (b:=5230) (join_sums term (lo:=62756) (a:=2614) (b:=2615) (join_sums term (lo:=62756) (a:=1307) (b:=1307) (join_sums term (lo:=62756) (a:=653) (b:=654) (join_sums term (lo:=62756) (a:=326) (b:=327) s62756 s63082) (join_sums term (lo:=63409) (a:=327) (b:=327) s63409 s63736)) (join_sums term (lo:=64063) (a:=653) (b:=654) (join_sums term (lo:=64063) (a:=326) (b:=327) s64063 s64389) (join_sums term (lo:=64716) (a:=327) (b:=327) s64716 s65043))) (join_sums term (lo:=65370) (a:=1307) (b:=1308) (join_sums term (lo:=65370) (a:=653) (b:=654) (join_sums term (lo:=65370) (a:=326) (b:=327) s65370 s65696) (join_sums term (lo:=66023) (a:=327) (b:=327) s66023 s66350)) (join_sums term (lo:=66677) (a:=654) (b:=654) (join_sums term (lo:=66677) (a:=327) (b:=327) s66677 s67004) (join_sums term (lo:=67331) (a:=327) (b:=327) s67331 s67658)))) (join_sums term (lo:=67985) (a:=2615) (b:=2615) (join_sums term (lo:=67985) (a:=1307) (b:=1308) (join_sums term (lo:=67985) (a:=653) (b:=654) (join_sums term (lo:=67985) (a:=326) (b:=327) s67985 s68311) (join_sums term (lo:=68638) (a:=327) (b:=327) s68638 s68965)) (join_sums term (lo:=69292) (a:=654) (b:=654) (join_sums term (lo:=69292) (a:=327) (b:=327) s69292 s69619) (join_sums term (lo:=69946) (a:=327) (b:=327) s69946 s70273))) (join_sums term (lo:=70600) (a:=1307) (b:=1308) (join_sums term (lo:=70600) (a:=653) (b:=654) (join_sums term (lo:=70600) (a:=326) (b:=327) s70600 s70926) (join_sums term (lo:=71253) (a:=327) (b:=327) s71253 s71580)) (join_sums term (lo:=71907) (a:=654) (b:=654) (join_sums term (lo:=71907) (a:=327) (b:=327) s71907 s72234) (join_sums term (lo:=72561) (a:=327) (b:=327) s72561 s72888))))) (join_sums term (lo:=73215) (a:=5230) (b:=5230) (join_sums term (lo:=73215) (a:=2615) (b:=2615) (join_sums term (lo:=73215) (a:=1307) (b:=1308) (join_sums term (lo:=73215) (a:=653) (b:=654) (join_sums term (lo:=73215) (a:=326) (b:=327) s73215 s73541) (join_sums term (lo:=73868) (a:=327) (b:=327) s73868 s74195)) (join_sums term (lo:=74522) (a:=654) (b:=654) (join_sums term (lo:=74522) (a:=327) (b:=327) s74522 s74849) (join_sums term (lo:=75176) (a:=327) (b:=327) s75176 s75503))) (join_sums term (lo:=75830) (a:=1307) (b:=1308) (join_sums term (lo:=75830) (a:=653) (b:=654) (join_sums term (lo:=75830) (a:=326) (b:=327) s75830 s76156) (join_sums term (lo:=76483) (a:=327) (b:=327) s76483 s76810)) (join_sums term (lo:=77137) (a:=654) (b:=654) (join_sums term (lo:=77137) (a:=327) (b:=327) s77137 s77464) (join_sums term (lo:=77791) (a:=327) (b:=327) s77791 s78118)))) (join_sums term (lo:=78445) (a:=2615) (b:=2615) (join_sums term (lo:=78445) (a:=1307) (b:=1308) (join_sums term (lo:=78445) (a:=653) (b:=654) (join_sums term (lo:=78445) (a:=326) (b:=327) s78445 s78771) (join_sums term (lo:=79098) (a:=327) (b:=327) s79098 s79425)) (join_sums term (lo:=79752) (a:=654) (b:=654) (join_sums term (lo:=79752) (a:=327) (b:=327) s79752 s80079) (join_sums term (lo:=80406) (a:=327) (b:=327) s80406 s80733))) (join_sums term (lo:=81060) (a:=1307) (b:=1308) (join_sums term (lo:=81060) (a:=653) (b:=654) (join_sums term (lo:=81060) (a:=326) (b:=327) s81060 s81386) (join_sums term (lo:=81713) (a:=327) (b:=327) s81713 s82040)) (join_sums term (lo:=82367) (a:=654) (b:=654) (join_sums term (lo:=82367) (a:=327) (b:=327) s82367 s82694) (join_sums term (lo:=83021) (a:=327) (b:=327) s83021 s83348)))))))) (join_sums term (lo:=83675) (a:=41838) (b:=41838) (join_sums term (lo:=83675) (a:=20919) (b:=20919) (join_sums term (lo:=83675) (a:=10459) (b:=10460) (join_sums term (lo:=83675) (a:=5229) (b:=5230) (join_sums term (lo:=83675) (a:=2614) (b:=2615) (join_sums term (lo:=83675) (a:=1307) (b:=1307) (join_sums term (lo:=83675) (a:=653) (b:=654) (join_sums term (lo:=83675) (a:=326) (b:=327) s83675 s84001) (join_sums term (lo:=84328) (a:=327) (b:=327) s84328 s84655)) (join_sums term (lo:=84982) (a:=653) (b:=654) (join_sums term (lo:=84982) (a:=326) (b:=327) s84982 s85308) (join_sums term (lo:=85635) (a:=327) (b:=327) s85635 s85962))) (join_sums term (lo:=86289) (a:=1307) (b:=1308) (join_sums term (lo:=86289) (a:=653) (b:=654) (join_sums term (lo:=86289) (a:=326) (b:=327) s86289 s86615) (join_sums term (lo:=86942) (a:=327) (b:=327) s86942 s87269)) (join_sums term (lo:=87596) (a:=654) (b:=654) (join_sums term (lo:=87596) (a:=327) (b:=327) s87596 s87923) (join_sums term (lo:=88250) (a:=327) (b:=327) s88250 s88577)))) (join_sums term (lo:=88904) (a:=2615) (b:=2615) (join_sums term (lo:=88904) (a:=1307) (b:=1308) (join_sums term (lo:=88904) (a:=653) (b:=654) (join_sums term (lo:=88904) (a:=326) (b:=327) s88904 s89230) (join_sums term (lo:=89557) (a:=327) (b:=327) s89557 s89884)) (join_sums term (lo:=90211) (a:=654) (b:=654) (join_sums term (lo:=90211) (a:=327) (b:=327) s90211 s90538) (join_sums term (lo:=90865) (a:=327) (b:=327) s90865 s91192))) (join_sums term (lo:=91519) (a:=1307) (b:=1308) (join_sums term (lo:=91519) (a:=653) (b:=654) (join_sums term (lo:=91519) (a:=326) (b:=327) s91519 s91845) (join_sums term (lo:=92172) (a:=327) (b:=327) s92172 s92499)) (join_sums term (lo:=92826) (a:=654) (b:=654) (join_sums term (lo:=92826) (a:=327) (b:=327) s92826 s93153) (join_sums term (lo:=93480) (a:=327) (b:=327) s93480 s93807))))) (join_sums term (lo:=94134) (a:=5230) (b:=5230) (join_sums term (lo:=94134) (a:=2615) (b:=2615) (join_sums term (lo:=94134) (a:=1307) (b:=1308) (join_sums term (lo:=94134) (a:=653) (b:=654) (join_sums term (lo:=94134) (a:=326) (b:=327) s94134 s94460) (join_sums term (lo:=94787) (a:=327) (b:=327) s94787 s95114)) (join_sums term (lo:=95441) (a:=654) (b:=654) (join_sums term (lo:=95441) (a:=327) (b:=327) s95441 s95768) (join_sums term (lo:=96095) (a:=327) (b:=327) s96095 s96422))) (join_sums term (lo:=96749) (a:=1307) (b:=1308) (join_sums term (lo:=96749) (a:=653) (b:=654) (join_sums term (lo:=96749) (a:=326) (b:=327) s96749 s97075) (join_sums term (lo:=97402) (a:=327) (b:=327) s97402 s97729)) (join_sums term (lo:=98056) (a:=654) (b:=654) (join_sums term (lo:=98056) (a:=327) (b:=327) s98056 s98383) (join_sums term (lo:=98710) (a:=327) (b:=327) s98710 s99037)))) (join_sums term (lo:=99364) (a:=2615) (b:=2615) (join_sums term (lo:=99364) (a:=1307) (b:=1308) (join_sums term (lo:=99364) (a:=653) (b:=654) (join_sums term (lo:=99364) (a:=326) (b:=327) s99364 s99690) (join_sums term (lo:=100017) (a:=327) (b:=327) s100017 s100344)) (join_sums term (lo:=100671) (a:=654) (b:=654) (join_sums term (lo:=100671) (a:=327) (b:=327) s100671 s100998) (join_sums term (lo:=101325) (a:=327) (b:=327) s101325 s101652))) (join_sums term (lo:=101979) (a:=1307) (b:=1308) (join_sums term (lo:=101979) (a:=653) (b:=654) (join_sums term (lo:=101979) (a:=326) (b:=327) s101979 s102305) (join_sums term (lo:=102632) (a:=327) (b:=327) s102632 s102959)) (join_sums term (lo:=103286) (a:=654) (b:=654) (join_sums term (lo:=103286) (a:=327) (b:=327) s103286 s103613) (join_sums term (lo:=103940) (a:=327) (b:=327) s103940 s104267)))))) (join_sums term (lo:=104594) (a:=10459) (b:=10460) (join_sums term (lo:=104594) (a:=5229) (b:=5230) (join_sums term (lo:=104594) (a:=2614) (b:=2615) (join_sums term (lo:=104594) (a:=1307) (b:=1307) (join_sums term (lo:=104594) (a:=653) (b:=654) (join_sums term (lo:=104594) (a:=326) (b:=327) s104594 s104920) (join_sums term (lo:=105247) (a:=327) (b:=327) s105247 s105574)) (join_sums term (lo:=105901) (a:=653) (b:=654) (join_sums term (lo:=105901) (a:=326) (b:=327) s105901 s106227) (join_sums term (lo:=106554) (a:=327) (b:=327) s106554 s106881))) (join_sums term (lo:=107208) (a:=1307) (b:=1308) (join_sums term (lo:=107208) (a:=653) (b:=654) (join_sums term (lo:=107208) (a:=326) (b:=327) s107208 s107534) (join_sums term (lo:=107861) (a:=327) (b:=327) s107861 s108188)) (join_sums term (lo:=108515) (a:=654) (b:=654) (join_sums term (lo:=108515) (a:=327) (b:=327) s108515 s108842) (join_sums term (lo:=109169) (a:=327) (b:=327) s109169 s109496)))) (join_sums term (lo:=109823) (a:=2615) (b:=2615) (join_sums term (lo:=109823) (a:=1307) (b:=1308) (join_sums term (lo:=109823) (a:=653) (b:=654) (join_sums term (lo:=109823) (a:=326) (b:=327) s109823 s110149) (join_sums term (lo:=110476) (a:=327) (b:=327) s110476 s110803)) (join_sums term (lo:=111130) (a:=654) (b:=654) (join_sums term (lo:=111130) (a:=327) (b:=327) s111130 s111457) (join_sums term (lo:=111784) (a:=327) (b:=327) s111784 s112111))) (join_sums term (lo:=112438) (a:=1307) (b:=1308) (join_sums term (lo:=112438) (a:=653) (b:=654) (join_sums term (lo:=112438) (a:=326) (b:=327) s112438 s112764) (join_sums term (lo:=113091) (a:=327) (b:=327) s113091 s113418)) (join_sums term (lo:=113745) (a:=654) (b:=654) (join_sums term (lo:=113745) (a:=327) (b:=327) s113745 s114072) (join_sums term (lo:=114399) (a:=327) (b:=327) s114399 s114726))))) (join_sums term (lo:=115053) (a:=5230) (b:=5230) (join_sums term (lo:=115053) (a:=2615) (b:=2615) (join_sums term (lo:=115053) (a:=1307) (b:=1308) (join_sums term (lo:=115053) (a:=653) (b:=654) (join_sums term (lo:=115053) (a:=326) (b:=327) s115053 s115379) (join_sums term (lo:=115706) (a:=327) (b:=327) s115706 s116033)) (join_sums term (lo:=116360) (a:=654) (b:=654) (join_sums term (lo:=116360) (a:=327) (b:=327) s116360 s116687) (join_sums term (lo:=117014) (a:=327) (b:=327) s117014 s117341))) (join_sums term (lo:=117668) (a:=1307) (b:=1308) (join_sums term (lo:=117668) (a:=653) (b:=654) (join_sums term (lo:=117668) (a:=326) (b:=327) s117668 s117994) (join_sums term (lo:=118321) (a:=327) (b:=327) s118321 s118648)) (join_sums term (lo:=118975) (a:=654) (b:=654) (join_sums term (lo:=118975) (a:=327) (b:=327) s118975 s119302) (join_sums term (lo:=119629) (a:=327) (b:=327) s119629 s119956)))) (join_sums term (lo:=120283) (a:=2615) (b:=2615) (join_sums term (lo:=120283) (a:=1307) (b:=1308) (join_sums term (lo:=120283) (a:=653) (b:=654) (join_sums term (lo:=120283) (a:=326) (b:=327) s120283 s120609) (join_sums term (lo:=120936) (a:=327) (b:=327) s120936 s121263)) (join_sums term (lo:=121590) (a:=654) (b:=654) (join_sums term (lo:=121590) (a:=327) (b:=327) s121590 s121917) (join_sums term (lo:=122244) (a:=327) (b:=327) s122244 s122571))) (join_sums term (lo:=122898) (a:=1307) (b:=1308) (join_sums term (lo:=122898) (a:=653) (b:=654) (join_sums term (lo:=122898) (a:=326) (b:=327) s122898 s123224) (join_sums term (lo:=123551) (a:=327) (b:=327) s123551 s123878)) (join_sums term (lo:=124205) (a:=654) (b:=654) (join_sums term (lo:=124205) (a:=327) (b:=327) s124205 s124532) (join_sums term (lo:=124859) (a:=327) (b:=327) s124859 s125186))))))) (join_sums term (lo:=125513) (a:=20919) (b:=20919) (join_sums term (lo:=125513) (a:=10459) (b:=10460) (join_sums term (lo:=125513) (a:=5229) (b:=5230) (join_sums term (lo:=125513) (a:=2614) (b:=2615) (join_sums term (lo:=125513) (a:=1307) (b:=1307) (join_sums term (lo:=125513) (a:=653) (b:=654) (join_sums term (lo:=125513) (a:=326) (b:=327) s125513 s125839) (join_sums term (lo:=126166) (a:=327) (b:=327) s126166 s126493)) (join_sums term (lo:=126820) (a:=653) (b:=654) (join_sums term (lo:=126820) (a:=326) (b:=327) s126820 s127146) (join_sums term (lo:=127473) (a:=327) (b:=327) s127473 s127800))) (join_sums term (lo:=128127) (a:=1307) (b:=1308) (join_sums term (lo:=128127) (a:=653) (b:=654) (join_sums term (lo:=128127) (a:=326) (b:=327) s128127 s128453) (join_sums term (lo:=128780) (a:=327) (b:=327) s128780 s129107)) (join_sums term (lo:=129434) (a:=654) (b:=654) (join_sums term (lo:=129434) (a:=327) (b:=327) s129434 s129761) (join_sums term (lo:=130088) (a:=327) (b:=327) s130088 s130415)))) (join_sums term (lo:=130742) (a:=2615) (b:=2615) (join_sums term (lo:=130742) (a:=1307) (b:=1308) (join_sums term (lo:=130742) (a:=653) (b:=654) (join_sums term (lo:=130742) (a:=326) (b:=327) s130742 s131068) (join_sums term (lo:=131395) (a:=327) (b:=327) s131395 s131722)) (join_sums term (lo:=132049) (a:=654) (b:=654) (join_sums term (lo:=132049) (a:=327) (b:=327) s132049 s132376) (join_sums term (lo:=132703) (a:=327) (b:=327) s132703 s133030))) (join_sums term (lo:=133357) (a:=1307) (b:=1308) (join_sums term (lo:=133357) (a:=653) (b:=654) (join_sums term (lo:=133357) (a:=326) (b:=327) s133357 s133683) (join_sums term (lo:=134010) (a:=327) (b:=327) s134010 s134337)) (join_sums term (lo:=134664) (a:=654) (b:=654) (join_sums term (lo:=134664) (a:=327) (b:=327) s134664 s134991) (join_sums term (lo:=135318) (a:=327) (b:=327) s135318 s135645))))) (join_sums term (lo:=135972) (a:=5230) (b:=5230) (join_sums term (lo:=135972) (a:=2615) (b:=2615) (join_sums term (lo:=135972) (a:=1307) (b:=1308) (join_sums term (lo:=135972) (a:=653) (b:=654) (join_sums term (lo:=135972) (a:=326) (b:=327) s135972 s136298) (join_sums term (lo:=136625) (a:=327) (b:=327) s136625 s136952)) (join_sums term (lo:=137279) (a:=654) (b:=654) (join_sums term (lo:=137279) (a:=327) (b:=327) s137279 s137606) (join_sums term (lo:=137933) (a:=327) (b:=327) s137933 s138260))) (join_sums term (lo:=138587) (a:=1307) (b:=1308) (join_sums term (lo:=138587) (a:=653) (b:=654) (join_sums term (lo:=138587) (a:=326) (b:=327) s138587 s138913) (join_sums term (lo:=139240) (a:=327) (b:=327) s139240 s139567)) (join_sums term (lo:=139894) (a:=654) (b:=654) (join_sums term (lo:=139894) (a:=327) (b:=327) s139894 s140221) (join_sums term (lo:=140548) (a:=327) (b:=327) s140548 s140875)))) (join_sums term (lo:=141202) (a:=2615) (b:=2615) (join_sums term (lo:=141202) (a:=1307) (b:=1308) (join_sums term (lo:=141202) (a:=653) (b:=654) (join_sums term (lo:=141202) (a:=326) (b:=327) s141202 s141528) (join_sums term (lo:=141855) (a:=327) (b:=327) s141855 s142182)) (join_sums term (lo:=142509) (a:=654) (b:=654) (join_sums term (lo:=142509) (a:=327) (b:=327) s142509 s142836) (join_sums term (lo:=143163) (a:=327) (b:=327) s143163 s143490))) (join_sums term (lo:=143817) (a:=1307) (b:=1308) (join_sums term (lo:=143817) (a:=653) (b:=654) (join_sums term (lo:=143817) (a:=326) (b:=327) s143817 s144143) (join_sums term (lo:=144470) (a:=327) (b:=327) s144470 s144797)) (join_sums term (lo:=145124) (a:=654) (b:=654) (join_sums term (lo:=145124) (a:=327) (b:=327) s145124 s145451) (join_sums term (lo:=145778) (a:=327) (b:=327) s145778 s146105)))))) (join_sums term (lo:=146432) (a:=10459) (b:=10460) (join_sums term (lo:=146432) (a:=5229) (b:=5230) (join_sums term (lo:=146432) (a:=2614) (b:=2615) (join_sums term (lo:=146432) (a:=1307) (b:=1307) (join_sums term (lo:=146432) (a:=653) (b:=654) (join_sums term (lo:=146432) (a:=326) (b:=327) s146432 s146758) (join_sums term (lo:=147085) (a:=327) (b:=327) s147085 s147412)) (join_sums term (lo:=147739) (a:=653) (b:=654) (join_sums term (lo:=147739) (a:=326) (b:=327) s147739 s148065) (join_sums term (lo:=148392) (a:=327) (b:=327) s148392 s148719))) (join_sums term (lo:=149046) (a:=1307) (b:=1308) (join_sums term (lo:=149046) (a:=653) (b:=654) (join_sums term (lo:=149046) (a:=326) (b:=327) s149046 s149372) (join_sums term (lo:=149699) (a:=327) (b:=327) s149699 s150026)) (join_sums term (lo:=150353) (a:=654) (b:=654) (join_sums term (lo:=150353) (a:=327) (b:=327) s150353 s150680) (join_sums term (lo:=151007) (a:=327) (b:=327) s151007 s151334)))) (join_sums term (lo:=151661) (a:=2615) (b:=2615) (join_sums term (lo:=151661) (a:=1307) (b:=1308) (join_sums term (lo:=151661) (a:=653) (b:=654) (join_sums term (lo:=151661) (a:=326) (b:=327) s151661 s151987) (join_sums term (lo:=152314) (a:=327) (b:=327) s152314 s152641)) (join_sums term (lo:=152968) (a:=654) (b:=654) (join_sums term (lo:=152968) (a:=327) (b:=327) s152968 s153295) (join_sums term (lo:=153622) (a:=327) (b:=327) s153622 s153949))) (join_sums term (lo:=154276) (a:=1307) (b:=1308) (join_sums term (lo:=154276) (a:=653) (b:=654) (join_sums term (lo:=154276) (a:=326) (b:=327) s154276 s154602) (join_sums term (lo:=154929) (a:=327) (b:=327) s154929 s155256)) (join_sums term (lo:=155583) (a:=654) (b:=654) (join_sums term (lo:=155583) (a:=327) (b:=327) s155583 s155910) (join_sums term (lo:=156237) (a:=327) (b:=327) s156237 s156564))))) (join_sums term (lo:=156891) (a:=5230) (b:=5230) (join_sums term (lo:=156891) (a:=2615) (b:=2615) (join_sums term (lo:=156891) (a:=1307) (b:=1308) (join_sums term (lo:=156891) (a:=653) (b:=654) (join_sums term (lo:=156891) (a:=326) (b:=327) s156891 s157217) (join_sums term (lo:=157544) (a:=327) (b:=327) s157544 s157871)) (join_sums term (lo:=158198) (a:=654) (b:=654) (join_sums term (lo:=158198) (a:=327) (b:=327) s158198 s158525) (join_sums term (lo:=158852) (a:=327) (b:=327) s158852 s159179))) (join_sums term (lo:=159506) (a:=1307) (b:=1308) (join_sums term (lo:=159506) (a:=653) (b:=654) (join_sums term (lo:=159506) (a:=326) (b:=327) s159506 s159832) (join_sums term (lo:=160159) (a:=327) (b:=327) s160159 s160486)) (join_sums term (lo:=160813) (a:=654) (b:=654) (join_sums term (lo:=160813) (a:=327) (b:=327) s160813 s161140) (join_sums term (lo:=161467) (a:=327) (b:=327) s161467 s161794)))) (join_sums term (lo:=162121) (a:=2615) (b:=2615) (join_sums term (lo:=162121) (a:=1307) (b:=1308) (join_sums term (lo:=162121) (a:=653) (b:=654) (join_sums term (lo:=162121) (a:=326) (b:=327) s162121 s162447) (join_sums term (lo:=162774) (a:=327) (b:=327) s162774 s163101)) (join_sums term (lo:=163428) (a:=654) (b:=654) (join_sums term (lo:=163428) (a:=327) (b:=327) s163428 s163755) (join_sums term (lo:=164082) (a:=327) (b:=327) s164082 s164409))) (join_sums term (lo:=164736) (a:=1307) (b:=1308) (join_sums term (lo:=164736) (a:=653) (b:=654) (join_sums term (lo:=164736) (a:=326) (b:=327) s164736 s165062) (join_sums term (lo:=165389) (a:=327) (b:=327) s165389 s165716)) (join_sums term (lo:=166043) (a:=654) (b:=654) (join_sums term (lo:=166043) (a:=327) (b:=327) s166043 s166370) (join_sums term (lo:=166697) (a:=327) (b:=327) s166697 s167024)))))))))

set_option maxRecDepth 8000 in
private theorem right_part :
    (∑ p ∈ (Nat.primesLE 167350).filter (3036 < ·),
      (Nat.primeCounting (28006150079/p) - Nat.primeCounting (p-1))) = 753837725 :=
  right_from_blocks tab prime HybridBound28006.fast_correct prime_ok (by decide) (by decide) rows

set_option maxRecDepth 12000 in
theorem exact_count : Nat.primeCounting 28006150079 = 1217243858 :=
  assemble (x:=28006150079) (y:=3036) (z:=167350) (a:=1971081584) (b:=753837725) (r:=1217243858)
    (by decide) (by decide) (by decide) (by decide) (by decide) left_part right_part (by decide)
end JointEndpoint28006
