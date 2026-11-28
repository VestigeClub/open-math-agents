import certificates.«semiprime-correction-555157672301-small»
import certificates.«rough-count-through-eleven»
import certificates.«semiprime-correction-204778727327-high»

/-!
# A certified value of the prime-counting function at 10,425,579,253

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

namespace HybridBound10425

def fast (n : ℕ) : ℕ :=
  if n≤206781 then WheelTableA94.fast n else CheckpointA10425Slim.fast n

theorem fast_correct (n : ℕ) (hn : n≤4775000) : fast n=Nat.primeCounting n := by
  unfold fast
  split_ifs with small
  · exact WheelTableA94.fast_correct n small
  · exact CheckpointA10425Slim.fast_correct n hn

end HybridBound10425


/- The Legendre and Meissel identities below are the public Physbuzz reduction
for OEIS A247824, itself crediting Daniel Veljjanoski and rleshner. The numerical proof below certifies one of the residual ranks. -/
open Finset
namespace JointEndpoint10425

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


private abbrev tab := HybridBound10425.fast
private abbrev F := evalPhi tab

private abbrev prime := CheckpointA10425Slim.prime
private theorem prime_ok (n : ℕ) (hn : n≤4775000) : prime n=true ↔ n.Prime := CheckpointA10425Slim.prime_ok n hn


private theorem takeStep {ps : List ℕ} {p q prev cut ans : ℕ}
    (notWheel : p≠11) (base : F ps 10425579253=prev) (part : F ps q=cut) (div : 10425579253/p=q)
    (le : p≤10425579253) (sq : (p+1)^2≤10425579253) (sub : prev-cut=ans) :
    F (p::ps) 10425579253=ans := eval_delta tab ps p 10425579253 q prev cut ans notWheel le sq div base part sub


private def ps0 : List ℕ := []
private theorem v0 : F ps0 10425579253=10425579253 := rfl

private def ps1 : List ℕ := 2::ps0
private theorem c1 : F ps0 5212789626=5212789626 := by decide +kernel
private theorem v1 : F ps1 10425579253=5212789627 :=
  takeStep (p:=2) (by decide) v0 c1 rfl (by decide) (by decide) rfl

private def ps2 : List ℕ := 3::ps1
private theorem c2 : F ps1 3475193084=1737596542 := by decide +kernel
private theorem v2 : F ps2 10425579253=3475193085 :=
  takeStep (p:=3) (by decide) v1 c2 rfl (by decide) (by decide) rfl

private def ps3 : List ℕ := 5::ps2
private theorem c3 : F ps2 2085115850=695038617 := by decide +kernel
private theorem v3 : F ps3 10425579253=2780154468 :=
  takeStep (p:=5) (by decide) v2 c3 rfl (by decide) (by decide) rfl

private def ps4 : List ℕ := 7::ps3
private theorem c4 : F ps3 1489368464=397164924 := by decide +kernel
private theorem v4 : F ps4 10425579253=2382989544 :=
  takeStep (p:=7) (by decide) v3 c4 rfl (by decide) (by decide) rfl

private def ps5 : List ℕ := 11::ps4
private theorem c5 : F ps4 947779932=216635412 := by decide +kernel
private theorem v5 : F ps5 10425579253=2166354132 := by decide +kernel

private def ps6 : List ℕ := 13::ps5
private theorem c6 : F ps5 801967634=166642626 := by decide +kernel
private theorem v6 : F ps6 10425579253=1999711506 :=
  takeStep (p:=13) (by decide) v5 c6 rfl (by decide) (by decide) rfl

private def ps7 : List ℕ := 17::ps6
private theorem c7 : F ps6 613269367=117630090 := by decide +kernel
private theorem v7 : F ps7 10425579253=1882081416 :=
  takeStep (p:=17) (by decide) v6 c7 rfl (by decide) (by decide) rfl

private def ps8 : List ℕ := 19::ps7
private theorem c8 : F ps7 548714697=99056918 := by decide +kernel
private theorem v8 : F ps8 10425579253=1783024498 :=
  takeStep (p:=19) (by decide) v7 c8 rfl (by decide) (by decide) rfl

private def ps9 : List ℕ := 23::ps8
private theorem c9 : F ps8 453286054=77522804 := by decide +kernel
private theorem v9 : F ps9 10425579253=1705501694 :=
  takeStep (p:=23) (by decide) v8 c9 rfl (by decide) (by decide) rfl

private def ps10 : List ℕ := 29::ps9
private theorem c10 : F ps9 359502732=58810403 := by decide +kernel
private theorem v10 : F ps10 10425579253=1646691291 :=
  takeStep (p:=29) (by decide) v9 c10 rfl (by decide) (by decide) rfl

private def ps11 : List ℕ := 31::ps10
private theorem c11 : F ps10 336309008=53119072 := by decide +kernel
private theorem v11 : F ps11 10425579253=1593572219 :=
  takeStep (p:=31) (by decide) v10 c11 rfl (by decide) (by decide) rfl

private def ps12 : List ℕ := 37::ps11
private theorem c12 : F ps11 281772412=43069511 := by decide +kernel
private theorem v12 : F ps12 10425579253=1550502708 :=
  takeStep (p:=37) (by decide) v11 c12 rfl (by decide) (by decide) rfl

private def ps13 : List ℕ := 41::ps12
private theorem c13 : F ps12 254282420=37817126 := by decide +kernel
private theorem v13 : F ps13 10425579253=1512685582 :=
  takeStep (p:=41) (by decide) v12 c13 rfl (by decide) (by decide) rfl

private def ps14 : List ℕ := 43::ps13
private theorem c14 : F ps13 242455331=35178743 := by decide +kernel
private theorem v14 : F ps14 10425579253=1477506839 :=
  takeStep (p:=43) (by decide) v13 c14 rfl (by decide) (by decide) rfl

private def ps15 : List ℕ := 47::ps14
private theorem c15 : F ps14 221820835=31436362 := by decide +kernel
private theorem v15 : F ps15 10425579253=1446070477 :=
  takeStep (p:=47) (by decide) v14 c15 rfl (by decide) (by decide) rfl

private def ps16 : List ℕ := 53::ps15
private theorem c16 : F ps15 196709042=27284493 := by decide +kernel
private theorem v16 : F ps16 10425579253=1418785984 :=
  takeStep (p:=53) (by decide) v15 c16 rfl (by decide) (by decide) rfl

private def ps17 : List ℕ := 59::ps16
private theorem c17 : F ps16 176704733=24047433 := by decide +kernel
private theorem v17 : F ps17 10425579253=1394738551 :=
  takeStep (p:=59) (by decide) v16 c17 rfl (by decide) (by decide) rfl

private def ps18 : List ℕ := 61::ps17
private theorem c18 : F ps17 170911135=22864831 := by decide +kernel
private theorem v18 : F ps18 10425579253=1371873720 :=
  takeStep (p:=61) (by decide) v17 c18 rfl (by decide) (by decide) rfl

private def ps19 : List ℕ := 67::ps18
private theorem c19 : F ps18 155605660=20475969 := by decide +kernel
private theorem v19 : F ps19 10425579253=1351397751 :=
  takeStep (p:=67) (by decide) v18 c19 rfl (by decide) (by decide) rfl

private def ps20 : List ℕ := 71::ps19
private theorem c20 : F ps19 146839144=19033892 := by decide +kernel
private theorem v20 : F ps20 10425579253=1332363859 :=
  takeStep (p:=71) (by decide) v19 c20 rfl (by decide) (by decide) rfl

private def ps21 : List ℕ := 73::ps20
private theorem c21 : F ps20 142816154=18251477 := by decide +kernel
private theorem v21 : F ps21 10425579253=1314112382 :=
  takeStep (p:=73) (by decide) v20 c21 rfl (by decide) (by decide) rfl

private def ps22 : List ℕ := 79::ps21
private theorem c22 : F ps21 131969357=16633926 := by decide +kernel
private theorem v22 : F ps22 10425579253=1297478456 :=
  takeStep (p:=79) (by decide) v21 c22 rfl (by decide) (by decide) rfl

private def ps23 : List ℕ := 83::ps22
private theorem c23 : F ps22 125609388=15631462 := by decide +kernel
private theorem v23 : F ps23 10425579253=1281846994 :=
  takeStep (p:=83) (by decide) v22 c23 rfl (by decide) (by decide) rfl

private def ps24 : List ℕ := 89::ps23
private theorem c24 : F ps23 117141339=14401460 := by decide +kernel
private theorem v24 : F ps24 10425579253=1267445534 :=
  takeStep (p:=89) (by decide) v23 c24 rfl (by decide) (by decide) rfl

private def ps25 : List ℕ := 97::ps24
private theorem c25 : F ps24 107480198=13064623 := by decide +kernel
private theorem v25 : F ps25 10425579253=1254380911 :=
  takeStep (p:=97) (by decide) v24 c25 rfl (by decide) (by decide) rfl

private def ps26 : List ℕ := 101::ps25
private theorem c26 : F ps25 103223556=12417319 := by decide +kernel
private theorem v26 : F ps26 10425579253=1241963592 :=
  takeStep (p:=101) (by decide) v25 c26 rfl (by decide) (by decide) rfl

private def ps27 : List ℕ := 103::ps26
private theorem c27 : F ps26 101219216=12055138 := by decide +kernel
private theorem v27 : F ps27 10425579253=1229908454 :=
  takeStep (p:=103) (by decide) v26 c27 rfl (by decide) (by decide) rfl

private def ps28 : List ℕ := 107::ps27
private theorem c28 : F ps27 97435320=11491316 := by decide +kernel
private theorem v28 : F ps28 10425579253=1218417138 :=
  takeStep (p:=107) (by decide) v27 c28 rfl (by decide) (by decide) rfl

private def ps29 : List ℕ := 109::ps28
private theorem c29 : F ps28 95647516=11174602 := by decide +kernel
private theorem v29 : F ps29 10425579253=1207242536 :=
  takeStep (p:=109) (by decide) v28 c29 rfl (by decide) (by decide) rfl

private def ps30 : List ℕ := 113::ps29
private theorem c30 : F ps29 92261763=10679763 := by decide +kernel
private theorem v30 : F ps30 10425579253=1196562773 :=
  takeStep (p:=113) (by decide) v29 c30 rfl (by decide) (by decide) rfl

private def ps31 : List ℕ := 127::ps30
private theorem c31 : F ps30 82091175=9418172 := by decide +kernel
private theorem v31 : F ps31 10425579253=1187144601 :=
  takeStep (p:=127) (by decide) v30 c31 rfl (by decide) (by decide) rfl

private def ps32 : List ℕ := 131::ps31
private theorem c32 : F ps31 79584574=9058717 := by decide +kernel
private theorem v32 : F ps32 10425579253=1178085884 :=
  takeStep (p:=131) (by decide) v31 c32 rfl (by decide) (by decide) rfl

private def ps33 : List ℕ := 137::ps32
private theorem c33 : F ps32 76099118=8596002 := by decide +kernel
private theorem v33 : F ps33 10425579253=1169489882 :=
  takeStep (p:=137) (by decide) v32 c33 rfl (by decide) (by decide) rfl

private def ps34 : List ℕ := 139::ps33
private theorem c34 : F ps33 75004167=8410725 := by decide +kernel
private theorem v34 : F ps34 10425579253=1161079157 :=
  takeStep (p:=139) (by decide) v33 c34 rfl (by decide) (by decide) rfl

private def ps35 : List ℕ := 149::ps34
private theorem c35 : F ps34 69970330=7790290 := by decide +kernel
private theorem v35 : F ps35 10425579253=1153288867 :=
  takeStep (p:=149) (by decide) v34 c35 rfl (by decide) (by decide) rfl

private def ps36 : List ℕ := 151::ps35
private theorem c36 : F ps35 69043571=7635959 := by decide +kernel
private theorem v36 : F ps36 10425579253=1145652908 :=
  takeStep (p:=151) (by decide) v35 c36 rfl (by decide) (by decide) rfl

private def ps37 : List ℕ := 157::ps36
private theorem c37 : F ps36 66404963=7296145 := by decide +kernel
private theorem v37 : F ps37 10425579253=1138356763 :=
  takeStep (p:=157) (by decide) v36 c37 rfl (by decide) (by decide) rfl

private def ps38 : List ℕ := 163::ps37
private theorem c38 : F ps37 63960608=6983629 := by decide +kernel
private theorem v38 : F ps38 10425579253=1131373134 :=
  takeStep (p:=163) (by decide) v37 c38 rfl (by decide) (by decide) rfl

private def ps39 : List ℕ := 167::ps38
private theorem c39 : F ps38 62428618=6775318 := by decide +kernel
private theorem v39 : F ps39 10425579253=1124597816 :=
  takeStep (p:=167) (by decide) v38 c39 rfl (by decide) (by decide) rfl

private def ps40 : List ℕ := 173::ps39
private theorem c40 : F ps39 60263463=6502070 := by decide +kernel
private theorem v40 : F ps40 10425579253=1118095746 :=
  takeStep (p:=173) (by decide) v39 c40 rfl (by decide) (by decide) rfl

private def ps41 : List ℕ := 179::ps40
private theorem c41 : F ps40 58243459=6248805 := by decide +kernel
private theorem v41 : F ps41 10425579253=1111846941 :=
  takeStep (p:=179) (by decide) v40 c41 rfl (by decide) (by decide) rfl

private def ps42 : List ℕ := 181::ps41
private theorem c42 : F ps41 57599885=6146103 := by decide +kernel
private theorem v42 : F ps42 10425579253=1105700838 :=
  takeStep (p:=181) (by decide) v41 c42 rfl (by decide) (by decide) rfl

private def ps43 : List ℕ := 191::ps42
private theorem c43 : F ps42 54584184=5793440 := by decide +kernel
private theorem v43 : F ps43 10425579253=1099907398 :=
  takeStep (p:=191) (by decide) v42 c43 rfl (by decide) (by decide) rfl

private def ps44 : List ℕ := 193::ps43
private theorem c44 : F ps43 54018545=5704367 := by decide +kernel
private theorem v44 : F ps44 10425579253=1094203031 :=
  takeStep (p:=193) (by decide) v43 c44 rfl (by decide) (by decide) rfl

private def ps45 : List ℕ := 197::ps44
private theorem c45 : F ps44 52921722=5560708 := by decide +kernel
private theorem v45 : F ps45 10425579253=1088642323 :=
  takeStep (p:=197) (by decide) v44 c45 rfl (by decide) (by decide) rfl

private def ps46 : List ℕ := 199::ps45
private theorem c46 : F ps45 52389845=5477909 := by decide +kernel
private theorem v46 : F ps46 10425579253=1083164414 :=
  takeStep (p:=199) (by decide) v45 c46 rfl (by decide) (by decide) rfl

private def ps47 : List ℕ := 211::ps46
private theorem c47 : F ps46 49410328=5141876 := by decide +kernel
private theorem v47 : F ps47 10425579253=1078022538 :=
  takeStep (p:=211) (by decide) v46 c47 rfl (by decide) (by decide) rfl

private def ps48 : List ℕ := 223::ps47
private theorem c48 : F ps47 46751476=4843671 := by decide +kernel
private theorem v48 : F ps48 10425579253=1073178867 :=
  takeStep (p:=223) (by decide) v47 c48 rfl (by decide) (by decide) rfl

private def ps49 : List ℕ := 227::ps48
private theorem c49 : F ps48 45927661=4738104 := by decide +kernel
private theorem v49 : F ps49 10425579253=1068440763 :=
  takeStep (p:=227) (by decide) v48 c49 rfl (by decide) (by decide) rfl

private def ps50 : List ℕ := 229::ps49
private theorem c50 : F ps49 45526546=4676972 := by decide +kernel
private theorem v50 : F ps50 10425579253=1063763791 :=
  takeStep (p:=229) (by decide) v49 c50 rfl (by decide) (by decide) rfl

private def ps51 : List ℕ := 233::ps50
private theorem c51 : F ps50 44744975=4577660 := by decide +kernel
private theorem v51 : F ps51 10425579253=1059186131 :=
  takeStep (p:=233) (by decide) v50 c51 rfl (by decide) (by decide) rfl

private def ps52 : List ℕ := 239::ps51
private theorem c52 : F ps51 43621670=4444795 := by decide +kernel
private theorem v52 : F ps52 10425579253=1054741336 :=
  takeStep (p:=239) (by decide) v51 c52 rfl (by decide) (by decide) rfl

private def ps53 : List ℕ := 241::ps52
private theorem c53 : F ps52 43259664=4390479 := by decide +kernel
private theorem v53 : F ps53 10425579253=1050350857 :=
  takeStep (p:=241) (by decide) v52 c53 rfl (by decide) (by decide) rfl

private def ps54 : List ℕ := 251::ps53
private theorem c54 : F ps53 41536172=4199368 := by decide +kernel
private theorem v54 : F ps54 10425579253=1046151489 :=
  takeStep (p:=251) (by decide) v53 c54 rfl (by decide) (by decide) rfl

private def ps55 : List ℕ := 257::ps54
private theorem c55 : F ps54 40566456=4086020 := by decide +kernel
private theorem v55 : F ps55 10425579253=1042065469 :=
  takeStep (p:=257) (by decide) v54 c55 rfl (by decide) (by decide) rfl

private def ps56 : List ℕ := 263::ps55
private theorem c56 : F ps55 39640985=3978295 := by decide +kernel
private theorem v56 : F ps56 10425579253=1038087174 :=
  takeStep (p:=263) (by decide) v55 c56 rfl (by decide) (by decide) rfl

private def ps57 : List ℕ := 269::ps56
private theorem c57 : F ps56 38756800=3875678 := by decide +kernel
private theorem v57 : F ps57 10425579253=1034211496 :=
  takeStep (p:=269) (by decide) v56 c57 rfl (by decide) (by decide) rfl

private def ps58 : List ℕ := 271::ps57
private theorem c58 : F ps57 38470772=3833545 := by decide +kernel
private theorem v58 : F ps58 10425579253=1030377951 :=
  takeStep (p:=271) (by decide) v57 c58 rfl (by decide) (by decide) rfl

private def ps59 : List ℕ := 277::ps58
private theorem c59 : F ps58 37637470=3737463 := by decide +kernel
private theorem v59 : F ps59 10425579253=1026640488 :=
  takeStep (p:=277) (by decide) v58 c59 rfl (by decide) (by decide) rfl

private def ps60 : List ℕ := 281::ps59
private theorem c60 : F ps59 37101705=3671699 := by decide +kernel
private theorem v60 : F ps60 10425579253=1022968789 :=
  takeStep (p:=281) (by decide) v59 c60 rfl (by decide) (by decide) rfl

private def ps61 : List ℕ := 283::ps60
private theorem c61 : F ps60 36839502=3633420 := by decide +kernel
private theorem v61 : F ps61 10425579253=1019335369 :=
  takeStep (p:=283) (by decide) v60 c61 rfl (by decide) (by decide) rfl

private def ps62 : List ℕ := 293::ps61
private theorem c62 : F ps61 35582181=3497817 := by decide +kernel
private theorem v62 : F ps62 10425579253=1015837552 :=
  takeStep (p:=293) (by decide) v61 c62 rfl (by decide) (by decide) rfl

private def ps63 : List ℕ := 307::ps62
private theorem c63 : F ps62 33959541=3327739 := by decide +kernel
private theorem v63 : F ps63 10425579253=1012509813 :=
  takeStep (p:=307) (by decide) v62 c63 rfl (by decide) (by decide) rfl

private def ps64 : List ℕ := 311::ps63
private theorem c64 : F ps63 33522762=3274684 := by decide +kernel
private theorem v64 : F ps64 10425579253=1009235129 :=
  takeStep (p:=311) (by decide) v63 c64 rfl (by decide) (by decide) rfl

private def ps65 : List ℕ := 313::ps64
private theorem c65 : F ps64 33308559=3243628 := by decide +kernel
private theorem v65 : F ps65 10425579253=1005991501 :=
  takeStep (p:=313) (by decide) v64 c65 rfl (by decide) (by decide) rfl

private def ps66 : List ℕ := 317::ps65
private theorem c66 : F ps65 32888262=3192764 := by decide +kernel
private theorem v66 : F ps66 10425579253=1002798737 :=
  takeStep (p:=317) (by decide) v65 c66 rfl (by decide) (by decide) rfl

private def ps67 : List ℕ := 331::ps66
private theorem c67 : F ps66 31497218=3048322 := by decide +kernel
private theorem v67 : F ps67 10425579253=999750415 :=
  takeStep (p:=331) (by decide) v66 c67 rfl (by decide) (by decide) rfl

private def ps68 : List ℕ := 337::ps67
private theorem c68 : F ps67 30936436=2985133 := by decide +kernel
private theorem v68 : F ps68 10425579253=996765282 :=
  takeStep (p:=337) (by decide) v67 c68 rfl (by decide) (by decide) rfl

private def ps69 : List ℕ := 347::ps68
private theorem c69 : F ps68 30044896=2890525 := by decide +kernel
private theorem v69 : F ps69 10425579253=993874757 :=
  takeStep (p:=347) (by decide) v68 c69 rfl (by decide) (by decide) rfl

private def ps70 : List ℕ := 349::ps69
private theorem c70 : F ps69 29872719=2865629 := by decide +kernel
private theorem v70 : F ps70 10425579253=991009128 :=
  takeStep (p:=349) (by decide) v69 c70 rfl (by decide) (by decide) rfl

private def ps71 : List ℕ := 353::ps70
private theorem c71 : F ps70 29534218=2824906 := by decide +kernel
private theorem v71 : F ps71 10425579253=988184222 :=
  takeStep (p:=353) (by decide) v70 c71 rfl (by decide) (by decide) rfl

private def ps72 : List ℕ := 359::ps71
private theorem c72 : F ps71 29040610=2769670 := by decide +kernel
private theorem v72 : F ps72 10425579253=985414552 :=
  takeStep (p:=359) (by decide) v71 c72 rfl (by decide) (by decide) rfl

private def ps73 : List ℕ := 367::ps72
private theorem c73 : F ps72 28407572=2701586 := by decide +kernel
private theorem v73 : F ps73 10425579253=982712966 :=
  takeStep (p:=367) (by decide) v72 c73 rfl (by decide) (by decide) rfl

private def ps74 : List ℕ := 373::ps73
private theorem c74 : F ps73 27950614=2650603 := by decide +kernel
private theorem v74 : F ps74 10425579253=980062363 :=
  takeStep (p:=373) (by decide) v73 c74 rfl (by decide) (by decide) rfl

private def ps75 : List ℕ := 379::ps74
private theorem c75 : F ps74 27508124=2601329 := by decide +kernel
private theorem v75 : F ps75 10425579253=977461034 :=
  takeStep (p:=379) (by decide) v74 c75 rfl (by decide) (by decide) rfl

private def ps76 : List ℕ := 383::ps75
private theorem c76 : F ps75 27220833=2567075 := by decide +kernel
private theorem v76 : F ps76 10425579253=974893959 :=
  takeStep (p:=383) (by decide) v75 c76 rfl (by decide) (by decide) rfl

private def ps77 : List ℕ := 389::ps76
private theorem c77 : F ps76 26800974=2520522 := by decide +kernel
private theorem v77 : F ps77 10425579253=972373437 :=
  takeStep (p:=389) (by decide) v76 c77 rfl (by decide) (by decide) rfl

private def ps78 : List ℕ := 397::ps77
private theorem c78 : F ps77 26260904=2462914 := by decide +kernel
private theorem v78 : F ps78 10425579253=969910523 :=
  takeStep (p:=397) (by decide) v77 c78 rfl (by decide) (by decide) rfl

private def ps79 : List ℕ := 401::ps78
private theorem c79 : F ps78 25998950=2431812 := by decide +kernel
private theorem v79 : F ps79 10425579253=967478711 :=
  takeStep (p:=401) (by decide) v78 c79 rfl (by decide) (by decide) rfl

private def ps80 : List ℕ := 409::ps79
private theorem c80 : F ps79 25490413=2377730 := by decide +kernel
private theorem v80 : F ps80 10425579253=965100981 :=
  takeStep (p:=409) (by decide) v79 c80 rfl (by decide) (by decide) rfl

private def ps81 : List ℕ := 419::ps80
private theorem c81 : F ps80 24882050=2314730 := by decide +kernel
private theorem v81 : F ps81 10425579253=962786251 :=
  takeStep (p:=419) (by decide) v80 c81 rfl (by decide) (by decide) rfl

private def ps82 : List ℕ := 421::ps81
private theorem c82 : F ps81 24763846=2297782 := by decide +kernel
private theorem v82 : F ps82 10425579253=960488469 :=
  takeStep (p:=421) (by decide) v81 c82 rfl (by decide) (by decide) rfl

private def ps83 : List ℕ := 431::ps82
private theorem c83 : F ps82 24189279=2238450 := by decide +kernel
private theorem v83 : F ps83 10425579253=958250019 :=
  takeStep (p:=431) (by decide) v82 c83 rfl (by decide) (by decide) rfl

private def ps84 : List ℕ := 433::ps83
private theorem c84 : F ps83 24077550=2222478 := by decide +kernel
private theorem v84 : F ps84 10425579253=956027541 :=
  takeStep (p:=433) (by decide) v83 c84 rfl (by decide) (by decide) rfl

private def ps85 : List ℕ := 439::ps84
private theorem c85 : F ps84 23748472=2186398 := by decide +kernel
private theorem v85 : F ps85 10425579253=953841143 :=
  takeStep (p:=439) (by decide) v84 c85 rfl (by decide) (by decide) rfl

private def ps86 : List ℕ := 443::ps85
private theorem c86 : F ps85 23534038=2161193 := by decide +kernel
private theorem v86 : F ps86 10425579253=951679950 :=
  takeStep (p:=443) (by decide) v85 c86 rfl (by decide) (by decide) rfl

private def ps87 : List ℕ := 449::ps86
private theorem c87 : F ps86 23219552=2126839 := by decide +kernel
private theorem v87 : F ps87 10425579253=949553111 :=
  takeStep (p:=449) (by decide) v86 c87 rfl (by decide) (by decide) rfl

private def ps88 : List ℕ := 457::ps87
private theorem c88 : F ps87 22813083=2084272 := by decide +kernel
private theorem v88 : F ps88 10425579253=947468839 :=
  takeStep (p:=457) (by decide) v87 c88 rfl (by decide) (by decide) rfl

private def ps89 : List ℕ := 461::ps88
private theorem c89 : F ps88 22615139=2061034 := by decide +kernel
private theorem v89 : F ps89 10425579253=945407805 :=
  takeStep (p:=461) (by decide) v88 c89 rfl (by decide) (by decide) rfl

private def ps90 : List ℕ := 463::ps89
private theorem c90 : F ps89 22517449=2047127 := by decide +kernel
private theorem v90 : F ps90 10425579253=943360678 :=
  takeStep (p:=463) (by decide) v89 c90 rfl (by decide) (by decide) rfl

private def ps91 : List ℕ := 467::ps90
private theorem c91 : F ps90 22324580=2024623 := by decide +kernel
private theorem v91 : F ps91 10425579253=941336055 :=
  takeStep (p:=467) (by decide) v90 c91 rfl (by decide) (by decide) rfl

private def ps92 : List ℕ := 479::ps91
private theorem c92 : F ps91 21765301=1968807 := by decide +kernel
private theorem v92 : F ps92 10425579253=939367248 :=
  takeStep (p:=479) (by decide) v91 c92 rfl (by decide) (by decide) rfl

private def ps93 : List ℕ := 487::ps92
private theorem c93 : F ps92 21407760=1931651 := by decide +kernel
private theorem v93 : F ps93 10425579253=937435597 :=
  takeStep (p:=487) (by decide) v92 c93 rfl (by decide) (by decide) rfl

private def ps94 : List ℕ := 491::ps93
private theorem c94 : F ps93 21233358=1911311 := by decide +kernel
private theorem v94 : F ps94 10425579253=935524286 :=
  takeStep (p:=491) (by decide) v93 c94 rfl (by decide) (by decide) rfl

private def ps95 : List ℕ := 499::ps94
private theorem c95 : F ps94 20892944=1876054 := by decide +kernel
private theorem v95 : F ps95 10425579253=933648232 :=
  takeStep (p:=499) (by decide) v94 c95 rfl (by decide) (by decide) rfl

private def ps96 : List ℕ := 503::ps95
private theorem c96 : F ps95 20726797=1856771 := by decide +kernel
private theorem v96 : F ps96 10425579253=931791461 :=
  takeStep (p:=503) (by decide) v95 c96 rfl (by decide) (by decide) rfl

private def ps97 : List ℕ := 509::ps96
private theorem c97 : F ps96 20482473=1830495 := by decide +kernel
private theorem v97 : F ps97 10425579253=929960966 :=
  takeStep (p:=509) (by decide) v96 c97 rfl (by decide) (by decide) rfl

private def ps98 : List ℕ := 521::ps97
private theorem c98 : F ps97 20010708=1783921 := by decide +kernel
private theorem v98 : F ps98 10425579253=928177045 :=
  takeStep (p:=521) (by decide) v97 c98 rfl (by decide) (by decide) rfl

private def ps99 : List ℕ := 523::ps98
private theorem c99 : F ps98 19934185=1773094 := by decide +kernel
private theorem v99 : F ps99 10425579253=926403951 :=
  takeStep (p:=523) (by decide) v98 c99 rfl (by decide) (by decide) rfl

private def ps100 : List ℕ := 541::ps99
private theorem c100 : F ps99 19270941=1709671 := by decide +kernel
private theorem v100 : F ps100 10425579253=924694280 :=
  takeStep (p:=541) (by decide) v99 c100 rfl (by decide) (by decide) rfl

private def ps101 : List ℕ := 547::ps100
private theorem c101 : F ps100 19059559=1687112 := by decide +kernel
private theorem v101 : F ps101 10425579253=923007168 :=
  takeStep (p:=547) (by decide) v100 c101 rfl (by decide) (by decide) rfl

private def ps102 : List ℕ := 557::ps101
private theorem c102 : F ps101 18717377=1652911 := by decide +kernel
private theorem v102 : F ps102 10425579253=921354257 :=
  takeStep (p:=557) (by decide) v101 c102 rfl (by decide) (by decide) rfl

private def ps103 : List ℕ := 563::ps102
private theorem c103 : F ps102 18517902=1631601 := by decide +kernel
private theorem v103 : F ps103 10425579253=919722656 :=
  takeStep (p:=563) (by decide) v102 c103 rfl (by decide) (by decide) rfl

private def ps104 : List ℕ := 569::ps103
private theorem c104 : F ps103 18322634=1610864 := by decide +kernel
private theorem v104 : F ps104 10425579253=918111792 :=
  takeStep (p:=569) (by decide) v103 c104 rfl (by decide) (by decide) rfl

private def ps105 : List ℕ := 571::ps104
private theorem c105 : F ps104 18258457=1601803 := by decide +kernel
private theorem v105 : F ps105 10425579253=916509989 :=
  takeStep (p:=571) (by decide) v104 c105 rfl (by decide) (by decide) rfl

private def ps106 : List ℕ := 577::ps105
private theorem c106 : F ps105 18068594=1581667 := by decide +kernel
private theorem v106 : F ps106 10425579253=914928322 :=
  takeStep (p:=577) (by decide) v105 c106 rfl (by decide) (by decide) rfl

private def ps107 : List ℕ := 587::ps106
private theorem c107 : F ps106 17760782=1551208 := by decide +kernel
private theorem v107 : F ps107 10425579253=913377114 :=
  takeStep (p:=587) (by decide) v106 c107 rfl (by decide) (by decide) rfl

private def ps108 : List ℕ := 593::ps107
private theorem c108 : F ps107 17581077=1532185 := by decide +kernel
private theorem v108 : F ps108 10425579253=911844929 :=
  takeStep (p:=593) (by decide) v107 c108 rfl (by decide) (by decide) rfl

private def ps109 : List ℕ := 599::ps108
private theorem c109 : F ps108 17404973=1513530 := by decide +kernel
private theorem v109 : F ps109 10425579253=910331399 :=
  takeStep (p:=599) (by decide) v108 c109 rfl (by decide) (by decide) rfl

private def ps110 : List ℕ := 601::ps109
private theorem c110 : F ps109 17347053=1505375 := by decide +kernel
private theorem v110 : F ps110 10425579253=908826024 :=
  takeStep (p:=601) (by decide) v109 c110 rfl (by decide) (by decide) rfl

private def ps111 : List ℕ := 607::ps110
private theorem c111 : F ps110 17175583=1487286 := by decide +kernel
private theorem v111 : F ps111 10425579253=907338738 :=
  takeStep (p:=607) (by decide) v110 c111 rfl (by decide) (by decide) rfl

private def ps112 : List ℕ := 613::ps111
private theorem c112 : F ps111 17007470=1469602 := by decide +kernel
private theorem v112 : F ps112 10425579253=905869136 :=
  takeStep (p:=613) (by decide) v111 c112 rfl (by decide) (by decide) rfl

private def ps113 : List ℕ := 617::ps112
private theorem c113 : F ps112 16897211=1457005 := by decide +kernel
private theorem v113 : F ps113 10425579253=904412131 :=
  takeStep (p:=617) (by decide) v112 c113 rfl (by decide) (by decide) rfl

private def ps114 : List ℕ := 619::ps113
private theorem c114 : F ps113 16842615=1449374 := by decide +kernel
private theorem v114 : F ps114 10425579253=902962757 :=
  takeStep (p:=619) (by decide) v113 c114 rfl (by decide) (by decide) rfl

private def ps115 : List ℕ := 631::ps114
private theorem c115 : F ps114 16522312=1418561 := by decide +kernel
private theorem v115 : F ps115 10425579253=901544196 :=
  takeStep (p:=631) (by decide) v114 c115 rfl (by decide) (by decide) rfl

private def ps116 : List ℕ := 641::ps115
private theorem c116 : F ps115 16264554=1393438 := by decide +kernel
private theorem v116 : F ps116 10425579253=900150758 :=
  takeStep (p:=641) (by decide) v115 c116 rfl (by decide) (by decide) rfl

private def ps117 : List ℕ := 643::ps116
private theorem c117 : F ps116 16213964=1386354 := by decide +kernel
private theorem v117 : F ps117 10425579253=898764404 :=
  takeStep (p:=643) (by decide) v116 c117 rfl (by decide) (by decide) rfl

private def ps118 : List ℕ := 647::ps117
private theorem c118 : F ps117 16113723=1375005 := by decide +kernel
private theorem v118 : F ps118 10425579253=897389399 :=
  takeStep (p:=647) (by decide) v117 c118 rfl (by decide) (by decide) rfl

private def ps119 : List ℕ := 653::ps118
private theorem c119 : F ps118 15965665=1359589 := by decide +kernel
private theorem v119 : F ps119 10425579253=896029810 :=
  takeStep (p:=653) (by decide) v118 c119 rfl (by decide) (by decide) rfl

private def ps120 : List ℕ := 659::ps119
private theorem c120 : F ps119 15820302=1344411 := by decide +kernel
private theorem v120 : F ps120 10425579253=894685399 :=
  takeStep (p:=659) (by decide) v119 c120 rfl (by decide) (by decide) rfl

private def ps121 : List ℕ := 661::ps120
private theorem c121 : F ps120 15772434=1337740 := by decide +kernel
private theorem v121 : F ps121 10425579253=893347659 :=
  takeStep (p:=661) (by decide) v120 c121 rfl (by decide) (by decide) rfl

private def ps122 : List ℕ := 673::ps121
private theorem c122 : F ps121 15491202=1310986 := by decide +kernel
private theorem v122 : F ps122 10425579253=892036673 :=
  takeStep (p:=673) (by decide) v121 c122 rfl (by decide) (by decide) rfl

private def ps123 : List ℕ := 677::ps122
private theorem c123 : F ps122 15399673=1300682 := by decide +kernel
private theorem v123 : F ps123 10425579253=890735991 :=
  takeStep (p:=677) (by decide) v122 c123 rfl (by decide) (by decide) rfl

private def ps124 : List ℕ := 683::ps123
private theorem c124 : F ps123 15264391=1286703 := by decide +kernel
private theorem v124 : F ps124 10425579253=889449288 :=
  takeStep (p:=683) (by decide) v123 c124 rfl (by decide) (by decide) rfl

private def ps125 : List ℕ := 691::ps124
private theorem c125 : F ps124 15087668=1269206 := by decide +kernel
private theorem v125 : F ps125 10425579253=888180082 :=
  takeStep (p:=691) (by decide) v124 c125 rfl (by decide) (by decide) rfl

private def ps126 : List ℕ := 701::ps125
private theorem c126 : F ps125 14872438=1248532 := by decide +kernel
private theorem v126 : F ps126 10425579253=886931550 :=
  takeStep (p:=701) (by decide) v125 c126 rfl (by decide) (by decide) rfl

private def ps127 : List ℕ := 709::ps126
private theorem c127 : F ps126 14704625=1231953 := by decide +kernel
private theorem v127 : F ps127 10425579253=885699597 :=
  takeStep (p:=709) (by decide) v126 c127 rfl (by decide) (by decide) rfl

private def ps128 : List ℕ := 719::ps127
private theorem c128 : F ps127 14500110=1212394 := by decide +kernel
private theorem v128 : F ps128 10425579253=884487203 :=
  takeStep (p:=719) (by decide) v127 c128 rfl (by decide) (by decide) rfl

private def ps129 : List ℕ := 727::ps128
private theorem c129 : F ps128 14340549=1196652 := by decide +kernel
private theorem v129 : F ps129 10425579253=883290551 :=
  takeStep (p:=727) (by decide) v128 c129 rfl (by decide) (by decide) rfl

private def ps130 : List ℕ := 733::ps129
private theorem c130 : F ps129 14223164=1184596 := by decide +kernel
private theorem v130 : F ps130 10425579253=882105955 :=
  takeStep (p:=733) (by decide) v129 c130 rfl (by decide) (by decide) rfl

private def ps131 : List ℕ := 739::ps130
private theorem c131 : F ps130 14107685=1172770 := by decide +kernel
private theorem v131 : F ps131 10425579253=880933185 :=
  takeStep (p:=739) (by decide) v130 c131 rfl (by decide) (by decide) rfl

private def ps132 : List ℕ := 743::ps131
private theorem c132 : F ps131 14031735=1164333 := by decide +kernel
private theorem v132 : F ps132 10425579253=879768852 :=
  takeStep (p:=743) (by decide) v131 c132 rfl (by decide) (by decide) rfl

private def ps133 : List ℕ := 751::ps132
private theorem c133 : F ps132 13882262=1149718 := by decide +kernel
private theorem v133 : F ps133 10425579253=878619134 :=
  takeStep (p:=751) (by decide) v132 c133 rfl (by decide) (by decide) rfl

private def ps134 : List ℕ := 757::ps133
private theorem c134 : F ps133 13772231=1138437 := by decide +kernel
private theorem v134 : F ps134 10425579253=877480697 :=
  takeStep (p:=757) (by decide) v133 c134 rfl (by decide) (by decide) rfl

private def ps135 : List ℕ := 761::ps134
private theorem c135 : F ps134 13699841=1130386 := by decide +kernel
private theorem v135 : F ps135 10425579253=876350311 :=
  takeStep (p:=761) (by decide) v134 c135 rfl (by decide) (by decide) rfl

private def ps136 : List ℕ := 769::ps135
private theorem c136 : F ps135 13557320=1116489 := by decide +kernel
private theorem v136 : F ps136 10425579253=875233822 :=
  takeStep (p:=769) (by decide) v135 c136 rfl (by decide) (by decide) rfl

private def ps137 : List ℕ := 773::ps136
private theorem c137 : F ps136 13487165=1108754 := by decide +kernel
private theorem v137 : F ps137 10425579253=874125068 :=
  takeStep (p:=773) (by decide) v136 c137 rfl (by decide) (by decide) rfl

private def ps138 : List ℕ := 787::ps137
private theorem c138 : F ps137 13247241=1086826 := by decide +kernel
private theorem v138 : F ps138 10425579253=873038242 :=
  takeStep (p:=787) (by decide) v137 c138 rfl (by decide) (by decide) rfl

private def ps139 : List ℕ := 797::ps138
private theorem c139 : F ps138 13081027=1071169 := by decide +kernel
private theorem v139 : F ps139 10425579253=871967073 :=
  takeStep (p:=797) (by decide) v138 c139 rfl (by decide) (by decide) rfl

private def ps140 : List ℕ := 809::ps139
private theorem c140 : F ps139 12886995=1053288 := by decide +kernel
private theorem v140 : F ps140 10425579253=870913785 :=
  takeStep (p:=809) (by decide) v139 c140 rfl (by decide) (by decide) rfl

private def ps141 : List ℕ := 811::ps140
private theorem c141 : F ps140 12855214=1048933 := by decide +kernel
private theorem v141 : F ps141 10425579253=869864852 :=
  takeStep (p:=811) (by decide) v140 c141 rfl (by decide) (by decide) rfl

private def ps142 : List ℕ := 821::ps141
private theorem c142 : F ps141 12698634=1034164 := by decide +kernel
private theorem v142 : F ps142 10425579253=868830688 :=
  takeStep (p:=821) (by decide) v141 c142 rfl (by decide) (by decide) rfl

private def ps143 : List ℕ := 823::ps142
private theorem c143 : F ps142 12667775=1029948 := by decide +kernel
private theorem v143 : F ps143 10425579253=867800740 :=
  takeStep (p:=823) (by decide) v142 c143 rfl (by decide) (by decide) rfl

private def ps144 : List ℕ := 827::ps143
private theorem c144 : F ps143 12606504=1023198 := by decide +kernel
private theorem v144 : F ps144 10425579253=866777542 :=
  takeStep (p:=827) (by decide) v143 c144 rfl (by decide) (by decide) rfl

private def ps145 : List ℕ := 829::ps144
private theorem c145 : F ps144 12576090=1019049 := by decide +kernel
private theorem v145 : F ps145 10425579253=865758493 :=
  takeStep (p:=829) (by decide) v144 c145 rfl (by decide) (by decide) rfl

private def ps146 : List ℕ := 839::ps145
private theorem c146 : F ps145 12426196=1005095 := by decide +kernel
private theorem v146 : F ps146 10425579253=864753398 :=
  takeStep (p:=839) (by decide) v145 c146 rfl (by decide) (by decide) rfl

private def ps147 : List ℕ := 853::ps146
private theorem c147 : F ps146 12222250=986660 := by decide +kernel
private theorem v147 : F ps147 10425579253=863766738 :=
  takeStep (p:=853) (by decide) v146 c147 rfl (by decide) (by decide) rfl

private def ps148 : List ℕ := 857::ps147
private theorem c148 : F ps147 12165203=980426 := by decide +kernel
private theorem v148 : F ps148 10425579253=862786312 :=
  takeStep (p:=857) (by decide) v147 c148 rfl (by decide) (by decide) rfl

private def ps149 : List ℕ := 859::ps148
private theorem c149 : F ps148 12136879=976570 := by decide +kernel
private theorem v149 : F ps149 10425579253=861809742 :=
  takeStep (p:=859) (by decide) v148 c149 rfl (by decide) (by decide) rfl

private def ps150 : List ℕ := 863::ps149
private theorem c150 : F ps149 12080624=970450 := by decide +kernel
private theorem v150 : F ps150 10425579253=860839292 :=
  takeStep (p:=863) (by decide) v149 c150 rfl (by decide) (by decide) rfl

private def ps151 : List ℕ := 877::ps150
private theorem c151 : F ps150 11887775=953181 := by decide +kernel
private theorem v151 : F ps151 10425579253=859886111 :=
  takeStep (p:=877) (by decide) v150 c151 rfl (by decide) (by decide) rfl

private def ps152 : List ℕ := 881::ps151
private theorem c152 : F ps151 11833801=947307 := by decide +kernel
private theorem v152 : F ps152 10425579253=858938804 :=
  takeStep (p:=881) (by decide) v151 c152 rfl (by decide) (by decide) rfl

private def ps153 : List ℕ := 883::ps152
private theorem c153 : F ps152 11806998=943691 := by decide +kernel
private theorem v153 : F ps153 10425579253=857995113 :=
  takeStep (p:=883) (by decide) v152 c153 rfl (by decide) (by decide) rfl

private def ps154 : List ℕ := 887::ps153
private theorem c154 : F ps153 11753753=937900 := by decide +kernel
private theorem v154 : F ps154 10425579253=857057213 :=
  takeStep (p:=887) (by decide) v153 c154 rfl (by decide) (by decide) rfl

private def ps155 : List ℕ := 907::ps154
private theorem c155 : F ps154 11494574=915376 := by decide +kernel
private theorem v155 : F ps155 10425579253=856141837 :=
  takeStep (p:=907) (by decide) v154 c155 rfl (by decide) (by decide) rfl

private def ps156 : List ℕ := 911::ps155
private theorem c156 : F ps155 11444104=909893 := by decide +kernel
private theorem v156 : F ps156 10425579253=855231944 :=
  takeStep (p:=911) (by decide) v155 c156 rfl (by decide) (by decide) rfl

private def ps157 : List ℕ := 919::ps156
private theorem c157 : F ps156 11344482=900498 := by decide +kernel
private theorem v157 : F ps157 10425579253=854331446 :=
  takeStep (p:=919) (by decide) v156 c157 rfl (by decide) (by decide) rfl

private def ps158 : List ℕ := 929::ps157
private theorem c158 : F ps157 11222367=889317 := by decide +kernel
private theorem v158 : F ps158 10425579253=853442129 :=
  takeStep (p:=929) (by decide) v157 c158 rfl (by decide) (by decide) rfl

private def ps159 : List ℕ := 937::ps158
private theorem c159 : F ps158 11126552=880273 := by decide +kernel
private theorem v159 : F ps159 10425579253=852561856 :=
  takeStep (p:=937) (by decide) v158 c159 rfl (by decide) (by decide) rfl

private def ps160 : List ℕ := 941::ps159
private theorem c160 : F ps159 11079255=875203 := by decide +kernel
private theorem v160 : F ps160 10425579253=851686653 :=
  takeStep (p:=941) (by decide) v159 c160 rfl (by decide) (by decide) rfl

private def ps161 : List ℕ := 947::ps160
private theorem c161 : F ps160 11009059=868296 := by decide +kernel
private theorem v161 : F ps161 10425579253=850818357 :=
  takeStep (p:=947) (by decide) v160 c161 rfl (by decide) (by decide) rfl

private def ps162 : List ℕ := 953::ps161
private theorem c162 : F ps161 10939747=861485 := by decide +kernel
private theorem v162 : F ps162 10425579253=849956872 :=
  takeStep (p:=953) (by decide) v161 c162 rfl (by decide) (by decide) rfl

private def ps163 : List ℕ := 967::ps162
private theorem c163 : F ps162 10781364=847518 := by decide +kernel
private theorem v163 : F ps163 10425579253=849109354 :=
  takeStep (p:=967) (by decide) v162 c163 rfl (by decide) (by decide) rfl

private def ps164 : List ℕ := 971::ps163
private theorem c164 : F ps163 10736950=842772 := by decide +kernel
private theorem v164 : F ps164 10425579253=848266582 :=
  takeStep (p:=971) (by decide) v163 c164 rfl (by decide) (by decide) rfl

private def ps165 : List ℕ := 977::ps164
private theorem c165 : F ps164 10671012=836283 := by decide +kernel
private theorem v165 : F ps165 10425579253=847430299 :=
  takeStep (p:=977) (by decide) v164 c165 rfl (by decide) (by decide) rfl

private def ps166 : List ℕ := 983::ps165
private theorem c166 : F ps165 10605879=829903 := by decide +kernel
private theorem v166 : F ps166 10425579253=846600396 :=
  takeStep (p:=983) (by decide) v165 c166 rfl (by decide) (by decide) rfl

private def ps167 : List ℕ := 991::ps166
private theorem c167 : F ps166 10520261=821921 := by decide +kernel
private theorem v167 : F ps167 10425579253=845778475 :=
  takeStep (p:=991) (by decide) v166 c167 rfl (by decide) (by decide) rfl

private def ps168 : List ℕ := 997::ps167
private theorem c168 : F ps167 10456950=815748 := by decide +kernel
private theorem v168 : F ps168 10425579253=844962727 :=
  takeStep (p:=997) (by decide) v167 c168 rfl (by decide) (by decide) rfl

private def ps169 : List ℕ := 1009::ps168
private theorem c169 : F ps168 10332585=804685 := by decide +kernel
private theorem v169 : F ps169 10425579253=844158042 :=
  takeStep (p:=1009) (by decide) v168 c169 rfl (by decide) (by decide) rfl

private def ps170 : List ℕ := 1013::ps169
private theorem c170 : F ps169 10291786=800369 := by decide +kernel
private theorem v170 : F ps170 10425579253=843357673 :=
  takeStep (p:=1013) (by decide) v169 c170 rfl (by decide) (by decide) rfl

private def ps171 : List ℕ := 1019::ps170
private theorem c171 : F ps170 10231186=794479 := by decide +kernel
private theorem v171 : F ps171 10425579253=842563194 :=
  takeStep (p:=1019) (by decide) v170 c171 rfl (by decide) (by decide) rfl

private def ps172 : List ℕ := 1021::ps171
private theorem c172 : F ps171 10211145=791803 := by decide +kernel
private theorem v172 : F ps172 10425579253=841771391 :=
  takeStep (p:=1021) (by decide) v171 c172 rfl (by decide) (by decide) rfl

private def ps173 : List ℕ := 1031::ps172
private theorem c173 : F ps172 10112104=782936 := by decide +kernel
private theorem v173 : F ps173 10425579253=840988455 :=
  takeStep (p:=1031) (by decide) v172 c173 rfl (by decide) (by decide) rfl

private def ps174 : List ℕ := 1033::ps173
private theorem c174 : F ps173 10092525=780361 := by decide +kernel
private theorem v174 : F ps174 10425579253=840208094 :=
  takeStep (p:=1033) (by decide) v173 c174 rfl (by decide) (by decide) rfl

private def ps175 : List ℕ := 1039::ps174
private theorem c175 : F ps174 10034243=774733 := by decide +kernel
private theorem v175 : F ps175 10425579253=839433361 :=
  takeStep (p:=1039) (by decide) v174 c175 rfl (by decide) (by decide) rfl

private def ps176 : List ℕ := 1049::ps175
private theorem c176 : F ps175 9938588=766182 := by decide +kernel
private theorem v176 : F ps176 10425579253=838667179 :=
  takeStep (p:=1049) (by decide) v175 c176 rfl (by decide) (by decide) rfl

private def ps177 : List ℕ := 1051::ps176
private theorem c177 : F ps176 9919675=763700 := by decide +kernel
private theorem v177 : F ps177 10425579253=837903479 :=
  takeStep (p:=1051) (by decide) v176 c177 rfl (by decide) (by decide) rfl

private def ps178 : List ℕ := 1061::ps177
private theorem c178 : F ps177 9826182=755392 := by decide +kernel
private theorem v178 : F ps178 10425579253=837148087 :=
  takeStep (p:=1061) (by decide) v177 c178 rfl (by decide) (by decide) rfl

private def ps179 : List ℕ := 1063::ps178
private theorem c179 : F ps178 9807694=752961 := by decide +kernel
private theorem v179 : F ps179 10425579253=836395126 :=
  takeStep (p:=1063) (by decide) v178 c179 rfl (by decide) (by decide) rfl

private def ps180 : List ℕ := 1069::ps179
private theorem c180 : F ps179 9752646=747706 := by decide +kernel
private theorem v180 : F ps180 10425579253=835647420 :=
  takeStep (p:=1069) (by decide) v179 c180 rfl (by decide) (by decide) rfl

private def ps181 : List ℕ := 1087::ps180
private theorem c181 : F ps180 9591149=734117 := by decide +kernel
private theorem v181 : F ps181 10425579253=834913303 :=
  takeStep (p:=1087) (by decide) v180 c181 rfl (by decide) (by decide) rfl

private def ps182 : List ℕ := 1091::ps181
private theorem c182 : F ps181 9555984=730419 := by decide +kernel
private theorem v182 : F ps182 10425579253=834182884 :=
  takeStep (p:=1091) (by decide) v181 c182 rfl (by decide) (by decide) rfl

private def ps183 : List ℕ := 1093::ps182
private theorem c183 : F ps182 9538498=728124 := by decide +kernel
private theorem v183 : F ps183 10425579253=833454760 :=
  takeStep (p:=1093) (by decide) v182 c183 rfl (by decide) (by decide) rfl

private def ps184 : List ℕ := 1097::ps183
private theorem c184 : F ps183 9503718=724525 := by decide +kernel
private theorem v184 : F ps184 10425579253=832730235 :=
  takeStep (p:=1097) (by decide) v183 c184 rfl (by decide) (by decide) rfl

private def ps185 : List ℕ := 1103::ps184
private theorem c185 : F ps184 9452021=719639 := by decide +kernel
private theorem v185 : F ps185 10425579253=832010596 :=
  takeStep (p:=1103) (by decide) v184 c185 rfl (by decide) (by decide) rfl

private def ps186 : List ℕ := 1109::ps185
private theorem c186 : F ps185 9400883=714785 := by decide +kernel
private theorem v186 : F ps186 10425579253=831295811 :=
  takeStep (p:=1109) (by decide) v185 c186 rfl (by decide) (by decide) rfl

private def ps187 : List ℕ := 1117::ps186
private theorem c187 : F ps186 9333553=708682 := by decide +kernel
private theorem v187 : F ps187 10425579253=830587129 :=
  takeStep (p:=1117) (by decide) v186 c187 rfl (by decide) (by decide) rfl

private def ps188 : List ℕ := 1123::ps187
private theorem c188 : F ps187 9283685=703963 := by decide +kernel
private theorem v188 : F ps188 10425579253=829883166 :=
  takeStep (p:=1123) (by decide) v187 c188 rfl (by decide) (by decide) rfl

private def ps189 : List ℕ := 1129::ps188
private theorem c189 : F ps188 9234348=699307 := by decide +kernel
private theorem v189 : F ps189 10425579253=829183859 :=
  takeStep (p:=1129) (by decide) v188 c189 rfl (by decide) (by decide) rfl

private def ps190 : List ℕ := 1151::ps189
private theorem c190 : F ps189 9057844=684801 := by decide +kernel
private theorem v190 : F ps190 10425579253=828499058 :=
  takeStep (p:=1151) (by decide) v189 c190 rfl (by decide) (by decide) rfl

private def ps191 : List ℕ := 1153::ps190
private theorem c191 : F ps190 9042132=682806 := by decide +kernel
private theorem v191 : F ps191 10425579253=827816252 :=
  takeStep (p:=1153) (by decide) v190 c191 rfl (by decide) (by decide) rfl

private def ps192 : List ℕ := 1163::ps191
private theorem c192 : F ps191 8964384=676027 := by decide +kernel
private theorem v192 : F ps192 10425579253=827140225 :=
  takeStep (p:=1163) (by decide) v191 c192 rfl (by decide) (by decide) rfl

private def ps193 : List ℕ := 1171::ps192
private theorem c193 : F ps192 8903141=670541 := by decide +kernel
private theorem v193 : F ps193 10425579253=826469684 :=
  takeStep (p:=1171) (by decide) v192 c193 rfl (by decide) (by decide) rfl

private def ps194 : List ℕ := 1181::ps193
private theorem c194 : F ps193 8827755=664022 := by decide +kernel
private theorem v194 : F ps194 10425579253=825805662 :=
  takeStep (p:=1181) (by decide) v193 c194 rfl (by decide) (by decide) rfl

private def ps195 : List ℕ := 1187::ps194
private theorem c195 : F ps194 8783133=659852 := by decide +kernel
private theorem v195 : F ps195 10425579253=825145810 :=
  takeStep (p:=1187) (by decide) v194 c195 rfl (by decide) (by decide) rfl

private def ps196 : List ℕ := 1193::ps195
private theorem c196 : F ps195 8738959=655704 := by decide +kernel
private theorem v196 : F ps196 10425579253=824490106 :=
  takeStep (p:=1193) (by decide) v195 c196 rfl (by decide) (by decide) rfl

private def ps197 : List ℕ := 1201::ps196
private theorem c197 : F ps196 8680748=650474 := by decide +kernel
private theorem v197 : F ps197 10425579253=823839632 :=
  takeStep (p:=1201) (by decide) v196 c197 rfl (by decide) (by decide) rfl

private def ps198 : List ℕ := 1213::ps197
private theorem c198 : F ps197 8594871=643193 := by decide +kernel
private theorem v198 : F ps198 10425579253=823196439 :=
  takeStep (p:=1213) (by decide) v197 c198 rfl (by decide) (by decide) rfl

private def ps199 : List ℕ := 1217::ps198
private theorem c199 : F ps198 8566622=640308 := by decide +kernel
private theorem v199 : F ps199 10425579253=822556131 :=
  takeStep (p:=1217) (by decide) v198 c199 rfl (by decide) (by decide) rfl

private def ps200 : List ℕ := 1223::ps199
private theorem c200 : F ps199 8524594=636381 := by decide +kernel
private theorem v200 : F ps200 10425579253=821919750 :=
  takeStep (p:=1223) (by decide) v199 c200 rfl (by decide) (by decide) rfl

private def ps201 : List ℕ := 1229::ps200
private theorem c201 : F ps200 8482977=632502 := by decide +kernel
private theorem v201 : F ps201 10425579253=821287248 :=
  takeStep (p:=1229) (by decide) v200 c201 rfl (by decide) (by decide) rfl

private def ps202 : List ℕ := 1231::ps201
private theorem c202 : F ps201 8469195=630759 := by decide +kernel
private theorem v202 : F ps202 10425579253=820656489 :=
  takeStep (p:=1231) (by decide) v201 c202 rfl (by decide) (by decide) rfl

private def ps203 : List ℕ := 1237::ps202
private theorem c203 : F ps202 8428115=626976 := by decide +kernel
private theorem v203 : F ps203 10425579253=820029513 :=
  takeStep (p:=1237) (by decide) v202 c203 rfl (by decide) (by decide) rfl

private def ps204 : List ℕ := 1249::ps203
private theorem c204 : F ps203 8347141=620206 := by decide +kernel
private theorem v204 : F ps204 10425579253=819409307 :=
  takeStep (p:=1249) (by decide) v203 c204 rfl (by decide) (by decide) rfl

private def ps205 : List ℕ := 1259::ps204
private theorem c205 : F ps204 8280841=614547 := by decide +kernel
private theorem v205 : F ps205 10425579253=818794760 :=
  takeStep (p:=1259) (by decide) v204 c205 rfl (by decide) (by decide) rfl

private def ps206 : List ℕ := 1277::ps205
private theorem c206 : F ps205 8164118=605073 := by decide +kernel
private theorem v206 : F ps206 10425579253=818189687 :=
  takeStep (p:=1277) (by decide) v205 c206 rfl (by decide) (by decide) rfl

private def ps207 : List ℕ := 1279::ps206
private theorem c207 : F ps206 8151352=603476 := by decide +kernel
private theorem v207 : F ps207 10425579253=817586211 :=
  takeStep (p:=1279) (by decide) v206 c207 rfl (by decide) (by decide) rfl

private def ps208 : List ℕ := 1283::ps207
private theorem c208 : F ps207 8125938=600931 := by decide +kernel
private theorem v208 : F ps208 10425579253=816985280 :=
  takeStep (p:=1283) (by decide) v207 c208 rfl (by decide) (by decide) rfl

private def ps209 : List ℕ := 1289::ps208
private theorem c209 : F ps208 8088114=597477 := by decide +kernel
private theorem v209 : F ps209 10425579253=816387803 :=
  takeStep (p:=1289) (by decide) v208 c209 rfl (by decide) (by decide) rfl

private def ps210 : List ℕ := 1291::ps209
private theorem c210 : F ps209 8075584=595956 := by decide +kernel
private theorem v210 : F ps210 10425579253=815791847 :=
  takeStep (p:=1291) (by decide) v209 c210 rfl (by decide) (by decide) rfl

private def ps211 : List ℕ := 1297::ps210
private theorem c211 : F ps210 8038226=592506 := by decide +kernel
private theorem v211 : F ps211 10425579253=815199341 :=
  takeStep (p:=1297) (by decide) v210 c211 rfl (by decide) (by decide) rfl

private def ps212 : List ℕ := 1301::ps211
private theorem c212 : F ps211 8013512=590084 := by decide +kernel
private theorem v212 : F ps212 10425579253=814609257 :=
  takeStep (p:=1301) (by decide) v211 c212 rfl (by decide) (by decide) rfl

private def ps213 : List ℕ := 1303::ps212
private theorem c213 : F ps212 8001212=588573 := by decide +kernel
private theorem v213 : F ps213 10425579253=814020684 :=
  takeStep (p:=1303) (by decide) v212 c213 rfl (by decide) (by decide) rfl

private def ps214 : List ℕ := 1307::ps213
private theorem c214 : F ps213 7976724=586159 := by decide +kernel
private theorem v214 : F ps214 10425579253=813434525 :=
  takeStep (p:=1307) (by decide) v213 c214 rfl (by decide) (by decide) rfl

private def ps215 : List ℕ := 1319::ps214
private theorem c215 : F ps214 7904154=580138 := by decide +kernel
private theorem v215 : F ps215 10425579253=812854387 :=
  takeStep (p:=1319) (by decide) v214 c215 rfl (by decide) (by decide) rfl

private def ps216 : List ℕ := 1321::ps215
private theorem c216 : F ps215 7892187=578701 := by decide +kernel
private theorem v216 : F ps216 10425579253=812275686 :=
  takeStep (p:=1321) (by decide) v215 c216 rfl (by decide) (by decide) rfl

private def ps217 : List ℕ := 1327::ps216
private theorem c217 : F ps216 7856502=575455 := by decide +kernel
private theorem v217 : F ps217 10425579253=811700231 :=
  takeStep (p:=1327) (by decide) v216 c217 rfl (by decide) (by decide) rfl

private def ps218 : List ℕ := 1361::ps217
private theorem c218 : F ps217 7660234=560338 := by decide +kernel
private theorem v218 : F ps218 10425579253=811139893 :=
  takeStep (p:=1361) (by decide) v217 c218 rfl (by decide) (by decide) rfl

private def ps219 : List ℕ := 1367::ps218
private theorem c219 : F ps218 7626612=557312 := by decide +kernel
private theorem v219 : F ps219 10425579253=810582581 :=
  takeStep (p:=1367) (by decide) v218 c219 rfl (by decide) (by decide) rfl

private def ps220 : List ℕ := 1373::ps219
private theorem c220 : F ps219 7593284=554296 := by decide +kernel
private theorem v220 : F ps220 10425579253=810028285 :=
  takeStep (p:=1373) (by decide) v219 c220 rfl (by decide) (by decide) rfl

private def ps221 : List ℕ := 1381::ps220
private theorem c221 : F ps220 7549297=550556 := by decide +kernel
private theorem v221 : F ps221 10425579253=809477729 :=
  takeStep (p:=1381) (by decide) v220 c221 rfl (by decide) (by decide) rfl

private def ps222 : List ℕ := 1399::ps221
private theorem c222 : F ps221 7452165=542920 := by decide +kernel
private theorem v222 : F ps222 10425579253=808934809 :=
  takeStep (p:=1399) (by decide) v221 c222 rfl (by decide) (by decide) rfl

private def ps223 : List ℕ := 1409::ps222
private theorem c223 : F ps222 7399275=538511 := by decide +kernel
private theorem v223 : F ps223 10425579253=808396298 :=
  takeStep (p:=1409) (by decide) v222 c223 rfl (by decide) (by decide) rfl

private def ps224 : List ℕ := 1423::ps223
private theorem c224 : F ps223 7326478=532691 := by decide +kernel
private theorem v224 : F ps224 10425579253=807863607 :=
  takeStep (p:=1423) (by decide) v223 c224 rfl (by decide) (by decide) rfl

private def ps225 : List ℕ := 1427::ps224
private theorem c225 : F ps224 7305942=530711 := by decide +kernel
private theorem v225 : F ps225 10425579253=807332896 :=
  takeStep (p:=1427) (by decide) v224 c225 rfl (by decide) (by decide) rfl

private def ps226 : List ℕ := 1429::ps225
private theorem c226 : F ps225 7295716=529504 := by decide +kernel
private theorem v226 : F ps226 10425579253=806803392 :=
  takeStep (p:=1429) (by decide) v225 c226 rfl (by decide) (by decide) rfl

private def ps227 : List ℕ := 1433::ps226
private theorem c227 : F ps226 7275351=527544 := by decide +kernel
private theorem v227 : F ps227 10425579253=806275848 :=
  takeStep (p:=1433) (by decide) v226 c227 rfl (by decide) (by decide) rfl

private def ps228 : List ℕ := 1439::ps227
private theorem c228 : F ps227 7245016=524867 := by decide +kernel
private theorem v228 : F ps228 10425579253=805750981 :=
  takeStep (p:=1439) (by decide) v227 c228 rfl (by decide) (by decide) rfl

private def ps229 : List ℕ := 1447::ps228
private theorem c229 : F ps228 7204961=521479 := by decide +kernel
private theorem v229 : F ps229 10425579253=805229502 :=
  takeStep (p:=1447) (by decide) v228 c229 rfl (by decide) (by decide) rfl

private def ps230 : List ℕ := 1451::ps229
private theorem c230 : F ps229 7185099=519588 := by decide +kernel
private theorem v230 : F ps230 10425579253=804709914 :=
  takeStep (p:=1451) (by decide) v229 c230 rfl (by decide) (by decide) rfl

private def ps231 : List ℕ := 1453::ps230
private theorem c231 : F ps230 7175209=518449 := by decide +kernel
private theorem v231 : F ps231 10425579253=804191465 :=
  takeStep (p:=1453) (by decide) v230 c231 rfl (by decide) (by decide) rfl

private def ps232 : List ℕ := 1459::ps231
private theorem c232 : F ps231 7145702=515860 := by decide +kernel
private theorem v232 : F ps232 10425579253=803675605 :=
  takeStep (p:=1459) (by decide) v231 c232 rfl (by decide) (by decide) rfl

private def ps233 : List ℕ := 1471::ps232
private theorem c233 : F ps232 7087409=511200 := by decide +kernel
private theorem v233 : F ps233 10425579253=803164405 :=
  takeStep (p:=1471) (by decide) v232 c233 rfl (by decide) (by decide) rfl

private def ps234 : List ℕ := 1481::ps233
private theorem c234 : F ps233 7039553=507316 := by decide +kernel
private theorem v234 : F ps234 10425579253=802657089 :=
  takeStep (p:=1481) (by decide) v233 c234 rfl (by decide) (by decide) rfl

private def ps235 : List ℕ := 1483::ps234
private theorem c235 : F ps234 7030060=506198 := by decide +kernel
private theorem v235 : F ps235 10425579253=802150891 :=
  takeStep (p:=1483) (by decide) v234 c235 rfl (by decide) (by decide) rfl

private def ps236 : List ℕ := 1487::ps235
private theorem c236 : F ps235 7011149=504396 := by decide +kernel
private theorem v236 : F ps236 10425579253=801646495 :=
  takeStep (p:=1487) (by decide) v235 c236 rfl (by decide) (by decide) rfl

private def ps237 : List ℕ := 1489::ps236
private theorem c237 : F ps236 7001732=503326 := by decide +kernel
private theorem v237 : F ps237 10425579253=801143169 :=
  takeStep (p:=1489) (by decide) v236 c237 rfl (by decide) (by decide) rfl

private def ps238 : List ℕ := 1493::ps237
private theorem c238 : F ps237 6982973=501573 := by decide +kernel
private theorem v238 : F ps238 10425579253=800641596 :=
  takeStep (p:=1493) (by decide) v237 c238 rfl (by decide) (by decide) rfl

private def ps239 : List ℕ := 1499::ps238
private theorem c239 : F ps238 6955022=499175 := by decide +kernel
private theorem v239 : F ps239 10425579253=800142421 :=
  takeStep (p:=1499) (by decide) v238 c239 rfl (by decide) (by decide) rfl

private def ps240 : List ℕ := 1511::ps239
private theorem c240 : F ps239 6899787=494768 := by decide +kernel
private theorem v240 : F ps240 10425579253=799647653 :=
  takeStep (p:=1511) (by decide) v239 c240 rfl (by decide) (by decide) rfl

private def ps241 : List ℕ := 1523::ps240
private theorem c241 : F ps240 6845423=490437 := by decide +kernel
private theorem v241 : F ps241 10425579253=799157216 :=
  takeStep (p:=1523) (by decide) v240 c241 rfl (by decide) (by decide) rfl

private def ps242 : List ℕ := 1531::ps241
private theorem c242 : F ps241 6809653=487460 := by decide +kernel
private theorem v242 : F ps242 10425579253=798669756 :=
  takeStep (p:=1531) (by decide) v241 c242 rfl (by decide) (by decide) rfl

private def ps243 : List ℕ := 1543::ps242
private theorem c243 : F ps242 6756694=483313 := by decide +kernel
private theorem v243 : F ps243 10425579253=798186443 :=
  takeStep (p:=1543) (by decide) v242 c243 rfl (by decide) (by decide) rfl

private def ps244 : List ℕ := 1549::ps243
private theorem c244 : F ps243 6730522=481066 := by decide +kernel
private theorem v244 : F ps244 10425579253=797705377 :=
  takeStep (p:=1549) (by decide) v243 c244 rfl (by decide) (by decide) rfl

private def ps245 : List ℕ := 1553::ps244
private theorem c245 : F ps244 6713186=479463 := by decide +kernel
private theorem v245 : F ps245 10425579253=797225914 :=
  takeStep (p:=1553) (by decide) v244 c245 rfl (by decide) (by decide) rfl

private def ps246 : List ℕ := 1559::ps245
private theorem c246 : F ps245 6687350=477239 := by decide +kernel
private theorem v246 : F ps246 10425579253=796748675 :=
  takeStep (p:=1559) (by decide) v245 c246 rfl (by decide) (by decide) rfl

private def ps247 : List ℕ := 1567::ps246
private theorem c247 : F ps246 6653209=474475 := by decide +kernel
private theorem v247 : F ps247 10425579253=796274200 :=
  takeStep (p:=1567) (by decide) v246 c247 rfl (by decide) (by decide) rfl

private def ps248 : List ℕ := 1571::ps247
private theorem c248 : F ps247 6636269=472925 := by decide +kernel
private theorem v248 : F ps248 10425579253=795801275 :=
  takeStep (p:=1571) (by decide) v247 c248 rfl (by decide) (by decide) rfl

private def ps249 : List ℕ := 1579::ps248
private theorem c249 : F ps248 6602646=470195 := by decide +kernel
private theorem v249 : F ps249 10425579253=795331080 :=
  takeStep (p:=1579) (by decide) v248 c249 rfl (by decide) (by decide) rfl

private def ps250 : List ℕ := 1583::ps249
private theorem c250 : F ps249 6585962=468686 := by decide +kernel
private theorem v250 : F ps250 10425579253=794862394 :=
  takeStep (p:=1583) (by decide) v249 c250 rfl (by decide) (by decide) rfl

private def ps251 : List ℕ := 1597::ps250
private theorem c251 : F ps250 6528227=464213 := by decide +kernel
private theorem v251 : F ps251 10425579253=794398181 :=
  takeStep (p:=1597) (by decide) v250 c251 rfl (by decide) (by decide) rfl

private def ps252 : List ℕ := 1601::ps251
private theorem c252 : F ps251 6511917=462752 := by decide +kernel
private theorem v252 : F ps252 10425579253=793935429 :=
  takeStep (p:=1601) (by decide) v251 c252 rfl (by decide) (by decide) rfl

private def ps253 : List ℕ := 1607::ps252
private theorem c253 : F ps252 6487603=460695 := by decide +kernel
private theorem v253 : F ps253 10425579253=793474734 :=
  takeStep (p:=1607) (by decide) v252 c253 rfl (by decide) (by decide) rfl

private def ps254 : List ℕ := 1609::ps253
private theorem c254 : F ps253 6479539=459818 := by decide +kernel
private theorem v254 : F ps254 10425579253=793014916 :=
  takeStep (p:=1609) (by decide) v253 c254 rfl (by decide) (by decide) rfl

private def ps255 : List ℕ := 1613::ps254
private theorem c255 : F ps254 6463471=458384 := by decide +kernel
private theorem v255 : F ps255 10425579253=792556532 :=
  takeStep (p:=1613) (by decide) v254 c255 rfl (by decide) (by decide) rfl

private def ps256 : List ℕ := 1619::ps255
private theorem c256 : F ps255 6439517=456387 := by decide +kernel
private theorem v256 : F ps256 10425579253=792100145 :=
  takeStep (p:=1619) (by decide) v255 c256 rfl (by decide) (by decide) rfl

private def ps257 : List ℕ := 1621::ps256
private theorem c257 : F ps256 6431572=455538 := by decide +kernel
private theorem v257 : F ps257 10425579253=791644607 :=
  takeStep (p:=1621) (by decide) v256 c257 rfl (by decide) (by decide) rfl

private def ps258 : List ℕ := 1627::ps257
private theorem c258 : F ps257 6407854=453566 := by decide +kernel
private theorem v258 : F ps258 10425579253=791191041 :=
  takeStep (p:=1627) (by decide) v257 c258 rfl (by decide) (by decide) rfl

private def ps259 : List ℕ := 1637::ps258
private theorem c259 : F ps258 6368710=450567 := by decide +kernel
private theorem v259 : F ps259 10425579253=790740474 :=
  takeStep (p:=1637) (by decide) v258 c259 rfl (by decide) (by decide) rfl

private def ps260 : List ℕ := 1657::ps259
private theorem c260 : F ps259 6291840=444846 := by decide +kernel
private theorem v260 : F ps260 10425579253=790295628 :=
  takeStep (p:=1657) (by decide) v259 c260 rfl (by decide) (by decide) rfl

private def ps261 : List ℕ := 1663::ps260
private theorem c261 : F ps260 6269139=442949 := by decide +kernel
private theorem v261 : F ps261 10425579253=789852679 :=
  takeStep (p:=1663) (by decide) v260 c261 rfl (by decide) (by decide) rfl

private def ps262 : List ℕ := 1667::ps261
private theorem c262 : F ps261 6254096=441615 := by decide +kernel
private theorem v262 : F ps262 10425579253=789411064 :=
  takeStep (p:=1667) (by decide) v261 c262 rfl (by decide) (by decide) rfl

private def ps263 : List ℕ := 1669::ps262
private theorem c263 : F ps262 6246602=440830 := by decide +kernel
private theorem v263 : F ps263 10425579253=788970234 :=
  takeStep (p:=1669) (by decide) v262 c263 rfl (by decide) (by decide) rfl

private def ps264 : List ℕ := 1693::ps263
private theorem c264 : F ps263 6158050=434381 := by decide +kernel
private theorem v264 : F ps264 10425579253=788535853 :=
  takeStep (p:=1693) (by decide) v263 c264 rfl (by decide) (by decide) rfl

private def ps265 : List ℕ := 1697::ps264
private theorem c265 : F ps264 6143535=433112 := by decide +kernel
private theorem v265 : F ps265 10425579253=788102741 :=
  takeStep (p:=1697) (by decide) v264 c265 rfl (by decide) (by decide) rfl

private def ps266 : List ℕ := 1699::ps265
private theorem c266 : F ps265 6136303=432362 := by decide +kernel
private theorem v266 : F ps266 10425579253=787670379 :=
  takeStep (p:=1699) (by decide) v265 c266 rfl (by decide) (by decide) rfl

private def ps267 : List ℕ := 1709::ps266
private theorem c267 : F ps266 6100397=429631 := by decide +kernel
private theorem v267 : F ps267 10425579253=787240748 :=
  takeStep (p:=1709) (by decide) v266 c267 rfl (by decide) (by decide) rfl

private def ps268 : List ℕ := 1721::ps267
private theorem c268 : F ps267 6057861=426432 := by decide +kernel
private theorem v268 : F ps268 10425579253=786814316 :=
  takeStep (p:=1721) (by decide) v267 c268 rfl (by decide) (by decide) rfl

private def ps269 : List ℕ := 1723::ps268
private theorem c269 : F ps268 6050829=425701 := by decide +kernel
private theorem v269 : F ps269 10425579253=786388615 :=
  takeStep (p:=1723) (by decide) v268 c269 rfl (by decide) (by decide) rfl

private def ps270 : List ℕ := 1733::ps269
private theorem c270 : F ps269 6015914=423072 := by decide +kernel
private theorem v270 : F ps270 10425579253=785965543 :=
  takeStep (p:=1733) (by decide) v269 c270 rfl (by decide) (by decide) rfl

private def ps271 : List ℕ := 1741::ps270
private theorem c271 : F ps270 5988270=420937 := by decide +kernel
private theorem v271 : F ps271 10425579253=785544606 :=
  takeStep (p:=1741) (by decide) v270 c271 rfl (by decide) (by decide) rfl

private def ps272 : List ℕ := 1747::ps271
private theorem c272 : F ps271 5967704=419308 := by decide +kernel
private theorem v272 : F ps272 10425579253=785125298 :=
  takeStep (p:=1747) (by decide) v271 c272 rfl (by decide) (by decide) rfl

private def ps273 : List ℕ := 1753::ps272
private theorem c273 : F ps272 5947278=417684 := by decide +kernel
private theorem v273 : F ps273 10425579253=784707614 :=
  takeStep (p:=1753) (by decide) v272 c273 rfl (by decide) (by decide) rfl

private def ps274 : List ℕ := 1759::ps273
private theorem c274 : F ps273 5926992=416079 := by decide +kernel
private theorem v274 : F ps274 10425579253=784291535 :=
  takeStep (p:=1759) (by decide) v273 c274 rfl (by decide) (by decide) rfl

private def ps275 : List ℕ := 1777::ps274
private theorem c275 : F ps274 5866955=411662 := by decide +kernel
private theorem v275 : F ps275 10425579253=783879873 :=
  takeStep (p:=1777) (by decide) v274 c275 rfl (by decide) (by decide) rfl

private def ps276 : List ℕ := 1783::ps275
private theorem c276 : F ps275 5847212=410132 := by decide +kernel
private theorem v276 : F ps276 10425579253=783469741 :=
  takeStep (p:=1783) (by decide) v275 c276 rfl (by decide) (by decide) rfl

private def ps277 : List ℕ := 1787::ps276
private theorem c277 : F ps276 5834123=409032 := by decide +kernel
private theorem v277 : F ps277 10425579253=783060709 :=
  takeStep (p:=1787) (by decide) v276 c277 rfl (by decide) (by decide) rfl

private def ps278 : List ℕ := 1789::ps277
private theorem c278 : F ps277 5827601=408399 := by decide +kernel
private theorem v278 : F ps278 10425579253=782652310 :=
  takeStep (p:=1789) (by decide) v277 c278 rfl (by decide) (by decide) rfl

private def ps279 : List ℕ := 1801::ps278
private theorem c279 : F ps278 5788772=405555 := by decide +kernel
private theorem v279 : F ps279 10425579253=782246755 :=
  takeStep (p:=1801) (by decide) v278 c279 rfl (by decide) (by decide) rfl

private def ps280 : List ℕ := 1811::ps279
private theorem c280 : F ps279 5756807=403221 := by decide +kernel
private theorem v280 : F ps280 10425579253=781843534 :=
  takeStep (p:=1811) (by decide) v279 c280 rfl (by decide) (by decide) rfl

private def ps281 : List ℕ := 1823::ps280
private theorem c281 : F ps280 5718913=400458 := by decide +kernel
private theorem v281 : F ps281 10425579253=781443076 :=
  takeStep (p:=1823) (by decide) v280 c281 rfl (by decide) (by decide) rfl

private def ps282 : List ℕ := 1831::ps281
private theorem c282 : F ps281 5693926=398546 := by decide +kernel
private theorem v282 : F ps282 10425579253=781044530 :=
  takeStep (p:=1831) (by decide) v281 c282 rfl (by decide) (by decide) rfl

private def ps283 : List ℕ := 1847::ps282
private theorem c283 : F ps282 5644601=395009 := by decide +kernel
private theorem v283 : F ps283 10425579253=780649521 :=
  takeStep (p:=1847) (by decide) v282 c283 rfl (by decide) (by decide) rfl

private def ps284 : List ℕ := 1861::ps283
private theorem c284 : F ps283 5602138=391963 := by decide +kernel
private theorem v284 : F ps284 10425579253=780257558 :=
  takeStep (p:=1861) (by decide) v283 c284 rfl (by decide) (by decide) rfl

private def ps285 : List ℕ := 1867::ps284
private theorem c285 : F ps284 5584134=390593 := by decide +kernel
private theorem v285 : F ps285 10425579253=779866965 :=
  takeStep (p:=1867) (by decide) v284 c285 rfl (by decide) (by decide) rfl

private def ps286 : List ℕ := 1871::ps285
private theorem c286 : F ps285 5572196=389648 := by decide +kernel
private theorem v286 : F ps286 10425579253=779477317 :=
  takeStep (p:=1871) (by decide) v285 c286 rfl (by decide) (by decide) rfl

private def ps287 : List ℕ := 1873::ps286
private theorem c287 : F ps286 5566246=389071 := by decide +kernel
private theorem v287 : F ps287 10425579253=779088246 :=
  takeStep (p:=1873) (by decide) v286 c287 rfl (by decide) (by decide) rfl

private def ps288 : List ℕ := 1877::ps287
private theorem c288 : F ps287 5554384=388127 := by decide +kernel
private theorem v288 : F ps288 10425579253=778700119 :=
  takeStep (p:=1877) (by decide) v287 c288 rfl (by decide) (by decide) rfl

private def ps289 : List ℕ := 1879::ps288
private theorem c289 : F ps288 5548472=387584 := by decide +kernel
private theorem v289 : F ps289 10425579253=778312535 :=
  takeStep (p:=1879) (by decide) v288 c289 rfl (by decide) (by decide) rfl

private def ps290 : List ℕ := 1889::ps289
private theorem c290 : F ps289 5519099=385470 := by decide +kernel
private theorem v290 : F ps290 10425579253=777927065 :=
  takeStep (p:=1889) (by decide) v289 c290 rfl (by decide) (by decide) rfl

private def ps291 : List ℕ := 1901::ps290
private theorem c291 : F ps290 5484260=382994 := by decide +kernel
private theorem v291 : F ps291 10425579253=777544071 :=
  takeStep (p:=1901) (by decide) v290 c291 rfl (by decide) (by decide) rfl

private def ps292 : List ℕ := 1907::ps291
private theorem c292 : F ps291 5467005=381712 := by decide +kernel
private theorem v292 : F ps292 10425579253=777162359 :=
  takeStep (p:=1907) (by decide) v291 c292 rfl (by decide) (by decide) rfl

private def ps293 : List ℕ := 1913::ps292
private theorem c293 : F ps292 5449858=380400 := by decide +kernel
private theorem v293 : F ps293 10425579253=776781959 :=
  takeStep (p:=1913) (by decide) v292 c293 rfl (by decide) (by decide) rfl

private def ps294 : List ℕ := 1931::ps293
private theorem c294 : F ps293 5399057=376839 := by decide +kernel
private theorem v294 : F ps294 10425579253=776405120 :=
  takeStep (p:=1931) (by decide) v293 c294 rfl (by decide) (by decide) rfl

private def ps295 : List ℕ := 1933::ps294
private theorem c295 : F ps294 5393470=376352 := by decide +kernel
private theorem v295 : F ps295 10425579253=776028768 :=
  takeStep (p:=1933) (by decide) v294 c295 rfl (by decide) (by decide) rfl

private def ps296 : List ℕ := 1949::ps295
private theorem c296 : F ps295 5349194=373241 := by decide +kernel
private theorem v296 : F ps296 10425579253=775655527 :=
  takeStep (p:=1949) (by decide) v295 c296 rfl (by decide) (by decide) rfl

private def ps297 : List ℕ := 1951::ps296
private theorem c297 : F ps296 5343710=372774 := by decide +kernel
private theorem v297 : F ps297 10425579253=775282753 :=
  takeStep (p:=1951) (by decide) v296 c297 rfl (by decide) (by decide) rfl

private def ps298 : List ℕ := 1973::ps297
private theorem c298 : F ps297 5284125=368636 := by decide +kernel
private theorem v298 : F ps298 10425579253=774914117 :=
  takeStep (p:=1973) (by decide) v297 c298 rfl (by decide) (by decide) rfl

private def ps299 : List ℕ := 1979::ps298
private theorem c299 : F ps298 5268104=367488 := by decide +kernel
private theorem v299 : F ps299 10425579253=774546629 :=
  takeStep (p:=1979) (by decide) v298 c299 rfl (by decide) (by decide) rfl

private def ps300 : List ℕ := 1987::ps299
private theorem c300 : F ps299 5246894=365967 := by decide +kernel
private theorem v300 : F ps300 10425579253=774180662 :=
  takeStep (p:=1987) (by decide) v299 c300 rfl (by decide) (by decide) rfl

private def ps301 : List ℕ := 1993::ps300
private theorem c301 : F ps300 5231098=364820 := by decide +kernel
private theorem v301 : F ps301 10425579253=773815842 :=
  takeStep (p:=1993) (by decide) v300 c301 rfl (by decide) (by decide) rfl

private def ps302 : List ℕ := 1997::ps301
private theorem c302 : F ps301 5220620=364037 := by decide +kernel
private theorem v302 : F ps302 10425579253=773451805 :=
  takeStep (p:=1997) (by decide) v301 c302 rfl (by decide) (by decide) rfl

private def ps303 : List ℕ := 1999::ps302
private theorem c303 : F ps302 5215397=363609 := by decide +kernel
private theorem v303 : F ps303 10425579253=773088196 :=
  takeStep (p:=1999) (by decide) v302 c303 rfl (by decide) (by decide) rfl

private def ps304 : List ℕ := 2003::ps303
private theorem c304 : F ps303 5204982=362835 := by decide +kernel
private theorem v304 : F ps304 10425579253=772725361 :=
  takeStep (p:=2003) (by decide) v303 c304 rfl (by decide) (by decide) rfl

private def ps305 : List ℕ := 2011::ps304
private theorem c305 : F ps304 5184276=361369 := by decide +kernel
private theorem v305 : F ps305 10425579253=772363992 :=
  takeStep (p:=2011) (by decide) v304 c305 rfl (by decide) (by decide) rfl

private def ps306 : List ℕ := 2017::ps305
private theorem c306 : F ps305 5168854=360281 := by decide +kernel
private theorem v306 : F ps306 10425579253=772003711 :=
  takeStep (p:=2017) (by decide) v305 c306 rfl (by decide) (by decide) rfl

private def ps307 : List ℕ := 2027::ps306
private theorem c307 : F ps306 5143354=358528 := by decide +kernel
private theorem v307 : F ps307 10425579253=771645183 :=
  takeStep (p:=2027) (by decide) v306 c307 rfl (by decide) (by decide) rfl

private def ps308 : List ℕ := 2029::ps307
private theorem c308 : F ps307 5138284=358121 := by decide +kernel
private theorem v308 : F ps308 10425579253=771287062 :=
  takeStep (p:=2029) (by decide) v307 c308 rfl (by decide) (by decide) rfl

private def ps309 : List ℕ := 2039::ps308
private theorem c309 : F ps308 5113084=356375 := by decide +kernel
private theorem v309 : F ps309 10425579253=770930687 :=
  takeStep (p:=2039) (by decide) v308 c309 rfl (by decide) (by decide) rfl

private def ps310 : List ℕ := 2053::ps309
private theorem c310 : F ps309 5078216=354000 := by decide +kernel
private theorem v310 : F ps310 10425579253=770576687 :=
  takeStep (p:=2053) (by decide) v309 c310 rfl (by decide) (by decide) rfl

private def ps311 : List ℕ := 2063::ps310
private theorem c311 : F ps310 5053601=352316 := by decide +kernel
private theorem v311 : F ps311 10425579253=770224371 :=
  takeStep (p:=2063) (by decide) v310 c311 rfl (by decide) (by decide) rfl

private def ps312 : List ℕ := 2069::ps311
private theorem c312 : F ps311 5038945=351296 := by decide +kernel
private theorem v312 : F ps312 10425579253=769873075 :=
  takeStep (p:=2069) (by decide) v311 c312 rfl (by decide) (by decide) rfl

private def ps313 : List ℕ := 2081::ps312
private theorem c313 : F ps312 5009889=349325 := by decide +kernel
private theorem v313 : F ps313 10425579253=769523750 :=
  takeStep (p:=2081) (by decide) v312 c313 rfl (by decide) (by decide) rfl

private def ps314 : List ℕ := 2083::ps313
private theorem c314 : F ps313 5005078=348963 := by decide +kernel
private theorem v314 : F ps314 10425579253=769174787 :=
  takeStep (p:=2083) (by decide) v313 c314 rfl (by decide) (by decide) rfl

private def ps315 : List ℕ := 2087::ps314
private theorem c315 : F ps314 4995485=348298 := by decide +kernel
private theorem v315 : F ps315 10425579253=768826489 :=
  takeStep (p:=2087) (by decide) v314 c315 rfl (by decide) (by decide) rfl

private def ps316 : List ℕ := 2089::ps315
private theorem c316 : F ps315 4990703=347949 := by decide +kernel
private theorem v316 : F ps316 10425579253=768478540 :=
  takeStep (p:=2089) (by decide) v315 c316 rfl (by decide) (by decide) rfl

private def ps317 : List ℕ := 2099::ps316
private theorem c317 : F ps316 4966926=346317 := by decide +kernel
private theorem v317 : F ps317 10425579253=768132223 :=
  takeStep (p:=2099) (by decide) v316 c317 rfl (by decide) (by decide) rfl

private def ps318 : List ℕ := 2111::ps317
private theorem c318 : F ps317 4938692=344407 := by decide +kernel
private theorem v318 : F ps318 10425579253=767787816 :=
  takeStep (p:=2111) (by decide) v317 c318 rfl (by decide) (by decide) rfl

private def ps319 : List ℕ := 2113::ps318
private theorem c319 : F ps318 4934017=344061 := by decide +kernel
private theorem v319 : F ps319 10425579253=767443755 :=
  takeStep (p:=2113) (by decide) v318 c319 rfl (by decide) (by decide) rfl

private def ps320 : List ℕ := 2129::ps319
private theorem c320 : F ps319 4896937=341605 := by decide +kernel
private theorem v320 : F ps320 10425579253=767102150 :=
  takeStep (p:=2129) (by decide) v319 c320 rfl (by decide) (by decide) rfl

private def ps321 : List ℕ := 2131::ps320
private theorem c321 : F ps320 4892341=341266 := by decide +kernel
private theorem v321 : F ps321 10425579253=766760884 :=
  takeStep (p:=2131) (by decide) v320 c321 rfl (by decide) (by decide) rfl

private def ps322 : List ℕ := 2137::ps321
private theorem c322 : F ps321 4878605=340313 := by decide +kernel
private theorem v322 : F ps322 10425579253=766420571 :=
  takeStep (p:=2137) (by decide) v321 c322 rfl (by decide) (by decide) rfl

private def ps323 : List ℕ := 2141::ps322
private theorem c323 : F ps322 4869490=339708 := by decide +kernel
private theorem v323 : F ps323 10425579253=766080863 :=
  takeStep (p:=2141) (by decide) v322 c323 rfl (by decide) (by decide) rfl

private def ps324 : List ℕ := 2143::ps323
private theorem c324 : F ps323 4864945=339387 := by decide +kernel
private theorem v324 : F ps324 10425579253=765741476 :=
  takeStep (p:=2143) (by decide) v323 c324 rfl (by decide) (by decide) rfl

private def ps325 : List ℕ := 2153::ps324
private theorem c325 : F ps324 4842349=337906 := by decide +kernel
private theorem v325 : F ps325 10425579253=765403570 :=
  takeStep (p:=2153) (by decide) v324 c325 rfl (by decide) (by decide) rfl

private def ps326 : List ℕ := 2161::ps325
private theorem c326 : F ps325 4824423=336727 := by decide +kernel
private theorem v326 : F ps326 10425579253=765066843 :=
  takeStep (p:=2161) (by decide) v325 c326 rfl (by decide) (by decide) rfl

private def ps327 : List ℕ := 2179::ps326
private theorem c327 : F ps326 4784570=334120 := by decide +kernel
private theorem v327 : F ps327 10425579253=764732723 :=
  takeStep (p:=2179) (by decide) v326 c327 rfl (by decide) (by decide) rfl

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

private def l0_68 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67]
private theorem l0_68ok : (List.range' 0 68).filter prime = l0_68 :=
  by decide +kernel

private def l68_136 : List ℕ := [71,73,79,83,89,97,101,103,107,109,113,127,131]
private theorem l68_136ok : (List.range' 68 68).filter prime = l68_136 :=
  by decide +kernel

private def l0_136 : List ℕ := l0_68 ++ l68_136
private theorem l0_136ok : (List.range' 0 136).filter prime = l0_136 :=
  merge_filter _ 0 68 68 _ _ l0_68ok l68_136ok

private def l136_204 : List ℕ := [137,139,149,151,157,163,167,173,179,181,191,193,197,199]
private theorem l136_204ok : (List.range' 136 68).filter prime = l136_204 :=
  by decide +kernel

private def l204_273 : List ℕ := [211,223,227,229,233,239,241,251,257,263,269,271]
private theorem l204_273ok : (List.range' 204 69).filter prime = l204_273 :=
  by decide +kernel

private def l136_273 : List ℕ := l136_204 ++ l204_273
private theorem l136_273ok : (List.range' 136 137).filter prime = l136_273 :=
  merge_filter _ 136 68 69 _ _ l136_204ok l204_273ok

private def l0_273 : List ℕ := l0_136 ++ l136_273
private theorem l0_273ok : (List.range' 0 273).filter prime = l0_273 :=
  merge_filter _ 0 136 137 _ _ l0_136ok l136_273ok

private def l273_341 : List ℕ := [277,281,283,293,307,311,313,317,331,337]
private theorem l273_341ok : (List.range' 273 68).filter prime = l273_341 :=
  by decide +kernel

private def l341_409 : List ℕ := [347,349,353,359,367,373,379,383,389,397,401]
private theorem l341_409ok : (List.range' 341 68).filter prime = l341_409 :=
  by decide +kernel

private def l273_409 : List ℕ := l273_341 ++ l341_409
private theorem l273_409ok : (List.range' 273 136).filter prime = l273_409 :=
  merge_filter _ 273 68 68 _ _ l273_341ok l341_409ok

private def l409_477 : List ℕ := [409,419,421,431,433,439,443,449,457,461,463,467]
private theorem l409_477ok : (List.range' 409 68).filter prime = l409_477 :=
  by decide +kernel

private def l477_546 : List ℕ := [479,487,491,499,503,509,521,523,541]
private theorem l477_546ok : (List.range' 477 69).filter prime = l477_546 :=
  by decide +kernel

private def l409_546 : List ℕ := l409_477 ++ l477_546
private theorem l409_546ok : (List.range' 409 137).filter prime = l409_546 :=
  merge_filter _ 409 68 69 _ _ l409_477ok l477_546ok

private def l273_546 : List ℕ := l273_409 ++ l409_546
private theorem l273_546ok : (List.range' 273 273).filter prime = l273_546 :=
  merge_filter _ 273 136 137 _ _ l273_409ok l409_546ok

private def l0_546 : List ℕ := l0_273 ++ l273_546
private theorem l0_546ok : (List.range' 0 546).filter prime = l0_546 :=
  merge_filter _ 0 273 273 _ _ l0_273ok l273_546ok

private def l546_614 : List ℕ := [547,557,563,569,571,577,587,593,599,601,607,613]
private theorem l546_614ok : (List.range' 546 68).filter prime = l546_614 :=
  by decide +kernel

private def l614_682 : List ℕ := [617,619,631,641,643,647,653,659,661,673,677]
private theorem l614_682ok : (List.range' 614 68).filter prime = l614_682 :=
  by decide +kernel

private def l546_682 : List ℕ := l546_614 ++ l614_682
private theorem l546_682ok : (List.range' 546 136).filter prime = l546_682 :=
  merge_filter _ 546 68 68 _ _ l546_614ok l614_682ok

private def l682_750 : List ℕ := [683,691,701,709,719,727,733,739,743]
private theorem l682_750ok : (List.range' 682 68).filter prime = l682_750 :=
  by decide +kernel

private def l750_819 : List ℕ := [751,757,761,769,773,787,797,809,811]
private theorem l750_819ok : (List.range' 750 69).filter prime = l750_819 :=
  by decide +kernel

private def l682_819 : List ℕ := l682_750 ++ l750_819
private theorem l682_819ok : (List.range' 682 137).filter prime = l682_819 :=
  merge_filter _ 682 68 69 _ _ l682_750ok l750_819ok

private def l546_819 : List ℕ := l546_682 ++ l682_819
private theorem l546_819ok : (List.range' 546 273).filter prime = l546_819 :=
  merge_filter _ 546 136 137 _ _ l546_682ok l682_819ok

private def l819_887 : List ℕ := [821,823,827,829,839,853,857,859,863,877,881,883]
private theorem l819_887ok : (List.range' 819 68).filter prime = l819_887 :=
  by decide +kernel

private def l887_955 : List ℕ := [887,907,911,919,929,937,941,947,953]
private theorem l887_955ok : (List.range' 887 68).filter prime = l887_955 :=
  by decide +kernel

private def l819_955 : List ℕ := l819_887 ++ l887_955
private theorem l819_955ok : (List.range' 819 136).filter prime = l819_955 :=
  merge_filter _ 819 68 68 _ _ l819_887ok l887_955ok

private def l955_1023 : List ℕ := [967,971,977,983,991,997,1009,1013,1019,1021]
private theorem l955_1023ok : (List.range' 955 68).filter prime = l955_1023 :=
  by decide +kernel

private def l1023_1092 : List ℕ := [1031,1033,1039,1049,1051,1061,1063,1069,1087,1091]
private theorem l1023_1092ok : (List.range' 1023 69).filter prime = l1023_1092 :=
  by decide +kernel

private def l955_1092 : List ℕ := l955_1023 ++ l1023_1092
private theorem l955_1092ok : (List.range' 955 137).filter prime = l955_1092 :=
  merge_filter _ 955 68 69 _ _ l955_1023ok l1023_1092ok

private def l819_1092 : List ℕ := l819_955 ++ l955_1092
private theorem l819_1092ok : (List.range' 819 273).filter prime = l819_1092 :=
  merge_filter _ 819 136 137 _ _ l819_955ok l955_1092ok

private def l546_1092 : List ℕ := l546_819 ++ l819_1092
private theorem l546_1092ok : (List.range' 546 546).filter prime = l546_1092 :=
  merge_filter _ 546 273 273 _ _ l546_819ok l819_1092ok

private def l0_1092 : List ℕ := l0_546 ++ l546_1092
private theorem l0_1092ok : (List.range' 0 1092).filter prime = l0_1092 :=
  merge_filter _ 0 546 546 _ _ l0_546ok l546_1092ok

private def l1092_1160 : List ℕ := [1093,1097,1103,1109,1117,1123,1129,1151,1153]
private theorem l1092_1160ok : (List.range' 1092 68).filter prime = l1092_1160 :=
  by decide +kernel

private def l1160_1228 : List ℕ := [1163,1171,1181,1187,1193,1201,1213,1217,1223]
private theorem l1160_1228ok : (List.range' 1160 68).filter prime = l1160_1228 :=
  by decide +kernel

private def l1092_1228 : List ℕ := l1092_1160 ++ l1160_1228
private theorem l1092_1228ok : (List.range' 1092 136).filter prime = l1092_1228 :=
  merge_filter _ 1092 68 68 _ _ l1092_1160ok l1160_1228ok

private def l1228_1296 : List ℕ := [1229,1231,1237,1249,1259,1277,1279,1283,1289,1291]
private theorem l1228_1296ok : (List.range' 1228 68).filter prime = l1228_1296 :=
  by decide +kernel

private def l1296_1365 : List ℕ := [1297,1301,1303,1307,1319,1321,1327,1361]
private theorem l1296_1365ok : (List.range' 1296 69).filter prime = l1296_1365 :=
  by decide +kernel

private def l1228_1365 : List ℕ := l1228_1296 ++ l1296_1365
private theorem l1228_1365ok : (List.range' 1228 137).filter prime = l1228_1365 :=
  merge_filter _ 1228 68 69 _ _ l1228_1296ok l1296_1365ok

private def l1092_1365 : List ℕ := l1092_1228 ++ l1228_1365
private theorem l1092_1365ok : (List.range' 1092 273).filter prime = l1092_1365 :=
  merge_filter _ 1092 136 137 _ _ l1092_1228ok l1228_1365ok

private def l1365_1433 : List ℕ := [1367,1373,1381,1399,1409,1423,1427,1429]
private theorem l1365_1433ok : (List.range' 1365 68).filter prime = l1365_1433 :=
  by decide +kernel

private def l1433_1501 : List ℕ := [1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499]
private theorem l1433_1501ok : (List.range' 1433 68).filter prime = l1433_1501 :=
  by decide +kernel

private def l1365_1501 : List ℕ := l1365_1433 ++ l1433_1501
private theorem l1365_1501ok : (List.range' 1365 136).filter prime = l1365_1501 :=
  merge_filter _ 1365 68 68 _ _ l1365_1433ok l1433_1501ok

private def l1501_1569 : List ℕ := [1511,1523,1531,1543,1549,1553,1559,1567]
private theorem l1501_1569ok : (List.range' 1501 68).filter prime = l1501_1569 :=
  by decide +kernel

private def l1569_1638 : List ℕ := [1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637]
private theorem l1569_1638ok : (List.range' 1569 69).filter prime = l1569_1638 :=
  by decide +kernel

private def l1501_1638 : List ℕ := l1501_1569 ++ l1569_1638
private theorem l1501_1638ok : (List.range' 1501 137).filter prime = l1501_1638 :=
  merge_filter _ 1501 68 69 _ _ l1501_1569ok l1569_1638ok

private def l1365_1638 : List ℕ := l1365_1501 ++ l1501_1638
private theorem l1365_1638ok : (List.range' 1365 273).filter prime = l1365_1638 :=
  merge_filter _ 1365 136 137 _ _ l1365_1501ok l1501_1638ok

private def l1092_1638 : List ℕ := l1092_1365 ++ l1365_1638
private theorem l1092_1638ok : (List.range' 1092 546).filter prime = l1092_1638 :=
  merge_filter _ 1092 273 273 _ _ l1092_1365ok l1365_1638ok

private def l1638_1706 : List ℕ := [1657,1663,1667,1669,1693,1697,1699]
private theorem l1638_1706ok : (List.range' 1638 68).filter prime = l1638_1706 :=
  by decide +kernel

private def l1706_1774 : List ℕ := [1709,1721,1723,1733,1741,1747,1753,1759]
private theorem l1706_1774ok : (List.range' 1706 68).filter prime = l1706_1774 :=
  by decide +kernel

private def l1638_1774 : List ℕ := l1638_1706 ++ l1706_1774
private theorem l1638_1774ok : (List.range' 1638 136).filter prime = l1638_1774 :=
  merge_filter _ 1638 68 68 _ _ l1638_1706ok l1706_1774ok

private def l1774_1842 : List ℕ := [1777,1783,1787,1789,1801,1811,1823,1831]
private theorem l1774_1842ok : (List.range' 1774 68).filter prime = l1774_1842 :=
  by decide +kernel

private def l1842_1911 : List ℕ := [1847,1861,1867,1871,1873,1877,1879,1889,1901,1907]
private theorem l1842_1911ok : (List.range' 1842 69).filter prime = l1842_1911 :=
  by decide +kernel

private def l1774_1911 : List ℕ := l1774_1842 ++ l1842_1911
private theorem l1774_1911ok : (List.range' 1774 137).filter prime = l1774_1911 :=
  merge_filter _ 1774 68 69 _ _ l1774_1842ok l1842_1911ok

private def l1638_1911 : List ℕ := l1638_1774 ++ l1774_1911
private theorem l1638_1911ok : (List.range' 1638 273).filter prime = l1638_1911 :=
  merge_filter _ 1638 136 137 _ _ l1638_1774ok l1774_1911ok

private def l1911_1979 : List ℕ := [1913,1931,1933,1949,1951,1973]
private theorem l1911_1979ok : (List.range' 1911 68).filter prime = l1911_1979 :=
  by decide +kernel

private def l1979_2048 : List ℕ := [1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039]
private theorem l1979_2048ok : (List.range' 1979 69).filter prime = l1979_2048 :=
  by decide +kernel

private def l1911_2048 : List ℕ := l1911_1979 ++ l1979_2048
private theorem l1911_2048ok : (List.range' 1911 137).filter prime = l1911_2048 :=
  merge_filter _ 1911 68 69 _ _ l1911_1979ok l1979_2048ok

private def l2048_2116 : List ℕ := [2053,2063,2069,2081,2083,2087,2089,2099,2111,2113]
private theorem l2048_2116ok : (List.range' 2048 68).filter prime = l2048_2116 :=
  by decide +kernel

private def l2116_2185 : List ℕ := [2129,2131,2137,2141,2143,2153,2161,2179]
private theorem l2116_2185ok : (List.range' 2116 69).filter prime = l2116_2185 :=
  by decide +kernel

private def l2048_2185 : List ℕ := l2048_2116 ++ l2116_2185
private theorem l2048_2185ok : (List.range' 2048 137).filter prime = l2048_2185 :=
  merge_filter _ 2048 68 69 _ _ l2048_2116ok l2116_2185ok

private def l1911_2185 : List ℕ := l1911_2048 ++ l2048_2185
private theorem l1911_2185ok : (List.range' 1911 274).filter prime = l1911_2185 :=
  merge_filter _ 1911 137 137 _ _ l1911_2048ok l2048_2185ok

private def l1638_2185 : List ℕ := l1638_1911 ++ l1911_2185
private theorem l1638_2185ok : (List.range' 1638 547).filter prime = l1638_2185 :=
  merge_filter _ 1638 273 274 _ _ l1638_1911ok l1911_2185ok

private def l1092_2185 : List ℕ := l1092_1638 ++ l1638_2185
private theorem l1092_2185ok : (List.range' 1092 1093).filter prime = l1092_2185 :=
  merge_filter _ 1092 546 547 _ _ l1092_1638ok l1638_2185ok

private def l0_2185 : List ℕ := l0_1092 ++ l1092_2185
private theorem l0_2185ok : (List.range' 0 2185).filter prime = l0_2185 :=
  merge_filter _ 0 1092 1093 _ _ l0_1092ok l1092_2185ok

set_option maxRecDepth 8000 in
private theorem last_row :
    ((List.range (2184+1)).filter (fun p => decide p.Prime)).reverse = ps327 := by
  rw [filter_from_test prime prime_ok 2184 (by decide),List.range_eq_range',l0_2185ok]
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
    (((List.range (2184+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id 10425579253) +
    (Nat.primesLE 2184).card = 764733050 := by
  exact left_from_rows tab HybridBound10425.fast_correct ps327 (by decide) (by decide) last_row (show evalPhi tab ps327 10425579253 = 764732723 from v327) (by decide +kernel)

private abbrev term := contribution 10425579253 2184 tab prime

private theorem s0 : blockSum term 0 398 0 := by unfold blockSum; decide +kernel

private theorem s398 : blockSum term 398 399 0 := by unfold blockSum; decide +kernel

private theorem s797 : blockSum term 797 399 0 := by unfold blockSum; decide +kernel

private theorem s1196 : blockSum term 1196 399 0 := by unfold blockSum; decide +kernel

private theorem s1595 : blockSum term 1595 398 0 := by unfold blockSum; decide +kernel

private theorem s1993 : blockSum term 1993 399 8905026 := by unfold blockSum; decide +kernel

private theorem s2392 : blockSum term 2392 399 14188690 := by unfold blockSum; decide +kernel

private theorem s2791 : blockSum term 2791 399 11499782 := by unfold blockSum; decide +kernel

private theorem s3190 : blockSum term 3190 398 11289154 := by unfold blockSum; decide +kernel

private theorem s3588 : blockSum term 3588 399 9408952 := by unfold blockSum; decide +kernel

private theorem s3987 : blockSum term 3987 399 8757715 := by unfold blockSum; decide +kernel

private theorem s4386 : blockSum term 4386 399 7532889 := by unfold blockSum; decide +kernel

private theorem s4785 : blockSum term 4785 399 7430246 := by unfold blockSum; decide +kernel

private theorem s5184 : blockSum term 5184 399 6747768 := by unfold blockSum; decide +kernel

private theorem s5583 : blockSum term 5583 399 6056615 := by unfold blockSum; decide +kernel

private theorem s5982 : blockSum term 5982 399 6304956 := by unfold blockSum; decide +kernel

private theorem s6381 : blockSum term 6381 398 4644022 := by unfold blockSum; decide +kernel

private theorem s6779 : blockSum term 6779 399 5204449 := by unfold blockSum; decide +kernel

private theorem s7178 : blockSum term 7178 399 4706561 := by unfold blockSum; decide +kernel

private theorem s7577 : blockSum term 7577 399 4591396 := by unfold blockSum; decide +kernel

private theorem s7976 : blockSum term 7976 399 4081302 := by unfold blockSum; decide +kernel

private theorem s8375 : blockSum term 8375 399 4179019 := by unfold blockSum; decide +kernel

private theorem s8774 : blockSum term 8774 399 3832425 := by unfold blockSum; decide +kernel

private theorem s9173 : blockSum term 9173 399 4019049 := by unfold blockSum; decide +kernel

private theorem s9572 : blockSum term 9572 398 3694893 := by unfold blockSum; decide +kernel

private theorem s9970 : blockSum term 9970 399 3396937 := by unfold blockSum; decide +kernel

private theorem s10369 : blockSum term 10369 399 3048538 := by unfold blockSum; decide +kernel

private theorem s10768 : blockSum term 10768 399 3017719 := by unfold blockSum; decide +kernel

private theorem s11167 : blockSum term 11167 399 2847447 := by unfold blockSum; decide +kernel

private theorem s11566 : blockSum term 11566 399 2888436 := by unfold blockSum; decide +kernel

private theorem s11965 : blockSum term 11965 399 2735380 := by unfold blockSum; decide +kernel

private theorem s12364 : blockSum term 12364 399 3040951 := by unfold blockSum; decide +kernel

private theorem s12763 : blockSum term 12763 398 2696883 := by unfold blockSum; decide +kernel

private theorem s13161 : blockSum term 13161 399 2376919 := by unfold blockSum; decide +kernel

private theorem s13560 : blockSum term 13560 399 2604614 := by unfold blockSum; decide +kernel

private theorem s13959 : blockSum term 13959 399 2016230 := by unfold blockSum; decide +kernel

private theorem s14358 : blockSum term 14358 398 2521513 := by unfold blockSum; decide +kernel

private theorem s14756 : blockSum term 14756 399 2293512 := by unfold blockSum; decide +kernel

private theorem s15155 : blockSum term 15155 399 2341467 := by unfold blockSum; decide +kernel

private theorem s15554 : blockSum term 15554 399 2282995 := by unfold blockSum; decide +kernel

private theorem s15953 : blockSum term 15953 398 1923762 := by unfold blockSum; decide +kernel

private theorem s16351 : blockSum term 16351 399 1976837 := by unfold blockSum; decide +kernel

private theorem s16750 : blockSum term 16750 399 1882378 := by unfold blockSum; decide +kernel

private theorem s17149 : blockSum term 17149 399 1980818 := by unfold blockSum; decide +kernel

private theorem s17548 : blockSum term 17548 399 1844505 := by unfold blockSum; decide +kernel

private theorem s17947 : blockSum term 17947 399 2028891 := by unfold blockSum; decide +kernel

private theorem s18346 : blockSum term 18346 399 1633188 := by unfold blockSum; decide +kernel

private theorem s18745 : blockSum term 18745 399 1424907 := by unfold blockSum; decide +kernel

private theorem s19144 : blockSum term 19144 398 1860100 := by unfold blockSum; decide +kernel

private theorem s19542 : blockSum term 19542 399 1574784 := by unfold blockSum; decide +kernel

private theorem s19941 : blockSum term 19941 399 1706586 := by unfold blockSum; decide +kernel

private theorem s20340 : blockSum term 20340 399 1513554 := by unfold blockSum; decide +kernel

private theorem s20739 : blockSum term 20739 399 1561762 := by unfold blockSum; decide +kernel

private theorem s21138 : blockSum term 21138 399 1645403 := by unfold blockSum; decide +kernel

private theorem s21537 : blockSum term 21537 399 1539998 := by unfold blockSum; decide +kernel

private theorem s21936 : blockSum term 21936 399 1547404 := by unfold blockSum; decide +kernel

private theorem s22335 : blockSum term 22335 398 1444875 := by unfold blockSum; decide +kernel

private theorem s22733 : blockSum term 22733 399 1490420 := by unfold blockSum; decide +kernel

private theorem s23132 : blockSum term 23132 399 1117061 := by unfold blockSum; decide +kernel

private theorem s23531 : blockSum term 23531 399 1679006 := by unfold blockSum; decide +kernel

private theorem s23930 : blockSum term 23930 399 1279504 := by unfold blockSum; decide +kernel

private theorem s24329 : blockSum term 24329 399 1157720 := by unfold blockSum; decide +kernel

private theorem s24728 : blockSum term 24728 399 1202298 := by unfold blockSum; decide +kernel

private theorem s25127 : blockSum term 25127 399 1214466 := by unfold blockSum; decide +kernel

private theorem s25526 : blockSum term 25526 398 1256961 := by unfold blockSum; decide +kernel

private theorem s25924 : blockSum term 25924 399 1298198 := by unfold blockSum; decide +kernel

private theorem s26323 : blockSum term 26323 399 1185144 := by unfold blockSum; decide +kernel

private theorem s26722 : blockSum term 26722 399 1255806 := by unfold blockSum; decide +kernel

private theorem s27121 : blockSum term 27121 398 912004 := by unfold blockSum; decide +kernel

private theorem s27519 : blockSum term 27519 399 1187457 := by unfold blockSum; decide +kernel

private theorem s27918 : blockSum term 27918 399 1084012 := by unfold blockSum; decide +kernel

private theorem s28317 : blockSum term 28317 399 1234593 := by unfold blockSum; decide +kernel

private theorem s28716 : blockSum term 28716 398 968264 := by unfold blockSum; decide +kernel

private theorem s29114 : blockSum term 29114 399 1117407 := by unfold blockSum; decide +kernel

private theorem s29513 : blockSum term 29513 399 912218 := by unfold blockSum; decide +kernel

private theorem s29912 : blockSum term 29912 399 1003788 := by unfold blockSum; decide +kernel

private theorem s30311 : blockSum term 30311 399 962662 := by unfold blockSum; decide +kernel

private theorem s30710 : blockSum term 30710 399 948971 := by unfold blockSum; decide +kernel

private theorem s31109 : blockSum term 31109 399 986595 := by unfold blockSum; decide +kernel

private theorem s31508 : blockSum term 31508 399 922000 := by unfold blockSum; decide +kernel

private theorem s31907 : blockSum term 31907 398 932140 := by unfold blockSum; decide +kernel

private theorem s32305 : blockSum term 32305 399 1040522 := by unfold blockSum; decide +kernel

private theorem s32704 : blockSum term 32704 399 976455 := by unfold blockSum; decide +kernel

private theorem s33103 : blockSum term 33103 399 891879 := by unfold blockSum; decide +kernel

private theorem s33502 : blockSum term 33502 399 1018519 := by unfold blockSum; decide +kernel

private theorem s33901 : blockSum term 33901 399 775522 := by unfold blockSum; decide +kernel

private theorem s34300 : blockSum term 34300 399 944683 := by unfold blockSum; decide +kernel

private theorem s34699 : blockSum term 34699 399 776297 := by unfold blockSum; decide +kernel

private theorem s35098 : blockSum term 35098 398 809900 := by unfold blockSum; decide +kernel

private theorem s35496 : blockSum term 35496 399 734436 := by unfold blockSum; decide +kernel

private theorem s35895 : blockSum term 35895 399 830987 := by unfold blockSum; decide +kernel

private theorem s36294 : blockSum term 36294 399 819655 := by unfold blockSum; decide +kernel

private theorem s36693 : blockSum term 36693 399 871103 := by unfold blockSum; decide +kernel

private theorem s37092 : blockSum term 37092 399 715748 := by unfold blockSum; decide +kernel

private theorem s37491 : blockSum term 37491 399 807844 := by unfold blockSum; decide +kernel

private theorem s37890 : blockSum term 37890 399 676829 := by unfold blockSum; decide +kernel

private theorem s38289 : blockSum term 38289 398 668294 := by unfold blockSum; decide +kernel

private theorem s38687 : blockSum term 38687 399 737505 := by unfold blockSum; decide +kernel

private theorem s39086 : blockSum term 39086 399 784663 := by unfold blockSum; decide +kernel

private theorem s39485 : blockSum term 39485 399 754523 := by unfold blockSum; decide +kernel

private theorem s39884 : blockSum term 39884 399 652038 := by unfold blockSum; decide +kernel

private theorem s40283 : blockSum term 40283 399 570252 := by unfold blockSum; decide +kernel

private theorem s40682 : blockSum term 40682 399 708425 := by unfold blockSum; decide +kernel

private theorem s41081 : blockSum term 41081 399 699323 := by unfold blockSum; decide +kernel

private theorem s41480 : blockSum term 41480 398 672599 := by unfold blockSum; decide +kernel

private theorem s41878 : blockSum term 41878 399 733792 := by unfold blockSum; decide +kernel

private theorem s42277 : blockSum term 42277 399 706831 := by unfold blockSum; decide +kernel

private theorem s42676 : blockSum term 42676 399 731287 := by unfold blockSum; decide +kernel

private theorem s43075 : blockSum term 43075 399 486547 := by unfold blockSum; decide +kernel

private theorem s43474 : blockSum term 43474 399 580046 := by unfold blockSum; decide +kernel

private theorem s43873 : blockSum term 43873 399 687037 := by unfold blockSum; decide +kernel

private theorem s44272 : blockSum term 44272 399 565258 := by unfold blockSum; decide +kernel

private theorem s44671 : blockSum term 44671 398 574878 := by unfold blockSum; decide +kernel

private theorem s45069 : blockSum term 45069 399 551872 := by unfold blockSum; decide +kernel

private theorem s45468 : blockSum term 45468 399 575425 := by unfold blockSum; decide +kernel

private theorem s45867 : blockSum term 45867 399 506789 := by unfold blockSum; decide +kernel

private theorem s46266 : blockSum term 46266 399 576293 := by unfold blockSum; decide +kernel

private theorem s46665 : blockSum term 46665 399 509392 := by unfold blockSum; decide +kernel

private theorem s47064 : blockSum term 47064 399 547044 := by unfold blockSum; decide +kernel

private theorem s47463 : blockSum term 47463 399 583628 := by unfold blockSum; decide +kernel

private theorem s47862 : blockSum term 47862 398 489924 := by unfold blockSum; decide +kernel

private theorem s48260 : blockSum term 48260 399 526638 := by unfold blockSum; decide +kernel

private theorem s48659 : blockSum term 48659 399 548098 := by unfold blockSum; decide +kernel

private theorem s49058 : blockSum term 49058 399 527573 := by unfold blockSum; decide +kernel

private theorem s49457 : blockSum term 49457 399 534324 := by unfold blockSum; decide +kernel

private theorem s49856 : blockSum term 49856 399 500326 := by unfold blockSum; decide +kernel

private theorem s50255 : blockSum term 50255 399 493770 := by unfold blockSum; decide +kernel

private theorem s50654 : blockSum term 50654 399 421408 := by unfold blockSum; decide +kernel

private theorem s51053 : blockSum term 51053 398 507254 := by unfold blockSum; decide +kernel

private theorem s51451 : blockSum term 51451 399 501130 := by unfold blockSum; decide +kernel

private theorem s51850 : blockSum term 51850 399 456814 := by unfold blockSum; decide +kernel

private theorem s52249 : blockSum term 52249 399 438492 := by unfold blockSum; decide +kernel

private theorem s52648 : blockSum term 52648 398 432916 := by unfold blockSum; decide +kernel

private theorem s53046 : blockSum term 53046 399 488547 := by unfold blockSum; decide +kernel

private theorem s53445 : blockSum term 53445 399 409833 := by unfold blockSum; decide +kernel

private theorem s53844 : blockSum term 53844 399 405058 := by unfold blockSum; decide +kernel

private theorem s54243 : blockSum term 54243 398 505022 := by unfold blockSum; decide +kernel

private theorem s54641 : blockSum term 54641 399 371124 := by unfold blockSum; decide +kernel

private theorem s55040 : blockSum term 55040 399 389417 := by unfold blockSum; decide +kernel

private theorem s55439 : blockSum term 55439 399 463285 := by unfold blockSum; decide +kernel

private theorem s55838 : blockSum term 55838 399 390460 := by unfold blockSum; decide +kernel

private theorem s56237 : blockSum term 56237 399 439965 := by unfold blockSum; decide +kernel

private theorem s56636 : blockSum term 56636 399 423367 := by unfold blockSum; decide +kernel

private theorem s57035 : blockSum term 57035 399 439050 := by unfold blockSum; decide +kernel

private theorem s57434 : blockSum term 57434 398 380298 := by unfold blockSum; decide +kernel

private theorem s57832 : blockSum term 57832 399 406558 := by unfold blockSum; decide +kernel

private theorem s58231 : blockSum term 58231 399 349566 := by unfold blockSum; decide +kernel

private theorem s58630 : blockSum term 58630 399 355204 := by unfold blockSum; decide +kernel

private theorem s59029 : blockSum term 59029 399 410350 := by unfold blockSum; decide +kernel

private theorem s59428 : blockSum term 59428 399 375302 := by unfold blockSum; decide +kernel

private theorem s59827 : blockSum term 59827 399 321385 := by unfold blockSum; decide +kernel

private theorem s60226 : blockSum term 60226 399 298156 := by unfold blockSum; decide +kernel

private theorem s60625 : blockSum term 60625 398 351240 := by unfold blockSum; decide +kernel

private theorem s61023 : blockSum term 61023 399 299461 := by unfold blockSum; decide +kernel

private theorem s61422 : blockSum term 61422 399 350788 := by unfold blockSum; decide +kernel

private theorem s61821 : blockSum term 61821 399 346000 := by unfold blockSum; decide +kernel

private theorem s62220 : blockSum term 62220 399 278451 := by unfold blockSum; decide +kernel

private theorem s62619 : blockSum term 62619 399 301500 := by unfold blockSum; decide +kernel

private theorem s63018 : blockSum term 63018 399 306193 := by unfold blockSum; decide +kernel

private theorem s63417 : blockSum term 63417 399 388214 := by unfold blockSum; decide +kernel

private theorem s63816 : blockSum term 63816 398 255163 := by unfold blockSum; decide +kernel

private theorem s64214 : blockSum term 64214 399 260182 := by unfold blockSum; decide +kernel

private theorem s64613 : blockSum term 64613 399 281465 := by unfold blockSum; decide +kernel

private theorem s65012 : blockSum term 65012 399 301989 := by unfold blockSum; decide +kernel

private theorem s65411 : blockSum term 65411 398 321648 := by unfold blockSum; decide +kernel

private theorem s65809 : blockSum term 65809 399 285433 := by unfold blockSum; decide +kernel

private theorem s66208 : blockSum term 66208 399 257581 := by unfold blockSum; decide +kernel

private theorem s66607 : blockSum term 66607 399 269594 := by unfold blockSum; decide +kernel

private theorem s67006 : blockSum term 67006 398 273307 := by unfold blockSum; decide +kernel

private theorem s67404 : blockSum term 67404 399 314008 := by unfold blockSum; decide +kernel

private theorem s67803 : blockSum term 67803 399 243128 := by unfold blockSum; decide +kernel

private theorem s68202 : blockSum term 68202 399 239432 := by unfold blockSum; decide +kernel

private theorem s68601 : blockSum term 68601 399 242950 := by unfold blockSum; decide +kernel

private theorem s69000 : blockSum term 69000 399 239196 := by unfold blockSum; decide +kernel

private theorem s69399 : blockSum term 69399 399 207978 := by unfold blockSum; decide +kernel

private theorem s69798 : blockSum term 69798 399 258969 := by unfold blockSum; decide +kernel

private theorem s70197 : blockSum term 70197 398 254930 := by unfold blockSum; decide +kernel

private theorem s70595 : blockSum term 70595 399 244120 := by unfold blockSum; decide +kernel

private theorem s70994 : blockSum term 70994 399 253190 := by unfold blockSum; decide +kernel

private theorem s71393 : blockSum term 71393 399 223625 := by unfold blockSum; decide +kernel

private theorem s71792 : blockSum term 71792 399 251356 := by unfold blockSum; decide +kernel

private theorem s72191 : blockSum term 72191 399 204087 := by unfold blockSum; decide +kernel

private theorem s72590 : blockSum term 72590 399 237203 := by unfold blockSum; decide +kernel

private theorem s72989 : blockSum term 72989 399 191610 := by unfold blockSum; decide +kernel

private theorem s73388 : blockSum term 73388 398 211903 := by unfold blockSum; decide +kernel

private theorem s73786 : blockSum term 73786 399 190890 := by unfold blockSum; decide +kernel

private theorem s74185 : blockSum term 74185 399 216042 := by unfold blockSum; decide +kernel

private theorem s74584 : blockSum term 74584 399 206580 := by unfold blockSum; decide +kernel

private theorem s74983 : blockSum term 74983 399 186579 := by unfold blockSum; decide +kernel

private theorem s75382 : blockSum term 75382 399 204823 := by unfold blockSum; decide +kernel

private theorem s75781 : blockSum term 75781 399 180008 := by unfold blockSum; decide +kernel

private theorem s76180 : blockSum term 76180 399 171451 := by unfold blockSum; decide +kernel

private theorem s76579 : blockSum term 76579 398 173389 := by unfold blockSum; decide +kernel

private theorem s76977 : blockSum term 76977 399 179950 := by unfold blockSum; decide +kernel

private theorem s77376 : blockSum term 77376 399 210910 := by unfold blockSum; decide +kernel

private theorem s77775 : blockSum term 77775 399 153949 := by unfold blockSum; decide +kernel

private theorem s78174 : blockSum term 78174 398 155830 := by unfold blockSum; decide +kernel

private theorem s78572 : blockSum term 78572 399 152781 := by unfold blockSum; decide +kernel

private theorem s78971 : blockSum term 78971 399 158825 := by unfold blockSum; decide +kernel

private theorem s79370 : blockSum term 79370 399 146977 := by unfold blockSum; decide +kernel

private theorem s79769 : blockSum term 79769 398 161577 := by unfold blockSum; decide +kernel

private theorem s80167 : blockSum term 80167 399 149685 := by unfold blockSum; decide +kernel

private theorem s80566 : blockSum term 80566 399 171364 := by unfold blockSum; decide +kernel

private theorem s80965 : blockSum term 80965 399 155169 := by unfold blockSum; decide +kernel

private theorem s81364 : blockSum term 81364 399 139620 := by unfold blockSum; decide +kernel

private theorem s81763 : blockSum term 81763 399 136570 := by unfold blockSum; decide +kernel

private theorem s82162 : blockSum term 82162 399 145173 := by unfold blockSum; decide +kernel

private theorem s82561 : blockSum term 82561 399 123240 := by unfold blockSum; decide +kernel

private theorem s82960 : blockSum term 82960 398 123934 := by unfold blockSum; decide +kernel

private theorem s83358 : blockSum term 83358 399 121144 := by unfold blockSum; decide +kernel

private theorem s83757 : blockSum term 83757 399 111284 := by unfold blockSum; decide +kernel

private theorem s84156 : blockSum term 84156 399 135615 := by unfold blockSum; decide +kernel

private theorem s84555 : blockSum term 84555 399 95912 := by unfold blockSum; decide +kernel

private theorem s84954 : blockSum term 84954 399 116224 := by unfold blockSum; decide +kernel

private theorem s85353 : blockSum term 85353 399 116143 := by unfold blockSum; decide +kernel

private theorem s85752 : blockSum term 85752 399 91649 := by unfold blockSum; decide +kernel

private theorem s86151 : blockSum term 86151 398 121683 := by unfold blockSum; decide +kernel

private theorem s86549 : blockSum term 86549 399 83679 := by unfold blockSum; decide +kernel

private theorem s86948 : blockSum term 86948 399 100911 := by unfold blockSum; decide +kernel

private theorem s87347 : blockSum term 87347 399 111468 := by unfold blockSum; decide +kernel

private theorem s87746 : blockSum term 87746 399 81868 := by unfold blockSum; decide +kernel

private theorem s88145 : blockSum term 88145 399 66756 := by unfold blockSum; decide +kernel

private theorem s88544 : blockSum term 88544 399 89532 := by unfold blockSum; decide +kernel

private theorem s88943 : blockSum term 88943 399 86706 := by unfold blockSum; decide +kernel

private theorem s89342 : blockSum term 89342 398 86211 := by unfold blockSum; decide +kernel

private theorem s89740 : blockSum term 89740 399 92069 := by unfold blockSum; decide +kernel

private theorem s90139 : blockSum term 90139 399 79865 := by unfold blockSum; decide +kernel

private theorem s90538 : blockSum term 90538 399 64519 := by unfold blockSum; decide +kernel

private theorem s90937 : blockSum term 90937 399 70217 := by unfold blockSum; decide +kernel

private theorem s91336 : blockSum term 91336 399 61905 := by unfold blockSum; decide +kernel

private theorem s91735 : blockSum term 91735 399 61499 := by unfold blockSum; decide +kernel

private theorem s92134 : blockSum term 92134 399 71155 := by unfold blockSum; decide +kernel

private theorem s92533 : blockSum term 92533 398 69720 := by unfold blockSum; decide +kernel

private theorem s92931 : blockSum term 92931 399 61400 := by unfold blockSum; decide +kernel

private theorem s93330 : blockSum term 93330 399 46285 := by unfold blockSum; decide +kernel

private theorem s93729 : blockSum term 93729 399 52863 := by unfold blockSum; decide +kernel

private theorem s94128 : blockSum term 94128 399 44580 := by unfold blockSum; decide +kernel

private theorem s94527 : blockSum term 94527 399 49068 := by unfold blockSum; decide +kernel

private theorem s94926 : blockSum term 94926 399 48634 := by unfold blockSum; decide +kernel

private theorem s95325 : blockSum term 95325 399 42074 := by unfold blockSum; decide +kernel

private theorem s95724 : blockSum term 95724 398 37158 := by unfold blockSum; decide +kernel

private theorem s96122 : blockSum term 96122 399 36668 := by unfold blockSum; decide +kernel

private theorem s96521 : blockSum term 96521 399 31106 := by unfold blockSum; decide +kernel

private theorem s96920 : blockSum term 96920 399 27331 := by unfold blockSum; decide +kernel

private theorem s97319 : blockSum term 97319 399 27650 := by unfold blockSum; decide +kernel

private theorem s97718 : blockSum term 97718 399 23652 := by unfold blockSum; decide +kernel

private theorem s98117 : blockSum term 98117 399 22570 := by unfold blockSum; decide +kernel

private theorem s98516 : blockSum term 98516 399 21449 := by unfold blockSum; decide +kernel

private theorem s98915 : blockSum term 98915 398 18877 := by unfold blockSum; decide +kernel

private theorem s99313 : blockSum term 99313 399 15394 := by unfold blockSum; decide +kernel

private theorem s99712 : blockSum term 99712 399 13016 := by unfold blockSum; decide +kernel

private theorem s100111 : blockSum term 100111 399 10203 := by unfold blockSum; decide +kernel

private theorem s100510 : blockSum term 100510 399 7649 := by unfold blockSum; decide +kernel

private theorem s100909 : blockSum term 100909 399 6822 := by unfold blockSum; decide +kernel

private theorem s101308 : blockSum term 101308 399 4151 := by unfold blockSum; decide +kernel

private theorem s101707 : blockSum term 101707 399 1504 := by unfold blockSum; decide +kernel

private theorem rows : blockSum term 0 102106 291216679 := (join_sums term (lo:=0) (a:=51053) (b:=51053) (join_sums term (lo:=0) (a:=25526) (b:=25527) (join_sums term (lo:=0) (a:=12763) (b:=12763) (join_sums term (lo:=0) (a:=6381) (b:=6382) (join_sums term (lo:=0) (a:=3190) (b:=3191) (join_sums term (lo:=0) (a:=1595) (b:=1595) (join_sums term (lo:=0) (a:=797) (b:=798) (join_sums term (lo:=0) (a:=398) (b:=399) s0 s398) (join_sums term (lo:=797) (a:=399) (b:=399) s797 s1196)) (join_sums term (lo:=1595) (a:=797) (b:=798) (join_sums term (lo:=1595) (a:=398) (b:=399) s1595 s1993) (join_sums term (lo:=2392) (a:=399) (b:=399) s2392 s2791))) (join_sums term (lo:=3190) (a:=1595) (b:=1596) (join_sums term (lo:=3190) (a:=797) (b:=798) (join_sums term (lo:=3190) (a:=398) (b:=399) s3190 s3588) (join_sums term (lo:=3987) (a:=399) (b:=399) s3987 s4386)) (join_sums term (lo:=4785) (a:=798) (b:=798) (join_sums term (lo:=4785) (a:=399) (b:=399) s4785 s5184) (join_sums term (lo:=5583) (a:=399) (b:=399) s5583 s5982)))) (join_sums term (lo:=6381) (a:=3191) (b:=3191) (join_sums term (lo:=6381) (a:=1595) (b:=1596) (join_sums term (lo:=6381) (a:=797) (b:=798) (join_sums term (lo:=6381) (a:=398) (b:=399) s6381 s6779) (join_sums term (lo:=7178) (a:=399) (b:=399) s7178 s7577)) (join_sums term (lo:=7976) (a:=798) (b:=798) (join_sums term (lo:=7976) (a:=399) (b:=399) s7976 s8375) (join_sums term (lo:=8774) (a:=399) (b:=399) s8774 s9173))) (join_sums term (lo:=9572) (a:=1595) (b:=1596) (join_sums term (lo:=9572) (a:=797) (b:=798) (join_sums term (lo:=9572) (a:=398) (b:=399) s9572 s9970) (join_sums term (lo:=10369) (a:=399) (b:=399) s10369 s10768)) (join_sums term (lo:=11167) (a:=798) (b:=798) (join_sums term (lo:=11167) (a:=399) (b:=399) s11167 s11566) (join_sums term (lo:=11965) (a:=399) (b:=399) s11965 s12364))))) (join_sums term (lo:=12763) (a:=6381) (b:=6382) (join_sums term (lo:=12763) (a:=3190) (b:=3191) (join_sums term (lo:=12763) (a:=1595) (b:=1595) (join_sums term (lo:=12763) (a:=797) (b:=798) (join_sums term (lo:=12763) (a:=398) (b:=399) s12763 s13161) (join_sums term (lo:=13560) (a:=399) (b:=399) s13560 s13959)) (join_sums term (lo:=14358) (a:=797) (b:=798) (join_sums term (lo:=14358) (a:=398) (b:=399) s14358 s14756) (join_sums term (lo:=15155) (a:=399) (b:=399) s15155 s15554))) (join_sums term (lo:=15953) (a:=1595) (b:=1596) (join_sums term (lo:=15953) (a:=797) (b:=798) (join_sums term (lo:=15953) (a:=398) (b:=399) s15953 s16351) (join_sums term (lo:=16750) (a:=399) (b:=399) s16750 s17149)) (join_sums term (lo:=17548) (a:=798) (b:=798) (join_sums term (lo:=17548) (a:=399) (b:=399) s17548 s17947) (join_sums term (lo:=18346) (a:=399) (b:=399) s18346 s18745)))) (join_sums term (lo:=19144) (a:=3191) (b:=3191) (join_sums term (lo:=19144) (a:=1595) (b:=1596) (join_sums term (lo:=19144) (a:=797) (b:=798) (join_sums term (lo:=19144) (a:=398) (b:=399) s19144 s19542) (join_sums term (lo:=19941) (a:=399) (b:=399) s19941 s20340)) (join_sums term (lo:=20739) (a:=798) (b:=798) (join_sums term (lo:=20739) (a:=399) (b:=399) s20739 s21138) (join_sums term (lo:=21537) (a:=399) (b:=399) s21537 s21936))) (join_sums term (lo:=22335) (a:=1595) (b:=1596) (join_sums term (lo:=22335) (a:=797) (b:=798) (join_sums term (lo:=22335) (a:=398) (b:=399) s22335 s22733) (join_sums term (lo:=23132) (a:=399) (b:=399) s23132 s23531)) (join_sums term (lo:=23930) (a:=798) (b:=798) (join_sums term (lo:=23930) (a:=399) (b:=399) s23930 s24329) (join_sums term (lo:=24728) (a:=399) (b:=399) s24728 s25127)))))) (join_sums term (lo:=25526) (a:=12763) (b:=12764) (join_sums term (lo:=25526) (a:=6381) (b:=6382) (join_sums term (lo:=25526) (a:=3190) (b:=3191) (join_sums term (lo:=25526) (a:=1595) (b:=1595) (join_sums term (lo:=25526) (a:=797) (b:=798) (join_sums term (lo:=25526) (a:=398) (b:=399) s25526 s25924) (join_sums term (lo:=26323) (a:=399) (b:=399) s26323 s26722)) (join_sums term (lo:=27121) (a:=797) (b:=798) (join_sums term (lo:=27121) (a:=398) (b:=399) s27121 s27519) (join_sums term (lo:=27918) (a:=399) (b:=399) s27918 s28317))) (join_sums term (lo:=28716) (a:=1595) (b:=1596) (join_sums term (lo:=28716) (a:=797) (b:=798) (join_sums term (lo:=28716) (a:=398) (b:=399) s28716 s29114) (join_sums term (lo:=29513) (a:=399) (b:=399) s29513 s29912)) (join_sums term (lo:=30311) (a:=798) (b:=798) (join_sums term (lo:=30311) (a:=399) (b:=399) s30311 s30710) (join_sums term (lo:=31109) (a:=399) (b:=399) s31109 s31508)))) (join_sums term (lo:=31907) (a:=3191) (b:=3191) (join_sums term (lo:=31907) (a:=1595) (b:=1596) (join_sums term (lo:=31907) (a:=797) (b:=798) (join_sums term (lo:=31907) (a:=398) (b:=399) s31907 s32305) (join_sums term (lo:=32704) (a:=399) (b:=399) s32704 s33103)) (join_sums term (lo:=33502) (a:=798) (b:=798) (join_sums term (lo:=33502) (a:=399) (b:=399) s33502 s33901) (join_sums term (lo:=34300) (a:=399) (b:=399) s34300 s34699))) (join_sums term (lo:=35098) (a:=1595) (b:=1596) (join_sums term (lo:=35098) (a:=797) (b:=798) (join_sums term (lo:=35098) (a:=398) (b:=399) s35098 s35496) (join_sums term (lo:=35895) (a:=399) (b:=399) s35895 s36294)) (join_sums term (lo:=36693) (a:=798) (b:=798) (join_sums term (lo:=36693) (a:=399) (b:=399) s36693 s37092) (join_sums term (lo:=37491) (a:=399) (b:=399) s37491 s37890))))) (join_sums term (lo:=38289) (a:=6382) (b:=6382) (join_sums term (lo:=38289) (a:=3191) (b:=3191) (join_sums term (lo:=38289) (a:=1595) (b:=1596) (join_sums term (lo:=38289) (a:=797) (b:=798) (join_sums term (lo:=38289) (a:=398) (b:=399) s38289 s38687) (join_sums term (lo:=39086) (a:=399) (b:=399) s39086 s39485)) (join_sums term (lo:=39884) (a:=798) (b:=798) (join_sums term (lo:=39884) (a:=399) (b:=399) s39884 s40283) (join_sums term (lo:=40682) (a:=399) (b:=399) s40682 s41081))) (join_sums term (lo:=41480) (a:=1595) (b:=1596) (join_sums term (lo:=41480) (a:=797) (b:=798) (join_sums term (lo:=41480) (a:=398) (b:=399) s41480 s41878) (join_sums term (lo:=42277) (a:=399) (b:=399) s42277 s42676)) (join_sums term (lo:=43075) (a:=798) (b:=798) (join_sums term (lo:=43075) (a:=399) (b:=399) s43075 s43474) (join_sums term (lo:=43873) (a:=399) (b:=399) s43873 s44272)))) (join_sums term (lo:=44671) (a:=3191) (b:=3191) (join_sums term (lo:=44671) (a:=1595) (b:=1596) (join_sums term (lo:=44671) (a:=797) (b:=798) (join_sums term (lo:=44671) (a:=398) (b:=399) s44671 s45069) (join_sums term (lo:=45468) (a:=399) (b:=399) s45468 s45867)) (join_sums term (lo:=46266) (a:=798) (b:=798) (join_sums term (lo:=46266) (a:=399) (b:=399) s46266 s46665) (join_sums term (lo:=47064) (a:=399) (b:=399) s47064 s47463))) (join_sums term (lo:=47862) (a:=1595) (b:=1596) (join_sums term (lo:=47862) (a:=797) (b:=798) (join_sums term (lo:=47862) (a:=398) (b:=399) s47862 s48260) (join_sums term (lo:=48659) (a:=399) (b:=399) s48659 s49058)) (join_sums term (lo:=49457) (a:=798) (b:=798) (join_sums term (lo:=49457) (a:=399) (b:=399) s49457 s49856) (join_sums term (lo:=50255) (a:=399) (b:=399) s50255 s50654))))))) (join_sums term (lo:=51053) (a:=25526) (b:=25527) (join_sums term (lo:=51053) (a:=12763) (b:=12763) (join_sums term (lo:=51053) (a:=6381) (b:=6382) (join_sums term (lo:=51053) (a:=3190) (b:=3191) (join_sums term (lo:=51053) (a:=1595) (b:=1595) (join_sums term (lo:=51053) (a:=797) (b:=798) (join_sums term (lo:=51053) (a:=398) (b:=399) s51053 s51451) (join_sums term (lo:=51850) (a:=399) (b:=399) s51850 s52249)) (join_sums term (lo:=52648) (a:=797) (b:=798) (join_sums term (lo:=52648) (a:=398) (b:=399) s52648 s53046) (join_sums term (lo:=53445) (a:=399) (b:=399) s53445 s53844))) (join_sums term (lo:=54243) (a:=1595) (b:=1596) (join_sums term (lo:=54243) (a:=797) (b:=798) (join_sums term (lo:=54243) (a:=398) (b:=399) s54243 s54641) (join_sums term (lo:=55040) (a:=399) (b:=399) s55040 s55439)) (join_sums term (lo:=55838) (a:=798) (b:=798) (join_sums term (lo:=55838) (a:=399) (b:=399) s55838 s56237) (join_sums term (lo:=56636) (a:=399) (b:=399) s56636 s57035)))) (join_sums term (lo:=57434) (a:=3191) (b:=3191) (join_sums term (lo:=57434) (a:=1595) (b:=1596) (join_sums term (lo:=57434) (a:=797) (b:=798) (join_sums term (lo:=57434) (a:=398) (b:=399) s57434 s57832) (join_sums term (lo:=58231) (a:=399) (b:=399) s58231 s58630)) (join_sums term (lo:=59029) (a:=798) (b:=798) (join_sums term (lo:=59029) (a:=399) (b:=399) s59029 s59428) (join_sums term (lo:=59827) (a:=399) (b:=399) s59827 s60226))) (join_sums term (lo:=60625) (a:=1595) (b:=1596) (join_sums term (lo:=60625) (a:=797) (b:=798) (join_sums term (lo:=60625) (a:=398) (b:=399) s60625 s61023) (join_sums term (lo:=61422) (a:=399) (b:=399) s61422 s61821)) (join_sums term (lo:=62220) (a:=798) (b:=798) (join_sums term (lo:=62220) (a:=399) (b:=399) s62220 s62619) (join_sums term (lo:=63018) (a:=399) (b:=399) s63018 s63417))))) (join_sums term (lo:=63816) (a:=6381) (b:=6382) (join_sums term (lo:=63816) (a:=3190) (b:=3191) (join_sums term (lo:=63816) (a:=1595) (b:=1595) (join_sums term (lo:=63816) (a:=797) (b:=798) (join_sums term (lo:=63816) (a:=398) (b:=399) s63816 s64214) (join_sums term (lo:=64613) (a:=399) (b:=399) s64613 s65012)) (join_sums term (lo:=65411) (a:=797) (b:=798) (join_sums term (lo:=65411) (a:=398) (b:=399) s65411 s65809) (join_sums term (lo:=66208) (a:=399) (b:=399) s66208 s66607))) (join_sums term (lo:=67006) (a:=1595) (b:=1596) (join_sums term (lo:=67006) (a:=797) (b:=798) (join_sums term (lo:=67006) (a:=398) (b:=399) s67006 s67404) (join_sums term (lo:=67803) (a:=399) (b:=399) s67803 s68202)) (join_sums term (lo:=68601) (a:=798) (b:=798) (join_sums term (lo:=68601) (a:=399) (b:=399) s68601 s69000) (join_sums term (lo:=69399) (a:=399) (b:=399) s69399 s69798)))) (join_sums term (lo:=70197) (a:=3191) (b:=3191) (join_sums term (lo:=70197) (a:=1595) (b:=1596) (join_sums term (lo:=70197) (a:=797) (b:=798) (join_sums term (lo:=70197) (a:=398) (b:=399) s70197 s70595) (join_sums term (lo:=70994) (a:=399) (b:=399) s70994 s71393)) (join_sums term (lo:=71792) (a:=798) (b:=798) (join_sums term (lo:=71792) (a:=399) (b:=399) s71792 s72191) (join_sums term (lo:=72590) (a:=399) (b:=399) s72590 s72989))) (join_sums term (lo:=73388) (a:=1595) (b:=1596) (join_sums term (lo:=73388) (a:=797) (b:=798) (join_sums term (lo:=73388) (a:=398) (b:=399) s73388 s73786) (join_sums term (lo:=74185) (a:=399) (b:=399) s74185 s74584)) (join_sums term (lo:=74983) (a:=798) (b:=798) (join_sums term (lo:=74983) (a:=399) (b:=399) s74983 s75382) (join_sums term (lo:=75781) (a:=399) (b:=399) s75781 s76180)))))) (join_sums term (lo:=76579) (a:=12763) (b:=12764) (join_sums term (lo:=76579) (a:=6381) (b:=6382) (join_sums term (lo:=76579) (a:=3190) (b:=3191) (join_sums term (lo:=76579) (a:=1595) (b:=1595) (join_sums term (lo:=76579) (a:=797) (b:=798) (join_sums term (lo:=76579) (a:=398) (b:=399) s76579 s76977) (join_sums term (lo:=77376) (a:=399) (b:=399) s77376 s77775)) (join_sums term (lo:=78174) (a:=797) (b:=798) (join_sums term (lo:=78174) (a:=398) (b:=399) s78174 s78572) (join_sums term (lo:=78971) (a:=399) (b:=399) s78971 s79370))) (join_sums term (lo:=79769) (a:=1595) (b:=1596) (join_sums term (lo:=79769) (a:=797) (b:=798) (join_sums term (lo:=79769) (a:=398) (b:=399) s79769 s80167) (join_sums term (lo:=80566) (a:=399) (b:=399) s80566 s80965)) (join_sums term (lo:=81364) (a:=798) (b:=798) (join_sums term (lo:=81364) (a:=399) (b:=399) s81364 s81763) (join_sums term (lo:=82162) (a:=399) (b:=399) s82162 s82561)))) (join_sums term (lo:=82960) (a:=3191) (b:=3191) (join_sums term (lo:=82960) (a:=1595) (b:=1596) (join_sums term (lo:=82960) (a:=797) (b:=798) (join_sums term (lo:=82960) (a:=398) (b:=399) s82960 s83358) (join_sums term (lo:=83757) (a:=399) (b:=399) s83757 s84156)) (join_sums term (lo:=84555) (a:=798) (b:=798) (join_sums term (lo:=84555) (a:=399) (b:=399) s84555 s84954) (join_sums term (lo:=85353) (a:=399) (b:=399) s85353 s85752))) (join_sums term (lo:=86151) (a:=1595) (b:=1596) (join_sums term (lo:=86151) (a:=797) (b:=798) (join_sums term (lo:=86151) (a:=398) (b:=399) s86151 s86549) (join_sums term (lo:=86948) (a:=399) (b:=399) s86948 s87347)) (join_sums term (lo:=87746) (a:=798) (b:=798) (join_sums term (lo:=87746) (a:=399) (b:=399) s87746 s88145) (join_sums term (lo:=88544) (a:=399) (b:=399) s88544 s88943))))) (join_sums term (lo:=89342) (a:=6382) (b:=6382) (join_sums term (lo:=89342) (a:=3191) (b:=3191) (join_sums term (lo:=89342) (a:=1595) (b:=1596) (join_sums term (lo:=89342) (a:=797) (b:=798) (join_sums term (lo:=89342) (a:=398) (b:=399) s89342 s89740) (join_sums term (lo:=90139) (a:=399) (b:=399) s90139 s90538)) (join_sums term (lo:=90937) (a:=798) (b:=798) (join_sums term (lo:=90937) (a:=399) (b:=399) s90937 s91336) (join_sums term (lo:=91735) (a:=399) (b:=399) s91735 s92134))) (join_sums term (lo:=92533) (a:=1595) (b:=1596) (join_sums term (lo:=92533) (a:=797) (b:=798) (join_sums term (lo:=92533) (a:=398) (b:=399) s92533 s92931) (join_sums term (lo:=93330) (a:=399) (b:=399) s93330 s93729)) (join_sums term (lo:=94128) (a:=798) (b:=798) (join_sums term (lo:=94128) (a:=399) (b:=399) s94128 s94527) (join_sums term (lo:=94926) (a:=399) (b:=399) s94926 s95325)))) (join_sums term (lo:=95724) (a:=3191) (b:=3191) (join_sums term (lo:=95724) (a:=1595) (b:=1596) (join_sums term (lo:=95724) (a:=797) (b:=798) (join_sums term (lo:=95724) (a:=398) (b:=399) s95724 s96122) (join_sums term (lo:=96521) (a:=399) (b:=399) s96521 s96920)) (join_sums term (lo:=97319) (a:=798) (b:=798) (join_sums term (lo:=97319) (a:=399) (b:=399) s97319 s97718) (join_sums term (lo:=98117) (a:=399) (b:=399) s98117 s98516))) (join_sums term (lo:=98915) (a:=1595) (b:=1596) (join_sums term (lo:=98915) (a:=797) (b:=798) (join_sums term (lo:=98915) (a:=398) (b:=399) s98915 s99313) (join_sums term (lo:=99712) (a:=399) (b:=399) s99712 s100111)) (join_sums term (lo:=100510) (a:=798) (b:=798) (join_sums term (lo:=100510) (a:=399) (b:=399) s100510 s100909) (join_sums term (lo:=101308) (a:=399) (b:=399) s101308 s101707))))))))

set_option maxRecDepth 8000 in
private theorem right_part :
    (∑ p ∈ (Nat.primesLE 102105).filter (2184 < ·),
      (Nat.primeCounting (10425579253/p) - Nat.primeCounting (p-1))) = 291216679 :=
  right_from_blocks tab prime HybridBound10425.fast_correct prime_ok (by decide) (by decide) rows

set_option maxRecDepth 12000 in
theorem exact_count : Nat.primeCounting 10425579253 = 473516370 :=
  assemble (x:=10425579253) (y:=2184) (z:=102105) (a:=764733050) (b:=291216679) (r:=473516370)
    (by decide) (by decide) (by decide) (by decide) (by decide) left_part right_part (by decide)
end JointEndpoint10425
