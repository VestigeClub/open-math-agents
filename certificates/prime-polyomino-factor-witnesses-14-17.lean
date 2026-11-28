import Mathlib

/-!
# Prime factors of a polyomino

Gordon Hamilton's four proposed maxima in OEIS A380455. Each factor tiles
the whole board with congruent copies of itself. Translations, rotations,
and reflections are allowed, and the one-cell shape is the unit.

Sources: https://oeis.org/A380455 and https://oeis.org/A342430.
-/

namespace OMA.S_oeis_a380455

abbrev Cell := ℤ × ℤ
abbrev Shape := Finset Cell

def adjacent (u v : Cell) : Prop :=
  (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)) ∨
  (u.2 = v.2 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1))

def polyomino (s : Shape) : Prop :=
  s.Nonempty ∧ ∀ p q : {c // c ∈ s},
    Relation.ReflTransGen (fun a b : {c // c ∈ s} => adjacent a.val b.val) p q

def congruent (a b : Shape) : Prop :=
  ∃ (swap : Bool) (sx sy : ℤ) (offset : Cell),
    (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧
    b = a.image (fun c =>
      let d := if swap then (c.2, c.1) else c
      (offset.1 + sx * d.1, offset.2 + sy * d.2))

def tiles (factor board : Shape) : Prop :=
  ∃ parts : Finset Shape,
    parts.Nonempty ∧ parts.biUnion id = board ∧
    (∀ p ∈ parts, congruent factor p) ∧
    (∀ p ∈ parts, ∀ q ∈ parts, p ≠ q → Disjoint p q)

/-- A prime shape has no monohedral tiling by a smaller nonunit shape. -/
def primeShape (s : Shape) : Prop :=
  polyomino s ∧ 1 < s.card ∧
    ∀ t : Shape, polyomino t → 1 < t.card → tiles t s → t.card = s.card

/-- A single board of area n admits k pairwise noncongruent prime factors.
Each factor has its own tiling of the board. -/
def realizes (n k : ℕ) : Prop :=
  ∃ (board : Shape) (factors : Finset Shape),
    polyomino board ∧ board.card = n ∧ factors.card = k ∧
    (∀ t ∈ factors, primeShape t ∧ tiles t board) ∧
    (∀ p ∈ factors, ∀ q ∈ factors, congruent p q → p = q)

def maximum (n k : ℕ) : Prop :=
  realizes n k ∧ ∀ j : ℕ, realizes n j → j ≤ k

end OMA.S_oeis_a380455

open Finset OMA.S_oeis_a380455
namespace PrimePolyFactor

structure Orientation where
  swap : Bool
  flipX : Bool
  flipY : Bool
deriving DecidableEq, Fintype

def sign (b : Bool) : ℤ := if b then -1 else 1

def turn (g : Orientation) (p : Cell) : Cell :=
  let q := if g.swap then (p.2,p.1) else p
  (sign g.flipX * q.1,sign g.flipY * q.2)

def move (g : Orientation) (o p : Cell) : Cell := o + turn g p

private theorem sign_ok (b : Bool) : sign b=1 ∨ sign b = -1 := by cases b <;> decide

private theorem sign_exists {x : ℤ} (h : x=1 ∨ x= -1) : ∃ b, x=sign b := by
  rcases h with rfl|rfl
  · exact ⟨false,rfl⟩
  · exact ⟨true,rfl⟩

theorem congruent_iff (A B : Shape) :
    congruent A B ↔ ∃ (g : Orientation) (o : Cell), B=A.image (move g o) := by
  constructor
  · rintro ⟨sw,sx,sy,o,hx,hy,rfl⟩
    obtain ⟨a,rfl⟩ := sign_exists hx
    obtain ⟨b,rfl⟩ := sign_exists hy
    exact ⟨⟨sw,a,b⟩,o,rfl⟩
  · rintro ⟨⟨sw,a,b⟩,o,rfl⟩
    exact ⟨sw,sign a,sign b,o,sign_ok a,sign_ok b,rfl⟩

def inverse (g : Orientation) : Orientation :=
  if g.swap then ⟨true,g.flipY,g.flipX⟩ else g

def compose (g h : Orientation) : Orientation :=
  ⟨g.swap ^^ h.swap,(if h.swap then g.flipY else g.flipX) ^^ h.flipX,
    (if h.swap then g.flipX else g.flipY) ^^ h.flipY⟩

theorem turn_inv (g : Orientation) (p : Cell) : turn (inverse g) (turn g p)=p := by
  obtain ⟨s,a,b⟩ := g
  cases s <;> cases a <;> cases b <;> simp [turn,inverse,sign]

theorem turn_comp (g h : Orientation) (p : Cell) : turn (compose g h) p=turn h (turn g p) := by
  obtain ⟨s,a,b⟩ := g
  obtain ⟨t,c,d⟩ := h
  cases s <;> cases t <;> cases a <;> cases b <;> cases c <;> cases d <;> simp [turn,compose,sign]

theorem turn_add (g : Orientation) (p q : Cell) : turn g (p+q)=turn g p+turn g q := by
  obtain ⟨s,a,b⟩:=g
  cases s <;> ext <;> simp [turn,mul_add]

theorem motion_card {A B : Shape} (h : congruent A B) : A.card=B.card := by
  obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp h
  symm
  apply card_image_of_injective
  intro p q eq
  have e : turn g p = turn g q := add_left_cancel (show o+turn g p=o+turn g q from eq)
  simpa only [turn_inv] using congrArg (turn (inverse g)) e

theorem motion_symm {A B : Shape} (h : congruent A B) : congruent B A := by
  obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp h
  apply (congruent_iff _ _).mpr
  refine ⟨inverse g,-turn (inverse g) o,?_⟩
  rw [image_image]
  have e : move (inverse g) (-turn (inverse g) o) ∘ move g o = id := by
    funext p
    simp [move,turn_add,turn_inv]
  simp only [e,image_id]

theorem motion_trans {A B C : Shape} (h : congruent A B) (k : congruent B C) : congruent A C := by
  obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp h
  obtain ⟨f,p,rfl⟩ := (congruent_iff _ _).mp k
  apply (congruent_iff _ _).mpr
  refine ⟨compose g f,p+turn f o,?_⟩
  rw [image_image]
  apply Finset.image_congr
  intro v hv
  simp [move,turn_add,turn_comp,add_assoc]

def pairWeight (p q : Cell) : ℕ :=
  let a := (p.1-q.1).natAbs
  let b := (p.2-q.2).natAbs
  64 ^ (5*max a b + min a b)

def signature (s : Shape) : ℕ :=
  ∑ p ∈ s, (∑ q ∈ s, pairWeight p q)^2

private theorem sign_delta (b : Bool) (x y : ℤ) :
    (sign b*x-sign b*y).natAbs=(x-y).natAbs := by
  rw [← mul_sub,Int.natAbs_mul]
  cases b <;> simp [sign]

private theorem weight_move (g : Orientation) (o p q : Cell) :
    pairWeight (move g o p) (move g o q)=pairWeight p q := by
  obtain ⟨s,x,y⟩:=g
  cases s <;> simp [pairWeight,move,turn,sign_delta,max_comm,min_comm]

theorem signature_invariant {A B : Shape} (eq : congruent A B) : signature A=signature B := by
  obtain ⟨g,o,rfl⟩ := (congruent_iff A B).mp eq
  have inj : Function.Injective (move g o) := by
    intro p q h
    have e : turn g p=turn g q := add_left_cancel (show o+turn g p=o+turn g q from h)
    simpa only [turn_inv] using congrArg (turn (inverse g)) e
  unfold signature
  rw [sum_image inj.injOn]
  apply sum_congr rfl
  intro p hp
  rw [sum_image inj.injOn]
  simp only [weight_move]

private theorem reverse_adj {a b : Cell} (h : adjacent a b) : adjacent b a := by
  rcases h with ⟨e,f|f⟩|⟨e,f|f⟩
  · exact Or.inl ⟨e.symm, Or.inr f⟩
  · exact Or.inl ⟨e.symm, Or.inl f⟩
  · exact Or.inr ⟨e.symm, Or.inr f⟩
  · exact Or.inr ⟨e.symm, Or.inl f⟩

private theorem add_cell {s : Shape} (h : polyomino s) (p q : Cell) (mem : q∈s)
    (edge : adjacent p q) : polyomino (insert p s) := by
  let lift (z : s) : ↥(insert p s) := ⟨z.val,mem_insert_of_mem z.property⟩
  let R (a b : ↥(insert p s)) := adjacent a.val b.val
  have within (a b : s) : Relation.ReflTransGen R (lift a) (lift b) :=
    Relation.ReflTransGen.lift lift (fun _ _ e => e) a b (h.2 a b)
  have both (a : ↥(insert p s)) :
      Relation.ReflTransGen R a (lift ⟨q,mem⟩) ∧ Relation.ReflTransGen R (lift ⟨q,mem⟩) a := by
    obtain ⟨v,hv⟩:=a
    rcases mem_insert.mp hv with rfl|hv
    · exact ⟨.single edge,.single (reverse_adj edge)⟩
    · exact ⟨within ⟨v,hv⟩ _,within _ ⟨v,hv⟩⟩
  exact ⟨insert_nonempty _ _,fun a b => (both a).1.trans (both b).2⟩

def neighborFlag (a b : Cell) : Bool :=
  decide ((a.1=b.1 ∧ (a.2+1=b.2 ∨ b.2+1=a.2)) ∨
    (a.2=b.2 ∧ (a.1+1=b.1 ∨ b.1+1=a.1)))

private theorem neighborFlag_spec (p q : Cell) : neighborFlag p q=true ↔ adjacent p q :=
  decide_eq_true_iff

def building : List Cell → Bool
  | [] => false
  | [_] => true
  | p::q::rest => building (q::rest) && (q::rest).any (neighborFlag p)

theorem poly_of_building : ∀ l : List Cell, building l=true → polyomino l.toFinset
  | [],h => by simp [building] at h
  | [p],_ => by
    refine ⟨by simp,?_⟩
    rintro ⟨a,ha⟩ ⟨b,hb⟩
    simp at ha hb
    subst a
    subst b
    rfl
  | p::q::rest,h => by
    have hb : building (q::rest)=true ∧ (q::rest).any (neighborFlag p)=true := by
      simpa only [building,Bool.and_eq_true] using h
    obtain ⟨v,hv,edge⟩ := List.any_eq_true.mp hb.2
    simpa only [List.toFinset_cons] using add_cell (poly_of_building _ hb.1) p v (List.mem_toFinset.mpr hv) ((neighborFlag_spec _ _).mp edge)

theorem move_injective (g : Orientation) (o : Cell) : Function.Injective (move g o) := by
  intro p q e
  have h : turn g p=turn g q := add_left_cancel (show o+turn g p=o+turn g q from e)
  simpa only [turn_inv] using congrArg (turn (inverse g)) h

theorem self_congruent (s : Shape) : congruent s s := by
  refine (congruent_iff _ _).mpr ⟨⟨false,false,false⟩,0,?_⟩
  have g : move ⟨false,false,false⟩ 0 = id := by funext p; ext <;> simp [move,turn,sign]
  simp [g]

theorem tile_area {f b : Shape} (tiling : tiles f b) : f.card ∣ b.card := by
  classical
  obtain ⟨parts,_,cover,cong,disj⟩ := tiling
  have rest : (∑ t∈parts,t.card)=parts.card*f.card := by
    calc
      _ = ∑ _t∈parts,f.card := sum_congr rfl (fun t ht => (motion_card (cong t ht)).symm)
      _ = _ := by simp
  refine ⟨parts.card,?_⟩
  rw [← cover,card_biUnion (by
    intro i hi j hj ne
    exact disj i hi j hj ne)]
  simpa only [id_eq,Nat.mul_comm] using rest

theorem prime_area {s : Shape} (poly : polyomino s) (prime : s.card.Prime) : primeShape s := by
  refine ⟨poly,prime.one_lt,?_⟩
  intro t _ h ts
  exact ((Nat.dvd_prime prime).mp (tile_area ts)).resolve_left (by omega)

theorem single_tile {s b : Shape} (h : tiles s b) (eq : s.card=b.card) : congruent s b := by
  obtain ⟨parts,⟨p,hp⟩,cover,cong,_⟩:=h
  have sub : p⊆b := by
    rw [← cover]
    intro a ha
    exact mem_biUnion.mpr ⟨p,hp,ha⟩
  have e : p=b := eq_of_subset_of_card_le sub (by rw [← eq,motion_card (cong p hp)])
  exact e ▸ cong p hp

theorem tiles_itself (s : Shape) : tiles s s := by
  refine ⟨{s},by simp,by simp,?_,?_⟩
  · simpa using self_congruent s
  · simp

theorem one_factor_of_prime {n : ℕ} (prime : n.Prime)
    (exists_poly : ∃ s : Shape,polyomino s ∧ s.card=n) : maximum n 1 := by
  obtain ⟨s,poly,hs⟩:=exists_poly
  constructor
  · refine ⟨s,{s},poly,hs,by simp,?_,?_⟩
    · simpa using And.intro (prime_area poly (hs ▸ prime)) (tiles_itself s)
    · simp
  · rintro j ⟨b,fs,_,hb,hj,fact,different⟩
    rw [← hj,card_le_one]
    have all (t : Shape) (ht : t∈fs) : congruent t b := by
      have g := fact t ht
      have p : b.card.Prime := hb ▸ prime
      exact single_tile g.2 (((Nat.dvd_prime p).mp (tile_area g.2)).resolve_left (by
        have := g.1.2.1
        omega))
    intro p hp q hq
    exact different p hp q hq (motion_trans (all p hp) (motion_symm (all q hq)))

def mark (p : Cell) : ZMod 2 := (p.1 : ZMod 2)+(p.2 : ZMod 2)
def mass (s : Shape) : ZMod 2 := ∑ p∈s,mark p

private theorem affine_mark (g : Orientation) (o p : Cell) :
    mark (move g o p)=mark o+mark p := by
  obtain ⟨s,a,b⟩:=g
  cases s <;> cases a <;> cases b <;> simp [move,turn,sign,mark] <;> ring

theorem mass_motion {s t : Shape} (h : congruent s t) (even : (s.card : ZMod 2)=0) :
    mass t=mass s := by
  obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp h
  unfold mass
  rw [sum_image (move_injective g o).injOn]
  simp only [affine_mark,sum_add_distrib,sum_const,nsmul_eq_mul,even,zero_mul,zero_add]

private theorem eight_arithmetic {n k : ℕ} (h : k*n=8) (two : 1<n) (proper : n≠8) :
    (n=2 ∧ k=4) ∨ (n=4 ∧ k=2) := by
  have pos : 0<k := by
    cases k with
    | zero => simp at h
    | succ k => omega
  have bound : n≤8 := h ▸ Nat.le_mul_of_pos_left n pos
  interval_cases n <;> omega

theorem odd_mass_eight {s : Shape} (poly : polyomino s) (size : s.card=8) (odd : mass s≠0) :
    primeShape s := by
  classical
  refine ⟨poly,by omega,?_⟩
  rintro t _ nt ⟨parts,_,cover,cong,disj⟩
  by_contra bad
  have sep : (↑parts : Set Shape).PairwiseDisjoint id := by
    intro a ha b hb ne
    exact disj a ha b hb ne
  have ar : parts.card*t.card=8 := calc
    _ = ∑ _u∈parts,t.card := by simp
    _ = ∑ u∈parts,u.card := sum_congr rfl (fun u hu => motion_card (cong u hu))
    _ = (parts.biUnion id).card := (card_biUnion sep).symm
    _ = 8 := by rw [cover,size]
  have cases_ := eight_arithmetic ar nt (by simpa only [size] using bad)
  have even_size : (t.card : ZMod 2)=0 := by rcases cases_ with h|h <;> rw [h.1] <;> decide
  have even_q : (parts.card : ZMod 2)=0 := by rcases cases_ with h|h <;> rw [h.2] <;> decide
  apply odd
  change (∑ c∈s,mark c) = 0
  rw [← cover,sum_biUnion sep]
  calc
    _ = ∑ _u∈parts,mass t := sum_congr rfl (fun u hu => mass_motion (cong u hu) even_size)
    _ = 0 := by simp [nsmul_eq_mul,even_q]

end PrimePolyFactor

open Finset OMA.S_oeis_a380455
namespace PrimePolyFactor

abbrev Placement := Orientation × Cell

def tileParts (s : Shape) (places : List Placement) : Finset Shape :=
  (places.map (fun m => s.image (move m.1 m.2))).toFinset

def checkTiling (s board : Shape) (places : List Placement) : Bool :=
  let parts := tileParts s places
  decide (parts.Nonempty ∧ parts.biUnion id=board ∧
    ∀ p∈parts, ∀ q∈parts, p≠q → Disjoint p q)

theorem checked_tiling {s b : Shape} {ms : List Placement} (ok : checkTiling s b ms=true) :
    tiles s b := by
  let parts := tileParts s ms
  have h : parts.Nonempty ∧ parts.biUnion id = b ∧
      ∀ p∈parts, ∀ q∈parts, p≠q → Disjoint p q := of_decide_eq_true ok
  refine ⟨parts,h.1,h.2.1,?_,h.2.2⟩
  intro p hp
  obtain ⟨m,_,em⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  exact (congruent_iff _ _).mpr ⟨m.1,m.2,em.symm⟩

structure Entry where
  cells : List Cell
  places : List Placement

def entryShape (e : Entry) : Shape := e.cells.toFinset

def entryCheck (board : Shape) (e : Entry) : Bool :=
  building e.cells && (decide (entryShape e).card.Prime ||
      decide ((entryShape e).card=8 ∧ mass (entryShape e)≠0)) &&
    checkTiling (entryShape e) board e.places

theorem entry_ok (board : Shape) (e : Entry) (ok : entryCheck board e=true) :
    primeShape (entryShape e) ∧ tiles (entryShape e) board := by
  simp only [entryCheck,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ok
  have poly := poly_of_building e.cells ok.1.1
  refine ⟨?_,checked_tiling ok.2⟩
  rcases ok.1.2 with hp|⟨sz,odd⟩
  · exact prime_area poly hp
  · exact odd_mass_eight poly sz odd

def modelsOf (es : List Entry) : Finset Shape := (es.map entryShape).toFinset

theorem of_entries (n k : ℕ) (b : List Cell) (entries : List Entry)
    (connected : building b=true) (area : b.toFinset.card=n)
    (count : (modelsOf entries).card=k) (ok : entries.all (entryCheck b.toFinset)=true)
    (unique : ((modelsOf entries).image signature).card=(modelsOf entries).card) :
    realizes n k := by
  refine ⟨b.toFinset,modelsOf entries,poly_of_building _ connected,area,count,?_,?_⟩
  · intro t ht
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    exact entry_ok _ _ (List.all_eq_true.mp ok e he)
  · intro p hp q hq eq
    exact card_image_iff.mp unique hp hq (signature_invariant eq)

end PrimePolyFactor

open Finset OMA.S_oeis_a380455
namespace PrimePolyFactor

def boardFourteen : List Cell := [(5,2),(4,2),(3,2),(4,1),(2,2),(3,1),(4,0),(1,2),(2,1),(3,0),(1,1),(2,0),(1,0),(0,0)]

def factorsFourteen : List Entry := [
  ⟨[(4,0),(3,0),(1,1),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(4,0)),(⟨false,false,true⟩,(1,2))]⟩,
  ⟨[(4,0),(2,1),(3,0),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(4,0)),(⟨false,false,true⟩,(1,2))]⟩,
  ⟨[(4,0),(2,1),(3,0),(1,1),(2,0),(1,0),(0,0)],[(⟨false,false,false⟩,(0,0)),(⟨false,true,true⟩,(5,2))]⟩,
  ⟨[(3,1),(4,0),(3,0),(1,1),(2,0),(1,0),(0,0)],[(⟨false,false,false⟩,(0,0)),(⟨false,false,true⟩,(1,2))]⟩,
  ⟨[(2,2),(2,1),(3,0),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(3,0)),(⟨false,false,true⟩,(2,2))]⟩,
  ⟨[(1,2),(2,1),(3,0),(1,1),(2,0),(1,0),(0,0)],[(⟨false,false,false⟩,(0,0)),(⟨false,true,true⟩,(5,2))]⟩,
  ⟨[(2,1),(0,2),(1,1),(2,0),(0,1),(1,0),(0,0)],[(⟨true,true,false⟩,(2,0)),(⟨true,false,true⟩,(3,2))]⟩,
  ⟨[(3,2),(2,2),(2,1),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,true⟩,(3,2)),(⟨false,false,false⟩,(2,0))]⟩,
  ⟨[(3,2),(2,2),(2,1),(1,1),(2,0),(1,0),(0,0)],[(⟨false,true,true⟩,(3,2)),(⟨false,false,false⟩,(2,0))]⟩,
  ⟨[(1,0),(0,0)],[(⟨false,false,false⟩,(0,0)),(⟨false,false,false⟩,(2,0)),(⟨true,false,false⟩,(4,0)),(⟨false,false,false⟩,(1,1)),(⟨true,false,false⟩,(3,1)),(⟨false,false,false⟩,(1,2)),(⟨false,false,false⟩,(4,2))]⟩]

set_option maxRecDepth 20000 in
private theorem tested14 : factorsFourteen.all (entryCheck boardFourteen.toFinset)=true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem distinct14 : ((modelsOf factorsFourteen).image signature).card=(modelsOf factorsFourteen).card := by decide +kernel

theorem achieves_14 : realizes 14 10 :=
  of_entries 14 10 boardFourteen factorsFourteen (by decide +kernel) (by decide +kernel)
    (by decide +kernel) tested14 distinct14

end PrimePolyFactor

open Finset OMA.S_oeis_a380455
namespace PrimePolyFactor

def boardFifteen : List Cell := [(6,1),(7,0),(5,1),(6,0),(3,2),(4,1),(5,0),(3,1),(4,0),(2,1),(3,0),(1,1),(2,0),(1,0),(0,0)]

def factorsFifteen : List Entry := [
  ⟨[(3,0),(1,1),(2,0),(1,0),(0,0)],[(⟨false,false,false⟩,(0,0)),(⟨false,true,false⟩,(7,0)),(⟨false,false,false⟩,(2,1))]⟩,
  ⟨[(1,1),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(2,0)),(⟨true,false,false⟩,(3,0)),(⟨false,false,false⟩,(5,0))]⟩,
  ⟨[(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(1,0)),(⟨false,false,false⟩,(2,0)),(⟨false,true,false⟩,(5,0)),(⟨false,false,false⟩,(6,0)),(⟨false,false,false⟩,(3,1))]⟩]

set_option maxRecDepth 20000 in
private theorem tested15 : factorsFifteen.all (entryCheck boardFifteen.toFinset)=true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem distinct15 : ((modelsOf factorsFifteen).image signature).card=(modelsOf factorsFifteen).card := by decide +kernel

theorem achieves_15 : realizes 15 3 :=
  of_entries 15 3 boardFifteen factorsFifteen (by decide +kernel) (by decide +kernel)
    (by decide +kernel) tested15 distinct15

end PrimePolyFactor

open Finset OMA.S_oeis_a380455
namespace PrimePolyFactor

def boardSixteen : List Cell := [(4,3),(5,2),(3,3),(4,2),(2,3),(3,0),(3,2),(4,1),(2,0),(2,2),(3,1),(1,0),(1,2),(2,1),(1,1),(0,1)]

def factorsSixteen : List Entry := [
  ⟨[(3,1),(4,0),(2,1),(3,0),(1,1),(2,0),(1,0),(0,0)],[(⟨false,false,true⟩,(0,1)),(⟨false,false,false⟩,(1,2))]⟩,
  ⟨[(1,2),(2,1),(3,0),(1,1),(2,0),(0,1),(1,0),(0,0)],[(⟨true,true,false⟩,(2,0)),(⟨true,false,true⟩,(3,3))]⟩,
  ⟨[(2,2),(3,1),(2,1),(1,1),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(3,0)),(⟨false,false,true⟩,(2,3))]⟩,
  ⟨[(2,2),(3,1),(2,1),(0,2),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(3,0)),(⟨false,false,true⟩,(2,3))]⟩,
  ⟨[(2,2),(3,1),(1,2),(2,1),(1,1),(2,0),(1,0),(0,0)],[(⟨false,true,false⟩,(3,0)),(⟨false,false,true⟩,(2,3))]⟩,
  ⟨[(4,2),(3,2),(3,1),(2,1),(1,1),(2,0),(1,0),(0,0)],[(⟨false,false,false⟩,(1,0)),(⟨false,true,true⟩,(4,3))]⟩,
  ⟨[(4,2),(3,2),(2,2),(2,1),(1,1),(2,0),(1,0),(0,0)],[(⟨false,true,true⟩,(5,2)),(⟨false,false,false⟩,(0,1))]⟩,
  ⟨[(0,2),(1,2),(2,2),(3,1),(2,1),(2,0),(1,0),(0,0)],[(⟨false,true,false⟩,(3,0)),(⟨false,false,false⟩,(2,1))]⟩,
  ⟨[(2,3),(3,2),(2,2),(2,1),(1,1),(0,1),(1,0),(0,0)],[(⟨false,true,true⟩,(3,3)),(⟨false,false,false⟩,(2,0))]⟩,
  ⟨[(2,3),(3,2),(2,2),(1,2),(2,1),(1,1),(1,0),(0,0)],[(⟨false,true,true⟩,(3,3)),(⟨false,false,false⟩,(2,0))]⟩,
  ⟨[(4,1),(3,1),(3,0),(2,0),(1,0),(1,2),(1,1),(0,1)],[(⟨false,true,false⟩,(4,0)),(⟨false,false,true⟩,(1,3))]⟩,
  ⟨[(2,3),(3,2),(2,0),(2,2),(1,0),(1,2),(1,1),(0,1)],[(⟨false,false,false⟩,(0,0)),(⟨false,true,true⟩,(5,3))]⟩]

set_option maxRecDepth 20000 in
private theorem tested16 : factorsSixteen.all (entryCheck boardSixteen.toFinset)=true := by decide +kernel

set_option maxRecDepth 20000 in
private theorem distinct16 : ((modelsOf factorsSixteen).image signature).card=(modelsOf factorsSixteen).card := by decide +kernel

theorem achieves_16 : realizes 16 12 :=
  of_entries 16 12 boardSixteen factorsSixteen (by decide +kernel) (by decide +kernel)
    (by decide +kernel) tested16 distinct16

end PrimePolyFactor

open Finset OMA.S_oeis_a380455
namespace PrimePolyFactor

private def barSeventeen : List Cell := [(16,0),(15,0),(14,0),(13,0),(12,0),(11,0),(10,0),(9,0),(8,0),(7,0),(6,0),(5,0),(4,0),(3,0),(2,0),(1,0),(0,0)]

theorem exact_seventeen : maximum 17 1 :=
  one_factor_of_prime (by decide) ⟨barSeventeen.toFinset,poly_of_building _ (by decide +kernel),by decide +kernel⟩

end PrimePolyFactor

namespace PrimePolyFactor

theorem four_cases :
    OMA.S_oeis_a380455.realizes 14 10 ∧ OMA.S_oeis_a380455.realizes 15 3 ∧
    OMA.S_oeis_a380455.realizes 16 12 ∧ OMA.S_oeis_a380455.maximum 17 1 :=
  ⟨achieves_14, achieves_15, achieves_16, exact_seventeen⟩

end PrimePolyFactor
