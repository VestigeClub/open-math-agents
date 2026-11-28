import OMAStatements.S_oeis_a380573

/-!
Proof of the first-appearance conjecture for straight terraces in OEIS A380573.
All bounds use the published symmetric Dyck-path region. The longest boundary
run has length floor(n/2)+1 and is unique; at an even level its top row attaches
to a new cell below, while at the following odd level it is isolated.
The edge characterization used in the proof is proved equivalent to the
literal maximal four-neighbor component in the statement.
-/

namespace Terrace
open OMA.S_oeis_a380573

lemma tri_succ (k : ℕ) : tri (k+1)=tri k+k+1 := rfl

lemma tri_ge (k : ℕ) : k ≤ tri k := by
  induction k with
  | zero => simp [tri]
  | succ k ih => simp only [tri]; omega

lemma tri_mono {k l : ℕ} (h : k ≤ l) : tri k ≤ tri l := by
  induction l, h using Nat.le_induction with
  | base => rfl
  | succ l hl ih => rw [tri_succ]; omega

lemma lt_count_iff (n k q : ℕ) (hk : 0<k) :
    q<count n k ↔ tri k+k*q ≤ n := by
  by_cases ht : tri k ≤ n
  · simp only [count,if_neg (show k≠0 by omega),if_pos ht,Nat.lt_add_one_iff]
    rw [Nat.le_div_iff_mul_le hk]
    rw [Nat.mul_comm q k]
    omega
  · simp only [count,if_neg (show k≠0 by omega),if_neg ht,not_lt_zero,false_iff]
    omega

lemma count_mono (n : ℕ) {k l : ℕ} (hk : 0<k) (hkl : k ≤ l) :
    count n l ≤ count n k := by
  by_contra h
  have h' : count n k<count n l := by omega
  have hh := (lt_count_iff n l (count n k) (by omega)).mp h'
  have ht := tri_mono hkl
  have hm := Nat.mul_le_mul_right (count n k) hkl
  have hn : tri k+k*count n k ≤ n := by omega
  have hf := (lt_count_iff n k (count n k) hk).mpr hn
  omega

lemma count_strict (n k : ℕ) (hk : 0<k) (hp : 0<count n k) :
    count n (k+1)<count n k := by
  by_cases hz : count n (k+1)=0
  · omega
  · have hq : 0<count n (k+1) := by omega
    have hh := (lt_count_iff n (k+1) (count n (k+1)-1) (by omega)).mp (by omega)
    have he : count n (k+1)-1+1=count n (k+1) := by omega
    apply (lt_count_iff n k (count n (k+1)) hk).mpr
    rw [tri_succ] at hh
    nlinarith

lemma count_one (n : ℕ) : count n 1=n := by
  by_cases hn : n=0
  · subst n; decide
  · simp [count,tri,show 1 ≤ n by omega]

lemma count_two (n : ℕ) (hn : 0<n) : count n 2=(n-1)/2 := by
  by_cases h3 : 3 ≤ n
  · simp only [count, show (2:ℕ)≠0 by decide, if_false, tri, show 0+0+1+1+1=3 by decide,
      if_pos h3]
    omega
  · interval_cases n <;> decide

lemma count_end (n : ℕ) : count n (n+1)=0 := by
  have h : n<tri (n+1) := by have := tri_ge (n+1); omega
  simp [count,show ¬tri (n+1) ≤ n by omega]

lemma shape_symm (r : List ℕ) (x y : ℕ) : InShape r x y ↔ InShape r y x := by
  match r with
  | [] => simp [InShape]
  | [a] => simp [InShape,and_comm]
  | a::b::r =>
    simp only [InShape]
    rw [shape_symm r (x-a) (y-a)]
    tauto
termination_by r.length

lemma shape_bound (r : List ℕ) (x y : ℕ) (h : InShape r x y) : x<r.sum ∧ y<r.sum := by
  match r with
  | [] => simp [InShape] at h
  | [a] => simpa [InShape] using h
  | a::b::r =>
    simp only [InShape] at h
    rcases h with h|h|⟨hx,hy,h⟩
    · simp only [List.sum_cons]; omega
    · simp only [List.sum_cons]; omega
    · have ih := shape_bound r (x-a) (y-a) h
      simp only [List.sum_cons]; omega
termination_by r.length

lemma widths_telescope (n start len : ℕ) (hs : 0<start) :
    ((List.range len).map (fun i => dropWidth n (start+i))).sum +
      count n (start+len) = count n start := by
  induction len with
  | zero => simp
  | succ len ih =>
    simp only [List.range_succ, List.map_append, List.sum_append,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    unfold dropWidth at *
    have hm := count_mono n (show 0<start+len by omega) (show start+len ≤ start+len+1 by omega)
    have he : start+(len+1)=start+len+1 := by omega
    rw [he]
    omega

lemma sum_filter_pos (l : List ℕ) : (l.filter (0<·)).sum=l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : 0<a
    · simp [h,ih]
    · have ha : a=0 := by omega
      simp [ha,ih]

lemma first_width (n : ℕ) (hn : 0<n) : dropWidth n 1=n/2+1 := by
  rw [dropWidth,count_one,count_two n hn]
  omega

lemma half_sum (n : ℕ) : (halfRuns n).sum=n := by
  by_cases hn : n=0
  · subst n; simp [halfRuns]
  · unfold halfRuns
    simp only [if_neg hn,List.sum_cons,sum_filter_pos]
    have h := widths_telescope n 2 (n-1) (by decide)
    rw [show 2+(n-1)=n+1 by omega,count_end] at h
    have ht : ((List.range (n-1)).map (fun i => dropWidth n (i+2))).sum=count n 2 := by
      simpa only [Nat.add_comm,add_zero] using h
    have hm := count_mono n (show 0<1 by decide) (show 1 ≤ 2 by decide)
    rw [count_one] at hm
    rw [dropWidth,count_one]
    change (n-count n 2)+((List.range (n-1)).map (fun i => dropWidth n (i+2))).sum=n
    rw [ht]
    omega

lemma half_nonempty (n : ℕ) (hn : 0<n) : ∃ r,
    halfRuns n=(n/2+1)::r ∧ (∀ a∈r, 0<a ∧ a<n/2+1) := by
  unfold halfRuns
  rw [if_neg (show n≠0 by omega),first_width n hn]
  refine ⟨_,rfl,?_⟩
  intro a ha
  simp only [List.mem_filter,List.mem_map,List.mem_range] at ha
  rcases ha with ⟨⟨i,hi,rfl⟩,hp⟩
  refine ⟨of_decide_eq_true hp,?_⟩
  have hm := count_mono n (show 0<2 by decide) (show 2 ≤ i+2 by omega)
  have hh : dropWidth n (i+2) ≤ count n (i+2) := Nat.sub_le _ _
  rw [count_two n hn] at hm
  omega

lemma half_pos (n : ℕ) : ∀ a∈halfRuns n, 0<a := by
  by_cases hn : n=0
  · subst n; simp [halfRuns]
  · obtain ⟨r,hr,hp⟩ := half_nonempty n (by omega)
    rw [hr]
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · omega
    · exact (hp a ha).1

def TopEdge (r : List ℕ) (x y : ℕ) : Prop :=
  InShape r x y ∧ ¬InShape r x (y+1)

lemma shape_left (a b : ℕ) (r : List ℕ) (x y : ℕ) (hx : x<a) :
    InShape (a::b::r) x y ↔ y<a+b+r.sum := by
  simp only [InShape]
  constructor
  · rintro (h|h|h) <;> omega
  · intro h; exact Or.inl ⟨hx,h⟩

lemma shape_low (a b : ℕ) (r : List ℕ) (x y : ℕ) (hx : a ≤ x) (hy : y<a) :
    InShape (a::b::r) x y ↔ x<a+b+r.sum := by
  simp only [InShape]
  constructor
  · rintro (h|h|h) <;> omega
  · intro h; exact Or.inr (Or.inl ⟨hy,h⟩)

lemma shape_inner (a b : ℕ) (r : List ℕ) (x y : ℕ) (hx : a ≤ x) (hy : a ≤ y) :
    InShape (a::b::r) x y ↔ InShape r (x-a) (y-a) := by
  simp only [InShape]
  constructor
  · rintro (h|h|h)
    · omega
    · omega
    · exact h.2.2
  · intro h; exact Or.inr (Or.inr ⟨hx,hy,h⟩)

lemma shape_zero (r : List ℕ) (x : ℕ) (hp : ∀a∈r,0<a) :
    InShape r x 0 ↔ x<r.sum := by
  match r with
  | [] => simp [InShape]
  | [a] =>
    have ha := hp a (by simp)
    simp [InShape,ha]
  | a::b::r =>
    have ha := hp a (by simp)
    simp only [List.sum_cons]
    by_cases hx : x<a
    · rw [shape_left a b r x 0 hx]; omega
    · rw [shape_low a b r x 0 (by omega) ha]; omega

lemma top_left (a b : ℕ) (r : List ℕ) (x y : ℕ) (hx : x<a) :
    TopEdge (a::b::r) x y ↔ y+1=a+b+r.sum := by
  rw [TopEdge,shape_left a b r x y hx,shape_left a b r x (y+1) hx]
  omega

lemma top_low (a b : ℕ) (r : List ℕ) (x y : ℕ)
    (hp : ∀v∈r,0<v) (hx : a ≤ x) (hy : y<a) :
    TopEdge (a::b::r) x y ↔
      y+1=a ∧ a+r.sum ≤ x ∧ x<a+b+r.sum := by
  by_cases hs : y+1<a
  · rw [TopEdge,shape_low a b r x y hx hy,shape_low a b r x (y+1) hx hs]
    omega
  · have he : y+1=a := by omega
    rw [TopEdge,shape_low a b r x y hx hy,shape_inner a b r x (y+1) hx (by omega)]
    rw [show y+1-a=0 by omega,shape_zero r (x-a) hp]
    omega

lemma top_inner (a b : ℕ) (r : List ℕ) (x y : ℕ) (hx : a ≤ x) (hy : a ≤ y) :
    TopEdge (a::b::r) x y ↔ TopEdge r (x-a) (y-a) := by
  rw [TopEdge,shape_inner a b r x y hx hy,shape_inner a b r x (y+1) hx (by omega)]
  rw [show y+1-a=y-a+1 by omega]
  rfl

lemma top_cases (a b : ℕ) (r : List ℕ) (x y : ℕ) (hp : ∀v∈r,0<v) :
    TopEdge (a::b::r) x y ↔
      (x<a ∧ y+1=a+b+r.sum) ∨
      (y+1=a ∧ a+r.sum ≤ x ∧ x<a+b+r.sum) ∨
      (a ≤ x ∧ a ≤ y ∧ TopEdge r (x-a) (y-a)) := by
  by_cases hx : x<a
  · rw [top_left a b r x y hx]
    constructor
    · intro h; exact Or.inl ⟨hx,h⟩
    · rintro (h|h|h) <;> omega
  · have hx' : a ≤ x := by omega
    by_cases hy : y<a
    · rw [top_low a b r x y hp hx' hy]
      constructor
      · intro h; exact Or.inr (Or.inl h)
      · rintro (h|h|h) <;> omega
    · have hy' : a ≤ y := by omega
      rw [top_inner a b r x y hx' hy']
      constructor
      · intro h; exact Or.inr (Or.inr ⟨hx',hy',h⟩)
      · rintro (h|h|h)
        · omega
        · omega
        · exact h.2.2

lemma shape_down (r : List ℕ) (x y u v : ℕ) (h : InShape r x y)
    (hu : u ≤ x) (hv : v ≤ y) : InShape r u v := by
  match r with
  | [] => exact False.elim h
  | [a] =>
    simp only [InShape] at *
    omega
  | a::b::r =>
    have hb := shape_bound (a::b::r) x y h
    simp only [List.sum_cons] at hb
    by_cases h1 : u<a
    · exact (shape_left a b r u v h1).mpr (by omega)
    · by_cases h2 : v<a
      · exact (shape_low a b r u v (by omega) h2).mpr (by omega)
      · have hx : a ≤ x := by omega
        have hy : a ≤ y := by omega
        apply (shape_inner a b r u v (by omega) (by omega)).mpr
        apply shape_down r (x-a) (y-a) (u-a) (v-a)
        · exact (shape_inner a b r x y hx hy).mp h
        · omega
        · omega
termination_by r.length

lemma shape_toprow (a : ℕ) (r : List ℕ) (x : ℕ) (hp : ∀v∈a::r,0<v) :
    InShape (a::r) x ((a::r).sum-1) ↔ x<a := by
  match r with
  | [] =>
    have ha := hp a (by simp)
    simp [InShape,ha]
  | b::r =>
    have ha := hp a (by simp)
    have hb := hp b (by simp)
    simp only [List.sum_cons]
    by_cases hx : x<a
    · rw [shape_left a b r x (a+(b+r.sum)-1) hx]
      omega
    · rw [shape_inner a b r x (a+(b+r.sum)-1) (by omega) (by omega)]
      constructor
      · intro h
        have hs := shape_bound r (x-a) (a+(b+r.sum)-1-a) h
        omega
      · omega

lemma top_segment_bound (r : List ℕ) (M x y k : ℕ)
    (hp : ∀v∈r,0<v) (hm : ∀v∈r,v ≤ M)
    (hs : ∀i<k,TopEdge r (x+i) y) : k ≤ M := by
  by_cases hk : k=0
  · omega
  · have hk' : 0<k := by omega
    have h0 := hs 0 hk'
    have hl := hs (k-1) (by omega)
    simp only [add_zero] at h0
    match r with
    | [] => exact False.elim h0.1
    | [a] =>
      have ha := hm a (by simp)
      have hx : x+(k-1)<a := hl.1.1
      omega
    | a::b::r =>
      have ha := hm a (by simp)
      have hb := hm b (by simp)
      have hb0 := hp b (by simp)
      have hpr : ∀v∈r,0<v := by intro v hv;exact hp v (by simp [hv])
      have hmr : ∀v∈r,v ≤ M := by intro v hv;exact hm v (by simp [hv])
      rcases (top_cases a b r x y hpr).mp h0 with h|h|h
      · have hy : y=(a::b::r).sum-1 := by simp only [List.sum_cons]; omega
        have hx := (shape_toprow a (b::r) (x+(k-1)) hp).mp (by simpa only [←hy] using hl.1)
        omega
      · have hx := (shape_bound (a::b::r) (x+(k-1)) y hl.1).1
        simp only [List.sum_cons] at hx
        omega
      · have hsi : ∀i<k, TopEdge r ((x-a)+i) (y-a) := by
          intro i hi
          have ht := (top_inner a b r (x+i) y (by omega) h.2.1).mp (hs i hi)
          simpa only [show x+i-a=(x-a)+i by omega] using ht
        exact top_segment_bound r M (x-a) (y-a) k hpr hmr hsi
termination_by r.length

lemma top_segment_unique (a : ℕ) (r : List ℕ) (x y : ℕ)
    (hp : ∀v∈a::r,0<v) (hm : ∀v∈r,v<a)
    (hs : ∀i<a,TopEdge (a::r) (x+i) y) :
    x=0 ∧ y+1=(a::r).sum := by
  have ha := hp a (by simp)
  have h0 := hs 0 ha
  have hl := hs (a-1) (by omega)
  simp only [add_zero] at h0
  match r with
  | [] =>
    have hx : x+(a-1)<a := hl.1.1
    have hy : y+1=a := by
      rcases h0 with ⟨h1,h2⟩
      simp only [InShape] at h1 h2
      omega
    simp only [List.sum_cons,List.sum_nil]
    omega
  | b::r =>
    have hb := hm b (by simp)
    have hb0 := hp b (by simp)
    have hpr : ∀v∈r,0<v := by intro v hv;exact hp v (by simp [hv])
    rcases (top_cases a b r x y hpr).mp h0 with h|h|h
    · have hy : y=(a::b::r).sum-1 := by simp only [List.sum_cons];omega
      have hx := (shape_toprow a (b::r) (x+(a-1)) hp).mp (by simpa only [←hy] using hl.1)
      constructor
      · omega
      · simp only [List.sum_cons];omega
    · have hx := (shape_bound (a::b::r) (x+(a-1)) y hl.1).1
      simp only [List.sum_cons] at hx
      omega
    · have hmr : ∀v∈r,v ≤ a-1 := by intro v hv;have := hm v (by simp [hv]);omega
      have hsi : ∀i<a,TopEdge r ((x-a)+i) (y-a) := by
        intro i hi
        have ht := (top_inner a b r (x+i) y (by omega) h.2.1).mp (hs i hi)
        simpa only [show x+i-a=(x-a)+i by omega] using ht
      have hh := top_segment_bound r (a-1) (x-a) (y-a) a hpr hmr hsi
      omega

def HorizontalPart (P : ℕ → ℕ → Prop) (x y k : ℕ) : Prop :=
  (∀ i : Fin k, P (x+i.val) y) ∧
  (∀ i : Fin k, ¬P (x+i.val) (y+1)) ∧
  (∀ i : Fin k, 0<y → ¬P (x+i.val) (y-1)) ∧
  (0<x → ¬P (x-1) y) ∧ ¬P (x+k) y

def Appears (n k : ℕ) : Prop :=
  (∃ x y, HorizontalPart (Layer n) x y k) ∨
  (∃ x y, HorizontalPart (fun u v => Layer n v u) x y k)

lemma layer_symm (n x y : ℕ) : Layer n x y ↔ Layer n y x := by
  simp only [Layer,shape_symm]

lemma horizontal_top (n x y k : ℕ) (h : HorizontalPart (Layer n) x y k) :
    ∀i<k, TopEdge (halfRuns n) (x+i) y := by
  intro i hi
  have hc := h.1 ⟨i,hi⟩
  refine ⟨hc.1,?_⟩
  intro hu
  apply h.2.1 ⟨i,hi⟩
  refine ⟨hu,?_⟩
  intro hold
  exact hc.2 (shape_down _ _ _ _ _ hold (by omega) (by omega))

lemma part_bound (n x y k : ℕ) (hn : 0<n) (h : HorizontalPart (Layer n) x y k) :
    k ≤ n/2+1 := by
  obtain ⟨r,hr,hless⟩ := half_nonempty n hn
  have hp := half_pos n
  have hm : ∀v∈halfRuns n, v ≤ n/2+1 := by
    rw [hr]
    intro v hv
    rcases List.mem_cons.mp hv with rfl|hv
    · omega
    · have := (hless v hv).2; omega
  exact top_segment_bound (halfRuns n) (n/2+1) x y k hp hm (horizontal_top n x y k h)

lemma part_unique (n x y : ℕ) (hn : 0<n)
    (h : HorizontalPart (Layer n) x y (n/2+1)) :
    x=0 ∧ y+1=n := by
  obtain ⟨r,hr,hless⟩ := half_nonempty n hn
  have hp := half_pos n
  have ht := horizontal_top n x y (n/2+1) h
  rw [hr] at hp ht
  have hu := top_segment_unique (n/2+1) r x y hp (fun v hv => (hless v hv).2) ht
  rw [←hr,half_sum] at hu
  exact hu

lemma first_horizontal (k : ℕ) (hk : 0<k) :
    HorizontalPart (Layer (2*k-1)) 0 (2*k-2) k := by
  by_cases h1 : k=1
  · subst k; unfold HorizontalPart; decide
  · have hk2 : 2 ≤ k := by omega
    have hn : 0<2*k-1 := by omega
    have ho : 0<(2*k-1)-1 := by omega
    obtain ⟨r,hr,hless⟩ := half_nonempty (2*k-1) hn
    obtain ⟨r0,hr0,hless0⟩ := half_nonempty ((2*k-1)-1) ho
    have he : (2*k-1)/2+1=k := by omega
    have he0 : ((2*k-1)-1)/2+1=k := by omega
    rw [he] at hr
    rw [he0] at hr0
    have hp := half_pos (2*k-1)
    have hp0 := half_pos ((2*k-1)-1)
    rw [hr] at hp
    rw [hr0] at hp0
    have hs : (k::r).sum=2*k-1 := by rw [←hr,half_sum]
    have hs0 : (k::r0).sum=(2*k-1)-1 := by rw [←hr0,half_sum]
    unfold HorizontalPart
    refine ⟨?_,?_,?_,by omega,?_⟩
    · intro i
      simp only [zero_add,Layer]
      constructor
      · rw [hr]
        have h := (shape_toprow k r i.val hp).mpr i.isLt
        simpa only [hs,show 2*k-1-1=2*k-2 by omega] using h
      · intro h
        have hb := (shape_bound _ _ _ h).2
        rw [half_sum] at hb
        omega
    · intro i h
      have hb := (shape_bound _ _ _ h.1).2
      rw [half_sum] at hb
      omega
    · intro i hy h
      apply h.2
      rw [hr0]
      have hh := (shape_toprow k r0 i.val hp0).mpr i.isLt
      simpa only [hs0,show ((2*k-1)-1)-1=(2*k-2)-1 by omega,zero_add] using hh
    · intro h
      have hb : InShape (k::r) k ((k::r).sum-1) := by
        simpa only [hr,hs,zero_add,show 2*k-1-1=2*k-2 by omega] using h.1
      have hh := (shape_toprow k r k hp).mp hb
      omega

lemma no_earlier_horizontal (n k x y : ℕ) (hn : 0<n) (hk : 0<k) (he : n<2*k-1) :
    ¬HorizontalPart (Layer n) x y k := by
  intro h
  have hb := part_bound n x y k hn h
  have heven : n=2*k-2 := by omega
  have heq : n/2+1=k := by omega
  have hu := part_unique n x y hn (by simpa only [heq] using h)
  obtain ⟨r0,hr0,hless0⟩ := half_nonempty (n-1) (by omega)
  have hf : (n-1)/2+1=k-1 := by omega
  rw [hf] at hr0
  have hp0 := half_pos (n-1)
  rw [hr0] at hp0
  have hs0 : ((k-1)::r0).sum=n-1 := by rw [←hr0,half_sum]
  have hlast := h.1 ⟨k-1,by omega⟩
  change Layer n (x+(k-1)) y at hlast
  have hlower : Layer n (x+(k-1)) (y-1) := by
    refine ⟨shape_down _ _ _ _ _ hlast.1 (by omega) (by omega),?_⟩
    intro hold
    have hold' : InShape ((k-1)::r0) (k-1) (((k-1)::r0).sum-1) := by
      simpa only [hu.1,zero_add,hr0,hs0,show y-1=n-1-1 by omega] using hold
    have hh := (shape_toprow (k-1) r0 (k-1) hp0).mp hold'
    omega
  exact h.2.2.1 ⟨k-1,by omega⟩ (by omega) hlower

theorem first_appearance (k : ℕ) (hk : 0<k) :
    Appears (2*k-1) k ∧ ∀n,0<n → n<2*k-1 → ¬Appears n k := by
  refine ⟨Or.inl ⟨0,2*k-2,first_horizontal k hk⟩,?_⟩
  intro n hn he h
  rcases h with ⟨x,y,h⟩|⟨x,y,h⟩
  · exact no_earlier_horizontal n k x y hn hk he h
  · have ht : (fun u v => Layer n v u)=Layer n := by
      funext u v
      exact propext (layer_symm n v u)
    rw [ht] at h
    exact no_earlier_horizontal n k x y hn hk he h

lemma horizontal_closed (P : ℕ → ℕ → Prop) (x y k : ℕ)
    (h : HorizontalPart P x y k) (u v u' v' : ℕ)
    (hu : x ≤ u) (hk : u<x+k) (hv : v=y)
    (ha : Adjacent u v u' v') (hp : P u' v') :
    x ≤ u' ∧ u'<x+k ∧ v'=y := by
  subst v
  have hi : u-x<k := by omega
  have he : x+(u-x)=u := by omega
  have hUp : ¬P u (y+1) := by simpa only [he] using h.2.1 ⟨u-x,hi⟩
  have hDown : 0<y → ¬P u (y-1) := by simpa only [he] using h.2.2.1 ⟨u-x,hi⟩
  rcases ha with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · by_cases hb : u'<x+k
    · exact ⟨by omega,hb,hy⟩
    · have heq : u'=x+k := by omega
      exact False.elim (h.2.2.2.2 (by simpa only [heq,hy] using hp))
  · by_cases hb : x ≤ u'
    · exact ⟨hb,by omega,hy⟩
    · have heq : u'=x-1 := by omega
      exact False.elim (h.2.2.2.1 (by omega) (by simpa only [heq,hy] using hp))
  · exact False.elim (hUp (by simpa only [hx,hy] using hp))
  · have heq : v'=y-1 := by omega
    exact False.elim (hDown (by omega) (by simpa only [hx,heq] using hp))

lemma reach_preserves (P : ℕ → ℕ → Prop) (p q : Cell)
    (hp : P p.1 p.2) (h : Reach P p q) : P q.1 q.2 := by
  induction h with
  | refl => exact hp
  | tail h he ih => exact he.2.1

lemma horizontal_reaches (P : ℕ → ℕ → Prop) (x y k : ℕ)
    (h : HorizontalPart P x y k) (i : ℕ) (hi : i<k) :
    Reach P (x,y) (x+i,y) := by
  induction i with
  | zero => exact Relation.ReflTransGen.refl
  | succ i ih =>
    refine Relation.ReflTransGen.tail (ih (by omega)) ?_
    change P (x+i) y ∧ P (x+(i+1)) y ∧ Adjacent (x+i) y (x+(i+1)) y
    exact ⟨h.1 ⟨i,by omega⟩,h.1 ⟨i+1,hi⟩,Or.inl ⟨by omega,rfl⟩⟩

lemma horizontal_component_iff (P : ℕ → ℕ → Prop) (x y k : ℕ) (hk : 0<k) :
    HorizontalPart P x y k ↔ HorizontalComponent P x y k := by
  constructor
  · intro h
    refine ⟨by simpa using h.1 ⟨0,hk⟩,?_⟩
    intro u v
    constructor
    · intro hr
      have hall : ∀q, Reach P (x,y) q → x ≤ q.1 ∧ q.1<x+k ∧ q.2=y := by
        intro q hq
        induction hq with
        | refl => exact ⟨by omega,by omega,rfl⟩
        | @tail q t hqt he ih =>
          exact horizontal_closed P x y k h q.1 q.2 t.1 t.2 ih.1 ih.2.1 ih.2.2 he.2.2 he.2.1
      exact hall (u,v) hr
    · rintro ⟨hu,huk,hv⟩
      subst v
      have hr := horizontal_reaches P x y k h (u-x) (by omega)
      simpa only [show x+(u-x)=u by omega] using hr
  · rintro ⟨hp,hc⟩
    have within : ∀u v,x ≤ u → u<x+k → v=y → P u v := by
      intro u v h1 h2 h3
      exact reach_preserves P (x,y) (u,v) hp ((hc u v).mpr ⟨h1,h2,h3⟩)
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i;exact within (x+i.val) y (by omega) (by omega) rfl
    · intro i hbad
      have hr := (hc (x+i.val) y).mpr ⟨by omega,by omega,rfl⟩
      have he : Edge P (x+i.val,y) (x+i.val,y+1) :=
        ⟨within _ _ (by omega) (by omega) rfl,hbad,Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))⟩
      have ht := (hc (x+i.val) (y+1)).mp (Relation.ReflTransGen.tail hr he)
      omega
    · intro i hy hbad
      have hr := (hc (x+i.val) y).mpr ⟨by omega,by omega,rfl⟩
      have he : Edge P (x+i.val,y) (x+i.val,y-1) :=
        ⟨within _ _ (by omega) (by omega) rfl,hbad,Or.inr (Or.inr (Or.inr ⟨rfl,by omega⟩))⟩
      have ht := (hc (x+i.val) (y-1)).mp (Relation.ReflTransGen.tail hr he)
      omega
    · intro hx hbad
      have he : Edge P (x,y) (x-1,y) :=
        ⟨hp,hbad,Or.inr (Or.inl ⟨by omega,rfl⟩)⟩
      have ht := (hc (x-1) y).mp (Relation.ReflTransGen.tail Relation.ReflTransGen.refl he)
      omega
    · intro hbad
      have hr := (hc (x+(k-1)) y).mpr ⟨by omega,by omega,rfl⟩
      have he : Edge P (x+(k-1),y) (x+k,y) :=
        ⟨within _ _ (by omega) (by omega) rfl,hbad,Or.inl ⟨by omega,rfl⟩⟩
      have ht := (hc (x+k) y).mp (Relation.ReflTransGen.tail hr he)
      omega

lemma component_appears_iff (n k : ℕ) (hk : 0<k) :
    Appears n k ↔ HasStraightTerrace n k := by
  unfold Appears HasStraightTerrace
  simp only [horizontal_component_iff _ _ _ _ hk]

theorem component_first_appearance (k : ℕ) (hk : 0<k) :
    HasStraightTerrace (2*k-1) k ∧ ∀n,0<n → n<2*k-1 → ¬HasStraightTerrace n k := by
  simpa only [←component_appears_iff _ _ hk] using first_appearance k hk

end Terrace

theorem OMA.solution : type_of% @OMA.S_oeis_a380573.main :=
  fun k hk => Terrace.component_first_appearance k hk
