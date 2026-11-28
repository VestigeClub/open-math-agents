import certificates.«pp-incidence-coverage-b»
import certificates.«pp-incidence-palettes»
import certificates.«pp-geometry-join-d»

open OMA.S_oeis_a380455 PrimePolyFactor HalfGeometry HalfCatalogue HalfIndex HalfPrimes
namespace HalfIncidence

def pointCheck (half id : ℕ) (cache : Orientation → ℤ × ℕ) (g : Orientation) (k : ℕ) : Bool :=
  let o := offsetAt k
  let value := fastKey cache g o
  offered half value id && (if half=8 ∧ value=exceptionKey then
    isExceptionalShape (shapeCells half id) g o else true)

def checks (half id : ℕ) (cache : Orientation → ℤ × ℕ) (g : Orientation) (mask : ℕ) : Bool :=
  mask.bitIndices.all (pointCheck half id cache g)

def RowFact (half id : ℕ) (g : Orientation) : Prop := ∀ o : Cell,
  (∃ u∈shape half id, ∃ v∈shape half id, ∃ n∈neighbors u, o=n-turn g v) →
  Disjoint (shape half id) ((shape half id).image (move g o)) →
  offered half (fastKey (views (shape half id)) g o) id=true ∧
  (half=8 → fastKey (views (shape half id)) g o=exceptionKey →
   congruent (joined (shapeCells half id) g o) exceptionShape)

theorem checked_row {half id : ℕ} {cache : Orientation → ℤ × ℕ} {g : Orientation} {mask : ℕ}
    (accurate : ∀ d, cache d=views (shape half id) d)
    (covers : coverage (shapeCells half id) g mask=true)
    (valid : checks half id cache g mask=true) : RowFact half id g := by
  intro o edges apart
  obtain ⟨k,hk,eq⟩:=proposed_captured covers edges apart
  have row:=List.all_eq_true.mp valid k hk
  have fn : cache=views (shape half id) := funext accurate
  rw [fn] at row
  change (offered half (fastKey (views (shape half id)) g (offsetAt k)) id &&
    (if half=8 ∧ fastKey (views (shape half id)) g (offsetAt k)=exceptionKey
     then isExceptionalShape (shapeCells half id) g (offsetAt k) else true))=true at row
  rw [eq] at row
  simp only [Bool.and_eq_true] at row
  refine ⟨row.1,?_⟩
  intro h8 high
  exact exceptional_of_check (by simpa only [if_pos (And.intro h8 high)] using row.2)

end HalfIncidence
