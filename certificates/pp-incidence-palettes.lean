import certificates.«pp-incidence-table-7»
import certificates.«pp-incidence-table-8»

open Finset OMA.S_oeis_a380455 HalfCatalogue
namespace HalfIndex

def exceptionKey : ℕ := 0x380000007c000000f80000007

def capacity (half key : ℕ) : ℕ :=
  if half=7 then 9 else if key=exceptionKey then 12 else 10

def unpack : ℕ → ℕ → List ℕ
  | 0,_ => []
  | k+1,bits => bits%512 :: unpack k (bits >>> 9)

theorem unpack_length (n bits : ℕ) : (unpack n bits).length=n := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih => simp [unpack,ih]

def choices (half key : ℕ) : List ℕ :=
  unpack (capacity half key) (if half=7 then packed7 key else packed8 key)

def offered (half key id : ℕ) : Bool := decide (id∈choices half key)

def palette (half key : ℕ) : Finset Shape :=
  ((choices half key).map (HalfCatalogue.shape half)).toFinset

theorem palette_card (half key : ℕ) : (palette half key).card≤capacity half key := by
  calc
    (palette half key).card ≤ ((choices half key).map (HalfCatalogue.shape half)).length := List.toFinset_card_le _
    _ = capacity half key := by simp [choices,unpack_length]

theorem in_palette {half key id : ℕ} (h : offered half key id=true) :
    HalfCatalogue.shape half id ∈ palette half key := by
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨id,of_decide_eq_true h,rfl⟩

end HalfIndex
