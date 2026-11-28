import certificates.«fifteen-cell-pentomino-upper-bound-candidates»

/-!
# Exhaustive search for pairs of pentomino tilings

A connected board of fifteen cells spans at most twenty-eight units in each
coordinate. A projection of stride thirty-two therefore preserves all its
cells. Each geometric tiling gives a partition by translated bit masks.

Every board with at least four prime factors has two distinct pentomino
factors. Aligning one piece fixes the translation and orientation. Starting
from it, the search chooses a cell covered by just one partial tiling and
checks every piece of the opposite tiling that could cover that cell.
The supplied pivot guides affect the choice of cell. The verifier checks
each pivot, every possible continuation, and each terminal board.
-/

/-! A complete finite search for tilings represented by binary occupancy masks. -/
open Finset
namespace FactorMaskCheck

def cells (word : ℕ) : Finset ℕ := word.bitIndices.toFinset

theorem cell_iff {word i : ℕ} : i ∈ cells word ↔ word.testBit i = true := by
  simp [cells, Nat.mem_bitIndices]

theorem cells_zero : cells 0 = ∅ := by simp [cells]

theorem cells_injective : Function.Injective cells := by
  intro a b eq
  apply Nat.eq_of_testBit_eq
  intro i
  have mem : i∈cells a ↔ i∈cells b := by rw [eq]
  rw [cell_iff,cell_iff] at mem
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem cells_and (a b : ℕ) : cells (a &&& b) = cells a ∩ cells b := by
  ext i
  simp [cell_iff,Nat.testBit_and]

theorem cells_or (a b : ℕ) : cells (a ||| b) = cells a ∪ cells b := by
  ext i
  simp [cell_iff,Nat.testBit_or]

theorem cells_rest (a b : ℕ) (sub : cells b ⊆ cells a) :
    cells (a ^^^ b) = cells a \ cells b := by
  ext i
  have h : i∈cells b → i∈cells a := fun hi => sub hi
  simp only [cell_iff,mem_sdiff,Nat.testBit_xor] at h ⊢
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

structure Template where
  shift : ℕ
  word : ℕ
deriving DecidableEq

def atCell (t : Template) (i : ℕ) : ℕ :=
  if t.shift ≤ i then t.word <<< (i - t.shift) else 0

def piece (model : List Template) (word : ℕ) : Prop :=
  word ≠ 0 ∧ ∀ i ∈ cells word, ∃ t ∈ model, atCell t i = word

def partition (model : List Template) (board : ℕ) (parts : Finset ℕ) : Prop :=
  parts.biUnion cells = cells board ∧
  (∀ p∈parts, piece model p) ∧
  (∀ p∈parts, ∀ q∈parts, p≠q → Disjoint (cells p) (cells q))

def covers (model : List Template) : ℕ → ℕ → Bool
  | 0, b => b == 0
  | k+1, b => if b=0 then true else
      model.any fun t =>
        let c := atCell t b.log2
        c != 0 && ((b &&& c) == c) && covers model k (b ^^^ c)

theorem covers_complete {model : List Template} (k : ℕ) {b : ℕ} {parts : Finset ℕ}
    (h : partition model b parts) (bound : parts.card≤k) : covers model k b = true := by
  induction k generalizing b parts with
  | zero =>
    have empty := card_eq_zero.mp (by omega : parts.card=0)
    have eq := h.1
    rw [empty,biUnion_empty] at eq
    have z : b=0 := cells_injective (eq.symm.trans cells_zero.symm)
    simp [covers,z]
  | succ k ih =>
    by_cases z : b=0
    · simp [covers,z]
    rw [covers,if_neg z,List.any_eq_true]
    obtain ⟨all,types,separate⟩ := h
    have tip : b.log2 ∈ cells b := cell_iff.mpr (Nat.testBit_log2 z)
    rw [←all] at tip
    obtain ⟨p,hp,hit⟩ := mem_biUnion.mp tip
    obtain ⟨nz,loc⟩ := types p hp
    obtain ⟨t,ht,atp⟩ := loc b.log2 hit
    have sub : cells p ⊆ cells b := by
      rw [←all]
      exact fun i hi => mem_biUnion.mpr ⟨p,hp,hi⟩
    have inter : b &&& p = p := cells_injective (by rw [cells_and,inter_eq_right.mpr sub])
    have next : partition model (b ^^^ p) (parts.erase p) := by
      refine ⟨?_,fun q hq => types q (mem_of_mem_erase hq),?_⟩
      · rw [cells_rest _ _ sub,←all]
        ext i
        constructor
        · intro hi
          obtain ⟨q,hq,req⟩ := mem_biUnion.mp hi
          obtain ⟨different,inAll⟩ := mem_erase.mp hq
          exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨q,inAll,req⟩,
            fun inside => disjoint_left.mp (separate q inAll p hp different) req inside⟩
        · intro hi
          obtain ⟨total,outside⟩ := mem_sdiff.mp hi
          obtain ⟨q,hq,iq⟩ := mem_biUnion.mp total
          have ne : q≠p := by rintro rfl; exact outside iq
          exact mem_biUnion.mpr ⟨q,mem_erase.mpr ⟨ne,hq⟩,iq⟩
      · intro q hq r hr ne
        exact separate q (mem_of_mem_erase hq) r (mem_of_mem_erase hr) ne
    have smaller : (parts.erase p).card ≤ k := by rw [card_erase_of_mem hp]; omega
    exact ⟨t,ht,by simp [atp,nz,inter,ih next smaller]⟩

end FactorMaskCheck

open Finset
namespace FactorMaskCheck

structure PairState where
  a : ℕ
  b : ℕ
  na : ℕ
  nb : ℕ

def usable (t : List Template) (i used other n m : ℕ) : List ℕ :=
  t.filterMap fun u =>
    let c := atCell u i
    if c ≠ 0 ∧ (c &&& used)=0 ∧ (n≠2 ∨ (other &&& (used ||| c))=other) ∧
       (m≠3 ∨ (c &&& other)=c) then some c else none

def options (left right : List Template) (s : PairState) (r : Bool × ℕ) : List ℕ :=
  if r.1 then usable right r.2 s.b s.a s.nb s.na else usable left r.2 s.a s.b s.na s.nb

def witnessPivot (s : PairState) (r : Bool × ℕ) : Bool :=
  if r.1 then s.a.testBit r.2 && !s.b.testBit r.2 else s.b.testBit r.2 && !s.a.testBit r.2

def extendState (s : PairState) (r : Bool × ℕ) (c : ℕ) : PairState :=
  if r.1 then ⟨s.a,s.b ||| c,s.na,s.nb+1⟩ else ⟨s.a ||| c,s.b,s.na+1,s.nb⟩

def tile0 : List Template := [⟨0,18446744078004518913⟩,⟨0,7⟩,⟨1,7⟩,⟨2,7⟩,⟨32,18446744078004518913⟩,⟨64,18446744078004518913⟩]

def tile1 : List Template := [⟨0,12884901889⟩,⟨0,4294967299⟩,⟨0,6442450945⟩,⟨0,8589934595⟩,⟨1,4294967299⟩,⟨1,8589934595⟩,⟨31,6442450945⟩,⟨32,12884901889⟩,⟨32,4294967299⟩,⟨32,6442450945⟩,⟨33,12884901889⟩,⟨33,8589934595⟩]

def tile2 : List Template := [⟨0,31⟩,⟨0,340282367000166625996085689103316680705⟩,⟨1,31⟩,⟨128,340282367000166625996085689103316680705⟩,⟨2,31⟩,⟨3,31⟩,⟨32,340282367000166625996085689103316680705⟩,⟨4,31⟩,⟨64,340282367000166625996085689103316680705⟩,⟨96,340282367000166625996085689103316680705⟩]

def tile3 : List Template := [⟨0,118842243789843250468320444417⟩,⟨0,158456325065422163343096938499⟩,⟨0,237684487561239756858636369921⟩,⟨0,34359738383⟩,⟨0,4294967311⟩,⟨0,64424509441⟩,⟨0,79228162532711081671548469251⟩,⟨0,8053063681⟩,⟨1,158456325065422163343096938499⟩,⟨1,34359738383⟩,⟨1,4294967311⟩,⟨1,79228162532711081671548469251⟩,⟨2,34359738383⟩,⟨2,4294967311⟩,⟨29,8053063681⟩,⟨3,34359738383⟩,⟨3,4294967311⟩,⟨30,8053063681⟩,⟨31,8053063681⟩,⟨32,118842243789843250468320444417⟩,⟨32,237684487561239756858636369921⟩,⟨32,4294967311⟩,⟨32,64424509441⟩,⟨32,79228162532711081671548469251⟩,⟨32,8053063681⟩,⟨33,158456325065422163343096938499⟩,⟨33,64424509441⟩,⟨34,64424509441⟩,⟨35,34359738383⟩,⟨35,64424509441⟩,⟨64,118842243789843250468320444417⟩,⟨64,237684487561239756858636369921⟩,⟨64,79228162532711081671548469251⟩,⟨65,158456325065422163343096938499⟩,⟨95,118842243789843250468320444417⟩,⟨96,118842243789843250468320444417⟩,⟨96,237684487561239756858636369921⟩,⟨96,79228162532711081671548469251⟩,⟨97,158456325065422163343096938499⟩,⟨97,237684487561239756858636369921⟩]

def tile4 : List Template := [⟨0,16106127361⟩,⟨0,17179869199⟩,⟨0,32212254721⟩,⟨0,79228162532711081673695952897⟩,⟨0,79228162532711081680138403841⟩,⟨0,79228162541934453708403245057⟩,⟨0,79228162569604569818967572481⟩,⟨0,8589934607⟩,⟨1,17179869199⟩,⟨1,8589934607⟩,⟨2,17179869199⟩,⟨2,8589934607⟩,⟨3,17179869199⟩,⟨3,8589934607⟩,⟨30,16106127361⟩,⟨31,16106127361⟩,⟨31,32212254721⟩,⟨31,79228162532711081673695952897⟩,⟨32,16106127361⟩,⟨32,32212254721⟩,⟨32,79228162532711081673695952897⟩,⟨32,79228162532711081680138403841⟩,⟨32,79228162541934453708403245057⟩,⟨32,79228162569604569818967572481⟩,⟨33,16106127361⟩,⟨33,32212254721⟩,⟨33,79228162532711081680138403841⟩,⟨33,8589934607⟩,⟨34,17179869199⟩,⟨34,32212254721⟩,⟨63,79228162541934453708403245057⟩,⟨64,79228162532711081673695952897⟩,⟨64,79228162532711081680138403841⟩,⟨64,79228162541934453708403245057⟩,⟨64,79228162569604569818967572481⟩,⟨65,79228162569604569818967572481⟩,⟨96,79228162532711081673695952897⟩,⟨96,79228162532711081680138403841⟩,⟨96,79228162541934453708403245057⟩,⟨96,79228162569604569818967572481⟩]

def tile5 : List Template := [⟨0,12884901895⟩,⟨0,15032385539⟩,⟨0,18446744086594453507⟩,⟨0,25769803783⟩,⟨0,27670116117006778369⟩,⟨0,30064771075⟩,⟨0,36893488160304005123⟩,⟨0,55340232234013556737⟩,⟨1,12884901895⟩,⟨1,15032385539⟩,⟨1,18446744086594453507⟩,⟨1,25769803783⟩,⟨1,30064771075⟩,⟨1,36893488160304005123⟩,⟨2,12884901895⟩,⟨2,25769803783⟩,⟨31,15032385539⟩,⟨31,27670116117006778369⟩,⟨32,12884901895⟩,⟨32,15032385539⟩,⟨32,18446744086594453507⟩,⟨32,27670116117006778369⟩,⟨32,30064771075⟩,⟨32,36893488160304005123⟩,⟨32,55340232234013556737⟩,⟨33,12884901895⟩,⟨33,15032385539⟩,⟨33,18446744086594453507⟩,⟨33,25769803783⟩,⟨33,30064771075⟩,⟨33,36893488160304005123⟩,⟨33,55340232234013556737⟩,⟨34,25769803783⟩,⟨34,30064771075⟩,⟨63,27670116117006778369⟩,⟨64,18446744086594453507⟩,⟨64,27670116117006778369⟩,⟨64,55340232234013556737⟩,⟨65,36893488160304005123⟩,⟨65,55340232234013556737⟩]

def tile6 : List Template := [⟨0,21474836487⟩,⟨0,30064771077⟩,⟨0,55340232225423622147⟩,⟨0,55340232229718589443⟩,⟨1,21474836487⟩,⟨1,55340232225423622147⟩,⟨1,55340232229718589443⟩,⟨2,21474836487⟩,⟨2,30064771077⟩,⟨32,21474836487⟩,⟨32,30064771077⟩,⟨32,55340232225423622147⟩,⟨33,30064771077⟩,⟨33,55340232229718589443⟩,⟨34,21474836487⟩,⟨34,30064771077⟩,⟨64,55340232225423622147⟩,⟨64,55340232229718589443⟩,⟨65,55340232225423622147⟩,⟨65,55340232229718589443⟩]

def tile7 : List Template := [⟨0,129127208520261828609⟩,⟨0,18446744078004518919⟩,⟨0,32281802133286682625⟩,⟨0,73786976312018075655⟩,⟨1,18446744078004518919⟩,⟨1,73786976312018075655⟩,⟨2,18446744078004518919⟩,⟨2,73786976312018075655⟩,⟨32,129127208520261828609⟩,⟨32,18446744078004518919⟩,⟨32,32281802133286682625⟩,⟨34,73786976312018075655⟩,⟨62,32281802133286682625⟩,⟨63,32281802133286682625⟩,⟨64,129127208520261828609⟩,⟨64,18446744078004518919⟩,⟨64,32281802133286682625⟩,⟨65,129127208520261828609⟩,⟨66,129127208520261828609⟩,⟨66,73786976312018075655⟩]

def tile8 : List Template := [⟨0,18446744081225744385⟩,⟨0,18446744103774322689⟩,⟨0,36893488156009037831⟩,⟨0,64563604262278397953⟩,⟨1,36893488156009037831⟩,⟨2,36893488156009037831⟩,⟨30,18446744081225744385⟩,⟨31,18446744081225744385⟩,⟨32,18446744081225744385⟩,⟨32,18446744103774322689⟩,⟨32,64563604262278397953⟩,⟨33,18446744103774322689⟩,⟨33,36893488156009037831⟩,⟨34,18446744103774322689⟩,⟨63,64563604262278397953⟩,⟨64,18446744081225744385⟩,⟨64,18446744103774322689⟩,⟨64,64563604262278397953⟩,⟨65,36893488156009037831⟩,⟨65,64563604262278397953⟩]

def tile9 : List Template := [⟨0,158456325065422163347391905793⟩,⟨0,158456325083868907412511522817⟩,⟨0,39614081266355540840069201921⟩,⟨0,39614081284802284911631269889⟩,⟨0,51539607559⟩,⟨0,60129542147⟩,⟨0,6442450951⟩,⟨0,7516192771⟩,⟨1,51539607559⟩,⟨1,60129542147⟩,⟨1,6442450951⟩,⟨1,7516192771⟩,⟨2,51539607559⟩,⟨2,6442450951⟩,⟨30,7516192771⟩,⟨31,39614081266355540840069201921⟩,⟨31,6442450951⟩,⟨31,7516192771⟩,⟨32,158456325065422163347391905793⟩,⟨32,158456325083868907412511522817⟩,⟨32,39614081266355540840069201921⟩,⟨32,39614081284802284911631269889⟩,⟨32,6442450951⟩,⟨32,7516192771⟩,⟨33,158456325065422163347391905793⟩,⟨33,60129542147⟩,⟨34,51539607559⟩,⟨34,60129542147⟩,⟨35,51539607559⟩,⟨35,60129542147⟩,⟨63,39614081266355540840069201921⟩,⟨63,39614081284802284911631269889⟩,⟨64,158456325083868907412511522817⟩,⟨64,39614081284802284911631269889⟩,⟨65,158456325065422163347391905793⟩,⟨65,158456325083868907412511522817⟩,⟨95,39614081266355540840069201921⟩,⟨95,39614081284802284911631269889⟩,⟨97,158456325065422163347391905793⟩,⟨97,158456325083868907412511522817⟩]

def tile10 : List Template := [⟨0,18446744080152002563⟩,⟨0,27670116123449229313⟩,⟨0,36893488162451488769⟩,⟨0,36893488173188907011⟩,⟨0,36893488177483874305⟩,⟨0,55340232227571105793⟩,⟨0,9223372044370968577⟩,⟨0,9223372051887161345⟩,⟨1,18446744080152002563⟩,⟨1,36893488173188907011⟩,⟨30,9223372044370968577⟩,⟨31,18446744080152002563⟩,⟨31,36893488162451488769⟩,⟨31,55340232227571105793⟩,⟨31,9223372044370968577⟩,⟨31,9223372051887161345⟩,⟨32,18446744080152002563⟩,⟨32,27670116123449229313⟩,⟨32,36893488162451488769⟩,⟨32,36893488177483874305⟩,⟨32,55340232227571105793⟩,⟨32,9223372044370968577⟩,⟨32,9223372051887161345⟩,⟨33,27670116123449229313⟩,⟨33,36893488162451488769⟩,⟨33,36893488173188907011⟩,⟨33,36893488177483874305⟩,⟨33,9223372051887161345⟩,⟨34,36893488173188907011⟩,⟨34,36893488177483874305⟩,⟨63,27670116123449229313⟩,⟨63,9223372044370968577⟩,⟨63,9223372051887161345⟩,⟨64,18446744080152002563⟩,⟨64,27670116123449229313⟩,⟨64,55340232227571105793⟩,⟨65,36893488162451488769⟩,⟨65,36893488173188907011⟩,⟨65,36893488177483874305⟩,⟨65,55340232227571105793⟩]

def tile11 : List Template := [⟨0,110680464455142211585⟩,⟨0,13835058061724614657⟩,⟨0,73786976320608010243⟩,⟨0,9223372043297226755⟩,⟨1,73786976320608010243⟩,⟨1,9223372043297226755⟩,⟨31,13835058061724614657⟩,⟨31,9223372043297226755⟩,⟨32,110680464455142211585⟩,⟨32,13835058061724614657⟩,⟨32,9223372043297226755⟩,⟨33,110680464455142211585⟩,⟨33,73786976320608010243⟩,⟨34,73786976320608010243⟩,⟨62,13835058061724614657⟩,⟨63,13835058061724614657⟩,⟨63,9223372043297226755⟩,⟨65,110680464455142211585⟩,⟨66,110680464455142211585⟩,⟨66,73786976320608010243⟩]

def tile12 : List Template := [⟨0,110680464450847244291⟩,⟨0,27670116114859294723⟩,⟨0,4611686025943580673⟩,⟨0,73786976324902977537⟩,⟨1,110680464450847244291⟩,⟨1,27670116114859294723⟩,⟨30,4611686025943580673⟩,⟨31,4611686025943580673⟩,⟨32,27670116114859294723⟩,⟨32,4611686025943580673⟩,⟨32,73786976324902977537⟩,⟨33,110680464450847244291⟩,⟨33,73786976324902977537⟩,⟨34,73786976324902977537⟩,⟨62,4611686025943580673⟩,⟨63,27670116114859294723⟩,⟨64,27670116114859294723⟩,⟨65,110680464450847244291⟩,⟨66,110680464450847244291⟩,⟨66,73786976324902977537⟩]

def tile13 : List Template := [⟨0,18446744088741937153⟩,⟨31,18446744088741937153⟩,⟨32,18446744088741937153⟩,⟨33,18446744088741937153⟩,⟨64,18446744088741937153⟩]

def table : List (ℕ × List Template) := [(5,tile0),(5,tile1),(3,tile2),(3,tile3),(3,tile4),(3,tile5),(3,tile6),(3,tile7),(3,tile8),(3,tile9),(3,tile10),(3,tile11),(3,tile12),(3,tile13)]

def atMostThree (board : ℕ) : Bool :=
  decide ((table.filter (fun m => covers m.2 m.1 board)).length ≤ 3)

end FactorMaskCheck

namespace FactorMaskCheck

def branches (test : ℕ → ℕ → Bool) : List ℕ → ℕ → Bool
  | [],_ => true
  | c::cs,i => test c i && branches test cs (i+1)

theorem branches_member (test : ℕ → ℕ → Bool) (l : List ℕ) (i c : ℕ)
    (h : c∈l) (checked : branches test l i=true) : ∃ j, test c j=true := by
  induction l generalizing i with
  | nil => simp at h
  | cons a tail ih =>
    simp only [branches,Bool.and_eq_true] at checked
    rcases List.mem_cons.mp h with rfl|ht
    · exact ⟨i,checked.1⟩
    · exact ih (i+1) ht checked.2

/-- Each certificate word records a pivot, its side, and the index of its first child.
The verifier tests the decoded pivot and visits every allowable choice. -/
def guidedPair (left right : List Template) (good : ℕ → Bool) (guide : ℕ → ℕ) :
    ℕ → PairState → ℕ → Bool
  | 0,s,_ => if s.a=s.b ∧ s.na=3 ∧ s.nb=3 then good s.a else true
  | k+1,s,i =>
    if s.a=s.b then
      if s.na=3 ∧ s.nb=3 then good s.a else true
    else if (s.na=3 ∧ (s.b &&& s.a)≠s.b) ∨ (s.nb=3 ∧ (s.a &&& s.b)≠s.a) then true
    else
      let packed := guide i
      let r := (packed.testBit 11,packed%2048)
      witnessPivot s r &&
        branches (fun c child => guidedPair left right good guide k (extendState s r c) child)
          (options left right s r) (packed/4096)

theorem guided_induction (left right : List Template) (good : ℕ → Bool) (board : ℕ)
    (valid : PairState → Prop)
    (equal : ∀ s, valid s → s.a=s.b → s.na=3 ∧ s.nb=3 ∧ s.a=board)
    (last : ∀ s, valid s → 6 ≤ s.na+s.nb → s.a=s.b)
    (inside : ∀ s, valid s → (s.na=3 → (s.b &&& s.a)=s.b) ∧ (s.nb=3 → (s.a &&& s.b)=s.a))
    (step : ∀ s r, valid s → witnessPivot s r=true →
      ∃ c∈options left right s r, valid (extendState s r c))
    (guide : ℕ → ℕ) (fuel : ℕ) (s : PairState) (i : ℕ) (h : valid s) (time : 6 ≤ s.na+s.nb+fuel)
    (accepted : guidedPair left right good guide fuel s i=true) : good board=true := by
  induction fuel generalizing s i with
  | zero =>
    have e:=last s h (by omega)
    obtain ⟨ha,hb,done⟩:=equal s h e
    simpa [guidedPair,e,ha,hb,e.symm.trans done] using accepted
  | succ k ih =>
    by_cases e : s.a=s.b
    · obtain ⟨ha,hb,done⟩:=equal s h e
      simpa [guidedPair,e,ha,hb,e.symm.trans done] using accepted
    · have live : ¬((s.na=3 ∧ (s.b &&& s.a)≠s.b) ∨ (s.nb=3 ∧ (s.a &&& s.b)≠s.a)) := by
        rintro (⟨a,b⟩|⟨a,b⟩)
        · exact b ((inside s h).1 a)
        · exact b ((inside s h).2 a)
      let r := ((guide i).testBit 11,guide i%2048)
      simp only [guidedPair,if_neg e,if_neg live,Bool.and_eq_true] at accepted
      obtain ⟨c,hc,next⟩:=step s r h accepted.1
      obtain ⟨j,hj⟩:=branches_member _ _ _ c hc accepted.2
      apply ih _ j next ?_ hj
      unfold extendState
      split <;> simp <;> omega

end FactorMaskCheck

namespace FactorMaskCheck

theorem check_cons {test : ℕ → ℕ → Bool} {cs : List ℕ} {c k : ℕ}
    (here : test c k=true) (later : branches test cs (k+1)=true) :
    branches test (c::cs) k=true := by simp only [branches,here,later,Bool.and_self]

theorem check_node {left right : List Template} {good : ℕ → Bool} {guide : ℕ → ℕ}
    {fuel i word : ℕ} {s : PairState} {r : Bool × ℕ} {children : List ℕ} {start : ℕ}
    (different : s.a≠s.b)
    (live : ¬((s.na=3 ∧ (s.b &&& s.a)≠s.b) ∨ (s.nb=3 ∧ (s.a &&& s.b)≠s.a)))
    (atNode : guide i=word) (which : (word.testBit 11,word%2048)=r) (whereAt : word/4096=start)
    (hit : witnessPivot s r=true) (all : options left right s r=children)
    (verified : branches (fun c child => guidedPair left right good guide fuel (extendState s r c) child)
      children start=true) : guidedPair left right good guide (fuel+1) s i=true := by
  simp only [guidedPair,if_neg different,if_neg live,atNode,which,whereAt,hit,all,verified,Bool.and_self]

end FactorMaskCheck

open Finset
namespace FactorMaskCheck

def groupCells (pieces : Finset ℕ) : Finset ℕ := pieces.biUnion cells

private lemma grows {a b : Finset ℕ} (h : a⊆b) : groupCells a ⊆ groupCells b := by
  intro p hp
  obtain ⟨q,hq,member⟩ := mem_biUnion.mp hp
  exact mem_biUnion.mpr ⟨q,h hq,member⟩

private lemma group_size {pieces : Finset ℕ} {d : ℕ}
    (areas : ∀ t∈pieces, (cells t).card=d)
    (away : ∀ p∈pieces, ∀ q∈pieces, p≠q → Disjoint (cells p) (cells q)) :
    (groupCells pieces).card=pieces.card*d := by
  rw [groupCells,card_biUnion (by intro p hp q hq ne; exact away p hp q hq ne)]
  calc
    _ = ∑ _p∈pieces,d := sum_congr rfl areas
    _ = _ := by simp

private lemma group_sdiff {full chosen : Finset ℕ} (sub : chosen⊆full)
    (away : ∀ p∈full, ∀ q∈full, p≠q → Disjoint (cells p) (cells q)) :
    groupCells (full \ chosen) = groupCells full \ groupCells chosen := by
  ext i
  constructor
  · intro hi
    obtain ⟨p,hp,ip⟩ := mem_biUnion.mp hi
    obtain ⟨pf,ps⟩ := mem_sdiff.mp hp
    refine mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨p,pf,ip⟩,?_⟩
    intro inside
    obtain ⟨q,hq,iq⟩ := mem_biUnion.mp inside
    exact disjoint_left.mp (away p pf q (sub hq) (fun e => ps (e ▸ hq))) ip iq
  · intro hi
    obtain ⟨inside,outside⟩:=mem_sdiff.mp hi
    obtain ⟨p,hp,ip⟩:=mem_biUnion.mp inside
    exact mem_biUnion.mpr ⟨p,mem_sdiff.mpr ⟨hp,fun e => outside (mem_biUnion.mpr ⟨p,e,ip⟩)⟩,ip⟩

private lemma singleton_conflict {A B : Finset ℕ} (disj : Disjoint A B)
    (sa : A.card=1) (sb : B.card=1) (same : groupCells A=groupCells B) : False := by
  obtain ⟨a,rfl⟩ := card_eq_one.mp sa
  obtain ⟨b,rfl⟩ := card_eq_one.mp sb
  have eq : a=b := cells_injective (by simpa [groupCells] using same)
  subst b
  exact disjoint_left.mp disj (mem_singleton_self _) (mem_singleton_self _)

structure FullPair (left right : List Template) (board : ℕ) where
  first : Finset ℕ
  second : Finset ℕ
  leftPartition : partition left board first
  rightPartition : partition right board second
  leftCount : first.card=3
  rightCount : second.card=3
  leftSize : ∀ p∈first, (cells p).card=5
  rightSize : ∀ p∈second, (cells p).card=5
  noCommon : Disjoint first second

variable {left right : List Template} {board : ℕ}

def FullPair.tracks (F : FullPair left right board) (s : PairState) : Prop :=
  ∃ A⊆F.first, ∃ B⊆F.second, A.Nonempty ∧
    groupCells A=cells s.a ∧ groupCells B=cells s.b ∧ A.card=s.na ∧ B.card=s.nb

private lemma FullPair.touch_all (F : FullPair left right board) {A B : Finset ℕ}
    (ap : A⊆F.first) (bp : B⊆F.second) (start : A.Nonempty)
    (same : groupCells A=groupCells B) : A=F.first ∧ B=F.second := by
  have leftArea := group_size (fun t ht => F.leftSize t (ap ht))
    (fun s hs t ht => F.leftPartition.2.2 s (ap hs) t (ap ht))
  have rightArea := group_size (fun t ht => F.rightSize t (bp ht))
    (fun s hs t ht => F.rightPartition.2.2 s (bp hs) t (bp ht))
  rw [same] at leftArea
  have equalArea : A.card=B.card := by omega
  have lower := card_pos.mpr start
  have upper := (card_le_card ap).trans F.leftCount.le
  have crosses : Disjoint A B := disjoint_left.mpr (fun _ ha hb => disjoint_left.mp F.noCommon (ap ha) (bp hb))
  by_cases one : A.card=1
  · exact (singleton_conflict crosses one (by omega) same).elim
  by_cases two : A.card=2
  · have ea := card_sdiff_of_subset ap
    have eb := card_sdiff_of_subset bp
    have a : (F.first \ A).card=1 := by rw [ea,F.leftCount,two]
    have b : (F.second \ B).card=1 := by rw [eb,F.rightCount,←equalArea,two]
    have non : Disjoint (F.first \ A) (F.second \ B) := disjoint_left.mpr fun _ ha hb =>
      disjoint_left.mp F.noCommon (mem_sdiff.mp ha).1 (mem_sdiff.mp hb).1
    have ga : groupCells F.first=cells board := F.leftPartition.1
    have gb : groupCells F.second=cells board := F.rightPartition.1
    have eq : groupCells (F.first \ A)=groupCells (F.second \ B) := by
      rw [group_sdiff ap F.leftPartition.2.2,group_sdiff bp F.rightPartition.2.2,ga,gb,same]
    exact (singleton_conflict non a b eq).elim
  · have a : A.card=3 := by omega
    exact ⟨eq_of_subset_of_card_le ap (by rw [a,F.leftCount]),
      eq_of_subset_of_card_le bp (by rw [←equalArea,a,F.rightCount])⟩

private lemma FullPair.equal_state (F : FullPair left right board) (s : PairState)
    (valid : F.tracks s) (same : s.a=s.b) : s.na=3 ∧ s.nb=3 ∧ s.a=board := by
  obtain ⟨A,ap,B,bp,start,la,lb,na,nb⟩:=valid
  have e := F.touch_all ap bp start (la.trans ((congrArg cells same).trans lb.symm))
  obtain ⟨rfl,rfl⟩:=e
  exact ⟨na.symm.trans F.leftCount,nb.symm.trans F.rightCount,cells_injective (la.symm.trans F.leftPartition.1)⟩

private lemma and_subset {a b : ℕ} (sub : cells a ⊆ cells b) : a &&& b=a :=
  cells_injective (by rw [cells_and,inter_eq_left.mpr sub])

private lemma FullPair.full_side (F : FullPair left right board) (s : PairState)
    (tracker : F.tracks s) :
    (cells s.a ⊆ cells board) ∧ (cells s.b ⊆ cells board) ∧
    (s.na=3 → cells s.a=cells board) ∧ (s.nb=3 → cells s.b=cells board) := by
  obtain ⟨A,ap,B,bp,_,la,lb,na,nb⟩:=tracker
  have ga : groupCells F.first=cells board := F.leftPartition.1
  have gb : groupCells F.second=cells board := F.rightPartition.1
  refine ⟨?_,?_,?_,?_⟩
  · rw [←la,←ga]
    exact grows ap
  · rw [←lb,←gb]
    exact grows bp
  · intro three
    have finished : A=F.first := eq_of_subset_of_card_le ap (by rw [F.leftCount,na,three])
    exact la.symm.trans (finished ▸ ga)
  · intro three
    have finished : B=F.second := eq_of_subset_of_card_le bp (by rw [F.rightCount,nb,three])
    exact lb.symm.trans (finished ▸ gb)


private lemma next_piece {model : List Template} {full chosen : Finset ℕ} {b u v n m i : ℕ}
    (tiling : partition model b full) (size : full.card=3) (sub : chosen⊆full)
    (used : groupCells chosen=cells u) (count : chosen.card=n)
    (other : cells v⊆cells b) (done : m=3 → cells v=cells b)
    (hit : i∈cells v) (miss : i∉cells u) :
    ∃ c ∈ usable model i u v n m, c∈full ∧ c∉chosen ∧
      groupCells (insert c chosen)=cells (u ||| c) := by
  have loc := other hit
  rw [←tiling.1] at loc
  obtain ⟨c,hc,ic⟩ := mem_biUnion.mp loc
  obtain ⟨template,ht,locates⟩ := (tiling.2.1 c hc).2 i ic
  have fresh : c∉chosen := fun h => miss (used ▸ mem_biUnion.mpr ⟨c,h,ic⟩)
  have disj : Disjoint (cells c) (cells u) := by
    rw [←used]
    refine disjoint_left.mpr ?_
    intro x xc old
    obtain ⟨q,hq,iq⟩ := mem_biUnion.mp old
    exact disjoint_left.mp (tiling.2.2 c hc q (sub hq) (fun eq => fresh (eq ▸ hq))) xc iq
  have clean : c &&& u=0 := cells_injective (by rw [cells_and,cells_zero]; exact disjoint_iff_inter_eq_empty.mp disj)
  have grew : groupCells (insert c chosen)=cells (u ||| c) := by
    rw [cells_or,←used]
    simp [groupCells,union_comm]
  have finish : n≠2 ∨ (v &&& (u ||| c))=v := by
    by_cases two : n=2
    · right
      have all : insert c chosen=full := eq_of_subset_of_card_le (insert_subset hc sub)
        (by rw [size,card_insert_of_notMem fresh,count,two])
      apply and_subset
      rw [←grew,all]
      change cells v ⊆ full.biUnion cells
      rw [tiling.1]
      exact other
    · exact Or.inl two
  have within : m≠3 ∨ (c &&& v)=c := by
    by_cases three : m=3
    · right
      apply and_subset
      rw [done three,←tiling.1]
      exact fun j hj => mem_biUnion.mpr ⟨c,hc,hj⟩
    · exact Or.inl three
  have positive := (tiling.2.1 c hc).1
  refine ⟨c,List.mem_filterMap.mpr ⟨template,ht,?_⟩,hc,fresh,grew⟩
  simp [locates,positive,clean,finish,within]

private lemma FullPair.next (F : FullPair left right board) (s : PairState) (r : Bool × ℕ)
    (valid : F.tracks s) (pivot : witnessPivot s r=true) :
    ∃ c∈options left right s r, F.tracks (extendState s r c) := by
  have info := F.full_side s valid
  obtain ⟨A,ap,B,bp,start,la,lb,na,nb⟩:=valid
  obtain ⟨side,i⟩:=r
  cases side with
  | true =>
    have pos : i∈cells s.a ∧ i∉cells s.b := by simpa [witnessPivot,cell_iff] using pivot
    obtain ⟨c,ok,hc,fresh,grew⟩ := next_piece F.rightPartition F.rightCount bp lb nb
      info.1 info.2.2.1 pos.1 pos.2
    refine ⟨c,ok,A,ap,insert c B,insert_subset hc bp,start,la,grew,na,?_⟩
    simp [extendState,card_insert_of_notMem fresh,nb]
  | false =>
    have pos : i∈cells s.b ∧ i∉cells s.a := by simpa [witnessPivot,cell_iff] using pivot
    obtain ⟨c,ok,hc,fresh,grew⟩ := next_piece F.leftPartition F.leftCount ap la na
      info.2.1 info.2.2.2 pos.1 pos.2
    refine ⟨c,ok,insert c A,insert_subset hc ap,B,bp,⟨c,mem_insert_self _ _⟩,grew,lb,?_,nb⟩
    simp [extendState,card_insert_of_notMem fresh,na]

theorem FullPair.guided (F : FullPair left right board) (good : ℕ → Bool)
    (guide : ℕ → ℕ) (fuel : ℕ) (s : PairState) (i : ℕ) (start : F.tracks s) (time : 6 ≤ s.na+s.nb+fuel)
    (certificate : guidedPair left right good guide fuel s i=true) : good board=true := by
  apply guided_induction left right good board F.tracks F.equal_state ?_ ?_ F.next guide fuel s i start time certificate
  · intro state v size
    have facts := F.full_side state v
    obtain ⟨A,ap,B,bp,_,_,_,na,nb⟩:=v
    have x := card_le_card ap
    have y := card_le_card bp
    rw [na,F.leftCount] at x
    rw [nb,F.rightCount] at y
    exact cells_injective ((facts.2.2.1 (by omega)).trans (facts.2.2.2 (by omega)).symm)
  · intro state v
    have facts := F.full_side state v
    constructor
    · intro three
      exact and_subset (by rw [facts.2.2.1 three]; exact facts.2.1)
    · intro three
      exact and_subset (by rw [facts.2.2.2 three]; exact facts.1)


theorem FullPair.anchored (F : FullPair left right board) {a : ℕ} (ha : a∈F.first) :
    F.tracks ⟨a,0,1,0⟩ := by
  refine ⟨{a},singleton_subset_iff.mpr ha,∅,empty_subset _,singleton_nonempty _,?_,?_,?_,?_⟩
  · simp [groupCells]
  · simp [groupCells,cells_zero]
  · simp
  · simp

end FactorMaskCheck

open Finset OMA.S_oeis_a380455
namespace PrimePolyFactor

def inBox (k : ℕ) (p : Cell) : Prop :=
  -(k : ℤ) ≤ p.1 ∧ p.1 ≤ k ∧ -(k : ℤ) ≤ p.2 ∧ p.2 ≤ k

theorem animal_box (k : ℕ) {a : Shape} (ha : a ∈ animals k) :
    ∀ p∈a, inBox k p := by
  induction k generalizing a with
  | zero =>
    have eq : a={(0,0)} := by simpa [animals] using ha
    simp [eq,inBox]
  | succ k ih =>
    obtain ⟨s,hs,rest⟩:=mem_biUnion.mp ha
    obtain ⟨c,hc,rest⟩:=mem_biUnion.mp rest
    obtain ⟨v,hv,rfl⟩:=mem_image.mp rest
    intro p hp
    rcases mem_insert.mp hp with eql | old
    · subst p
      obtain ⟨x,y⟩:=c
      have base:=ih hs (x,y) hc
      have next: v∈neighbors (x,y) := (mem_filter.mp hv).1
      simp only [neighbors,mem_insert,mem_singleton] at next
      rcases next with rfl|rfl|rfl|rfl <;> simp [inBox] at base ⊢ <;> omega
    · have base:=ih hs p old
      simp [inBox] at base ⊢
      omega

def closeCells (a b : Cell) : Prop :=
  -28 ≤ a.1-b.1 ∧ a.1-b.1 ≤ 28 ∧ -28 ≤ a.2-b.2 ∧ a.2-b.2 ≤ 28

theorem close_of_move (g : Orientation) (o a b : Cell)
    (e : closeCells (move g o a) (move g o b)) : closeCells a b := by
  obtain ⟨s,x,y⟩:=g
  cases s <;> cases x <;> cases y <;> simp [closeCells,move,turn,sign] at e ⊢ <;> omega

theorem bounded_span (k : ℕ) (hk : k≤14) {board : Shape} (poly : polyomino board)
    (sz : board.card=k+1) {p q : Cell} (hp : p∈board) (hq : q∈board) : closeCells p q := by
  obtain ⟨a,ha,e⟩:=rooted_model poly k sz
  obtain ⟨g,o,eq⟩:=(congruent_iff _ _).mp e
  have moved (c : Cell) (hc : c∈board) : move g o c∈a := by
    rw [eq]
    exact mem_image_of_mem _ hc
  have p' := @animal_box k a ha (move g o p) (moved p hp)
  have q' := @animal_box k a ha (move g o q) (moved q hq)
  apply close_of_move g o
  simp only [inBox] at p' q'
  simp only [closeCells]
  omega

theorem span_fifteen {board : Shape} (poly : polyomino board) (sz : board.card=15)
    {p q : Cell} (hp : p∈board) (hq : q∈board) : closeCells p q :=
  bounded_span 14 (by decide) poly sz hp hq

def flat (c : Cell) : ℤ := c.1 + 32*c.2
def indexCell (c : Cell) : ℕ := (1024 + flat c).toNat
def boardWord (s : Shape) : ℕ := Finset.equivBitIndices.symm (s.image indexCell)

theorem cells_boardWord (s : Shape) : FactorMaskCheck.cells (boardWord s)=s.image indexCell :=
  Finset.equivBitIndices.apply_symm_apply _

structure SafeBoard (b : Shape) : Prop where
  above : ∀ c∈b, 0 ≤ 1024+flat c
  inject : Set.InjOn indexCell (↑b : Set Cell)

theorem safe_fifteen {b : Shape} (poly : polyomino b) (sz : b.card=15)
    {q : Cell} (hq : q∈b) (xx : 0≤q.1) (yy : 0≤q.2) : SafeBoard b := by
  have above (c : Cell) (hc : c∈b) : 0≤1024+flat c := by
    have span:=span_fifteen poly sz hc hq
    simp only [closeCells] at span
    unfold flat
    omega
  refine ⟨above,?_⟩
  intro a ha c hc equal
  have aa:=above a ha
  have ac:=above c hc
  have span:=span_fifteen poly sz ha hc
  change (1024+flat a).toNat=(1024+flat c).toNat at equal
  have flatEq : 1024+flat a=1024+flat c := by omega
  simp only [closeCells] at span
  unfold flat at flatEq
  apply Prod.ext <;> omega

theorem index_image_injective {b : Shape} (safe : SafeBoard b) {s t : Shape}
    (hs : s⊆b) (ht : t⊆b) (eq : boardWord s=boardWord t) : s=t := by
  have im := congrArg FactorMaskCheck.cells eq
  rw [cells_boardWord,cells_boardWord] at im
  ext c
  constructor
  · intro hc
    obtain ⟨d,hd,same⟩ := mem_image.mp (im ▸ mem_image_of_mem indexCell hc)
    exact safe.inject (ht hd) (hs hc) same ▸ hd
  · intro hc
    obtain ⟨d,hd,same⟩ := mem_image.mp (im.symm ▸ mem_image_of_mem indexCell hc)
    exact safe.inject (hs hd) (ht hc) same ▸ hd

theorem cells_word_card {b s : Shape} (safe : SafeBoard b) (sub : s⊆b) :
    (FactorMaskCheck.cells (boardWord s)).card=s.card := by
  rw [cells_boardWord]
  exact Finset.card_image_iff.mpr (fun _ ha _ hb eq => safe.inject (sub ha) (sub hb) eq)

theorem poly_motion {b c : Shape} (h : polyomino b) (geo : congruent b c) : polyomino c := by
  obtain ⟨g,o,rfl⟩:=(congruent_iff _ _).mp geo
  let f : b → b.image (move g o) := fun v => ⟨move g o v,mem_image_of_mem _ v.property⟩
  refine ⟨h.1.image _,?_⟩
  rintro ⟨p,hp⟩ ⟨q,hq⟩
  obtain ⟨a,ha,rfl⟩:=mem_image.mp hp
  obtain ⟨v,hv,rfl⟩:=mem_image.mp hq
  let a' : b := ⟨a,ha⟩
  let v' : b := ⟨v,hv⟩
  change Relation.ReflTransGen (fun x y : b.image (move g o) => adjacent x.val y.val) (f a') (f v')
  have carry (t : b) (path : Relation.ReflTransGen (fun x y : b => adjacent x.val y.val) a' t) :
      Relation.ReflTransGen (fun x y : b.image (move g o) => adjacent x.val y.val) (f a') (f t) := by
    induction path with
    | refl => exact .refl
    | @tail x y prev step ih =>
      apply ih.tail
      change adjacent (move g o x.val) (move g o y.val)
      obtain ⟨s,i,j⟩:=g
      cases s <;> cases i <;> cases j <;> simp [adjacent,move,turn,sign] at step ⊢ <;> omega
  exact carry v' (h.2 a' v')

end PrimePolyFactor

open Finset OMA.S_oeis_a380455 FactorMaskCheck
namespace PrimePolyFactor

theorem shifted_cells (w k : ℕ) : cells (w <<< k)=(cells w).image (·+k) := by
  simp only [cells,Nat.shiftLeft_eq,Nat.mul_comm w,Nat.bitIndices_two_pow_mul]
  ext i
  simp

def delta (g : Orientation) (z c : Cell) : ℕ :=
  (flat (turn g c)-flat (turn g z)).toNat

def relativeCells (m : List Cell) (g : Orientation) (z : Cell) : Finset ℕ :=
  m.toFinset.image (delta g z)

def correctCodes (m : List Cell) (ts : List Template) : Bool :=
  directions.all fun g => m.all fun p => m.any fun z =>
    (m.all fun q => decide (flat (turn g z)≤flat (turn g q))) &&
    ts.any fun t => decide (t.shift=delta g z p ∧ cells t.word=relativeCells m g z)

theorem flat_move (o : Cell) (g : Orientation) (q : Cell) :
    flat (move g o q)=flat o+flat (turn g q) := by
  simp [flat,move]
  ring

theorem relative_index (b : Shape) (safe : SafeBoard b) {o q z : Cell} {g : Orientation}
    (start : move g o z∈b) (later : flat (turn g z)≤flat (turn g q)) :
    indexCell (move g o q)=delta g z q+indexCell (move g o z) := by
  have nonneg := safe.above _ start
  simp only [indexCell,delta,flat_move] at *
  omega

theorem physical_piece {b : Shape} (safe : SafeBoard b) {m : List Cell} {ts : List Template}
    (cert : correctCodes m ts=true) {s : Shape} (ne : s.Nonempty) (sub : s⊆b)
    (geo : congruent m.toFinset s) : piece ts (boardWord s) := by
  obtain ⟨g,o,rfl⟩:=(congruent_iff _ _).mp geo
  refine ⟨?_,?_⟩
  · intro zero
    have eq:=congrArg cells zero
    rw [cells_boardWord,cells_zero] at eq
    have present:=ne.image indexCell
    exact present.ne_empty eq
  · intro i hit
    rw [cells_boardWord] at hit
    obtain ⟨v,hv,rfl⟩:=mem_image.mp hit
    obtain ⟨p,hp,rfl⟩:=mem_image.mp hv
    have complete:=List.all_eq_true.mp cert g (direction_mem g)
    have row:=List.all_eq_true.mp complete p (List.mem_toFinset.mp hp)
    obtain ⟨z,hz,ok⟩:=List.any_eq_true.mp row
    simp only [Bool.and_eq_true] at ok
    obtain ⟨least,templates⟩:=ok
    obtain ⟨t,ht,chosen⟩:=List.any_eq_true.mp templates
    have low (q : Cell) (hq : q∈m.toFinset) : flat (turn g z)≤flat (turn g q) :=
      of_decide_eq_true (List.all_eq_true.mp least q (List.mem_toFinset.mp hq))
    have ht' : t.shift=delta g z p ∧ cells t.word=relativeCells m g z := of_decide_eq_true chosen
    have phys:=sub (mem_image_of_mem (move g o) (List.mem_toFinset.mpr hz))
    have mapped (q : Cell) (hq : q∈m.toFinset) := relative_index b safe phys (low q hq)
    have here:=mapped p hp
    have fits : t.shift ≤ indexCell (move g o p) := by rw [ht'.1,here]; omega
    have base : indexCell (move g o p)-t.shift=indexCell (move g o z) := by rw [ht'.1,here]; omega
    refine ⟨t,ht,cells_injective ?_⟩
    rw [atCell,if_pos fits,base,shifted_cells,ht'.2,cells_boardWord,relativeCells]
    ext j
    constructor
    · intro hj
      obtain ⟨j',hj',rfl⟩:=mem_image.mp hj
      obtain ⟨q,hq,rfl⟩:=mem_image.mp hj'
      exact mem_image.mpr ⟨move g o q,mem_image_of_mem _ hq,mapped q hq⟩
    · intro hj
      obtain ⟨v,hv,rfl⟩:=mem_image.mp hj
      obtain ⟨q,hq,rfl⟩:=mem_image.mp hv
      exact mem_image.mpr ⟨delta g z q,mem_image_of_mem _ hq,(mapped q hq).symm⟩

end PrimePolyFactor

open Finset OMA.S_oeis_a380455 FactorMaskCheck
namespace PrimePolyFactor

structure RealTiling (f b : Shape) where
  parts : Finset Shape
  cover : parts.biUnion id=b
  same : ∀ p∈parts, congruent f p
  separate : ∀ p∈parts, ∀ q∈parts, p≠q → Disjoint p q

theorem existsRealTiling {f b : Shape} (tiling : tiles f b) : Nonempty (RealTiling f b) := by
  obtain ⟨parts,_,cov,cong,dis⟩:=tiling
  exact ⟨⟨parts,cov,cong,dis⟩⟩

theorem RealTiling.sub {f b : Shape} (t : RealTiling f b) {p : Shape}
    (hp : p∈t.parts) : p⊆b := by
  intro c hc
  rw [←t.cover]
  exact mem_biUnion.mpr ⟨p,hp,hc⟩

theorem RealTiling.area {f b : Shape} (t : RealTiling f b) :
    b.card=t.parts.card*f.card := by
  calc
    b.card = (t.parts.biUnion id).card := congrArg Finset.card t.cover.symm
    _ = ∑ p∈t.parts,p.card := card_biUnion (by intro p hp q hq ne; exact t.separate p hp q hq ne)
    _ = ∑ _p∈t.parts,f.card := sum_congr rfl fun p hp => (motion_card (t.same p hp)).symm
    _ = _ := by simp

def RealTiling.moveBy {f b : Shape} (t : RealTiling f b) (g : Orientation) (o : Cell) :
    RealTiling f (b.image (move g o)) := by
  let shift := fun p : Shape => p.image (move g o)
  refine ⟨t.parts.image shift,?_,?_,?_⟩
  · ext c
    constructor
    · intro hc
      obtain ⟨s,hs,inside⟩:=mem_biUnion.mp hc
      obtain ⟨p,hp,rfl⟩:=mem_image.mp hs
      obtain ⟨v,hv,rfl⟩:=mem_image.mp inside
      exact mem_image_of_mem _ (t.sub hp hv)
    · intro hc
      obtain ⟨v,hv,rfl⟩:=mem_image.mp hc
      rw [←t.cover] at hv
      obtain ⟨p,hp,inside⟩:=mem_biUnion.mp hv
      exact mem_biUnion.mpr ⟨shift p,mem_image_of_mem _ hp,mem_image_of_mem _ inside⟩
  · intro s hs
    obtain ⟨p,hp,rfl⟩:=mem_image.mp hs
    exact motion_trans (t.same p hp) ((congruent_iff _ _).mpr ⟨g,o,rfl⟩)
  · intro s hs u hu ne
    obtain ⟨p,hp,rfl⟩:=mem_image.mp hs
    obtain ⟨q,hq,rfl⟩:=mem_image.mp hu
    refine disjoint_left.mpr ?_
    intro c a b'
    obtain ⟨v,hv,rfl⟩:=mem_image.mp a
    obtain ⟨v',hv',e⟩:=mem_image.mp b'
    exact disjoint_left.mp (t.separate p hp q hq (fun e => ne (congrArg shift e))) hv
      (move_injective g o e ▸ hv')

theorem RealTiling.moved_piece {f b : Shape} (t : RealTiling f b) {p : Shape}
    (hp : p∈t.parts) (g : Orientation) (o : Cell) :
    p.image (move g o)∈(t.moveBy g o).parts := mem_image_of_mem _ hp

theorem RealTiling.word_count {f b : Shape} (t : RealTiling f b) (safe : SafeBoard b) :
    (t.parts.image boardWord).card=t.parts.card :=
  card_image_iff.mpr (fun _ ha _ hc eq => index_image_injective safe (t.sub ha) (t.sub hc) eq)

theorem RealTiling.word_size {f b : Shape} (t : RealTiling f b) (safe : SafeBoard b)
    {v : ℕ} (hv : v∈t.parts.image boardWord) : (cells v).card=f.card := by
  obtain ⟨p,hp,rfl⟩:=mem_image.mp hv
  exact (cells_word_card safe (t.sub hp)).trans (motion_card (t.same p hp)).symm

theorem RealTiling.maskPartition {f b : Shape} (t : RealTiling f b) (safe : SafeBoard b)
    {m : List Cell} {ts : List Template} (type : congruent m.toFinset f)
    (cert : correctCodes m ts=true) (pos : 0<f.card) :
    partition ts (boardWord b) (t.parts.image boardWord) := by
  refine ⟨?_,?_,?_⟩
  · rw [cells_boardWord]
    ext i
    constructor
    · intro h
      obtain ⟨v,hv,inside⟩:=mem_biUnion.mp h
      obtain ⟨p,hp,rfl⟩:=mem_image.mp hv
      rw [cells_boardWord] at inside
      obtain ⟨c,hc,rfl⟩:=mem_image.mp inside
      exact mem_image_of_mem _ (t.sub hp hc)
    · intro h
      obtain ⟨c,hc,rfl⟩:=mem_image.mp h
      rw [← t.cover] at hc
      obtain ⟨p,hp,cell⟩:=mem_biUnion.mp hc
      refine mem_biUnion.mpr ⟨boardWord p,mem_image_of_mem _ hp,?_⟩
      rw [cells_boardWord]
      exact mem_image_of_mem _ cell
  · intro v hv
    obtain ⟨p,hp,rfl⟩:=mem_image.mp hv
    have size := motion_card (t.same p hp)
    exact physical_piece safe cert (card_pos.mp (by omega)) (t.sub hp) (motion_trans type (t.same p hp))
  · intro v hv u hu ne
    obtain ⟨p,hp,rfl⟩:=mem_image.mp hv
    obtain ⟨q,hq,rfl⟩:=mem_image.mp hu
    rw [cells_boardWord,cells_boardWord]
    refine disjoint_left.mpr ?_
    intro i ip iq
    obtain ⟨c,hc,rfl⟩:=mem_image.mp ip
    obtain ⟨e,he,eq⟩:=mem_image.mp iq
    exact disjoint_left.mp (t.separate p hp q hq (fun h => ne (congrArg boardWord h))) hc
      (safe.inject (t.sub hq he) (t.sub hp hc) eq ▸ he)

theorem physical_no_common {f g b : Shape} (a : RealTiling f b) (c : RealTiling g b)
    (safe : SafeBoard b) (diff : ¬congruent f g) :
    Disjoint (a.parts.image boardWord) (c.parts.image boardWord) := by
  refine disjoint_left.mpr ?_
  intro u hu hv
  obtain ⟨p,hp,rfl⟩:=mem_image.mp hu
  obtain ⟨q,hq,e⟩:=mem_image.mp hv
  have same:=index_image_injective safe (c.sub hq) (a.sub hp) e
  exact diff (motion_trans (a.same p hp) (motion_symm (same ▸ c.same q hq)))

end PrimePolyFactor

open Finset OMA.S_oeis_a380455 FactorMaskCheck
namespace PrimePolyFactor

structure TileEntry where
  id : ℕ
  picture : List Cell
  code : List Template
  limit : ℕ
deriving DecidableEq

def TileEntry.shape (e : TileEntry) : Shape := e.picture.toFinset

def entries : List TileEntry := [
  ⟨0,[(0,0),(0,1),(0,2)],tile0,5⟩,
  ⟨1,[(0,0),(0,1),(1,0)],tile1,5⟩,
  ⟨2,[(0,0),(0,1),(0,2),(0,3),(0,4)],tile2,3⟩,
  ⟨3,[(0,0),(0,1),(0,2),(0,3),(1,0)],tile3,3⟩,
  ⟨4,[(0,0),(0,1),(0,2),(0,3),(1,1)],tile4,3⟩,
  ⟨5,[(0,0),(0,1),(0,2),(1,0),(1,1)],tile5,3⟩,
  ⟨6,[(0,0),(0,1),(0,2),(1,0),(1,2)],tile6,3⟩,
  ⟨7,[(0,0),(0,1),(0,2),(1,0),(2,0)],tile7,3⟩,
  ⟨8,[(0,0),(0,1),(0,2),(1,1),(2,1)],tile8,3⟩,
  ⟨9,[(0,0),(0,1),(0,2),(1,2),(1,3)],tile9,3⟩,
  ⟨10,[(0,0),(0,1),(1,1),(1,2),(2,1)],tile10,3⟩,
  ⟨11,[(0,0),(0,1),(1,1),(1,2),(2,2)],tile11,3⟩,
  ⟨12,[(0,0),(0,1),(1,1),(2,1),(2,2)],tile12,3⟩,
  ⟨13,[(0,1),(1,0),(1,1),(1,2),(2,1)],tile13,3⟩]

def TileEntry.key (e : TileEntry) := (e.limit,e.code)
def TileEntry.passes (w : ℕ) (e : TileEntry) : Bool := covers e.code e.limit w

theorem entries_table : entries.map TileEntry.key=table := rfl

private theorem count_filtered (p : (ℕ × List Template) → Bool) (l : List TileEntry) :
    ((l.map TileEntry.key).filter p).length=(l.filter (fun e => p e.key)).length := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    cases test : p e.key <;> simp [test,ih]

def admissibleShapes (w : ℕ) : Finset Shape :=
  ((entries.filter (TileEntry.passes w)).map TileEntry.shape).toFinset

theorem admissible_card {w : ℕ} (checked : atMostThree w=true) : (admissibleShapes w).card≤3 := by
  have lim : (table.filter (fun m => covers m.2 m.1 w)).length≤3 := of_decide_eq_true checked
  rw [←entries_table,count_filtered] at lim
  have bound := List.toFinset_card_le ((entries.filter (TileEntry.passes w)).map TileEntry.shape)
  rw [List.length_map] at bound
  exact bound.trans lim

def originShift : Orientation := ⟨false,false,false⟩
def matched (s : Shape) (e : TileEntry) : Bool :=
  decide (s=e.shape ∨ s.image (move originShift (0,1))=e.shape)

theorem matched_geo {s : Shape} {e : TileEntry} (yes : matched s e=true) : congruent s e.shape := by
  rcases (of_decide_eq_true yes : s=e.shape ∨ s.image (move originShift (0,1))=e.shape) with eq|eq
  · exact eq ▸ self_congruent s
  · exact (congruent_iff _ _).mpr ⟨originShift,(0,1),eq.symm⟩

set_option maxRecDepth 20000 in
theorem model_entries : ∀ r∈level2 ∪ level4, entries.any (matched r)=true := by decide +kernel

theorem entry_for {f : Shape} (poly : polyomino f) (area : f.card=3 ∨ f.card=5) :
    ∃ e∈entries, congruent f e.shape := by
  have model : ∃ r∈level2 ∪ level4, congruent f r := by
    rcases area with h|h
    · obtain ⟨r,hr,rel⟩:=representative poly 2 (by decide) h
      exact ⟨r,mem_union_left _ hr,rel⟩
    · obtain ⟨r,hr,rel⟩:=representative poly 4 (by decide) h
      exact ⟨r,mem_union_right _ hr,rel⟩
  obtain ⟨r,hr,rel⟩:=model
  obtain ⟨e,he,h⟩:=List.any_eq_true.mp (model_entries r hr)
  exact ⟨e,he,motion_trans rel (matched_geo h)⟩

def measured (e : TileEntry) : Bool :=
  decide (e.limit*e.shape.card=15 ∧ 0<e.shape.card ∧
    (e.shape.card=5 ↔ 2≤e.id) ∧ e.id<14 ∧ ∃ c∈e.shape, 0≤c.1 ∧ 0≤c.2)

theorem entry_measures {e : TileEntry} (he : e∈entries) :
    e.limit*e.shape.card=15 ∧ 0<e.shape.card ∧
    (e.shape.card=5 ↔ 2≤e.id) ∧ e.id<14 ∧ ∃ c∈e.shape, 0≤c.1 ∧ 0≤c.2 := by
  have all : entries.all measured=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all e he)

theorem same_id {e f : TileEntry} (he : e∈entries) (hf : f∈entries) (same : e.id=f.id) : e=f := by
  have all : entries.all (fun e => entries.all (fun f => decide (e.id=f.id → e=f)))=true := by decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all e he) f hf) : e.id=f.id → e=f) same

set_option maxRecDepth 16000 in
private theorem layout0 : correctCodes entries[0].picture entries[0].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout1 : correctCodes entries[1].picture entries[1].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout2 : correctCodes entries[2].picture entries[2].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout3 : correctCodes entries[3].picture entries[3].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout4 : correctCodes entries[4].picture entries[4].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout5 : correctCodes entries[5].picture entries[5].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout6 : correctCodes entries[6].picture entries[6].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout7 : correctCodes entries[7].picture entries[7].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout8 : correctCodes entries[8].picture entries[8].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout9 : correctCodes entries[9].picture entries[9].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout10 : correctCodes entries[10].picture entries[10].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout11 : correctCodes entries[11].picture entries[11].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout12 : correctCodes entries[12].picture entries[12].code=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem layout13 : correctCodes entries[13].picture entries[13].code=true := by decide +kernel

theorem entry_codes {e : TileEntry} (he : e∈entries) : correctCodes e.picture e.code=true := by
  simp only [entries,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact layout0
  · exact layout1
  · exact layout2
  · exact layout3
  · exact layout4
  · exact layout5
  · exact layout6
  · exact layout7
  · exact layout8
  · exact layout9
  · exact layout10
  · exact layout11
  · exact layout12
  · exact layout13

end PrimePolyFactor

open Finset OMA.S_oeis_a380455 FactorMaskCheck
namespace PrimePolyFactor

def completePairs : Prop := ∀ e∈entries, ∀ d∈entries,
  e.shape.card=5 → d.shape.card=5 → e.id<d.id →
  ∃ guide : ℕ → ℕ, guidedPair e.code d.code atMostThree guide 5 ⟨boardWord e.shape,0,1,0⟩ 0=true

theorem detectsEntry {b f : Shape} {e : TileEntry} (he : e∈entries) (safe : SafeBoard b)
    (fifteen : b.card=15) (geom : congruent f e.shape) (tiling : tiles f b) :
    e.passes (boardWord b)=true := by
  obtain ⟨t⟩:=existsRealTiling tiling
  have m:=entry_measures he
  have sz:=motion_card geom
  have pos : 0<f.card := by omega
  have h : t.parts.card * f.card=e.limit * f.card := by
    rw [←t.area,fifteen,sz,m.1]
  have number : t.parts.card=e.limit := Nat.eq_of_mul_eq_mul_right pos h
  apply covers_complete _ (t.maskPartition safe (motion_symm geom) (entry_codes he) pos)
  rw [t.word_count safe,number]

theorem counterexample_areas {b : Shape} {fs : Finset Shape} (size : b.card=15) (tooMany : 4≤fs.card)
    (factors : ∀ f∈fs, primeShape f ∧ tiles f b)
    (distinct : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q) {f : Shape} (hf : f∈fs) :
    f.card=3 ∨ f.card=5 := by
  have divisor := tile_area (factors f hf).2
  rw [size] at divisor
  have few:=Nat.le_of_dvd (by decide : 0<15) divisor
  have pos:1<f.card := (factors f hf).1.2.1
  have ne : f.card≠15 := fun eq =>
    (by omega : ¬fs.card≤1) (bounds_when_whole factors distinct ⟨f,hf,eq.trans size.symm⟩)
  generalize e : f.card=n at *
  interval_cases n <;> omega

theorem after_alignment (checks : completePairs) {b p q : Shape}
    (poly : polyomino b) (size : b.card=15) (areaP : p.card=5) (areaQ : q.card=5)
    (unequal : ¬congruent p q) (tilesP : tiles p b) (tilesQ : tiles q b)
    {e d : TileEntry} (he : e∈entries) (hd : d∈entries)
    (pModel : congruent p e.shape) (qModel : congruent q d.shape) (order : e.id<d.id) :
    ∃ c, congruent b c ∧ SafeBoard c ∧ atMostThree (boardWord c)=true := by
  obtain ⟨P⟩:=existsRealTiling tilesP
  obtain ⟨Q⟩:=existsRealTiling tilesQ
  have count0:=P.area
  rw [size,areaP] at count0
  obtain ⟨part,member⟩:=card_pos.mp (by omega : 0<P.parts.card)
  obtain ⟨g,o,align⟩:=(congruent_iff part e.shape).mp (motion_trans (motion_symm (P.same part member)) pModel)
  let c := b.image (move g o)
  have moved : congruent b c := (congruent_iff _ _).mpr ⟨g,o,rfl⟩
  have csz : c.card=15 := (motion_card moved).symm.trans size
  let L := P.moveBy g o
  let R := Q.moveBy g o
  have firstTile : e.shape∈L.parts := by
    rw [align]
    exact P.moved_piece member g o
  obtain ⟨v,hv,xx,yy⟩:=(entry_measures he).2.2.2.2
  have safe := safe_fifteen (poly_motion poly moved) csz (L.sub firstTile hv) xx yy
  have left := L.maskPartition safe (motion_symm pModel) (entry_codes he) (by omega)
  have right := R.maskPartition safe (motion_symm qModel) (entry_codes hd) (by omega)
  let F : FullPair e.code d.code (boardWord c) :=
    { first := L.parts.image boardWord
      second := R.parts.image boardWord
      leftPartition := left
      rightPartition := right
      leftCount := by
        rw [L.word_count safe]
        have num:=L.area
        change c.card=L.parts.card*p.card at num
        rw [csz,areaP] at num
        omega
      rightCount := by
        rw [R.word_count safe]
        have num:=R.area
        change c.card=R.parts.card*q.card at num
        rw [csz,areaQ] at num
        omega
      leftSize := fun _ h => (L.word_size safe h).trans areaP
      rightSize := fun _ h => (R.word_size safe h).trans areaQ
      noCommon := physical_no_common L R safe unequal }
  have start : boardWord e.shape∈F.first := mem_image_of_mem _ firstTile
  obtain ⟨guide,proof⟩:=checks e he d hd ((motion_card pModel).symm.trans areaP)
    ((motion_card qModel).symm.trans areaQ) order
  refine ⟨c,moved,safe,?_⟩
  exact F.guided atMostThree guide 5 _ 0 (F.anchored start) (show 6 ≤ 1+0+5 by decide) proof

theorem fifteen_upper_of_pair_checks (checks : completePairs) {b : Shape} {fs : Finset Shape}
    (poly : polyomino b) (size : b.card=15)
    (factors : ∀ f∈fs, primeShape f ∧ tiles f b)
    (distinct : ∀ p∈fs, ∀ q∈fs, congruent p q → p=q) : fs.card≤3 := by
  by_contra! large
  obtain ⟨p,hp,q,hq,areaP,areaQ,unequal⟩:=two_pentominoes_of_four size large factors distinct
  obtain ⟨e,he,relP⟩:=entry_for (factors p hp).1.1 (Or.inr areaP)
  obtain ⟨d,hd,relQ⟩:=entry_for (factors q hq).1.1 (Or.inr areaQ)
  obtain ⟨c,moved,safe,ok⟩ : ∃ c, congruent b c ∧ SafeBoard c ∧ atMostThree (boardWord c)=true := by
    rcases lt_trichotomy e.id d.id with ord|eq|ord
    · exact after_alignment checks poly size areaP areaQ unequal (factors p hp).2 (factors q hq).2 he hd relP relQ ord
    · have same:=same_id he hd eq
      exact (unequal (motion_trans relP (motion_symm (same ▸ relQ)))).elim
    · exact after_alignment checks poly size areaQ areaP (fun h => unequal (motion_symm h)) (factors q hq).2
        (factors p hp).2 hd he relQ relP ord
  have bound : fs.card≤(admissibleShapes (boardWord c)).card := by
    apply represented_card distinct
    intro f hf
    obtain ⟨r,hr,geo⟩:=entry_for (factors f hf).1.1 (counterexample_areas size large factors distinct hf)
    have ok := detectsEntry hr safe ((motion_card moved).symm.trans size) geo (transport_tiles (factors f hf).2 moved)
    exact ⟨r.shape,List.mem_toFinset.mpr (List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨hr,ok⟩,rfl⟩),geo⟩
  have small:=bound.trans (admissible_card ok)
  omega

end PrimePolyFactor

open Finset OMA.S_oeis_a380455 FactorMaskCheck
namespace PrimePolyFactor

def tileAt (i : Fin 14) : TileEntry := entries[i.val]'(show i.val<14 from i.isLt)

theorem entry_is_index {e : TileEntry} (he : e∈entries) : ∃ i : Fin 14, tileAt i=e := by
  obtain ⟨n,hn,hm⟩:=List.mem_iff_getElem.mp he
  exact ⟨⟨n,hn⟩,hm⟩

theorem id_at (i : Fin 14) : (tileAt i).id=i.val := by fin_cases i <;> rfl

def pairAt (i j : Fin 14) : Prop := ∃ guide : ℕ → ℕ,
  guidedPair (tileAt i).code (tileAt j).code atMostThree guide 5
    ⟨boardWord (tileAt i).shape,0,1,0⟩ 0=true

theorem complete_from_indices
    (h : ∀ i j : Fin 14, 2 ≤ i.val → i.val < j.val → pairAt i j) : completePairs := by
  intro e he d hd earea _ order
  obtain ⟨i,rfl⟩:=entry_is_index he
  obtain ⟨j,rfl⟩:=entry_is_index hd
  have big := (entry_measures he).2.2.1.mp earea
  rw [id_at] at big
  rw [id_at,id_at] at order
  exact h i j big order

end PrimePolyFactor
