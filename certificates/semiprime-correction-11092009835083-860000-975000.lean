import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 860,000 through 975,000

The sum covers 8,384 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction11092009835083From860000To975000

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev term := contribution 11092009835083 860000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 860001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 860000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r860001 : blockSum term 860001 449 27881339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r860450 : blockSum term 860450 449 23995189 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r860899 : blockSum term 860899 449 27077922 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r861348 : blockSum term 861348 449 22422461 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r861797 : blockSum term 861797 449 32455409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r862246 : blockSum term 862246 449 30119695 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r862695 : blockSum term 862695 449 23926733 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r863144 : blockSum term 863144 450 16970520 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r863594 : blockSum term 863594 449 26212210 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r864043 : blockSum term 864043 449 29280712 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r864492 : blockSum term 864492 449 23872772 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r864941 : blockSum term 864941 450 30784577 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r865391 : blockSum term 865391 449 26920044 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r865840 : blockSum term 865840 449 24600446 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r866289 : blockSum term 866289 449 22280487 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r866738 : blockSum term 866738 450 25339427 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r867188 : blockSum term 867188 449 29929544 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r867637 : blockSum term 867637 449 23776987 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r868086 : blockSum term 868086 449 26829239 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r868535 : blockSum term 868535 450 26813499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r868985 : blockSum term 868985 449 26798551 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r869434 : blockSum term 869434 449 24487515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r869883 : blockSum term 869883 449 28297296 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r870332 : blockSum term 870332 450 23695195 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r870782 : blockSum term 870782 449 24446051 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r871231 : blockSum term 871231 449 20613185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r871680 : blockSum term 871680 449 22127632 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r872129 : blockSum term 872129 450 31267175 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r872579 : blockSum term 872579 449 19816393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r873028 : blockSum term 873028 449 24374909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r873477 : blockSum term 873477 449 21316744 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r873926 : blockSum term 873926 450 24347248 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r874376 : blockSum term 874376 449 27374966 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r874825 : blockSum term 874825 449 23558989 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r875274 : blockSum term 875274 449 31141337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r875723 : blockSum term 875723 449 26569128 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r876172 : blockSum term 876172 449 25037437 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r876621 : blockSum term 876621 449 22749049 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r877070 : blockSum term 877070 449 24251879 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r877519 : blockSum term 877519 450 22722667 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r877969 : blockSum term 877969 449 25738325 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r878418 : blockSum term 878418 449 27235707 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r878867 : blockSum term 878867 449 25708447 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r879316 : blockSum term 879316 450 26449197 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r879766 : blockSum term 879766 449 24923755 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r880215 : blockSum term 880215 449 24155311 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r880664 : blockSum term 880664 449 28668447 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r881113 : blockSum term 881113 450 27897363 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r881563 : blockSum term 881563 449 18085088 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r882012 : blockSum term 882012 449 25606913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r882461 : blockSum term 882461 449 23333982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r882910 : blockSum term 882910 450 27082245 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r883360 : blockSum term 883360 449 25563412 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r883809 : blockSum term 883809 449 21791393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r884258 : blockSum term 884258 449 24033548 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r884707 : blockSum term 884707 450 21017173 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r885157 : blockSum term 885157 449 25507896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r885606 : blockSum term 885606 449 29240527 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r886055 : blockSum term 886055 449 23978292 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r886504 : blockSum term 886504 450 22468337 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r886954 : blockSum term 886954 449 25449574 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r887403 : blockSum term 887403 449 26931423 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r887852 : blockSum term 887852 449 23178448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r888301 : blockSum term 888301 450 24660838 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r888751 : blockSum term 888751 449 26140789 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r889200 : blockSum term 889200 449 22393496 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r889649 : blockSum term 889649 449 23127086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r890098 : blockSum term 890098 449 20877698 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r890547 : blockSum term 890547 449 24590840 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r890996 : blockSum term 890996 449 23832971 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r891445 : blockSum term 891445 449 30518476 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r891894 : blockSum term 891894 450 23806459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r892344 : blockSum term 892344 449 24536405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r892793 : blockSum term 892793 449 25265369 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r893242 : blockSum term 893242 449 22281316 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r893691 : blockSum term 893691 450 22267832 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r894141 : blockSum term 894141 449 29674686 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r894590 : blockSum term 894590 449 20019001 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r895039 : blockSum term 895039 449 27417711 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r895488 : blockSum term 895488 450 28142808 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r895938 : blockSum term 895938 449 19984619 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r896387 : blockSum term 896387 449 21454730 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r896836 : blockSum term 896836 449 24398809 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r897285 : blockSum term 897285 450 27340048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r897735 : blockSum term 897735 449 22154385 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r898184 : blockSum term 898184 449 27309802 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r898633 : blockSum term 898633 449 20655411 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r899082 : blockSum term 899082 450 21381536 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r899532 : blockSum term 899532 449 19895846 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r899981 : blockSum term 899981 449 22832154 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r900430 : blockSum term 900430 449 26499313 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r900879 : blockSum term 900879 450 24276730 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r901329 : blockSum term 901329 449 23528212 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r901778 : blockSum term 901778 449 22045197 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r902227 : blockSum term 902227 449 24235671 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r902676 : blockSum term 902676 450 22020338 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r903126 : blockSum term 903126 449 23475190 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r903575 : blockSum term 903575 449 18330184 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r904024 : blockSum term 904024 449 21984974 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r904473 : blockSum term 904473 449 32957405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r904922 : blockSum term 904922 449 24154869 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r905371 : blockSum term 905371 449 23409729 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r905820 : blockSum term 905820 449 21934998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r906269 : blockSum term 906269 450 27769945 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r906719 : blockSum term 906719 449 24102621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r907168 : blockSum term 907168 449 27738842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r907617 : blockSum term 907617 449 25534569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r908066 : blockSum term 908066 450 23332125 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r908516 : blockSum term 908516 449 30606343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r908965 : blockSum term 908965 449 28403536 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r909414 : blockSum term 909414 449 24020826 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r909863 : blockSum term 909863 450 25463376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r910313 : blockSum term 910313 449 18177131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r910762 : blockSum term 910762 449 23981448 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r911211 : blockSum term 911211 449 22516929 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r911660 : blockSum term 911660 450 28311550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r912110 : blockSum term 912110 449 24666941 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r912559 : blockSum term 912559 449 20302998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r913008 : blockSum term 913008 449 19567842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r913457 : blockSum term 913457 450 15211250 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r913907 : blockSum term 913907 449 19545938 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r914356 : blockSum term 914356 449 26771476 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r914805 : blockSum term 914805 449 26756514 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r915254 : blockSum term 915254 450 20959126 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r915704 : blockSum term 915704 449 23114627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r916153 : blockSum term 916153 449 24546394 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r916602 : blockSum term 916602 449 20203222 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r917051 : blockSum term 917051 450 24520795 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r917501 : blockSum term 917501 449 28110449 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r917950 : blockSum term 917950 449 25933468 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r918399 : blockSum term 918399 449 22319480 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r918848 : blockSum term 918848 449 23747078 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r919297 : blockSum term 919297 449 20138701 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r919746 : blockSum term 919746 449 22283845 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r920195 : blockSum term 920195 449 24427084 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r920644 : blockSum term 920644 450 25848643 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r921094 : blockSum term 921094 449 22246513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r921543 : blockSum term 921543 449 23668696 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r921992 : blockSum term 921992 449 24373041 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r922441 : blockSum term 922441 450 23644104 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r922891 : blockSum term 922891 449 21481946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r923340 : blockSum term 923340 449 26480468 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r923789 : blockSum term 923789 449 25750442 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r924238 : blockSum term 924238 450 23591746 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r924688 : blockSum term 924688 449 29295048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r925137 : blockSum term 925137 449 24994224 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r925586 : blockSum term 925586 449 23552308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r926035 : blockSum term 926035 450 22826610 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r926485 : blockSum term 926485 449 24240569 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r926934 : blockSum term 926934 449 20664778 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r927383 : blockSum term 927383 449 21365105 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r927832 : blockSum term 927832 450 21353134 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r928282 : blockSum term 928282 449 22764361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r928731 : blockSum term 928731 449 25595137 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r929180 : blockSum term 929180 449 24160106 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r929629 : blockSum term 929629 450 22727632 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r930079 : blockSum term 930079 449 22714746 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r930528 : blockSum term 930528 449 20574168 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r930977 : blockSum term 930977 449 21980811 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r931426 : blockSum term 931426 450 20550926 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r931876 : blockSum term 931876 449 24790515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r932325 : blockSum term 932325 449 24068840 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r932774 : blockSum term 932774 449 23348449 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r933223 : blockSum term 933223 449 20507291 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r933672 : blockSum term 933672 449 26149057 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r934121 : blockSum term 934121 449 24015625 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r934570 : blockSum term 934570 449 25415006 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r935019 : blockSum term 935019 450 22578523 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r935469 : blockSum term 935469 449 23271192 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r935918 : blockSum term 935918 449 18324316 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r936367 : blockSum term 936367 449 25359732 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r936816 : blockSum term 936816 450 21121971 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r937266 : blockSum term 937266 449 21110020 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r937715 : blockSum term 937715 449 26022951 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r938164 : blockSum term 938164 449 22494323 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r938613 : blockSum term 938613 450 20373706 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r939063 : blockSum term 939063 449 22470149 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r939512 : blockSum term 939512 449 19650558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r939961 : blockSum term 939961 449 24549785 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r940410 : blockSum term 940410 450 22433213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r940860 : blockSum term 940860 449 24523610 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r941309 : blockSum term 941309 449 28010192 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r941758 : blockSum term 941758 449 23095559 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r942207 : blockSum term 942207 450 20285913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r942657 : blockSum term 942657 449 25168736 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r943106 : blockSum term 943106 449 23059515 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r943555 : blockSum term 943555 449 23047206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r944004 : blockSum term 944004 450 20940183 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r944454 : blockSum term 944454 449 25812856 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r944903 : blockSum term 944903 449 15339838 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r945352 : blockSum term 945352 449 22300888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r945801 : blockSum term 945801 450 24378809 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r946251 : blockSum term 946251 449 20188240 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r946700 : blockSum term 946700 449 21569753 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r947149 : blockSum term 947149 449 20166977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r947598 : blockSum term 947598 449 24327178 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r948047 : blockSum term 948047 449 23618464 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r948496 : blockSum term 948496 449 17356958 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r948945 : blockSum term 948945 449 20124267 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r949394 : blockSum term 949394 450 23580961 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r949844 : blockSum term 949844 449 26341473 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r950293 : blockSum term 950293 449 24248289 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r950742 : blockSum term 950742 449 24928165 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r951191 : blockSum term 951191 450 21454275 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r951641 : blockSum term 951641 449 19367647 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r952090 : blockSum term 952090 449 22814239 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r952539 : blockSum term 952539 449 26255602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r952988 : blockSum term 952988 450 18646197 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r953438 : blockSum term 953438 449 21397941 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r953887 : blockSum term 953887 449 24145602 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r954336 : blockSum term 954336 449 19995673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r954785 : blockSum term 954785 450 23430116 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r955235 : blockSum term 955235 449 20663036 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r955684 : blockSum term 955684 449 24781039 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r956133 : blockSum term 956133 449 17887776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r956582 : blockSum term 956582 450 17877893 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r957032 : blockSum term 957032 449 22680593 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r957481 : blockSum term 957481 449 19920039 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r957930 : blockSum term 957930 449 24714621 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r958379 : blockSum term 958379 450 21957421 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r958829 : blockSum term 958829 449 22631437 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r959278 : blockSum term 959278 449 21248237 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r959727 : blockSum term 959727 449 23292301 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r960176 : blockSum term 960176 450 19171687 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r960626 : blockSum term 960626 449 22583186 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r961075 : blockSum term 961075 449 24623353 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r961524 : blockSum term 961524 449 28027329 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r961973 : blockSum term 961973 449 19130558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r962422 : blockSum term 962422 449 26630426 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r962871 : blockSum term 962871 449 21155943 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r963320 : blockSum term 963320 449 23191441 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r963769 : blockSum term 963769 450 21134911 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r964219 : blockSum term 964219 449 23168007 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r964668 : blockSum term 964668 449 22474119 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r965117 : blockSum term 965117 449 24504490 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r965566 : blockSum term 965566 450 19729056 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r966016 : blockSum term 966016 449 23797832 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r966465 : blockSum term 966465 449 19708646 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r966914 : blockSum term 966914 449 18339343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r967363 : blockSum term 967363 450 20366523 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r967813 : blockSum term 967813 449 25105255 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r968262 : blockSum term 968262 449 23735127 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r968711 : blockSum term 968711 449 20333224 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r969160 : blockSum term 969160 450 22354527 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r969610 : blockSum term 969610 449 22342701 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r970059 : blockSum term 970059 449 22331359 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r970508 : blockSum term 970508 449 22319088 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r970957 : blockSum term 970957 450 27715992 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r971407 : blockSum term 971407 449 20268819 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r971856 : blockSum term 971856 449 25660478 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r972305 : blockSum term 972305 449 22272745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r972754 : blockSum term 972754 450 21585816 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r973204 : blockSum term 973204 449 18203639 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r973653 : blockSum term 973653 449 18194048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r974102 : blockSum term 974102 449 26266320 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r974551 : blockSum term 974551 450 26251656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 860001 115000 6054181604 := (join_sums term (lo:=860001) (a:=57500) (b:=57500) (join_sums term (lo:=860001) (a:=28750) (b:=28750) (join_sums term (lo:=860001) (a:=14375) (b:=14375) (join_sums term (lo:=860001) (a:=7187) (b:=7188) (join_sums term (lo:=860001) (a:=3593) (b:=3594) (join_sums term (lo:=860001) (a:=1796) (b:=1797) (join_sums term (lo:=860001) (a:=898) (b:=898) (join_sums term (lo:=860001) (a:=449) (b:=449) r860001 r860450) (join_sums term (lo:=860899) (a:=449) (b:=449) r860899 r861348)) (join_sums term (lo:=861797) (a:=898) (b:=899) (join_sums term (lo:=861797) (a:=449) (b:=449) r861797 r862246) (join_sums term (lo:=862695) (a:=449) (b:=450) r862695 r863144))) (join_sums term (lo:=863594) (a:=1797) (b:=1797) (join_sums term (lo:=863594) (a:=898) (b:=899) (join_sums term (lo:=863594) (a:=449) (b:=449) r863594 r864043) (join_sums term (lo:=864492) (a:=449) (b:=450) r864492 r864941)) (join_sums term (lo:=865391) (a:=898) (b:=899) (join_sums term (lo:=865391) (a:=449) (b:=449) r865391 r865840) (join_sums term (lo:=866289) (a:=449) (b:=450) r866289 r866738)))) (join_sums term (lo:=867188) (a:=3594) (b:=3594) (join_sums term (lo:=867188) (a:=1797) (b:=1797) (join_sums term (lo:=867188) (a:=898) (b:=899) (join_sums term (lo:=867188) (a:=449) (b:=449) r867188 r867637) (join_sums term (lo:=868086) (a:=449) (b:=450) r868086 r868535)) (join_sums term (lo:=868985) (a:=898) (b:=899) (join_sums term (lo:=868985) (a:=449) (b:=449) r868985 r869434) (join_sums term (lo:=869883) (a:=449) (b:=450) r869883 r870332))) (join_sums term (lo:=870782) (a:=1797) (b:=1797) (join_sums term (lo:=870782) (a:=898) (b:=899) (join_sums term (lo:=870782) (a:=449) (b:=449) r870782 r871231) (join_sums term (lo:=871680) (a:=449) (b:=450) r871680 r872129)) (join_sums term (lo:=872579) (a:=898) (b:=899) (join_sums term (lo:=872579) (a:=449) (b:=449) r872579 r873028) (join_sums term (lo:=873477) (a:=449) (b:=450) r873477 r873926))))) (join_sums term (lo:=874376) (a:=7187) (b:=7188) (join_sums term (lo:=874376) (a:=3593) (b:=3594) (join_sums term (lo:=874376) (a:=1796) (b:=1797) (join_sums term (lo:=874376) (a:=898) (b:=898) (join_sums term (lo:=874376) (a:=449) (b:=449) r874376 r874825) (join_sums term (lo:=875274) (a:=449) (b:=449) r875274 r875723)) (join_sums term (lo:=876172) (a:=898) (b:=899) (join_sums term (lo:=876172) (a:=449) (b:=449) r876172 r876621) (join_sums term (lo:=877070) (a:=449) (b:=450) r877070 r877519))) (join_sums term (lo:=877969) (a:=1797) (b:=1797) (join_sums term (lo:=877969) (a:=898) (b:=899) (join_sums term (lo:=877969) (a:=449) (b:=449) r877969 r878418) (join_sums term (lo:=878867) (a:=449) (b:=450) r878867 r879316)) (join_sums term (lo:=879766) (a:=898) (b:=899) (join_sums term (lo:=879766) (a:=449) (b:=449) r879766 r880215) (join_sums term (lo:=880664) (a:=449) (b:=450) r880664 r881113)))) (join_sums term (lo:=881563) (a:=3594) (b:=3594) (join_sums term (lo:=881563) (a:=1797) (b:=1797) (join_sums term (lo:=881563) (a:=898) (b:=899) (join_sums term (lo:=881563) (a:=449) (b:=449) r881563 r882012) (join_sums term (lo:=882461) (a:=449) (b:=450) r882461 r882910)) (join_sums term (lo:=883360) (a:=898) (b:=899) (join_sums term (lo:=883360) (a:=449) (b:=449) r883360 r883809) (join_sums term (lo:=884258) (a:=449) (b:=450) r884258 r884707))) (join_sums term (lo:=885157) (a:=1797) (b:=1797) (join_sums term (lo:=885157) (a:=898) (b:=899) (join_sums term (lo:=885157) (a:=449) (b:=449) r885157 r885606) (join_sums term (lo:=886055) (a:=449) (b:=450) r886055 r886504)) (join_sums term (lo:=886954) (a:=898) (b:=899) (join_sums term (lo:=886954) (a:=449) (b:=449) r886954 r887403) (join_sums term (lo:=887852) (a:=449) (b:=450) r887852 r888301)))))) (join_sums term (lo:=888751) (a:=14375) (b:=14375) (join_sums term (lo:=888751) (a:=7187) (b:=7188) (join_sums term (lo:=888751) (a:=3593) (b:=3594) (join_sums term (lo:=888751) (a:=1796) (b:=1797) (join_sums term (lo:=888751) (a:=898) (b:=898) (join_sums term (lo:=888751) (a:=449) (b:=449) r888751 r889200) (join_sums term (lo:=889649) (a:=449) (b:=449) r889649 r890098)) (join_sums term (lo:=890547) (a:=898) (b:=899) (join_sums term (lo:=890547) (a:=449) (b:=449) r890547 r890996) (join_sums term (lo:=891445) (a:=449) (b:=450) r891445 r891894))) (join_sums term (lo:=892344) (a:=1797) (b:=1797) (join_sums term (lo:=892344) (a:=898) (b:=899) (join_sums term (lo:=892344) (a:=449) (b:=449) r892344 r892793) (join_sums term (lo:=893242) (a:=449) (b:=450) r893242 r893691)) (join_sums term (lo:=894141) (a:=898) (b:=899) (join_sums term (lo:=894141) (a:=449) (b:=449) r894141 r894590) (join_sums term (lo:=895039) (a:=449) (b:=450) r895039 r895488)))) (join_sums term (lo:=895938) (a:=3594) (b:=3594) (join_sums term (lo:=895938) (a:=1797) (b:=1797) (join_sums term (lo:=895938) (a:=898) (b:=899) (join_sums term (lo:=895938) (a:=449) (b:=449) r895938 r896387) (join_sums term (lo:=896836) (a:=449) (b:=450) r896836 r897285)) (join_sums term (lo:=897735) (a:=898) (b:=899) (join_sums term (lo:=897735) (a:=449) (b:=449) r897735 r898184) (join_sums term (lo:=898633) (a:=449) (b:=450) r898633 r899082))) (join_sums term (lo:=899532) (a:=1797) (b:=1797) (join_sums term (lo:=899532) (a:=898) (b:=899) (join_sums term (lo:=899532) (a:=449) (b:=449) r899532 r899981) (join_sums term (lo:=900430) (a:=449) (b:=450) r900430 r900879)) (join_sums term (lo:=901329) (a:=898) (b:=899) (join_sums term (lo:=901329) (a:=449) (b:=449) r901329 r901778) (join_sums term (lo:=902227) (a:=449) (b:=450) r902227 r902676))))) (join_sums term (lo:=903126) (a:=7187) (b:=7188) (join_sums term (lo:=903126) (a:=3593) (b:=3594) (join_sums term (lo:=903126) (a:=1796) (b:=1797) (join_sums term (lo:=903126) (a:=898) (b:=898) (join_sums term (lo:=903126) (a:=449) (b:=449) r903126 r903575) (join_sums term (lo:=904024) (a:=449) (b:=449) r904024 r904473)) (join_sums term (lo:=904922) (a:=898) (b:=899) (join_sums term (lo:=904922) (a:=449) (b:=449) r904922 r905371) (join_sums term (lo:=905820) (a:=449) (b:=450) r905820 r906269))) (join_sums term (lo:=906719) (a:=1797) (b:=1797) (join_sums term (lo:=906719) (a:=898) (b:=899) (join_sums term (lo:=906719) (a:=449) (b:=449) r906719 r907168) (join_sums term (lo:=907617) (a:=449) (b:=450) r907617 r908066)) (join_sums term (lo:=908516) (a:=898) (b:=899) (join_sums term (lo:=908516) (a:=449) (b:=449) r908516 r908965) (join_sums term (lo:=909414) (a:=449) (b:=450) r909414 r909863)))) (join_sums term (lo:=910313) (a:=3594) (b:=3594) (join_sums term (lo:=910313) (a:=1797) (b:=1797) (join_sums term (lo:=910313) (a:=898) (b:=899) (join_sums term (lo:=910313) (a:=449) (b:=449) r910313 r910762) (join_sums term (lo:=911211) (a:=449) (b:=450) r911211 r911660)) (join_sums term (lo:=912110) (a:=898) (b:=899) (join_sums term (lo:=912110) (a:=449) (b:=449) r912110 r912559) (join_sums term (lo:=913008) (a:=449) (b:=450) r913008 r913457))) (join_sums term (lo:=913907) (a:=1797) (b:=1797) (join_sums term (lo:=913907) (a:=898) (b:=899) (join_sums term (lo:=913907) (a:=449) (b:=449) r913907 r914356) (join_sums term (lo:=914805) (a:=449) (b:=450) r914805 r915254)) (join_sums term (lo:=915704) (a:=898) (b:=899) (join_sums term (lo:=915704) (a:=449) (b:=449) r915704 r916153) (join_sums term (lo:=916602) (a:=449) (b:=450) r916602 r917051))))))) (join_sums term (lo:=917501) (a:=28750) (b:=28750) (join_sums term (lo:=917501) (a:=14375) (b:=14375) (join_sums term (lo:=917501) (a:=7187) (b:=7188) (join_sums term (lo:=917501) (a:=3593) (b:=3594) (join_sums term (lo:=917501) (a:=1796) (b:=1797) (join_sums term (lo:=917501) (a:=898) (b:=898) (join_sums term (lo:=917501) (a:=449) (b:=449) r917501 r917950) (join_sums term (lo:=918399) (a:=449) (b:=449) r918399 r918848)) (join_sums term (lo:=919297) (a:=898) (b:=899) (join_sums term (lo:=919297) (a:=449) (b:=449) r919297 r919746) (join_sums term (lo:=920195) (a:=449) (b:=450) r920195 r920644))) (join_sums term (lo:=921094) (a:=1797) (b:=1797) (join_sums term (lo:=921094) (a:=898) (b:=899) (join_sums term (lo:=921094) (a:=449) (b:=449) r921094 r921543) (join_sums term (lo:=921992) (a:=449) (b:=450) r921992 r922441)) (join_sums term (lo:=922891) (a:=898) (b:=899) (join_sums term (lo:=922891) (a:=449) (b:=449) r922891 r923340) (join_sums term (lo:=923789) (a:=449) (b:=450) r923789 r924238)))) (join_sums term (lo:=924688) (a:=3594) (b:=3594) (join_sums term (lo:=924688) (a:=1797) (b:=1797) (join_sums term (lo:=924688) (a:=898) (b:=899) (join_sums term (lo:=924688) (a:=449) (b:=449) r924688 r925137) (join_sums term (lo:=925586) (a:=449) (b:=450) r925586 r926035)) (join_sums term (lo:=926485) (a:=898) (b:=899) (join_sums term (lo:=926485) (a:=449) (b:=449) r926485 r926934) (join_sums term (lo:=927383) (a:=449) (b:=450) r927383 r927832))) (join_sums term (lo:=928282) (a:=1797) (b:=1797) (join_sums term (lo:=928282) (a:=898) (b:=899) (join_sums term (lo:=928282) (a:=449) (b:=449) r928282 r928731) (join_sums term (lo:=929180) (a:=449) (b:=450) r929180 r929629)) (join_sums term (lo:=930079) (a:=898) (b:=899) (join_sums term (lo:=930079) (a:=449) (b:=449) r930079 r930528) (join_sums term (lo:=930977) (a:=449) (b:=450) r930977 r931426))))) (join_sums term (lo:=931876) (a:=7187) (b:=7188) (join_sums term (lo:=931876) (a:=3593) (b:=3594) (join_sums term (lo:=931876) (a:=1796) (b:=1797) (join_sums term (lo:=931876) (a:=898) (b:=898) (join_sums term (lo:=931876) (a:=449) (b:=449) r931876 r932325) (join_sums term (lo:=932774) (a:=449) (b:=449) r932774 r933223)) (join_sums term (lo:=933672) (a:=898) (b:=899) (join_sums term (lo:=933672) (a:=449) (b:=449) r933672 r934121) (join_sums term (lo:=934570) (a:=449) (b:=450) r934570 r935019))) (join_sums term (lo:=935469) (a:=1797) (b:=1797) (join_sums term (lo:=935469) (a:=898) (b:=899) (join_sums term (lo:=935469) (a:=449) (b:=449) r935469 r935918) (join_sums term (lo:=936367) (a:=449) (b:=450) r936367 r936816)) (join_sums term (lo:=937266) (a:=898) (b:=899) (join_sums term (lo:=937266) (a:=449) (b:=449) r937266 r937715) (join_sums term (lo:=938164) (a:=449) (b:=450) r938164 r938613)))) (join_sums term (lo:=939063) (a:=3594) (b:=3594) (join_sums term (lo:=939063) (a:=1797) (b:=1797) (join_sums term (lo:=939063) (a:=898) (b:=899) (join_sums term (lo:=939063) (a:=449) (b:=449) r939063 r939512) (join_sums term (lo:=939961) (a:=449) (b:=450) r939961 r940410)) (join_sums term (lo:=940860) (a:=898) (b:=899) (join_sums term (lo:=940860) (a:=449) (b:=449) r940860 r941309) (join_sums term (lo:=941758) (a:=449) (b:=450) r941758 r942207))) (join_sums term (lo:=942657) (a:=1797) (b:=1797) (join_sums term (lo:=942657) (a:=898) (b:=899) (join_sums term (lo:=942657) (a:=449) (b:=449) r942657 r943106) (join_sums term (lo:=943555) (a:=449) (b:=450) r943555 r944004)) (join_sums term (lo:=944454) (a:=898) (b:=899) (join_sums term (lo:=944454) (a:=449) (b:=449) r944454 r944903) (join_sums term (lo:=945352) (a:=449) (b:=450) r945352 r945801)))))) (join_sums term (lo:=946251) (a:=14375) (b:=14375) (join_sums term (lo:=946251) (a:=7187) (b:=7188) (join_sums term (lo:=946251) (a:=3593) (b:=3594) (join_sums term (lo:=946251) (a:=1796) (b:=1797) (join_sums term (lo:=946251) (a:=898) (b:=898) (join_sums term (lo:=946251) (a:=449) (b:=449) r946251 r946700) (join_sums term (lo:=947149) (a:=449) (b:=449) r947149 r947598)) (join_sums term (lo:=948047) (a:=898) (b:=899) (join_sums term (lo:=948047) (a:=449) (b:=449) r948047 r948496) (join_sums term (lo:=948945) (a:=449) (b:=450) r948945 r949394))) (join_sums term (lo:=949844) (a:=1797) (b:=1797) (join_sums term (lo:=949844) (a:=898) (b:=899) (join_sums term (lo:=949844) (a:=449) (b:=449) r949844 r950293) (join_sums term (lo:=950742) (a:=449) (b:=450) r950742 r951191)) (join_sums term (lo:=951641) (a:=898) (b:=899) (join_sums term (lo:=951641) (a:=449) (b:=449) r951641 r952090) (join_sums term (lo:=952539) (a:=449) (b:=450) r952539 r952988)))) (join_sums term (lo:=953438) (a:=3594) (b:=3594) (join_sums term (lo:=953438) (a:=1797) (b:=1797) (join_sums term (lo:=953438) (a:=898) (b:=899) (join_sums term (lo:=953438) (a:=449) (b:=449) r953438 r953887) (join_sums term (lo:=954336) (a:=449) (b:=450) r954336 r954785)) (join_sums term (lo:=955235) (a:=898) (b:=899) (join_sums term (lo:=955235) (a:=449) (b:=449) r955235 r955684) (join_sums term (lo:=956133) (a:=449) (b:=450) r956133 r956582))) (join_sums term (lo:=957032) (a:=1797) (b:=1797) (join_sums term (lo:=957032) (a:=898) (b:=899) (join_sums term (lo:=957032) (a:=449) (b:=449) r957032 r957481) (join_sums term (lo:=957930) (a:=449) (b:=450) r957930 r958379)) (join_sums term (lo:=958829) (a:=898) (b:=899) (join_sums term (lo:=958829) (a:=449) (b:=449) r958829 r959278) (join_sums term (lo:=959727) (a:=449) (b:=450) r959727 r960176))))) (join_sums term (lo:=960626) (a:=7187) (b:=7188) (join_sums term (lo:=960626) (a:=3593) (b:=3594) (join_sums term (lo:=960626) (a:=1796) (b:=1797) (join_sums term (lo:=960626) (a:=898) (b:=898) (join_sums term (lo:=960626) (a:=449) (b:=449) r960626 r961075) (join_sums term (lo:=961524) (a:=449) (b:=449) r961524 r961973)) (join_sums term (lo:=962422) (a:=898) (b:=899) (join_sums term (lo:=962422) (a:=449) (b:=449) r962422 r962871) (join_sums term (lo:=963320) (a:=449) (b:=450) r963320 r963769))) (join_sums term (lo:=964219) (a:=1797) (b:=1797) (join_sums term (lo:=964219) (a:=898) (b:=899) (join_sums term (lo:=964219) (a:=449) (b:=449) r964219 r964668) (join_sums term (lo:=965117) (a:=449) (b:=450) r965117 r965566)) (join_sums term (lo:=966016) (a:=898) (b:=899) (join_sums term (lo:=966016) (a:=449) (b:=449) r966016 r966465) (join_sums term (lo:=966914) (a:=449) (b:=450) r966914 r967363)))) (join_sums term (lo:=967813) (a:=3594) (b:=3594) (join_sums term (lo:=967813) (a:=1797) (b:=1797) (join_sums term (lo:=967813) (a:=898) (b:=899) (join_sums term (lo:=967813) (a:=449) (b:=449) r967813 r968262) (join_sums term (lo:=968711) (a:=449) (b:=450) r968711 r969160)) (join_sums term (lo:=969610) (a:=898) (b:=899) (join_sums term (lo:=969610) (a:=449) (b:=449) r969610 r970059) (join_sums term (lo:=970508) (a:=449) (b:=450) r970508 r970957))) (join_sums term (lo:=971407) (a:=1797) (b:=1797) (join_sums term (lo:=971407) (a:=898) (b:=899) (join_sums term (lo:=971407) (a:=449) (b:=449) r971407 r971856) (join_sums term (lo:=972305) (a:=449) (b:=450) r972305 r972754)) (join_sums term (lo:=973204) (a:=898) (b:=899) (join_sums term (lo:=973204) (a:=449) (b:=449) r973204 r973653) (join_sums term (lo:=974102) (a:=449) (b:=450) r974102 r974551))))))))

private theorem rows : blockSum term 0 975001 6054181604 :=
  join_sums term (lo:=0) (a:=860001) (b:=115000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 975000).filter (860000 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=6054181604 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From860000To975000
