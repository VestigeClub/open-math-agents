import certificates.«semiprime-correction-555157672301-middle»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 900,000 through 990,000

The sum covers 6,503 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction30110134441897From900000To990000

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


private abbrev term := contribution 30110134441897 900000 SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 900001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 900000 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r900001 : blockSum term 900001 703 105255460 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r900704 : blockSum term 900704 703 101205595 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r901407 : blockSum term 901407 703 101127070 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r902110 : blockSum term 902110 703 99061339 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r902813 : blockSum term 902813 703 91065900 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r903516 : blockSum term 903516 703 94949690 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r904219 : blockSum term 904219 703 112660323 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r904922 : blockSum term 904922 704 94804238 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r905626 : blockSum term 905626 703 100649802 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r906329 : blockSum term 906329 703 116347578 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r907032 : blockSum term 907032 703 114282478 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r907735 : blockSum term 907735 703 92538242 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r908438 : blockSum term 908438 703 127878096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r909141 : blockSum term 909141 703 110083614 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r909844 : blockSum term 909844 703 90359875 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r910547 : blockSum term 910547 704 104022133 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r911251 : blockSum term 911251 703 103943622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r911954 : blockSum term 911954 703 99945331 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r912657 : blockSum term 912657 703 84203044 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r913360 : blockSum term 913360 703 74355174 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r914063 : blockSum term 914063 703 95800579 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r914766 : blockSum term 914766 703 101594797 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r915469 : blockSum term 915469 703 101510191 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r916172 : blockSum term 916172 704 95583567 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r916876 : blockSum term 916876 703 101356588 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r917579 : blockSum term 917579 703 112965488 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r918282 : blockSum term 918282 703 101199233 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r918985 : blockSum term 918985 703 91402041 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r919688 : blockSum term 919688 703 101044935 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r920391 : blockSum term 920391 703 102908139 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r921094 : blockSum term 921094 703 98947152 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r921797 : blockSum term 921797 704 102748083 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r922501 : blockSum term 922501 703 96859361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r923204 : blockSum term 923204 703 100657143 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r923907 : blockSum term 923907 703 106384843 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r924610 : blockSum term 924610 703 119827765 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r925313 : blockSum term 925313 703 96560909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r926016 : blockSum term 926016 703 106135256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r926719 : blockSum term 926719 703 86772613 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r927422 : blockSum term 927422 704 86705213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r928126 : blockSum term 928126 703 102040924 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r928829 : blockSum term 928829 703 101962955 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r929532 : blockSum term 929532 703 105729643 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r930235 : blockSum term 930235 703 88360314 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r930938 : blockSum term 930938 703 84454709 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r931641 : blockSum term 931641 703 103570206 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r932344 : blockSum term 932344 703 101574573 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r933047 : blockSum term 933047 704 86177654 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r933751 : blockSum term 933751 703 103335440 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r934454 : blockSum term 934454 703 112817238 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r935157 : blockSum term 935157 703 99354131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r935860 : blockSum term 935860 703 85912220 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r936563 : blockSum term 936563 703 95390429 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r937266 : blockSum term 937266 703 95313200 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r937969 : blockSum term 937969 703 97152416 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r938672 : blockSum term 938672 704 93266920 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r939376 : blockSum term 939376 703 91294890 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r940079 : blockSum term 940079 703 95029334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r940782 : blockSum term 940782 703 106353481 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r941485 : blockSum term 941485 703 110068622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r942188 : blockSum term 942188 703 92915112 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r942891 : blockSum term 942891 703 100427490 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r943594 : blockSum term 943594 703 90885924 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r944297 : blockSum term 944297 704 102170598 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r945001 : blockSum term 945001 703 81291651 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r945704 : blockSum term 945704 703 94458880 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r946407 : blockSum term 946407 703 90611316 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r947110 : blockSum term 947110 703 94313213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r947813 : blockSum term 947813 703 96129431 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r948516 : blockSum term 948516 703 84754687 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r949219 : blockSum term 949219 703 90340528 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r949922 : blockSum term 949922 704 107202270 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r950626 : blockSum term 950626 703 101482973 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r951329 : blockSum term 951329 703 90139758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r952032 : blockSum term 952032 703 97577067 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r952735 : blockSum term 952735 703 93756513 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r953438 : blockSum term 953438 703 91808669 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r954141 : blockSum term 954141 703 89868597 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r954844 : blockSum term 954844 703 106638828 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r955547 : blockSum term 955547 704 85994821 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r956251 : blockSum term 956251 703 80328171 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r956954 : blockSum term 956954 703 91470547 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r957657 : blockSum term 957657 703 93265977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r958360 : blockSum term 958360 703 95065565 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r959063 : blockSum term 959063 703 93130533 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r959766 : blockSum term 959766 703 91202305 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r960469 : blockSum term 960469 703 106006463 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r961172 : blockSum term 961172 704 109643993 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r961876 : blockSum term 961876 703 87281050 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r962579 : blockSum term 962579 703 96495585 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r963282 : blockSum term 963282 703 101986492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r963985 : blockSum term 963985 703 90792570 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r964688 : blockSum term 964688 703 98133250 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r965391 : blockSum term 965391 703 85112888 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r966094 : blockSum term 966094 703 97993342 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r966797 : blockSum term 966797 704 84984072 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r967501 : blockSum term 967501 703 97841737 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r968204 : blockSum term 968204 703 94085892 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r968907 : blockSum term 968907 703 94014228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r969610 : blockSum term 969610 703 99472653 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r970313 : blockSum term 970313 703 93874700 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r971016 : blockSum term 971016 703 104848179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r971719 : blockSum term 971719 703 104767943 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r972422 : blockSum term 972422 704 89999228 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r973126 : blockSum term 973126 703 82592477 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r973829 : blockSum term 973829 703 93533756 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r974532 : blockSum term 974532 703 102632637 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r975235 : blockSum term 975235 703 91568474 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r975938 : blockSum term 975938 703 95158521 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r976641 : blockSum term 976641 703 73145477 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r977344 : blockSum term 977344 703 84056692 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r978047 : blockSum term 978047 704 104084350 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r978751 : blockSum term 978751 703 94881545 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r979454 : blockSum term 979454 703 71109913 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r980157 : blockSum term 980157 703 85634980 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r980860 : blockSum term 980860 703 98319343 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r981563 : blockSum term 981563 703 92788947 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r982266 : blockSum term 982266 703 87263876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r982969 : blockSum term 982969 703 90834349 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r983672 : blockSum term 983672 704 88951280 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r984376 : blockSum term 984376 703 88889073 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r985079 : blockSum term 985079 703 94259472 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r985782 : blockSum term 985782 703 90570068 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r986485 : blockSum term 986485 703 104984668 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r987188 : blockSum term 987188 703 72351923 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r987891 : blockSum term 987891 703 97601455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r988594 : blockSum term 988594 703 75858997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r989297 : blockSum term 989297 704 101072163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 900001 90000 12311571924 := (join_sums term (lo:=900001) (a:=45000) (b:=45000) (join_sums term (lo:=900001) (a:=22500) (b:=22500) (join_sums term (lo:=900001) (a:=11250) (b:=11250) (join_sums term (lo:=900001) (a:=5625) (b:=5625) (join_sums term (lo:=900001) (a:=2812) (b:=2813) (join_sums term (lo:=900001) (a:=1406) (b:=1406) (join_sums term (lo:=900001) (a:=703) (b:=703) r900001 r900704) (join_sums term (lo:=901407) (a:=703) (b:=703) r901407 r902110)) (join_sums term (lo:=902813) (a:=1406) (b:=1407) (join_sums term (lo:=902813) (a:=703) (b:=703) r902813 r903516) (join_sums term (lo:=904219) (a:=703) (b:=704) r904219 r904922))) (join_sums term (lo:=905626) (a:=2812) (b:=2813) (join_sums term (lo:=905626) (a:=1406) (b:=1406) (join_sums term (lo:=905626) (a:=703) (b:=703) r905626 r906329) (join_sums term (lo:=907032) (a:=703) (b:=703) r907032 r907735)) (join_sums term (lo:=908438) (a:=1406) (b:=1407) (join_sums term (lo:=908438) (a:=703) (b:=703) r908438 r909141) (join_sums term (lo:=909844) (a:=703) (b:=704) r909844 r910547)))) (join_sums term (lo:=911251) (a:=5625) (b:=5625) (join_sums term (lo:=911251) (a:=2812) (b:=2813) (join_sums term (lo:=911251) (a:=1406) (b:=1406) (join_sums term (lo:=911251) (a:=703) (b:=703) r911251 r911954) (join_sums term (lo:=912657) (a:=703) (b:=703) r912657 r913360)) (join_sums term (lo:=914063) (a:=1406) (b:=1407) (join_sums term (lo:=914063) (a:=703) (b:=703) r914063 r914766) (join_sums term (lo:=915469) (a:=703) (b:=704) r915469 r916172))) (join_sums term (lo:=916876) (a:=2812) (b:=2813) (join_sums term (lo:=916876) (a:=1406) (b:=1406) (join_sums term (lo:=916876) (a:=703) (b:=703) r916876 r917579) (join_sums term (lo:=918282) (a:=703) (b:=703) r918282 r918985)) (join_sums term (lo:=919688) (a:=1406) (b:=1407) (join_sums term (lo:=919688) (a:=703) (b:=703) r919688 r920391) (join_sums term (lo:=921094) (a:=703) (b:=704) r921094 r921797))))) (join_sums term (lo:=922501) (a:=11250) (b:=11250) (join_sums term (lo:=922501) (a:=5625) (b:=5625) (join_sums term (lo:=922501) (a:=2812) (b:=2813) (join_sums term (lo:=922501) (a:=1406) (b:=1406) (join_sums term (lo:=922501) (a:=703) (b:=703) r922501 r923204) (join_sums term (lo:=923907) (a:=703) (b:=703) r923907 r924610)) (join_sums term (lo:=925313) (a:=1406) (b:=1407) (join_sums term (lo:=925313) (a:=703) (b:=703) r925313 r926016) (join_sums term (lo:=926719) (a:=703) (b:=704) r926719 r927422))) (join_sums term (lo:=928126) (a:=2812) (b:=2813) (join_sums term (lo:=928126) (a:=1406) (b:=1406) (join_sums term (lo:=928126) (a:=703) (b:=703) r928126 r928829) (join_sums term (lo:=929532) (a:=703) (b:=703) r929532 r930235)) (join_sums term (lo:=930938) (a:=1406) (b:=1407) (join_sums term (lo:=930938) (a:=703) (b:=703) r930938 r931641) (join_sums term (lo:=932344) (a:=703) (b:=704) r932344 r933047)))) (join_sums term (lo:=933751) (a:=5625) (b:=5625) (join_sums term (lo:=933751) (a:=2812) (b:=2813) (join_sums term (lo:=933751) (a:=1406) (b:=1406) (join_sums term (lo:=933751) (a:=703) (b:=703) r933751 r934454) (join_sums term (lo:=935157) (a:=703) (b:=703) r935157 r935860)) (join_sums term (lo:=936563) (a:=1406) (b:=1407) (join_sums term (lo:=936563) (a:=703) (b:=703) r936563 r937266) (join_sums term (lo:=937969) (a:=703) (b:=704) r937969 r938672))) (join_sums term (lo:=939376) (a:=2812) (b:=2813) (join_sums term (lo:=939376) (a:=1406) (b:=1406) (join_sums term (lo:=939376) (a:=703) (b:=703) r939376 r940079) (join_sums term (lo:=940782) (a:=703) (b:=703) r940782 r941485)) (join_sums term (lo:=942188) (a:=1406) (b:=1407) (join_sums term (lo:=942188) (a:=703) (b:=703) r942188 r942891) (join_sums term (lo:=943594) (a:=703) (b:=704) r943594 r944297)))))) (join_sums term (lo:=945001) (a:=22500) (b:=22500) (join_sums term (lo:=945001) (a:=11250) (b:=11250) (join_sums term (lo:=945001) (a:=5625) (b:=5625) (join_sums term (lo:=945001) (a:=2812) (b:=2813) (join_sums term (lo:=945001) (a:=1406) (b:=1406) (join_sums term (lo:=945001) (a:=703) (b:=703) r945001 r945704) (join_sums term (lo:=946407) (a:=703) (b:=703) r946407 r947110)) (join_sums term (lo:=947813) (a:=1406) (b:=1407) (join_sums term (lo:=947813) (a:=703) (b:=703) r947813 r948516) (join_sums term (lo:=949219) (a:=703) (b:=704) r949219 r949922))) (join_sums term (lo:=950626) (a:=2812) (b:=2813) (join_sums term (lo:=950626) (a:=1406) (b:=1406) (join_sums term (lo:=950626) (a:=703) (b:=703) r950626 r951329) (join_sums term (lo:=952032) (a:=703) (b:=703) r952032 r952735)) (join_sums term (lo:=953438) (a:=1406) (b:=1407) (join_sums term (lo:=953438) (a:=703) (b:=703) r953438 r954141) (join_sums term (lo:=954844) (a:=703) (b:=704) r954844 r955547)))) (join_sums term (lo:=956251) (a:=5625) (b:=5625) (join_sums term (lo:=956251) (a:=2812) (b:=2813) (join_sums term (lo:=956251) (a:=1406) (b:=1406) (join_sums term (lo:=956251) (a:=703) (b:=703) r956251 r956954) (join_sums term (lo:=957657) (a:=703) (b:=703) r957657 r958360)) (join_sums term (lo:=959063) (a:=1406) (b:=1407) (join_sums term (lo:=959063) (a:=703) (b:=703) r959063 r959766) (join_sums term (lo:=960469) (a:=703) (b:=704) r960469 r961172))) (join_sums term (lo:=961876) (a:=2812) (b:=2813) (join_sums term (lo:=961876) (a:=1406) (b:=1406) (join_sums term (lo:=961876) (a:=703) (b:=703) r961876 r962579) (join_sums term (lo:=963282) (a:=703) (b:=703) r963282 r963985)) (join_sums term (lo:=964688) (a:=1406) (b:=1407) (join_sums term (lo:=964688) (a:=703) (b:=703) r964688 r965391) (join_sums term (lo:=966094) (a:=703) (b:=704) r966094 r966797))))) (join_sums term (lo:=967501) (a:=11250) (b:=11250) (join_sums term (lo:=967501) (a:=5625) (b:=5625) (join_sums term (lo:=967501) (a:=2812) (b:=2813) (join_sums term (lo:=967501) (a:=1406) (b:=1406) (join_sums term (lo:=967501) (a:=703) (b:=703) r967501 r968204) (join_sums term (lo:=968907) (a:=703) (b:=703) r968907 r969610)) (join_sums term (lo:=970313) (a:=1406) (b:=1407) (join_sums term (lo:=970313) (a:=703) (b:=703) r970313 r971016) (join_sums term (lo:=971719) (a:=703) (b:=704) r971719 r972422))) (join_sums term (lo:=973126) (a:=2812) (b:=2813) (join_sums term (lo:=973126) (a:=1406) (b:=1406) (join_sums term (lo:=973126) (a:=703) (b:=703) r973126 r973829) (join_sums term (lo:=974532) (a:=703) (b:=703) r974532 r975235)) (join_sums term (lo:=975938) (a:=1406) (b:=1407) (join_sums term (lo:=975938) (a:=703) (b:=703) r975938 r976641) (join_sums term (lo:=977344) (a:=703) (b:=704) r977344 r978047)))) (join_sums term (lo:=978751) (a:=5625) (b:=5625) (join_sums term (lo:=978751) (a:=2812) (b:=2813) (join_sums term (lo:=978751) (a:=1406) (b:=1406) (join_sums term (lo:=978751) (a:=703) (b:=703) r978751 r979454) (join_sums term (lo:=980157) (a:=703) (b:=703) r980157 r980860)) (join_sums term (lo:=981563) (a:=1406) (b:=1407) (join_sums term (lo:=981563) (a:=703) (b:=703) r981563 r982266) (join_sums term (lo:=982969) (a:=703) (b:=704) r982969 r983672))) (join_sums term (lo:=984376) (a:=2812) (b:=2813) (join_sums term (lo:=984376) (a:=1406) (b:=1406) (join_sums term (lo:=984376) (a:=703) (b:=703) r984376 r985079) (join_sums term (lo:=985782) (a:=703) (b:=703) r985782 r986485)) (join_sums term (lo:=987188) (a:=1406) (b:=1407) (join_sums term (lo:=987188) (a:=703) (b:=703) r987188 r987891) (join_sums term (lo:=988594) (a:=703) (b:=704) r988594 r989297)))))))

private theorem rows : blockSum term 0 990001 12311571924 :=
  join_sums term (lo:=0) (a:=900001) (b:=90000) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 990000).filter (900000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=12311571924 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=4775000)
    SparsePrimeA204.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From900000To990000
