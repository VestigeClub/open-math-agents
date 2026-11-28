import certificates.«semiprime-correction-555157672301-small»
import certificates.«semiprime-correction-204778727327-high»

/-!
# Semiprime terms at 30,110,134,441,897 for primes above 745,089 through 810,000

The sum covers 4,800 primes. Their quotient counts are checked by the
certified prime-counting table through 67,545,646.
-/
open Finset
namespace Correction30110134441897From745089To810000

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


private abbrev term := contribution 30110134441897 745089 RangePrimeA26.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 745090 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 745089 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r745090 : blockSum term 745090 507 71897594 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r745597 : blockSum term 745597 507 91007677 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r746104 : blockSum term 746104 507 93342239 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r746611 : blockSum term 746611 507 83708997 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r747118 : blockSum term 747118 507 90819656 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r747625 : blockSum term 747625 507 81207007 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r748132 : blockSum term 748132 507 90698989 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r748639 : blockSum term 748639 507 97797308 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r749146 : blockSum term 749146 507 83434676 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r749653 : blockSum term 749653 507 95283523 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r750160 : blockSum term 750160 507 71416523 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r750667 : blockSum term 750667 507 92778820 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r751174 : blockSum term 751174 507 104604663 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r751681 : blockSum term 751681 507 95031023 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r752188 : blockSum term 752188 507 87847304 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r752695 : blockSum term 752695 508 90159520 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r753203 : blockSum term 753203 507 82980957 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r753710 : blockSum term 753710 507 99516931 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r754217 : blockSum term 754217 507 94719046 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r754724 : blockSum term 754724 507 87554372 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r755231 : blockSum term 755231 507 92229418 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r755738 : blockSum term 755738 507 73260918 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r756245 : blockSum term 756245 507 89744262 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r756752 : blockSum term 756752 508 66082056 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r757260 : blockSum term 757260 507 91984661 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r757767 : blockSum term 757767 507 87205993 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r758274 : blockSum term 758274 507 91862558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r758781 : blockSum term 758781 507 87096896 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r759288 : blockSum term 759288 507 101151236 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r759795 : blockSum term 759795 507 94028138 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r760302 : blockSum term 760302 507 82222507 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r760809 : blockSum term 760809 508 93907204 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r761317 : blockSum term 761317 507 103233097 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r761824 : blockSum term 761824 507 77372354 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r762331 : blockSum term 762331 507 79663488 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r762838 : blockSum term 762838 507 86637499 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r763345 : blockSum term 763345 507 95939909 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r763852 : blockSum term 763852 507 98215598 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r764359 : blockSum term 764359 507 74779149 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r764866 : blockSum term 764866 508 107426352 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r765374 : blockSum term 765374 507 84018266 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r765881 : blockSum term 765881 507 102619555 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r766388 : blockSum term 766388 507 88565667 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r766895 : blockSum term 766895 507 81520482 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r767402 : blockSum term 767402 507 88448405 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r767909 : blockSum term 767909 507 93039527 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r768416 : blockSum term 768416 507 79037583 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r768923 : blockSum term 768923 508 90600962 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r769431 : blockSum term 769431 507 78934680 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r769938 : blockSum term 769938 507 92805670 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r770445 : blockSum term 770445 507 95059627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r770952 : blockSum term 770952 507 85730468 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r771459 : blockSum term 771459 507 87992064 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r771966 : blockSum term 771966 507 85618725 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r772473 : blockSum term 772473 507 78626838 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r772980 : blockSum term 772980 508 83200939 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r773488 : blockSum term 773488 507 94691533 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r773995 : blockSum term 773995 507 83093627 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r774502 : blockSum term 774502 507 87649898 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r775009 : blockSum term 775009 507 76067181 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r775516 : blockSum term 775516 507 78321425 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r776023 : blockSum term 776023 507 87478410 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r776530 : blockSum term 776530 507 80517212 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r777037 : blockSum term 777037 508 91963182 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r777545 : blockSum term 777545 507 82712197 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r778052 : blockSum term 778052 507 94137495 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r778559 : blockSum term 778559 507 94077117 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r779066 : blockSum term 779066 507 71085996 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r779573 : blockSum term 779573 507 93958818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r780080 : blockSum term 780080 507 68704898 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r780587 : blockSum term 780587 507 96125223 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r781094 : blockSum term 781094 508 100638112 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r781602 : blockSum term 781602 507 89142985 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r782109 : blockSum term 782109 507 82238414 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r782616 : blockSum term 782616 507 73049976 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r783123 : blockSum term 783123 507 84412370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r783630 : blockSum term 783630 507 88920570 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r784137 : blockSum term 784137 507 97973655 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r784644 : blockSum term 784644 507 75139785 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r785151 : blockSum term 785151 508 100125492 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r785659 : blockSum term 785659 507 77319833 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r786166 : blockSum term 786166 507 72725958 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r786673 : blockSum term 786673 507 86305283 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r787180 : blockSum term 787180 507 83978552 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r787687 : blockSum term 787687 507 92997325 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r788194 : blockSum term 788194 507 90672977 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r788701 : blockSum term 788701 507 88346393 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r789208 : blockSum term 789208 508 79232188 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r789716 : blockSum term 789716 507 76921262 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r790223 : blockSum term 790223 507 88178566 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r790730 : blockSum term 790730 507 90382334 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r791237 : blockSum term 791237 507 72260793 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r791744 : blockSum term 791744 507 94779060 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r792251 : blockSum term 792251 507 101483082 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r792758 : blockSum term 792758 507 67613143 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r793265 : blockSum term 793265 508 87839865 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r793773 : blockSum term 793773 507 103542056 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r794280 : blockSum term 794280 507 78731486 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r794787 : blockSum term 794787 507 74184731 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r795294 : blockSum term 795294 507 92111944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r795801 : blockSum term 795801 507 80828556 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r796308 : blockSum term 796308 507 89753037 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r796815 : blockSum term 796815 507 87458960 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r797322 : blockSum term 797322 508 82919357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r797830 : blockSum term 797830 507 91823873 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r798337 : blockSum term 798337 507 76099086 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r798844 : blockSum term 798844 507 67103479 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r799351 : blockSum term 799351 507 87180710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r799858 : blockSum term 799858 507 89358739 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r800365 : blockSum term 800365 507 96002665 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r800872 : blockSum term 800872 507 84786986 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r801379 : blockSum term 801379 508 78043700 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r801887 : blockSum term 801887 507 73537354 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r802394 : blockSum term 802394 507 77944853 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r802901 : blockSum term 802901 507 73443787 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r803408 : blockSum term 803408 507 80072131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r803915 : blockSum term 803915 507 86689881 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r804422 : blockSum term 804422 507 88855998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r804929 : blockSum term 804929 507 99902277 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r805436 : blockSum term 805436 508 84307964 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r805944 : blockSum term 805944 507 82038280 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r806451 : blockSum term 806451 507 68690488 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r806958 : blockSum term 806958 507 77505522 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r807465 : blockSum term 807465 507 77459951 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r807972 : blockSum term 807972 507 77408818 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r808479 : blockSum term 808479 507 75154262 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r808986 : blockSum term 808986 507 92777717 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r809493 : blockSum term 809493 508 83889639 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 745090 64911 11038540048 := (join_sums term (lo:=745090) (a:=32455) (b:=32456) (join_sums term (lo:=745090) (a:=16227) (b:=16228) (join_sums term (lo:=745090) (a:=8113) (b:=8114) (join_sums term (lo:=745090) (a:=4056) (b:=4057) (join_sums term (lo:=745090) (a:=2028) (b:=2028) (join_sums term (lo:=745090) (a:=1014) (b:=1014) (join_sums term (lo:=745090) (a:=507) (b:=507) r745090 r745597) (join_sums term (lo:=746104) (a:=507) (b:=507) r746104 r746611)) (join_sums term (lo:=747118) (a:=1014) (b:=1014) (join_sums term (lo:=747118) (a:=507) (b:=507) r747118 r747625) (join_sums term (lo:=748132) (a:=507) (b:=507) r748132 r748639))) (join_sums term (lo:=749146) (a:=2028) (b:=2029) (join_sums term (lo:=749146) (a:=1014) (b:=1014) (join_sums term (lo:=749146) (a:=507) (b:=507) r749146 r749653) (join_sums term (lo:=750160) (a:=507) (b:=507) r750160 r750667)) (join_sums term (lo:=751174) (a:=1014) (b:=1015) (join_sums term (lo:=751174) (a:=507) (b:=507) r751174 r751681) (join_sums term (lo:=752188) (a:=507) (b:=508) r752188 r752695)))) (join_sums term (lo:=753203) (a:=4057) (b:=4057) (join_sums term (lo:=753203) (a:=2028) (b:=2029) (join_sums term (lo:=753203) (a:=1014) (b:=1014) (join_sums term (lo:=753203) (a:=507) (b:=507) r753203 r753710) (join_sums term (lo:=754217) (a:=507) (b:=507) r754217 r754724)) (join_sums term (lo:=755231) (a:=1014) (b:=1015) (join_sums term (lo:=755231) (a:=507) (b:=507) r755231 r755738) (join_sums term (lo:=756245) (a:=507) (b:=508) r756245 r756752))) (join_sums term (lo:=757260) (a:=2028) (b:=2029) (join_sums term (lo:=757260) (a:=1014) (b:=1014) (join_sums term (lo:=757260) (a:=507) (b:=507) r757260 r757767) (join_sums term (lo:=758274) (a:=507) (b:=507) r758274 r758781)) (join_sums term (lo:=759288) (a:=1014) (b:=1015) (join_sums term (lo:=759288) (a:=507) (b:=507) r759288 r759795) (join_sums term (lo:=760302) (a:=507) (b:=508) r760302 r760809))))) (join_sums term (lo:=761317) (a:=8114) (b:=8114) (join_sums term (lo:=761317) (a:=4057) (b:=4057) (join_sums term (lo:=761317) (a:=2028) (b:=2029) (join_sums term (lo:=761317) (a:=1014) (b:=1014) (join_sums term (lo:=761317) (a:=507) (b:=507) r761317 r761824) (join_sums term (lo:=762331) (a:=507) (b:=507) r762331 r762838)) (join_sums term (lo:=763345) (a:=1014) (b:=1015) (join_sums term (lo:=763345) (a:=507) (b:=507) r763345 r763852) (join_sums term (lo:=764359) (a:=507) (b:=508) r764359 r764866))) (join_sums term (lo:=765374) (a:=2028) (b:=2029) (join_sums term (lo:=765374) (a:=1014) (b:=1014) (join_sums term (lo:=765374) (a:=507) (b:=507) r765374 r765881) (join_sums term (lo:=766388) (a:=507) (b:=507) r766388 r766895)) (join_sums term (lo:=767402) (a:=1014) (b:=1015) (join_sums term (lo:=767402) (a:=507) (b:=507) r767402 r767909) (join_sums term (lo:=768416) (a:=507) (b:=508) r768416 r768923)))) (join_sums term (lo:=769431) (a:=4057) (b:=4057) (join_sums term (lo:=769431) (a:=2028) (b:=2029) (join_sums term (lo:=769431) (a:=1014) (b:=1014) (join_sums term (lo:=769431) (a:=507) (b:=507) r769431 r769938) (join_sums term (lo:=770445) (a:=507) (b:=507) r770445 r770952)) (join_sums term (lo:=771459) (a:=1014) (b:=1015) (join_sums term (lo:=771459) (a:=507) (b:=507) r771459 r771966) (join_sums term (lo:=772473) (a:=507) (b:=508) r772473 r772980))) (join_sums term (lo:=773488) (a:=2028) (b:=2029) (join_sums term (lo:=773488) (a:=1014) (b:=1014) (join_sums term (lo:=773488) (a:=507) (b:=507) r773488 r773995) (join_sums term (lo:=774502) (a:=507) (b:=507) r774502 r775009)) (join_sums term (lo:=775516) (a:=1014) (b:=1015) (join_sums term (lo:=775516) (a:=507) (b:=507) r775516 r776023) (join_sums term (lo:=776530) (a:=507) (b:=508) r776530 r777037)))))) (join_sums term (lo:=777545) (a:=16228) (b:=16228) (join_sums term (lo:=777545) (a:=8114) (b:=8114) (join_sums term (lo:=777545) (a:=4057) (b:=4057) (join_sums term (lo:=777545) (a:=2028) (b:=2029) (join_sums term (lo:=777545) (a:=1014) (b:=1014) (join_sums term (lo:=777545) (a:=507) (b:=507) r777545 r778052) (join_sums term (lo:=778559) (a:=507) (b:=507) r778559 r779066)) (join_sums term (lo:=779573) (a:=1014) (b:=1015) (join_sums term (lo:=779573) (a:=507) (b:=507) r779573 r780080) (join_sums term (lo:=780587) (a:=507) (b:=508) r780587 r781094))) (join_sums term (lo:=781602) (a:=2028) (b:=2029) (join_sums term (lo:=781602) (a:=1014) (b:=1014) (join_sums term (lo:=781602) (a:=507) (b:=507) r781602 r782109) (join_sums term (lo:=782616) (a:=507) (b:=507) r782616 r783123)) (join_sums term (lo:=783630) (a:=1014) (b:=1015) (join_sums term (lo:=783630) (a:=507) (b:=507) r783630 r784137) (join_sums term (lo:=784644) (a:=507) (b:=508) r784644 r785151)))) (join_sums term (lo:=785659) (a:=4057) (b:=4057) (join_sums term (lo:=785659) (a:=2028) (b:=2029) (join_sums term (lo:=785659) (a:=1014) (b:=1014) (join_sums term (lo:=785659) (a:=507) (b:=507) r785659 r786166) (join_sums term (lo:=786673) (a:=507) (b:=507) r786673 r787180)) (join_sums term (lo:=787687) (a:=1014) (b:=1015) (join_sums term (lo:=787687) (a:=507) (b:=507) r787687 r788194) (join_sums term (lo:=788701) (a:=507) (b:=508) r788701 r789208))) (join_sums term (lo:=789716) (a:=2028) (b:=2029) (join_sums term (lo:=789716) (a:=1014) (b:=1014) (join_sums term (lo:=789716) (a:=507) (b:=507) r789716 r790223) (join_sums term (lo:=790730) (a:=507) (b:=507) r790730 r791237)) (join_sums term (lo:=791744) (a:=1014) (b:=1015) (join_sums term (lo:=791744) (a:=507) (b:=507) r791744 r792251) (join_sums term (lo:=792758) (a:=507) (b:=508) r792758 r793265))))) (join_sums term (lo:=793773) (a:=8114) (b:=8114) (join_sums term (lo:=793773) (a:=4057) (b:=4057) (join_sums term (lo:=793773) (a:=2028) (b:=2029) (join_sums term (lo:=793773) (a:=1014) (b:=1014) (join_sums term (lo:=793773) (a:=507) (b:=507) r793773 r794280) (join_sums term (lo:=794787) (a:=507) (b:=507) r794787 r795294)) (join_sums term (lo:=795801) (a:=1014) (b:=1015) (join_sums term (lo:=795801) (a:=507) (b:=507) r795801 r796308) (join_sums term (lo:=796815) (a:=507) (b:=508) r796815 r797322))) (join_sums term (lo:=797830) (a:=2028) (b:=2029) (join_sums term (lo:=797830) (a:=1014) (b:=1014) (join_sums term (lo:=797830) (a:=507) (b:=507) r797830 r798337) (join_sums term (lo:=798844) (a:=507) (b:=507) r798844 r799351)) (join_sums term (lo:=799858) (a:=1014) (b:=1015) (join_sums term (lo:=799858) (a:=507) (b:=507) r799858 r800365) (join_sums term (lo:=800872) (a:=507) (b:=508) r800872 r801379)))) (join_sums term (lo:=801887) (a:=4057) (b:=4057) (join_sums term (lo:=801887) (a:=2028) (b:=2029) (join_sums term (lo:=801887) (a:=1014) (b:=1014) (join_sums term (lo:=801887) (a:=507) (b:=507) r801887 r802394) (join_sums term (lo:=802901) (a:=507) (b:=507) r802901 r803408)) (join_sums term (lo:=803915) (a:=1014) (b:=1015) (join_sums term (lo:=803915) (a:=507) (b:=507) r803915 r804422) (join_sums term (lo:=804929) (a:=507) (b:=508) r804929 r805436))) (join_sums term (lo:=805944) (a:=2028) (b:=2029) (join_sums term (lo:=805944) (a:=1014) (b:=1014) (join_sums term (lo:=805944) (a:=507) (b:=507) r805944 r806451) (join_sums term (lo:=806958) (a:=507) (b:=507) r806958 r807465)) (join_sums term (lo:=807972) (a:=1014) (b:=1015) (join_sums term (lo:=807972) (a:=507) (b:=507) r807972 r808479) (join_sums term (lo:=808986) (a:=507) (b:=508) r808986 r809493)))))))

private theorem rows : blockSum term 0 810001 11038540048 :=
  join_sums term (lo:=0) (a:=745090) (b:=64911) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 810000).filter (745089 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1)))=11038540048 :=
  right_from_blocks (l:=34751024) (b:=67545646) (small:=4775000)
    RangePrimeA26.fast CheckpointA10425Slim.fast CheckpointA10425Slim.prime (RangePrimeA26.fast_correct RankWheel34751.first_anchor)
    CheckpointA10425Slim.fast_correct CheckpointA10425Slim.prime_ok (by decide) (by decide) (by decide) rows

end Correction30110134441897From745089To810000
