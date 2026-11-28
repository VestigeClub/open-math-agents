import certificates.«semiprime-correction-555157672301-middle»

/-!
# Semiprime terms at 11,092,009,835,083 for primes above 319,185 through 430,000

The sum covers 8,622 primes. Their quotient counts are checked by the
certified prime-counting table through 34,751,024.
-/
open Finset
namespace Correction11092009835083From319185To430000

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


private abbrev term := contribution 11092009835083 319185 SparsePrimeA204.fast FastDenseA26.fast FastDenseA26.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))


private theorem before : blockSum term 0 319186 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 319185 < p := by omega
  simp [term,contribution,no]

set_option maxRecDepth 5000 in
private theorem r319186 : blockSum term 319186 432 79928968 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r319618 : blockSum term 319618 433 73524114 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r320051 : blockSum term 320051 433 79730445 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r320484 : blockSum term 320484 433 64955181 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r320917 : blockSum term 320917 432 73238809 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r321349 : blockSum term 321349 433 71057094 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r321782 : blockSum term 321782 433 73051933 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r322215 : blockSum term 322215 433 77122406 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r322648 : blockSum term 322648 432 62452496 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r323080 : blockSum term 323080 433 68612014 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r323513 : blockSum term 323513 433 62295793 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r323946 : blockSum term 323946 433 66363684 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r324379 : blockSum term 324379 433 86991776 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r324812 : blockSum term 324812 433 78604824 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r325245 : blockSum term 325245 433 66109710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r325678 : blockSum term 325678 433 78411076 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r326111 : blockSum term 326111 432 57704254 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r326543 : blockSum term 326543 433 72039012 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r326976 : blockSum term 326976 433 69888808 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r327409 : blockSum term 327409 433 86224550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r327842 : blockSum term 327842 433 65612402 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r328275 : blockSum term 328275 433 67576559 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r328708 : blockSum term 328708 433 63396998 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r329141 : blockSum term 329141 433 69446963 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r329574 : blockSum term 329574 432 75478110 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r330006 : blockSum term 330006 433 79454112 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r330439 : blockSum term 330439 433 67139336 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r330872 : blockSum term 330872 433 65027009 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r331305 : blockSum term 331305 433 71039903 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r331738 : blockSum term 331738 433 70948630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r332171 : blockSum term 332171 433 66811967 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r332604 : blockSum term 332604 433 62677225 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r333037 : blockSum term 333037 432 72695616 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r333469 : blockSum term 333469 433 66559860 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r333902 : blockSum term 333902 433 64459276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r334335 : blockSum term 334335 433 72423982 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r334768 : blockSum term 334768 433 72332936 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r335201 : blockSum term 335201 433 62210361 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r335634 : blockSum term 335634 433 62137543 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r336067 : blockSum term 336067 433 66065950 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r336500 : blockSum term 336500 432 83974276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r336932 : blockSum term 336932 433 67889355 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r337365 : blockSum term 337365 433 65813442 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r337798 : blockSum term 337798 433 67725560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r338231 : blockSum term 338231 433 75608751 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r338664 : blockSum term 338664 433 55640763 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r339097 : blockSum term 339097 433 57559041 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r339530 : blockSum term 339530 433 65413701 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r339963 : blockSum term 339963 432 65331545 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r340395 : blockSum term 340395 433 69203268 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r340828 : blockSum term 340828 433 67149171 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r341261 : blockSum term 341261 433 72981256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r341694 : blockSum term 341694 433 65007825 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r342127 : blockSum term 342127 433 72801241 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r342560 : blockSum term 342560 433 58955662 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r342993 : blockSum term 342993 433 70655285 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r343426 : blockSum term 343426 432 66651094 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r343858 : blockSum term 343858 433 72438402 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r344291 : blockSum term 344291 433 56713400 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r344724 : blockSum term 344724 433 70319644 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r345157 : blockSum term 345157 433 54621283 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r345590 : blockSum term 345590 433 72100282 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r346023 : blockSum term 346023 433 81732489 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r346456 : blockSum term 346456 433 58315689 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r346889 : blockSum term 346889 432 73773976 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r347321 : blockSum term 347321 433 54294052 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r347754 : blockSum term 347754 433 67792360 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r348187 : blockSum term 348187 433 73511326 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r348620 : blockSum term 348620 433 59895705 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r349053 : blockSum term 349053 433 69470624 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r349486 : blockSum term 349486 433 63606882 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r349919 : blockSum term 349919 433 59687728 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r350352 : blockSum term 350352 432 67299250 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r350784 : blockSum term 350784 433 65303884 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r351217 : blockSum term 351217 433 67148256 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r351650 : blockSum term 351650 433 70894087 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r352083 : blockSum term 352083 433 74632941 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r352516 : blockSum term 352516 433 59256745 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r352949 : blockSum term 352949 433 59190685 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r353382 : blockSum term 353382 433 68652177 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r353815 : blockSum term 353815 432 62861458 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r354247 : blockSum term 354247 433 76107585 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r354680 : blockSum term 354680 433 79805931 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r355113 : blockSum term 355113 433 55035376 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r355546 : blockSum term 355546 433 66351917 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r355979 : blockSum term 355979 433 49232160 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r356412 : blockSum term 356412 433 52959581 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r356845 : blockSum term 356845 433 62340995 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r357278 : blockSum term 357278 432 71701118 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r357710 : blockSum term 357710 433 54663131 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r358143 : blockSum term 358143 433 67777138 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r358576 : blockSum term 358576 433 77096917 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r359009 : blockSum term 359009 433 65736678 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r359442 : blockSum term 359442 433 56282791 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r359875 : blockSum term 359875 433 56208327 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r360308 : blockSum term 360308 433 37436263 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r360741 : blockSum term 360741 432 59829185 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r361173 : blockSum term 361173 433 70960550 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r361606 : blockSum term 361606 433 63414903 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r362039 : blockSum term 362039 433 76380330 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r362472 : blockSum term 362472 433 44656813 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r362905 : blockSum term 362905 433 63195794 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r363338 : blockSum term 363338 433 74262074 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r363771 : blockSum term 363771 433 59339129 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r364204 : blockSum term 364204 432 66680096 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r364636 : blockSum term 364636 433 61054455 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r365069 : blockSum term 365069 433 66526834 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r365502 : blockSum term 365502 433 60918871 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r365935 : blockSum term 365935 433 70058906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r366368 : blockSum term 366368 433 57092135 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r366801 : blockSum term 366801 433 73581227 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r367234 : blockSum term 367234 433 60632188 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r367667 : blockSum term 367667 432 58733165 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r368099 : blockSum term 368099 433 64164427 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r368532 : blockSum term 368532 433 54933365 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r368965 : blockSum term 368965 433 53041842 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r369398 : blockSum term 369398 433 45670968 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r369831 : blockSum term 369831 433 67518042 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r370264 : blockSum term 370264 433 60142562 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r370697 : blockSum term 370697 433 40053238 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r371130 : blockSum term 371130 432 69110336 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r371562 : blockSum term 371562 433 52675383 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r371995 : blockSum term 371995 433 63505054 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r372428 : blockSum term 372428 433 67055485 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r372861 : blockSum term 372861 433 59743679 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r373294 : blockSum term 373294 433 57869490 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r373727 : blockSum term 373727 433 61408906 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r374160 : blockSum term 374160 433 50521834 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r374593 : blockSum term 374593 432 72089510 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r375025 : blockSum term 375025 433 75611544 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r375458 : blockSum term 375458 433 57546240 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r375891 : blockSum term 375891 433 59277536 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r376324 : blockSum term 376324 433 57412048 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r376757 : blockSum term 376757 433 66317558 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r377190 : blockSum term 377190 433 59077347 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r377623 : blockSum term 377623 433 51861947 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r378056 : blockSum term 378056 432 55376674 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r378488 : blockSum term 378488 433 62451276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r378921 : blockSum term 378921 433 62380773 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r379354 : blockSum term 379354 433 64091432 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r379787 : blockSum term 379787 433 60463323 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r380220 : blockSum term 380220 433 58621808 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r380653 : blockSum term 380653 433 56778182 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r381086 : blockSum term 381086 433 58488626 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r381519 : blockSum term 381519 432 56659163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r381951 : blockSum term 381951 433 49521358 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r382384 : blockSum term 382384 433 63596179 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r382817 : blockSum term 382817 433 58236791 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r383250 : blockSum term 383250 433 59933276 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r383683 : blockSum term 383683 433 65151552 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r384116 : blockSum term 384116 433 63321815 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r384549 : blockSum term 384549 433 56224170 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r384982 : blockSum term 384982 432 61427583 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r385414 : blockSum term 385414 433 59608006 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r385847 : blockSum term 385847 433 61292984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r386280 : blockSum term 386280 433 62979581 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r386713 : blockSum term 386713 433 48929768 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r387146 : blockSum term 387146 433 52371284 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r387579 : blockSum term 387579 433 52311710 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r388012 : blockSum term 388012 433 55739389 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r388445 : blockSum term 388445 432 53939379 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r388877 : blockSum term 388877 433 67784702 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r389310 : blockSum term 389310 433 53817835 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r389743 : blockSum term 389743 433 67636736 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r390176 : blockSum term 390176 433 64099466 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r390609 : blockSum term 390609 433 58836213 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r391042 : blockSum term 391042 433 62232872 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r391475 : blockSum term 391475 433 56980854 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r391908 : blockSum term 391908 432 68992996 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r392340 : blockSum term 392340 433 55138544 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r392773 : blockSum term 392773 433 70567946 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r393206 : blockSum term 393206 433 61893498 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r393639 : blockSum term 393639 433 60115357 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r394072 : blockSum term 394072 433 49755417 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r394505 : blockSum term 394505 433 58273556 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r394938 : blockSum term 394938 433 63347984 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r395371 : blockSum term 395371 432 51309676 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r395803 : blockSum term 395803 433 51251144 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r396236 : blockSum term 396236 433 63143016 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r396669 : blockSum term 396669 433 49434249 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r397102 : blockSum term 397102 433 52790978 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r397535 : blockSum term 397535 433 56139034 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r397968 : blockSum term 397968 433 64573563 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r398401 : blockSum term 398401 433 59415725 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r398834 : blockSum term 398834 432 57653389 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r399266 : blockSum term 399266 433 59287370 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r399699 : blockSum term 399699 433 55842409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r400132 : blockSum term 400132 433 50714053 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r400565 : blockSum term 400565 433 50659882 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r400998 : blockSum term 400998 433 55665624 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r401431 : blockSum term 401431 433 43811470 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r401864 : blockSum term 401864 433 55551658 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r402297 : blockSum term 402297 432 55495258 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r402729 : blockSum term 402729 433 60473250 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r403162 : blockSum term 403162 433 50338877 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r403595 : blockSum term 403595 433 58666766 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r404028 : blockSum term 404028 433 56931650 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r404461 : blockSum term 404461 433 41820907 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r404894 : blockSum term 404894 433 55141121 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r405327 : blockSum term 405327 433 60091785 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r405760 : blockSum term 405760 432 55029876 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r406192 : blockSum term 406192 433 53303169 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r406625 : blockSum term 406625 433 41605018 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r407058 : blockSum term 407058 433 58183758 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r407491 : blockSum term 407491 433 63104870 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r407924 : blockSum term 407924 433 56404272 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r408357 : blockSum term 408357 433 59660884 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r408790 : blockSum term 408790 433 49666680 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r409223 : blockSum term 409223 432 56231854 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r409655 : blockSum term 409655 433 61128477 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r410088 : blockSum term 410088 433 62712186 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r410521 : blockSum term 410521 433 47812112 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r410954 : blockSum term 410954 433 55998853 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r411387 : blockSum term 411387 433 60874073 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r411820 : blockSum term 411820 433 64097859 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r412253 : blockSum term 412253 433 50896630 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r412686 : blockSum term 412686 432 45920218 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r413118 : blockSum term 413118 433 44242180 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r413551 : blockSum term 413551 433 49106886 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r413984 : blockSum term 413984 433 60501163 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r414417 : blockSum term 414417 433 65339944 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r414850 : blockSum term 414850 433 60380252 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r415283 : blockSum term 415283 433 52162412 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r415716 : blockSum term 415716 433 50487802 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r416149 : blockSum term 416149 432 61821505 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r416581 : blockSum term 416581 433 37380580 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r417014 : blockSum term 417014 433 55204794 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r417447 : blockSum term 417447 433 58392965 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r417880 : blockSum term 417880 433 58333356 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r418313 : blockSum term 418313 433 51800612 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r418746 : blockSum term 418746 433 61451054 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r419179 : blockSum term 419179 433 64610823 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r419612 : blockSum term 419612 432 46797639 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r420044 : blockSum term 420044 433 53195887 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r420477 : blockSum term 420477 433 51535029 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r420910 : blockSum term 420910 433 51483793 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r421343 : blockSum term 421343 433 56252227 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r421776 : blockSum term 421776 433 48165805 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r422209 : blockSum term 422209 433 51329560 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r422642 : blockSum term 422642 433 54481459 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r423075 : blockSum term 423075 432 64032491 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r423507 : blockSum term 423507 433 49576409 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r423940 : blockSum term 423940 433 60711916 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r424373 : blockSum term 424373 433 47880463 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r424806 : blockSum term 424806 433 55808651 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r425239 : blockSum term 425239 433 52566841 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r425672 : blockSum term 425672 433 50918976 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r426105 : blockSum term 426105 433 38153226 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r426538 : blockSum term 426538 432 57173622 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r426970 : blockSum term 426970 433 52356673 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r427403 : blockSum term 427403 433 50723648 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r427836 : blockSum term 427836 433 60170040 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r428269 : blockSum term 428269 433 50615802 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r428702 : blockSum term 428702 433 39507355 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r429135 : blockSum term 429135 433 63146709 := by unfold blockSum; decide +kernel

set_option maxRecDepth 5000 in
private theorem r429568 : blockSum term 429568 433 64660690 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem interval : blockSum term 319186 110815 15667002090 := (join_sums term (lo:=319186) (a:=55407) (b:=55408) (join_sums term (lo:=319186) (a:=27703) (b:=27704) (join_sums term (lo:=319186) (a:=13851) (b:=13852) (join_sums term (lo:=319186) (a:=6925) (b:=6926) (join_sums term (lo:=319186) (a:=3462) (b:=3463) (join_sums term (lo:=319186) (a:=1731) (b:=1731) (join_sums term (lo:=319186) (a:=865) (b:=866) (join_sums term (lo:=319186) (a:=432) (b:=433) r319186 r319618) (join_sums term (lo:=320051) (a:=433) (b:=433) r320051 r320484)) (join_sums term (lo:=320917) (a:=865) (b:=866) (join_sums term (lo:=320917) (a:=432) (b:=433) r320917 r321349) (join_sums term (lo:=321782) (a:=433) (b:=433) r321782 r322215))) (join_sums term (lo:=322648) (a:=1731) (b:=1732) (join_sums term (lo:=322648) (a:=865) (b:=866) (join_sums term (lo:=322648) (a:=432) (b:=433) r322648 r323080) (join_sums term (lo:=323513) (a:=433) (b:=433) r323513 r323946)) (join_sums term (lo:=324379) (a:=866) (b:=866) (join_sums term (lo:=324379) (a:=433) (b:=433) r324379 r324812) (join_sums term (lo:=325245) (a:=433) (b:=433) r325245 r325678)))) (join_sums term (lo:=326111) (a:=3463) (b:=3463) (join_sums term (lo:=326111) (a:=1731) (b:=1732) (join_sums term (lo:=326111) (a:=865) (b:=866) (join_sums term (lo:=326111) (a:=432) (b:=433) r326111 r326543) (join_sums term (lo:=326976) (a:=433) (b:=433) r326976 r327409)) (join_sums term (lo:=327842) (a:=866) (b:=866) (join_sums term (lo:=327842) (a:=433) (b:=433) r327842 r328275) (join_sums term (lo:=328708) (a:=433) (b:=433) r328708 r329141))) (join_sums term (lo:=329574) (a:=1731) (b:=1732) (join_sums term (lo:=329574) (a:=865) (b:=866) (join_sums term (lo:=329574) (a:=432) (b:=433) r329574 r330006) (join_sums term (lo:=330439) (a:=433) (b:=433) r330439 r330872)) (join_sums term (lo:=331305) (a:=866) (b:=866) (join_sums term (lo:=331305) (a:=433) (b:=433) r331305 r331738) (join_sums term (lo:=332171) (a:=433) (b:=433) r332171 r332604))))) (join_sums term (lo:=333037) (a:=6926) (b:=6926) (join_sums term (lo:=333037) (a:=3463) (b:=3463) (join_sums term (lo:=333037) (a:=1731) (b:=1732) (join_sums term (lo:=333037) (a:=865) (b:=866) (join_sums term (lo:=333037) (a:=432) (b:=433) r333037 r333469) (join_sums term (lo:=333902) (a:=433) (b:=433) r333902 r334335)) (join_sums term (lo:=334768) (a:=866) (b:=866) (join_sums term (lo:=334768) (a:=433) (b:=433) r334768 r335201) (join_sums term (lo:=335634) (a:=433) (b:=433) r335634 r336067))) (join_sums term (lo:=336500) (a:=1731) (b:=1732) (join_sums term (lo:=336500) (a:=865) (b:=866) (join_sums term (lo:=336500) (a:=432) (b:=433) r336500 r336932) (join_sums term (lo:=337365) (a:=433) (b:=433) r337365 r337798)) (join_sums term (lo:=338231) (a:=866) (b:=866) (join_sums term (lo:=338231) (a:=433) (b:=433) r338231 r338664) (join_sums term (lo:=339097) (a:=433) (b:=433) r339097 r339530)))) (join_sums term (lo:=339963) (a:=3463) (b:=3463) (join_sums term (lo:=339963) (a:=1731) (b:=1732) (join_sums term (lo:=339963) (a:=865) (b:=866) (join_sums term (lo:=339963) (a:=432) (b:=433) r339963 r340395) (join_sums term (lo:=340828) (a:=433) (b:=433) r340828 r341261)) (join_sums term (lo:=341694) (a:=866) (b:=866) (join_sums term (lo:=341694) (a:=433) (b:=433) r341694 r342127) (join_sums term (lo:=342560) (a:=433) (b:=433) r342560 r342993))) (join_sums term (lo:=343426) (a:=1731) (b:=1732) (join_sums term (lo:=343426) (a:=865) (b:=866) (join_sums term (lo:=343426) (a:=432) (b:=433) r343426 r343858) (join_sums term (lo:=344291) (a:=433) (b:=433) r344291 r344724)) (join_sums term (lo:=345157) (a:=866) (b:=866) (join_sums term (lo:=345157) (a:=433) (b:=433) r345157 r345590) (join_sums term (lo:=346023) (a:=433) (b:=433) r346023 r346456)))))) (join_sums term (lo:=346889) (a:=13852) (b:=13852) (join_sums term (lo:=346889) (a:=6926) (b:=6926) (join_sums term (lo:=346889) (a:=3463) (b:=3463) (join_sums term (lo:=346889) (a:=1731) (b:=1732) (join_sums term (lo:=346889) (a:=865) (b:=866) (join_sums term (lo:=346889) (a:=432) (b:=433) r346889 r347321) (join_sums term (lo:=347754) (a:=433) (b:=433) r347754 r348187)) (join_sums term (lo:=348620) (a:=866) (b:=866) (join_sums term (lo:=348620) (a:=433) (b:=433) r348620 r349053) (join_sums term (lo:=349486) (a:=433) (b:=433) r349486 r349919))) (join_sums term (lo:=350352) (a:=1731) (b:=1732) (join_sums term (lo:=350352) (a:=865) (b:=866) (join_sums term (lo:=350352) (a:=432) (b:=433) r350352 r350784) (join_sums term (lo:=351217) (a:=433) (b:=433) r351217 r351650)) (join_sums term (lo:=352083) (a:=866) (b:=866) (join_sums term (lo:=352083) (a:=433) (b:=433) r352083 r352516) (join_sums term (lo:=352949) (a:=433) (b:=433) r352949 r353382)))) (join_sums term (lo:=353815) (a:=3463) (b:=3463) (join_sums term (lo:=353815) (a:=1731) (b:=1732) (join_sums term (lo:=353815) (a:=865) (b:=866) (join_sums term (lo:=353815) (a:=432) (b:=433) r353815 r354247) (join_sums term (lo:=354680) (a:=433) (b:=433) r354680 r355113)) (join_sums term (lo:=355546) (a:=866) (b:=866) (join_sums term (lo:=355546) (a:=433) (b:=433) r355546 r355979) (join_sums term (lo:=356412) (a:=433) (b:=433) r356412 r356845))) (join_sums term (lo:=357278) (a:=1731) (b:=1732) (join_sums term (lo:=357278) (a:=865) (b:=866) (join_sums term (lo:=357278) (a:=432) (b:=433) r357278 r357710) (join_sums term (lo:=358143) (a:=433) (b:=433) r358143 r358576)) (join_sums term (lo:=359009) (a:=866) (b:=866) (join_sums term (lo:=359009) (a:=433) (b:=433) r359009 r359442) (join_sums term (lo:=359875) (a:=433) (b:=433) r359875 r360308))))) (join_sums term (lo:=360741) (a:=6926) (b:=6926) (join_sums term (lo:=360741) (a:=3463) (b:=3463) (join_sums term (lo:=360741) (a:=1731) (b:=1732) (join_sums term (lo:=360741) (a:=865) (b:=866) (join_sums term (lo:=360741) (a:=432) (b:=433) r360741 r361173) (join_sums term (lo:=361606) (a:=433) (b:=433) r361606 r362039)) (join_sums term (lo:=362472) (a:=866) (b:=866) (join_sums term (lo:=362472) (a:=433) (b:=433) r362472 r362905) (join_sums term (lo:=363338) (a:=433) (b:=433) r363338 r363771))) (join_sums term (lo:=364204) (a:=1731) (b:=1732) (join_sums term (lo:=364204) (a:=865) (b:=866) (join_sums term (lo:=364204) (a:=432) (b:=433) r364204 r364636) (join_sums term (lo:=365069) (a:=433) (b:=433) r365069 r365502)) (join_sums term (lo:=365935) (a:=866) (b:=866) (join_sums term (lo:=365935) (a:=433) (b:=433) r365935 r366368) (join_sums term (lo:=366801) (a:=433) (b:=433) r366801 r367234)))) (join_sums term (lo:=367667) (a:=3463) (b:=3463) (join_sums term (lo:=367667) (a:=1731) (b:=1732) (join_sums term (lo:=367667) (a:=865) (b:=866) (join_sums term (lo:=367667) (a:=432) (b:=433) r367667 r368099) (join_sums term (lo:=368532) (a:=433) (b:=433) r368532 r368965)) (join_sums term (lo:=369398) (a:=866) (b:=866) (join_sums term (lo:=369398) (a:=433) (b:=433) r369398 r369831) (join_sums term (lo:=370264) (a:=433) (b:=433) r370264 r370697))) (join_sums term (lo:=371130) (a:=1731) (b:=1732) (join_sums term (lo:=371130) (a:=865) (b:=866) (join_sums term (lo:=371130) (a:=432) (b:=433) r371130 r371562) (join_sums term (lo:=371995) (a:=433) (b:=433) r371995 r372428)) (join_sums term (lo:=372861) (a:=866) (b:=866) (join_sums term (lo:=372861) (a:=433) (b:=433) r372861 r373294) (join_sums term (lo:=373727) (a:=433) (b:=433) r373727 r374160))))))) (join_sums term (lo:=374593) (a:=27704) (b:=27704) (join_sums term (lo:=374593) (a:=13852) (b:=13852) (join_sums term (lo:=374593) (a:=6926) (b:=6926) (join_sums term (lo:=374593) (a:=3463) (b:=3463) (join_sums term (lo:=374593) (a:=1731) (b:=1732) (join_sums term (lo:=374593) (a:=865) (b:=866) (join_sums term (lo:=374593) (a:=432) (b:=433) r374593 r375025) (join_sums term (lo:=375458) (a:=433) (b:=433) r375458 r375891)) (join_sums term (lo:=376324) (a:=866) (b:=866) (join_sums term (lo:=376324) (a:=433) (b:=433) r376324 r376757) (join_sums term (lo:=377190) (a:=433) (b:=433) r377190 r377623))) (join_sums term (lo:=378056) (a:=1731) (b:=1732) (join_sums term (lo:=378056) (a:=865) (b:=866) (join_sums term (lo:=378056) (a:=432) (b:=433) r378056 r378488) (join_sums term (lo:=378921) (a:=433) (b:=433) r378921 r379354)) (join_sums term (lo:=379787) (a:=866) (b:=866) (join_sums term (lo:=379787) (a:=433) (b:=433) r379787 r380220) (join_sums term (lo:=380653) (a:=433) (b:=433) r380653 r381086)))) (join_sums term (lo:=381519) (a:=3463) (b:=3463) (join_sums term (lo:=381519) (a:=1731) (b:=1732) (join_sums term (lo:=381519) (a:=865) (b:=866) (join_sums term (lo:=381519) (a:=432) (b:=433) r381519 r381951) (join_sums term (lo:=382384) (a:=433) (b:=433) r382384 r382817)) (join_sums term (lo:=383250) (a:=866) (b:=866) (join_sums term (lo:=383250) (a:=433) (b:=433) r383250 r383683) (join_sums term (lo:=384116) (a:=433) (b:=433) r384116 r384549))) (join_sums term (lo:=384982) (a:=1731) (b:=1732) (join_sums term (lo:=384982) (a:=865) (b:=866) (join_sums term (lo:=384982) (a:=432) (b:=433) r384982 r385414) (join_sums term (lo:=385847) (a:=433) (b:=433) r385847 r386280)) (join_sums term (lo:=386713) (a:=866) (b:=866) (join_sums term (lo:=386713) (a:=433) (b:=433) r386713 r387146) (join_sums term (lo:=387579) (a:=433) (b:=433) r387579 r388012))))) (join_sums term (lo:=388445) (a:=6926) (b:=6926) (join_sums term (lo:=388445) (a:=3463) (b:=3463) (join_sums term (lo:=388445) (a:=1731) (b:=1732) (join_sums term (lo:=388445) (a:=865) (b:=866) (join_sums term (lo:=388445) (a:=432) (b:=433) r388445 r388877) (join_sums term (lo:=389310) (a:=433) (b:=433) r389310 r389743)) (join_sums term (lo:=390176) (a:=866) (b:=866) (join_sums term (lo:=390176) (a:=433) (b:=433) r390176 r390609) (join_sums term (lo:=391042) (a:=433) (b:=433) r391042 r391475))) (join_sums term (lo:=391908) (a:=1731) (b:=1732) (join_sums term (lo:=391908) (a:=865) (b:=866) (join_sums term (lo:=391908) (a:=432) (b:=433) r391908 r392340) (join_sums term (lo:=392773) (a:=433) (b:=433) r392773 r393206)) (join_sums term (lo:=393639) (a:=866) (b:=866) (join_sums term (lo:=393639) (a:=433) (b:=433) r393639 r394072) (join_sums term (lo:=394505) (a:=433) (b:=433) r394505 r394938)))) (join_sums term (lo:=395371) (a:=3463) (b:=3463) (join_sums term (lo:=395371) (a:=1731) (b:=1732) (join_sums term (lo:=395371) (a:=865) (b:=866) (join_sums term (lo:=395371) (a:=432) (b:=433) r395371 r395803) (join_sums term (lo:=396236) (a:=433) (b:=433) r396236 r396669)) (join_sums term (lo:=397102) (a:=866) (b:=866) (join_sums term (lo:=397102) (a:=433) (b:=433) r397102 r397535) (join_sums term (lo:=397968) (a:=433) (b:=433) r397968 r398401))) (join_sums term (lo:=398834) (a:=1731) (b:=1732) (join_sums term (lo:=398834) (a:=865) (b:=866) (join_sums term (lo:=398834) (a:=432) (b:=433) r398834 r399266) (join_sums term (lo:=399699) (a:=433) (b:=433) r399699 r400132)) (join_sums term (lo:=400565) (a:=866) (b:=866) (join_sums term (lo:=400565) (a:=433) (b:=433) r400565 r400998) (join_sums term (lo:=401431) (a:=433) (b:=433) r401431 r401864)))))) (join_sums term (lo:=402297) (a:=13852) (b:=13852) (join_sums term (lo:=402297) (a:=6926) (b:=6926) (join_sums term (lo:=402297) (a:=3463) (b:=3463) (join_sums term (lo:=402297) (a:=1731) (b:=1732) (join_sums term (lo:=402297) (a:=865) (b:=866) (join_sums term (lo:=402297) (a:=432) (b:=433) r402297 r402729) (join_sums term (lo:=403162) (a:=433) (b:=433) r403162 r403595)) (join_sums term (lo:=404028) (a:=866) (b:=866) (join_sums term (lo:=404028) (a:=433) (b:=433) r404028 r404461) (join_sums term (lo:=404894) (a:=433) (b:=433) r404894 r405327))) (join_sums term (lo:=405760) (a:=1731) (b:=1732) (join_sums term (lo:=405760) (a:=865) (b:=866) (join_sums term (lo:=405760) (a:=432) (b:=433) r405760 r406192) (join_sums term (lo:=406625) (a:=433) (b:=433) r406625 r407058)) (join_sums term (lo:=407491) (a:=866) (b:=866) (join_sums term (lo:=407491) (a:=433) (b:=433) r407491 r407924) (join_sums term (lo:=408357) (a:=433) (b:=433) r408357 r408790)))) (join_sums term (lo:=409223) (a:=3463) (b:=3463) (join_sums term (lo:=409223) (a:=1731) (b:=1732) (join_sums term (lo:=409223) (a:=865) (b:=866) (join_sums term (lo:=409223) (a:=432) (b:=433) r409223 r409655) (join_sums term (lo:=410088) (a:=433) (b:=433) r410088 r410521)) (join_sums term (lo:=410954) (a:=866) (b:=866) (join_sums term (lo:=410954) (a:=433) (b:=433) r410954 r411387) (join_sums term (lo:=411820) (a:=433) (b:=433) r411820 r412253))) (join_sums term (lo:=412686) (a:=1731) (b:=1732) (join_sums term (lo:=412686) (a:=865) (b:=866) (join_sums term (lo:=412686) (a:=432) (b:=433) r412686 r413118) (join_sums term (lo:=413551) (a:=433) (b:=433) r413551 r413984)) (join_sums term (lo:=414417) (a:=866) (b:=866) (join_sums term (lo:=414417) (a:=433) (b:=433) r414417 r414850) (join_sums term (lo:=415283) (a:=433) (b:=433) r415283 r415716))))) (join_sums term (lo:=416149) (a:=6926) (b:=6926) (join_sums term (lo:=416149) (a:=3463) (b:=3463) (join_sums term (lo:=416149) (a:=1731) (b:=1732) (join_sums term (lo:=416149) (a:=865) (b:=866) (join_sums term (lo:=416149) (a:=432) (b:=433) r416149 r416581) (join_sums term (lo:=417014) (a:=433) (b:=433) r417014 r417447)) (join_sums term (lo:=417880) (a:=866) (b:=866) (join_sums term (lo:=417880) (a:=433) (b:=433) r417880 r418313) (join_sums term (lo:=418746) (a:=433) (b:=433) r418746 r419179))) (join_sums term (lo:=419612) (a:=1731) (b:=1732) (join_sums term (lo:=419612) (a:=865) (b:=866) (join_sums term (lo:=419612) (a:=432) (b:=433) r419612 r420044) (join_sums term (lo:=420477) (a:=433) (b:=433) r420477 r420910)) (join_sums term (lo:=421343) (a:=866) (b:=866) (join_sums term (lo:=421343) (a:=433) (b:=433) r421343 r421776) (join_sums term (lo:=422209) (a:=433) (b:=433) r422209 r422642)))) (join_sums term (lo:=423075) (a:=3463) (b:=3463) (join_sums term (lo:=423075) (a:=1731) (b:=1732) (join_sums term (lo:=423075) (a:=865) (b:=866) (join_sums term (lo:=423075) (a:=432) (b:=433) r423075 r423507) (join_sums term (lo:=423940) (a:=433) (b:=433) r423940 r424373)) (join_sums term (lo:=424806) (a:=866) (b:=866) (join_sums term (lo:=424806) (a:=433) (b:=433) r424806 r425239) (join_sums term (lo:=425672) (a:=433) (b:=433) r425672 r426105))) (join_sums term (lo:=426538) (a:=1731) (b:=1732) (join_sums term (lo:=426538) (a:=865) (b:=866) (join_sums term (lo:=426538) (a:=432) (b:=433) r426538 r426970) (join_sums term (lo:=427403) (a:=433) (b:=433) r427403 r427836)) (join_sums term (lo:=428269) (a:=866) (b:=866) (join_sums term (lo:=428269) (a:=433) (b:=433) r428269 r428702) (join_sums term (lo:=429135) (a:=433) (b:=433) r429135 r429568))))))))

private theorem rows : blockSum term 0 430001 15667002090 :=
  join_sums term (lo:=0) (a:=319186) (b:=110815) before interval

theorem interval_sum :
    (∑ p ∈ (Nat.primesLE 430000).filter (319185 < ·),
      (Nat.primeCounting (11092009835083/p) - Nat.primeCounting (p-1)))=15667002090 :=
  right_from_blocks (l:=0) (b:=34751024) (small:=745089)
    SparsePrimeA204.fast FastDenseA26.fast FastDenseA26.prime (fun n _ hn => SparsePrimeA204.fast_correct n hn)
    FastDenseA26.fast_correct FastDenseA26.prime_ok (by decide) (by decide) (by decide) rows

end Correction11092009835083From319185To430000
