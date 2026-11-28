import certificates.«prime-table-through-9223368»

/-!
# Semiprime correction above 4,500,000 through 5,487,270 at 30,110,134,441,897

The proof uses a shared certified prime-counting table for every prime and quotient.
-/
open Finset
namespace CorrectionHigh30

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

private abbrev tab := CheckpointA28006Slim.fast

private abbrev prime := CheckpointA28006Slim.prime
private theorem prime_ok (n : ℕ) (hn : n≤9223368) : prime n=true ↔ n.Prime := CheckpointA28006Slim.prime_ok n hn

private abbrev term := contribution 30110134441897 4500000 tab prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))

private theorem before : blockSum term 0 4500001 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 4500000 < p := by omega
  simp [term,contribution,no]

private theorem block4500001 : blockSum term 4500001 964 9439863 := by unfold blockSum; decide +kernel

private theorem block4500965 : blockSum term 4500965 964 8022160 := by unfold blockSum; decide +kernel

private theorem block4501929 : blockSum term 4501929 964 9138460 := by unfold blockSum; decide +kernel

private theorem block4502893 : blockSum term 4502893 964 9409180 := by unfold blockSum; decide +kernel

private theorem block4503857 : blockSum term 4503857 964 9258635 := by unfold blockSum; decide +kernel

private theorem block4504821 : blockSum term 4504821 964 9948780 := by unfold blockSum; decide +kernel

private theorem block4505785 : blockSum term 4505785 964 8817942 := by unfold blockSum; decide +kernel

private theorem block4506749 : blockSum term 4506749 965 7830046 := by unfold blockSum; decide +kernel

private theorem block4507714 : blockSum term 4507714 964 8101210 := by unfold blockSum; decide +kernel

private theorem block4508678 : blockSum term 4508678 964 8511059 := by unfold blockSum; decide +kernel

private theorem block4509642 : blockSum term 4509642 964 7944464 := by unfold blockSum; decide +kernel

private theorem block4510606 : blockSum term 4510606 964 8910664 := by unfold blockSum; decide +kernel

private theorem block4511570 : blockSum term 4511570 964 7788138 := by unfold blockSum; decide +kernel

private theorem block4512534 : blockSum term 4512534 964 8474338 := by unfold blockSum; decide +kernel

private theorem block4513498 : blockSum term 4513498 964 8603931 := by unfold blockSum; decide +kernel

private theorem block4514462 : blockSum term 4514462 965 9149079 := by unfold blockSum; decide +kernel

private theorem block4515427 : blockSum term 4515427 964 8446013 := by unfold blockSum; decide +kernel

private theorem block4516391 : blockSum term 4516391 964 8575494 := by unfold blockSum; decide +kernel

private theorem block4517355 : blockSum term 4517355 964 8427663 := by unfold blockSum; decide +kernel

private theorem block4518319 : blockSum term 4518319 964 8280686 := by unfold blockSum; decide +kernel

private theorem block4519283 : blockSum term 4519283 964 9511843 := by unfold blockSum; decide +kernel

private theorem block4520247 : blockSum term 4520247 964 7711233 := by unfold blockSum; decide +kernel

private theorem block4521211 : blockSum term 4521211 964 8803178 := by unfold blockSum; decide +kernel

private theorem block4522175 : blockSum term 4522175 965 8244489 := by unfold blockSum; decide +kernel

private theorem block4523140 : blockSum term 4523140 964 8509819 := by unfold blockSum; decide +kernel

private theorem block4524104 : blockSum term 4524104 964 7403664 := by unfold blockSum; decide +kernel

private theorem block4525068 : blockSum term 4525068 964 8765663 := by unfold blockSum; decide +kernel

private theorem block4526032 : blockSum term 4526032 964 9712828 := by unfold blockSum; decide +kernel

private theorem block4526996 : blockSum term 4526996 964 8062239 := by unfold blockSum; decide +kernel

private theorem block4527960 : blockSum term 4527960 964 8463602 := by unfold blockSum; decide +kernel

private theorem block4528924 : blockSum term 4528924 964 8999919 := by unfold blockSum; decide +kernel

private theorem block4529888 : blockSum term 4529888 965 8988966 := by unfold blockSum; decide +kernel

private theorem block4530853 : blockSum term 4530853 964 7890663 := by unfold blockSum; decide +kernel

private theorem block4531817 : blockSum term 4531817 964 7882296 := by unfold blockSum; decide +kernel

private theorem block4532781 : blockSum term 4532781 964 8959495 := by unfold blockSum; decide +kernel

private theorem block4533745 : blockSum term 4533745 964 7728697 := by unfold blockSum; decide +kernel

private theorem block4534709 : blockSum term 4534709 964 8532549 := by unfold blockSum; decide +kernel

private theorem block4535673 : blockSum term 4535673 964 7981942 := by unfold blockSum; decide +kernel

private theorem block4536637 : blockSum term 4536637 964 8108412 := by unfold blockSum; decide +kernel

private theorem block4537601 : blockSum term 4537601 965 7964509 := by unfold blockSum; decide +kernel

private theorem block4538566 : blockSum term 4538566 964 7956155 := by unfold blockSum; decide +kernel

private theorem block4539530 : blockSum term 4539530 964 9429094 := by unfold blockSum; decide +kernel

private theorem block4540494 : blockSum term 4540494 964 8476536 := by unfold blockSum; decide +kernel

private theorem block4541458 : blockSum term 4541458 964 8332541 := by unfold blockSum; decide +kernel

private theorem block4542422 : blockSum term 4542422 964 8457097 := by unfold blockSum; decide +kernel

private theorem block4543386 : blockSum term 4543386 964 8179353 := by unfold blockSum; decide +kernel

private theorem block4544350 : blockSum term 4544350 964 8572060 := by unfold blockSum; decide +kernel

private theorem block4545314 : blockSum term 4545314 965 9365006 := by unfold blockSum; decide +kernel

private theorem block4546279 : blockSum term 4546279 964 8819662 := by unfold blockSum; decide +kernel

private theorem block4547243 : blockSum term 4547243 964 8009317 := by unfold blockSum; decide +kernel

private theorem block4548207 : blockSum term 4548207 964 7067446 := by unfold blockSum; decide +kernel

private theorem block4549171 : blockSum term 4549171 964 7858702 := by unfold blockSum; decide +kernel

private theorem block4550135 : blockSum term 4550135 964 8780988 := by unfold blockSum; decide +kernel

private theorem block4551099 : blockSum term 4551099 964 7840348 := by unfold blockSum; decide +kernel

private theorem block4552063 : blockSum term 4552063 964 9025908 := by unfold blockSum; decide +kernel

private theorem block4553027 : blockSum term 4553027 965 9809547 := by unfold blockSum; decide +kernel

private theorem block4553992 : blockSum term 4553992 964 8606370 := by unfold blockSum; decide +kernel

private theorem block4554956 : blockSum term 4554956 964 9125169 := by unfold blockSum; decide +kernel

private theorem block4555920 : blockSum term 4555920 964 8057414 := by unfold blockSum; decide +kernel

private theorem block4556884 : blockSum term 4556884 964 7652936 := by unfold blockSum; decide +kernel

private theorem block4557848 : blockSum term 4557848 964 7380422 := by unfold blockSum; decide +kernel

private theorem block4558812 : blockSum term 4558812 964 7767030 := by unfold blockSum; decide +kernel

private theorem block4559776 : blockSum term 4559776 964 7758329 := by unfold blockSum; decide +kernel

private theorem block4560740 : blockSum term 4560740 965 8799866 := by unfold blockSum; decide +kernel

private theorem block4561705 : blockSum term 4561705 964 8265041 := by unfold blockSum; decide +kernel

private theorem block4562669 : blockSum term 4562669 964 10089376 := by unfold blockSum; decide +kernel

private theorem block4563633 : blockSum term 4563633 964 8113891 := by unfold blockSum; decide +kernel

private theorem block4564597 : blockSum term 4564597 964 8366241 := by unfold blockSum; decide +kernel

private theorem block4565561 : blockSum term 4565561 964 8356483 := by unfold blockSum; decide +kernel

private theorem block4566525 : blockSum term 4566525 964 8476761 := by unfold blockSum; decide +kernel

private theorem block4567489 : blockSum term 4567489 964 8727205 := by unfold blockSum; decide +kernel

private theorem block4568453 : blockSum term 4568453 965 8457507 := by unfold blockSum; decide +kernel

private theorem block4569418 : blockSum term 4569418 964 7278269 := by unfold blockSum; decide +kernel

private theorem block4570382 : blockSum term 4570382 964 8178868 := by unfold blockSum; decide +kernel

private theorem block4571346 : blockSum term 4571346 964 7390986 := by unfold blockSum; decide +kernel

private theorem block4572310 : blockSum term 4572310 964 7253328 := by unfold blockSum; decide +kernel

private theorem block4573274 : blockSum term 4573274 964 8408816 := by unfold blockSum; decide +kernel

private theorem block4574238 : blockSum term 4574238 964 8398199 := by unfold blockSum; decide +kernel

private theorem block4575202 : blockSum term 4575202 964 8129824 := by unfold blockSum; decide +kernel

private theorem block4576166 : blockSum term 4576166 965 8635640 := by unfold blockSum; decide +kernel

private theorem block4577131 : blockSum term 4577131 964 7724622 := by unfold blockSum; decide +kernel

private theorem block4578095 : blockSum term 4578095 964 9129964 := by unfold blockSum; decide +kernel

private theorem block4579059 : blockSum term 4579059 964 8219326 := by unfold blockSum; decide +kernel

private theorem block4580023 : blockSum term 4580023 964 7568362 := by unfold blockSum; decide +kernel

private theorem block4580987 : blockSum term 4580987 964 7944240 := by unfold blockSum; decide +kernel

private theorem block4581951 : blockSum term 4581951 964 8190681 := by unfold blockSum; decide +kernel

private theorem block4582915 : blockSum term 4582915 964 8436463 := by unfold blockSum; decide +kernel

private theorem block4583879 : blockSum term 4583879 965 8426326 := by unfold blockSum; decide +kernel

private theorem block4584844 : blockSum term 4584844 964 7268941 := by unfold blockSum; decide +kernel

private theorem block4585808 : blockSum term 4585808 964 7260656 := by unfold blockSum; decide +kernel

private theorem block4586772 : blockSum term 4586772 964 8906468 := by unfold blockSum; decide +kernel

private theorem block4587736 : blockSum term 4587736 964 7116868 := by unfold blockSum; decide +kernel

private theorem block4588700 : blockSum term 4588700 964 7616155 := by unfold blockSum; decide +kernel

private theorem block4589664 : blockSum term 4589664 964 7986982 := by unfold blockSum; decide +kernel

private theorem block4590628 : blockSum term 4590628 964 8989531 := by unfold blockSum; decide +kernel

private theorem block4591592 : blockSum term 4591592 965 7587882 := by unfold blockSum; decide +kernel

private theorem block4592557 : blockSum term 4592557 964 8715903 := by unfold blockSum; decide +kernel

private theorem block4593521 : blockSum term 4593521 964 7821789 := by unfold blockSum; decide +kernel

private theorem block4594485 : blockSum term 4594485 964 8317182 := by unfold blockSum; decide +kernel

private theorem block4595449 : blockSum term 4595449 964 8934971 := by unfold blockSum; decide +kernel

private theorem block4596413 : blockSum term 4596413 964 7039535 := by unfold blockSum; decide +kernel

private theorem block4597377 : blockSum term 4597377 964 8035952 := by unfold blockSum; decide +kernel

private theorem block4598341 : blockSum term 4598341 964 7273953 := by unfold blockSum; decide +kernel

private theorem block4599305 : blockSum term 4599305 965 7139814 := by unfold blockSum; decide +kernel

private theorem block4600270 : blockSum term 4600270 964 7632376 := by unfold blockSum; decide +kernel

private theorem block4601234 : blockSum term 4601234 964 7373248 := by unfold blockSum; decide +kernel

private theorem block4602198 : blockSum term 4602198 964 8362771 := by unfold blockSum; decide +kernel

private theorem block4603162 : blockSum term 4603162 964 7480000 := by unfold blockSum; decide +kernel

private theorem block4604126 : blockSum term 4604126 964 8342691 := by unfold blockSum; decide +kernel

private theorem block4605090 : blockSum term 4605090 964 7462094 := by unfold blockSum; decide +kernel

private theorem block4606054 : blockSum term 4606054 964 7701139 := by unfold blockSum; decide +kernel

private theorem block4607018 : blockSum term 4607018 965 8684277 := by unfold blockSum; decide +kernel

private theorem block4607983 : blockSum term 4607983 964 7930536 := by unfold blockSum; decide +kernel

private theorem block4608947 : blockSum term 4608947 964 8663998 := by unfold blockSum; decide +kernel

private theorem block4609911 : blockSum term 4609911 964 8034085 := by unfold blockSum; decide +kernel

private theorem block4610875 : blockSum term 4610875 964 7777703 := by unfold blockSum; decide +kernel

private theorem block4611839 : blockSum term 4611839 964 7767638 := by unfold blockSum; decide +kernel

private theorem block4612803 : blockSum term 4612803 964 8250963 := by unfold blockSum; decide +kernel

private theorem block4613767 : blockSum term 4613767 964 6888006 := by unfold blockSum; decide +kernel

private theorem block4614731 : blockSum term 4614731 965 7248415 := by unfold blockSum; decide +kernel

private theorem block4615696 : blockSum term 4615696 964 6503657 := by unfold blockSum; decide +kernel

private theorem block4616660 : blockSum term 4616660 964 8212216 := by unfold blockSum; decide +kernel

private theorem block4617624 : blockSum term 4617624 964 8323914 := by unfold blockSum; decide +kernel

private theorem block4618588 : blockSum term 4618588 964 8558505 := by unfold blockSum; decide +kernel

private theorem block4619552 : blockSum term 4619552 964 7326533 := by unfold blockSum; decide +kernel

private theorem block4620516 : blockSum term 4620516 964 7683229 := by unfold blockSum; decide +kernel

private theorem block4621480 : blockSum term 4621480 964 6090987 := by unfold blockSum; decide +kernel

private theorem block4622444 : blockSum term 4622444 965 7909192 := by unfold blockSum; decide +kernel

private theorem block4623409 : blockSum term 4623409 964 7656145 := by unfold blockSum; decide +kernel

private theorem block4624373 : blockSum term 4624373 964 9223904 := by unfold blockSum; decide +kernel

private theorem block4625337 : blockSum term 4625337 964 7272345 := by unfold blockSum; decide +kernel

private theorem block4626301 : blockSum term 4626301 964 7143015 := by unfold blockSum; decide +kernel

private theorem block4627265 : blockSum term 4627265 964 6288096 := by unfold blockSum; decide +kernel

private theorem block4628229 : blockSum term 4628229 964 8092728 := by unfold blockSum; decide +kernel

private theorem block4629193 : blockSum term 4629193 964 8202991 := by unfold blockSum; decide +kernel

private theorem block4630157 : blockSum term 4630157 965 7710543 := by unfold blockSum; decide +kernel

private theorem block4631122 : blockSum term 4631122 964 6858563 := by unfold blockSum; decide +kernel

private theorem block4632086 : blockSum term 4632086 964 7330295 := by unfold blockSum; decide +kernel

private theorem block4633050 : blockSum term 4633050 964 7561091 := by unfold blockSum; decide +kernel

private theorem block4634014 : blockSum term 4634014 964 7432064 := by unfold blockSum; decide +kernel

private theorem block4634978 : blockSum term 4634978 964 8020968 := by unfold blockSum; decide +kernel

private theorem block4635942 : blockSum term 4635942 964 7293597 := by unfold blockSum; decide +kernel

private theorem block4636906 : blockSum term 4636906 964 7404517 := by unfold blockSum; decide +kernel

private theorem block4637870 : blockSum term 4637870 965 7633907 := by unfold blockSum; decide +kernel

private theorem block4638835 : blockSum term 4638835 964 7385664 := by unfold blockSum; decide +kernel

private theorem block4639799 : blockSum term 4639799 964 7971160 := by unfold blockSum; decide +kernel

private theorem block4640763 : blockSum term 4640763 964 7485949 := by unfold blockSum; decide +kernel

private theorem block4641727 : blockSum term 4641727 964 6527482 := by unfold blockSum; decide +kernel

private theorem block4642691 : blockSum term 4642691 964 7468137 := by unfold blockSum; decide +kernel

private theorem block4643655 : blockSum term 4643655 964 6630052 := by unfold blockSum; decide +kernel

private theorem block4644619 : blockSum term 4644619 964 7212995 := by unfold blockSum; decide +kernel

private theorem block4645583 : blockSum term 4645583 965 8030084 := by unfold blockSum; decide +kernel

private theorem block4646548 : blockSum term 4646548 964 8609440 := by unfold blockSum; decide +kernel

private theorem block4647512 : blockSum term 4647512 964 7185360 := by unfold blockSum; decide +kernel

private theorem block4648476 : blockSum term 4648476 964 7293514 := by unfold blockSum; decide +kernel

private theorem block4649440 : blockSum term 4649440 964 7049868 := by unfold blockSum; decide +kernel

private theorem block4650404 : blockSum term 4650404 964 7627402 := by unfold blockSum; decide +kernel

private theorem block4651368 : blockSum term 4651368 964 6915186 := by unfold blockSum; decide +kernel

private theorem block4652332 : blockSum term 4652332 964 6555282 := by unfold blockSum; decide +kernel

private theorem block4653296 : blockSum term 4653296 965 7365710 := by unfold blockSum; decide +kernel

private theorem block4654261 : blockSum term 4654261 964 6773250 := by unfold blockSum; decide +kernel

private theorem block4655225 : blockSum term 4655225 964 6881334 := by unfold blockSum; decide +kernel

private theorem block4656189 : blockSum term 4656189 964 6173884 := by unfold blockSum; decide +kernel

private theorem block4657153 : blockSum term 4657153 964 7446260 := by unfold blockSum; decide +kernel

private theorem block4658117 : blockSum term 4658117 964 7552426 := by unfold blockSum; decide +kernel

private theorem block4659081 : blockSum term 4659081 964 6498861 := by unfold blockSum; decide +kernel

private theorem block4660045 : blockSum term 4660045 964 7765593 := by unfold blockSum; decide +kernel

private theorem block4661009 : blockSum term 4661009 965 7176764 := by unfold blockSum; decide +kernel

private theorem block4661974 : blockSum term 4661974 964 7283469 := by unfold blockSum; decide +kernel

private theorem block4662938 : blockSum term 4662938 964 7620397 := by unfold blockSum; decide +kernel

private theorem block4663902 : blockSum term 4663902 964 7841015 := by unfold blockSum; decide +kernel

private theorem block4664866 : blockSum term 4664866 964 5988350 := by unfold blockSum; decide +kernel

private theorem block4665830 : blockSum term 4665830 964 7246216 := by unfold blockSum; decide +kernel

private theorem block4666794 : blockSum term 4666794 964 7465893 := by unfold blockSum; decide +kernel

private theorem block4667758 : blockSum term 4667758 964 8143500 := by unfold blockSum; decide +kernel

private theorem block4668722 : blockSum term 4668722 965 7674804 := by unfold blockSum; decide +kernel

private theorem block4669687 : blockSum term 4669687 964 6063465 := by unfold blockSum; decide +kernel

private theorem block4670651 : blockSum term 4670651 964 7884327 := by unfold blockSum; decide +kernel

private theorem block4671615 : blockSum term 4671615 964 7303205 := by unfold blockSum; decide +kernel

private theorem block4672579 : blockSum term 4672579 964 7293331 := by unfold blockSum; decide +kernel

private theorem block4673543 : blockSum term 4673543 964 7170328 := by unfold blockSum; decide +kernel

private theorem block4674507 : blockSum term 4674507 964 7387735 := by unfold blockSum; decide +kernel

private theorem block4675471 : blockSum term 4675471 964 8172780 := by unfold blockSum; decide +kernel

private theorem block4676435 : blockSum term 4676435 965 6234745 := by unfold blockSum; decide +kernel

private theorem block4677400 : blockSum term 4677400 964 7133025 := by unfold blockSum; decide +kernel

private theorem block4678364 : blockSum term 4678364 964 7123650 := by unfold blockSum; decide +kernel

private theorem block4679328 : blockSum term 4679328 964 7340968 := by unfold blockSum; decide +kernel

private theorem block4680292 : blockSum term 4680292 964 7444113 := by unfold blockSum; decide +kernel

private theorem block4681256 : blockSum term 4681256 964 7997150 := by unfold blockSum; decide +kernel

private theorem block4682220 : blockSum term 4682220 964 7424183 := by unfold blockSum; decide +kernel

private theorem block4683184 : blockSum term 4683184 964 7414282 := by unfold blockSum; decide +kernel

private theorem block4684148 : blockSum term 4684148 965 5946544 := by unfold blockSum; decide +kernel

private theorem block4685113 : blockSum term 4685113 964 8403795 := by unfold blockSum; decide +kernel

private theorem block4686077 : blockSum term 4686077 964 7608477 := by unfold blockSum; decide +kernel

private theorem block4687041 : blockSum term 4687041 964 7598040 := by unfold blockSum; decide +kernel

private theorem block4688005 : blockSum term 4688005 964 6806886 := by unfold blockSum; decide +kernel

private theorem block4688969 : blockSum term 4688969 964 6463610 := by unfold blockSum; decide +kernel

private theorem block4689933 : blockSum term 4689933 964 6121454 := by unfold blockSum; decide +kernel

private theorem block4690897 : blockSum term 4690897 964 6447327 := by unfold blockSum; decide +kernel

private theorem block4691861 : blockSum term 4691861 965 6550064 := by unfold blockSum; decide +kernel

private theorem block4692826 : blockSum term 4692826 964 7206384 := by unfold blockSum; decide +kernel

private theorem block4693790 : blockSum term 4693790 964 6089914 := by unfold blockSum; decide +kernel

private theorem block4694754 : blockSum term 4694754 964 8072686 := by unfold blockSum; decide +kernel

private theorem block4695718 : blockSum term 4695718 964 7840641 := by unfold blockSum; decide +kernel

private theorem block4696682 : blockSum term 4696682 964 7498798 := by unfold blockSum; decide +kernel

private theorem block4697646 : blockSum term 4697646 964 7598406 := by unfold blockSum; decide +kernel

private theorem block4698610 : blockSum term 4698610 964 5498923 := by unfold blockSum; decide +kernel

private theorem block4699574 : blockSum term 4699574 965 6919804 := by unfold blockSum; decide +kernel

private theorem block4700539 : blockSum term 4700539 964 7568888 := by unfold blockSum; decide +kernel

private theorem block4701503 : blockSum term 4701503 964 6900649 := by unfold blockSum; decide +kernel

private theorem block4702467 : blockSum term 4702467 964 6782152 := by unfold blockSum; decide +kernel

private theorem block4703431 : blockSum term 4703431 964 6991377 := by unfold blockSum; decide +kernel

private theorem block4704395 : blockSum term 4704395 964 6764517 := by unfold blockSum; decide +kernel

private theorem block4705359 : blockSum term 4705359 964 6319482 := by unfold blockSum; decide +kernel

private theorem block4706323 : blockSum term 4706323 964 5766972 := by unfold blockSum; decide +kernel

private theorem block4707287 : blockSum term 4707287 965 6846132 := by unfold blockSum; decide +kernel

private theorem block4708252 : blockSum term 4708252 964 7379372 := by unfold blockSum; decide +kernel

private theorem block4709216 : blockSum term 4709216 964 6285509 := by unfold blockSum; decide +kernel

private theorem block4710180 : blockSum term 4710180 964 6926606 := by unfold blockSum; decide +kernel

private theorem block4711144 : blockSum term 4711144 964 6484942 := by unfold blockSum; decide +kernel

private theorem block4712108 : blockSum term 4712108 964 6907828 := by unfold blockSum; decide +kernel

private theorem block4713072 : blockSum term 4713072 964 6252014 := by unfold blockSum; decide +kernel

private theorem block4714036 : blockSum term 4714036 964 7105186 := by unfold blockSum; decide +kernel

private theorem block4715000 : blockSum term 4715000 965 6236279 := by unfold blockSum; decide +kernel

private theorem block4715965 : blockSum term 4715965 964 7408888 := by unfold blockSum; decide +kernel

private theorem block4716929 : blockSum term 4716929 964 7720084 := by unfold blockSum; decide +kernel

private theorem block4717893 : blockSum term 4717893 964 6424055 := by unfold blockSum; decide +kernel

private theorem block4718857 : blockSum term 4718857 964 6736248 := by unfold blockSum; decide +kernel

private theorem block4719821 : blockSum term 4719821 964 6940589 := by unfold blockSum; decide +kernel

private theorem block4720785 : blockSum term 4720785 964 6931102 := by unfold blockSum; decide +kernel

private theorem block4721749 : blockSum term 4721749 964 6602757 := by unfold blockSum; decide +kernel

private theorem block4722713 : blockSum term 4722713 965 5743322 := by unfold blockSum; decide +kernel

private theorem block4723678 : blockSum term 4723678 964 5947995 := by unfold blockSum; decide +kernel

private theorem block4724642 : blockSum term 4724642 964 7531170 := by unfold blockSum; decide +kernel

private theorem block4725606 : blockSum term 4725606 964 6673777 := by unfold blockSum; decide +kernel

private theorem block4726570 : blockSum term 4726570 964 6558691 := by unfold blockSum; decide +kernel

private theorem block4727534 : blockSum term 4727534 964 6973242 := by unfold blockSum; decide +kernel

private theorem block4728498 : blockSum term 4728498 964 5591847 := by unfold blockSum; decide +kernel

private theorem block4729462 : blockSum term 4729462 964 7269899 := by unfold blockSum; decide +kernel

private theorem block4730426 : blockSum term 4730426 965 6943406 := by unfold blockSum; decide +kernel

private theorem block4731391 : blockSum term 4731391 964 6933573 := by unfold blockSum; decide +kernel

private theorem block4732355 : blockSum term 4732355 964 6924044 := by unfold blockSum; decide +kernel

private theorem block4733319 : blockSum term 4733319 964 7124637 := by unfold blockSum; decide +kernel

private theorem block4734283 : blockSum term 4734283 964 6905193 := by unfold blockSum; decide +kernel

private theorem block4735247 : blockSum term 4735247 964 6164360 := by unfold blockSum; decide +kernel

private theorem block4736211 : blockSum term 4736211 964 7094334 := by unfold blockSum; decide +kernel

private theorem block4737175 : blockSum term 4737175 964 6980019 := by unfold blockSum; decide +kernel

private theorem block4738139 : blockSum term 4738139 965 6242064 := by unfold blockSum; decide +kernel

private theorem block4739104 : blockSum term 4739104 964 5090865 := by unfold blockSum; decide +kernel

private theorem block4740068 : blockSum term 4740068 964 6537155 := by unfold blockSum; decide +kernel

private theorem block4741032 : blockSum term 4741032 964 6527832 := by unfold blockSum; decide +kernel

private theorem block4741996 : blockSum term 4741996 965 7242465 := by unfold blockSum; decide +kernel

private theorem block4742961 : blockSum term 4742961 964 6405157 := by unfold blockSum; decide +kernel

private theorem block4743925 : blockSum term 4743925 964 5984632 := by unfold blockSum; decide +kernel

private theorem block4744889 : blockSum term 4744889 964 6285298 := by unfold blockSum; decide +kernel

private theorem block4745853 : blockSum term 4745853 965 6893772 := by unfold blockSum; decide +kernel

private theorem block4746818 : blockSum term 4746818 964 5856295 := by unfold blockSum; decide +kernel

private theorem block4747782 : blockSum term 4747782 964 6771568 := by unfold blockSum; decide +kernel

private theorem block4748746 : blockSum term 4748746 964 5840253 := by unfold blockSum; decide +kernel

private theorem block4749710 : blockSum term 4749710 964 6037660 := by unfold blockSum; decide +kernel

private theorem block4750674 : blockSum term 4750674 964 6233477 := by unfold blockSum; decide +kernel

private theorem block4751638 : blockSum term 4751638 964 6122531 := by unfold blockSum; decide +kernel

private theorem block4752602 : blockSum term 4752602 964 5298902 := by unfold blockSum; decide +kernel

private theorem block4753566 : blockSum term 4753566 965 6614969 := by unfold blockSum; decide +kernel

private theorem block4754531 : blockSum term 4754531 964 7113356 := by unfold blockSum; decide +kernel

private theorem block4755495 : blockSum term 4755495 964 5683088 := by unfold blockSum; decide +kernel

private theorem block4756459 : blockSum term 4756459 964 6485067 := by unfold blockSum; decide +kernel

private theorem block4757423 : blockSum term 4757423 964 6172332 := by unfold blockSum; decide +kernel

private theorem block4758387 : blockSum term 4758387 964 6668501 := by unfold blockSum; decide +kernel

private theorem block4759351 : blockSum term 4759351 964 7465240 := by unfold blockSum; decide +kernel

private theorem block4760315 : blockSum term 4760315 964 5741649 := by unfold blockSum; decide +kernel

private theorem block4761279 : blockSum term 4761279 965 6236641 := by unfold blockSum; decide +kernel

private theorem block4762244 : blockSum term 4762244 964 6327969 := by unfold blockSum; decide +kernel

private theorem block4763208 : blockSum term 4763208 964 5115908 := by unfold blockSum; decide +kernel

private theorem block4764172 : blockSum term 4764172 964 7411694 := by unfold blockSum; decide +kernel

private theorem block4765136 : blockSum term 4765136 964 6800316 := by unfold blockSum; decide +kernel

private theorem block4766100 : blockSum term 4766100 964 5791816 := by unfold blockSum; decide +kernel

private theorem block4767064 : blockSum term 4767064 964 6082807 := by unfold blockSum; decide +kernel

private theorem block4768028 : blockSum term 4768028 964 7367572 := by unfold blockSum; decide +kernel

private theorem block4768992 : blockSum term 4768992 965 5269492 := by unfold blockSum; decide +kernel

private theorem block4769957 : blockSum term 4769957 964 6454374 := by unfold blockSum; decide +kernel

private theorem block4770921 : blockSum term 4770921 964 5255217 := by unfold blockSum; decide +kernel

private theorem block4771885 : blockSum term 4771885 964 5544885 := by unfold blockSum; decide +kernel

private theorem block4772849 : blockSum term 4772849 964 5636308 := by unfold blockSum; decide +kernel

private theorem block4773813 : blockSum term 4773813 964 6615682 := by unfold blockSum; decide +kernel

private theorem block4774777 : blockSum term 4774777 964 7098820 := by unfold blockSum; decide +kernel

private theorem block4775741 : blockSum term 4775741 964 5808350 := by unfold blockSum; decide +kernel

private theorem block4776705 : blockSum term 4776705 965 5505158 := by unfold blockSum; decide +kernel

private theorem block4777670 : blockSum term 4777670 964 6576356 := by unfold blockSum; decide +kernel

private theorem block4778634 : blockSum term 4778634 964 5782338 := by unfold blockSum; decide +kernel

private theorem block4779598 : blockSum term 4779598 964 6067091 := by unfold blockSum; decide +kernel

private theorem block4780562 : blockSum term 4780562 964 6253588 := by unfold blockSum; decide +kernel

private theorem block4781526 : blockSum term 4781526 964 6633864 := by unfold blockSum; decide +kernel

private theorem block4782490 : blockSum term 4782490 964 6331323 := by unfold blockSum; decide +kernel

private theorem block4783454 : blockSum term 4783454 964 5446339 := by unfold blockSum; decide +kernel

private theorem block4784418 : blockSum term 4784418 965 5826957 := by unfold blockSum; decide +kernel

private theorem block4785383 : blockSum term 4785383 964 6109550 := by unfold blockSum; decide +kernel

private theorem block4786347 : blockSum term 4786347 964 6100355 := by unfold blockSum; decide +kernel

private theorem block4787311 : blockSum term 4787311 964 5995054 := by unfold blockSum; decide +kernel

private theorem block4788275 : blockSum term 4788275 964 6372025 := by unfold blockSum; decide +kernel

private theorem block4789239 : blockSum term 4789239 964 5687777 := by unfold blockSum; decide +kernel

private theorem block4790203 : blockSum term 4790203 964 5102188 := by unfold blockSum; decide +kernel

private theorem block4791167 : blockSum term 4791167 964 6248003 := by unfold blockSum; decide +kernel

private theorem block4792131 : blockSum term 4792131 965 5854298 := by unfold blockSum; decide +kernel

private theorem block4793096 : blockSum term 4793096 964 5270619 := by unfold blockSum; decide +kernel

private theorem block4794060 : blockSum term 4794060 964 6219320 := by unfold blockSum; decide +kernel

private theorem block4795024 : blockSum term 4795024 964 6113877 := by unfold blockSum; decide +kernel

private theorem block4795988 : blockSum term 4795988 964 6391170 := by unfold blockSum; decide +kernel

private theorem block4796952 : blockSum term 4796952 964 6000600 := by unfold blockSum; decide +kernel

private theorem block4797916 : blockSum term 4797916 964 5706110 := by unfold blockSum; decide +kernel

private theorem block4798880 : blockSum term 4798880 964 5888158 := by unfold blockSum; decide +kernel

private theorem block4799844 : blockSum term 4799844 965 6163622 := by unfold blockSum; decide +kernel

private theorem block4800809 : blockSum term 4800809 964 6153858 := by unfold blockSum; decide +kernel

private theorem block4801773 : blockSum term 4801773 964 6144142 := by unfold blockSum; decide +kernel

private theorem block4802737 : blockSum term 4802737 964 6700498 := by unfold blockSum; decide +kernel

private theorem block4803701 : blockSum term 4803701 964 6407231 := by unfold blockSum; decide +kernel

private theorem block4804665 : blockSum term 4804665 964 5551077 := by unfold blockSum; decide +kernel

private theorem block4805629 : blockSum term 4805629 964 6200287 := by unfold blockSum; decide +kernel

private theorem block4806593 : blockSum term 4806593 964 6190331 := by unfold blockSum; decide +kernel

private theorem block4807557 : blockSum term 4807557 965 5431190 := by unfold blockSum; decide +kernel

private theorem block4808522 : blockSum term 4808522 964 5610156 := by unfold blockSum; decide +kernel

private theorem block4809486 : blockSum term 4809486 964 4855185 := by unfold blockSum; decide +kernel

private theorem block4810450 : blockSum term 4810450 964 6153430 := by unfold blockSum; decide +kernel

private theorem block4811414 : blockSum term 4811414 964 5957124 := by unfold blockSum; decide +kernel

private theorem block4812378 : blockSum term 4812378 964 5483238 := by unfold blockSum; decide +kernel

private theorem block4813342 : blockSum term 4813342 964 6310157 := by unfold blockSum; decide +kernel

private theorem block4814306 : blockSum term 4814306 964 5002847 := by unfold blockSum; decide +kernel

private theorem block4815270 : blockSum term 4815270 965 6105816 := by unfold blockSum; decide +kernel

private theorem block4816235 : blockSum term 4816235 964 6095968 := by unfold blockSum; decide +kernel

private theorem block4817199 : blockSum term 4817199 964 5901464 := by unfold blockSum; decide +kernel

private theorem block4818163 : blockSum term 4818163 964 5800535 := by unfold blockSum; decide +kernel

private theorem block4819127 : blockSum term 4819127 964 6067439 := by unfold blockSum; decide +kernel

private theorem block4820091 : blockSum term 4820091 964 5415727 := by unfold blockSum; decide +kernel

private theorem block4821055 : blockSum term 4821055 964 6048613 := by unfold blockSum; decide +kernel

private theorem block4822019 : blockSum term 4822019 964 6222309 := by unfold blockSum; decide +kernel

private theorem block4822983 : blockSum term 4822983 965 5390379 := by unfold blockSum; decide +kernel

private theorem block4823948 : blockSum term 4823948 964 5564660 := by unfold blockSum; decide +kernel

private theorem block4824912 : blockSum term 4824912 964 4554348 := by unfold blockSum; decide +kernel

private theorem block4825876 : blockSum term 4825876 964 5275381 := by unfold blockSum; decide +kernel

private theorem block4826840 : blockSum term 4826840 964 5630372 := by unfold blockSum; decide +kernel

private theorem block4827804 : blockSum term 4827804 964 5984643 := by unfold blockSum; decide +kernel

private theorem block4828768 : blockSum term 4828768 964 5703203 := by unfold blockSum; decide +kernel

private theorem block4829732 : blockSum term 4829732 964 5332467 := by unfold blockSum; decide +kernel

private theorem block4830696 : blockSum term 4830696 965 4692733 := by unfold blockSum; decide +kernel

private theorem block4831661 : blockSum term 4831661 964 6757740 := by unfold blockSum; decide +kernel

private theorem block4832625 : blockSum term 4832625 964 5307906 := by unfold blockSum; decide +kernel

private theorem block4833589 : blockSum term 4833589 964 5479045 := by unfold blockSum; decide +kernel

private theorem block4834553 : blockSum term 4834553 964 6187354 := by unfold blockSum; decide +kernel

private theorem block4835517 : blockSum term 4835517 964 6892913 := by unfold blockSum; decide +kernel

private theorem block4836481 : blockSum term 4836481 964 5809093 := by unfold blockSum; decide +kernel

private theorem block4837445 : blockSum term 4837445 964 6691805 := by unfold blockSum; decide +kernel

private theorem block4838409 : blockSum term 4838409 965 5522788 := by unfold blockSum; decide +kernel

private theorem block4839374 : blockSum term 4839374 964 5158000 := by unfold blockSum; decide +kernel

private theorem block4840338 : blockSum term 4840338 964 4972522 := by unfold blockSum; decide +kernel

private theorem block4841302 : blockSum term 4841302 964 5674382 := by unfold blockSum; decide +kernel

private theorem block4842266 : blockSum term 4842266 964 5399937 := by unfold blockSum; decide +kernel

private theorem block4843230 : blockSum term 4843230 964 5038389 := by unfold blockSum; decide +kernel

private theorem block4844194 : blockSum term 4844194 964 5471748 := by unfold blockSum; decide +kernel

private theorem block4845158 : blockSum term 4845158 964 5374944 := by unfold blockSum; decide +kernel

private theorem block4846122 : blockSum term 4846122 965 5190669 := by unfold blockSum; decide +kernel

private theorem block4847087 : blockSum term 4847087 964 6060985 := by unfold blockSum; decide +kernel

private theorem block4848051 : blockSum term 4848051 964 5612690 := by unfold blockSum; decide +kernel

private theorem block4849015 : blockSum term 4849015 964 5340846 := by unfold blockSum; decide +kernel

private theorem block4849979 : blockSum term 4849979 964 5594572 := by unfold blockSum; decide +kernel

private theorem block4850943 : blockSum term 4850943 964 5672836 := by unfold blockSum; decide +kernel

private theorem block4851907 : blockSum term 4851907 964 6099087 := by unfold blockSum; decide +kernel

private theorem block4852871 : blockSum term 4852871 964 4958342 := by unfold blockSum; decide +kernel

private theorem block4853835 : blockSum term 4853835 965 5644822 := by unfold blockSum; decide +kernel

private theorem block4854800 : blockSum term 4854800 964 4768832 := by unfold blockSum; decide +kernel

private theorem block4855764 : blockSum term 4855764 964 5021096 := by unfold blockSum; decide +kernel

private theorem block4856728 : blockSum term 4856728 964 5531222 := by unfold blockSum; decide +kernel

private theorem block4857692 : blockSum term 4857692 964 5176444 := by unfold blockSum; decide +kernel

private theorem block4858656 : blockSum term 4858656 964 5770627 := by unfold blockSum; decide +kernel

private theorem block4859620 : blockSum term 4859620 964 5760455 := by unfold blockSum; decide +kernel

private theorem block4860584 : blockSum term 4860584 964 4721147 := by unfold blockSum; decide +kernel

private theorem block4861548 : blockSum term 4861548 965 5570565 := by unfold blockSum; decide +kernel

private theorem block4862513 : blockSum term 4862513 964 5048060 := by unfold blockSum; decide +kernel

private theorem block4863477 : blockSum term 4863477 964 6065432 := by unfold blockSum; decide +kernel

private theorem block4864441 : blockSum term 4864441 964 4775912 := by unfold blockSum; decide +kernel

private theorem block4865405 : blockSum term 4865405 965 5875109 := by unfold blockSum; decide +kernel

private theorem block4866370 : blockSum term 4866370 964 6289606 := by unfold blockSum; decide +kernel

private theorem block4867334 : blockSum term 4867334 964 5175985 := by unfold blockSum; decide +kernel

private theorem block4868298 : blockSum term 4868298 964 5675587 := by unfold blockSum; decide +kernel

private theorem block4869262 : blockSum term 4869262 965 5074309 := by unfold blockSum; decide +kernel

private theorem block4870227 : blockSum term 4870227 964 4982115 := by unfold blockSum; decide +kernel

private theorem block4871191 : blockSum term 4871191 964 5732950 := by unfold blockSum; decide +kernel

private theorem block4872155 : blockSum term 4872155 964 5302455 := by unfold blockSum; decide +kernel

private theorem block4873119 : blockSum term 4873119 964 4957397 := by unfold blockSum; decide +kernel

private theorem block4874083 : blockSum term 4874083 964 4362387 := by unfold blockSum; decide +kernel

private theorem block4875047 : blockSum term 4875047 964 5528241 := by unfold blockSum; decide +kernel

private theorem block4876011 : blockSum term 4876011 964 4765760 := by unfold blockSum; decide +kernel

private theorem block4876975 : blockSum term 4876975 965 5426346 := by unfold blockSum; decide +kernel

private theorem block4877940 : blockSum term 4877940 964 5083520 := by unfold blockSum; decide +kernel

private theorem block4878904 : blockSum term 4878904 964 4991940 := by unfold blockSum; decide +kernel

private theorem block4879868 : blockSum term 4879868 964 5399278 := by unfold blockSum; decide +kernel

private theorem block4880832 : blockSum term 4880832 964 5969775 := by unfold blockSum; decide +kernel

private theorem block4881796 : blockSum term 4881796 964 5462069 := by unfold blockSum; decide +kernel

private theorem block4882760 : blockSum term 4882760 964 4708875 := by unfold blockSum; decide +kernel

private theorem block4883724 : blockSum term 4883724 964 5278307 := by unfold blockSum; decide +kernel

private theorem block4884688 : blockSum term 4884688 965 5680583 := by unfold blockSum; decide +kernel

private theorem block4885653 : blockSum term 4885653 964 4849020 := by unfold blockSum; decide +kernel

private theorem block4886617 : blockSum term 4886617 964 4923641 := by unfold blockSum; decide +kernel

private theorem block4887581 : blockSum term 4887581 964 5570070 := by unfold blockSum; decide +kernel

private theorem block4888545 : blockSum term 4888545 964 5968461 := by unfold blockSum; decide +kernel

private theorem block4889509 : blockSum term 4889509 964 4896867 := by unfold blockSum; decide +kernel

private theorem block4890473 : blockSum term 4890473 964 5947679 := by unfold blockSum; decide +kernel

private theorem block4891437 : blockSum term 4891437 964 4880241 := by unfold blockSum; decide +kernel

private theorem block4892401 : blockSum term 4892401 965 5196628 := by unfold blockSum; decide +kernel

private theorem block4893366 : blockSum term 4893366 964 5592407 := by unfold blockSum; decide +kernel

private theorem block4894330 : blockSum term 4894330 964 4935083 := by unfold blockSum; decide +kernel

private theorem block4895294 : blockSum term 4895294 964 5491627 := by unfold blockSum; decide +kernel

private theorem block4896258 : blockSum term 4896258 964 5078401 := by unfold blockSum; decide +kernel

private theorem block4897222 : blockSum term 4897222 964 5390774 := by unfold blockSum; decide +kernel

private theorem block4898186 : blockSum term 4898186 964 5140509 := by unfold blockSum; decide +kernel

private theorem block4899150 : blockSum term 4899150 964 5372019 := by unfold blockSum; decide +kernel

private theorem block4900114 : blockSum term 4900114 965 5762800 := by unfold blockSum; decide +kernel

private theorem block4901079 : blockSum term 4901079 964 5193221 := by unfold blockSum; decide +kernel

private theorem block4902043 : blockSum term 4902043 964 4864872 := by unfold blockSum; decide +kernel

private theorem block4903007 : blockSum term 4903007 964 4219882 := by unfold blockSum; decide +kernel

private theorem block4903971 : blockSum term 4903971 964 4689630 := by unfold blockSum; decide +kernel

private theorem block4904935 : blockSum term 4904935 964 4364191 := by unfold blockSum; decide +kernel

private theorem block4905899 : blockSum term 4905899 964 5623661 := by unfold blockSum; decide +kernel

private theorem block4906863 : blockSum term 4906863 964 5297077 := by unfold blockSum; decide +kernel

private theorem block4907827 : blockSum term 4907827 965 5445077 := by unfold blockSum; decide +kernel

private theorem block4908792 : blockSum term 4908792 964 4569219 := by unfold blockSum; decide +kernel

private theorem block4909756 : blockSum term 4909756 964 4482491 := by unfold blockSum; decide +kernel

private theorem block4910720 : blockSum term 4910720 964 4553474 := by unfold blockSum; decide +kernel

private theorem block4911684 : blockSum term 4911684 964 5016272 := by unfold blockSum; decide +kernel

private theorem block4912648 : blockSum term 4912648 964 4616007 := by unfold blockSum; decide +kernel

private theorem block4913612 : blockSum term 4913612 964 4685637 := by unfold blockSum; decide +kernel

private theorem block4914576 : blockSum term 4914576 964 5301249 := by unfold blockSum; decide +kernel

private theorem block4915540 : blockSum term 4915540 965 4902190 := by unfold blockSum; decide +kernel

private theorem block4916505 : blockSum term 4916505 964 3961821 := by unfold blockSum; decide +kernel

private theorem block4917469 : blockSum term 4917469 964 4187813 := by unfold blockSum; decide +kernel

private theorem block4918433 : blockSum term 4918433 964 5651127 := by unfold blockSum; decide +kernel

private theorem block4919397 : blockSum term 4919397 964 4636522 := by unfold blockSum; decide +kernel

private theorem block4920361 : blockSum term 4920361 964 5553686 := by unfold blockSum; decide +kernel

private theorem block4921325 : blockSum term 4921325 964 4773480 := by unfold blockSum; decide +kernel

private theorem block4922289 : blockSum term 4922289 964 4764855 := by unfold blockSum; decide +kernel

private theorem block4923253 : blockSum term 4923253 965 4832839 := by unfold blockSum; decide +kernel

private theorem block4924218 : blockSum term 4924218 964 4900450 := by unfold blockSum; decide +kernel

private theorem block4925182 : blockSum term 4925182 964 4509706 := by unfold blockSum; decide +kernel

private theorem block4926146 : blockSum term 4926146 964 4959167 := by unfold blockSum; decide +kernel

private theorem block4927110 : blockSum term 4927110 964 4645628 := by unfold blockSum; decide +kernel

private theorem block4928074 : blockSum term 4928074 964 5016608 := by unfold blockSum; decide +kernel

private theorem block4929038 : blockSum term 4929038 964 4400267 := by unfold blockSum; decide +kernel

private theorem block4930002 : blockSum term 4930002 964 5225441 := by unfold blockSum; decide +kernel

private theorem block4930966 : blockSum term 4930966 965 4308718 := by unfold blockSum; decide +kernel

private theorem block4931931 : blockSum term 4931931 964 5206529 := by unfold blockSum; decide +kernel

private theorem block4932895 : blockSum term 4932895 964 4368241 := by unfold blockSum; decide +kernel

private theorem block4933859 : blockSum term 4933859 964 4585883 := by unfold blockSum; decide +kernel

private theorem block4934823 : blockSum term 4934823 964 5027313 := by unfold blockSum; decide +kernel

private theorem block4935787 : blockSum term 4935787 964 4568402 := by unfold blockSum; decide +kernel

private theorem block4936751 : blockSum term 4936751 964 4186033 := by unfold blockSum; decide +kernel

private theorem block4937715 : blockSum term 4937715 964 5446181 := by unfold blockSum; decide +kernel

private theorem block4938679 : blockSum term 4938679 965 4318715 := by unfold blockSum; decide +kernel

private theorem block4939644 : blockSum term 4939644 964 4682362 := by unfold blockSum; decide +kernel

private theorem block4940608 : blockSum term 4940608 964 4525733 := by unfold blockSum; decide +kernel

private theorem block4941572 : blockSum term 4941572 964 4073664 := by unfold blockSum; decide +kernel

private theorem block4942536 : blockSum term 4942536 964 5321955 := by unfold blockSum; decide +kernel

private theorem block4943500 : blockSum term 4943500 964 4573933 := by unfold blockSum; decide +kernel

private theorem block4944464 : blockSum term 4944464 964 5007498 := by unfold blockSum; decide +kernel

private theorem block4945428 : blockSum term 4945428 964 4849978 := by unfold blockSum; decide +kernel

private theorem block4946392 : blockSum term 4946392 965 4693664 := by unfold blockSum; decide +kernel

private theorem block4947357 : blockSum term 4947357 964 3806831 := by unfold blockSum; decide +kernel

private theorem block4948321 : blockSum term 4948321 964 4531452 := by unfold blockSum; decide +kernel

private theorem block4949285 : blockSum term 4949285 964 4450264 := by unfold blockSum; decide +kernel

private theorem block4950249 : blockSum term 4950249 964 4806240 := by unfold blockSum; decide +kernel

private theorem block4951213 : blockSum term 4951213 964 4578697 := by unfold blockSum; decide +kernel

private theorem block4952177 : blockSum term 4952177 964 5077565 := by unfold blockSum; decide +kernel

private theorem block4953141 : blockSum term 4953141 964 4560452 := by unfold blockSum; decide +kernel

private theorem block4954105 : blockSum term 4954105 965 4335513 := by unfold blockSum; decide +kernel

private theorem block4955070 : blockSum term 4955070 964 4831927 := by unfold blockSum; decide +kernel

private theorem block4956034 : blockSum term 4956034 964 4390369 := by unfold blockSum; decide +kernel

private theorem block4956998 : blockSum term 4956998 964 5172129 := by unfold blockSum; decide +kernel

private theorem block4957962 : blockSum term 4957962 964 3656577 := by unfold blockSum; decide +kernel

private theorem block4958926 : blockSum term 4958926 964 3578266 := by unfold blockSum; decide +kernel

private theorem block4959890 : blockSum term 4959890 964 4714172 := by unfold blockSum; decide +kernel

private theorem block4960854 : blockSum term 4960854 964 5132229 := by unfold blockSum; decide +kernel

private theorem block4961818 : blockSum term 4961818 965 4837522 := by unfold blockSum; decide +kernel

private theorem block4962783 : blockSum term 4962783 964 4898905 := by unfold blockSum; decide +kernel

private theorem block4963747 : blockSum term 4963747 964 3897362 := by unfold blockSum; decide +kernel

private theorem block4964711 : blockSum term 4964711 964 5445520 := by unfold blockSum; decide +kernel

private theorem block4965675 : blockSum term 4965675 964 3952709 := by unfold blockSum; decide +kernel

private theorem block4966639 : blockSum term 4966639 964 4790650 := by unfold blockSum; decide +kernel

private theorem block4967603 : blockSum term 4967603 964 4570346 := by unfold blockSum; decide +kernel

private theorem block4968567 : blockSum term 4968567 964 4351356 := by unfold blockSum; decide +kernel

private theorem block4969531 : blockSum term 4969531 965 3852369 := by unfold blockSum; decide +kernel

private theorem block4970496 : blockSum term 4970496 964 4264610 := by unfold blockSum; decide +kernel

private theorem block4971460 : blockSum term 4971460 964 4534703 := by unfold blockSum; decide +kernel

private theorem block4972424 : blockSum term 4972424 964 4525660 := by unfold blockSum; decide +kernel

private theorem block4973388 : blockSum term 4973388 964 3404953 := by unfold blockSum; decide +kernel

private theorem block4974352 : blockSum term 4974352 964 4577701 := by unfold blockSum; decide +kernel

private theorem block4975316 : blockSum term 4975316 964 4637362 := by unfold blockSum; decide +kernel

private theorem block4976280 : blockSum term 4976280 964 4903204 := by unfold blockSum; decide +kernel

private theorem block4977244 : blockSum term 4977244 965 4823966 := by unfold blockSum; decide +kernel

private theorem block4978209 : blockSum term 4978209 964 4264164 := by unfold blockSum; decide +kernel

private theorem block4979173 : blockSum term 4979173 964 4599197 := by unfold blockSum; decide +kernel

private theorem block4980137 : blockSum term 4980137 964 3699875 := by unfold blockSum; decide +kernel

private theorem block4981101 : blockSum term 4981101 964 4034693 := by unfold blockSum; decide +kernel

private theorem block4982065 : blockSum term 4982065 964 3890657 := by unfold blockSum; decide +kernel

private theorem block4983029 : blockSum term 4983029 964 4699516 := by unfold blockSum; decide +kernel

private theorem block4983993 : blockSum term 4983993 964 4621509 := by unfold blockSum; decide +kernel

private theorem block4984957 : blockSum term 4984957 965 4137151 := by unfold blockSum; decide +kernel

private theorem block4985922 : blockSum term 4985922 964 4603134 := by unfold blockSum; decide +kernel

private theorem block4986886 : blockSum term 4986886 964 4390528 := by unfold blockSum; decide +kernel

private theorem block4987850 : blockSum term 4987850 964 4381724 := by unfold blockSum; decide +kernel

private theorem block4988814 : blockSum term 4988814 965 4305833 := by unfold blockSum; decide +kernel

private theorem block4989779 : blockSum term 4989779 964 4700697 := by unfold blockSum; decide +kernel

private theorem block4990743 : blockSum term 4990743 964 4623872 := by unfold blockSum; decide +kernel

private theorem block4991707 : blockSum term 4991707 964 4012901 := by unfold blockSum; decide +kernel

private theorem block4992671 : blockSum term 4992671 965 4004903 := by unfold blockSum; decide +kernel

private theorem block4993636 : blockSum term 4993636 964 4130155 := by unfold blockSum; decide +kernel

private theorem block4994600 : blockSum term 4994600 964 3855234 := by unfold blockSum; decide +kernel

private theorem block4995564 : blockSum term 4995564 964 3914095 := by unfold blockSum; decide +kernel

private theorem block4996528 : blockSum term 4996528 964 3508716 := by unfold blockSum; decide +kernel

private theorem block4997492 : blockSum term 4997492 964 3501793 := by unfold blockSum; decide +kernel

private theorem block4998456 : blockSum term 4998456 964 4549413 := by unfold blockSum; decide +kernel

private theorem block4999420 : blockSum term 4999420 964 4341848 := by unfold blockSum; decide +kernel

private theorem block5000384 : blockSum term 5000384 965 4529098 := by unfold blockSum; decide +kernel

private theorem block5001349 : blockSum term 5001349 964 3602983 := by unfold blockSum; decide +kernel

private theorem block5002313 : blockSum term 5002313 964 3922504 := by unfold blockSum; decide +kernel

private theorem block5003277 : blockSum term 5003277 964 4631451 := by unfold blockSum; decide +kernel

private theorem block5004241 : blockSum term 5004241 964 3384975 := by unfold blockSum; decide +kernel

private theorem block5005205 : blockSum term 5005205 964 3703180 := by unfold blockSum; decide +kernel

private theorem block5006169 : blockSum term 5006169 964 4343909 := by unfold blockSum; decide +kernel

private theorem block5007133 : blockSum term 5007133 964 4334506 := by unfold blockSum; decide +kernel

private theorem block5008097 : blockSum term 5008097 965 3615768 := by unfold blockSum; decide +kernel

private theorem block5009062 : blockSum term 5009062 964 4251893 := by unfold blockSum; decide +kernel

private theorem block5010026 : blockSum term 5010026 964 3856928 := by unfold blockSum; decide +kernel

private theorem block5010990 : blockSum term 5010990 964 3720820 := by unfold blockSum; decide +kernel

private theorem block5011954 : blockSum term 5011954 964 3904549 := by unfold blockSum; decide +kernel

private theorem block5012918 : blockSum term 5012918 964 3832412 := by unfold blockSum; decide +kernel

private theorem block5013882 : blockSum term 5013882 964 3696680 := by unfold blockSum; decide +kernel

private theorem block5014846 : blockSum term 5014846 964 4578306 := by unfold blockSum; decide +kernel

private theorem block5015810 : blockSum term 5015810 965 4060679 := by unfold blockSum; decide +kernel

private theorem block5016775 : blockSum term 5016775 964 3609210 := by unfold blockSum; decide +kernel

private theorem block5017739 : blockSum term 5017739 964 3854250 := by unfold blockSum; decide +kernel

private theorem block5018703 : blockSum term 5018703 964 4160888 := by unfold blockSum; decide +kernel

private theorem block5019667 : blockSum term 5019667 964 4402676 := by unfold blockSum; decide +kernel

private theorem block5020631 : blockSum term 5020631 964 3703046 := by unfold blockSum; decide +kernel

private theorem block5021595 : blockSum term 5021595 964 3132414 := by unfold blockSum; decide +kernel

private theorem block5022559 : blockSum term 5022559 964 3876044 := by unfold blockSum; decide +kernel

private theorem block5023523 : blockSum term 5023523 965 4117099 := by unfold blockSum; decide +kernel

private theorem block5024488 : blockSum term 5024488 964 4108518 := by unfold blockSum; decide +kernel

private theorem block5025452 : blockSum term 5025452 964 4161389 := by unfold blockSum; decide +kernel

private theorem block5026416 : blockSum term 5026416 964 4337393 := by unfold blockSum; decide +kernel

private theorem block5027380 : blockSum term 5027380 964 3586085 := by unfold blockSum; decide +kernel

private theorem block5028344 : blockSum term 5028344 964 4133277 := by unfold blockSum; decide +kernel

private theorem block5029308 : blockSum term 5029308 964 3754430 := by unfold blockSum; decide +kernel

private theorem block5030272 : blockSum term 5030272 964 3561906 := by unfold blockSum; decide +kernel

private theorem block5031236 : blockSum term 5031236 965 4166079 := by unfold blockSum; decide +kernel

private theorem block5032201 : blockSum term 5032201 964 3301143 := by unfold blockSum; decide +kernel

private theorem block5033165 : blockSum term 5033165 964 3843564 := by unfold blockSum; decide +kernel

private theorem block5034129 : blockSum term 5034129 964 4017482 := by unfold blockSum; decide +kernel

private theorem block5035093 : blockSum term 5035093 964 3644476 := by unfold blockSum; decide +kernel

private theorem block5036057 : blockSum term 5036057 964 3393904 := by unfold blockSum; decide +kernel

private theorem block5037021 : blockSum term 5037021 964 3688060 := by unfold blockSum; decide +kernel

private theorem block5037985 : blockSum term 5037985 964 3740681 := by unfold blockSum; decide +kernel

private theorem block5038949 : blockSum term 5038949 965 4033736 := by unfold blockSum; decide +kernel

private theorem block5039914 : blockSum term 5039914 964 3663885 := by unfold blockSum; decide +kernel

private theorem block5040878 : blockSum term 5040878 964 3895339 := by unfold blockSum; decide +kernel

private theorem block5041842 : blockSum term 5041842 964 3647734 := by unfold blockSum; decide +kernel

private theorem block5042806 : blockSum term 5042806 964 3818864 := by unfold blockSum; decide +kernel

private theorem block5043770 : blockSum term 5043770 964 3512488 := by unfold blockSum; decide +kernel

private theorem block5044734 : blockSum term 5044734 964 3386171 := by unfold blockSum; decide +kernel

private theorem block5045698 : blockSum term 5045698 964 3556835 := by unfold blockSum; decide +kernel

private theorem block5046662 : blockSum term 5046662 965 3607673 := by unfold blockSum; decide +kernel

private theorem block5047627 : blockSum term 5047627 964 3422878 := by unfold blockSum; decide +kernel

private theorem block5048591 : blockSum term 5048591 964 3532878 := by unfold blockSum; decide +kernel

private theorem block5049555 : blockSum term 5049555 964 3583655 := by unfold blockSum; decide +kernel

private theorem block5050519 : blockSum term 5050519 964 3809651 := by unfold blockSum; decide +kernel

private theorem block5051483 : blockSum term 5051483 964 3625186 := by unfold blockSum; decide +kernel

private theorem block5052447 : blockSum term 5052447 964 3675155 := by unfold blockSum; decide +kernel

private theorem block5053411 : blockSum term 5053411 964 4306423 := by unfold blockSum; decide +kernel

private theorem block5054375 : blockSum term 5054375 965 3541350 := by unfold blockSum; decide +kernel

private theorem block5055340 : blockSum term 5055340 964 3765211 := by unfold blockSum; decide +kernel

private theorem block5056304 : blockSum term 5056304 964 4217941 := by unfold blockSum; decide +kernel

private theorem block5057268 : blockSum term 5057268 964 3458522 := by unfold blockSum; decide +kernel

private theorem block5058232 : blockSum term 5058232 964 3623064 := by unfold blockSum; decide +kernel

private theorem block5059196 : blockSum term 5059196 964 3499720 := by unfold blockSum; decide +kernel

private theorem block5060160 : blockSum term 5060160 964 3491767 := by unfold blockSum; decide +kernel

private theorem block5061124 : blockSum term 5061124 964 2741736 := by unfold blockSum; decide +kernel

private theorem block5062088 : blockSum term 5062088 965 4273717 := by unfold blockSum; decide +kernel

private theorem block5063053 : blockSum term 5063053 964 2899268 := by unfold blockSum; decide +kernel

private theorem block5064017 : blockSum term 5064017 964 3856808 := by unfold blockSum; decide +kernel

private theorem block5064981 : blockSum term 5064981 964 3281831 := by unfold blockSum; decide +kernel

private theorem block5065945 : blockSum term 5065945 964 3669305 := by unfold blockSum; decide +kernel

private theorem block5066909 : blockSum term 5066909 964 3491201 := by unfold blockSum; decide +kernel

private theorem block5067873 : blockSum term 5067873 964 3202221 := by unfold blockSum; decide +kernel

private theorem block5068837 : blockSum term 5068837 964 3643048 := by unfold blockSum; decide +kernel

private theorem block5069801 : blockSum term 5069801 965 4025282 := by unfold blockSum; decide +kernel

private theorem block5070766 : blockSum term 5070766 964 3624341 := by unfold blockSum; decide +kernel

private theorem block5071730 : blockSum term 5071730 964 3059941 := by unfold blockSum; decide +kernel

private theorem block5072694 : blockSum term 5072694 964 2997228 := by unfold blockSum; decide +kernel

private theorem block5073658 : blockSum term 5073658 964 3599497 := by unfold blockSum; decide +kernel

private theorem block5074622 : blockSum term 5074622 964 3755979 := by unfold blockSum; decide +kernel

private theorem block5075586 : blockSum term 5075586 964 3305257 := by unfold blockSum; decide +kernel

private theorem block5076550 : blockSum term 5076550 964 3517459 := by unfold blockSum; decide +kernel

private theorem block5077514 : blockSum term 5077514 965 3234599 := by unfold blockSum; decide +kernel

private theorem block5078479 : blockSum term 5078479 964 3828278 := by unfold blockSum; decide +kernel

private theorem block5079443 : blockSum term 5079443 964 3436625 := by unfold blockSum; decide +kernel

private theorem block5080407 : blockSum term 5080407 964 2939031 := by unfold blockSum; decide +kernel

private theorem block5081371 : blockSum term 5081371 964 3962468 := by unfold blockSum; decide +kernel

private theorem block5082335 : blockSum term 5082335 964 3140452 := by unfold blockSum; decide +kernel

private theorem block5083299 : blockSum term 5083299 964 3294895 := by unfold blockSum; decide +kernel

private theorem block5084263 : blockSum term 5084263 964 3501760 := by unfold blockSum; decide +kernel

private theorem block5085227 : blockSum term 5085227 965 3707829 := by unfold blockSum; decide +kernel

private theorem block5086192 : blockSum term 5086192 964 3269222 := by unfold blockSum; decide +kernel

private theorem block5087156 : blockSum term 5087156 964 3582141 := by unfold blockSum; decide +kernel

private theorem block5088120 : blockSum term 5088120 964 3145908 := by unfold blockSum; decide +kernel

private theorem block5089084 : blockSum term 5089084 964 3191007 := by unfold blockSum; decide +kernel

private theorem block5090048 : blockSum term 5090048 964 3448226 := by unfold blockSum; decide +kernel

private theorem block5091012 : blockSum term 5091012 964 3280374 := by unfold blockSum; decide +kernel

private theorem block5091976 : blockSum term 5091976 964 3324295 := by unfold blockSum; decide +kernel

private theorem block5092940 : blockSum term 5092940 965 3421273 := by unfold blockSum; decide +kernel

private theorem block5093905 : blockSum term 5093905 964 3044713 := by unfold blockSum; decide +kernel

private theorem block5094869 : blockSum term 5094869 964 3037293 := by unfold blockSum; decide +kernel

private theorem block5095833 : blockSum term 5095833 964 3081747 := by unfold blockSum; decide +kernel

private theorem block5096797 : blockSum term 5096797 964 3490722 := by unfold blockSum; decide +kernel

private theorem block5097761 : blockSum term 5097761 964 3273796 := by unfold blockSum; decide +kernel

private theorem block5098725 : blockSum term 5098725 964 3213409 := by unfold blockSum; decide +kernel

private theorem block5099689 : blockSum term 5099689 964 2843364 := by unfold blockSum; decide +kernel

private theorem block5100653 : blockSum term 5100653 965 3969952 := by unfold blockSum; decide +kernel

private theorem block5101618 : blockSum term 5101618 964 2673864 := by unfold blockSum; decide +kernel

private theorem block5102582 : blockSum term 5102582 964 3231058 := by unfold blockSum; decide +kernel

private theorem block5103546 : blockSum term 5103546 964 3375842 := by unfold blockSum; decide +kernel

private theorem block5104510 : blockSum term 5104510 964 2806368 := by unfold blockSum; decide +kernel

private theorem block5105474 : blockSum term 5105474 964 2697374 := by unfold blockSum; decide +kernel

private theorem block5106438 : blockSum term 5106438 964 3097161 := by unfold blockSum; decide +kernel

private theorem block5107402 : blockSum term 5107402 964 3442792 := by unfold blockSum; decide +kernel

private theorem block5108366 : blockSum term 5108366 965 2979120 := by unfold blockSum; decide +kernel

private theorem block5109331 : blockSum term 5109331 964 3122319 := by unfold blockSum; decide +kernel

private theorem block5110295 : blockSum term 5110295 964 3314619 := by unfold blockSum; decide +kernel

private theorem block5111259 : blockSum term 5111259 964 3005222 := by unfold blockSum; decide +kernel

private theorem block5112223 : blockSum term 5112223 964 3097367 := by unfold blockSum; decide +kernel

private theorem block5113187 : blockSum term 5113187 964 3189250 := by unfold blockSum; decide +kernel

private theorem block5114151 : blockSum term 5114151 964 3031502 := by unfold blockSum; decide +kernel

private theorem block5115115 : blockSum term 5115115 964 3122042 := by unfold blockSum; decide +kernel

private theorem block5116079 : blockSum term 5116079 965 2866346 := by unfold blockSum; decide +kernel

private theorem block5117044 : blockSum term 5117044 964 3055834 := by unfold blockSum; decide +kernel

private theorem block5118008 : blockSum term 5118008 964 2949004 := by unfold blockSum; decide +kernel

private theorem block5118972 : blockSum term 5118972 964 3087256 := by unfold blockSum; decide +kernel

private theorem block5119936 : blockSum term 5119936 964 2980908 := by unfold blockSum; decide +kernel

private theorem block5120900 : blockSum term 5120900 964 3216248 := by unfold blockSum; decide +kernel

private theorem block5121864 : blockSum term 5121864 964 3353422 := by unfold blockSum; decide +kernel

private theorem block5122828 : blockSum term 5122828 964 3391971 := by unfold blockSum; decide +kernel

private theorem block5123792 : blockSum term 5123792 965 2995957 := by unfold blockSum; decide +kernel

private theorem block5124757 : blockSum term 5124757 964 2939028 := by unfold blockSum; decide +kernel

private theorem block5125721 : blockSum term 5125721 964 3411959 := by unfold blockSum; decide +kernel

private theorem block5126685 : blockSum term 5126685 964 2635872 := by unfold blockSum; decide +kernel

private theorem block5127649 : blockSum term 5127649 964 2771350 := by unfold blockSum; decide +kernel

private theorem block5128613 : blockSum term 5128613 964 2954741 := by unfold blockSum; decide +kernel

private theorem block5129577 : blockSum term 5129577 964 2566297 := by unfold blockSum; decide +kernel

private theorem block5130541 : blockSum term 5130541 964 3270326 := by unfold blockSum; decide +kernel

private theorem block5131505 : blockSum term 5131505 965 3024246 := by unfold blockSum; decide +kernel

private theorem block5132470 : blockSum term 5132470 964 3157086 := by unfold blockSum; decide +kernel

private theorem block5133434 : blockSum term 5133434 964 3241978 := by unfold blockSum; decide +kernel

private theorem block5134398 : blockSum term 5134398 964 2904176 := by unfold blockSum; decide +kernel

private theorem block5135362 : blockSum term 5135362 964 2756430 := by unfold blockSum; decide +kernel

private theorem block5136326 : blockSum term 5136326 964 2842258 := by unfold blockSum; decide +kernel

private theorem block5137290 : blockSum term 5137290 964 2834006 := by unfold blockSum; decide +kernel

private theorem block5138254 : blockSum term 5138254 964 2733606 := by unfold blockSum; decide +kernel

private theorem block5139218 : blockSum term 5139218 965 3280330 := by unfold blockSum; decide +kernel

private theorem block5140183 : blockSum term 5140183 964 3178412 := by unfold blockSum; decide +kernel

private theorem block5141147 : blockSum term 5141147 964 2755657 := by unfold blockSum; decide +kernel

private theorem block5142111 : blockSum term 5142111 964 2610703 := by unfold blockSum; decide +kernel

private theorem block5143075 : blockSum term 5143075 964 2923051 := by unfold blockSum; decide +kernel

private theorem block5144039 : blockSum term 5144039 964 3187451 := by unfold blockSum; decide +kernel

private theorem block5145003 : blockSum term 5145003 964 2587639 := by unfold blockSum; decide +kernel

private theorem block5145967 : blockSum term 5145967 964 2851411 := by unfold blockSum; decide +kernel

private theorem block5146931 : blockSum term 5146931 965 2482518 := by unfold blockSum; decide +kernel

private theorem block5147896 : blockSum term 5147896 964 2520654 := by unfold blockSum; decide +kernel

private theorem block5148860 : blockSum term 5148860 964 2782480 := by unfold blockSum; decide +kernel

private theorem block5149824 : blockSum term 5149824 964 2729055 := by unfold blockSum; decide +kernel

private theorem block5150788 : blockSum term 5150788 964 3077527 := by unfold blockSum; decide +kernel

private theorem block5151752 : blockSum term 5151752 964 2846165 := by unfold blockSum; decide +kernel

private theorem block5152716 : blockSum term 5152716 964 2571256 := by unfold blockSum; decide +kernel

private theorem block5153680 : blockSum term 5153680 964 2873035 := by unfold blockSum; decide +kernel

private theorem block5154644 : blockSum term 5154644 965 2600448 := by unfold blockSum; decide +kernel

private theorem block5155609 : blockSum term 5155609 964 2811556 := by unfold blockSum; decide +kernel

private theorem block5156573 : blockSum term 5156573 964 2409247 := by unfold blockSum; decide +kernel

private theorem block5157537 : blockSum term 5157537 964 3057035 := by unfold blockSum; decide +kernel

private theorem block5158501 : blockSum term 5158501 964 2438641 := by unfold blockSum; decide +kernel

private theorem block5159465 : blockSum term 5159465 964 2779048 := by unfold blockSum; decide +kernel

private theorem block5160429 : blockSum term 5160429 964 2899900 := by unfold blockSum; decide +kernel

private theorem block5161393 : blockSum term 5161393 964 2632236 := by unfold blockSum; decide +kernel

private theorem block5162357 : blockSum term 5162357 965 2624552 := by unfold blockSum; decide +kernel

private theorem block5163322 : blockSum term 5163322 964 2658727 := by unfold blockSum; decide +kernel

private theorem block5164286 : blockSum term 5164286 964 2308911 := by unfold blockSum; decide +kernel

private theorem block5165250 : blockSum term 5165250 964 3026223 := by unfold blockSum; decide +kernel

private theorem block5166214 : blockSum term 5166214 964 2294453 := by unfold blockSum; decide +kernel

private theorem block5167178 : blockSum term 5167178 964 2838203 := by unfold blockSum; decide +kernel

private theorem block5168142 : blockSum term 5168142 964 2618331 := by unfold blockSum; decide +kernel

private theorem block5169106 : blockSum term 5169106 964 2736835 := by unfold blockSum; decide +kernel

private theorem block5170070 : blockSum term 5170070 965 2392797 := by unfold blockSum; decide +kernel

private theorem block5171035 : blockSum term 5171035 964 2971095 := by unfold blockSum; decide +kernel

private theorem block5171999 : blockSum term 5171999 964 2794683 := by unfold blockSum; decide +kernel

private theorem block5172963 : blockSum term 5172963 964 2286273 := by unfold blockSum; decide +kernel

private theorem block5173927 : blockSum term 5173927 964 2652284 := by unfold blockSum; decide +kernel

private theorem block5174891 : blockSum term 5174891 964 2396291 := by unfold blockSum; decide +kernel

private theorem block5175855 : blockSum term 5175855 964 2471344 := by unfold blockSum; decide +kernel

private theorem block5176819 : blockSum term 5176819 964 2217519 := by unfold blockSum; decide +kernel

private theorem block5177783 : blockSum term 5177783 965 2538235 := by unfold blockSum; decide +kernel

private theorem block5178748 : blockSum term 5178748 964 2529834 := by unfold blockSum; decide +kernel

private theorem block5179712 : blockSum term 5179712 964 2399944 := by unfold blockSum; decide +kernel

private theorem block5180676 : blockSum term 5180676 964 2635609 := by unfold blockSum; decide +kernel

private theorem block5181640 : blockSum term 5181640 964 2384881 := by unfold blockSum; decide +kernel

private theorem block5182604 : blockSum term 5182604 964 2376899 := by unfold blockSum; decide +kernel

private theorem block5183568 : blockSum term 5183568 964 2529852 := by unfold blockSum; decide +kernel

private theorem block5184532 : blockSum term 5184532 964 2601246 := by unfold blockSum; decide +kernel

private theorem block5185496 : blockSum term 5185496 965 2632196 := by unfold blockSum; decide +kernel

private theorem block5186461 : blockSum term 5186461 964 2265765 := by unfold blockSum; decide +kernel

private theorem block5187425 : blockSum term 5187425 964 2416503 := by unfold blockSum; decide +kernel

private theorem block5188389 : blockSum term 5188389 964 2408379 := by unfold blockSum; decide +kernel

private theorem block5189353 : blockSum term 5189353 964 2597092 := by unfold blockSum; decide +kernel

private theorem block5190317 : blockSum term 5190317 964 2274426 := by unfold blockSum; decide +kernel

private theorem block5191281 : blockSum term 5191281 964 2463152 := by unfold blockSum; decide +kernel

private theorem block5192245 : blockSum term 5192245 964 2143106 := by unfold blockSum; decide +kernel

private theorem block5193209 : blockSum term 5193209 965 2369228 := by unfold blockSum; decide +kernel

private theorem block5194174 : blockSum term 5194174 964 2709087 := by unfold blockSum; decide +kernel

private theorem block5195138 : blockSum term 5195138 964 2237067 := by unfold blockSum; decide +kernel

private theorem block5196102 : blockSum term 5196102 964 2422334 := by unfold blockSum; decide +kernel

private theorem block5197066 : blockSum term 5197066 964 2452109 := by unfold blockSum; decide +kernel

private theorem block5198030 : blockSum term 5198030 964 2710075 := by unfold blockSum; decide +kernel

private theorem block5198994 : blockSum term 5198994 964 2168235 := by unfold blockSum; decide +kernel

private theorem block5199958 : blockSum term 5199958 964 2236805 := by unfold blockSum; decide +kernel

private theorem block5200922 : blockSum term 5200922 965 2644600 := by unfold blockSum; decide +kernel

private theorem block5201887 : blockSum term 5201887 964 2446621 := by unfold blockSum; decide +kernel

private theorem block5202851 : blockSum term 5202851 964 2363180 := by unfold blockSum; decide +kernel

private theorem block5203815 : blockSum term 5203815 964 2542057 := by unfold blockSum; decide +kernel

private theorem block5204779 : blockSum term 5204779 964 2383806 := by unfold blockSum; decide +kernel

private theorem block5205743 : blockSum term 5205743 964 2709213 := by unfold blockSum; decide +kernel

private theorem block5206707 : blockSum term 5206707 964 2218857 := by unfold blockSum; decide +kernel

private theorem block5207671 : blockSum term 5207671 964 2100445 := by unfold blockSum; decide +kernel

private theorem block5208635 : blockSum term 5208635 965 2239789 := by unfold blockSum; decide +kernel

private theorem block5209600 : blockSum term 5209600 964 2305291 := by unfold blockSum; decide +kernel

private theorem block5210564 : blockSum term 5210564 964 1932624 := by unfold blockSum; decide +kernel

private theorem block5211528 : blockSum term 5211528 964 2217035 := by unfold blockSum; decide +kernel

private theorem block5212492 : blockSum term 5212492 964 2679531 := by unfold blockSum; decide +kernel

private theorem block5213456 : blockSum term 5213456 964 2164663 := by unfold blockSum; decide +kernel

private theorem block5214420 : blockSum term 5214420 964 2336747 := by unfold blockSum; decide +kernel

private theorem block5215384 : blockSum term 5215384 964 2435843 := by unfold blockSum; decide +kernel

private theorem block5216348 : blockSum term 5216348 965 1926653 := by unfold blockSum; decide +kernel

private theorem block5217313 : blockSum term 5217313 964 2204254 := by unfold blockSum; decide +kernel

private theorem block5218277 : blockSum term 5218277 964 2125539 := by unfold blockSum; decide +kernel

private theorem block5219241 : blockSum term 5219241 964 2364711 := by unfold blockSum; decide +kernel

private theorem block5220205 : blockSum term 5220205 964 2285859 := by unfold blockSum; decide +kernel

private theorem block5221169 : blockSum term 5221169 964 2277421 := by unfold blockSum; decide +kernel

private theorem block5222133 : blockSum term 5222133 964 2094327 := by unfold blockSum; decide +kernel

private theorem block5223097 : blockSum term 5223097 964 1808732 := by unfold blockSum; decide +kernel

private theorem block5224061 : blockSum term 5224061 965 2460286 := by unfold blockSum; decide +kernel

private theorem block5225026 : blockSum term 5225026 964 2106335 := by unfold blockSum; decide +kernel

private theorem block5225990 : blockSum term 5225990 964 2201081 := by unfold blockSum; decide +kernel

private theorem block5226954 : blockSum term 5226954 964 1953138 := by unfold blockSum; decide +kernel

private theorem block5227918 : blockSum term 5227918 964 2252953 := by unfold blockSum; decide +kernel

private theorem block5228882 : blockSum term 5228882 964 2176489 := by unfold blockSum; decide +kernel

private theorem block5229846 : blockSum term 5229846 964 2134209 := by unfold blockSum; decide +kernel

private theorem block5230810 : blockSum term 5230810 964 2193692 := by unfold blockSum; decide +kernel

private theorem block5231774 : blockSum term 5231774 965 1949903 := by unfold blockSum; decide +kernel

private theorem block5232739 : blockSum term 5232739 964 1975667 := by unfold blockSum; decide +kernel

private theorem block5233703 : blockSum term 5233703 964 2201537 := by unfold blockSum; decide +kernel

private theorem block5234667 : blockSum term 5234667 964 1894070 := by unfold blockSum; decide +kernel

private theorem block5235631 : blockSum term 5235631 965 1986178 := by unfold blockSum; decide +kernel

private theorem block5236596 : blockSum term 5236596 964 1912228 := by unfold blockSum; decide +kernel

private theorem block5237560 : blockSum term 5237560 964 2560864 := by unfold blockSum; decide +kernel

private theorem block5238524 : blockSum term 5238524 964 2026622 := by unfold blockSum; decide +kernel

private theorem block5239488 : blockSum term 5239488 965 1921458 := by unfold blockSum; decide +kernel

private theorem block5240453 : blockSum term 5240453 964 2108685 := by unfold blockSum; decide +kernel

private theorem block5241417 : blockSum term 5241417 964 1712858 := by unfold blockSum; decide +kernel

private theorem block5242381 : blockSum term 5242381 964 2317108 := by unfold blockSum; decide +kernel

private theorem block5243345 : blockSum term 5243345 964 2210999 := by unfold blockSum; decide +kernel

private theorem block5244309 : blockSum term 5244309 964 1946360 := by unfold blockSum; decide +kernel

private theorem block5245273 : blockSum term 5245273 964 1906340 := by unfold blockSum; decide +kernel

private theorem block5246237 : blockSum term 5246237 964 2151423 := by unfold blockSum; decide +kernel

private theorem block5247201 : blockSum term 5247201 965 2047626 := by unfold blockSum; decide +kernel

private theorem block5248166 : blockSum term 5248166 964 1976813 := by unfold blockSum; decide +kernel

private theorem block5249130 : blockSum term 5249130 964 2249678 := by unfold blockSum; decide +kernel

private theorem block5250094 : blockSum term 5250094 964 2146600 := by unfold blockSum; decide +kernel

private theorem block5251058 : blockSum term 5251058 964 1642321 := by unfold blockSum; decide +kernel

private theorem block5252022 : blockSum term 5252022 964 2315075 := by unfold blockSum; decide +kernel

private theorem block5252986 : blockSum term 5252986 964 1751434 := by unfold blockSum; decide +kernel

private theorem block5253950 : blockSum term 5253950 964 1835760 := by unfold blockSum; decide +kernel

private theorem block5254914 : blockSum term 5254914 965 1828249 := by unfold blockSum; decide +kernel

private theorem block5255879 : blockSum term 5255879 964 1790532 := by unfold blockSum; decide +kernel

private theorem block5256843 : blockSum term 5256843 964 1692521 := by unfold blockSum; decide +kernel

private theorem block5257807 : blockSum term 5257807 964 1745381 := by unfold blockSum; decide +kernel

private theorem block5258771 : blockSum term 5258771 964 1947706 := by unfold blockSum; decide +kernel

private theorem block5259735 : blockSum term 5259735 964 1879443 := by unfold blockSum; decide +kernel

private theorem block5260699 : blockSum term 5260699 964 1723543 := by unfold blockSum; decide +kernel

private theorem block5261663 : blockSum term 5261663 964 2070879 := by unfold blockSum; decide +kernel

private theorem block5262627 : blockSum term 5262627 965 1678568 := by unfold blockSum; decide +kernel

private theorem block5263592 : blockSum term 5263592 964 2140361 := by unfold blockSum; decide +kernel

private theorem block5264556 : blockSum term 5264556 964 1809373 := by unfold blockSum; decide +kernel

private theorem block5265520 : blockSum term 5265520 964 1800764 := by unfold blockSum; decide +kernel

private theorem block5266484 : blockSum term 5266484 964 1705807 := by unfold blockSum; decide +kernel

private theorem block5267448 : blockSum term 5267448 964 1698595 := by unfold blockSum; decide +kernel

private theorem block5268412 : blockSum term 5268412 964 1719570 := by unfold blockSum; decide +kernel

private theorem block5269376 : blockSum term 5269376 964 1740433 := by unfold blockSum; decide +kernel

private theorem block5270340 : blockSum term 5270340 965 1987446 := by unfold blockSum; decide +kernel

private theorem block5271305 : blockSum term 5271305 964 1977420 := by unfold blockSum; decide +kernel

private theorem block5272269 : blockSum term 5272269 964 1799284 := by unfold blockSum; decide +kernel

private theorem block5273233 : blockSum term 5273233 964 1707271 := by unfold blockSum; decide +kernel

private theorem block5274197 : blockSum term 5274197 964 1783174 := by unfold blockSum; decide +kernel

private theorem block5275161 : blockSum term 5275161 964 1497810 := by unfold blockSum; decide +kernel

private theorem block5276125 : blockSum term 5276125 964 1767476 := by unfold blockSum; decide +kernel

private theorem block5277089 : blockSum term 5277089 964 1567166 := by unfold blockSum; decide +kernel

private theorem block5278053 : blockSum term 5278053 965 1805930 := by unfold blockSum; decide +kernel

private theorem block5279018 : blockSum term 5279018 964 1634100 := by unfold blockSum; decide +kernel

private theorem block5279982 : blockSum term 5279982 964 1815810 := by unfold blockSum; decide +kernel

private theorem block5280946 : blockSum term 5280946 964 1402556 := by unfold blockSum; decide +kernel

private theorem block5281910 : blockSum term 5281910 964 1691171 := by unfold blockSum; decide +kernel

private theorem block5282874 : blockSum term 5282874 964 1416348 := by unfold blockSum; decide +kernel

private theorem block5283838 : blockSum term 5283838 964 1648480 := by unfold blockSum; decide +kernel

private theorem block5284802 : blockSum term 5284802 964 1402399 := by unfold blockSum; decide +kernel

private theorem block5285766 : blockSum term 5285766 965 1527211 := by unfold blockSum; decide +kernel

private theorem block5286731 : blockSum term 5286731 964 1781621 := by unfold blockSum; decide +kernel

private theorem block5287695 : blockSum term 5287695 964 1798708 := by unfold blockSum; decide +kernel

private theorem block5288659 : blockSum term 5288659 964 1607847 := by unfold blockSum; decide +kernel

private theorem block5289623 : blockSum term 5289623 964 1677643 := by unfold blockSum; decide +kernel

private theorem block5290587 : blockSum term 5290587 964 1745299 := by unfold blockSum; decide +kernel

private theorem block5291551 : blockSum term 5291551 964 1658969 := by unfold blockSum; decide +kernel

private theorem block5292515 : blockSum term 5292515 964 1422336 := by unfold blockSum; decide +kernel

private theorem block5293479 : blockSum term 5293479 965 1718578 := by unfold blockSum; decide +kernel

private theorem block5294444 : blockSum term 5294444 964 1609063 := by unfold blockSum; decide +kernel

private theorem block5295408 : blockSum term 5295408 964 1500827 := by unfold blockSum; decide +kernel

private theorem block5296372 : blockSum term 5296372 964 1592397 := by unfold blockSum; decide +kernel

private theorem block5297336 : blockSum term 5297336 964 1608441 := by unfold blockSum; decide +kernel

private theorem block5298300 : blockSum term 5298300 964 1427808 := by unfold blockSum; decide +kernel

private theorem block5299264 : blockSum term 5299264 964 1518538 := by unfold blockSum; decide +kernel

private theorem block5300228 : blockSum term 5300228 964 1535279 := by unfold blockSum; decide +kernel

private theorem block5301192 : blockSum term 5301192 965 1720830 := by unfold blockSum; decide +kernel

private theorem block5302157 : blockSum term 5302157 964 1398486 := by unfold blockSum; decide +kernel

private theorem block5303121 : blockSum term 5303121 964 1606741 := by unfold blockSum; decide +kernel

private theorem block5304085 : blockSum term 5304085 964 1574035 := by unfold blockSum; decide +kernel

private theorem block5305049 : blockSum term 5305049 964 1470191 := by unfold blockSum; decide +kernel

private theorem block5306013 : blockSum term 5306013 964 1509561 := by unfold blockSum; decide +kernel

private theorem block5306977 : blockSum term 5306977 964 1407858 := by unfold blockSum; decide +kernel

private theorem block5307941 : blockSum term 5307941 964 1399978 := by unfold blockSum; decide +kernel

private theorem block5308905 : blockSum term 5308905 965 1322857 := by unfold blockSum; decide +kernel

private theorem block5309870 : blockSum term 5309870 964 1292804 := by unfold blockSum; decide +kernel

private theorem block5310834 : blockSum term 5310834 964 1217056 := by unfold blockSum; decide +kernel

private theorem block5311798 : blockSum term 5311798 964 1507502 := by unfold blockSum; decide +kernel

private theorem block5312762 : blockSum term 5312762 964 1385741 := by unfold blockSum; decide +kernel

private theorem block5313726 : blockSum term 5313726 964 1513334 := by unfold blockSum; decide +kernel

private theorem block5314690 : blockSum term 5314690 964 1280275 := by unfold blockSum; decide +kernel

private theorem block5315654 : blockSum term 5315654 964 1541348 := by unfold blockSum; decide +kernel

private theorem block5316618 : blockSum term 5316618 965 1376833 := by unfold blockSum; decide +kernel

private theorem block5317583 : blockSum term 5317583 964 1302343 := by unfold blockSum; decide +kernel

private theorem block5318547 : blockSum term 5318547 964 1492230 := by unfold blockSum; decide +kernel

private theorem block5319511 : blockSum term 5319511 964 1243295 := by unfold blockSum; decide +kernel

private theorem block5320475 : blockSum term 5320475 964 1171215 := by unfold blockSum; decide +kernel

private theorem block5321439 : blockSum term 5321439 964 1423098 := by unfold blockSum; decide +kernel

private theorem block5322403 : blockSum term 5322403 964 1350672 := by unfold blockSum; decide +kernel

private theorem block5323367 : blockSum term 5323367 964 1215300 := by unfold blockSum; decide +kernel

private theorem block5324331 : blockSum term 5324331 965 1483041 := by unfold blockSum; decide +kernel

private theorem block5325296 : blockSum term 5325296 964 1431371 := by unfold blockSum; decide +kernel

private theorem block5326260 : blockSum term 5326260 964 1025622 := by unfold blockSum; decide +kernel

private theorem block5327224 : blockSum term 5327224 964 1518954 := by unfold blockSum; decide +kernel

private theorem block5328188 : blockSum term 5328188 964 1137157 := by unfold blockSum; decide +kernel

private theorem block5329152 : blockSum term 5329152 964 1314711 := by unfold blockSum; decide +kernel

private theorem block5330116 : blockSum term 5330116 964 1408973 := by unfold blockSum; decide +kernel

private theorem block5331080 : blockSum term 5331080 964 1217047 := by unfold blockSum; decide +kernel

private theorem block5332044 : blockSum term 5332044 965 1249699 := by unfold blockSum; decide +kernel

private theorem block5333009 : blockSum term 5333009 964 1342473 := by unfold blockSum; decide +kernel

private theorem block5333973 : blockSum term 5333973 964 1313165 := by unfold blockSum; decide +kernel

private theorem block5334937 : blockSum term 5334937 964 1206020 := by unfold blockSum; decide +kernel

private theorem block5335901 : blockSum term 5335901 964 1237679 := by unfold blockSum; decide +kernel

private theorem block5336865 : blockSum term 5336865 964 1093343 := by unfold blockSum; decide +kernel

private theorem block5337829 : blockSum term 5337829 964 1280545 := by unfold blockSum; decide +kernel

private theorem block5338793 : blockSum term 5338793 964 1137278 := by unfold blockSum; decide +kernel

private theorem block5339757 : blockSum term 5339757 965 1264311 := by unfold blockSum; decide +kernel

private theorem block5340722 : blockSum term 5340722 964 1217663 := by unfold blockSum; decide +kernel

private theorem block5341686 : blockSum term 5341686 964 1152753 := by unfold blockSum; decide +kernel

private theorem block5342650 : blockSum term 5342650 964 1257420 := by unfold blockSum; decide +kernel

private theorem block5343614 : blockSum term 5343614 964 1137049 := by unfold blockSum; decide +kernel

private theorem block5344578 : blockSum term 5344578 964 1147391 := by unfold blockSum; decide +kernel

private theorem block5345542 : blockSum term 5345542 964 1341493 := by unfold blockSum; decide +kernel

private theorem block5346506 : blockSum term 5346506 964 1094670 := by unfold blockSum; decide +kernel

private theorem block5347470 : blockSum term 5347470 965 1014209 := by unfold blockSum; decide +kernel

private theorem block5348435 : blockSum term 5348435 964 953828 := by unfold blockSum; decide +kernel

private theorem block5349399 : blockSum term 5349399 964 1090416 := by unfold blockSum; decide +kernel

private theorem block5350363 : blockSum term 5350363 964 958511 := by unfold blockSum; decide +kernel

private theorem block5351327 : blockSum term 5351327 964 1268219 := by unfold blockSum; decide +kernel

private theorem block5352291 : blockSum term 5352291 964 1014499 := by unfold blockSum; decide +kernel

private theorem block5353255 : blockSum term 5353255 964 1093845 := by unfold blockSum; decide +kernel

private theorem block5354219 : blockSum term 5354219 964 1102860 := by unfold blockSum; decide +kernel

private theorem block5355183 : blockSum term 5355183 965 1145786 := by unfold blockSum; decide +kernel

private theorem block5356148 : blockSum term 5356148 964 1035821 := by unfold blockSum; decide +kernel

private theorem block5357112 : blockSum term 5357112 964 1011425 := by unfold blockSum; decide +kernel

private theorem block5358076 : blockSum term 5358076 964 1037508 := by unfold blockSum; decide +kernel

private theorem block5359040 : blockSum term 5359040 965 996317 := by unfold blockSum; decide +kernel

private theorem block5360005 : blockSum term 5360005 964 1137079 := by unfold blockSum; decide +kernel

private theorem block5360969 : blockSum term 5360969 964 1144098 := by unfold blockSum; decide +kernel

private theorem block5361933 : blockSum term 5361933 964 843235 := by unfold blockSum; decide +kernel

private theorem block5362897 : blockSum term 5362897 965 998254 := by unfold blockSum; decide +kernel

private theorem block5363862 : blockSum term 5363862 964 878972 := by unfold blockSum; decide +kernel

private theorem block5364826 : blockSum term 5364826 964 951810 := by unfold blockSum; decide +kernel

private theorem block5365790 : blockSum term 5365790 964 1022500 := by unfold blockSum; decide +kernel

private theorem block5366754 : blockSum term 5366754 964 842494 := by unfold blockSum; decide +kernel

private theorem block5367718 : blockSum term 5367718 964 1083435 := by unfold blockSum; decide +kernel

private theorem block5368682 : blockSum term 5368682 964 981680 := by unfold blockSum; decide +kernel

private theorem block5369646 : blockSum term 5369646 964 790922 := by unfold blockSum; decide +kernel

private theorem block5370610 : blockSum term 5370610 965 860360 := by unfold blockSum; decide +kernel

private theorem block5371575 : blockSum term 5371575 964 1017504 := by unfold blockSum; decide +kernel

private theorem block5372539 : blockSum term 5372539 964 920196 := by unfold blockSum; decide +kernel

private theorem block5373503 : blockSum term 5373503 964 986099 := by unfold blockSum; decide +kernel

private theorem block5374467 : blockSum term 5374467 964 904405 := by unfold blockSum; decide +kernel

private theorem block5375431 : blockSum term 5375431 964 1041215 := by unfold blockSum; decide +kernel

private theorem block5376395 : blockSum term 5376395 964 974331 := by unfold blockSum; decide +kernel

private theorem block5377359 : blockSum term 5377359 964 865703 := by unfold blockSum; decide +kernel

private theorem block5378323 : blockSum term 5378323 965 928085 := by unfold blockSum; decide +kernel

private theorem block5379288 : blockSum term 5379288 964 780651 := by unfold blockSum; decide +kernel

private theorem block5380252 : blockSum term 5380252 964 787653 := by unfold blockSum; decide +kernel

private theorem block5381216 : blockSum term 5381216 964 958459 := by unfold blockSum; decide +kernel

private theorem block5382180 : blockSum term 5382180 964 962732 := by unfold blockSum; decide +kernel

private theorem block5383144 : blockSum term 5383144 964 939205 := by unfold blockSum; decide +kernel

private theorem block5384108 : blockSum term 5384108 964 850256 := by unfold blockSum; decide +kernel

private theorem block5385072 : blockSum term 5385072 964 736854 := by unfold blockSum; decide +kernel

private theorem block5386036 : blockSum term 5386036 965 652029 := by unfold blockSum; decide +kernel

private theorem block5387001 : blockSum term 5387001 964 1007993 := by unfold blockSum; decide +kernel

private theorem block5387965 : blockSum term 5387965 964 716516 := by unfold blockSum; decide +kernel

private theorem block5388929 : blockSum term 5388929 964 772876 := by unfold blockSum; decide +kernel

private theorem block5389893 : blockSum term 5389893 964 790304 := by unfold blockSum; decide +kernel

private theorem block5390857 : blockSum term 5390857 964 782277 := by unfold blockSum; decide +kernel

private theorem block5391821 : blockSum term 5391821 964 749424 := by unfold blockSum; decide +kernel

private theorem block5392785 : blockSum term 5392785 964 656833 := by unfold blockSum; decide +kernel

private theorem block5393749 : blockSum term 5393749 965 710693 := by unfold blockSum; decide +kernel

private theorem block5394714 : blockSum term 5394714 964 762832 := by unfold blockSum; decide +kernel

private theorem block5395678 : blockSum term 5395678 964 695310 := by unfold blockSum; decide +kernel

private theorem block5396642 : blockSum term 5396642 964 676346 := by unfold blockSum; decide +kernel

private theorem block5397606 : blockSum term 5397606 964 830845 := by unfold blockSum; decide +kernel

private theorem block5398570 : blockSum term 5398570 964 696317 := by unfold blockSum; decide +kernel

private theorem block5399534 : blockSum term 5399534 964 655447 := by unfold blockSum; decide +kernel

private theorem block5400498 : blockSum term 5400498 964 737175 := by unfold blockSum; decide +kernel

private theorem block5401462 : blockSum term 5401462 965 640970 := by unfold blockSum; decide +kernel

private theorem block5402427 : blockSum term 5402427 964 557741 := by unfold blockSum; decide +kernel

private theorem block5403391 : blockSum term 5403391 964 735323 := by unfold blockSum; decide +kernel

private theorem block5404355 : blockSum term 5404355 964 619374 := by unfold blockSum; decide +kernel

private theorem block5405319 : blockSum term 5405319 964 622336 := by unfold blockSum; decide +kernel

private theorem block5406283 : blockSum term 5406283 964 687566 := by unfold blockSum; decide +kernel

private theorem block5407247 : blockSum term 5407247 964 648265 := by unfold blockSum; decide +kernel

private theorem block5408211 : blockSum term 5408211 964 660100 := by unfold blockSum; decide +kernel

private theorem block5409175 : blockSum term 5409175 965 571499 := by unfold blockSum; decide +kernel

private theorem block5410140 : blockSum term 5410140 964 751521 := by unfold blockSum; decide +kernel

private theorem block5411104 : blockSum term 5411104 964 546963 := by unfold blockSum; decide +kernel

private theorem block5412068 : blockSum term 5412068 964 540375 := by unfold blockSum; decide +kernel

private theorem block5413032 : blockSum term 5413032 964 553141 := by unfold blockSum; decide +kernel

private theorem block5413996 : blockSum term 5413996 964 639521 := by unfold blockSum; decide +kernel

private theorem block5414960 : blockSum term 5414960 964 602620 := by unfold blockSum; decide +kernel

private theorem block5415924 : blockSum term 5415924 964 567010 := by unfold blockSum; decide +kernel

private theorem block5416888 : blockSum term 5416888 965 594963 := by unfold blockSum; decide +kernel

private theorem block5417853 : blockSum term 5417853 964 479915 := by unfold blockSum; decide +kernel

private theorem block5418817 : blockSum term 5418817 964 464933 := by unfold blockSum; decide +kernel

private theorem block5419781 : blockSum term 5419781 964 605807 := by unfold blockSum; decide +kernel

private theorem block5420745 : blockSum term 5420745 964 537239 := by unfold blockSum; decide +kernel

private theorem block5421709 : blockSum term 5421709 964 554125 := by unfold blockSum; decide +kernel

private theorem block5422673 : blockSum term 5422673 964 512628 := by unfold blockSum; decide +kernel

private theorem block5423637 : blockSum term 5423637 964 529345 := by unfold blockSum; decide +kernel

private theorem block5424601 : blockSum term 5424601 965 497209 := by unfold blockSum; decide +kernel

private theorem block5425566 : blockSum term 5425566 964 520815 := by unfold blockSum; decide +kernel

private theorem block5426530 : blockSum term 5426530 964 465671 := by unfold blockSum; decide +kernel

private theorem block5427494 : blockSum term 5427494 964 450612 := by unfold blockSum; decide +kernel

private theorem block5428458 : blockSum term 5428458 964 481438 := by unfold blockSum; decide +kernel

private theorem block5429422 : blockSum term 5429422 964 495371 := by unfold blockSum; decide +kernel

private theorem block5430386 : blockSum term 5430386 964 465089 := by unfold blockSum; decide +kernel

private theorem block5431350 : blockSum term 5431350 964 407431 := by unfold blockSum; decide +kernel

private theorem block5432314 : blockSum term 5432314 965 428957 := by unfold blockSum; decide +kernel

private theorem block5433279 : blockSum term 5433279 964 476762 := by unfold blockSum; decide +kernel

private theorem block5434243 : blockSum term 5434243 964 339455 := by unfold blockSum; decide +kernel

private theorem block5435207 : blockSum term 5435207 964 373518 := by unfold blockSum; decide +kernel

private theorem block5436171 : blockSum term 5436171 964 451927 := by unfold blockSum; decide +kernel

private theorem block5437135 : blockSum term 5437135 964 429693 := by unfold blockSum; decide +kernel

private theorem block5438099 : blockSum term 5438099 964 389856 := by unfold blockSum; decide +kernel

private theorem block5439063 : blockSum term 5439063 964 418135 := by unfold blockSum; decide +kernel

private theorem block5440027 : blockSum term 5440027 965 378571 := by unfold blockSum; decide +kernel

private theorem block5440992 : blockSum term 5440992 964 340881 := by unfold blockSum; decide +kernel

private theorem block5441956 : blockSum term 5441956 964 322535 := by unfold blockSum; decide +kernel

private theorem block5442920 : blockSum term 5442920 964 310022 := by unfold blockSum; decide +kernel

private theorem block5443884 : blockSum term 5443884 964 374964 := by unfold blockSum; decide +kernel

private theorem block5444848 : blockSum term 5444848 964 350439 := by unfold blockSum; decide +kernel

private theorem block5445812 : blockSum term 5445812 964 289786 := by unfold blockSum; decide +kernel

private theorem block5446776 : blockSum term 5446776 964 319249 := by unfold blockSum; decide +kernel

private theorem block5447740 : blockSum term 5447740 965 346766 := by unfold blockSum; decide +kernel

private theorem block5448705 : blockSum term 5448705 964 289320 := by unfold blockSum; decide +kernel

private theorem block5449669 : blockSum term 5449669 964 362647 := by unfold blockSum; decide +kernel

private theorem block5450633 : blockSum term 5450633 964 283055 := by unfold blockSum; decide +kernel

private theorem block5451597 : blockSum term 5451597 964 257811 := by unfold blockSum; decide +kernel

private theorem block5452561 : blockSum term 5452561 964 281445 := by unfold blockSum; decide +kernel

private theorem block5453525 : blockSum term 5453525 964 273191 := by unfold blockSum; decide +kernel

private theorem block5454489 : blockSum term 5454489 964 219799 := by unfold blockSum; decide +kernel

private theorem block5455453 : blockSum term 5455453 965 262465 := by unfold blockSum; decide +kernel

private theorem block5456418 : blockSum term 5456418 964 254653 := by unfold blockSum; decide +kernel

private theorem block5457382 : blockSum term 5457382 964 249640 := by unfold blockSum; decide +kernel

private theorem block5458346 : blockSum term 5458346 964 227276 := by unfold blockSum; decide +kernel

private theorem block5459310 : blockSum term 5459310 964 243281 := by unfold blockSum; decide +kernel

private theorem block5460274 : blockSum term 5460274 964 207104 := by unfold blockSum; decide +kernel

private theorem block5461238 : blockSum term 5461238 964 206264 := by unfold blockSum; decide +kernel

private theorem block5462202 : blockSum term 5462202 964 220545 := by unfold blockSum; decide +kernel

private theorem block5463166 : blockSum term 5463166 965 166545 := by unfold blockSum; decide +kernel

private theorem block5464131 : blockSum term 5464131 964 180424 := by unfold blockSum; decide +kernel

private theorem block5465095 : blockSum term 5465095 964 184206 := by unfold blockSum; decide +kernel

private theorem block5466059 : blockSum term 5466059 964 154640 := by unfold blockSum; decide +kernel

private theorem block5467023 : blockSum term 5467023 964 144944 := by unfold blockSum; decide +kernel

private theorem block5467987 : blockSum term 5467987 964 152458 := by unfold blockSum; decide +kernel

private theorem block5468951 : blockSum term 5468951 964 132707 := by unfold blockSum; decide +kernel

private theorem block5469915 : blockSum term 5469915 964 121809 := by unfold blockSum; decide +kernel

private theorem block5470879 : blockSum term 5470879 965 129078 := by unfold blockSum; decide +kernel

private theorem block5471844 : blockSum term 5471844 964 126943 := by unfold blockSum; decide +kernel

private theorem block5472808 : blockSum term 5472808 964 113046 := by unfold blockSum; decide +kernel

private theorem block5473772 : blockSum term 5473772 964 102009 := by unfold blockSum; decide +kernel

private theorem block5474736 : blockSum term 5474736 964 89746 := by unfold blockSum; decide +kernel

private theorem block5475700 : blockSum term 5475700 964 86740 := by unfold blockSum; decide +kernel

private theorem block5476664 : blockSum term 5476664 964 84243 := by unfold blockSum; decide +kernel

private theorem block5477628 : blockSum term 5477628 964 65748 := by unfold blockSum; decide +kernel

private theorem block5478592 : blockSum term 5478592 965 56109 := by unfold blockSum; decide +kernel

private theorem block5479557 : blockSum term 5479557 964 61782 := by unfold blockSum; decide +kernel

private theorem block5480521 : blockSum term 5480521 964 56815 := by unfold blockSum; decide +kernel

private theorem block5481485 : blockSum term 5481485 964 42800 := by unfold blockSum; decide +kernel

private theorem block5482449 : blockSum term 5482449 965 30476 := by unfold blockSum; decide +kernel

private theorem block5483414 : blockSum term 5483414 964 27771 := by unfold blockSum; decide +kernel

private theorem block5484378 : blockSum term 5484378 964 17764 := by unfold blockSum; decide +kernel

private theorem block5485342 : blockSum term 5485342 964 12317 := by unfold blockSum; decide +kernel

private theorem block5486306 : blockSum term 5486306 965 3706 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem after_cut : blockSum term 4500001 987270 4359356685 := (join_sums term (lo:=4500001) (a:=493635) (b:=493635) (join_sums term (lo:=4500001) (a:=246817) (b:=246818) (join_sums term (lo:=4500001) (a:=123408) (b:=123409) (join_sums term (lo:=4500001) (a:=61704) (b:=61704) (join_sums term (lo:=4500001) (a:=30852) (b:=30852) (join_sums term (lo:=4500001) (a:=15426) (b:=15426) (join_sums term (lo:=4500001) (a:=7713) (b:=7713) (join_sums term (lo:=4500001) (a:=3856) (b:=3857) (join_sums term (lo:=4500001) (a:=1928) (b:=1928) (join_sums term (lo:=4500001) (a:=964) (b:=964) block4500001 block4500965) (join_sums term (lo:=4501929) (a:=964) (b:=964) block4501929 block4502893)) (join_sums term (lo:=4503857) (a:=1928) (b:=1929) (join_sums term (lo:=4503857) (a:=964) (b:=964) block4503857 block4504821) (join_sums term (lo:=4505785) (a:=964) (b:=965) block4505785 block4506749))) (join_sums term (lo:=4507714) (a:=3856) (b:=3857) (join_sums term (lo:=4507714) (a:=1928) (b:=1928) (join_sums term (lo:=4507714) (a:=964) (b:=964) block4507714 block4508678) (join_sums term (lo:=4509642) (a:=964) (b:=964) block4509642 block4510606)) (join_sums term (lo:=4511570) (a:=1928) (b:=1929) (join_sums term (lo:=4511570) (a:=964) (b:=964) block4511570 block4512534) (join_sums term (lo:=4513498) (a:=964) (b:=965) block4513498 block4514462)))) (join_sums term (lo:=4515427) (a:=7713) (b:=7713) (join_sums term (lo:=4515427) (a:=3856) (b:=3857) (join_sums term (lo:=4515427) (a:=1928) (b:=1928) (join_sums term (lo:=4515427) (a:=964) (b:=964) block4515427 block4516391) (join_sums term (lo:=4517355) (a:=964) (b:=964) block4517355 block4518319)) (join_sums term (lo:=4519283) (a:=1928) (b:=1929) (join_sums term (lo:=4519283) (a:=964) (b:=964) block4519283 block4520247) (join_sums term (lo:=4521211) (a:=964) (b:=965) block4521211 block4522175))) (join_sums term (lo:=4523140) (a:=3856) (b:=3857) (join_sums term (lo:=4523140) (a:=1928) (b:=1928) (join_sums term (lo:=4523140) (a:=964) (b:=964) block4523140 block4524104) (join_sums term (lo:=4525068) (a:=964) (b:=964) block4525068 block4526032)) (join_sums term (lo:=4526996) (a:=1928) (b:=1929) (join_sums term (lo:=4526996) (a:=964) (b:=964) block4526996 block4527960) (join_sums term (lo:=4528924) (a:=964) (b:=965) block4528924 block4529888))))) (join_sums term (lo:=4530853) (a:=15426) (b:=15426) (join_sums term (lo:=4530853) (a:=7713) (b:=7713) (join_sums term (lo:=4530853) (a:=3856) (b:=3857) (join_sums term (lo:=4530853) (a:=1928) (b:=1928) (join_sums term (lo:=4530853) (a:=964) (b:=964) block4530853 block4531817) (join_sums term (lo:=4532781) (a:=964) (b:=964) block4532781 block4533745)) (join_sums term (lo:=4534709) (a:=1928) (b:=1929) (join_sums term (lo:=4534709) (a:=964) (b:=964) block4534709 block4535673) (join_sums term (lo:=4536637) (a:=964) (b:=965) block4536637 block4537601))) (join_sums term (lo:=4538566) (a:=3856) (b:=3857) (join_sums term (lo:=4538566) (a:=1928) (b:=1928) (join_sums term (lo:=4538566) (a:=964) (b:=964) block4538566 block4539530) (join_sums term (lo:=4540494) (a:=964) (b:=964) block4540494 block4541458)) (join_sums term (lo:=4542422) (a:=1928) (b:=1929) (join_sums term (lo:=4542422) (a:=964) (b:=964) block4542422 block4543386) (join_sums term (lo:=4544350) (a:=964) (b:=965) block4544350 block4545314)))) (join_sums term (lo:=4546279) (a:=7713) (b:=7713) (join_sums term (lo:=4546279) (a:=3856) (b:=3857) (join_sums term (lo:=4546279) (a:=1928) (b:=1928) (join_sums term (lo:=4546279) (a:=964) (b:=964) block4546279 block4547243) (join_sums term (lo:=4548207) (a:=964) (b:=964) block4548207 block4549171)) (join_sums term (lo:=4550135) (a:=1928) (b:=1929) (join_sums term (lo:=4550135) (a:=964) (b:=964) block4550135 block4551099) (join_sums term (lo:=4552063) (a:=964) (b:=965) block4552063 block4553027))) (join_sums term (lo:=4553992) (a:=3856) (b:=3857) (join_sums term (lo:=4553992) (a:=1928) (b:=1928) (join_sums term (lo:=4553992) (a:=964) (b:=964) block4553992 block4554956) (join_sums term (lo:=4555920) (a:=964) (b:=964) block4555920 block4556884)) (join_sums term (lo:=4557848) (a:=1928) (b:=1929) (join_sums term (lo:=4557848) (a:=964) (b:=964) block4557848 block4558812) (join_sums term (lo:=4559776) (a:=964) (b:=965) block4559776 block4560740)))))) (join_sums term (lo:=4561705) (a:=30852) (b:=30852) (join_sums term (lo:=4561705) (a:=15426) (b:=15426) (join_sums term (lo:=4561705) (a:=7713) (b:=7713) (join_sums term (lo:=4561705) (a:=3856) (b:=3857) (join_sums term (lo:=4561705) (a:=1928) (b:=1928) (join_sums term (lo:=4561705) (a:=964) (b:=964) block4561705 block4562669) (join_sums term (lo:=4563633) (a:=964) (b:=964) block4563633 block4564597)) (join_sums term (lo:=4565561) (a:=1928) (b:=1929) (join_sums term (lo:=4565561) (a:=964) (b:=964) block4565561 block4566525) (join_sums term (lo:=4567489) (a:=964) (b:=965) block4567489 block4568453))) (join_sums term (lo:=4569418) (a:=3856) (b:=3857) (join_sums term (lo:=4569418) (a:=1928) (b:=1928) (join_sums term (lo:=4569418) (a:=964) (b:=964) block4569418 block4570382) (join_sums term (lo:=4571346) (a:=964) (b:=964) block4571346 block4572310)) (join_sums term (lo:=4573274) (a:=1928) (b:=1929) (join_sums term (lo:=4573274) (a:=964) (b:=964) block4573274 block4574238) (join_sums term (lo:=4575202) (a:=964) (b:=965) block4575202 block4576166)))) (join_sums term (lo:=4577131) (a:=7713) (b:=7713) (join_sums term (lo:=4577131) (a:=3856) (b:=3857) (join_sums term (lo:=4577131) (a:=1928) (b:=1928) (join_sums term (lo:=4577131) (a:=964) (b:=964) block4577131 block4578095) (join_sums term (lo:=4579059) (a:=964) (b:=964) block4579059 block4580023)) (join_sums term (lo:=4580987) (a:=1928) (b:=1929) (join_sums term (lo:=4580987) (a:=964) (b:=964) block4580987 block4581951) (join_sums term (lo:=4582915) (a:=964) (b:=965) block4582915 block4583879))) (join_sums term (lo:=4584844) (a:=3856) (b:=3857) (join_sums term (lo:=4584844) (a:=1928) (b:=1928) (join_sums term (lo:=4584844) (a:=964) (b:=964) block4584844 block4585808) (join_sums term (lo:=4586772) (a:=964) (b:=964) block4586772 block4587736)) (join_sums term (lo:=4588700) (a:=1928) (b:=1929) (join_sums term (lo:=4588700) (a:=964) (b:=964) block4588700 block4589664) (join_sums term (lo:=4590628) (a:=964) (b:=965) block4590628 block4591592))))) (join_sums term (lo:=4592557) (a:=15426) (b:=15426) (join_sums term (lo:=4592557) (a:=7713) (b:=7713) (join_sums term (lo:=4592557) (a:=3856) (b:=3857) (join_sums term (lo:=4592557) (a:=1928) (b:=1928) (join_sums term (lo:=4592557) (a:=964) (b:=964) block4592557 block4593521) (join_sums term (lo:=4594485) (a:=964) (b:=964) block4594485 block4595449)) (join_sums term (lo:=4596413) (a:=1928) (b:=1929) (join_sums term (lo:=4596413) (a:=964) (b:=964) block4596413 block4597377) (join_sums term (lo:=4598341) (a:=964) (b:=965) block4598341 block4599305))) (join_sums term (lo:=4600270) (a:=3856) (b:=3857) (join_sums term (lo:=4600270) (a:=1928) (b:=1928) (join_sums term (lo:=4600270) (a:=964) (b:=964) block4600270 block4601234) (join_sums term (lo:=4602198) (a:=964) (b:=964) block4602198 block4603162)) (join_sums term (lo:=4604126) (a:=1928) (b:=1929) (join_sums term (lo:=4604126) (a:=964) (b:=964) block4604126 block4605090) (join_sums term (lo:=4606054) (a:=964) (b:=965) block4606054 block4607018)))) (join_sums term (lo:=4607983) (a:=7713) (b:=7713) (join_sums term (lo:=4607983) (a:=3856) (b:=3857) (join_sums term (lo:=4607983) (a:=1928) (b:=1928) (join_sums term (lo:=4607983) (a:=964) (b:=964) block4607983 block4608947) (join_sums term (lo:=4609911) (a:=964) (b:=964) block4609911 block4610875)) (join_sums term (lo:=4611839) (a:=1928) (b:=1929) (join_sums term (lo:=4611839) (a:=964) (b:=964) block4611839 block4612803) (join_sums term (lo:=4613767) (a:=964) (b:=965) block4613767 block4614731))) (join_sums term (lo:=4615696) (a:=3856) (b:=3857) (join_sums term (lo:=4615696) (a:=1928) (b:=1928) (join_sums term (lo:=4615696) (a:=964) (b:=964) block4615696 block4616660) (join_sums term (lo:=4617624) (a:=964) (b:=964) block4617624 block4618588)) (join_sums term (lo:=4619552) (a:=1928) (b:=1929) (join_sums term (lo:=4619552) (a:=964) (b:=964) block4619552 block4620516) (join_sums term (lo:=4621480) (a:=964) (b:=965) block4621480 block4622444))))))) (join_sums term (lo:=4623409) (a:=61704) (b:=61705) (join_sums term (lo:=4623409) (a:=30852) (b:=30852) (join_sums term (lo:=4623409) (a:=15426) (b:=15426) (join_sums term (lo:=4623409) (a:=7713) (b:=7713) (join_sums term (lo:=4623409) (a:=3856) (b:=3857) (join_sums term (lo:=4623409) (a:=1928) (b:=1928) (join_sums term (lo:=4623409) (a:=964) (b:=964) block4623409 block4624373) (join_sums term (lo:=4625337) (a:=964) (b:=964) block4625337 block4626301)) (join_sums term (lo:=4627265) (a:=1928) (b:=1929) (join_sums term (lo:=4627265) (a:=964) (b:=964) block4627265 block4628229) (join_sums term (lo:=4629193) (a:=964) (b:=965) block4629193 block4630157))) (join_sums term (lo:=4631122) (a:=3856) (b:=3857) (join_sums term (lo:=4631122) (a:=1928) (b:=1928) (join_sums term (lo:=4631122) (a:=964) (b:=964) block4631122 block4632086) (join_sums term (lo:=4633050) (a:=964) (b:=964) block4633050 block4634014)) (join_sums term (lo:=4634978) (a:=1928) (b:=1929) (join_sums term (lo:=4634978) (a:=964) (b:=964) block4634978 block4635942) (join_sums term (lo:=4636906) (a:=964) (b:=965) block4636906 block4637870)))) (join_sums term (lo:=4638835) (a:=7713) (b:=7713) (join_sums term (lo:=4638835) (a:=3856) (b:=3857) (join_sums term (lo:=4638835) (a:=1928) (b:=1928) (join_sums term (lo:=4638835) (a:=964) (b:=964) block4638835 block4639799) (join_sums term (lo:=4640763) (a:=964) (b:=964) block4640763 block4641727)) (join_sums term (lo:=4642691) (a:=1928) (b:=1929) (join_sums term (lo:=4642691) (a:=964) (b:=964) block4642691 block4643655) (join_sums term (lo:=4644619) (a:=964) (b:=965) block4644619 block4645583))) (join_sums term (lo:=4646548) (a:=3856) (b:=3857) (join_sums term (lo:=4646548) (a:=1928) (b:=1928) (join_sums term (lo:=4646548) (a:=964) (b:=964) block4646548 block4647512) (join_sums term (lo:=4648476) (a:=964) (b:=964) block4648476 block4649440)) (join_sums term (lo:=4650404) (a:=1928) (b:=1929) (join_sums term (lo:=4650404) (a:=964) (b:=964) block4650404 block4651368) (join_sums term (lo:=4652332) (a:=964) (b:=965) block4652332 block4653296))))) (join_sums term (lo:=4654261) (a:=15426) (b:=15426) (join_sums term (lo:=4654261) (a:=7713) (b:=7713) (join_sums term (lo:=4654261) (a:=3856) (b:=3857) (join_sums term (lo:=4654261) (a:=1928) (b:=1928) (join_sums term (lo:=4654261) (a:=964) (b:=964) block4654261 block4655225) (join_sums term (lo:=4656189) (a:=964) (b:=964) block4656189 block4657153)) (join_sums term (lo:=4658117) (a:=1928) (b:=1929) (join_sums term (lo:=4658117) (a:=964) (b:=964) block4658117 block4659081) (join_sums term (lo:=4660045) (a:=964) (b:=965) block4660045 block4661009))) (join_sums term (lo:=4661974) (a:=3856) (b:=3857) (join_sums term (lo:=4661974) (a:=1928) (b:=1928) (join_sums term (lo:=4661974) (a:=964) (b:=964) block4661974 block4662938) (join_sums term (lo:=4663902) (a:=964) (b:=964) block4663902 block4664866)) (join_sums term (lo:=4665830) (a:=1928) (b:=1929) (join_sums term (lo:=4665830) (a:=964) (b:=964) block4665830 block4666794) (join_sums term (lo:=4667758) (a:=964) (b:=965) block4667758 block4668722)))) (join_sums term (lo:=4669687) (a:=7713) (b:=7713) (join_sums term (lo:=4669687) (a:=3856) (b:=3857) (join_sums term (lo:=4669687) (a:=1928) (b:=1928) (join_sums term (lo:=4669687) (a:=964) (b:=964) block4669687 block4670651) (join_sums term (lo:=4671615) (a:=964) (b:=964) block4671615 block4672579)) (join_sums term (lo:=4673543) (a:=1928) (b:=1929) (join_sums term (lo:=4673543) (a:=964) (b:=964) block4673543 block4674507) (join_sums term (lo:=4675471) (a:=964) (b:=965) block4675471 block4676435))) (join_sums term (lo:=4677400) (a:=3856) (b:=3857) (join_sums term (lo:=4677400) (a:=1928) (b:=1928) (join_sums term (lo:=4677400) (a:=964) (b:=964) block4677400 block4678364) (join_sums term (lo:=4679328) (a:=964) (b:=964) block4679328 block4680292)) (join_sums term (lo:=4681256) (a:=1928) (b:=1929) (join_sums term (lo:=4681256) (a:=964) (b:=964) block4681256 block4682220) (join_sums term (lo:=4683184) (a:=964) (b:=965) block4683184 block4684148)))))) (join_sums term (lo:=4685113) (a:=30852) (b:=30853) (join_sums term (lo:=4685113) (a:=15426) (b:=15426) (join_sums term (lo:=4685113) (a:=7713) (b:=7713) (join_sums term (lo:=4685113) (a:=3856) (b:=3857) (join_sums term (lo:=4685113) (a:=1928) (b:=1928) (join_sums term (lo:=4685113) (a:=964) (b:=964) block4685113 block4686077) (join_sums term (lo:=4687041) (a:=964) (b:=964) block4687041 block4688005)) (join_sums term (lo:=4688969) (a:=1928) (b:=1929) (join_sums term (lo:=4688969) (a:=964) (b:=964) block4688969 block4689933) (join_sums term (lo:=4690897) (a:=964) (b:=965) block4690897 block4691861))) (join_sums term (lo:=4692826) (a:=3856) (b:=3857) (join_sums term (lo:=4692826) (a:=1928) (b:=1928) (join_sums term (lo:=4692826) (a:=964) (b:=964) block4692826 block4693790) (join_sums term (lo:=4694754) (a:=964) (b:=964) block4694754 block4695718)) (join_sums term (lo:=4696682) (a:=1928) (b:=1929) (join_sums term (lo:=4696682) (a:=964) (b:=964) block4696682 block4697646) (join_sums term (lo:=4698610) (a:=964) (b:=965) block4698610 block4699574)))) (join_sums term (lo:=4700539) (a:=7713) (b:=7713) (join_sums term (lo:=4700539) (a:=3856) (b:=3857) (join_sums term (lo:=4700539) (a:=1928) (b:=1928) (join_sums term (lo:=4700539) (a:=964) (b:=964) block4700539 block4701503) (join_sums term (lo:=4702467) (a:=964) (b:=964) block4702467 block4703431)) (join_sums term (lo:=4704395) (a:=1928) (b:=1929) (join_sums term (lo:=4704395) (a:=964) (b:=964) block4704395 block4705359) (join_sums term (lo:=4706323) (a:=964) (b:=965) block4706323 block4707287))) (join_sums term (lo:=4708252) (a:=3856) (b:=3857) (join_sums term (lo:=4708252) (a:=1928) (b:=1928) (join_sums term (lo:=4708252) (a:=964) (b:=964) block4708252 block4709216) (join_sums term (lo:=4710180) (a:=964) (b:=964) block4710180 block4711144)) (join_sums term (lo:=4712108) (a:=1928) (b:=1929) (join_sums term (lo:=4712108) (a:=964) (b:=964) block4712108 block4713072) (join_sums term (lo:=4714036) (a:=964) (b:=965) block4714036 block4715000))))) (join_sums term (lo:=4715965) (a:=15426) (b:=15427) (join_sums term (lo:=4715965) (a:=7713) (b:=7713) (join_sums term (lo:=4715965) (a:=3856) (b:=3857) (join_sums term (lo:=4715965) (a:=1928) (b:=1928) (join_sums term (lo:=4715965) (a:=964) (b:=964) block4715965 block4716929) (join_sums term (lo:=4717893) (a:=964) (b:=964) block4717893 block4718857)) (join_sums term (lo:=4719821) (a:=1928) (b:=1929) (join_sums term (lo:=4719821) (a:=964) (b:=964) block4719821 block4720785) (join_sums term (lo:=4721749) (a:=964) (b:=965) block4721749 block4722713))) (join_sums term (lo:=4723678) (a:=3856) (b:=3857) (join_sums term (lo:=4723678) (a:=1928) (b:=1928) (join_sums term (lo:=4723678) (a:=964) (b:=964) block4723678 block4724642) (join_sums term (lo:=4725606) (a:=964) (b:=964) block4725606 block4726570)) (join_sums term (lo:=4727534) (a:=1928) (b:=1929) (join_sums term (lo:=4727534) (a:=964) (b:=964) block4727534 block4728498) (join_sums term (lo:=4729462) (a:=964) (b:=965) block4729462 block4730426)))) (join_sums term (lo:=4731391) (a:=7713) (b:=7714) (join_sums term (lo:=4731391) (a:=3856) (b:=3857) (join_sums term (lo:=4731391) (a:=1928) (b:=1928) (join_sums term (lo:=4731391) (a:=964) (b:=964) block4731391 block4732355) (join_sums term (lo:=4733319) (a:=964) (b:=964) block4733319 block4734283)) (join_sums term (lo:=4735247) (a:=1928) (b:=1929) (join_sums term (lo:=4735247) (a:=964) (b:=964) block4735247 block4736211) (join_sums term (lo:=4737175) (a:=964) (b:=965) block4737175 block4738139))) (join_sums term (lo:=4739104) (a:=3857) (b:=3857) (join_sums term (lo:=4739104) (a:=1928) (b:=1929) (join_sums term (lo:=4739104) (a:=964) (b:=964) block4739104 block4740068) (join_sums term (lo:=4741032) (a:=964) (b:=965) block4741032 block4741996)) (join_sums term (lo:=4742961) (a:=1928) (b:=1929) (join_sums term (lo:=4742961) (a:=964) (b:=964) block4742961 block4743925) (join_sums term (lo:=4744889) (a:=964) (b:=965) block4744889 block4745853)))))))) (join_sums term (lo:=4746818) (a:=123409) (b:=123409) (join_sums term (lo:=4746818) (a:=61704) (b:=61705) (join_sums term (lo:=4746818) (a:=30852) (b:=30852) (join_sums term (lo:=4746818) (a:=15426) (b:=15426) (join_sums term (lo:=4746818) (a:=7713) (b:=7713) (join_sums term (lo:=4746818) (a:=3856) (b:=3857) (join_sums term (lo:=4746818) (a:=1928) (b:=1928) (join_sums term (lo:=4746818) (a:=964) (b:=964) block4746818 block4747782) (join_sums term (lo:=4748746) (a:=964) (b:=964) block4748746 block4749710)) (join_sums term (lo:=4750674) (a:=1928) (b:=1929) (join_sums term (lo:=4750674) (a:=964) (b:=964) block4750674 block4751638) (join_sums term (lo:=4752602) (a:=964) (b:=965) block4752602 block4753566))) (join_sums term (lo:=4754531) (a:=3856) (b:=3857) (join_sums term (lo:=4754531) (a:=1928) (b:=1928) (join_sums term (lo:=4754531) (a:=964) (b:=964) block4754531 block4755495) (join_sums term (lo:=4756459) (a:=964) (b:=964) block4756459 block4757423)) (join_sums term (lo:=4758387) (a:=1928) (b:=1929) (join_sums term (lo:=4758387) (a:=964) (b:=964) block4758387 block4759351) (join_sums term (lo:=4760315) (a:=964) (b:=965) block4760315 block4761279)))) (join_sums term (lo:=4762244) (a:=7713) (b:=7713) (join_sums term (lo:=4762244) (a:=3856) (b:=3857) (join_sums term (lo:=4762244) (a:=1928) (b:=1928) (join_sums term (lo:=4762244) (a:=964) (b:=964) block4762244 block4763208) (join_sums term (lo:=4764172) (a:=964) (b:=964) block4764172 block4765136)) (join_sums term (lo:=4766100) (a:=1928) (b:=1929) (join_sums term (lo:=4766100) (a:=964) (b:=964) block4766100 block4767064) (join_sums term (lo:=4768028) (a:=964) (b:=965) block4768028 block4768992))) (join_sums term (lo:=4769957) (a:=3856) (b:=3857) (join_sums term (lo:=4769957) (a:=1928) (b:=1928) (join_sums term (lo:=4769957) (a:=964) (b:=964) block4769957 block4770921) (join_sums term (lo:=4771885) (a:=964) (b:=964) block4771885 block4772849)) (join_sums term (lo:=4773813) (a:=1928) (b:=1929) (join_sums term (lo:=4773813) (a:=964) (b:=964) block4773813 block4774777) (join_sums term (lo:=4775741) (a:=964) (b:=965) block4775741 block4776705))))) (join_sums term (lo:=4777670) (a:=15426) (b:=15426) (join_sums term (lo:=4777670) (a:=7713) (b:=7713) (join_sums term (lo:=4777670) (a:=3856) (b:=3857) (join_sums term (lo:=4777670) (a:=1928) (b:=1928) (join_sums term (lo:=4777670) (a:=964) (b:=964) block4777670 block4778634) (join_sums term (lo:=4779598) (a:=964) (b:=964) block4779598 block4780562)) (join_sums term (lo:=4781526) (a:=1928) (b:=1929) (join_sums term (lo:=4781526) (a:=964) (b:=964) block4781526 block4782490) (join_sums term (lo:=4783454) (a:=964) (b:=965) block4783454 block4784418))) (join_sums term (lo:=4785383) (a:=3856) (b:=3857) (join_sums term (lo:=4785383) (a:=1928) (b:=1928) (join_sums term (lo:=4785383) (a:=964) (b:=964) block4785383 block4786347) (join_sums term (lo:=4787311) (a:=964) (b:=964) block4787311 block4788275)) (join_sums term (lo:=4789239) (a:=1928) (b:=1929) (join_sums term (lo:=4789239) (a:=964) (b:=964) block4789239 block4790203) (join_sums term (lo:=4791167) (a:=964) (b:=965) block4791167 block4792131)))) (join_sums term (lo:=4793096) (a:=7713) (b:=7713) (join_sums term (lo:=4793096) (a:=3856) (b:=3857) (join_sums term (lo:=4793096) (a:=1928) (b:=1928) (join_sums term (lo:=4793096) (a:=964) (b:=964) block4793096 block4794060) (join_sums term (lo:=4795024) (a:=964) (b:=964) block4795024 block4795988)) (join_sums term (lo:=4796952) (a:=1928) (b:=1929) (join_sums term (lo:=4796952) (a:=964) (b:=964) block4796952 block4797916) (join_sums term (lo:=4798880) (a:=964) (b:=965) block4798880 block4799844))) (join_sums term (lo:=4800809) (a:=3856) (b:=3857) (join_sums term (lo:=4800809) (a:=1928) (b:=1928) (join_sums term (lo:=4800809) (a:=964) (b:=964) block4800809 block4801773) (join_sums term (lo:=4802737) (a:=964) (b:=964) block4802737 block4803701)) (join_sums term (lo:=4804665) (a:=1928) (b:=1929) (join_sums term (lo:=4804665) (a:=964) (b:=964) block4804665 block4805629) (join_sums term (lo:=4806593) (a:=964) (b:=965) block4806593 block4807557)))))) (join_sums term (lo:=4808522) (a:=30852) (b:=30853) (join_sums term (lo:=4808522) (a:=15426) (b:=15426) (join_sums term (lo:=4808522) (a:=7713) (b:=7713) (join_sums term (lo:=4808522) (a:=3856) (b:=3857) (join_sums term (lo:=4808522) (a:=1928) (b:=1928) (join_sums term (lo:=4808522) (a:=964) (b:=964) block4808522 block4809486) (join_sums term (lo:=4810450) (a:=964) (b:=964) block4810450 block4811414)) (join_sums term (lo:=4812378) (a:=1928) (b:=1929) (join_sums term (lo:=4812378) (a:=964) (b:=964) block4812378 block4813342) (join_sums term (lo:=4814306) (a:=964) (b:=965) block4814306 block4815270))) (join_sums term (lo:=4816235) (a:=3856) (b:=3857) (join_sums term (lo:=4816235) (a:=1928) (b:=1928) (join_sums term (lo:=4816235) (a:=964) (b:=964) block4816235 block4817199) (join_sums term (lo:=4818163) (a:=964) (b:=964) block4818163 block4819127)) (join_sums term (lo:=4820091) (a:=1928) (b:=1929) (join_sums term (lo:=4820091) (a:=964) (b:=964) block4820091 block4821055) (join_sums term (lo:=4822019) (a:=964) (b:=965) block4822019 block4822983)))) (join_sums term (lo:=4823948) (a:=7713) (b:=7713) (join_sums term (lo:=4823948) (a:=3856) (b:=3857) (join_sums term (lo:=4823948) (a:=1928) (b:=1928) (join_sums term (lo:=4823948) (a:=964) (b:=964) block4823948 block4824912) (join_sums term (lo:=4825876) (a:=964) (b:=964) block4825876 block4826840)) (join_sums term (lo:=4827804) (a:=1928) (b:=1929) (join_sums term (lo:=4827804) (a:=964) (b:=964) block4827804 block4828768) (join_sums term (lo:=4829732) (a:=964) (b:=965) block4829732 block4830696))) (join_sums term (lo:=4831661) (a:=3856) (b:=3857) (join_sums term (lo:=4831661) (a:=1928) (b:=1928) (join_sums term (lo:=4831661) (a:=964) (b:=964) block4831661 block4832625) (join_sums term (lo:=4833589) (a:=964) (b:=964) block4833589 block4834553)) (join_sums term (lo:=4835517) (a:=1928) (b:=1929) (join_sums term (lo:=4835517) (a:=964) (b:=964) block4835517 block4836481) (join_sums term (lo:=4837445) (a:=964) (b:=965) block4837445 block4838409))))) (join_sums term (lo:=4839374) (a:=15426) (b:=15427) (join_sums term (lo:=4839374) (a:=7713) (b:=7713) (join_sums term (lo:=4839374) (a:=3856) (b:=3857) (join_sums term (lo:=4839374) (a:=1928) (b:=1928) (join_sums term (lo:=4839374) (a:=964) (b:=964) block4839374 block4840338) (join_sums term (lo:=4841302) (a:=964) (b:=964) block4841302 block4842266)) (join_sums term (lo:=4843230) (a:=1928) (b:=1929) (join_sums term (lo:=4843230) (a:=964) (b:=964) block4843230 block4844194) (join_sums term (lo:=4845158) (a:=964) (b:=965) block4845158 block4846122))) (join_sums term (lo:=4847087) (a:=3856) (b:=3857) (join_sums term (lo:=4847087) (a:=1928) (b:=1928) (join_sums term (lo:=4847087) (a:=964) (b:=964) block4847087 block4848051) (join_sums term (lo:=4849015) (a:=964) (b:=964) block4849015 block4849979)) (join_sums term (lo:=4850943) (a:=1928) (b:=1929) (join_sums term (lo:=4850943) (a:=964) (b:=964) block4850943 block4851907) (join_sums term (lo:=4852871) (a:=964) (b:=965) block4852871 block4853835)))) (join_sums term (lo:=4854800) (a:=7713) (b:=7714) (join_sums term (lo:=4854800) (a:=3856) (b:=3857) (join_sums term (lo:=4854800) (a:=1928) (b:=1928) (join_sums term (lo:=4854800) (a:=964) (b:=964) block4854800 block4855764) (join_sums term (lo:=4856728) (a:=964) (b:=964) block4856728 block4857692)) (join_sums term (lo:=4858656) (a:=1928) (b:=1929) (join_sums term (lo:=4858656) (a:=964) (b:=964) block4858656 block4859620) (join_sums term (lo:=4860584) (a:=964) (b:=965) block4860584 block4861548))) (join_sums term (lo:=4862513) (a:=3857) (b:=3857) (join_sums term (lo:=4862513) (a:=1928) (b:=1929) (join_sums term (lo:=4862513) (a:=964) (b:=964) block4862513 block4863477) (join_sums term (lo:=4864441) (a:=964) (b:=965) block4864441 block4865405)) (join_sums term (lo:=4866370) (a:=1928) (b:=1929) (join_sums term (lo:=4866370) (a:=964) (b:=964) block4866370 block4867334) (join_sums term (lo:=4868298) (a:=964) (b:=965) block4868298 block4869262))))))) (join_sums term (lo:=4870227) (a:=61704) (b:=61705) (join_sums term (lo:=4870227) (a:=30852) (b:=30852) (join_sums term (lo:=4870227) (a:=15426) (b:=15426) (join_sums term (lo:=4870227) (a:=7713) (b:=7713) (join_sums term (lo:=4870227) (a:=3856) (b:=3857) (join_sums term (lo:=4870227) (a:=1928) (b:=1928) (join_sums term (lo:=4870227) (a:=964) (b:=964) block4870227 block4871191) (join_sums term (lo:=4872155) (a:=964) (b:=964) block4872155 block4873119)) (join_sums term (lo:=4874083) (a:=1928) (b:=1929) (join_sums term (lo:=4874083) (a:=964) (b:=964) block4874083 block4875047) (join_sums term (lo:=4876011) (a:=964) (b:=965) block4876011 block4876975))) (join_sums term (lo:=4877940) (a:=3856) (b:=3857) (join_sums term (lo:=4877940) (a:=1928) (b:=1928) (join_sums term (lo:=4877940) (a:=964) (b:=964) block4877940 block4878904) (join_sums term (lo:=4879868) (a:=964) (b:=964) block4879868 block4880832)) (join_sums term (lo:=4881796) (a:=1928) (b:=1929) (join_sums term (lo:=4881796) (a:=964) (b:=964) block4881796 block4882760) (join_sums term (lo:=4883724) (a:=964) (b:=965) block4883724 block4884688)))) (join_sums term (lo:=4885653) (a:=7713) (b:=7713) (join_sums term (lo:=4885653) (a:=3856) (b:=3857) (join_sums term (lo:=4885653) (a:=1928) (b:=1928) (join_sums term (lo:=4885653) (a:=964) (b:=964) block4885653 block4886617) (join_sums term (lo:=4887581) (a:=964) (b:=964) block4887581 block4888545)) (join_sums term (lo:=4889509) (a:=1928) (b:=1929) (join_sums term (lo:=4889509) (a:=964) (b:=964) block4889509 block4890473) (join_sums term (lo:=4891437) (a:=964) (b:=965) block4891437 block4892401))) (join_sums term (lo:=4893366) (a:=3856) (b:=3857) (join_sums term (lo:=4893366) (a:=1928) (b:=1928) (join_sums term (lo:=4893366) (a:=964) (b:=964) block4893366 block4894330) (join_sums term (lo:=4895294) (a:=964) (b:=964) block4895294 block4896258)) (join_sums term (lo:=4897222) (a:=1928) (b:=1929) (join_sums term (lo:=4897222) (a:=964) (b:=964) block4897222 block4898186) (join_sums term (lo:=4899150) (a:=964) (b:=965) block4899150 block4900114))))) (join_sums term (lo:=4901079) (a:=15426) (b:=15426) (join_sums term (lo:=4901079) (a:=7713) (b:=7713) (join_sums term (lo:=4901079) (a:=3856) (b:=3857) (join_sums term (lo:=4901079) (a:=1928) (b:=1928) (join_sums term (lo:=4901079) (a:=964) (b:=964) block4901079 block4902043) (join_sums term (lo:=4903007) (a:=964) (b:=964) block4903007 block4903971)) (join_sums term (lo:=4904935) (a:=1928) (b:=1929) (join_sums term (lo:=4904935) (a:=964) (b:=964) block4904935 block4905899) (join_sums term (lo:=4906863) (a:=964) (b:=965) block4906863 block4907827))) (join_sums term (lo:=4908792) (a:=3856) (b:=3857) (join_sums term (lo:=4908792) (a:=1928) (b:=1928) (join_sums term (lo:=4908792) (a:=964) (b:=964) block4908792 block4909756) (join_sums term (lo:=4910720) (a:=964) (b:=964) block4910720 block4911684)) (join_sums term (lo:=4912648) (a:=1928) (b:=1929) (join_sums term (lo:=4912648) (a:=964) (b:=964) block4912648 block4913612) (join_sums term (lo:=4914576) (a:=964) (b:=965) block4914576 block4915540)))) (join_sums term (lo:=4916505) (a:=7713) (b:=7713) (join_sums term (lo:=4916505) (a:=3856) (b:=3857) (join_sums term (lo:=4916505) (a:=1928) (b:=1928) (join_sums term (lo:=4916505) (a:=964) (b:=964) block4916505 block4917469) (join_sums term (lo:=4918433) (a:=964) (b:=964) block4918433 block4919397)) (join_sums term (lo:=4920361) (a:=1928) (b:=1929) (join_sums term (lo:=4920361) (a:=964) (b:=964) block4920361 block4921325) (join_sums term (lo:=4922289) (a:=964) (b:=965) block4922289 block4923253))) (join_sums term (lo:=4924218) (a:=3856) (b:=3857) (join_sums term (lo:=4924218) (a:=1928) (b:=1928) (join_sums term (lo:=4924218) (a:=964) (b:=964) block4924218 block4925182) (join_sums term (lo:=4926146) (a:=964) (b:=964) block4926146 block4927110)) (join_sums term (lo:=4928074) (a:=1928) (b:=1929) (join_sums term (lo:=4928074) (a:=964) (b:=964) block4928074 block4929038) (join_sums term (lo:=4930002) (a:=964) (b:=965) block4930002 block4930966)))))) (join_sums term (lo:=4931931) (a:=30852) (b:=30853) (join_sums term (lo:=4931931) (a:=15426) (b:=15426) (join_sums term (lo:=4931931) (a:=7713) (b:=7713) (join_sums term (lo:=4931931) (a:=3856) (b:=3857) (join_sums term (lo:=4931931) (a:=1928) (b:=1928) (join_sums term (lo:=4931931) (a:=964) (b:=964) block4931931 block4932895) (join_sums term (lo:=4933859) (a:=964) (b:=964) block4933859 block4934823)) (join_sums term (lo:=4935787) (a:=1928) (b:=1929) (join_sums term (lo:=4935787) (a:=964) (b:=964) block4935787 block4936751) (join_sums term (lo:=4937715) (a:=964) (b:=965) block4937715 block4938679))) (join_sums term (lo:=4939644) (a:=3856) (b:=3857) (join_sums term (lo:=4939644) (a:=1928) (b:=1928) (join_sums term (lo:=4939644) (a:=964) (b:=964) block4939644 block4940608) (join_sums term (lo:=4941572) (a:=964) (b:=964) block4941572 block4942536)) (join_sums term (lo:=4943500) (a:=1928) (b:=1929) (join_sums term (lo:=4943500) (a:=964) (b:=964) block4943500 block4944464) (join_sums term (lo:=4945428) (a:=964) (b:=965) block4945428 block4946392)))) (join_sums term (lo:=4947357) (a:=7713) (b:=7713) (join_sums term (lo:=4947357) (a:=3856) (b:=3857) (join_sums term (lo:=4947357) (a:=1928) (b:=1928) (join_sums term (lo:=4947357) (a:=964) (b:=964) block4947357 block4948321) (join_sums term (lo:=4949285) (a:=964) (b:=964) block4949285 block4950249)) (join_sums term (lo:=4951213) (a:=1928) (b:=1929) (join_sums term (lo:=4951213) (a:=964) (b:=964) block4951213 block4952177) (join_sums term (lo:=4953141) (a:=964) (b:=965) block4953141 block4954105))) (join_sums term (lo:=4955070) (a:=3856) (b:=3857) (join_sums term (lo:=4955070) (a:=1928) (b:=1928) (join_sums term (lo:=4955070) (a:=964) (b:=964) block4955070 block4956034) (join_sums term (lo:=4956998) (a:=964) (b:=964) block4956998 block4957962)) (join_sums term (lo:=4958926) (a:=1928) (b:=1929) (join_sums term (lo:=4958926) (a:=964) (b:=964) block4958926 block4959890) (join_sums term (lo:=4960854) (a:=964) (b:=965) block4960854 block4961818))))) (join_sums term (lo:=4962783) (a:=15426) (b:=15427) (join_sums term (lo:=4962783) (a:=7713) (b:=7713) (join_sums term (lo:=4962783) (a:=3856) (b:=3857) (join_sums term (lo:=4962783) (a:=1928) (b:=1928) (join_sums term (lo:=4962783) (a:=964) (b:=964) block4962783 block4963747) (join_sums term (lo:=4964711) (a:=964) (b:=964) block4964711 block4965675)) (join_sums term (lo:=4966639) (a:=1928) (b:=1929) (join_sums term (lo:=4966639) (a:=964) (b:=964) block4966639 block4967603) (join_sums term (lo:=4968567) (a:=964) (b:=965) block4968567 block4969531))) (join_sums term (lo:=4970496) (a:=3856) (b:=3857) (join_sums term (lo:=4970496) (a:=1928) (b:=1928) (join_sums term (lo:=4970496) (a:=964) (b:=964) block4970496 block4971460) (join_sums term (lo:=4972424) (a:=964) (b:=964) block4972424 block4973388)) (join_sums term (lo:=4974352) (a:=1928) (b:=1929) (join_sums term (lo:=4974352) (a:=964) (b:=964) block4974352 block4975316) (join_sums term (lo:=4976280) (a:=964) (b:=965) block4976280 block4977244)))) (join_sums term (lo:=4978209) (a:=7713) (b:=7714) (join_sums term (lo:=4978209) (a:=3856) (b:=3857) (join_sums term (lo:=4978209) (a:=1928) (b:=1928) (join_sums term (lo:=4978209) (a:=964) (b:=964) block4978209 block4979173) (join_sums term (lo:=4980137) (a:=964) (b:=964) block4980137 block4981101)) (join_sums term (lo:=4982065) (a:=1928) (b:=1929) (join_sums term (lo:=4982065) (a:=964) (b:=964) block4982065 block4983029) (join_sums term (lo:=4983993) (a:=964) (b:=965) block4983993 block4984957))) (join_sums term (lo:=4985922) (a:=3857) (b:=3857) (join_sums term (lo:=4985922) (a:=1928) (b:=1929) (join_sums term (lo:=4985922) (a:=964) (b:=964) block4985922 block4986886) (join_sums term (lo:=4987850) (a:=964) (b:=965) block4987850 block4988814)) (join_sums term (lo:=4989779) (a:=1928) (b:=1929) (join_sums term (lo:=4989779) (a:=964) (b:=964) block4989779 block4990743) (join_sums term (lo:=4991707) (a:=964) (b:=965) block4991707 block4992671))))))))) (join_sums term (lo:=4993636) (a:=246817) (b:=246818) (join_sums term (lo:=4993636) (a:=123408) (b:=123409) (join_sums term (lo:=4993636) (a:=61704) (b:=61704) (join_sums term (lo:=4993636) (a:=30852) (b:=30852) (join_sums term (lo:=4993636) (a:=15426) (b:=15426) (join_sums term (lo:=4993636) (a:=7713) (b:=7713) (join_sums term (lo:=4993636) (a:=3856) (b:=3857) (join_sums term (lo:=4993636) (a:=1928) (b:=1928) (join_sums term (lo:=4993636) (a:=964) (b:=964) block4993636 block4994600) (join_sums term (lo:=4995564) (a:=964) (b:=964) block4995564 block4996528)) (join_sums term (lo:=4997492) (a:=1928) (b:=1929) (join_sums term (lo:=4997492) (a:=964) (b:=964) block4997492 block4998456) (join_sums term (lo:=4999420) (a:=964) (b:=965) block4999420 block5000384))) (join_sums term (lo:=5001349) (a:=3856) (b:=3857) (join_sums term (lo:=5001349) (a:=1928) (b:=1928) (join_sums term (lo:=5001349) (a:=964) (b:=964) block5001349 block5002313) (join_sums term (lo:=5003277) (a:=964) (b:=964) block5003277 block5004241)) (join_sums term (lo:=5005205) (a:=1928) (b:=1929) (join_sums term (lo:=5005205) (a:=964) (b:=964) block5005205 block5006169) (join_sums term (lo:=5007133) (a:=964) (b:=965) block5007133 block5008097)))) (join_sums term (lo:=5009062) (a:=7713) (b:=7713) (join_sums term (lo:=5009062) (a:=3856) (b:=3857) (join_sums term (lo:=5009062) (a:=1928) (b:=1928) (join_sums term (lo:=5009062) (a:=964) (b:=964) block5009062 block5010026) (join_sums term (lo:=5010990) (a:=964) (b:=964) block5010990 block5011954)) (join_sums term (lo:=5012918) (a:=1928) (b:=1929) (join_sums term (lo:=5012918) (a:=964) (b:=964) block5012918 block5013882) (join_sums term (lo:=5014846) (a:=964) (b:=965) block5014846 block5015810))) (join_sums term (lo:=5016775) (a:=3856) (b:=3857) (join_sums term (lo:=5016775) (a:=1928) (b:=1928) (join_sums term (lo:=5016775) (a:=964) (b:=964) block5016775 block5017739) (join_sums term (lo:=5018703) (a:=964) (b:=964) block5018703 block5019667)) (join_sums term (lo:=5020631) (a:=1928) (b:=1929) (join_sums term (lo:=5020631) (a:=964) (b:=964) block5020631 block5021595) (join_sums term (lo:=5022559) (a:=964) (b:=965) block5022559 block5023523))))) (join_sums term (lo:=5024488) (a:=15426) (b:=15426) (join_sums term (lo:=5024488) (a:=7713) (b:=7713) (join_sums term (lo:=5024488) (a:=3856) (b:=3857) (join_sums term (lo:=5024488) (a:=1928) (b:=1928) (join_sums term (lo:=5024488) (a:=964) (b:=964) block5024488 block5025452) (join_sums term (lo:=5026416) (a:=964) (b:=964) block5026416 block5027380)) (join_sums term (lo:=5028344) (a:=1928) (b:=1929) (join_sums term (lo:=5028344) (a:=964) (b:=964) block5028344 block5029308) (join_sums term (lo:=5030272) (a:=964) (b:=965) block5030272 block5031236))) (join_sums term (lo:=5032201) (a:=3856) (b:=3857) (join_sums term (lo:=5032201) (a:=1928) (b:=1928) (join_sums term (lo:=5032201) (a:=964) (b:=964) block5032201 block5033165) (join_sums term (lo:=5034129) (a:=964) (b:=964) block5034129 block5035093)) (join_sums term (lo:=5036057) (a:=1928) (b:=1929) (join_sums term (lo:=5036057) (a:=964) (b:=964) block5036057 block5037021) (join_sums term (lo:=5037985) (a:=964) (b:=965) block5037985 block5038949)))) (join_sums term (lo:=5039914) (a:=7713) (b:=7713) (join_sums term (lo:=5039914) (a:=3856) (b:=3857) (join_sums term (lo:=5039914) (a:=1928) (b:=1928) (join_sums term (lo:=5039914) (a:=964) (b:=964) block5039914 block5040878) (join_sums term (lo:=5041842) (a:=964) (b:=964) block5041842 block5042806)) (join_sums term (lo:=5043770) (a:=1928) (b:=1929) (join_sums term (lo:=5043770) (a:=964) (b:=964) block5043770 block5044734) (join_sums term (lo:=5045698) (a:=964) (b:=965) block5045698 block5046662))) (join_sums term (lo:=5047627) (a:=3856) (b:=3857) (join_sums term (lo:=5047627) (a:=1928) (b:=1928) (join_sums term (lo:=5047627) (a:=964) (b:=964) block5047627 block5048591) (join_sums term (lo:=5049555) (a:=964) (b:=964) block5049555 block5050519)) (join_sums term (lo:=5051483) (a:=1928) (b:=1929) (join_sums term (lo:=5051483) (a:=964) (b:=964) block5051483 block5052447) (join_sums term (lo:=5053411) (a:=964) (b:=965) block5053411 block5054375)))))) (join_sums term (lo:=5055340) (a:=30852) (b:=30852) (join_sums term (lo:=5055340) (a:=15426) (b:=15426) (join_sums term (lo:=5055340) (a:=7713) (b:=7713) (join_sums term (lo:=5055340) (a:=3856) (b:=3857) (join_sums term (lo:=5055340) (a:=1928) (b:=1928) (join_sums term (lo:=5055340) (a:=964) (b:=964) block5055340 block5056304) (join_sums term (lo:=5057268) (a:=964) (b:=964) block5057268 block5058232)) (join_sums term (lo:=5059196) (a:=1928) (b:=1929) (join_sums term (lo:=5059196) (a:=964) (b:=964) block5059196 block5060160) (join_sums term (lo:=5061124) (a:=964) (b:=965) block5061124 block5062088))) (join_sums term (lo:=5063053) (a:=3856) (b:=3857) (join_sums term (lo:=5063053) (a:=1928) (b:=1928) (join_sums term (lo:=5063053) (a:=964) (b:=964) block5063053 block5064017) (join_sums term (lo:=5064981) (a:=964) (b:=964) block5064981 block5065945)) (join_sums term (lo:=5066909) (a:=1928) (b:=1929) (join_sums term (lo:=5066909) (a:=964) (b:=964) block5066909 block5067873) (join_sums term (lo:=5068837) (a:=964) (b:=965) block5068837 block5069801)))) (join_sums term (lo:=5070766) (a:=7713) (b:=7713) (join_sums term (lo:=5070766) (a:=3856) (b:=3857) (join_sums term (lo:=5070766) (a:=1928) (b:=1928) (join_sums term (lo:=5070766) (a:=964) (b:=964) block5070766 block5071730) (join_sums term (lo:=5072694) (a:=964) (b:=964) block5072694 block5073658)) (join_sums term (lo:=5074622) (a:=1928) (b:=1929) (join_sums term (lo:=5074622) (a:=964) (b:=964) block5074622 block5075586) (join_sums term (lo:=5076550) (a:=964) (b:=965) block5076550 block5077514))) (join_sums term (lo:=5078479) (a:=3856) (b:=3857) (join_sums term (lo:=5078479) (a:=1928) (b:=1928) (join_sums term (lo:=5078479) (a:=964) (b:=964) block5078479 block5079443) (join_sums term (lo:=5080407) (a:=964) (b:=964) block5080407 block5081371)) (join_sums term (lo:=5082335) (a:=1928) (b:=1929) (join_sums term (lo:=5082335) (a:=964) (b:=964) block5082335 block5083299) (join_sums term (lo:=5084263) (a:=964) (b:=965) block5084263 block5085227))))) (join_sums term (lo:=5086192) (a:=15426) (b:=15426) (join_sums term (lo:=5086192) (a:=7713) (b:=7713) (join_sums term (lo:=5086192) (a:=3856) (b:=3857) (join_sums term (lo:=5086192) (a:=1928) (b:=1928) (join_sums term (lo:=5086192) (a:=964) (b:=964) block5086192 block5087156) (join_sums term (lo:=5088120) (a:=964) (b:=964) block5088120 block5089084)) (join_sums term (lo:=5090048) (a:=1928) (b:=1929) (join_sums term (lo:=5090048) (a:=964) (b:=964) block5090048 block5091012) (join_sums term (lo:=5091976) (a:=964) (b:=965) block5091976 block5092940))) (join_sums term (lo:=5093905) (a:=3856) (b:=3857) (join_sums term (lo:=5093905) (a:=1928) (b:=1928) (join_sums term (lo:=5093905) (a:=964) (b:=964) block5093905 block5094869) (join_sums term (lo:=5095833) (a:=964) (b:=964) block5095833 block5096797)) (join_sums term (lo:=5097761) (a:=1928) (b:=1929) (join_sums term (lo:=5097761) (a:=964) (b:=964) block5097761 block5098725) (join_sums term (lo:=5099689) (a:=964) (b:=965) block5099689 block5100653)))) (join_sums term (lo:=5101618) (a:=7713) (b:=7713) (join_sums term (lo:=5101618) (a:=3856) (b:=3857) (join_sums term (lo:=5101618) (a:=1928) (b:=1928) (join_sums term (lo:=5101618) (a:=964) (b:=964) block5101618 block5102582) (join_sums term (lo:=5103546) (a:=964) (b:=964) block5103546 block5104510)) (join_sums term (lo:=5105474) (a:=1928) (b:=1929) (join_sums term (lo:=5105474) (a:=964) (b:=964) block5105474 block5106438) (join_sums term (lo:=5107402) (a:=964) (b:=965) block5107402 block5108366))) (join_sums term (lo:=5109331) (a:=3856) (b:=3857) (join_sums term (lo:=5109331) (a:=1928) (b:=1928) (join_sums term (lo:=5109331) (a:=964) (b:=964) block5109331 block5110295) (join_sums term (lo:=5111259) (a:=964) (b:=964) block5111259 block5112223)) (join_sums term (lo:=5113187) (a:=1928) (b:=1929) (join_sums term (lo:=5113187) (a:=964) (b:=964) block5113187 block5114151) (join_sums term (lo:=5115115) (a:=964) (b:=965) block5115115 block5116079))))))) (join_sums term (lo:=5117044) (a:=61704) (b:=61705) (join_sums term (lo:=5117044) (a:=30852) (b:=30852) (join_sums term (lo:=5117044) (a:=15426) (b:=15426) (join_sums term (lo:=5117044) (a:=7713) (b:=7713) (join_sums term (lo:=5117044) (a:=3856) (b:=3857) (join_sums term (lo:=5117044) (a:=1928) (b:=1928) (join_sums term (lo:=5117044) (a:=964) (b:=964) block5117044 block5118008) (join_sums term (lo:=5118972) (a:=964) (b:=964) block5118972 block5119936)) (join_sums term (lo:=5120900) (a:=1928) (b:=1929) (join_sums term (lo:=5120900) (a:=964) (b:=964) block5120900 block5121864) (join_sums term (lo:=5122828) (a:=964) (b:=965) block5122828 block5123792))) (join_sums term (lo:=5124757) (a:=3856) (b:=3857) (join_sums term (lo:=5124757) (a:=1928) (b:=1928) (join_sums term (lo:=5124757) (a:=964) (b:=964) block5124757 block5125721) (join_sums term (lo:=5126685) (a:=964) (b:=964) block5126685 block5127649)) (join_sums term (lo:=5128613) (a:=1928) (b:=1929) (join_sums term (lo:=5128613) (a:=964) (b:=964) block5128613 block5129577) (join_sums term (lo:=5130541) (a:=964) (b:=965) block5130541 block5131505)))) (join_sums term (lo:=5132470) (a:=7713) (b:=7713) (join_sums term (lo:=5132470) (a:=3856) (b:=3857) (join_sums term (lo:=5132470) (a:=1928) (b:=1928) (join_sums term (lo:=5132470) (a:=964) (b:=964) block5132470 block5133434) (join_sums term (lo:=5134398) (a:=964) (b:=964) block5134398 block5135362)) (join_sums term (lo:=5136326) (a:=1928) (b:=1929) (join_sums term (lo:=5136326) (a:=964) (b:=964) block5136326 block5137290) (join_sums term (lo:=5138254) (a:=964) (b:=965) block5138254 block5139218))) (join_sums term (lo:=5140183) (a:=3856) (b:=3857) (join_sums term (lo:=5140183) (a:=1928) (b:=1928) (join_sums term (lo:=5140183) (a:=964) (b:=964) block5140183 block5141147) (join_sums term (lo:=5142111) (a:=964) (b:=964) block5142111 block5143075)) (join_sums term (lo:=5144039) (a:=1928) (b:=1929) (join_sums term (lo:=5144039) (a:=964) (b:=964) block5144039 block5145003) (join_sums term (lo:=5145967) (a:=964) (b:=965) block5145967 block5146931))))) (join_sums term (lo:=5147896) (a:=15426) (b:=15426) (join_sums term (lo:=5147896) (a:=7713) (b:=7713) (join_sums term (lo:=5147896) (a:=3856) (b:=3857) (join_sums term (lo:=5147896) (a:=1928) (b:=1928) (join_sums term (lo:=5147896) (a:=964) (b:=964) block5147896 block5148860) (join_sums term (lo:=5149824) (a:=964) (b:=964) block5149824 block5150788)) (join_sums term (lo:=5151752) (a:=1928) (b:=1929) (join_sums term (lo:=5151752) (a:=964) (b:=964) block5151752 block5152716) (join_sums term (lo:=5153680) (a:=964) (b:=965) block5153680 block5154644))) (join_sums term (lo:=5155609) (a:=3856) (b:=3857) (join_sums term (lo:=5155609) (a:=1928) (b:=1928) (join_sums term (lo:=5155609) (a:=964) (b:=964) block5155609 block5156573) (join_sums term (lo:=5157537) (a:=964) (b:=964) block5157537 block5158501)) (join_sums term (lo:=5159465) (a:=1928) (b:=1929) (join_sums term (lo:=5159465) (a:=964) (b:=964) block5159465 block5160429) (join_sums term (lo:=5161393) (a:=964) (b:=965) block5161393 block5162357)))) (join_sums term (lo:=5163322) (a:=7713) (b:=7713) (join_sums term (lo:=5163322) (a:=3856) (b:=3857) (join_sums term (lo:=5163322) (a:=1928) (b:=1928) (join_sums term (lo:=5163322) (a:=964) (b:=964) block5163322 block5164286) (join_sums term (lo:=5165250) (a:=964) (b:=964) block5165250 block5166214)) (join_sums term (lo:=5167178) (a:=1928) (b:=1929) (join_sums term (lo:=5167178) (a:=964) (b:=964) block5167178 block5168142) (join_sums term (lo:=5169106) (a:=964) (b:=965) block5169106 block5170070))) (join_sums term (lo:=5171035) (a:=3856) (b:=3857) (join_sums term (lo:=5171035) (a:=1928) (b:=1928) (join_sums term (lo:=5171035) (a:=964) (b:=964) block5171035 block5171999) (join_sums term (lo:=5172963) (a:=964) (b:=964) block5172963 block5173927)) (join_sums term (lo:=5174891) (a:=1928) (b:=1929) (join_sums term (lo:=5174891) (a:=964) (b:=964) block5174891 block5175855) (join_sums term (lo:=5176819) (a:=964) (b:=965) block5176819 block5177783)))))) (join_sums term (lo:=5178748) (a:=30852) (b:=30853) (join_sums term (lo:=5178748) (a:=15426) (b:=15426) (join_sums term (lo:=5178748) (a:=7713) (b:=7713) (join_sums term (lo:=5178748) (a:=3856) (b:=3857) (join_sums term (lo:=5178748) (a:=1928) (b:=1928) (join_sums term (lo:=5178748) (a:=964) (b:=964) block5178748 block5179712) (join_sums term (lo:=5180676) (a:=964) (b:=964) block5180676 block5181640)) (join_sums term (lo:=5182604) (a:=1928) (b:=1929) (join_sums term (lo:=5182604) (a:=964) (b:=964) block5182604 block5183568) (join_sums term (lo:=5184532) (a:=964) (b:=965) block5184532 block5185496))) (join_sums term (lo:=5186461) (a:=3856) (b:=3857) (join_sums term (lo:=5186461) (a:=1928) (b:=1928) (join_sums term (lo:=5186461) (a:=964) (b:=964) block5186461 block5187425) (join_sums term (lo:=5188389) (a:=964) (b:=964) block5188389 block5189353)) (join_sums term (lo:=5190317) (a:=1928) (b:=1929) (join_sums term (lo:=5190317) (a:=964) (b:=964) block5190317 block5191281) (join_sums term (lo:=5192245) (a:=964) (b:=965) block5192245 block5193209)))) (join_sums term (lo:=5194174) (a:=7713) (b:=7713) (join_sums term (lo:=5194174) (a:=3856) (b:=3857) (join_sums term (lo:=5194174) (a:=1928) (b:=1928) (join_sums term (lo:=5194174) (a:=964) (b:=964) block5194174 block5195138) (join_sums term (lo:=5196102) (a:=964) (b:=964) block5196102 block5197066)) (join_sums term (lo:=5198030) (a:=1928) (b:=1929) (join_sums term (lo:=5198030) (a:=964) (b:=964) block5198030 block5198994) (join_sums term (lo:=5199958) (a:=964) (b:=965) block5199958 block5200922))) (join_sums term (lo:=5201887) (a:=3856) (b:=3857) (join_sums term (lo:=5201887) (a:=1928) (b:=1928) (join_sums term (lo:=5201887) (a:=964) (b:=964) block5201887 block5202851) (join_sums term (lo:=5203815) (a:=964) (b:=964) block5203815 block5204779)) (join_sums term (lo:=5205743) (a:=1928) (b:=1929) (join_sums term (lo:=5205743) (a:=964) (b:=964) block5205743 block5206707) (join_sums term (lo:=5207671) (a:=964) (b:=965) block5207671 block5208635))))) (join_sums term (lo:=5209600) (a:=15426) (b:=15427) (join_sums term (lo:=5209600) (a:=7713) (b:=7713) (join_sums term (lo:=5209600) (a:=3856) (b:=3857) (join_sums term (lo:=5209600) (a:=1928) (b:=1928) (join_sums term (lo:=5209600) (a:=964) (b:=964) block5209600 block5210564) (join_sums term (lo:=5211528) (a:=964) (b:=964) block5211528 block5212492)) (join_sums term (lo:=5213456) (a:=1928) (b:=1929) (join_sums term (lo:=5213456) (a:=964) (b:=964) block5213456 block5214420) (join_sums term (lo:=5215384) (a:=964) (b:=965) block5215384 block5216348))) (join_sums term (lo:=5217313) (a:=3856) (b:=3857) (join_sums term (lo:=5217313) (a:=1928) (b:=1928) (join_sums term (lo:=5217313) (a:=964) (b:=964) block5217313 block5218277) (join_sums term (lo:=5219241) (a:=964) (b:=964) block5219241 block5220205)) (join_sums term (lo:=5221169) (a:=1928) (b:=1929) (join_sums term (lo:=5221169) (a:=964) (b:=964) block5221169 block5222133) (join_sums term (lo:=5223097) (a:=964) (b:=965) block5223097 block5224061)))) (join_sums term (lo:=5225026) (a:=7713) (b:=7714) (join_sums term (lo:=5225026) (a:=3856) (b:=3857) (join_sums term (lo:=5225026) (a:=1928) (b:=1928) (join_sums term (lo:=5225026) (a:=964) (b:=964) block5225026 block5225990) (join_sums term (lo:=5226954) (a:=964) (b:=964) block5226954 block5227918)) (join_sums term (lo:=5228882) (a:=1928) (b:=1929) (join_sums term (lo:=5228882) (a:=964) (b:=964) block5228882 block5229846) (join_sums term (lo:=5230810) (a:=964) (b:=965) block5230810 block5231774))) (join_sums term (lo:=5232739) (a:=3857) (b:=3857) (join_sums term (lo:=5232739) (a:=1928) (b:=1929) (join_sums term (lo:=5232739) (a:=964) (b:=964) block5232739 block5233703) (join_sums term (lo:=5234667) (a:=964) (b:=965) block5234667 block5235631)) (join_sums term (lo:=5236596) (a:=1928) (b:=1929) (join_sums term (lo:=5236596) (a:=964) (b:=964) block5236596 block5237560) (join_sums term (lo:=5238524) (a:=964) (b:=965) block5238524 block5239488)))))))) (join_sums term (lo:=5240453) (a:=123409) (b:=123409) (join_sums term (lo:=5240453) (a:=61704) (b:=61705) (join_sums term (lo:=5240453) (a:=30852) (b:=30852) (join_sums term (lo:=5240453) (a:=15426) (b:=15426) (join_sums term (lo:=5240453) (a:=7713) (b:=7713) (join_sums term (lo:=5240453) (a:=3856) (b:=3857) (join_sums term (lo:=5240453) (a:=1928) (b:=1928) (join_sums term (lo:=5240453) (a:=964) (b:=964) block5240453 block5241417) (join_sums term (lo:=5242381) (a:=964) (b:=964) block5242381 block5243345)) (join_sums term (lo:=5244309) (a:=1928) (b:=1929) (join_sums term (lo:=5244309) (a:=964) (b:=964) block5244309 block5245273) (join_sums term (lo:=5246237) (a:=964) (b:=965) block5246237 block5247201))) (join_sums term (lo:=5248166) (a:=3856) (b:=3857) (join_sums term (lo:=5248166) (a:=1928) (b:=1928) (join_sums term (lo:=5248166) (a:=964) (b:=964) block5248166 block5249130) (join_sums term (lo:=5250094) (a:=964) (b:=964) block5250094 block5251058)) (join_sums term (lo:=5252022) (a:=1928) (b:=1929) (join_sums term (lo:=5252022) (a:=964) (b:=964) block5252022 block5252986) (join_sums term (lo:=5253950) (a:=964) (b:=965) block5253950 block5254914)))) (join_sums term (lo:=5255879) (a:=7713) (b:=7713) (join_sums term (lo:=5255879) (a:=3856) (b:=3857) (join_sums term (lo:=5255879) (a:=1928) (b:=1928) (join_sums term (lo:=5255879) (a:=964) (b:=964) block5255879 block5256843) (join_sums term (lo:=5257807) (a:=964) (b:=964) block5257807 block5258771)) (join_sums term (lo:=5259735) (a:=1928) (b:=1929) (join_sums term (lo:=5259735) (a:=964) (b:=964) block5259735 block5260699) (join_sums term (lo:=5261663) (a:=964) (b:=965) block5261663 block5262627))) (join_sums term (lo:=5263592) (a:=3856) (b:=3857) (join_sums term (lo:=5263592) (a:=1928) (b:=1928) (join_sums term (lo:=5263592) (a:=964) (b:=964) block5263592 block5264556) (join_sums term (lo:=5265520) (a:=964) (b:=964) block5265520 block5266484)) (join_sums term (lo:=5267448) (a:=1928) (b:=1929) (join_sums term (lo:=5267448) (a:=964) (b:=964) block5267448 block5268412) (join_sums term (lo:=5269376) (a:=964) (b:=965) block5269376 block5270340))))) (join_sums term (lo:=5271305) (a:=15426) (b:=15426) (join_sums term (lo:=5271305) (a:=7713) (b:=7713) (join_sums term (lo:=5271305) (a:=3856) (b:=3857) (join_sums term (lo:=5271305) (a:=1928) (b:=1928) (join_sums term (lo:=5271305) (a:=964) (b:=964) block5271305 block5272269) (join_sums term (lo:=5273233) (a:=964) (b:=964) block5273233 block5274197)) (join_sums term (lo:=5275161) (a:=1928) (b:=1929) (join_sums term (lo:=5275161) (a:=964) (b:=964) block5275161 block5276125) (join_sums term (lo:=5277089) (a:=964) (b:=965) block5277089 block5278053))) (join_sums term (lo:=5279018) (a:=3856) (b:=3857) (join_sums term (lo:=5279018) (a:=1928) (b:=1928) (join_sums term (lo:=5279018) (a:=964) (b:=964) block5279018 block5279982) (join_sums term (lo:=5280946) (a:=964) (b:=964) block5280946 block5281910)) (join_sums term (lo:=5282874) (a:=1928) (b:=1929) (join_sums term (lo:=5282874) (a:=964) (b:=964) block5282874 block5283838) (join_sums term (lo:=5284802) (a:=964) (b:=965) block5284802 block5285766)))) (join_sums term (lo:=5286731) (a:=7713) (b:=7713) (join_sums term (lo:=5286731) (a:=3856) (b:=3857) (join_sums term (lo:=5286731) (a:=1928) (b:=1928) (join_sums term (lo:=5286731) (a:=964) (b:=964) block5286731 block5287695) (join_sums term (lo:=5288659) (a:=964) (b:=964) block5288659 block5289623)) (join_sums term (lo:=5290587) (a:=1928) (b:=1929) (join_sums term (lo:=5290587) (a:=964) (b:=964) block5290587 block5291551) (join_sums term (lo:=5292515) (a:=964) (b:=965) block5292515 block5293479))) (join_sums term (lo:=5294444) (a:=3856) (b:=3857) (join_sums term (lo:=5294444) (a:=1928) (b:=1928) (join_sums term (lo:=5294444) (a:=964) (b:=964) block5294444 block5295408) (join_sums term (lo:=5296372) (a:=964) (b:=964) block5296372 block5297336)) (join_sums term (lo:=5298300) (a:=1928) (b:=1929) (join_sums term (lo:=5298300) (a:=964) (b:=964) block5298300 block5299264) (join_sums term (lo:=5300228) (a:=964) (b:=965) block5300228 block5301192)))))) (join_sums term (lo:=5302157) (a:=30852) (b:=30853) (join_sums term (lo:=5302157) (a:=15426) (b:=15426) (join_sums term (lo:=5302157) (a:=7713) (b:=7713) (join_sums term (lo:=5302157) (a:=3856) (b:=3857) (join_sums term (lo:=5302157) (a:=1928) (b:=1928) (join_sums term (lo:=5302157) (a:=964) (b:=964) block5302157 block5303121) (join_sums term (lo:=5304085) (a:=964) (b:=964) block5304085 block5305049)) (join_sums term (lo:=5306013) (a:=1928) (b:=1929) (join_sums term (lo:=5306013) (a:=964) (b:=964) block5306013 block5306977) (join_sums term (lo:=5307941) (a:=964) (b:=965) block5307941 block5308905))) (join_sums term (lo:=5309870) (a:=3856) (b:=3857) (join_sums term (lo:=5309870) (a:=1928) (b:=1928) (join_sums term (lo:=5309870) (a:=964) (b:=964) block5309870 block5310834) (join_sums term (lo:=5311798) (a:=964) (b:=964) block5311798 block5312762)) (join_sums term (lo:=5313726) (a:=1928) (b:=1929) (join_sums term (lo:=5313726) (a:=964) (b:=964) block5313726 block5314690) (join_sums term (lo:=5315654) (a:=964) (b:=965) block5315654 block5316618)))) (join_sums term (lo:=5317583) (a:=7713) (b:=7713) (join_sums term (lo:=5317583) (a:=3856) (b:=3857) (join_sums term (lo:=5317583) (a:=1928) (b:=1928) (join_sums term (lo:=5317583) (a:=964) (b:=964) block5317583 block5318547) (join_sums term (lo:=5319511) (a:=964) (b:=964) block5319511 block5320475)) (join_sums term (lo:=5321439) (a:=1928) (b:=1929) (join_sums term (lo:=5321439) (a:=964) (b:=964) block5321439 block5322403) (join_sums term (lo:=5323367) (a:=964) (b:=965) block5323367 block5324331))) (join_sums term (lo:=5325296) (a:=3856) (b:=3857) (join_sums term (lo:=5325296) (a:=1928) (b:=1928) (join_sums term (lo:=5325296) (a:=964) (b:=964) block5325296 block5326260) (join_sums term (lo:=5327224) (a:=964) (b:=964) block5327224 block5328188)) (join_sums term (lo:=5329152) (a:=1928) (b:=1929) (join_sums term (lo:=5329152) (a:=964) (b:=964) block5329152 block5330116) (join_sums term (lo:=5331080) (a:=964) (b:=965) block5331080 block5332044))))) (join_sums term (lo:=5333009) (a:=15426) (b:=15427) (join_sums term (lo:=5333009) (a:=7713) (b:=7713) (join_sums term (lo:=5333009) (a:=3856) (b:=3857) (join_sums term (lo:=5333009) (a:=1928) (b:=1928) (join_sums term (lo:=5333009) (a:=964) (b:=964) block5333009 block5333973) (join_sums term (lo:=5334937) (a:=964) (b:=964) block5334937 block5335901)) (join_sums term (lo:=5336865) (a:=1928) (b:=1929) (join_sums term (lo:=5336865) (a:=964) (b:=964) block5336865 block5337829) (join_sums term (lo:=5338793) (a:=964) (b:=965) block5338793 block5339757))) (join_sums term (lo:=5340722) (a:=3856) (b:=3857) (join_sums term (lo:=5340722) (a:=1928) (b:=1928) (join_sums term (lo:=5340722) (a:=964) (b:=964) block5340722 block5341686) (join_sums term (lo:=5342650) (a:=964) (b:=964) block5342650 block5343614)) (join_sums term (lo:=5344578) (a:=1928) (b:=1929) (join_sums term (lo:=5344578) (a:=964) (b:=964) block5344578 block5345542) (join_sums term (lo:=5346506) (a:=964) (b:=965) block5346506 block5347470)))) (join_sums term (lo:=5348435) (a:=7713) (b:=7714) (join_sums term (lo:=5348435) (a:=3856) (b:=3857) (join_sums term (lo:=5348435) (a:=1928) (b:=1928) (join_sums term (lo:=5348435) (a:=964) (b:=964) block5348435 block5349399) (join_sums term (lo:=5350363) (a:=964) (b:=964) block5350363 block5351327)) (join_sums term (lo:=5352291) (a:=1928) (b:=1929) (join_sums term (lo:=5352291) (a:=964) (b:=964) block5352291 block5353255) (join_sums term (lo:=5354219) (a:=964) (b:=965) block5354219 block5355183))) (join_sums term (lo:=5356148) (a:=3857) (b:=3857) (join_sums term (lo:=5356148) (a:=1928) (b:=1929) (join_sums term (lo:=5356148) (a:=964) (b:=964) block5356148 block5357112) (join_sums term (lo:=5358076) (a:=964) (b:=965) block5358076 block5359040)) (join_sums term (lo:=5360005) (a:=1928) (b:=1929) (join_sums term (lo:=5360005) (a:=964) (b:=964) block5360005 block5360969) (join_sums term (lo:=5361933) (a:=964) (b:=965) block5361933 block5362897))))))) (join_sums term (lo:=5363862) (a:=61704) (b:=61705) (join_sums term (lo:=5363862) (a:=30852) (b:=30852) (join_sums term (lo:=5363862) (a:=15426) (b:=15426) (join_sums term (lo:=5363862) (a:=7713) (b:=7713) (join_sums term (lo:=5363862) (a:=3856) (b:=3857) (join_sums term (lo:=5363862) (a:=1928) (b:=1928) (join_sums term (lo:=5363862) (a:=964) (b:=964) block5363862 block5364826) (join_sums term (lo:=5365790) (a:=964) (b:=964) block5365790 block5366754)) (join_sums term (lo:=5367718) (a:=1928) (b:=1929) (join_sums term (lo:=5367718) (a:=964) (b:=964) block5367718 block5368682) (join_sums term (lo:=5369646) (a:=964) (b:=965) block5369646 block5370610))) (join_sums term (lo:=5371575) (a:=3856) (b:=3857) (join_sums term (lo:=5371575) (a:=1928) (b:=1928) (join_sums term (lo:=5371575) (a:=964) (b:=964) block5371575 block5372539) (join_sums term (lo:=5373503) (a:=964) (b:=964) block5373503 block5374467)) (join_sums term (lo:=5375431) (a:=1928) (b:=1929) (join_sums term (lo:=5375431) (a:=964) (b:=964) block5375431 block5376395) (join_sums term (lo:=5377359) (a:=964) (b:=965) block5377359 block5378323)))) (join_sums term (lo:=5379288) (a:=7713) (b:=7713) (join_sums term (lo:=5379288) (a:=3856) (b:=3857) (join_sums term (lo:=5379288) (a:=1928) (b:=1928) (join_sums term (lo:=5379288) (a:=964) (b:=964) block5379288 block5380252) (join_sums term (lo:=5381216) (a:=964) (b:=964) block5381216 block5382180)) (join_sums term (lo:=5383144) (a:=1928) (b:=1929) (join_sums term (lo:=5383144) (a:=964) (b:=964) block5383144 block5384108) (join_sums term (lo:=5385072) (a:=964) (b:=965) block5385072 block5386036))) (join_sums term (lo:=5387001) (a:=3856) (b:=3857) (join_sums term (lo:=5387001) (a:=1928) (b:=1928) (join_sums term (lo:=5387001) (a:=964) (b:=964) block5387001 block5387965) (join_sums term (lo:=5388929) (a:=964) (b:=964) block5388929 block5389893)) (join_sums term (lo:=5390857) (a:=1928) (b:=1929) (join_sums term (lo:=5390857) (a:=964) (b:=964) block5390857 block5391821) (join_sums term (lo:=5392785) (a:=964) (b:=965) block5392785 block5393749))))) (join_sums term (lo:=5394714) (a:=15426) (b:=15426) (join_sums term (lo:=5394714) (a:=7713) (b:=7713) (join_sums term (lo:=5394714) (a:=3856) (b:=3857) (join_sums term (lo:=5394714) (a:=1928) (b:=1928) (join_sums term (lo:=5394714) (a:=964) (b:=964) block5394714 block5395678) (join_sums term (lo:=5396642) (a:=964) (b:=964) block5396642 block5397606)) (join_sums term (lo:=5398570) (a:=1928) (b:=1929) (join_sums term (lo:=5398570) (a:=964) (b:=964) block5398570 block5399534) (join_sums term (lo:=5400498) (a:=964) (b:=965) block5400498 block5401462))) (join_sums term (lo:=5402427) (a:=3856) (b:=3857) (join_sums term (lo:=5402427) (a:=1928) (b:=1928) (join_sums term (lo:=5402427) (a:=964) (b:=964) block5402427 block5403391) (join_sums term (lo:=5404355) (a:=964) (b:=964) block5404355 block5405319)) (join_sums term (lo:=5406283) (a:=1928) (b:=1929) (join_sums term (lo:=5406283) (a:=964) (b:=964) block5406283 block5407247) (join_sums term (lo:=5408211) (a:=964) (b:=965) block5408211 block5409175)))) (join_sums term (lo:=5410140) (a:=7713) (b:=7713) (join_sums term (lo:=5410140) (a:=3856) (b:=3857) (join_sums term (lo:=5410140) (a:=1928) (b:=1928) (join_sums term (lo:=5410140) (a:=964) (b:=964) block5410140 block5411104) (join_sums term (lo:=5412068) (a:=964) (b:=964) block5412068 block5413032)) (join_sums term (lo:=5413996) (a:=1928) (b:=1929) (join_sums term (lo:=5413996) (a:=964) (b:=964) block5413996 block5414960) (join_sums term (lo:=5415924) (a:=964) (b:=965) block5415924 block5416888))) (join_sums term (lo:=5417853) (a:=3856) (b:=3857) (join_sums term (lo:=5417853) (a:=1928) (b:=1928) (join_sums term (lo:=5417853) (a:=964) (b:=964) block5417853 block5418817) (join_sums term (lo:=5419781) (a:=964) (b:=964) block5419781 block5420745)) (join_sums term (lo:=5421709) (a:=1928) (b:=1929) (join_sums term (lo:=5421709) (a:=964) (b:=964) block5421709 block5422673) (join_sums term (lo:=5423637) (a:=964) (b:=965) block5423637 block5424601)))))) (join_sums term (lo:=5425566) (a:=30852) (b:=30853) (join_sums term (lo:=5425566) (a:=15426) (b:=15426) (join_sums term (lo:=5425566) (a:=7713) (b:=7713) (join_sums term (lo:=5425566) (a:=3856) (b:=3857) (join_sums term (lo:=5425566) (a:=1928) (b:=1928) (join_sums term (lo:=5425566) (a:=964) (b:=964) block5425566 block5426530) (join_sums term (lo:=5427494) (a:=964) (b:=964) block5427494 block5428458)) (join_sums term (lo:=5429422) (a:=1928) (b:=1929) (join_sums term (lo:=5429422) (a:=964) (b:=964) block5429422 block5430386) (join_sums term (lo:=5431350) (a:=964) (b:=965) block5431350 block5432314))) (join_sums term (lo:=5433279) (a:=3856) (b:=3857) (join_sums term (lo:=5433279) (a:=1928) (b:=1928) (join_sums term (lo:=5433279) (a:=964) (b:=964) block5433279 block5434243) (join_sums term (lo:=5435207) (a:=964) (b:=964) block5435207 block5436171)) (join_sums term (lo:=5437135) (a:=1928) (b:=1929) (join_sums term (lo:=5437135) (a:=964) (b:=964) block5437135 block5438099) (join_sums term (lo:=5439063) (a:=964) (b:=965) block5439063 block5440027)))) (join_sums term (lo:=5440992) (a:=7713) (b:=7713) (join_sums term (lo:=5440992) (a:=3856) (b:=3857) (join_sums term (lo:=5440992) (a:=1928) (b:=1928) (join_sums term (lo:=5440992) (a:=964) (b:=964) block5440992 block5441956) (join_sums term (lo:=5442920) (a:=964) (b:=964) block5442920 block5443884)) (join_sums term (lo:=5444848) (a:=1928) (b:=1929) (join_sums term (lo:=5444848) (a:=964) (b:=964) block5444848 block5445812) (join_sums term (lo:=5446776) (a:=964) (b:=965) block5446776 block5447740))) (join_sums term (lo:=5448705) (a:=3856) (b:=3857) (join_sums term (lo:=5448705) (a:=1928) (b:=1928) (join_sums term (lo:=5448705) (a:=964) (b:=964) block5448705 block5449669) (join_sums term (lo:=5450633) (a:=964) (b:=964) block5450633 block5451597)) (join_sums term (lo:=5452561) (a:=1928) (b:=1929) (join_sums term (lo:=5452561) (a:=964) (b:=964) block5452561 block5453525) (join_sums term (lo:=5454489) (a:=964) (b:=965) block5454489 block5455453))))) (join_sums term (lo:=5456418) (a:=15426) (b:=15427) (join_sums term (lo:=5456418) (a:=7713) (b:=7713) (join_sums term (lo:=5456418) (a:=3856) (b:=3857) (join_sums term (lo:=5456418) (a:=1928) (b:=1928) (join_sums term (lo:=5456418) (a:=964) (b:=964) block5456418 block5457382) (join_sums term (lo:=5458346) (a:=964) (b:=964) block5458346 block5459310)) (join_sums term (lo:=5460274) (a:=1928) (b:=1929) (join_sums term (lo:=5460274) (a:=964) (b:=964) block5460274 block5461238) (join_sums term (lo:=5462202) (a:=964) (b:=965) block5462202 block5463166))) (join_sums term (lo:=5464131) (a:=3856) (b:=3857) (join_sums term (lo:=5464131) (a:=1928) (b:=1928) (join_sums term (lo:=5464131) (a:=964) (b:=964) block5464131 block5465095) (join_sums term (lo:=5466059) (a:=964) (b:=964) block5466059 block5467023)) (join_sums term (lo:=5467987) (a:=1928) (b:=1929) (join_sums term (lo:=5467987) (a:=964) (b:=964) block5467987 block5468951) (join_sums term (lo:=5469915) (a:=964) (b:=965) block5469915 block5470879)))) (join_sums term (lo:=5471844) (a:=7713) (b:=7714) (join_sums term (lo:=5471844) (a:=3856) (b:=3857) (join_sums term (lo:=5471844) (a:=1928) (b:=1928) (join_sums term (lo:=5471844) (a:=964) (b:=964) block5471844 block5472808) (join_sums term (lo:=5473772) (a:=964) (b:=964) block5473772 block5474736)) (join_sums term (lo:=5475700) (a:=1928) (b:=1929) (join_sums term (lo:=5475700) (a:=964) (b:=964) block5475700 block5476664) (join_sums term (lo:=5477628) (a:=964) (b:=965) block5477628 block5478592))) (join_sums term (lo:=5479557) (a:=3857) (b:=3857) (join_sums term (lo:=5479557) (a:=1928) (b:=1929) (join_sums term (lo:=5479557) (a:=964) (b:=964) block5479557 block5480521) (join_sums term (lo:=5481485) (a:=964) (b:=965) block5481485 block5482449)) (join_sums term (lo:=5483414) (a:=1928) (b:=1929) (join_sums term (lo:=5483414) (a:=964) (b:=964) block5483414 block5484378) (join_sums term (lo:=5485342) (a:=964) (b:=965) block5485342 block5486306))))))))))

private theorem rows : blockSum term 0 5487271 4359356685 :=
  join_sums term (lo:=0) (a:=4500001) (b:=987270) before after_cut

theorem exact_upper_sum :
    (∑ p ∈ (Nat.primesLE 5487270).filter (4500000 < ·),
      (Nat.primeCounting (30110134441897/p) - Nat.primeCounting (p-1))) = 4359356685 :=
  right_from_blocks tab prime CheckpointA28006Slim.fast_correct prime_ok (by decide) (by decide) rows

end CorrectionHigh30
