import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ94085731To120000000

def index (n : ℕ) : ℕ := 8*(n/30) + ((703383147439395582067753010374709520 : ℕ) >>> (4*(n%30)))%16

def number (i : ℕ) : ℕ := 30*(i/8) + ((1021784272097 : ℕ) >>> (5*(i%8)))%32

theorem shift_index (q r : ℕ) : index (30*q+r) = 8*q+index r := by
  unfold index
  rw [Nat.mul_add_div (by decide : 0<30),Nat.mul_add_mod]
  omega

theorem shift_number (q j : ℕ) : number (8*q+j) = 30*q+number j := by
  unfold number
  rw [Nat.mul_add_div (by decide : 0<8),Nat.mul_add_mod]
  omega

theorem wheel_step (n : ℕ) :
    (index (n+1) = index n ∧ (2 ∣ n+1 ∨ 3 ∣ n+1 ∨ 5 ∣ n+1)) ∨
    (index (n+1) = index n+1 ∧ number (index n) = n+1) := by
  have tab : ∀ r : Fin 30,
      (index (r.1+1) = index r.1 ∧ (2 ∣ r.1+1 ∨ 3 ∣ r.1+1 ∨ 5 ∣ r.1+1)) ∨
      (index (r.1+1) = index r.1+1 ∧ number (index r.1) = r.1+1) := by decide +kernel
  let q := n/30
  let r := n%30
  have split : n = 30*q+r := (Nat.div_add_mod n 30).symm
  have next : n+1 = 30*q+(r+1) := by omega
  rcases tab ⟨r,Nat.mod_lt _ (by decide)⟩ with ⟨eq,hd⟩ | ⟨eq,hn⟩
  · left
    constructor
    · rw [next,split,shift_index,shift_index,eq]
    · rw [next]
      rcases hd with h|h|h
      · exact Or.inl (dvd_add (dvd_mul_of_dvd_left (by decide : 2 ∣ 30) q) h)
      · exact Or.inr (Or.inl (dvd_add (dvd_mul_of_dvd_left (by decide : 3 ∣ 30) q) h))
      · exact Or.inr (Or.inr (dvd_add (dvd_mul_of_dvd_left (by decide : 5 ∣ 30) q) h))
  · change index (r+1) = index r+1 at eq
    change number (index r) = r+1 at hn
    right
    constructor
    · rw [next,split,shift_index,shift_index,eq]
      omega
    · rw [next,split,shift_index,shift_number,hn]

theorem skips_composite {n : ℕ} (large : 5 < n) (d : 2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n) : ¬ n.Prime := by
  intro h
  rcases d with hd|hd|hd
  all_goals rcases (Nat.dvd_prime h).mp hd with e|e <;> omega

theorem index_bound {n b : ℕ} (h : n ≤ b) : index n < 8*(b/30+2) := by
  have t : ∀ r : Fin 30, ((703383147439395582067753010374709520 : ℕ) >>> (4*r.val))%16 ≤ 8 := by decide +kernel
  have a := t ⟨n%30,Nat.mod_lt _ (by decide)⟩
  change ((703383147439395582067753010374709520 : ℕ) >>> (4*(n%30)))%16 ≤ 8 at a
  have d : n/30 ≤ b/30 := Nat.div_le_div_right h
  unfold index
  omega




private def radical : ℕ := 0x2fae32a5f1a962e1eb478fc550c8dc9fa8124a2c10a4286541eec3203fc8d4fe2f72f0f27f87d21142acb1ca01819f745783a11dc83c468f8027ca06478f601c3127924e3d3d8e04d6520bdf8a097484e68c056a2f6e296ba29ccd61641349951c6401aaff1f55ecc4bdf6f11b92f4b0752c8fec718788df2e8c5616e6d0df88a7e4eefe6b1b6e05c5284d0926049ad37c950a1b53d6d1fdbe74289e28393626eb690ec9b2854b525684e90c7423b65950a15d71e6c35194ee5b25343690602beeb6cd57a9ab99e08fe03b368a9a7431acdbb0b67165bbacf0171c8713e2b8ccdfa4caa4f16b8d78320064983b0502014ee0b56b6e3344d57329e8364a793ff4202882814e46681ad152d091c99e69eb4b927f4e684c5fcae23782846f13e20f2f6614aa5672e63a89a649f90b2bc29817fb3a83331c363a3b6a2c325d7b92c284c4d029a1639ee85a90ad5f189fb126f4d2ef49d3a7fd74c1108f025a8810ad3437de8e7f0bfb395d39b21dee2c96ed1148d56625b9708bcbe1b12e669305c20766b4e21a2bf5a2edd24f5babc465a5873cc09818df5a2d2bf1aa65bb70bd20285995f61988424e93fe1b306247c2e9539b30929fe6c31b1b9525ceac91fb7065665adac86c6ce22c06bec4bcad67b11d3f80101a0a33023dfa2c0237184976dd594aca5d3c2cdf38fa47f7854b922d0f068d48c470534894751e78325c2aeaf275ac175f271f593407cea85d5da7bcda731a2faff64ee27b23e7c188c914edfbc189ed18f41c869be078f3514cc93b554433dc4b3f6834019f0ea6591359437b24f17d0388b923cebbdc77306a3380d82e76c1ee4b1b7ee5c92ac49497cbce0fe544952baa72a853b86badbaf7e357fc6f383ece63dc5903750f6cfbd7a5bdc98dd9b66962d65e6d7dc1b2efda1ac561d56c18b3bb2085b1394e7bd4923865d767798b9dd4f7f651a442ec53887a3c114233757e91c83a03f4fd6b8b47f4ad9cd132710d9b19bc3c32d077c473d002a4c906077e2a8e269a3904bc840420c08a11abe14b5e80e0d95141e518bdac63ce58f2f485751ee39ffc7697294357ad936bd6edac0e6a973a3a7031f40d55d4508074830312c9cb6358777a3237c3b35d376fc0ea78a6f256525886c1edc8f54af39c6b889ddadd3c3f4b665f0f72de943a1a648885988ab514173d5c1101a96ad432fbb05913f22c38f8110177744b9480149ca3cfe2850940bf15bd19298cb32fb2ed6d1c6133a3860586cce7c13a0f8f1900880e02d597907ebfabfb9ffdbe811bcef5d37ec3da38ae866f12c5d0e9f4060bb9420a4bf0a15e884e3afc1bfe71ca87a52f840dbe393bbeebd16d8730452d9b6c5908f42d2603a60dbcf7b44835c8a71bd6d6482c3bd6a607a5aa67de8d0d52c1b082abbc875c4908c8aa5ea5de4a830dc4108266a48d2bef1bd2b4ca2588bde5972e5f6cd10a571dfb4365df0b7430a7d2588884ae1bb3743bfe349c872363c4c99ad2b514020c353d0455b58c5d73473b4c692ca4451303ece3c2e0e2624dbb665ebcfd2a519fca6b371a2a5baa2a87ad07b0a8cc6e53678461877e21b266536ac6eef6a6613d61c3c7b33296e6f76425909461d196302872d1f0024bfc17506004d4cf48d44995266bdf0dd6034878904d5e9290f678a7ca27f0b9fa0f09974a627d9fc1cc8227fe6fe9c5dc729e361975f4b58a8d730a218f578a0f511fb45047a77c3e7c6b10987fc61a88991053ae43107734eaba2df21378f9f550a6d5f730412270272a41cd381e4c0700600340918630c12354af5233242f3217649aa1d5f9abf6f2070d276a1a1f37b3c96c12baf8ccad15f47d6ad2225c43a9f6a9816dee304c83c70dbcbba1692f64e2949ac2b09e14c8307a4844cd95551b04a8b0746899ce622e1d8929d617320bb39038806479d62a5822b144f4df8beaa5d2b809668b459668df7c0e8a4f4618eca95f1179b0cafc29b78ad11428e0cf18f1fc3597f24e70e1d558a05763aef9413d79c43a3eaf216bc76bba4c6ade4f2a98bbced147075e75d69ed0c0356d976d72c116b4f5e2f368e9921f95e41f89421f40a2f7eda6cdcb518725176ff9c53e78f74c87730281d4b19c898e605009593ee53e524324dbb3a1362014f6c0d3cd3dbc019492f6389dcde1c2d5fd45497819f987d1afc7942e957ff65b4631056e3ab050d9b434d62ce8c05ea0cddc65933148f851cfbc06cf631ec7ae0e5a965770132380971cae375f28765afa5320b115788bd6c24e18c4a517aea010092a00332d4ffed25ee2f0f27100fb4c46a06a70fecda86a7e54d1f250d62b2d25147b44e6c184d61f36a73730b450d0f8649c7f187d5e16db09f8bc20ae7082ecc01a62b243ac648da538b5ca2e42014bec1275881d4af7ecbfa74a824fad1c00692a703187b893a97704baa0280260d4de38f0c5a160dd496dff30cc5d18b075db559f6fb6c5007158aab094e8151547215efcaef23be355fe878330d1d65cec56f14637f29dfa26175813d4a06b5d6c69ff63e71a8cfd66f7a34995f11b4c0b216b9b81444bca3fceafab6f18688616c3dee24c299974b7a0cc5d4ca1a8418f2f7c9696ba59db9c00bfd3739f2825bb2d1dac6c2c17d0c255dd094916feda4e804e5f70310f8593cc8c565a54cc0c0614897c815003b511f5303cd82e29075c9cff2ac508ffac48ad3543beaae8865d534552ca5c22edd20351d5b413b268b7a2b4fe234c2ec1e35035611dc965e6e

private def light (n : ℕ) : Bool :=
  if n≤104 then decide n.Prime else n.gcd 10299016745145627623848583864765044283053772454999072182325491776887871732475287174542709871683888003235965704141638377695179741979175588724736000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤10954) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 104 = 10299016745145627623848583864765044283053772454999072182325491776887871732475287174542709871683888003235965704141638377695179741979175588724736000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 104 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤10954 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 42 := by unfold smallValid; decide +kernel

private theorem sp42 : smallValid 42 43 := by unfold smallValid; decide +kernel

private theorem sp85 : smallValid 85 43 := by unfold smallValid; decide +kernel

private theorem sp128 : smallValid 128 43 := by unfold smallValid; decide +kernel

private theorem sp171 : smallValid 171 42 := by unfold smallValid; decide +kernel

private theorem sp213 : smallValid 213 43 := by unfold smallValid; decide +kernel

private theorem sp256 : smallValid 256 43 := by unfold smallValid; decide +kernel

private theorem sp299 : smallValid 299 43 := by unfold smallValid; decide +kernel

private theorem sp342 : smallValid 342 42 := by unfold smallValid; decide +kernel

private theorem sp384 : smallValid 384 43 := by unfold smallValid; decide +kernel

private theorem sp427 : smallValid 427 43 := by unfold smallValid; decide +kernel

private theorem sp470 : smallValid 470 43 := by unfold smallValid; decide +kernel

private theorem sp513 : smallValid 513 42 := by unfold smallValid; decide +kernel

private theorem sp555 : smallValid 555 43 := by unfold smallValid; decide +kernel

private theorem sp598 : smallValid 598 43 := by unfold smallValid; decide +kernel

private theorem sp641 : smallValid 641 43 := by unfold smallValid; decide +kernel

private theorem sp684 : smallValid 684 42 := by unfold smallValid; decide +kernel

private theorem sp726 : smallValid 726 43 := by unfold smallValid; decide +kernel

private theorem sp769 : smallValid 769 43 := by unfold smallValid; decide +kernel

private theorem sp812 : smallValid 812 43 := by unfold smallValid; decide +kernel

private theorem sp855 : smallValid 855 42 := by unfold smallValid; decide +kernel

private theorem sp897 : smallValid 897 43 := by unfold smallValid; decide +kernel

private theorem sp940 : smallValid 940 43 := by unfold smallValid; decide +kernel

private theorem sp983 : smallValid 983 43 := by unfold smallValid; decide +kernel

private theorem sp1026 : smallValid 1026 42 := by unfold smallValid; decide +kernel

private theorem sp1068 : smallValid 1068 43 := by unfold smallValid; decide +kernel

private theorem sp1111 : smallValid 1111 43 := by unfold smallValid; decide +kernel

private theorem sp1154 : smallValid 1154 43 := by unfold smallValid; decide +kernel

private theorem sp1197 : smallValid 1197 43 := by unfold smallValid; decide +kernel

private theorem sp1240 : smallValid 1240 43 := by unfold smallValid; decide +kernel

private theorem sp1283 : smallValid 1283 43 := by unfold smallValid; decide +kernel

private theorem sp1326 : smallValid 1326 43 := by unfold smallValid; decide +kernel

private theorem sp1369 : smallValid 1369 42 := by unfold smallValid; decide +kernel

private theorem sp1411 : smallValid 1411 43 := by unfold smallValid; decide +kernel

private theorem sp1454 : smallValid 1454 43 := by unfold smallValid; decide +kernel

private theorem sp1497 : smallValid 1497 43 := by unfold smallValid; decide +kernel

private theorem sp1540 : smallValid 1540 42 := by unfold smallValid; decide +kernel

private theorem sp1582 : smallValid 1582 43 := by unfold smallValid; decide +kernel

private theorem sp1625 : smallValid 1625 43 := by unfold smallValid; decide +kernel

private theorem sp1668 : smallValid 1668 43 := by unfold smallValid; decide +kernel

private theorem sp1711 : smallValid 1711 42 := by unfold smallValid; decide +kernel

private theorem sp1753 : smallValid 1753 43 := by unfold smallValid; decide +kernel

private theorem sp1796 : smallValid 1796 43 := by unfold smallValid; decide +kernel

private theorem sp1839 : smallValid 1839 43 := by unfold smallValid; decide +kernel

private theorem sp1882 : smallValid 1882 42 := by unfold smallValid; decide +kernel

private theorem sp1924 : smallValid 1924 43 := by unfold smallValid; decide +kernel

private theorem sp1967 : smallValid 1967 43 := by unfold smallValid; decide +kernel

private theorem sp2010 : smallValid 2010 43 := by unfold smallValid; decide +kernel

private theorem sp2053 : smallValid 2053 42 := by unfold smallValid; decide +kernel

private theorem sp2095 : smallValid 2095 43 := by unfold smallValid; decide +kernel

private theorem sp2138 : smallValid 2138 43 := by unfold smallValid; decide +kernel

private theorem sp2181 : smallValid 2181 43 := by unfold smallValid; decide +kernel

private theorem sp2224 : smallValid 2224 42 := by unfold smallValid; decide +kernel

private theorem sp2266 : smallValid 2266 43 := by unfold smallValid; decide +kernel

private theorem sp2309 : smallValid 2309 43 := by unfold smallValid; decide +kernel

private theorem sp2352 : smallValid 2352 43 := by unfold smallValid; decide +kernel

private theorem sp2395 : smallValid 2395 42 := by unfold smallValid; decide +kernel

private theorem sp2437 : smallValid 2437 43 := by unfold smallValid; decide +kernel

private theorem sp2480 : smallValid 2480 43 := by unfold smallValid; decide +kernel

private theorem sp2523 : smallValid 2523 43 := by unfold smallValid; decide +kernel

private theorem sp2566 : smallValid 2566 43 := by unfold smallValid; decide +kernel

private theorem sp2609 : smallValid 2609 43 := by unfold smallValid; decide +kernel

private theorem sp2652 : smallValid 2652 43 := by unfold smallValid; decide +kernel

private theorem sp2695 : smallValid 2695 43 := by unfold smallValid; decide +kernel

private theorem sp2738 : smallValid 2738 42 := by unfold smallValid; decide +kernel

private theorem sp2780 : smallValid 2780 43 := by unfold smallValid; decide +kernel

private theorem sp2823 : smallValid 2823 43 := by unfold smallValid; decide +kernel

private theorem sp2866 : smallValid 2866 43 := by unfold smallValid; decide +kernel

private theorem sp2909 : smallValid 2909 42 := by unfold smallValid; decide +kernel

private theorem sp2951 : smallValid 2951 43 := by unfold smallValid; decide +kernel

private theorem sp2994 : smallValid 2994 43 := by unfold smallValid; decide +kernel

private theorem sp3037 : smallValid 3037 43 := by unfold smallValid; decide +kernel

private theorem sp3080 : smallValid 3080 42 := by unfold smallValid; decide +kernel

private theorem sp3122 : smallValid 3122 43 := by unfold smallValid; decide +kernel

private theorem sp3165 : smallValid 3165 43 := by unfold smallValid; decide +kernel

private theorem sp3208 : smallValid 3208 43 := by unfold smallValid; decide +kernel

private theorem sp3251 : smallValid 3251 42 := by unfold smallValid; decide +kernel

private theorem sp3293 : smallValid 3293 43 := by unfold smallValid; decide +kernel

private theorem sp3336 : smallValid 3336 43 := by unfold smallValid; decide +kernel

private theorem sp3379 : smallValid 3379 43 := by unfold smallValid; decide +kernel

private theorem sp3422 : smallValid 3422 42 := by unfold smallValid; decide +kernel

private theorem sp3464 : smallValid 3464 43 := by unfold smallValid; decide +kernel

private theorem sp3507 : smallValid 3507 43 := by unfold smallValid; decide +kernel

private theorem sp3550 : smallValid 3550 43 := by unfold smallValid; decide +kernel

private theorem sp3593 : smallValid 3593 42 := by unfold smallValid; decide +kernel

private theorem sp3635 : smallValid 3635 43 := by unfold smallValid; decide +kernel

private theorem sp3678 : smallValid 3678 43 := by unfold smallValid; decide +kernel

private theorem sp3721 : smallValid 3721 43 := by unfold smallValid; decide +kernel

private theorem sp3764 : smallValid 3764 42 := by unfold smallValid; decide +kernel

private theorem sp3806 : smallValid 3806 43 := by unfold smallValid; decide +kernel

private theorem sp3849 : smallValid 3849 43 := by unfold smallValid; decide +kernel

private theorem sp3892 : smallValid 3892 43 := by unfold smallValid; decide +kernel

private theorem sp3935 : smallValid 3935 43 := by unfold smallValid; decide +kernel

private theorem sp3978 : smallValid 3978 43 := by unfold smallValid; decide +kernel

private theorem sp4021 : smallValid 4021 43 := by unfold smallValid; decide +kernel

private theorem sp4064 : smallValid 4064 43 := by unfold smallValid; decide +kernel

private theorem sp4107 : smallValid 4107 42 := by unfold smallValid; decide +kernel

private theorem sp4149 : smallValid 4149 43 := by unfold smallValid; decide +kernel

private theorem sp4192 : smallValid 4192 43 := by unfold smallValid; decide +kernel

private theorem sp4235 : smallValid 4235 43 := by unfold smallValid; decide +kernel

private theorem sp4278 : smallValid 4278 42 := by unfold smallValid; decide +kernel

private theorem sp4320 : smallValid 4320 43 := by unfold smallValid; decide +kernel

private theorem sp4363 : smallValid 4363 43 := by unfold smallValid; decide +kernel

private theorem sp4406 : smallValid 4406 43 := by unfold smallValid; decide +kernel

private theorem sp4449 : smallValid 4449 42 := by unfold smallValid; decide +kernel

private theorem sp4491 : smallValid 4491 43 := by unfold smallValid; decide +kernel

private theorem sp4534 : smallValid 4534 43 := by unfold smallValid; decide +kernel

private theorem sp4577 : smallValid 4577 43 := by unfold smallValid; decide +kernel

private theorem sp4620 : smallValid 4620 43 := by unfold smallValid; decide +kernel

private theorem sp4663 : smallValid 4663 43 := by unfold smallValid; decide +kernel

private theorem sp4706 : smallValid 4706 43 := by unfold smallValid; decide +kernel

private theorem sp4749 : smallValid 4749 43 := by unfold smallValid; decide +kernel

private theorem sp4792 : smallValid 4792 42 := by unfold smallValid; decide +kernel

private theorem sp4834 : smallValid 4834 43 := by unfold smallValid; decide +kernel

private theorem sp4877 : smallValid 4877 43 := by unfold smallValid; decide +kernel

private theorem sp4920 : smallValid 4920 43 := by unfold smallValid; decide +kernel

private theorem sp4963 : smallValid 4963 42 := by unfold smallValid; decide +kernel

private theorem sp5005 : smallValid 5005 43 := by unfold smallValid; decide +kernel

private theorem sp5048 : smallValid 5048 43 := by unfold smallValid; decide +kernel

private theorem sp5091 : smallValid 5091 43 := by unfold smallValid; decide +kernel

private theorem sp5134 : smallValid 5134 42 := by unfold smallValid; decide +kernel

private theorem sp5176 : smallValid 5176 43 := by unfold smallValid; decide +kernel

private theorem sp5219 : smallValid 5219 43 := by unfold smallValid; decide +kernel

private theorem sp5262 : smallValid 5262 43 := by unfold smallValid; decide +kernel

private theorem sp5305 : smallValid 5305 43 := by unfold smallValid; decide +kernel

private theorem sp5348 : smallValid 5348 43 := by unfold smallValid; decide +kernel

private theorem sp5391 : smallValid 5391 43 := by unfold smallValid; decide +kernel

private theorem sp5434 : smallValid 5434 43 := by unfold smallValid; decide +kernel

private theorem sp5477 : smallValid 5477 42 := by unfold smallValid; decide +kernel

private theorem sp5519 : smallValid 5519 43 := by unfold smallValid; decide +kernel

private theorem sp5562 : smallValid 5562 43 := by unfold smallValid; decide +kernel

private theorem sp5605 : smallValid 5605 43 := by unfold smallValid; decide +kernel

private theorem sp5648 : smallValid 5648 42 := by unfold smallValid; decide +kernel

private theorem sp5690 : smallValid 5690 43 := by unfold smallValid; decide +kernel

private theorem sp5733 : smallValid 5733 43 := by unfold smallValid; decide +kernel

private theorem sp5776 : smallValid 5776 43 := by unfold smallValid; decide +kernel

private theorem sp5819 : smallValid 5819 42 := by unfold smallValid; decide +kernel

private theorem sp5861 : smallValid 5861 43 := by unfold smallValid; decide +kernel

private theorem sp5904 : smallValid 5904 43 := by unfold smallValid; decide +kernel

private theorem sp5947 : smallValid 5947 43 := by unfold smallValid; decide +kernel

private theorem sp5990 : smallValid 5990 42 := by unfold smallValid; decide +kernel

private theorem sp6032 : smallValid 6032 43 := by unfold smallValid; decide +kernel

private theorem sp6075 : smallValid 6075 43 := by unfold smallValid; decide +kernel

private theorem sp6118 : smallValid 6118 43 := by unfold smallValid; decide +kernel

private theorem sp6161 : smallValid 6161 42 := by unfold smallValid; decide +kernel

private theorem sp6203 : smallValid 6203 43 := by unfold smallValid; decide +kernel

private theorem sp6246 : smallValid 6246 43 := by unfold smallValid; decide +kernel

private theorem sp6289 : smallValid 6289 43 := by unfold smallValid; decide +kernel

private theorem sp6332 : smallValid 6332 42 := by unfold smallValid; decide +kernel

private theorem sp6374 : smallValid 6374 43 := by unfold smallValid; decide +kernel

private theorem sp6417 : smallValid 6417 43 := by unfold smallValid; decide +kernel

private theorem sp6460 : smallValid 6460 43 := by unfold smallValid; decide +kernel

private theorem sp6503 : smallValid 6503 42 := by unfold smallValid; decide +kernel

private theorem sp6545 : smallValid 6545 43 := by unfold smallValid; decide +kernel

private theorem sp6588 : smallValid 6588 43 := by unfold smallValid; decide +kernel

private theorem sp6631 : smallValid 6631 43 := by unfold smallValid; decide +kernel

private theorem sp6674 : smallValid 6674 43 := by unfold smallValid; decide +kernel

private theorem sp6717 : smallValid 6717 43 := by unfold smallValid; decide +kernel

private theorem sp6760 : smallValid 6760 43 := by unfold smallValid; decide +kernel

private theorem sp6803 : smallValid 6803 43 := by unfold smallValid; decide +kernel

private theorem sp6846 : smallValid 6846 42 := by unfold smallValid; decide +kernel

private theorem sp6888 : smallValid 6888 43 := by unfold smallValid; decide +kernel

private theorem sp6931 : smallValid 6931 43 := by unfold smallValid; decide +kernel

private theorem sp6974 : smallValid 6974 43 := by unfold smallValid; decide +kernel

private theorem sp7017 : smallValid 7017 42 := by unfold smallValid; decide +kernel

private theorem sp7059 : smallValid 7059 43 := by unfold smallValid; decide +kernel

private theorem sp7102 : smallValid 7102 43 := by unfold smallValid; decide +kernel

private theorem sp7145 : smallValid 7145 43 := by unfold smallValid; decide +kernel

private theorem sp7188 : smallValid 7188 42 := by unfold smallValid; decide +kernel

private theorem sp7230 : smallValid 7230 43 := by unfold smallValid; decide +kernel

private theorem sp7273 : smallValid 7273 43 := by unfold smallValid; decide +kernel

private theorem sp7316 : smallValid 7316 43 := by unfold smallValid; decide +kernel

private theorem sp7359 : smallValid 7359 43 := by unfold smallValid; decide +kernel

private theorem sp7402 : smallValid 7402 43 := by unfold smallValid; decide +kernel

private theorem sp7445 : smallValid 7445 43 := by unfold smallValid; decide +kernel

private theorem sp7488 : smallValid 7488 43 := by unfold smallValid; decide +kernel

private theorem sp7531 : smallValid 7531 42 := by unfold smallValid; decide +kernel

private theorem sp7573 : smallValid 7573 43 := by unfold smallValid; decide +kernel

private theorem sp7616 : smallValid 7616 43 := by unfold smallValid; decide +kernel

private theorem sp7659 : smallValid 7659 43 := by unfold smallValid; decide +kernel

private theorem sp7702 : smallValid 7702 42 := by unfold smallValid; decide +kernel

private theorem sp7744 : smallValid 7744 43 := by unfold smallValid; decide +kernel

private theorem sp7787 : smallValid 7787 43 := by unfold smallValid; decide +kernel

private theorem sp7830 : smallValid 7830 43 := by unfold smallValid; decide +kernel

private theorem sp7873 : smallValid 7873 42 := by unfold smallValid; decide +kernel

private theorem sp7915 : smallValid 7915 43 := by unfold smallValid; decide +kernel

private theorem sp7958 : smallValid 7958 43 := by unfold smallValid; decide +kernel

private theorem sp8001 : smallValid 8001 43 := by unfold smallValid; decide +kernel

private theorem sp8044 : smallValid 8044 43 := by unfold smallValid; decide +kernel

private theorem sp8087 : smallValid 8087 43 := by unfold smallValid; decide +kernel

private theorem sp8130 : smallValid 8130 43 := by unfold smallValid; decide +kernel

private theorem sp8173 : smallValid 8173 43 := by unfold smallValid; decide +kernel

private theorem sp8216 : smallValid 8216 42 := by unfold smallValid; decide +kernel

private theorem sp8258 : smallValid 8258 43 := by unfold smallValid; decide +kernel

private theorem sp8301 : smallValid 8301 43 := by unfold smallValid; decide +kernel

private theorem sp8344 : smallValid 8344 43 := by unfold smallValid; decide +kernel

private theorem sp8387 : smallValid 8387 42 := by unfold smallValid; decide +kernel

private theorem sp8429 : smallValid 8429 43 := by unfold smallValid; decide +kernel

private theorem sp8472 : smallValid 8472 43 := by unfold smallValid; decide +kernel

private theorem sp8515 : smallValid 8515 43 := by unfold smallValid; decide +kernel

private theorem sp8558 : smallValid 8558 42 := by unfold smallValid; decide +kernel

private theorem sp8600 : smallValid 8600 43 := by unfold smallValid; decide +kernel

private theorem sp8643 : smallValid 8643 43 := by unfold smallValid; decide +kernel

private theorem sp8686 : smallValid 8686 43 := by unfold smallValid; decide +kernel

private theorem sp8729 : smallValid 8729 42 := by unfold smallValid; decide +kernel

private theorem sp8771 : smallValid 8771 43 := by unfold smallValid; decide +kernel

private theorem sp8814 : smallValid 8814 43 := by unfold smallValid; decide +kernel

private theorem sp8857 : smallValid 8857 43 := by unfold smallValid; decide +kernel

private theorem sp8900 : smallValid 8900 42 := by unfold smallValid; decide +kernel

private theorem sp8942 : smallValid 8942 43 := by unfold smallValid; decide +kernel

private theorem sp8985 : smallValid 8985 43 := by unfold smallValid; decide +kernel

private theorem sp9028 : smallValid 9028 43 := by unfold smallValid; decide +kernel

private theorem sp9071 : smallValid 9071 42 := by unfold smallValid; decide +kernel

private theorem sp9113 : smallValid 9113 43 := by unfold smallValid; decide +kernel

private theorem sp9156 : smallValid 9156 43 := by unfold smallValid; decide +kernel

private theorem sp9199 : smallValid 9199 43 := by unfold smallValid; decide +kernel

private theorem sp9242 : smallValid 9242 42 := by unfold smallValid; decide +kernel

private theorem sp9284 : smallValid 9284 43 := by unfold smallValid; decide +kernel

private theorem sp9327 : smallValid 9327 43 := by unfold smallValid; decide +kernel

private theorem sp9370 : smallValid 9370 43 := by unfold smallValid; decide +kernel

private theorem sp9413 : smallValid 9413 43 := by unfold smallValid; decide +kernel

private theorem sp9456 : smallValid 9456 43 := by unfold smallValid; decide +kernel

private theorem sp9499 : smallValid 9499 43 := by unfold smallValid; decide +kernel

private theorem sp9542 : smallValid 9542 43 := by unfold smallValid; decide +kernel

private theorem sp9585 : smallValid 9585 42 := by unfold smallValid; decide +kernel

private theorem sp9627 : smallValid 9627 43 := by unfold smallValid; decide +kernel

private theorem sp9670 : smallValid 9670 43 := by unfold smallValid; decide +kernel

private theorem sp9713 : smallValid 9713 43 := by unfold smallValid; decide +kernel

private theorem sp9756 : smallValid 9756 42 := by unfold smallValid; decide +kernel

private theorem sp9798 : smallValid 9798 43 := by unfold smallValid; decide +kernel

private theorem sp9841 : smallValid 9841 43 := by unfold smallValid; decide +kernel

private theorem sp9884 : smallValid 9884 43 := by unfold smallValid; decide +kernel

private theorem sp9927 : smallValid 9927 42 := by unfold smallValid; decide +kernel

private theorem sp9969 : smallValid 9969 43 := by unfold smallValid; decide +kernel

private theorem sp10012 : smallValid 10012 43 := by unfold smallValid; decide +kernel

private theorem sp10055 : smallValid 10055 43 := by unfold smallValid; decide +kernel

private theorem sp10098 : smallValid 10098 43 := by unfold smallValid; decide +kernel

private theorem sp10141 : smallValid 10141 43 := by unfold smallValid; decide +kernel

private theorem sp10184 : smallValid 10184 43 := by unfold smallValid; decide +kernel

private theorem sp10227 : smallValid 10227 43 := by unfold smallValid; decide +kernel

private theorem sp10270 : smallValid 10270 42 := by unfold smallValid; decide +kernel

private theorem sp10312 : smallValid 10312 43 := by unfold smallValid; decide +kernel

private theorem sp10355 : smallValid 10355 43 := by unfold smallValid; decide +kernel

private theorem sp10398 : smallValid 10398 43 := by unfold smallValid; decide +kernel

private theorem sp10441 : smallValid 10441 42 := by unfold smallValid; decide +kernel

private theorem sp10483 : smallValid 10483 43 := by unfold smallValid; decide +kernel

private theorem sp10526 : smallValid 10526 43 := by unfold smallValid; decide +kernel

private theorem sp10569 : smallValid 10569 43 := by unfold smallValid; decide +kernel

private theorem sp10612 : smallValid 10612 42 := by unfold smallValid; decide +kernel

private theorem sp10654 : smallValid 10654 43 := by unfold smallValid; decide +kernel

private theorem sp10697 : smallValid 10697 43 := by unfold smallValid; decide +kernel

private theorem sp10740 : smallValid 10740 43 := by unfold smallValid; decide +kernel

private theorem sp10783 : smallValid 10783 43 := by unfold smallValid; decide +kernel

private theorem sp10826 : smallValid 10826 43 := by unfold smallValid; decide +kernel

private theorem sp10869 : smallValid 10869 43 := by unfold smallValid; decide +kernel

private theorem sp10912 : smallValid 10912 43 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤10954) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 10955 := (joinSmall (lo:=0) (a:=5477) (b:=5478) (joinSmall (lo:=0) (a:=2738) (b:=2739) (joinSmall (lo:=0) (a:=1369) (b:=1369) (joinSmall (lo:=0) (a:=684) (b:=685) (joinSmall (lo:=0) (a:=342) (b:=342) (joinSmall (lo:=0) (a:=171) (b:=171) (joinSmall (lo:=0) (a:=85) (b:=86) (joinSmall (lo:=0) (a:=42) (b:=43) sp0 sp42) (joinSmall (lo:=85) (a:=43) (b:=43) sp85 sp128)) (joinSmall (lo:=171) (a:=85) (b:=86) (joinSmall (lo:=171) (a:=42) (b:=43) sp171 sp213) (joinSmall (lo:=256) (a:=43) (b:=43) sp256 sp299))) (joinSmall (lo:=342) (a:=171) (b:=171) (joinSmall (lo:=342) (a:=85) (b:=86) (joinSmall (lo:=342) (a:=42) (b:=43) sp342 sp384) (joinSmall (lo:=427) (a:=43) (b:=43) sp427 sp470)) (joinSmall (lo:=513) (a:=85) (b:=86) (joinSmall (lo:=513) (a:=42) (b:=43) sp513 sp555) (joinSmall (lo:=598) (a:=43) (b:=43) sp598 sp641)))) (joinSmall (lo:=684) (a:=342) (b:=343) (joinSmall (lo:=684) (a:=171) (b:=171) (joinSmall (lo:=684) (a:=85) (b:=86) (joinSmall (lo:=684) (a:=42) (b:=43) sp684 sp726) (joinSmall (lo:=769) (a:=43) (b:=43) sp769 sp812)) (joinSmall (lo:=855) (a:=85) (b:=86) (joinSmall (lo:=855) (a:=42) (b:=43) sp855 sp897) (joinSmall (lo:=940) (a:=43) (b:=43) sp940 sp983))) (joinSmall (lo:=1026) (a:=171) (b:=172) (joinSmall (lo:=1026) (a:=85) (b:=86) (joinSmall (lo:=1026) (a:=42) (b:=43) sp1026 sp1068) (joinSmall (lo:=1111) (a:=43) (b:=43) sp1111 sp1154)) (joinSmall (lo:=1197) (a:=86) (b:=86) (joinSmall (lo:=1197) (a:=43) (b:=43) sp1197 sp1240) (joinSmall (lo:=1283) (a:=43) (b:=43) sp1283 sp1326))))) (joinSmall (lo:=1369) (a:=684) (b:=685) (joinSmall (lo:=1369) (a:=342) (b:=342) (joinSmall (lo:=1369) (a:=171) (b:=171) (joinSmall (lo:=1369) (a:=85) (b:=86) (joinSmall (lo:=1369) (a:=42) (b:=43) sp1369 sp1411) (joinSmall (lo:=1454) (a:=43) (b:=43) sp1454 sp1497)) (joinSmall (lo:=1540) (a:=85) (b:=86) (joinSmall (lo:=1540) (a:=42) (b:=43) sp1540 sp1582) (joinSmall (lo:=1625) (a:=43) (b:=43) sp1625 sp1668))) (joinSmall (lo:=1711) (a:=171) (b:=171) (joinSmall (lo:=1711) (a:=85) (b:=86) (joinSmall (lo:=1711) (a:=42) (b:=43) sp1711 sp1753) (joinSmall (lo:=1796) (a:=43) (b:=43) sp1796 sp1839)) (joinSmall (lo:=1882) (a:=85) (b:=86) (joinSmall (lo:=1882) (a:=42) (b:=43) sp1882 sp1924) (joinSmall (lo:=1967) (a:=43) (b:=43) sp1967 sp2010)))) (joinSmall (lo:=2053) (a:=342) (b:=343) (joinSmall (lo:=2053) (a:=171) (b:=171) (joinSmall (lo:=2053) (a:=85) (b:=86) (joinSmall (lo:=2053) (a:=42) (b:=43) sp2053 sp2095) (joinSmall (lo:=2138) (a:=43) (b:=43) sp2138 sp2181)) (joinSmall (lo:=2224) (a:=85) (b:=86) (joinSmall (lo:=2224) (a:=42) (b:=43) sp2224 sp2266) (joinSmall (lo:=2309) (a:=43) (b:=43) sp2309 sp2352))) (joinSmall (lo:=2395) (a:=171) (b:=172) (joinSmall (lo:=2395) (a:=85) (b:=86) (joinSmall (lo:=2395) (a:=42) (b:=43) sp2395 sp2437) (joinSmall (lo:=2480) (a:=43) (b:=43) sp2480 sp2523)) (joinSmall (lo:=2566) (a:=86) (b:=86) (joinSmall (lo:=2566) (a:=43) (b:=43) sp2566 sp2609) (joinSmall (lo:=2652) (a:=43) (b:=43) sp2652 sp2695)))))) (joinSmall (lo:=2738) (a:=1369) (b:=1370) (joinSmall (lo:=2738) (a:=684) (b:=685) (joinSmall (lo:=2738) (a:=342) (b:=342) (joinSmall (lo:=2738) (a:=171) (b:=171) (joinSmall (lo:=2738) (a:=85) (b:=86) (joinSmall (lo:=2738) (a:=42) (b:=43) sp2738 sp2780) (joinSmall (lo:=2823) (a:=43) (b:=43) sp2823 sp2866)) (joinSmall (lo:=2909) (a:=85) (b:=86) (joinSmall (lo:=2909) (a:=42) (b:=43) sp2909 sp2951) (joinSmall (lo:=2994) (a:=43) (b:=43) sp2994 sp3037))) (joinSmall (lo:=3080) (a:=171) (b:=171) (joinSmall (lo:=3080) (a:=85) (b:=86) (joinSmall (lo:=3080) (a:=42) (b:=43) sp3080 sp3122) (joinSmall (lo:=3165) (a:=43) (b:=43) sp3165 sp3208)) (joinSmall (lo:=3251) (a:=85) (b:=86) (joinSmall (lo:=3251) (a:=42) (b:=43) sp3251 sp3293) (joinSmall (lo:=3336) (a:=43) (b:=43) sp3336 sp3379)))) (joinSmall (lo:=3422) (a:=342) (b:=343) (joinSmall (lo:=3422) (a:=171) (b:=171) (joinSmall (lo:=3422) (a:=85) (b:=86) (joinSmall (lo:=3422) (a:=42) (b:=43) sp3422 sp3464) (joinSmall (lo:=3507) (a:=43) (b:=43) sp3507 sp3550)) (joinSmall (lo:=3593) (a:=85) (b:=86) (joinSmall (lo:=3593) (a:=42) (b:=43) sp3593 sp3635) (joinSmall (lo:=3678) (a:=43) (b:=43) sp3678 sp3721))) (joinSmall (lo:=3764) (a:=171) (b:=172) (joinSmall (lo:=3764) (a:=85) (b:=86) (joinSmall (lo:=3764) (a:=42) (b:=43) sp3764 sp3806) (joinSmall (lo:=3849) (a:=43) (b:=43) sp3849 sp3892)) (joinSmall (lo:=3935) (a:=86) (b:=86) (joinSmall (lo:=3935) (a:=43) (b:=43) sp3935 sp3978) (joinSmall (lo:=4021) (a:=43) (b:=43) sp4021 sp4064))))) (joinSmall (lo:=4107) (a:=685) (b:=685) (joinSmall (lo:=4107) (a:=342) (b:=343) (joinSmall (lo:=4107) (a:=171) (b:=171) (joinSmall (lo:=4107) (a:=85) (b:=86) (joinSmall (lo:=4107) (a:=42) (b:=43) sp4107 sp4149) (joinSmall (lo:=4192) (a:=43) (b:=43) sp4192 sp4235)) (joinSmall (lo:=4278) (a:=85) (b:=86) (joinSmall (lo:=4278) (a:=42) (b:=43) sp4278 sp4320) (joinSmall (lo:=4363) (a:=43) (b:=43) sp4363 sp4406))) (joinSmall (lo:=4449) (a:=171) (b:=172) (joinSmall (lo:=4449) (a:=85) (b:=86) (joinSmall (lo:=4449) (a:=42) (b:=43) sp4449 sp4491) (joinSmall (lo:=4534) (a:=43) (b:=43) sp4534 sp4577)) (joinSmall (lo:=4620) (a:=86) (b:=86) (joinSmall (lo:=4620) (a:=43) (b:=43) sp4620 sp4663) (joinSmall (lo:=4706) (a:=43) (b:=43) sp4706 sp4749)))) (joinSmall (lo:=4792) (a:=342) (b:=343) (joinSmall (lo:=4792) (a:=171) (b:=171) (joinSmall (lo:=4792) (a:=85) (b:=86) (joinSmall (lo:=4792) (a:=42) (b:=43) sp4792 sp4834) (joinSmall (lo:=4877) (a:=43) (b:=43) sp4877 sp4920)) (joinSmall (lo:=4963) (a:=85) (b:=86) (joinSmall (lo:=4963) (a:=42) (b:=43) sp4963 sp5005) (joinSmall (lo:=5048) (a:=43) (b:=43) sp5048 sp5091))) (joinSmall (lo:=5134) (a:=171) (b:=172) (joinSmall (lo:=5134) (a:=85) (b:=86) (joinSmall (lo:=5134) (a:=42) (b:=43) sp5134 sp5176) (joinSmall (lo:=5219) (a:=43) (b:=43) sp5219 sp5262)) (joinSmall (lo:=5305) (a:=86) (b:=86) (joinSmall (lo:=5305) (a:=43) (b:=43) sp5305 sp5348) (joinSmall (lo:=5391) (a:=43) (b:=43) sp5391 sp5434))))))) (joinSmall (lo:=5477) (a:=2739) (b:=2739) (joinSmall (lo:=5477) (a:=1369) (b:=1370) (joinSmall (lo:=5477) (a:=684) (b:=685) (joinSmall (lo:=5477) (a:=342) (b:=342) (joinSmall (lo:=5477) (a:=171) (b:=171) (joinSmall (lo:=5477) (a:=85) (b:=86) (joinSmall (lo:=5477) (a:=42) (b:=43) sp5477 sp5519) (joinSmall (lo:=5562) (a:=43) (b:=43) sp5562 sp5605)) (joinSmall (lo:=5648) (a:=85) (b:=86) (joinSmall (lo:=5648) (a:=42) (b:=43) sp5648 sp5690) (joinSmall (lo:=5733) (a:=43) (b:=43) sp5733 sp5776))) (joinSmall (lo:=5819) (a:=171) (b:=171) (joinSmall (lo:=5819) (a:=85) (b:=86) (joinSmall (lo:=5819) (a:=42) (b:=43) sp5819 sp5861) (joinSmall (lo:=5904) (a:=43) (b:=43) sp5904 sp5947)) (joinSmall (lo:=5990) (a:=85) (b:=86) (joinSmall (lo:=5990) (a:=42) (b:=43) sp5990 sp6032) (joinSmall (lo:=6075) (a:=43) (b:=43) sp6075 sp6118)))) (joinSmall (lo:=6161) (a:=342) (b:=343) (joinSmall (lo:=6161) (a:=171) (b:=171) (joinSmall (lo:=6161) (a:=85) (b:=86) (joinSmall (lo:=6161) (a:=42) (b:=43) sp6161 sp6203) (joinSmall (lo:=6246) (a:=43) (b:=43) sp6246 sp6289)) (joinSmall (lo:=6332) (a:=85) (b:=86) (joinSmall (lo:=6332) (a:=42) (b:=43) sp6332 sp6374) (joinSmall (lo:=6417) (a:=43) (b:=43) sp6417 sp6460))) (joinSmall (lo:=6503) (a:=171) (b:=172) (joinSmall (lo:=6503) (a:=85) (b:=86) (joinSmall (lo:=6503) (a:=42) (b:=43) sp6503 sp6545) (joinSmall (lo:=6588) (a:=43) (b:=43) sp6588 sp6631)) (joinSmall (lo:=6674) (a:=86) (b:=86) (joinSmall (lo:=6674) (a:=43) (b:=43) sp6674 sp6717) (joinSmall (lo:=6760) (a:=43) (b:=43) sp6760 sp6803))))) (joinSmall (lo:=6846) (a:=685) (b:=685) (joinSmall (lo:=6846) (a:=342) (b:=343) (joinSmall (lo:=6846) (a:=171) (b:=171) (joinSmall (lo:=6846) (a:=85) (b:=86) (joinSmall (lo:=6846) (a:=42) (b:=43) sp6846 sp6888) (joinSmall (lo:=6931) (a:=43) (b:=43) sp6931 sp6974)) (joinSmall (lo:=7017) (a:=85) (b:=86) (joinSmall (lo:=7017) (a:=42) (b:=43) sp7017 sp7059) (joinSmall (lo:=7102) (a:=43) (b:=43) sp7102 sp7145))) (joinSmall (lo:=7188) (a:=171) (b:=172) (joinSmall (lo:=7188) (a:=85) (b:=86) (joinSmall (lo:=7188) (a:=42) (b:=43) sp7188 sp7230) (joinSmall (lo:=7273) (a:=43) (b:=43) sp7273 sp7316)) (joinSmall (lo:=7359) (a:=86) (b:=86) (joinSmall (lo:=7359) (a:=43) (b:=43) sp7359 sp7402) (joinSmall (lo:=7445) (a:=43) (b:=43) sp7445 sp7488)))) (joinSmall (lo:=7531) (a:=342) (b:=343) (joinSmall (lo:=7531) (a:=171) (b:=171) (joinSmall (lo:=7531) (a:=85) (b:=86) (joinSmall (lo:=7531) (a:=42) (b:=43) sp7531 sp7573) (joinSmall (lo:=7616) (a:=43) (b:=43) sp7616 sp7659)) (joinSmall (lo:=7702) (a:=85) (b:=86) (joinSmall (lo:=7702) (a:=42) (b:=43) sp7702 sp7744) (joinSmall (lo:=7787) (a:=43) (b:=43) sp7787 sp7830))) (joinSmall (lo:=7873) (a:=171) (b:=172) (joinSmall (lo:=7873) (a:=85) (b:=86) (joinSmall (lo:=7873) (a:=42) (b:=43) sp7873 sp7915) (joinSmall (lo:=7958) (a:=43) (b:=43) sp7958 sp8001)) (joinSmall (lo:=8044) (a:=86) (b:=86) (joinSmall (lo:=8044) (a:=43) (b:=43) sp8044 sp8087) (joinSmall (lo:=8130) (a:=43) (b:=43) sp8130 sp8173)))))) (joinSmall (lo:=8216) (a:=1369) (b:=1370) (joinSmall (lo:=8216) (a:=684) (b:=685) (joinSmall (lo:=8216) (a:=342) (b:=342) (joinSmall (lo:=8216) (a:=171) (b:=171) (joinSmall (lo:=8216) (a:=85) (b:=86) (joinSmall (lo:=8216) (a:=42) (b:=43) sp8216 sp8258) (joinSmall (lo:=8301) (a:=43) (b:=43) sp8301 sp8344)) (joinSmall (lo:=8387) (a:=85) (b:=86) (joinSmall (lo:=8387) (a:=42) (b:=43) sp8387 sp8429) (joinSmall (lo:=8472) (a:=43) (b:=43) sp8472 sp8515))) (joinSmall (lo:=8558) (a:=171) (b:=171) (joinSmall (lo:=8558) (a:=85) (b:=86) (joinSmall (lo:=8558) (a:=42) (b:=43) sp8558 sp8600) (joinSmall (lo:=8643) (a:=43) (b:=43) sp8643 sp8686)) (joinSmall (lo:=8729) (a:=85) (b:=86) (joinSmall (lo:=8729) (a:=42) (b:=43) sp8729 sp8771) (joinSmall (lo:=8814) (a:=43) (b:=43) sp8814 sp8857)))) (joinSmall (lo:=8900) (a:=342) (b:=343) (joinSmall (lo:=8900) (a:=171) (b:=171) (joinSmall (lo:=8900) (a:=85) (b:=86) (joinSmall (lo:=8900) (a:=42) (b:=43) sp8900 sp8942) (joinSmall (lo:=8985) (a:=43) (b:=43) sp8985 sp9028)) (joinSmall (lo:=9071) (a:=85) (b:=86) (joinSmall (lo:=9071) (a:=42) (b:=43) sp9071 sp9113) (joinSmall (lo:=9156) (a:=43) (b:=43) sp9156 sp9199))) (joinSmall (lo:=9242) (a:=171) (b:=172) (joinSmall (lo:=9242) (a:=85) (b:=86) (joinSmall (lo:=9242) (a:=42) (b:=43) sp9242 sp9284) (joinSmall (lo:=9327) (a:=43) (b:=43) sp9327 sp9370)) (joinSmall (lo:=9413) (a:=86) (b:=86) (joinSmall (lo:=9413) (a:=43) (b:=43) sp9413 sp9456) (joinSmall (lo:=9499) (a:=43) (b:=43) sp9499 sp9542))))) (joinSmall (lo:=9585) (a:=685) (b:=685) (joinSmall (lo:=9585) (a:=342) (b:=343) (joinSmall (lo:=9585) (a:=171) (b:=171) (joinSmall (lo:=9585) (a:=85) (b:=86) (joinSmall (lo:=9585) (a:=42) (b:=43) sp9585 sp9627) (joinSmall (lo:=9670) (a:=43) (b:=43) sp9670 sp9713)) (joinSmall (lo:=9756) (a:=85) (b:=86) (joinSmall (lo:=9756) (a:=42) (b:=43) sp9756 sp9798) (joinSmall (lo:=9841) (a:=43) (b:=43) sp9841 sp9884))) (joinSmall (lo:=9927) (a:=171) (b:=172) (joinSmall (lo:=9927) (a:=85) (b:=86) (joinSmall (lo:=9927) (a:=42) (b:=43) sp9927 sp9969) (joinSmall (lo:=10012) (a:=43) (b:=43) sp10012 sp10055)) (joinSmall (lo:=10098) (a:=86) (b:=86) (joinSmall (lo:=10098) (a:=43) (b:=43) sp10098 sp10141) (joinSmall (lo:=10184) (a:=43) (b:=43) sp10184 sp10227)))) (joinSmall (lo:=10270) (a:=342) (b:=343) (joinSmall (lo:=10270) (a:=171) (b:=171) (joinSmall (lo:=10270) (a:=85) (b:=86) (joinSmall (lo:=10270) (a:=42) (b:=43) sp10270 sp10312) (joinSmall (lo:=10355) (a:=43) (b:=43) sp10355 sp10398)) (joinSmall (lo:=10441) (a:=85) (b:=86) (joinSmall (lo:=10441) (a:=42) (b:=43) sp10441 sp10483) (joinSmall (lo:=10526) (a:=43) (b:=43) sp10526 sp10569))) (joinSmall (lo:=10612) (a:=171) (b:=172) (joinSmall (lo:=10612) (a:=85) (b:=86) (joinSmall (lo:=10612) (a:=42) (b:=43) sp10612 sp10654) (joinSmall (lo:=10697) (a:=43) (b:=43) sp10697 sp10740)) (joinSmall (lo:=10783) (a:=86) (b:=86) (joinSmall (lo:=10783) (a:=43) (b:=43) sp10783 sp10826) (joinSmall (lo:=10869) (a:=43) (b:=43) sp10869 sp10912))))))))
  have good : (List.range 10955).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 120000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 10954 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 10954 := by
        by_contra! hi
        have hb := Nat.mul_le_mul hi hi
        rw [pow_two] at hsq
        omega
      have hd := Nat.dvd_gcd (Nat.minFac_dvd n) (smallPrimeDvd n.minFac hfac hpr)
      rw [eq] at hd
      exact hpr.not_dvd_one hd
    · intro hp
      exact Nat.Coprime.of_dvd_right hm (hp.coprime_factorial_of_lt (by omega))





def tally (f : ℕ → Bool) (s len : ℕ) : ℕ := (List.range' s len).countP f

theorem tally_succ (f : ℕ → Bool) (s len : ℕ) :
    tally f s (len+1) = tally f s len + (if f (s+len) then 1 else 0) := by
  unfold tally
  rw [← List.range'_append_1, List.countP_append]
  simp

def fromBlocks (c : ℕ → ℕ) (f : ℕ → Bool) (j : ℕ) : ℕ :=
  c (j/512) + tally f (512*(j/512)) (j%512)

theorem fromBlocks_succ (c : ℕ → ℕ) (f : ℕ → Bool) (j : ℕ)
    (boundary : c (j/512+1) = c (j/512) + tally f (512*(j/512)) 512) :
    fromBlocks c f (j+1) = fromBlocks c f j + (if f j then 1 else 0) := by
  have split := Nat.div_add_mod j 512
  have hs := tally_succ f (512*(j/512)) (j%512)
  rw [split] at hs
  unfold fromBlocks
  by_cases h : j%512=511
  · have div : (j+1)/512 = j/512+1 := by omega
    have rem : (j+1)%512 = 0 := by omega
    rw [div,rem,boundary]
    rw [show j%512+1=512 by omega] at hs
    simp [tally] at *
    omega
  · have div : (j+1)/512 = j/512 := by omega
    have rem : (j+1)%512 = j%512+1 := by omega
    rw [div,rem,hs]
    omega


private def packet (i : ℕ) : ℕ := (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 5 then (if i < 4 then 0 else 0) else (if i < 6 then 0 else 0))) else (if i < 11 then (if i < 9 then (if i < 8 then 0 else 0) else (if i < 10 then 0 else 0)) else (if i < 13 then (if i < 12 then 0 else 0) else (if i < 14 then 0 else 0)))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then 0 else 0) else (if i < 18 then 0 else 0)) else (if i < 21 then (if i < 20 then 0 else 0) else (if i < 22 then 0 else 0))) else (if i < 27 then (if i < 25 then (if i < 24 then 0 else 0) else (if i < 26 then 0 else 0)) else (if i < 29 then (if i < 28 then 0 else 0) else (if i < 30 then 0 else 0))))) else (if i < 46 then (if i < 38 then (if i < 34 then (if i < 32 then 0 else (if i < 33 then 0 else 0)) else (if i < 36 then (if i < 35 then 0 else 0) else (if i < 37 then 0 else 0))) else (if i < 42 then (if i < 40 then (if i < 39 then 0 else 0) else (if i < 41 then 0 else 0)) else (if i < 44 then (if i < 43 then 0 else 0) else (if i < 45 then 0 else 0)))) else (if i < 54 then (if i < 50 then (if i < 48 then (if i < 47 then 0 else 0x53378b31096d8aae4ea240107c77034817009d44121a409983500dc0005331252fe1638a464c0233903075234316889b040e1a50a203600d0000532a8f30d169ca944df24410bc78835c17b09f84241ad09e03380de0005324143059694a704d42358fd873a33916e09e84301a609e03300ca000531d813171724ac44fd242908075434d1760a0c4321ae0a283440d60005316e031a974cae850c25090cc7843551778a084201b70a583600ce0005310863009650a684d9240104876633f16c09cc41a1ae0a2834c0d20005309f830f16b8a864d9233901075033116209743f619709c036c0ce0005303853049698a944e724310a078235717589ec4321b409d033c0ce00052fcef318971cabc4e223c104877034616e89bc41a1a10a003380c000052f65431b170ca9c4e0239902073433d16c099c40019f09a83540dc00052ef9a325977cade50a249105c75a34116789a040419509c03500e400052e91b3079688a664d4238901c73a333165897c3f819309403000b600052e2a33081698a884db237900873232b15e094c3ce18609383100ae00052dc0631b1710ac24f8249909077c35b17589f84301b40a403780d200052d55d3221770ae450a24b10c878a3521788a104341a309b83540d400052cecf31496f8aa84ef23b905c75434316c09a440419a09c03580b600052c85130996aca924e323a903475034716c89c040419d09a033c0da00052c1b031b172cab64e223b900474233a16589a03e8194095032c0d800052bb403019660a744cf23590287563421720a1842c1a50a003440e400052b4a631a96f8ac44f724610a477834b17289cc4241a70a203680e200052ae392fe1670a684cb2280fa46fc32815d89603de18709082e40bc00052a7b530e96e0a9e4e9242107475234316f89fc4201aa0a003340c800052a12d3141720ac04ea23e109477e35617209cc4301ae09e835c0e4000529aa23199724ab24ed24890bc79635917009e84141a809f03580d400052943a301967ca644ca230102075433e16809ac3fa19d09e03300d0000528daa3139700a964ea242108c76034c1718a0043a1af0a183340c800052873c3099690a8a4e023a104076c3531758a004221a909a835c0dc0005280b331496c8a824d82380fe874032c16589783de19e09d035c0d60005279fe3279788afc51625310e07a635f17e0a484561b509d83600e6000527392301967ca5c4ba22c0ff073032c166898c4001a409e03640cc000526d0b30d16a4a7a4d9235900474833316a09e441e1a609c03580d000052667b3189704ac24ff24910d879635717809d842c1af0a103540e2000525fd231e9744ad44f0246106c76a34316f09f441e1a30a083840dc00052593531716e8abc4fb243906c76634616e8a1c4361b90a9836c0e40005252c4304166ca5e4c222b8fe473c33a16689984101a30a083640d8000524c4b3099698a8a4ce234901073032215f89ac3fe18509383000bc0005245c330c16b0a804d7235100871833216a09c04101a309e83580d6000523f183219778ae851325891007b636c1820a7045a1bf0a603740e000052388a3141714abc4f1245908076a3501700a0841e1a709f83700d000052320b304966ca6a4d4239903474634817089f844a1ac0a0835c0d6000522b723141728ad44fa245109077a34e17309d041a1a40a003380c60005224f530896c0a864e3238103476834c17209e441e1a809d835c0e0000521e833019654a524cd2330ff073433016709ac41619909b03500d000052181b3011648a624cb23a101073a33716689803fc19409603200d80005211bb301966ca764d5238901c74033f16e09e842a1b009a03680d6000520b4c303965ca744db236900c73632d16689843fc19f09b03480d00005204c130f170cac64fa240106075834116a89bc4101a009d03340d200051fe143219728ab04f324e90a077034d17309dc41e19b0a083480d400051f7a830696a0a9a4e8244108878a35b17709f84201a309c03400d200051f0f83269784aec51225711287b036717d0a684521b20a2835c0e000051ea6a3131704aba4f2247908476e35017789fc4441b00a403700ce00051e3e830d96f0ab04e423e107c77c35817a0a1843c1bd0a803900de00051dd5c3119708aa64f8245106475c35117389f441a1a909f03440cc00051d6b1322178cada50725190d47983691820a6844a1ba0a103a40dc00051d03030b16b8a864d0238102072e33816b89c040a19909f83580be00051c99c31e176cad44fc24690a077a34f16c89c84001a40a403680e800051c2f331d1744abe4f9246908076634d17289fc41c1a709883440da00051bc8f30796b0a9c4e223a903c7643491748a084421b10a583740e200051b5f63199728aca4fa249906c75c34217109d03fe197097832c0c200051af7f30816a4a904e223c104474e34a16f09f843019b09d03580e000051a8f031416e4aa84e623d904c76634716e09c04281a70a0036c0c800051a25831c1748ab64ff24890a076234f17409f042e1ab09f83340c4000519bd131116d4a884da236102473633115f89943ee19709f83540d6000) else (if i < 49 then 0x54d9e531396e0a904f0241105076634616e89e04141a709683300c200054d36b30916b0a884db23a104076633a16b09b04081a709a83340c600054ccca31c972cabe4f924890c077a34f17609f44341aa09e035c0d600054c65e2fd963ca6e4cc232101074433215e89403d417809002cc0aa00054c01f2ee95dca244ad2248f886da30915b09703ea18609302dc0b400054b96332997a0b0a516259910c7a836f1870a8c4781c00a783840e800054b2f73011668a5e4c9232900c72a332167897c3f019909a033c0cc00054ac6531596f4ab44f4247106877034f17089d440219209b03380d600054a5e130c9694a8a4d923b103073a32d16789a44041a809d03380ce000549f7a3009660a564d0237100073633b16a89c440e1a709c83540d40005499063009648a564ce2310fec72c32f16389a04101ac09e03680d600054928330d16d4ab04ee245906476233c16b09c03ee19a0a083440cc000548bc73261744abc4fc246108877e34b16b89bc4161a80a083580dc00054855930616aca764cb231100474433f169899840219409883140bc000547ea93221744ad04f224990a479836517a8a2c4241ac0a203600d800054781b3151728ad850124a90b077a34c17289c041a1a509c83440de0005471873159710abe4f1242903c75c34916c099c4101a70a203680ca000546afa30e96a0a5e4d02370ffc74034116b89c040419b09883380c400054646c31296d8a904da233900073e33916909b44121a00a203700e8000545df73049694a6a4d42348ff473034016f09c840619b096033c0c60005457902ff9670a544d4233101c73c33516189a44141a609c83280d400054510e30d96f8aa24dd237103074833e168098c3ee18809583340c8000544a7f3149704a9e4e723e903c76834816f89d04161a509b03440d200054440e30796aca804d7235901073e33b16c89ac41c19f09d03640e2000543d9a3071694a824de238103c75234817289c440619409983300ca00054371d30b96d0a9e4ec247908c77c34917209c0412195098831c0b2000543086317970cab64f6247108476a35017389d04221a409803040d0000542a0630d1694a804ce232900873c33916909bc40219a09903440ca00054234f3221738ac24f223e106477a34c17289cc41a1a509d03300d2000541cb531c976cae450024f90e07843501760a284281ae0a083440d000054161f3149700a964e2239904475834717009f441819b09b833c0c0000540f993089688a7c4d423b100071431f15989183ba17608d83040b800054091830d96e0a8a4dc233101472a33416209944101a10a103600cc0005402913111718aca4f7245107876234717189d842c1ab09f03600d000053fbfe3159728ab84f6240107876e34a17289e44041a209a83340ce00053f5903051688a6a4d923c903074c34316f09e84221a309983300c800053eef33209758ad64fb245108477c35d17389e84241a709e83480cc00053e85831b171cac250224e10a477a35b17109e04221ad09d83380de00053e1d030e96dcaa04f124090547723521730a1842c1aa0a003440d000053db613031680a6e4cc233102074433d16e89e041419f09e83580e000053d4e530b16a4a664cc234900073a33116a09ac40619909683380ca00053ce6031196d8a9a4e723c105074633f16b89a03f41a209f83800d600053c7f32ff1638a504b42278fbc72432916a09d04121a109e03680e400053c16a31796f4aa04ec23e102875234416e09e44281b109f03400d000053badb314971caa04f1241906476834217009a04081a509c035c0d400053b42c31d1720abc50224e90a079636217e0a684581c10a7037c0dc00053ad92319171cab64fc243907c76e35217409e441a1a409c834c0cc00053a70231796f8a944ea23f105474c34916f89b042e1a509d03300d800053a06131696f4aa24ef243906475e3491740a0441c1ae0a1837c0da00053999f3289794b0851024c90b078035917a0a2442a1af09f03580d400053930831296ecaa64f124110407603401710a084361af0a303880d6000538c8131496f8aaa4ea23b104075234417209e043a1b40a483800ce0005385e931496fcaac4ee240905876234616f89a841019809b034c0e8000537f7630d96e4aaa4f1247109877635017409f042419e099833c0dc0005378fd304967ca6c4cf2360ffc73a33b16789b840018b09282fc0ca00053726a31296d8aa64e523f905876234917289e041a19809e03400d4000536bc531d9760aea50d25190e47aa36617c8a3c43c1b209f83580ec0005365642f79630a464c32280fc072032815e09583e419309a03240ba000535edc30f96f0aa04ea243106475834b17109dc4101a109b033c0c00005358443199738ac650924e90c07a83621778a044201a009a82fc0c40005351ab3181710ab04e9243909c7743481760a0842c1b40a283540e2000534b2331196d0a924dc235900874e33b16d09e04261a909f033c0d400053449f30916c0aa44e923b106475234116c89d84121a909c03280c0000533e1031316dca9e4ed249109477c3501778a384321a609e83700d0000 else 0x567bb231316d8ab44f5242108c7763601780a3842a1ae0a583580d800056751e31616f0ab64f724b10b478835117909d84181a609e83700dc000566e8e31b1768acc4fc24a90b479c3681810a4043c1bc0ab039c0e400056680a30d96d0aa44ee242105c76834917009e441a1a309a83240da00056619730416a0a824cc2308fd872c32615f09683e619409583040ba000565b1830c96e4a924de23b904473a33516689d84141ac09d83300d40005654ba2fb962ca544c222e100872432915d09343de18f09783500d0000564e3d30596a4a8e4d92330ff872c33416989b03f419b09903280d00005647b83071684a6e4c922d8ff472432816309883f019f09f83700e200056415b2f79608a364b22280fb070832f16409803ee19109583100bc000563ae630996c8a8e4da23d104873833916b89b040e1a509d03340de0005634793029690a7e4d523b100872c32816289743ea18b09c83240d6000562db533097e0afc50c25410f07a83591798a0c42e1a90a4836c0de00056273030c1688a5a4bd2288fbc72a32b16789903fc18f09383300c80005620ce2fc9638a564b922b8f886ea31115709303dc17e09502ec0b8000561a1d31e9748ade51025010e879c3581770a1843a1b60a803680da00056138a31316dca9a4e223b103077034d1718a0c4401b20a803b00e0000560d0730b96b4a804d7236903875233f16909c040a1a00a103680d800056067631c9748adc4fd24a109878035517589fc4241b00a283640ca0005600003041698a844cf2378ffc72e33216289883fa19909a03380c600055f97f30b96a8a684c42330ff87423441770a3c42e1af0a283400ca00055f30c30a96a0a744cb2310fcc71232015b89483d818a09203280c400055ec6f3189700ab84f3246908c77235117009f041c1b10a003400d000055e5ed31696dcabe503248908c78035217109d04241a109d035c0d800055df3032b17b0aec51225090f07a43711828a704621c60a883a40ea00055d8ab3139708aac4f2242106476234517109ec4281a20a503700d600055d1f7329177cad8501242105c77034e1768a4044a1bb0a803800d400055cb4a31f1770aec50824b109476c34e17489f840219409c83200c600055c4ca30e16dca984e723e104076634817009f04281b00a103600e000055be313189704ab24fb24810a077435a1790a104381a709f833c0d600055b7bc30716a0a804de23c102c73a33316389843ec18c09583000c200055b144306969ca7c4d22340ff473633416809b43f419009c032c0cc00055aab631416e8a9a4e423d104875234516d89dc4181a10a103540cc00055a42e30e9704aa64ec240104075c34a17389f041c1a60a1834c0dc000559d7932a97a8afc51424e90e079c35917489ec41c1ad0a083500d600055971f2fa1628a504cb2308fd871c32915e896040a19809c03480c60005590d82ef1628a524c322c8fec73833916489603cc18208f82dc0b0000558a4c30d16bca8e4e823d103475833d167898441819f09a03340ca0005583df30516c0a864df23a902873433916b09e842a1b30a3833c0c2000557d5a30d96b4a9a4ea23c907075234616e09e040c19d09a03640d80005576dc30a96c0a904de240108c77435217189f04341ac09c03440d000055704d31216c4a944df23f103c75c34417289e042a1a80a083940ea0005569b83199770af450924c90d077635516f09b83fe19c09803100ca0005563123211784b0251524e10c877a3521738a044441b70a783a40ec000555c8830996b0a944df240106474c33316989a43fc18d09103240cc0005556193071688a704cf22f0fe071e32116009583d418408f03040d6000554f8c3121710ab6500246909876c35417509fc4201ae0a603800ec00055492a2fa1630a464c722b0fd472232e16489a84261ab0a2037c0e40005542933159724aba4fc246107c77234f17309ec41a1a009b83400c4000553c0331316e4aaa4e223a104075234316c09b040619709d833c0d000055356f3151718aca50524d109c76e34c16d099c3ec199095831c0cc000552f132ff9680a7a4d9235102c73e33916709a04021a209c03540d0000552866321975cac650025090dc79a36617e8a2842a1ac0a383640e40005521d931016f8abe4fc247907c77835217189c840a1a409e836c0da000551b3d315973caea50824f10a87a03591780a244341ae0a283640d200055149c3159724abe4fe241905076234716f8a184461ab09e033c0c0000550e043169734abe4f024990a078235a17209dc41a1a60a3037c0e200055076f3159704abe4fc245105475634316f09a44121a409f833c0c60005501162f79644a5e4c22330ffc73833e16c09b04201aa09f03540dc00054fa96306968ca724d2236102073e33216d09dc4181a80a403800da00054f42c3031654a5c4bd2328fec73233c16d09c041e1a009f03400c800054ed8931e1730ae250624e90bc79035217889fc4301ad0a2036c0d200054e6e93199754ade50124a10c078a35817409e04321a509903440dc00054e0783031678a784d0238902c73633816b899c40219f09d03380ce000)) else (if i < 52 then (if i < 51 then 0x581ca23011674a864da23b103874e34617089e041c1a409c83440d000058161530f96fcab24e923d905476034d16f09d44201b20a2034c0ca000580f863171710aba4f1241103c74e34316a89c43fc19109903100b40005808f830f96c4a8a4da23b102473633116989ac3da18108f031c0ca00058025a3171754ad04fc24a10c476e35417109c84141a009a03440e800057fbd930d96d0a8c4d62358ff472e32f162896c3e019109283040c200057f55730d16bca8a4e223b102c75234516d09d44141a809783140ca00057eec93151744abc4ff244905c75235217389e84321a909c83000c800057e8553081694a724e223f108476e34b17289d840c19d09b834c0c800057e1bb3161744abe4f5243908078436217a8a084341b60a883940f200057db2f3149708aa44f723f905c76a34616c89cc4181a90a0835c0d600057d4a331196dca984ec241108477a3511700a0c4341af0a583440c200057ce2431116fcaa44ee245108877234617089d4418196098831c0d000057c79131016d8a984e723a9014746331162898c3fc1a20a1036c0dc00057c10e30816aca824d7236901474834516c09b04121a60a403700da00057baa1304166ca624cb22a0fb470a32516109984001a00a103600d200057b41a30a96a4a7c4d0238903474833e16789ac41019409483240c800057adac3009698a864df23e905877435a17289fc4201aa0a3036c0dc00057a73a2fe9688a524c122e0fec72432c16209643fc19c09d032c0c000057a0d12fb1660a684c622f8fe472633016709443ea18d09303340c0000579a623049668a704d4231901c72832c16389583e619509902f80c000057936f33d9850b4252825991447c637817b0a404501b90a303600d2000578ce030f96aca944e723e908c77834b17109cc4121b009a03240be00057864b31716fcaaa4e823d902c75c33616a09ac4061a8098831c0d8000577fe42fd1670a784ca2338fec73433416209c440019409903540d60005779443189718ac44fc24d90c079436617b8a404481b60a483840f20005772aa31296d8a924e823f905c75634616e09b83fc18e09483300d2000576c3f2ff9688a844da23c102c75833d17089c441c1a109d03540da0005765cb30916b4a9a4e7241105876e34c1720a084481bc0a683600e2000575f4730c1698a764d623d107877a35517589e441c1a40a083500de00057588f3269788b0050e25390dc7903571790a384421b30a403740cc00057522f3049668a584ca235102874e33f16a89bc4141a509c03540d0000574bc92fc1618a5c4c9237102074234416989943fc19909a03600e800057454a30d9708aa84f5243908478035a17b0a0842c1b50a283740d0000573ef02fa1610a324bc22c0fb471632416109643ee19b098031c0b00005738773069690a7c4d8238905476634f16f89ac3fc19209683300d00005731e93199720abe4fc24a90c078235d17b0a344321b90a3036c0be000572b753029660a684c9232900873233716f09d44321b00a703680d80005725113011674a7e4d8232104076634916f09b8400190098833c0d6000571e783171718aa64e823d905876034c17289e84161ad0a403700e20005717bf325175cac44fc24810987903511748a184441ac09f83440d200057112331116ecaa24ed240104c74633e16d89d040a19809683140dc000570ab73051684a5c4c722f0fc872232c16609803f619609c03400d20005704593031674a804d622f8ff073233916a89a040019e09803540b600056fdf52fa162ca5a4d42350fdc72633216389ac41019f09e83540cc00056f77c30a1690a6e4cd237902474433916989d841619f093832c0d200056f0e13179720ac84fd24c10e47a436017a8a284341b409f83500da00056ea6230a16dca944da235901075634116d09dc40e18f099832c0d400056e3fe2ff1614a464bd2250f846f631815a895c3dc19109283440cc00056dd9e3019688a804e423e108c76834016a89883fa19309c83380c200056d71d30b96b4a8e4e4237903c75434016d09b43fe19c09c83440ce00056d0c82fc1650a504bf22f0fcc71e32015889283d218c09403000c000056ca3231616ecab64f4248107c75e3501790a3443a1ab09a83200b600056c3a731296f8aa84ed245106c77a35b17a0a2c4261a40a303640e200056bd2230a96cca944f1244106876234d17a0a184361b80aa039c0e400056b6a130f96c8a9e4e5241106876a34316b09d04141ae09e83340da00056b00231d1760ace50925190b877c3541760a144321ad0a1835c0e400056a96631616f4aba4ef245106876033a16709883f819309503180ca00056a2f730b1668a644df23d103475034017309e04181a40a103680d4000569c5a31a176cae450824c908877235116b09cc40a19b09783100c20005695e63059678a524c922e8fa870c327159893c3d0187091830c0c0000568f4731b9734ac64f524490a87683541760a204441b50a4834c0c80005688be31296cca9e4de23d103075c34716989a840c1a309d83800ee00056824430896a4a6e4c92328fe072a32b15e09883fa18c098031c0c0000 else 0x59bd5c2f8164ca4c4c922c8ffc73233416a099840e1a609903380d200059b6c231296fcaae4e023a909876a35317309f04221a609a83280cc00059b00632d178cae650a25291087b437217e8a5444a1b10a883640e200059a9a62fc9660a7a4cd2310fd072233016a89b440619209983300d600059a33b3021694a704cd232901074033816909bc40619f09a03300d4000599ca931296e8a8e4e423a904875834a17089e440a19f09c835c0d00005996183129708aac4ec23e103475834116c09b840c18f09803380e2000598f9030916b0a924d8238104c76033f16d89d4410197097032c0c200059890431316fcac64f6247108875e35217409e44221ad0a083540ca00059826e31b1740ac84fd245108477a35017309f842e1b30a083400d2000597bc73199740ac4504245908478035c17b8a3c4441b50a203840d60005975493059684a824cd237101073632f16389c440819a09982f40be000596ec630c16c0a9a4dd2328fd471631c15b895c3f019009503200c800059685130a16b8a9e4e5240106475434416d89d84201a209c03440cc0005961c630f970cab24e6243903c72c33816589883f819009783480d6000595b2b31f174cac850725290dc7963591780a4c4601bc0a883ac0ea0005954d12f89630a564d32370ff472e335163097c3de18d09683280b4000594e4f30c96c8a824db23e101c75434517289e44241b109f835c0c40005947f02fa9644a564bb2268fa470c32115f89583e218e095832c0ca00059416030e9708a964f024510b479a36217689d441219709b03400e4000593ad431016dca9c4e123a103c74c34016d09a83fa19c098032c0d20005934902f095d0a284ba22b0fc070831d15989703f219709583280c0000592ded31a1710ad24f3246908c76a34816f89ac3fe19409383300c40005927812ff1650a5a4c82311010742336167899440619409683340ca0005920da31c172caba50024b109877e35017509cc4041a10a183600da000591a4b3149718aba4ef246907874e3501720a1042c1af09e83500d80005913cd308167ca964ee24810ac78834b17289f841e1ab0a3036c0de000590d6a2fc9658a4c4ca2329004736336165899c3fe18e09282f80b60005906da31016e8a8c4e323a103c76234616e09ec43c1aa0a503900e600059002e31d1750ade50824b10b878a35817b0a3444c1b80a903900e000058f9d92fa1638a604c52318fe071c32a160096c3fe18e092831c0c600058f34a31416dcaa04e723d106476034a1720a1842e1ae0ab03740cc00058eca831c1728aa44e6239906c75c33d16e89d842419f0a283740d400058e6223159744ac04fe24590a075c34316e89c442e1ad09d83480e000058dfcb2f59604a2a4b622a8fa870c31e15f89583e418d08f83100d400058d92131d9744ad250825210cc79635e17b0a044521b80a4838c0e200058d2b230716aca904e623f903874a33216909bc3fc19809d83580d800058cc3030a96b0a784d523b904c77034816e09b840e19f09b03340cc00058c583324174cad450224e90dc7823571748a144341b40a403540d200058bf0230c96d4a884ea23d905c74e33516989b840019c09a83280d000058b87b31116cca864dc237100c71a32716509bc41e1a80a0832c0c600058b1e33191734ab64ea242907076a34016a09a440419909803180d400058ab4b313972caae4f524390987763541780a1843c1a80a583940da00058a4ab31b173caca4f724990a076635617309f042e1b80a403800ce000589e2531416f0aaa4dd23b904c77034316b89d442e1af0a103600e00005897ab30a16bca7c4da236903473e33d16b09a441619009583380c00005891433019664a564c522c0fb46fa31b15c09403e619209503380d2000588ae62fc1658a624d323a902873432516289803fc19209503140ba0005884583121700abe4fa244103c75633916589a43f219509583140c4000587de83031664a664c92308fe472c32e167098440619c09a833c0d400058776d3051680a784c32298fb46fa31415809303d018309183180ce0005870d131c1730ac24f8245106075834b17409e04321ae0a683ac0ea000586a6c2fe166ca664c9231901074833b16809883fc19509683500d60005863f53069688a824cc233100c74233516789b84261b30a3835c0ee000585d8230e16d8a8e4d92378ff87503441720a184441b70a403740e000058570730d16c8a904dd23f104073e33a16409844081a50a083540d200058507430d16d0a9c4ee23d902c75434016c09a840419b09983180c80005849eb31716e4a9e4de232101473c34316d89ec4401b60a503740d400058436930c16b4a944da235903074633c16909a43f81a009a03580c4000583d132fa9634a4e4c22310fd471c32815e895c3ee18809603240bc00058368b3179720aaa4e223b900873c339169899c40e1a409e034c0d60005830232fe9658a6a4d3238902474834716f09a83f419a09683340cc0005829a930a1698a8a4e023b102473833b16409943fc19609b03580dc00058230c31716ecaac4f9241908c7703501750a0843e1bf0ac03ac0ec000) else (if i < 53 then 0x5b5e042f9964ca4e4c222f8fb470c32216089503dc190099831c0d20005b57923039678a824ca22b8fd071232315708ec3b217608a83000c00005b50ca33297d4b0051525811107a63591780a2442a1ab09e83580e20005b4a663031674a624bd22a0fa871c322162099c3fe19d09e03280c60005b43cf3189718aba50124710a878e3571748a1443c1aa0a083840ec0005b3d2a316972caca50824f90dc79235617289f04301b109f033c0c60005b36853209764ad250124890e87963751868a804621ca0ac83940e40005b2ff63141724ac04fc249107c7743501790a184381aa09f83600d80005b297930816c4a8e4e523f906c75c34916d89cc3fe1a009a03140c80005b22ed3179738ade50624d10d878035d17689e44381a809783200c80005b1c7b30a96cca904e323d105c76234d16d89dc4181a409e833c0ce0005b15e931516cca884d5234102072e33116209ac4121a70a0034c0d80005b0fa42ee95dca144a72238f9c6fa31415609383d217c09282dc0bc0005b09043151710aba4f8246108077c35617509cc4261ac0a083400d60005b02a32f81620a604c42320fd071e31a15c89703ea19009603100d20005afc1c31316c4a9c4dd23d105c75434416d89903f018e09402d40b00005af57a31f9744ade4f924910a077635817a8a0c4381b30a603480cc0005aef093049668a764cf231102473432c15b89103c018108c82f40d40005ae89d3019690a824cc2328fec72c33516b09984101a80a083580c40005ae21131396f8aa04e623a100c73833416909a03fe194097832c0ce0005adbbe2fc167ca7a4d7238900872433616a09bc41c1a809b83540d80005ad52e31496d8aa64e223c102474834116d89d842c1a609e03300d20005acec43051690a8a4e423e105475834717009e44301ae09f03540d60005ac84530f96c4a904e0235102072a33716a89f84221a109903200be0005ac1b731016fcab84fa24f10c078e35417189f843e1a609e834c0ce0005abb1e31a9720ab84f3244908476e35817a0a2043c1b309f033c0c20005ab4a430d96a8a904e523f904074a34516e0a0043c1ac0a283640e60005aae1531596dcaba4e823e902874034016d09b440019709a036c0ec0005aa78c31496dca7c4d022f0fe072233016809b04101ac0a103500ea0005aa10830e96e8aa44e9244909077435217309bc40a19809b83440ca0005a9a6b3171708aaa4ed241106074633c16589ac40819609683340d20005a94052f91628a444c6234900c74033516789b04121a309e83700e80005a8d9c2fc1658a624c6236103473c33c16c899c40619c09d83240d60005a872e3041698a6c4d4234100873432e16189783e019409a031c0b60005a80a830e96a0a844db238100872633116589943fc19b09b034c0ea0005a7a502f69640a4a4bb22d0fe872032015f89803ec19709b835c0d60005a73aa323976cae650224590847703571740a0c42c1af09f03440d40005a6d1c3131710aac4ee241906c76c35117189b841c1a009e034c0d20005a6692312171caa44e7243907076634816b09a441a1a809e83640d80005a602030516aca724cb22f8fdc72e34016e09943f2199095832c0de0005a59c42fd1670a4e4c42300fb871031615609343c018508d030c0c00005a53433051684a7a4d322e0ff473832a1648998408196098832c0d20005a4cb830f16e8aa44e5241106476234516f09c440a1a509a034c0ea0005a463a30c969ca884dc237102074233516309843ec18909583300cc0005a3f9332517a4ae850524b90c877c3571768a104381ab09d834c0dc0005a392130a96bca8c4d4238102874833e16e09cc3f819809783080be0005a32cd2f295fca364b12220f8c6f0307153891c3c017c093832c0c40005a2c2e31596fcaa44e0237901475633e17309fc42a1a90a003400c00005a259e30e16dca984de23a901c74a33f16e09c84241a109a83380ec0005a1f3030116b0a8a4d8238902c73632c16189583e618609303100c00005a18c32fc1668a6a4d1231900c73232716089343da183096032c0c80005a1243309168ca824dc23c904875233b17089f442c1b10a3038c0e40005a0ba43131710aa84e0241105c75a34116a89e042a1af0aa83a40ec0005a053230b16aca8c4e2238901c73034116d09c83fc18b09803480e000059feb131016f8ab64e523c104473c33916609983fa1a309c032c0ca00059f81a3181710abc4f724610ac7843521728a1442c1a90a383700ce00059f19e3029664a6c4cd237102475634616d09bc4121a109f03400c800059eb293049688a844d8235101873c32f162098c3e618509683280c400059e4b4300163ca604bc2270f8071032816209883fa19c094832c0cc00059de2e30d16b8a7a4d22320fd4732330166097c40219309a83380be00059d79c31396d8aa04e823c105c76a34d17109cc40819609483480d200059d0fa31a96f0aae4e7240105c76435317489d04221a909c03700d000059ca5c3201738ac04fe248905877834d17109dc41a1a509d83740d600059c3b431b9714ab64ff24c90b47a83681800a384421b409d833c0e4000 else 0x5cfd7e304967ca684c4231100473832e16309a83fe19a09903400bc0005cf6f630f16ccaa84e7243107475833e16909b84261a709f03500d80005cf0952ff9680a684dd2380fec72833c16c89fc4221b60a503680d20005ce9ee31b175cade50224c10c478a35a1788a204381a909e03480ce0005ce3972f6961ca364ae2240fac70231c15e89843da18c091831c0d40005cdd1530b16aca864d52358ffc74033416b89bc40019c09383080c20005cd6903141710a8e4ec244106075a34216f09e441019f0a283540d80005cd0362f8964ca4a4be2268f8c6fa31115889203d818609303300c80005cc9a3316172cac44fe247908477635b1730a2c42a1a709d033c0d60005cc32730b96c0a9c4f0246909877835117189dc40e1a70a1834c0de0005cbcca2fd1650a464c422c8ff072e32f16389883fc19709d83680dc0005cb63d30e96c8a944de23f906874033c16789a43f819e09803080ce0005cafb63079690a6a4d122e0ff473032b163098840018e09103000bc0005ca92331896f8a9e4e023d903c74234916b89ec4321be0a583640d40005ca29d30996d8a924df235102c74a34316d09bc40619709703240bc0005c9c1b30a16a8a804d923c1040754337168896c3f019809d033c0d80005c95a73059690a8e4df239903c75834e17109fc43c1b40a4835c0d40005c8f2b30b16cca9c4ea243109c76a35017589f042a1b609f03480d40005c88bf306967ca6e4c7237102875a34417189e84201b90a583880f00005c823c30c16d0a8a4dd23b901872833216309783fc19309403200c80005c7bd92fc1650a4a4c0230901873a34117309e840419e09c03340d60005c75663089690a6e4c72328fb872233716389843fc19509a03380ca0005c6ee830b1698a7e4d623d906074c34317189c041218d095831c0ce0005c687630496a0a7a4cd235900072c33316a09d44221aa09d03600d40005c61e230f96ecab64fc246109076834a16e09a040e19c09983240c00005c5b5d31096dca984e5247108c77c35c17a0a304301ab0a783740e00005c54e030896c0a8a4e123e101c73a339167898c3fa19d09d03700d80005c4e6f2fe9628a504c02328ff071232515e89783da18309283180cc0005c47ef3019678a664cb235101873633916409403e418709102fc0c00005c417b3001668a6c4cc237904476034816b89c441c19c09c03300d40005c3b1e2fc9684a8a4d4232902074c33716a89c040c19809b03100be0005c346d3241784ae44f924d90ac78c3581780a304381ae0a503880dc0005c2deb30a16aca824db241104c77034617209c44281a109f03540ce0005c276731016e8aae4ed243906075e34d1700a3442c1a70a203540bc0005c20db31116d8aa04dc234901874433416809d841619a09b034c0d60005c1a683069680a504ce2330fdc73c33c16a09c04101a60a003580d40005c13d43161724aca4fb247909478035217909f84301b109f03600e00005c0d6d3009658a524cc233902074e33a16909a440019e09883500d20005c06e431116d8aa04ea240106c77635e1768a184421a809d83640d40005c006130b96aca9e4dd238904074634117109e44121ab0a203700dc0005bf9f13019674a5c4c4234900c73633c16989a84161b60a3039c0da0005bf37d30596aca8c4da2330fe072a33215f09803f819509a83100c40005bed0e30416a8a884d3236103473c33116489a03f819609303100c40005be6603229774ae650824b10ac79e35d1768a0c42e19a09c834c0d80005bdfd831016c0a8e4d5233101c74433816509ac40819909783300d80005bd96f2fd9684a7e4c82320fd873233b16409ac40c1a209f835c0d00005bd2ea31116e4a924e7241107475033d16989bc3e418f09883380bc0005bcc7f30596b8a9e4e623e105076e3521740a0041219509483100c00005bc6192fe9650a6a4c522f0fec72c32315f89683dc19509603340d00005bbfb62ff1658a704ce236900072e33516809984141a609e03480ca0005bb91b3171710ab44ee241908877034616e89f44261b50a283840ec0005bb29430f16f8a904e723a905076834716e0a084241ab09f834c0cc0005bac1830916b4a884e123c105076234416e09f44381b80a783640ea0005ba5a13089668a764d6238905077434517589e04081a109883440da0005b9f2130c16bca8c4d923e106476034d17209d04221a609f035c0de0005b98a330b16ecab04d823c103474034616e89b44141a50a083780c80005b921731116ecabc4fc24590b477635217089ec418196091032c0c80005b8bad2fd1670a744da236901872432a164098c3fe19f09683380c00005b85123179728ab24f924790847703561728a1c4281ae0a583740de0005b7ea62ff1650a684d023c905075434016c89dc41a1a209f03300c20005b7841301968ca684d3238103074834517009b84101a509883240de0005b71bc3171710ab84fa24e10a077435017909f44181b30a103540cc0005b6b283171730ad04fe249108877434716f09f441c1a109883180dc0005b646832617a8af050424e90f07b637317b8a3c43c1b40a283440d0000))) else (if i < 58 then (if i < 56 then (if i < 55 then 0x5e9cef31616cca8a4d923f902c75834316a099440419809983480d80005e968530816aca784d8238101873e34816f89f84281b00a4837c0d20005e8fd931c1730ae650425190b07883581780a284521b709e03540ee0005e895c30d96d0a944dd236100c74633716e09e040c19909683200d60005e830c2f6964ca564d4233901074a33c16309483e819309703300d40005e7caa3051660a5a4c922e8fb471232515f09803fa19809903280d80005e765a2f4161ca464af2250fc471432515b89243bc18b09082cc0ae0005e6ff03061694a744d82350fec71c32d162895c3ec18c09282c00b40005e695b3149728ac64fe24b107476434517109f44321a709f83600da0005e62f62ff1658a5a4c422d0fcc71a32316009503f819809a832c0ce0005e5c6431416c0a8e4e423d905476434e17289ec4101a809b035c0dc0005e55ec3071690a744d2238102474034016b09a040c1a80a283580d60005e4f7630a96c0a844e123a904c75634d1758a0c4161a50a003240cc0005e48e630e16dcaa24e3240109078235617589e842e1b00a183840d00005e42523199738ad250824a90c479036417c8a344501b509e83440d20005e3bd730d16d0ab04f3241107076435117289ec4281a80a2036c0ce0005e35323179718ab84f324410a477e35217109cc4141a309f83740d20005e2eb830b96b8a944e7247105875e34917009f842e1a009e03540d40005e284c2fe163ca424bc22e8fec73833b16a89c841819709f83380de0005e21cf30816a4a704cb2358fec74a33816d09a44061a209e034c0c40005e1b712fb964ca5c4ca2348ff473633616a09944061a50a083680da0005e150030b96b8a844c822e8fd472432715d89783e418809582f40aa0005e0e8331116c8a8e4df23d900875233d16d09e44141a009d83140c20005e07ee31416c4a764d923b903472c33616989d44161ae0a583740ce0005e015831a16eca9c4fa243107875c34917609e04281b30a3838c0e00005dfafa2fe1668a7a4d423f104074633c16c89bc41c1a109f034c0d80005df4553179704aa24e324290807683471778a044261a40a0035c0ca0005dede530916bca944eb23f104474c34616c89b04061b00a103680ce0005de7842fa1638a344bd22e8fcc71e31915589243d018309183100c00005de0cf31f9724ac44fd24a109475c35216f09e44241a109a83440e80005dda3e31096d4a984e923f105875e34016f09c44181aa09c83380d00005dd3a231c171caa44f324b90b478235617209cc4121a509803380d00005dcd1431096d8aa84f624110647723531720a1442c1b20a203680d00005dc694318171cab84ed242905c75834816e89c041a1ae09b83580e80005dc0123061690a784cd232101874e33d16b09cc4161a80a1036c0e00005db9c42f8960ca404b722b8fe070632415a89503f819309983400e00005db3223219740ade50924a108877035517409ec4181af0a0835c0c80005dac9d30a96c0a924e523c904c76a3521778a2043a1b40a2835c0da0005da5f63181718acc4fc24810987743531778a404421b80a603580e20005d9fca2eb15c8a0e49b2208f4c6f231c15d091c3ca19109783240d00005d993131516fca984ee23f905874834316709b041c1aa09d03580e60005d92bb30716c4a9a4dd23c903c75033b16e09fc4261af0a303680e40005d8c3730c96d0a9c4ea243106876834917089d04161a90a3032c0be0005d85bb303968ca4e4c02270fa471e32515b89283de18d09883000be0005d7f4e302968ca9c4ea23d903874633516709783de181094830c0b80005d78d830916c8a824dd238901873a33816a09883f819509783200c80005d72653061688a724ca237903875c34316d89c84141a10a283740f00005d6bf13039688aa24e8243905076e35216e89cc41a19109603400ca0005d657a3021648a4c4bb22c8f9c70231015809243d817c09283080b40005d5f0c3001658a5a4c922d8fcc72833016609683ec199095831c0ae0005d586f3169708ac44f124a107c77034717109e44201ad09d03400c80005d51f230a1698a7c4d7235101073232d163897c3fc1a209e03300e00005d4b6730a96cca924d7238107077635316c09d04161a009903440d20005d44d831016b4a804d4239103875234717209d84161a309f03440dc0005d3e6330a96b4a864d12390ffc74033416889b83fa19309483380d00005d37d531316d8aa04dc240907075a341166899c4101a509b03340d60005d315430d169ca924e3241105874a33e16f09e04361ae0a203480cc0005d2adc30c1698a9c4ee23a906477634516e89c440819409b03480d00005d24912f5161ca424bc22b8fd472832e16509883f619d097830c0c20005d1dbc32f17bcb1851d25b11387b43751868a804721c40ac03a410e0005d174630a16d8a984de239903474233a16c09b840a1a30a0834c0cc0005d10f92f99654a604c622d900073232f16509b03f219a09d03380de0005d0a6f310171cace4ff24c909077c35a17d8a384421aa0a303840ea0005d03e731396f8a964e023910587543501770a0841c19f09803140c4000 else 0x603d1c32e97e0b1452525f91507a836217f0a544401b70a283200c80006036a430c16b8a824d3237101874e34416c89d84141ab0a003640dc00060302230d96c0a844d923c105473c32b16409643f419309503200d600060299330f96fcaa64dd235103074834116b89d84281a709b834c0d600060231430d16b4a964e3239105074c33516689d040c19909c83480d2000601c7b319170caba50024e10b47783581770a1c43e1b00a683740e80006015fe30a16a4a884db236904074e33916e89f041e1a109d03200ca000600f8d304969ca8e4d2232100074233615f89803e418909583240d60006009013139710ab64f6240103477235117109cc3fe19a09903300ce0006002972ff1648a544ba2290fc872832916309944021a009783480d80005ffc033161734ac24f3240104c74a33e166897040019f09282e40b80005ff56f31416e0a924dc23a100c73e32e16109783e619009a83200ca0005feef630596acaa44f2241106075834416d89f442a1ac0a183580da0005fe88d3029674a6c4cc2348ffc73e32a16809ac41419d09d03580cc0005fe21431396e0aa44f124990b077434c1760a1442a1a40a0035c0d40005fdb8930f16aca884d72340ff873433316789c840219f09a833c0e40005fd5302f59624a504b42268fc470e31f15e89483dc190097833c0dc0005fce9a3191710ab24ed23b902874032f16689b43f61a50a2035c0ce0005fc81d30e16cca9a4e423c906475434717089cc406199099831c0c80005fc19730c96d4aa44f523f105873833b16709c84321b009e03680de0005fbb323029628a404b42278f9070e33616089a040819a09d03400c80005fb4873201750ab64f324810a879235d1770a384381ac0a083740dc0005fadee31a9748ad2500245909476434016909ec40e1a60a203780de0005fa75131b1744ac04ff24e90a477634e16e09dc40219e09c03640e80005fa0fa2f91644a564cc2338ff072e32915e09503d818909203100ca0005f9aa62f51618a4e4c222a0fb4714327162098040419809682fc0bc0005f942131016dca984de23a102476434c16b09f843e1ab0a403600c80005f8d963171700aa84ed24810c07823571790a3c4461b30a883a80e80005f87173099690a6c4dd235900474634016a89bc41819c0a203480e20005f80a530596a0a784df2380ff073833816409943f019209603200d20005f7a1c30916a8a784c7235101474834016889c04121a50a183540d80005f738831296f8aa44ed244907876a34416789b040218c09403140d20005f6d2b2f415f8a344bc2238f9c72432e162894c3dc192096831c0cc0005f669831416f8ab04ff241907c76e34417209c040619709c03540d80005f60133119710aaa4e6238102873833916c09ac3f419709a83400ce0005f599c30b16bca844e223c8fe072e33b17309d84421b40a683800e40005f533d2fe165ca584c62320ffc736338167098840019f09583380ce0005f4cbe30916bca9a4e523a101075834216b89d040a19809903300bc0005f463f30996d4a984ea240105074a33916389743ec19509a03340ce0005f3fd92fc1644a664d6236101c72232916389b03f619409302ec0b80005f39872f7960ca4a4be2308fd071e32415d89583e419609b032c0be0005f330630996b8a7e4d8237101473432e16109643da18b09383080be0005f2c503219758af050124890b477c35717a8a304461b30a283540d60005f25dd30b96f0a9a4e123b105c74233a16a09ec4281a409e03380d20005f1f3c31f976cad64fa244907076a35917409e041e1ba0a683700da0005f18fd2ec15dca264b62278fd073033316609743f018909203100ba0005f12833051680a764d223b104474c34016a89c44221a70a003480ce0005f0c0f3079688a8c4da23c101474c34216709ac3f218b09083040cc0005f059930916a0a6e4ca22e901071c33216889783e618a092831c0cc0005eff2330916b0a8e4e2238901c74834717509e44161a009f83440de0005ef8a130b16d8a9c4eb23c903875034116b09c440219909a03440c80005ef1f93201780ad050b24a108478c35717609e04181ae0a383640d00005eeb7a30596a8a744d1234900072a33016b89a44041a009b834c0c80005ee4e5314971cac64f824a906c75833d17089e840e19d09703380d20005ede6830416b0a784d323d103874633216409984001ab0a103680d20005ed7c031e1754ad44ff24810b47943601780a044281a709a83380da0005ed14530816b0a7c4d923a105074033816d09c440419b09a03480c80005ecab73119704a8a4da238901473432e16609803f0192098034c0c00005ec42831416f4aa24e823d905475634216f89b44161a30a003600d60005ebd973179708aa44e323f907475c341168098c4141a709d03340d20005eb6e13221760ada4fa24b907876034016d89bc41e1a109a83300c80005eb07530596cca924de233902874e33616909bc4221a009d03300cc0005eaa033089644a4c4ca2310fe873a32d16389a43ec19809903500c60005ea3843079674a5c4ca238103c75034017209dc4261b10a083880e0000) else (if i < 57 then 0x61dad7302965ca524c8233903074a33e16a89a43e21a009f03580d600061d43e31c9744aac4ea24110b478e35f1790a1043e1b80a403540d800061cddd3001634a6a4d122f900073232f16709703ea18008e03000c200061c74731896f8aa44ec242909c77634e17489f040a19809b832c0d000061c1042e7956ca044a02210f506da30414b08d03b217508b82cc0b200061ba89309169ca764dc2370ffc74434017489fc42c1ac0a183580be00061b40630696a0a764d2233100473233b169899840219e098832c0ca00061ad8931096f8abc50024b90c478834a16e89c84201ad09e03480c800061a6f4316970cac04e923b904c74433716889b041019b09d83580da00061a0713081698a884d523a101470e32515e89503f419109a83440e00006199fb3061694a6a4db239101c73c33215d898c3f019209603140c20006193633189720aaa4f6247909877034916f09d842e19e09b83580c8000618cef3039670a724d1235901873032c16589703f219509683140be0006186783019678a524cb2310fe872833316a09903f81a009d83440cc000617ffb31116dca924e623e9040756333164899c4101a50a3837c0de00061798c303165ca624c72310fdc71031c15b89483c618709503200ba0006173212fe166ca6a4d1235103073c33216b89ac3fa19409703440c4000616cdb2f11628a624bf2320fc871831d15709403e618d09683180c000061664631296dca9e4de23c903075834017089d44201a90a2836c0dc000615fdd3011628a564c522a0fd071232416089803da18a08c02d80b80006159912ed95e8a2c4b42278fb471231f15b09583f219c09a03380c800061531c31216f0a9a4e5242107476c34b17289f44241a70a003340bc000614c9c30e96fcac04f924810b478034c1760a0c42a1a009f83580b600061461930c16c4a704d623c906476234716d09b43fe19809c03200d0000613f643261790aee4fa248908077c35617709f04181a309f03300ca00061392a2ed15c8a1a4b222a0fb06fc30d15509203c017f08b82d40ba0006132da2f61644a684be22a0fb470a33116109603e619709a83300cc000612c4a3159724ac84f824190547743541708a004341a809c83500d40006125d930816d4aac4f124790ac7823541798a404301ac0a083480d2000611f5f30f9704a9e4e323e106075a33816909bc3ec19209083180be0006118d631116fcaa84ec243106476434016b09b042a1ae09e83780de0006112762fc1638a4c4bf235903c76c35317289f04221a80a483780d8000610c03307168ca8e4d72341008738339167098c3f819c09c03640c800061058a30c16b0a8e4d3236902072432815d09303fa19a096832c0cc00060ff1530b16a8a824dc238101074634917289c44241ae0a403740e400060f866322975cae851225190f079c36b1808a504361ac09e834c0e200060f2172f31608a224b52270fb871232f16309703de19109582f80b600060eb7d31a9730ab24f0249108477c3531730a084361b00a5839c0f200060e4f23151704a984e8243107876e34e17109f041c1a70a203440d600060de872fe1640a4e4bb22f8fcc71c32c16409a440819c09903300c400060d80e3081690a804d02368ff471e32115a89443ca17d08c82cc0a000060d19d2fe9640a5c4cc2310fe471632816009903e418a09283040b800060cb352ff9660a6a4db22e900874633516889c040819f09f03580b600060c48e3171720ab64f324310607563441710a1041e19b09c03680da00060be322fd9628a484b42288fd472633516689903f018709002e00c600060b79331c9730ac44f724810bc79a35b17389bc41c1a309a83300d000060b12230596dca9c4ea242108c76e34d1748a104201b90a903980da00060aa8e3159734acc4f1243107476834916f8a0c4381a109a83280c400060a4282fd165ca464c322f0fc470e32416389603e018b08e831c0c2000609dbf3019664a644db23a904874434217089d0412192094831c0d80006097672f71638a524b82278fb870232715d89743f819809b83600dc0006090e830816d0a8e4d923d103875a34216d09cc4161a609a83380d6000608a5f3101714aaa4f6246907477434816f09f442a1b60a083580d00006083bd31d1734ad44f2241104075633f16b89b83f01a009883180be000607d45306967ca6e4d2235102473e33d16609903ec18e09883240da0006076f72ef15f4a3a4ac2218f6c6d830c15709343d418209083180ba0006070a62f19614a424b92258fb470e31e15d09603d4180093832c0d0000606a3f2ff1658a7a4d8237904474c34a1708a1042e1aa0a703700de0006063cb3091698a6c4d5237902875a34116b89c842019d09903200d8000605d613011638a424c422b0fb070e32015d095c3dc18b096030c0c20006057012fa9648a664d723d103c74833e16b896c3e619809a83280c80006050ab2f7160ca1c4a22208f586ee31115d09243ca19209883480d2000604a443039698a844da2391020732322162098840219d09c83400d00006043e02fd164ca644c522e0fec746334166099440219809e83340d0000 else 0x6378a930916a8a844d2236904073a33416889a83ec192094832c0be0006372532f79610a384bf22f0fc871e32e16689c841a1a009f036c0cc000636bce30c96a4a8a4df239103072e33916909a041219b09683000ca00063653a31016cca964e2238901c74e33a17089d84321b60a903880de000635ed92fa9660a784de23c104474e34116e09cc4281ae0a1036c0e400063587e3001654a6e4d423b102c76434417089e042a1ae0a1836c0dc00063520e303168ca6a4d823d904c76034d17109f042a1ac0a303640da000634b8c30a16a4a964df23c0fdc72032115f09703f619309703380d800063453f2f015cca0a4a521e8f746e630e15b09303ca18409302ec0bc000633ec130c169ca6e4dc23b904075833d16c89c041e1a109b032c0c4000633857300167ca684cf230900071a32315f099c40e19b09b03440b60006331df305165ca564c32328fd071e31815588e039c16108782e40ac000632b5e30896c0aa04e823c905076434717289e04201ab0a103880d60006324f13021694a704de23d104874033316709c03fe19a09b03480d6000631ec22e9959ca064a92218f5c6f031e15789203d418d09b03440d000063183730f96c8a864d5233102074e33e17109f44301ad0a283500e00006311d32fb9680a684c9230901072a33616009683ea18b09383000c4000630b403159704abc4ef241108875e34816f89a841a1a309b03480c40006304bd30a16c8a9c4eb240103874a33716689c040019209603400cc00062fe652f81630a464b72298fb471e32216089903e819d09c03380c800062f7df31096e8a8e4ea248908074c34916a89d04241a70a1034c0e000062f19b2f015e8a444b5225900071632716689703ec19b09683040b600062eb0131816f4a8e4e9242103474c34916f89c84121a70a003680da00062e47d31316fcaa84ee23b105076433a16709cc4161a209a03540cc00062de0d30516bca7e4db23a901873633d16d09d441a1a109d83500d800062d79f3061690a864de23f907476434c16e09bc4061a309c83480c400062d1472fd1614a3c4bd22a0fc471431f15e09583e819509983240be00062cadf2fe1658a4e4cd23a100c75033816709a44161a209d832c0c800062c44a317170caa84f924890c878c35e1800a604501b209f03380d000062bdb531516fcacc4f8243909477234816d09ac40a19909983300bc00062b72a3131718aa84e323d102074c336162898840018808d83040be00062b08331d9750aca50924f90d479835817109e44241b609f033c0d400062aa222f9964ca524c4232900473632816289743f4195093033c0be00062a3af3079694a784d4233101874433b16689943f419d09c03340d0000629d18319172cac44eb23d102c75233f16709a43e8191093832c0ca0006296c22fd167ca644cb231901073633916589743de18108f832c0d60006290542fb168ca604c922d0fe872a34017289dc40e1aa0a583580c80006289ce31096b8a964df238902875834116d09903fa19509803300cc0006283702fd9634a564bd22c8ff873033516c09a841019a09b03440c6000627cdb3171710a944db2368fec72632b162897440018e09703440d800062767b2fb169ca864e4239102475a34116a09a041e19f09a03400c2000626fc93209748ad24fc24e10c079c36117c89ec4201a609e03500d00006269523041668a6a4c62300fd473433216889c44281a709c03440c80006262d930816b8a784d2236901074434116d89a83f819b097834c0be000625c5a30996bca8a4d623c103474e34b16e09c841a1a609e83240c20006255c0319974cade4fa24590b87843611790a1441c1a70a0836c0e2000624f6e2f2161ca444b92278f9070231d16009703ee19309402dc0ba0006248de31416fcaa44f724990d07a236117b8a2c4501c40af03900f400062426930716b0a984e623f903873032716609883f419009703380cc000623c033011670a684d823b103476034816d09b84081a009603080ca00062358130996aca884e923f108877634f16a89dc4221a509e03540e2000622f0c30796c8aae4f624a90a878c35d17e0a1843c1b90a483640da0006228d92e815c8a304ae21c8f5070031c15f893c3de18609783000c800062225d30916d4a944de23b903876233e16c09b44181a60a003580da000621bf23021654a704d0236104474c33c16a89c44081ab0a583780e00006215603161704aa24de2378ffc72833a16389c84181a109f03580cc000620ec73189704ace4fa24b10d079a3691808a204261a209903380d00006208742f495f4a164a82230fa470632016309b440219409383440d80006202282f81634a364bf2278fb470231115b094c3e018208f03000b000061fb803209748aca4fd25010d87a235d1788a304681c70a783940e000061f4e531c172cabc4fd246907879035f1798a044261a80a0836c0d400061ee6a309168ca844d823d104875834d1748a2443e1b10a803a00e200061e7fd30796b0a744d423c904075a34116d89cc4221ae09b83400bc00061e1473279780ad44ff258111c7b036817e0a5c4541ba0a203880d6000)) else (if i < 60 then (if i < 59 then 0x65161231f974caf651025591407cc38018b0a9846c1c40a903a40ec000650fc02fd9644a6c4d023a103875a34616d89a43f619909a832c0d600065090d31b1758ae250424b10c878835317209d041e1a009f03580ea00065028230e96b8a8e4d6235902074a33c16d09bc40a19f09d83380d800064fc182fd9638a664d12360fe472633716a09b84121a309d03340c400064f5aa30516cca884d02368ffc72233416589943fc19109e032c0ca00064ef652ef9608a244b22248f9472232315889443d018308f82c00b000064e8d73179740ac64f924790a476a35317409cc4181aa09b83300c600064e2712fa9664a764ca2358fd871c32716009583da18708d82f40b800064dbd73159710aa84ef244908c77634b17509f44221a609a832c0c800064d5792fe1664a3e4b82280fbc71c33116589d841a1a909e83440d800064cf003031678a6e4da23b104c75233b16a89d44121a009c83340ca00064c87d30f16d4a8e4db239902c74633e1718a044341b20a283600da00064c1de31c1760ace4fc24b10ac7803571798a1043a1ac09d03500de00064bb8e2f49608a3a4b522c8fc872033016509a040419309783300cc00064b51c30816b8a7c4db23d902473633316b89a440819609682f40ca00064ae8731816f0aa64f724b90b07843551720a1c41c1ab09f03600d800064a8113089694a804d6239100c746334167099c40619f09b03300d400064a1ab3009654a544b92280fa06fc32715e896c3e618808f02f00c0000649b3a30a96e0aa44ec241906875633616689a03fe1a30a1834c0dc0006494ce300967ca564c9235902074a34217289f041819d09e83580c4000648e7c2f39600a3a4b622c0fa8706322162894c3e2192098832c0c40006487f131016dcaa24f124510a47663421740a084301ab0a4833c0d000064817a30a96c4a8c4ce2350fe873633316c09a8404197098831c0c0000647b1b2fa9660a864d723e101873233316789b840c1a50a083500c600064748e3139704acc4fa244906877234e1740a0841e1a209e037c0da000646e1830896a4a764dd235101c74833a16489883e819a098030c0b60006467aa30816aca984db23c904876234616e89e440e19909e035c0d40006461382fe1634a4e4bc2280fb871032816489503e819009183000ca000645aef2ef95d0a0c4a82258fb070c32a15e89903f019709903440dc000645450320174cad24f7246909076234b17389fc43a1b70a483640da000644dc230f96e4a924e7241107876034a16c09b841819909d83280d600064474a3091694a8a4db239904474033016609cc4101ae0a603700de0006440d83029640a5a4c522f901074a33516b89d041a19f09d832c0c0000643a5730b16b0a8c4e123c104c76034f1748a0c44a1bb0a583580e40006433db30c16b0aa24dc23e103c76033f16489c840619c09d03200c2000642d6930996e8abc4f023f907878a35a1738a2442c1ad0a183700de0006426fe302168ca784e823e105074a33b16b09ac40019b09d83480cc00064208e3059664a5c4c82300fd8736328161097c40019b09d83300da000641a0e30916a0a824cf2330ff873433b16e09d442219f0a003580e00006413a3302166ca744ce2360fdc72231d162095c3de18508f832c0c6000640d35303168ca784e323b105074433f16989a83f218d09383200cc0006406da2fd1624a404c6230101872032615e099040819209483240c80006400712fe9670a5a4c42308fdc71232516789943fe19409a03680f400063f9a333197d8b2653225f91207c037a1848a244261aa09803180c200063f32130916a0a7c4d4237904475433e16a89b041c1ab0a503840ee00063ecbc2ff1654a644c62310ff873233216989e440a19f09c83380d200063e6692f69620a5a4bf232100872c32915c09483cc18909a03380d600063e0042fc1640a3a4c122a8fa8708326163098440419409303180de00063d98d3099680a6c4d8239102074834116c89d04241b009f03440c600063d3632e39570a0049f2230f6c6fe32315f09583bc18308a83000b200063cce43081690a7a4df23d106075c34b17409dc4281a609f83480d800063c68a2fb1624a3e4c422f0ff872832f162897c3e018a09703480c800063c00730e96e8aae4e6241107475e35117289e841a19a09703300c800063b97631616ecaa04ef242906076035017389f04221a209e834c0d600063b2fb30a16a0a7c4d3233100873833a16189783f219b09983600d800063ac6031396f4a904cb239905876434b16e89bc3f419809783140c200063a5fb2fc1668a4a4be22d8fe473632f15f09683f019909f033c0c2000639f88304168ca784d3234100c73a33816a09a040019d09c03280c80006398f53131704ac44fe244107474a338163098840a1a409903100d800063926f30b96d4aa04e7243905c74233c16989c84301a709a83300cc000638bf230996a8a904ec23d905075c339169096c3f41970a203880e00006385882fc9654a6a4d12358fec72232516709984101a009d834c0de000637f1a3011650a6c4c8233100073033916909b840c1a609f03540ce000 else 0x66b3c730d96b0a924dd23e908077434616a09d041e19c09903180b800066ad34314171caae4fa24a90947803601778a084241aa0a103680d400066a6c33021658a5e4d02378ff0742340164098840019b09783300d000066a0782f8162ca564ce235101474032d166899c41419d09583380c60006699d531d1744ade50224d90c07ac37217e0a6c4501b50a283380d200066933731d1778ada50125210c479236017b0a2c44c1b40a2835c0ce000668cb930b96b4a744d52328fcc74033215e09803e218a09903540d600066865c3021664a764d9238902c74c34216909b040819909703080b2000667ffe3009638a444cd234902c76633916c09bc3fe19d09b832c0cc00066799d3039670a7c4d9239906076234516b09bc40619f09e03440d600066731b308169ca6a4cd2348ff872633516909a440c19c09c035c0ce000666cbb302169ca824e4239100c73c3501768a0c4441bc0a903780ee00066660932b17a0af450e25110dc79a3691750a3c4541b30a483440de000665f9130616a4a984e7244907077e35117189d84241a50a2034c0de0006659322fd9654a524c22310fbc72432d16609883e618d09403380ca0006652d22fc9610a3a4c22300fdc72233216509a04121a609903400d2000664c423151728abc4f524890b078234f17409d440819f0a083600da0006645e13001684a664ca2328fd871c31b15f09583cc18309083180be000663f7e3019688a7c4d1237102c76034516e09e84021a009d03280e20006639143049698a824ce237903c73c32d15f097c3fa18608f03100c20006632b22fd1648a564ca239900874234016709a03f419c09e83500da000662c3430a16d8aaa4ee241104c76034416f09d841019a09702f40b80006625ab31296e8ab04df23e104c74a33b16889c841e19e09b033c0da000661f572f71624a5a4c522f0fd472432715f896c3da18609082dc0c40006618be31296fcaa44e623f106c77234116d09e04221ac09e83600d000066124f304967ca684c622f0fe474633e16b89b84061a609e834c0ca000660bde3001644a684d023a902874e33b16c09dc4001a209c03300be0006605872f79620a3c4ca22c0ff872a32a160096c3dc18b09483140c600065ff0b30f16e4aaa4e5241904c75234516809983f619909b834c0c400065f89030596b0a744cd2310ff071c324163897c40819709603480ce00065f2292fe9648a524bf22c0fc872632316309803e418509103140be00065eb9b31116dca944e7241104874233d16b09ac40019d09583240cc00065e50e31196ecaa04f424c909c76c34116a89903e018b097833c0d000065dea230696a4a7e4d822f0fdc732333167894c3da17508f02f40a600065d81a31216d8a9c4ef242907477a34d17009fc41619d09e03540da00065d1ac2fe162ca524bf22e0fc071232215e09743e618b093830c0d000065cb40305168ca7a4d72330ff472a33116589e440c1aa09f03680da00065c4d5304168ca744d723c103c740340166099c40419609783280c200065be772fd1630a5e4cd231900873633c16b89b43fe1a209d03700da00065b81c2fb1660a6c4cb2319008728336168899c3f619b09c83400bc00065b1a530a16c8a8e4e123f101874634716a89ac40a19c09f83500d800065ab4b2f495f8a184ad2280fbc71232816589a841419e09a83280c000065a4b131d1740ab84f224c109878e35e17709dc42219e09c03500d6000659e4f2fb9620a524ce2320fdc73433c16909c840219c09803040c00006597b231f1710ab04f0244907075a34116e09c43fa19d09583100b40006591652f195d4a284b022c8fd070031a15b09343ca182090030c0be000658aba31c9748ac84f324e10e478035917709f442019b09a837c0da0006584582f71634a5a4d4238901c73032f15d89843de190097834c0d8000657e022f59614a304b922d0fd471231815909203d818609282fc0c800065777c31496ecab64f7242906473a34116b89e442a1b20a2035c0e400065710030896a4a724d4237901c73032d16889a040019c0a103540dc000656a7430e96f0aba4ee23c102875434517089f842019e09c83280c80006563ed30d9700aa44e9240904076c34c1760a144301ab0a083540d2000655d76309968ca784dc2330ff470c32116209583f419309a03300ca0006557142f9163ca604c7236102c73c33716a09b041c1ab0a0037c0e000065509f307167ca5c4c722c8fd471833216409603d819309983340ea000654a2a3051684a6c4d523b904474e34616f89d84241ac0a003680ce0006543c52fe966ca6a4d8237902875a34316589843fe19c09d03600d8000653d5b3029688a724cf234102873833a16a89983e818d09683240d60006536c7316172cad04f3249107076234c16f89d84261a30a203580d600065304e30a969ca8c4d9235900c73833616809c04121ab0a4036c0de0006529d430d96a8a744d82380ff473e33c16609ac40e19709483240c400065235530d168ca7a4ce22e8fc471632a16609a43e4182092830c0bc000651cb231d1734ac64f2240907076e34d1710a0c4281a80a1039c0f6000) else (if i < 61 then 0x68501930b169ca804c7231100874033a16a89c840819b09c83440c00006849a6304168ca804df240902872e330164897c3fe19c09e03600dc0006842fc3201744ac64f524410987723531740a184201a30a183580b6000683c893059690a7e4d4235103474033c16809b041419f09b03140c20006836202fe9668a704c422e0ff071433616989c84021a109e83580e6000682fac30a96c4a944ec23e905075034416e09b040819409803540d600068293a3009644a5a4d12340ff074233f16889904001a80a003380d60006822c83041688a764d7239901474032416109643e219809a03300b4000681c5f3001678a704c522d8ff072032d16889c441e1ab0a583780e000068160a2f61624a384c02288fb871a32e167099c3f219209383380da000680f8230f96ccaa84ee243106c75234217189f84101a50a103640e000068090130f96cca8c4da232100c73433c17009d84141a70a2837c0ea00068029f2fd9654a7a4d2235900073633d16909a84101aa09b03500de00067fc103141720aae4ef24c10a477c35917a8a4846a1c30ac038c0ec00067f5b92f4160ca4c4c82300fd070632516509944241a70a183480d600067ef4c304967ca644c622a8fac6fe311158091c3da18308b82f40c600067e8ce30996a4a824d12358fdc72633816809b04061a009f03680d800067e24231216d8a9a4e423c104c74c33e16c09803fa19009703280d600067dbca30b968ca684ca2341000726330166898c40e1a709f03780e200067d55f3011650a5e4d323e101c75034117109f441219e09f03440d200067cef93021678a6e4d923a102c75034416b89c03fa19b09683200c800067c85a31b1730aa44ea241908c76034a16f09d04181a709f83480d000067c1eb2fc9650a684d02370fec73e34416f89c841c1a209c03580ca00067bb852fe9654a824d6239102c74c34216c09d84301b50a1836c0d400067b5432e915bca304b02280f8c70230b15a893c3d818809383040c200067aecf3039668a5a4c622e0fc872632515c09603f0190098832c0c200067a84e30696c8aa44eb23d105c75634d17309cc42219f0a2037c0e600067a2062f39608a3e4b322b0fd472232815d097840819f09b83100cc000679ba62fd166ca684d2239101c73432f16409a441019909703380cc00067953230696b4a984e023a102075433c16f09b440219c0a0835c0ee000678eb031116d4a944e323a106075033d16b89d84261b60a303640e00006788622f31608a3c4b92238fa070e316159891c3cc18509002e40b60006782152f79634a3e4bb22c0fd071632616209803ea18e09583280c4000677b9d3051688a7e4cf234100073a33316689c440c19b09c03400b800067752c30d16bca884e123b104874834416e89cc40a1a109b83080de000676edc2f91614a2c4b12250fb871e32d163896c3f81a109a832c0b600067684d31296dcab44ea240908c7783521748a1c4301ad09e832c0b200067620f2e995cca164a22208f886fe31f15b09383f419809b03200c4000675ba63011664a744d823b1030734332167899c41419f09a83540c600067553e300167ca664cc2330ff071e32515f09803ee19509783180bc000674e933209770aca50224d10cc78a35b1778a184301ad0a1037c0ce0006748322fb9630a4c4bc22f8fd471632916389bc4061a80a183600e00006741c12fe9614a464c12318ffc73c34516e89b441019e09c83480d0000673b4730516d4a964dd239105476834f17289dc40e19809883600d20006734d53039668a744cd235900073633916689a43f819709582f40b8000672e6330d16c4a8a4e023e104475434d17309f04381aa0a383580de0006728012fe9660a704d9238900c71a32e16609983f818709383100c000067218130c96e4aac4ef23d904874233e16a89dc42a1a50a303700dc000671aef3191740ade50624a10b077434b1740a004381b00a303800d800067146c30f96dcaac4ee24a90a479235017189dc40619a09203240ca000670df6308168ca924eb242109075a33f16989a03fe19409583080ac0006707a22ee95e8a184a22200fb470c32215e89603ee19509183100d000067014c2f81614a4c4c7234902474833c16a09c84161a70a383600e800066fabf30f16c8a9e4ed241904874233e16609903f418d09583240d800066f4572fd9670a604cb2318fec74433916b09803e2191099033c0c800066edf1301966ca704d12318fcc71632115e095c3ee19609a83280e800066e78530a9688a884d923a901474433e16b09b03f019109983300dc00066e0da3219770aea50b247907875a344169899c3f819c09b03380c000066da64307968ca744d123a103c73633816389904181a609903100c800066d4112f59604a3c4bb231100074033f16a09a040219a09983300d800066cd9930e16d0aae4ef242906476633916b89c041019909483280ca00066c70e318971caa44eb23f905476c34e1760a0c42a1a609c835c0cc00066c0a4300167ca784d52391010724333161898c404198096031c0c600066ba482f61604a404bd2260f8c70832116009583d6189099830c0ca000 else 0x68639200000000000000000000000000000000040219b09403300c8000685d1730796a0a984db23a903473433916889bc40c19a09b830c0ba00068569e30d96d8a984ea24710a079436717b0a3c4441b70a803740da000))))))

private def checkpoint (i : ℕ) : ℕ :=
  let word := (packet (i/1024) >>> (232*((i%1024)/16))) % (2^232)
  (word >>> 208) + ((word >>> (13*(i%16))) % 8192)

private def raw (j : ℕ) : ℕ := fromBlocks checkpoint (fun r => quick (number r)) j

private def small (n : ℕ) : ℕ := if 5≤n then 3 else if 3≤n then 2 else if 2≤n then 1 else 0
def fast (n : ℕ) : ℕ := raw (index n) + small n

private def step (i : ℕ) := checkpoint (i+1) == checkpoint i + tally (fun r => quick (number r)) (512*i) 512

private def valid (lo len : ℕ) : Prop := (List.range' lo len).all step = true
private theorem glue {lo a b : ℕ} (left : valid lo a) (right : valid (lo+a) b) : valid lo (a+b) := by
  unfold valid at *
  rw [←List.range'_append_1,List.all_append,left,right]
  rfl


private theorem halve (lo n : ℕ) (h : valid lo (n/2))
    (k : valid (lo+n/2) (n-n/2)) : valid lo n := by
  simpa only [show n/2+(n-n/2)=n by omega] using glue h k

private def covered (lo hi : ℕ) : Prop :=
  ∀ j, lo≤j → j<hi → step j=true

private theorem checked {lo hi : ℕ} (h : valid lo (hi-lo)) : covered lo hi := by
  intro j lower upper
  exact List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨lower,by omega⟩)

private theorem joinCoverage {lo mid hi : ℕ} (l : covered lo mid) (r : covered mid hi) :
    covered lo hi := by
  intro j lower upper
  by_cases isLeft : j < mid
  · exact l j lower isLeft
  · exact r j (by omega) upper



private theorem b48950 : covered 48950 49072 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b49072 : covered 49072 49194 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b49194 : covered 49194 49316 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b49316 : covered 49316 49438 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b49438 : covered 49438 49560 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b49560 : covered 49560 49682 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b49682 : covered 49682 49804 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b49804 : covered 49804 49926 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b49926 : covered 49926 50048 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b50048 : covered 50048 50170 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b50170 : covered 50170 50292 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b50292 : covered 50292 50414 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b50414 : covered 50414 50536 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b50536 : covered 50536 50658 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b50658 : covered 50658 50781 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b50781 : covered 50781 50903 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b50903 : covered 50903 51025 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b51025 : covered 51025 51147 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b51147 : covered 51147 51269 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b51269 : covered 51269 51391 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b51391 : covered 51391 51513 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b51513 : covered 51513 51635 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b51635 : covered 51635 51757 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b51757 : covered 51757 51879 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b51879 : covered 51879 52001 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b52001 : covered 52001 52123 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b52123 : covered 52123 52245 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b52245 : covered 52245 52367 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b52367 : covered 52367 52489 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b52489 : covered 52489 52611 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b52611 : covered 52611 52734 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b52734 : covered 52734 52856 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b52856 : covered 52856 52978 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b52978 : covered 52978 53100 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b53100 : covered 53100 53222 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b53222 : covered 53222 53344 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b53344 : covered 53344 53466 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b53466 : covered 53466 53588 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b53588 : covered 53588 53711 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b53711 : covered 53711 53833 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b53833 : covered 53833 53955 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b53955 : covered 53955 54077 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b54077 : covered 54077 54199 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b54199 : covered 54199 54321 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b54321 : covered 54321 54443 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b54443 : covered 54443 54565 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b54565 : covered 54565 54688 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b54688 : covered 54688 54810 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b54810 : covered 54810 54932 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b54932 : covered 54932 55054 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b55054 : covered 55054 55176 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b55176 : covered 55176 55298 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b55298 : covered 55298 55420 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b55420 : covered 55420 55542 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b55542 : covered 55542 55664 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b55664 : covered 55664 55786 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b55786 : covered 55786 55908 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b55908 : covered 55908 56030 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b56030 : covered 56030 56152 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b56152 : covered 56152 56274 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b56274 : covered 56274 56396 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b56396 : covered 56396 56518 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b56518 : covered 56518 56641 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b56641 : covered 56641 56763 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b56763 : covered 56763 56885 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b56885 : covered 56885 57007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b57007 : covered 57007 57129 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b57129 : covered 57129 57251 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b57251 : covered 57251 57373 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b57373 : covered 57373 57495 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b57495 : covered 57495 57617 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b57617 : covered 57617 57739 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b57739 : covered 57739 57861 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b57861 : covered 57861 57983 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b57983 : covered 57983 58105 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b58105 : covered 58105 58227 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b58227 : covered 58227 58349 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b58349 : covered 58349 58471 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b58471 : covered 58471 58594 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b58594 : covered 58594 58716 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b58716 : covered 58716 58838 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b58838 : covered 58838 58960 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b58960 : covered 58960 59082 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b59082 : covered 59082 59204 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b59204 : covered 59204 59326 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b59326 : covered 59326 59448 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b59448 : covered 59448 59570 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b59570 : covered 59570 59692 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b59692 : covered 59692 59814 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b59814 : covered 59814 59936 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b59936 : covered 59936 60058 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b60058 : covered 60058 60180 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b60180 : covered 60180 60302 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b60302 : covered 60302 60424 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b60424 : covered 60424 60547 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b60547 : covered 60547 60669 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b60669 : covered 60669 60791 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b60791 : covered 60791 60913 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b60913 : covered 60913 61035 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b61035 : covered 61035 61157 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b61157 : covered 61157 61279 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b61279 : covered 61279 61401 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b61401 : covered 61401 61524 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b61524 : covered 61524 61646 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b61646 : covered 61646 61768 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b61768 : covered 61768 61890 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b61890 : covered 61890 62012 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b62012 : covered 62012 62134 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b62134 : covered 62134 62256 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b62256 : covered 62256 62378 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b62378 : covered 62378 62501 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 48950 62501 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b48950 (joinCoverage b49072 b49194)) (joinCoverage b49316 (joinCoverage b49438 b49560))) (joinCoverage (joinCoverage b49682 (joinCoverage b49804 b49926)) (joinCoverage (joinCoverage b50048 b50170) (joinCoverage b50292 b50414)))) (joinCoverage (joinCoverage (joinCoverage b50536 (joinCoverage b50658 b50781)) (joinCoverage (joinCoverage b50903 b51025) (joinCoverage b51147 b51269))) (joinCoverage (joinCoverage b51391 (joinCoverage b51513 b51635)) (joinCoverage (joinCoverage b51757 b51879) (joinCoverage b52001 b52123))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b52245 (joinCoverage b52367 b52489)) (joinCoverage (joinCoverage b52611 b52734) (joinCoverage b52856 b52978))) (joinCoverage (joinCoverage b53100 (joinCoverage b53222 b53344)) (joinCoverage (joinCoverage b53466 b53588) (joinCoverage b53711 b53833)))) (joinCoverage (joinCoverage (joinCoverage b53955 (joinCoverage b54077 b54199)) (joinCoverage (joinCoverage b54321 b54443) (joinCoverage b54565 b54688))) (joinCoverage (joinCoverage b54810 (joinCoverage b54932 b55054)) (joinCoverage (joinCoverage b55176 b55298) (joinCoverage b55420 b55542)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b55664 (joinCoverage b55786 b55908)) (joinCoverage (joinCoverage b56030 b56152) (joinCoverage b56274 b56396))) (joinCoverage (joinCoverage b56518 (joinCoverage b56641 b56763)) (joinCoverage (joinCoverage b56885 b57007) (joinCoverage b57129 b57251)))) (joinCoverage (joinCoverage (joinCoverage b57373 (joinCoverage b57495 b57617)) (joinCoverage (joinCoverage b57739 b57861) (joinCoverage b57983 b58105))) (joinCoverage (joinCoverage b58227 (joinCoverage b58349 b58471)) (joinCoverage (joinCoverage b58594 b58716) (joinCoverage b58838 b58960))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b59082 (joinCoverage b59204 b59326)) (joinCoverage (joinCoverage b59448 b59570) (joinCoverage b59692 b59814))) (joinCoverage (joinCoverage b59936 (joinCoverage b60058 b60180)) (joinCoverage (joinCoverage b60302 b60424) (joinCoverage b60547 b60669)))) (joinCoverage (joinCoverage (joinCoverage b60791 (joinCoverage b60913 b61035)) (joinCoverage (joinCoverage b61157 b61279) (joinCoverage b61401 b61524))) (joinCoverage (joinCoverage b61646 (joinCoverage b61768 b61890)) (joinCoverage (joinCoverage b62012 b62134) (joinCoverage b62256 b62378)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 48950 ≤ index 94085731/512 := by decide +kernel
private theorem starting_value : fast 94085731=5439846 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 94085731=5439846) (n : ℕ) (low : 94085731≤n) (bound : n≤120000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=94085731
    · rw [first,anchor]
      exact starting_value
    · have past : 94085731≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤120000000 by omega)
        have within : index n / 512 < 62501 := by omega
        have lower : index 94085731/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
        have chk := beq_iff_eq.mp (allrows _ (starting_block.trans lower) within)
        change checkpoint (index n/512+1) = checkpoint (index n/512) +
          tally (fun j => quick (number j)) (512*(index n/512)) 512 at chk
        have h := fromBlocks_succ checkpoint (fun j => quick (number j)) (index n) chk
        change raw (index n+1) = raw (index n) + (if quick (number (index n)) then 1 else 0) at h
        rw [whose] at h
        simp only [fast,e,h,unchanged]
        by_cases hp : (n+1).Prime
        · simp [hp,(quick_ok bound).mpr hp,Nat.add_right_comm]
        · simp [hp,mt (quick_ok bound).mp hp]
def prime (n : ℕ) : Bool := quick n

theorem prime_ok (n : ℕ) (hn : n≤120000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ94085731To120000000
