import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ195000000To220000000

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




private def radical : ℕ := 0x66a3ad740d8fc3bce4f9e4535ae0bf5237fc96b9bb83ed53e3fdbd167259a3a6085d1f952fdfcc2d5d7f998f6d19f12e6fe693de44a91be64c03090d85a40d7135edac22bb54db31b05bd76ac12f469d20e3e16c1928fff8444f5e1ee688f2d67871279ee72744d5bc72b1ae49f7722f0b4d13a0347a6a490eb7cb753ab65a0654ec25325b3c845b058389ddb91aea127312feeecffce0484ae0494ec4d9a0aad521cd7acb2acb703da20d4eaee3475cc9f5e98df89678beb9a3b7477cabcd7dfe45d8c1debacec9476f3318476ea128101e507ca5c98c72638dc3f8092372be4e716eec5d2874d73e7fc270e8cfa3f2750e7354e51db8f18d4e33ce8abdffe74145e08c393ee3a63ff64ea4cd0ce6547b393a722278bffd6fc79cc87ac070a5315e6e8ca79a63e5eca2b2059619ed36b7f9f693e2357b6aa7b31162777afca055e598e13bfdb7227823f3c6d8b44743917cf04b8deb9ca8613f52a97da2144791b2f1b6c5396b7f271eda62ac3b139165d6221e5b3a94bdff8b0496b56891718afca51ec280fc0ba19d558e6add28ec19e6f416e68ec2fe3d660b341971b1a9e35cab108da030442dc4dbd46132b369b7501a9a2b53cae26aeba0277953a1679013618f8acd5dccec0080041f4c2305d12d910e6c4a46e8a91ff926bd461b87d966f88b3fc4ffe77cbb02edd8b1992e4bd11bdcf42fbc95d3bc1f9fdaa90b724a5bf5d8a2e86e882252e26aebb1b91078bac39a36b967db45435b7ffdf5684ca04fe1201056193d36d6c9aca3b3c03f76f73efe4f859f08646f11041f6ff6e98a82c3d88115dffa3c82f1546d89636d1c1814a77ed86da4d75a914c74d4e07245b3ed8364c35aa0f130d5c7504059fdb0518467ae463c3ed2b240d6e9cf6d4ec547b410014ba8e3755660bd8a4273812d01e1f83c339c70dea533b54cadfbade986017da0c65ac3e89ad532a29abe6667458a4aeb0c21ecc6983b8c6406c16a470102aeee674ffcf0e29b5f44ec7af3415fceaf56412fb1e8b79f5d2c3300a24c1c534d32432575c4aed3b30f0aece3ec3a80d0c1c7f0fa78ea89404cf67252d24693ab56be139fe50b5c1eaea63029fc70ad8ef2586fb3fae5442a1d8fb9da330ed37795f9f8d6305e4d77da4c8bf397bbba5dcd72598ba7161e5f94024fa7d66414a65928bc2f19ac1f78c7782afe62ce886f4623afcd87506048ab131ee382f9891d02c5303b7435fcb81f8cdd8cf8d5cae07df4ae6c084f3b9dc9a7eab2f7f48e5cdfbf18e2e8dfed12bfaf1af7772151dcad117498c9d00ed769cd44d524f029ff293540b3ab26b1fb471c413529cd91d9392048fff5a3f550b7645b5ab1558359565107687faa97c69796125dc2f46cf31b509e281a42db633d7223ea6340e9d794462422b9748cbdf49f924e1ed7a253064fae1ea7b47ba3725c6374053f1ff76ef9ed43b74af89bc0edd28c21032b5994e4c02b3a86122cd1d5f0b49309f2a3b9dc2dc2fccb2fa297e2685e3e3a6d526b531e0a3e96690c36af5e655b801ddda7675fa383251bf505418f4df74312186e877e42d70e7e4dadd26978725a7e0b19698c4c506348a627cc0f7484c1af33f8313219f007a1c0fb2449a9d7ab356bdc3a3f1766afd4c2ecab54bb7a1c3e822fe22c4b91416093fb098edb54fa9a9eb9f5bd213af9c835ba31b1d6cb1de918d19132920d7d1e1e82e0681ae73ed82e6ba1d2f9bbbcbd61d4214d26bddd756a4c49265b978a324136f3b648640f44b4c44b8f2864b3ca3a99fbede4bd07ebf831f6f6f3e4642e34c8e2bff6df1a094a6537077e53166a78e8f952a9ee431756af21db419e4cdf19c304f6cdfd15df450e5c2348db1f6d6a8044c021ccf6fee0a8c5e95c7fe39382b4912bdc5fd9125337bf3569e5cec9d9991a42eb3b498ef5e72524d62a74803fae5ba02e52395367aa20ffe7864e7cc2167738d6eb49bf176a0dd4ec9e5d951af07669390b55fe456a537a6812770571a45a2a9a542a5aaf520011c8f9fff19857d314ca853f56e77d0efa56ae48f0734311d13d6a9d1f4e0f1c7763486f1a8ac2b6e6aad23599f8e41b77ef09b6a396e677d0d4cef971c6cfa896c5c7a3daff7a63cdab11d29fe4b216f1b732313e365be0d3537f39b8b9f4a6aa5631ebe0ec4e1b803f2c981304b9c1e095274da526d1c5dd5f106602e22063ff3f801a6e71fafdf93fe7064bc5929cb5f0319530cbcdac55d949349df79042a05f3198593f2b27f0bed5361a94de338a1115e0bfd6cad976e3dcd49db5e202c51bf72b8b20c4949d67e2ee775a90bf067f0466c2d9c58fbc116e9f896e31947e938aaad8704121d97869e92fd7320e22103a54f525accf4147f9316934abe65bfee51433d6ba168fe28e22d216e868f23395bea932c18a63065bc3549f0ae9ec715fffc866cd4914ca9028f067920b0d191d22c1cc27e80c790e40378552902899abac0db389d3580e0a2076bb3565358725512af8c1958d092cfa6541094c1e5e604bd341a3412d664649b7337bae8927266a0460d78365bf2a68ed837964fbe368fd1a3203d74d31d6ef4cb994df623e29c5cd967b844ce934d0e81b77846a8604dc5bd6f9cf0e68a4b6c4da7e30b8347c75cbdbbe7515c326e5c078fb1bc20f8b0c9962ff398884705b6b7890b22df2a540b6ab77a95f20700ecf1e79c53a859959189c9875d14506cf298b9b31fece7fc94040ab39109d31d0077d89f688f316df82647d9d3827b886f304818c8f519f961e488782528728b78c710d6496bdeba834bf3c9ae79fc206566ae41c454176606210323888b538eadf295b67ff2c9d07eb7f799d4b11ead0422726c54da73ce000ee04b37d8cb4274f94b28438f64e4deb5c5aea9ea66c20718e1ceaf0baefe040153d8acc7e3fb26ecc0ba4cb33df6054495ad04fa6c5733d1fac4f96e264a22d7bd6235474424ea7d74a6f997b0410f6d476b059b0b9dfd9c45453c16e851fc0a5a232fa69e76f7d57b7f582d88c5fbf226d901a35a8f5d19e62ec3ee6616c1ec41b75d322645c9348b00a1404ca7f893fd19b7966fa38238dd75ee14325cf421740f66dd8da804c532a534e9f633ca399fc7bb539bfde3c37343faa230e4bc5249b4e7787d8156a3944147794dd33c2e09b24d3a55d71ae4e11cf50492e310f1679877de62ec8d87d204119b6e876bd4c648fb833fcfe8fbfcea836976b861880dae17074558647373c630facd088b5e7af9603ea967a5281cb78f33148bffec5d0d681f950c7cacc822cb425315d18b7618b6535e63498b50993eabeb72c664cc1ca78911d3fd56e89a3e9d745fb87e7b77bbea8ad14770368ec2132ced4190b972db888fb8a50f3c4f45a12013fc73ed05f9f562e28e35c24f6c724ed8693335067f1d960157bdc6fe96ef5f4f06988687a1966d91e5871809d912a0040f2b945bb902c96e5bd8785cf877a08c12cab9d29f74b295602b51bc08bc42f9ae980e435a1067d2d5b24d5426716e2c0d5886c8712ecb4da60e6b1fe26bd3cb8d5734ab6eef49586eeb711e40fb209952baefd16034f315e7b784e8f7bd909877b4a60ed639eebb04db696844fa349ef58028a4ab648580cfa44f7acdc9d7455aeff592a8a3cc97e83b1bfc02096fc0fa088cb5dc0316e373e23a27681aa98271128fece30ce6ed7eb29217bf6c712715b68142fe329cd66c7b488d8465fd502e65ef46b9579deb1191c5221a8ff5d2

private def light (n : ℕ) : Bool :=
  if n≤121 then decide n.Prime else n.gcd 809429852527344373968162284544935082997082306309701607045776233628497660426640521713391773997910182738287074185078904956856663439318382745047716214841147650721760223072092160000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤14832) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 121 = 809429852527344373968162284544935082997082306309701607045776233628497660426640521713391773997910182738287074185078904956856663439318382745047716214841147650721760223072092160000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 121 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤14832 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 57 := by unfold smallValid; decide +kernel

private theorem sp57 : smallValid 57 58 := by unfold smallValid; decide +kernel

private theorem sp115 : smallValid 115 58 := by unfold smallValid; decide +kernel

private theorem sp173 : smallValid 173 58 := by unfold smallValid; decide +kernel

private theorem sp231 : smallValid 231 58 := by unfold smallValid; decide +kernel

private theorem sp289 : smallValid 289 58 := by unfold smallValid; decide +kernel

private theorem sp347 : smallValid 347 58 := by unfold smallValid; decide +kernel

private theorem sp405 : smallValid 405 58 := by unfold smallValid; decide +kernel

private theorem sp463 : smallValid 463 58 := by unfold smallValid; decide +kernel

private theorem sp521 : smallValid 521 58 := by unfold smallValid; decide +kernel

private theorem sp579 : smallValid 579 58 := by unfold smallValid; decide +kernel

private theorem sp637 : smallValid 637 58 := by unfold smallValid; decide +kernel

private theorem sp695 : smallValid 695 58 := by unfold smallValid; decide +kernel

private theorem sp753 : smallValid 753 58 := by unfold smallValid; decide +kernel

private theorem sp811 : smallValid 811 58 := by unfold smallValid; decide +kernel

private theorem sp869 : smallValid 869 58 := by unfold smallValid; decide +kernel

private theorem sp927 : smallValid 927 57 := by unfold smallValid; decide +kernel

private theorem sp984 : smallValid 984 58 := by unfold smallValid; decide +kernel

private theorem sp1042 : smallValid 1042 58 := by unfold smallValid; decide +kernel

private theorem sp1100 : smallValid 1100 58 := by unfold smallValid; decide +kernel

private theorem sp1158 : smallValid 1158 58 := by unfold smallValid; decide +kernel

private theorem sp1216 : smallValid 1216 58 := by unfold smallValid; decide +kernel

private theorem sp1274 : smallValid 1274 58 := by unfold smallValid; decide +kernel

private theorem sp1332 : smallValid 1332 58 := by unfold smallValid; decide +kernel

private theorem sp1390 : smallValid 1390 58 := by unfold smallValid; decide +kernel

private theorem sp1448 : smallValid 1448 58 := by unfold smallValid; decide +kernel

private theorem sp1506 : smallValid 1506 58 := by unfold smallValid; decide +kernel

private theorem sp1564 : smallValid 1564 58 := by unfold smallValid; decide +kernel

private theorem sp1622 : smallValid 1622 58 := by unfold smallValid; decide +kernel

private theorem sp1680 : smallValid 1680 58 := by unfold smallValid; decide +kernel

private theorem sp1738 : smallValid 1738 58 := by unfold smallValid; decide +kernel

private theorem sp1796 : smallValid 1796 58 := by unfold smallValid; decide +kernel

private theorem sp1854 : smallValid 1854 57 := by unfold smallValid; decide +kernel

private theorem sp1911 : smallValid 1911 58 := by unfold smallValid; decide +kernel

private theorem sp1969 : smallValid 1969 58 := by unfold smallValid; decide +kernel

private theorem sp2027 : smallValid 2027 58 := by unfold smallValid; decide +kernel

private theorem sp2085 : smallValid 2085 58 := by unfold smallValid; decide +kernel

private theorem sp2143 : smallValid 2143 58 := by unfold smallValid; decide +kernel

private theorem sp2201 : smallValid 2201 58 := by unfold smallValid; decide +kernel

private theorem sp2259 : smallValid 2259 58 := by unfold smallValid; decide +kernel

private theorem sp2317 : smallValid 2317 58 := by unfold smallValid; decide +kernel

private theorem sp2375 : smallValid 2375 58 := by unfold smallValid; decide +kernel

private theorem sp2433 : smallValid 2433 58 := by unfold smallValid; decide +kernel

private theorem sp2491 : smallValid 2491 58 := by unfold smallValid; decide +kernel

private theorem sp2549 : smallValid 2549 58 := by unfold smallValid; decide +kernel

private theorem sp2607 : smallValid 2607 58 := by unfold smallValid; decide +kernel

private theorem sp2665 : smallValid 2665 58 := by unfold smallValid; decide +kernel

private theorem sp2723 : smallValid 2723 58 := by unfold smallValid; decide +kernel

private theorem sp2781 : smallValid 2781 57 := by unfold smallValid; decide +kernel

private theorem sp2838 : smallValid 2838 58 := by unfold smallValid; decide +kernel

private theorem sp2896 : smallValid 2896 58 := by unfold smallValid; decide +kernel

private theorem sp2954 : smallValid 2954 58 := by unfold smallValid; decide +kernel

private theorem sp3012 : smallValid 3012 58 := by unfold smallValid; decide +kernel

private theorem sp3070 : smallValid 3070 58 := by unfold smallValid; decide +kernel

private theorem sp3128 : smallValid 3128 58 := by unfold smallValid; decide +kernel

private theorem sp3186 : smallValid 3186 58 := by unfold smallValid; decide +kernel

private theorem sp3244 : smallValid 3244 58 := by unfold smallValid; decide +kernel

private theorem sp3302 : smallValid 3302 58 := by unfold smallValid; decide +kernel

private theorem sp3360 : smallValid 3360 58 := by unfold smallValid; decide +kernel

private theorem sp3418 : smallValid 3418 58 := by unfold smallValid; decide +kernel

private theorem sp3476 : smallValid 3476 58 := by unfold smallValid; decide +kernel

private theorem sp3534 : smallValid 3534 58 := by unfold smallValid; decide +kernel

private theorem sp3592 : smallValid 3592 58 := by unfold smallValid; decide +kernel

private theorem sp3650 : smallValid 3650 58 := by unfold smallValid; decide +kernel

private theorem sp3708 : smallValid 3708 57 := by unfold smallValid; decide +kernel

private theorem sp3765 : smallValid 3765 58 := by unfold smallValid; decide +kernel

private theorem sp3823 : smallValid 3823 58 := by unfold smallValid; decide +kernel

private theorem sp3881 : smallValid 3881 58 := by unfold smallValid; decide +kernel

private theorem sp3939 : smallValid 3939 58 := by unfold smallValid; decide +kernel

private theorem sp3997 : smallValid 3997 58 := by unfold smallValid; decide +kernel

private theorem sp4055 : smallValid 4055 58 := by unfold smallValid; decide +kernel

private theorem sp4113 : smallValid 4113 58 := by unfold smallValid; decide +kernel

private theorem sp4171 : smallValid 4171 58 := by unfold smallValid; decide +kernel

private theorem sp4229 : smallValid 4229 58 := by unfold smallValid; decide +kernel

private theorem sp4287 : smallValid 4287 58 := by unfold smallValid; decide +kernel

private theorem sp4345 : smallValid 4345 58 := by unfold smallValid; decide +kernel

private theorem sp4403 : smallValid 4403 58 := by unfold smallValid; decide +kernel

private theorem sp4461 : smallValid 4461 58 := by unfold smallValid; decide +kernel

private theorem sp4519 : smallValid 4519 58 := by unfold smallValid; decide +kernel

private theorem sp4577 : smallValid 4577 58 := by unfold smallValid; decide +kernel

private theorem sp4635 : smallValid 4635 57 := by unfold smallValid; decide +kernel

private theorem sp4692 : smallValid 4692 58 := by unfold smallValid; decide +kernel

private theorem sp4750 : smallValid 4750 58 := by unfold smallValid; decide +kernel

private theorem sp4808 : smallValid 4808 58 := by unfold smallValid; decide +kernel

private theorem sp4866 : smallValid 4866 58 := by unfold smallValid; decide +kernel

private theorem sp4924 : smallValid 4924 58 := by unfold smallValid; decide +kernel

private theorem sp4982 : smallValid 4982 58 := by unfold smallValid; decide +kernel

private theorem sp5040 : smallValid 5040 58 := by unfold smallValid; decide +kernel

private theorem sp5098 : smallValid 5098 58 := by unfold smallValid; decide +kernel

private theorem sp5156 : smallValid 5156 58 := by unfold smallValid; decide +kernel

private theorem sp5214 : smallValid 5214 58 := by unfold smallValid; decide +kernel

private theorem sp5272 : smallValid 5272 58 := by unfold smallValid; decide +kernel

private theorem sp5330 : smallValid 5330 58 := by unfold smallValid; decide +kernel

private theorem sp5388 : smallValid 5388 58 := by unfold smallValid; decide +kernel

private theorem sp5446 : smallValid 5446 58 := by unfold smallValid; decide +kernel

private theorem sp5504 : smallValid 5504 58 := by unfold smallValid; decide +kernel

private theorem sp5562 : smallValid 5562 57 := by unfold smallValid; decide +kernel

private theorem sp5619 : smallValid 5619 58 := by unfold smallValid; decide +kernel

private theorem sp5677 : smallValid 5677 58 := by unfold smallValid; decide +kernel

private theorem sp5735 : smallValid 5735 58 := by unfold smallValid; decide +kernel

private theorem sp5793 : smallValid 5793 58 := by unfold smallValid; decide +kernel

private theorem sp5851 : smallValid 5851 58 := by unfold smallValid; decide +kernel

private theorem sp5909 : smallValid 5909 58 := by unfold smallValid; decide +kernel

private theorem sp5967 : smallValid 5967 58 := by unfold smallValid; decide +kernel

private theorem sp6025 : smallValid 6025 58 := by unfold smallValid; decide +kernel

private theorem sp6083 : smallValid 6083 58 := by unfold smallValid; decide +kernel

private theorem sp6141 : smallValid 6141 58 := by unfold smallValid; decide +kernel

private theorem sp6199 : smallValid 6199 58 := by unfold smallValid; decide +kernel

private theorem sp6257 : smallValid 6257 58 := by unfold smallValid; decide +kernel

private theorem sp6315 : smallValid 6315 58 := by unfold smallValid; decide +kernel

private theorem sp6373 : smallValid 6373 58 := by unfold smallValid; decide +kernel

private theorem sp6431 : smallValid 6431 58 := by unfold smallValid; decide +kernel

private theorem sp6489 : smallValid 6489 57 := by unfold smallValid; decide +kernel

private theorem sp6546 : smallValid 6546 58 := by unfold smallValid; decide +kernel

private theorem sp6604 : smallValid 6604 58 := by unfold smallValid; decide +kernel

private theorem sp6662 : smallValid 6662 58 := by unfold smallValid; decide +kernel

private theorem sp6720 : smallValid 6720 58 := by unfold smallValid; decide +kernel

private theorem sp6778 : smallValid 6778 58 := by unfold smallValid; decide +kernel

private theorem sp6836 : smallValid 6836 58 := by unfold smallValid; decide +kernel

private theorem sp6894 : smallValid 6894 58 := by unfold smallValid; decide +kernel

private theorem sp6952 : smallValid 6952 58 := by unfold smallValid; decide +kernel

private theorem sp7010 : smallValid 7010 58 := by unfold smallValid; decide +kernel

private theorem sp7068 : smallValid 7068 58 := by unfold smallValid; decide +kernel

private theorem sp7126 : smallValid 7126 58 := by unfold smallValid; decide +kernel

private theorem sp7184 : smallValid 7184 58 := by unfold smallValid; decide +kernel

private theorem sp7242 : smallValid 7242 58 := by unfold smallValid; decide +kernel

private theorem sp7300 : smallValid 7300 58 := by unfold smallValid; decide +kernel

private theorem sp7358 : smallValid 7358 58 := by unfold smallValid; decide +kernel

private theorem sp7416 : smallValid 7416 57 := by unfold smallValid; decide +kernel

private theorem sp7473 : smallValid 7473 58 := by unfold smallValid; decide +kernel

private theorem sp7531 : smallValid 7531 58 := by unfold smallValid; decide +kernel

private theorem sp7589 : smallValid 7589 58 := by unfold smallValid; decide +kernel

private theorem sp7647 : smallValid 7647 58 := by unfold smallValid; decide +kernel

private theorem sp7705 : smallValid 7705 58 := by unfold smallValid; decide +kernel

private theorem sp7763 : smallValid 7763 58 := by unfold smallValid; decide +kernel

private theorem sp7821 : smallValid 7821 58 := by unfold smallValid; decide +kernel

private theorem sp7879 : smallValid 7879 58 := by unfold smallValid; decide +kernel

private theorem sp7937 : smallValid 7937 58 := by unfold smallValid; decide +kernel

private theorem sp7995 : smallValid 7995 58 := by unfold smallValid; decide +kernel

private theorem sp8053 : smallValid 8053 58 := by unfold smallValid; decide +kernel

private theorem sp8111 : smallValid 8111 58 := by unfold smallValid; decide +kernel

private theorem sp8169 : smallValid 8169 58 := by unfold smallValid; decide +kernel

private theorem sp8227 : smallValid 8227 58 := by unfold smallValid; decide +kernel

private theorem sp8285 : smallValid 8285 58 := by unfold smallValid; decide +kernel

private theorem sp8343 : smallValid 8343 57 := by unfold smallValid; decide +kernel

private theorem sp8400 : smallValid 8400 58 := by unfold smallValid; decide +kernel

private theorem sp8458 : smallValid 8458 58 := by unfold smallValid; decide +kernel

private theorem sp8516 : smallValid 8516 58 := by unfold smallValid; decide +kernel

private theorem sp8574 : smallValid 8574 58 := by unfold smallValid; decide +kernel

private theorem sp8632 : smallValid 8632 58 := by unfold smallValid; decide +kernel

private theorem sp8690 : smallValid 8690 58 := by unfold smallValid; decide +kernel

private theorem sp8748 : smallValid 8748 58 := by unfold smallValid; decide +kernel

private theorem sp8806 : smallValid 8806 58 := by unfold smallValid; decide +kernel

private theorem sp8864 : smallValid 8864 58 := by unfold smallValid; decide +kernel

private theorem sp8922 : smallValid 8922 58 := by unfold smallValid; decide +kernel

private theorem sp8980 : smallValid 8980 58 := by unfold smallValid; decide +kernel

private theorem sp9038 : smallValid 9038 58 := by unfold smallValid; decide +kernel

private theorem sp9096 : smallValid 9096 58 := by unfold smallValid; decide +kernel

private theorem sp9154 : smallValid 9154 58 := by unfold smallValid; decide +kernel

private theorem sp9212 : smallValid 9212 58 := by unfold smallValid; decide +kernel

private theorem sp9270 : smallValid 9270 57 := by unfold smallValid; decide +kernel

private theorem sp9327 : smallValid 9327 58 := by unfold smallValid; decide +kernel

private theorem sp9385 : smallValid 9385 58 := by unfold smallValid; decide +kernel

private theorem sp9443 : smallValid 9443 58 := by unfold smallValid; decide +kernel

private theorem sp9501 : smallValid 9501 58 := by unfold smallValid; decide +kernel

private theorem sp9559 : smallValid 9559 58 := by unfold smallValid; decide +kernel

private theorem sp9617 : smallValid 9617 58 := by unfold smallValid; decide +kernel

private theorem sp9675 : smallValid 9675 58 := by unfold smallValid; decide +kernel

private theorem sp9733 : smallValid 9733 58 := by unfold smallValid; decide +kernel

private theorem sp9791 : smallValid 9791 58 := by unfold smallValid; decide +kernel

private theorem sp9849 : smallValid 9849 58 := by unfold smallValid; decide +kernel

private theorem sp9907 : smallValid 9907 58 := by unfold smallValid; decide +kernel

private theorem sp9965 : smallValid 9965 58 := by unfold smallValid; decide +kernel

private theorem sp10023 : smallValid 10023 58 := by unfold smallValid; decide +kernel

private theorem sp10081 : smallValid 10081 58 := by unfold smallValid; decide +kernel

private theorem sp10139 : smallValid 10139 58 := by unfold smallValid; decide +kernel

private theorem sp10197 : smallValid 10197 57 := by unfold smallValid; decide +kernel

private theorem sp10254 : smallValid 10254 58 := by unfold smallValid; decide +kernel

private theorem sp10312 : smallValid 10312 58 := by unfold smallValid; decide +kernel

private theorem sp10370 : smallValid 10370 58 := by unfold smallValid; decide +kernel

private theorem sp10428 : smallValid 10428 58 := by unfold smallValid; decide +kernel

private theorem sp10486 : smallValid 10486 58 := by unfold smallValid; decide +kernel

private theorem sp10544 : smallValid 10544 58 := by unfold smallValid; decide +kernel

private theorem sp10602 : smallValid 10602 58 := by unfold smallValid; decide +kernel

private theorem sp10660 : smallValid 10660 58 := by unfold smallValid; decide +kernel

private theorem sp10718 : smallValid 10718 58 := by unfold smallValid; decide +kernel

private theorem sp10776 : smallValid 10776 58 := by unfold smallValid; decide +kernel

private theorem sp10834 : smallValid 10834 58 := by unfold smallValid; decide +kernel

private theorem sp10892 : smallValid 10892 58 := by unfold smallValid; decide +kernel

private theorem sp10950 : smallValid 10950 58 := by unfold smallValid; decide +kernel

private theorem sp11008 : smallValid 11008 58 := by unfold smallValid; decide +kernel

private theorem sp11066 : smallValid 11066 58 := by unfold smallValid; decide +kernel

private theorem sp11124 : smallValid 11124 57 := by unfold smallValid; decide +kernel

private theorem sp11181 : smallValid 11181 58 := by unfold smallValid; decide +kernel

private theorem sp11239 : smallValid 11239 58 := by unfold smallValid; decide +kernel

private theorem sp11297 : smallValid 11297 58 := by unfold smallValid; decide +kernel

private theorem sp11355 : smallValid 11355 58 := by unfold smallValid; decide +kernel

private theorem sp11413 : smallValid 11413 58 := by unfold smallValid; decide +kernel

private theorem sp11471 : smallValid 11471 58 := by unfold smallValid; decide +kernel

private theorem sp11529 : smallValid 11529 58 := by unfold smallValid; decide +kernel

private theorem sp11587 : smallValid 11587 58 := by unfold smallValid; decide +kernel

private theorem sp11645 : smallValid 11645 58 := by unfold smallValid; decide +kernel

private theorem sp11703 : smallValid 11703 58 := by unfold smallValid; decide +kernel

private theorem sp11761 : smallValid 11761 58 := by unfold smallValid; decide +kernel

private theorem sp11819 : smallValid 11819 58 := by unfold smallValid; decide +kernel

private theorem sp11877 : smallValid 11877 58 := by unfold smallValid; decide +kernel

private theorem sp11935 : smallValid 11935 58 := by unfold smallValid; decide +kernel

private theorem sp11993 : smallValid 11993 58 := by unfold smallValid; decide +kernel

private theorem sp12051 : smallValid 12051 57 := by unfold smallValid; decide +kernel

private theorem sp12108 : smallValid 12108 58 := by unfold smallValid; decide +kernel

private theorem sp12166 : smallValid 12166 58 := by unfold smallValid; decide +kernel

private theorem sp12224 : smallValid 12224 58 := by unfold smallValid; decide +kernel

private theorem sp12282 : smallValid 12282 58 := by unfold smallValid; decide +kernel

private theorem sp12340 : smallValid 12340 58 := by unfold smallValid; decide +kernel

private theorem sp12398 : smallValid 12398 58 := by unfold smallValid; decide +kernel

private theorem sp12456 : smallValid 12456 58 := by unfold smallValid; decide +kernel

private theorem sp12514 : smallValid 12514 58 := by unfold smallValid; decide +kernel

private theorem sp12572 : smallValid 12572 58 := by unfold smallValid; decide +kernel

private theorem sp12630 : smallValid 12630 58 := by unfold smallValid; decide +kernel

private theorem sp12688 : smallValid 12688 58 := by unfold smallValid; decide +kernel

private theorem sp12746 : smallValid 12746 58 := by unfold smallValid; decide +kernel

private theorem sp12804 : smallValid 12804 58 := by unfold smallValid; decide +kernel

private theorem sp12862 : smallValid 12862 58 := by unfold smallValid; decide +kernel

private theorem sp12920 : smallValid 12920 58 := by unfold smallValid; decide +kernel

private theorem sp12978 : smallValid 12978 57 := by unfold smallValid; decide +kernel

private theorem sp13035 : smallValid 13035 58 := by unfold smallValid; decide +kernel

private theorem sp13093 : smallValid 13093 58 := by unfold smallValid; decide +kernel

private theorem sp13151 : smallValid 13151 58 := by unfold smallValid; decide +kernel

private theorem sp13209 : smallValid 13209 58 := by unfold smallValid; decide +kernel

private theorem sp13267 : smallValid 13267 58 := by unfold smallValid; decide +kernel

private theorem sp13325 : smallValid 13325 58 := by unfold smallValid; decide +kernel

private theorem sp13383 : smallValid 13383 58 := by unfold smallValid; decide +kernel

private theorem sp13441 : smallValid 13441 58 := by unfold smallValid; decide +kernel

private theorem sp13499 : smallValid 13499 58 := by unfold smallValid; decide +kernel

private theorem sp13557 : smallValid 13557 58 := by unfold smallValid; decide +kernel

private theorem sp13615 : smallValid 13615 58 := by unfold smallValid; decide +kernel

private theorem sp13673 : smallValid 13673 58 := by unfold smallValid; decide +kernel

private theorem sp13731 : smallValid 13731 58 := by unfold smallValid; decide +kernel

private theorem sp13789 : smallValid 13789 58 := by unfold smallValid; decide +kernel

private theorem sp13847 : smallValid 13847 58 := by unfold smallValid; decide +kernel

private theorem sp13905 : smallValid 13905 58 := by unfold smallValid; decide +kernel

private theorem sp13963 : smallValid 13963 58 := by unfold smallValid; decide +kernel

private theorem sp14021 : smallValid 14021 58 := by unfold smallValid; decide +kernel

private theorem sp14079 : smallValid 14079 58 := by unfold smallValid; decide +kernel

private theorem sp14137 : smallValid 14137 58 := by unfold smallValid; decide +kernel

private theorem sp14195 : smallValid 14195 58 := by unfold smallValid; decide +kernel

private theorem sp14253 : smallValid 14253 58 := by unfold smallValid; decide +kernel

private theorem sp14311 : smallValid 14311 58 := by unfold smallValid; decide +kernel

private theorem sp14369 : smallValid 14369 58 := by unfold smallValid; decide +kernel

private theorem sp14427 : smallValid 14427 58 := by unfold smallValid; decide +kernel

private theorem sp14485 : smallValid 14485 58 := by unfold smallValid; decide +kernel

private theorem sp14543 : smallValid 14543 58 := by unfold smallValid; decide +kernel

private theorem sp14601 : smallValid 14601 58 := by unfold smallValid; decide +kernel

private theorem sp14659 : smallValid 14659 58 := by unfold smallValid; decide +kernel

private theorem sp14717 : smallValid 14717 58 := by unfold smallValid; decide +kernel

private theorem sp14775 : smallValid 14775 58 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤14832) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 14833 := (joinSmall (lo:=0) (a:=7416) (b:=7417) (joinSmall (lo:=0) (a:=3708) (b:=3708) (joinSmall (lo:=0) (a:=1854) (b:=1854) (joinSmall (lo:=0) (a:=927) (b:=927) (joinSmall (lo:=0) (a:=463) (b:=464) (joinSmall (lo:=0) (a:=231) (b:=232) (joinSmall (lo:=0) (a:=115) (b:=116) (joinSmall (lo:=0) (a:=57) (b:=58) sp0 sp57) (joinSmall (lo:=115) (a:=58) (b:=58) sp115 sp173)) (joinSmall (lo:=231) (a:=116) (b:=116) (joinSmall (lo:=231) (a:=58) (b:=58) sp231 sp289) (joinSmall (lo:=347) (a:=58) (b:=58) sp347 sp405))) (joinSmall (lo:=463) (a:=232) (b:=232) (joinSmall (lo:=463) (a:=116) (b:=116) (joinSmall (lo:=463) (a:=58) (b:=58) sp463 sp521) (joinSmall (lo:=579) (a:=58) (b:=58) sp579 sp637)) (joinSmall (lo:=695) (a:=116) (b:=116) (joinSmall (lo:=695) (a:=58) (b:=58) sp695 sp753) (joinSmall (lo:=811) (a:=58) (b:=58) sp811 sp869)))) (joinSmall (lo:=927) (a:=463) (b:=464) (joinSmall (lo:=927) (a:=231) (b:=232) (joinSmall (lo:=927) (a:=115) (b:=116) (joinSmall (lo:=927) (a:=57) (b:=58) sp927 sp984) (joinSmall (lo:=1042) (a:=58) (b:=58) sp1042 sp1100)) (joinSmall (lo:=1158) (a:=116) (b:=116) (joinSmall (lo:=1158) (a:=58) (b:=58) sp1158 sp1216) (joinSmall (lo:=1274) (a:=58) (b:=58) sp1274 sp1332))) (joinSmall (lo:=1390) (a:=232) (b:=232) (joinSmall (lo:=1390) (a:=116) (b:=116) (joinSmall (lo:=1390) (a:=58) (b:=58) sp1390 sp1448) (joinSmall (lo:=1506) (a:=58) (b:=58) sp1506 sp1564)) (joinSmall (lo:=1622) (a:=116) (b:=116) (joinSmall (lo:=1622) (a:=58) (b:=58) sp1622 sp1680) (joinSmall (lo:=1738) (a:=58) (b:=58) sp1738 sp1796))))) (joinSmall (lo:=1854) (a:=927) (b:=927) (joinSmall (lo:=1854) (a:=463) (b:=464) (joinSmall (lo:=1854) (a:=231) (b:=232) (joinSmall (lo:=1854) (a:=115) (b:=116) (joinSmall (lo:=1854) (a:=57) (b:=58) sp1854 sp1911) (joinSmall (lo:=1969) (a:=58) (b:=58) sp1969 sp2027)) (joinSmall (lo:=2085) (a:=116) (b:=116) (joinSmall (lo:=2085) (a:=58) (b:=58) sp2085 sp2143) (joinSmall (lo:=2201) (a:=58) (b:=58) sp2201 sp2259))) (joinSmall (lo:=2317) (a:=232) (b:=232) (joinSmall (lo:=2317) (a:=116) (b:=116) (joinSmall (lo:=2317) (a:=58) (b:=58) sp2317 sp2375) (joinSmall (lo:=2433) (a:=58) (b:=58) sp2433 sp2491)) (joinSmall (lo:=2549) (a:=116) (b:=116) (joinSmall (lo:=2549) (a:=58) (b:=58) sp2549 sp2607) (joinSmall (lo:=2665) (a:=58) (b:=58) sp2665 sp2723)))) (joinSmall (lo:=2781) (a:=463) (b:=464) (joinSmall (lo:=2781) (a:=231) (b:=232) (joinSmall (lo:=2781) (a:=115) (b:=116) (joinSmall (lo:=2781) (a:=57) (b:=58) sp2781 sp2838) (joinSmall (lo:=2896) (a:=58) (b:=58) sp2896 sp2954)) (joinSmall (lo:=3012) (a:=116) (b:=116) (joinSmall (lo:=3012) (a:=58) (b:=58) sp3012 sp3070) (joinSmall (lo:=3128) (a:=58) (b:=58) sp3128 sp3186))) (joinSmall (lo:=3244) (a:=232) (b:=232) (joinSmall (lo:=3244) (a:=116) (b:=116) (joinSmall (lo:=3244) (a:=58) (b:=58) sp3244 sp3302) (joinSmall (lo:=3360) (a:=58) (b:=58) sp3360 sp3418)) (joinSmall (lo:=3476) (a:=116) (b:=116) (joinSmall (lo:=3476) (a:=58) (b:=58) sp3476 sp3534) (joinSmall (lo:=3592) (a:=58) (b:=58) sp3592 sp3650)))))) (joinSmall (lo:=3708) (a:=1854) (b:=1854) (joinSmall (lo:=3708) (a:=927) (b:=927) (joinSmall (lo:=3708) (a:=463) (b:=464) (joinSmall (lo:=3708) (a:=231) (b:=232) (joinSmall (lo:=3708) (a:=115) (b:=116) (joinSmall (lo:=3708) (a:=57) (b:=58) sp3708 sp3765) (joinSmall (lo:=3823) (a:=58) (b:=58) sp3823 sp3881)) (joinSmall (lo:=3939) (a:=116) (b:=116) (joinSmall (lo:=3939) (a:=58) (b:=58) sp3939 sp3997) (joinSmall (lo:=4055) (a:=58) (b:=58) sp4055 sp4113))) (joinSmall (lo:=4171) (a:=232) (b:=232) (joinSmall (lo:=4171) (a:=116) (b:=116) (joinSmall (lo:=4171) (a:=58) (b:=58) sp4171 sp4229) (joinSmall (lo:=4287) (a:=58) (b:=58) sp4287 sp4345)) (joinSmall (lo:=4403) (a:=116) (b:=116) (joinSmall (lo:=4403) (a:=58) (b:=58) sp4403 sp4461) (joinSmall (lo:=4519) (a:=58) (b:=58) sp4519 sp4577)))) (joinSmall (lo:=4635) (a:=463) (b:=464) (joinSmall (lo:=4635) (a:=231) (b:=232) (joinSmall (lo:=4635) (a:=115) (b:=116) (joinSmall (lo:=4635) (a:=57) (b:=58) sp4635 sp4692) (joinSmall (lo:=4750) (a:=58) (b:=58) sp4750 sp4808)) (joinSmall (lo:=4866) (a:=116) (b:=116) (joinSmall (lo:=4866) (a:=58) (b:=58) sp4866 sp4924) (joinSmall (lo:=4982) (a:=58) (b:=58) sp4982 sp5040))) (joinSmall (lo:=5098) (a:=232) (b:=232) (joinSmall (lo:=5098) (a:=116) (b:=116) (joinSmall (lo:=5098) (a:=58) (b:=58) sp5098 sp5156) (joinSmall (lo:=5214) (a:=58) (b:=58) sp5214 sp5272)) (joinSmall (lo:=5330) (a:=116) (b:=116) (joinSmall (lo:=5330) (a:=58) (b:=58) sp5330 sp5388) (joinSmall (lo:=5446) (a:=58) (b:=58) sp5446 sp5504))))) (joinSmall (lo:=5562) (a:=927) (b:=927) (joinSmall (lo:=5562) (a:=463) (b:=464) (joinSmall (lo:=5562) (a:=231) (b:=232) (joinSmall (lo:=5562) (a:=115) (b:=116) (joinSmall (lo:=5562) (a:=57) (b:=58) sp5562 sp5619) (joinSmall (lo:=5677) (a:=58) (b:=58) sp5677 sp5735)) (joinSmall (lo:=5793) (a:=116) (b:=116) (joinSmall (lo:=5793) (a:=58) (b:=58) sp5793 sp5851) (joinSmall (lo:=5909) (a:=58) (b:=58) sp5909 sp5967))) (joinSmall (lo:=6025) (a:=232) (b:=232) (joinSmall (lo:=6025) (a:=116) (b:=116) (joinSmall (lo:=6025) (a:=58) (b:=58) sp6025 sp6083) (joinSmall (lo:=6141) (a:=58) (b:=58) sp6141 sp6199)) (joinSmall (lo:=6257) (a:=116) (b:=116) (joinSmall (lo:=6257) (a:=58) (b:=58) sp6257 sp6315) (joinSmall (lo:=6373) (a:=58) (b:=58) sp6373 sp6431)))) (joinSmall (lo:=6489) (a:=463) (b:=464) (joinSmall (lo:=6489) (a:=231) (b:=232) (joinSmall (lo:=6489) (a:=115) (b:=116) (joinSmall (lo:=6489) (a:=57) (b:=58) sp6489 sp6546) (joinSmall (lo:=6604) (a:=58) (b:=58) sp6604 sp6662)) (joinSmall (lo:=6720) (a:=116) (b:=116) (joinSmall (lo:=6720) (a:=58) (b:=58) sp6720 sp6778) (joinSmall (lo:=6836) (a:=58) (b:=58) sp6836 sp6894))) (joinSmall (lo:=6952) (a:=232) (b:=232) (joinSmall (lo:=6952) (a:=116) (b:=116) (joinSmall (lo:=6952) (a:=58) (b:=58) sp6952 sp7010) (joinSmall (lo:=7068) (a:=58) (b:=58) sp7068 sp7126)) (joinSmall (lo:=7184) (a:=116) (b:=116) (joinSmall (lo:=7184) (a:=58) (b:=58) sp7184 sp7242) (joinSmall (lo:=7300) (a:=58) (b:=58) sp7300 sp7358))))))) (joinSmall (lo:=7416) (a:=3708) (b:=3709) (joinSmall (lo:=7416) (a:=1854) (b:=1854) (joinSmall (lo:=7416) (a:=927) (b:=927) (joinSmall (lo:=7416) (a:=463) (b:=464) (joinSmall (lo:=7416) (a:=231) (b:=232) (joinSmall (lo:=7416) (a:=115) (b:=116) (joinSmall (lo:=7416) (a:=57) (b:=58) sp7416 sp7473) (joinSmall (lo:=7531) (a:=58) (b:=58) sp7531 sp7589)) (joinSmall (lo:=7647) (a:=116) (b:=116) (joinSmall (lo:=7647) (a:=58) (b:=58) sp7647 sp7705) (joinSmall (lo:=7763) (a:=58) (b:=58) sp7763 sp7821))) (joinSmall (lo:=7879) (a:=232) (b:=232) (joinSmall (lo:=7879) (a:=116) (b:=116) (joinSmall (lo:=7879) (a:=58) (b:=58) sp7879 sp7937) (joinSmall (lo:=7995) (a:=58) (b:=58) sp7995 sp8053)) (joinSmall (lo:=8111) (a:=116) (b:=116) (joinSmall (lo:=8111) (a:=58) (b:=58) sp8111 sp8169) (joinSmall (lo:=8227) (a:=58) (b:=58) sp8227 sp8285)))) (joinSmall (lo:=8343) (a:=463) (b:=464) (joinSmall (lo:=8343) (a:=231) (b:=232) (joinSmall (lo:=8343) (a:=115) (b:=116) (joinSmall (lo:=8343) (a:=57) (b:=58) sp8343 sp8400) (joinSmall (lo:=8458) (a:=58) (b:=58) sp8458 sp8516)) (joinSmall (lo:=8574) (a:=116) (b:=116) (joinSmall (lo:=8574) (a:=58) (b:=58) sp8574 sp8632) (joinSmall (lo:=8690) (a:=58) (b:=58) sp8690 sp8748))) (joinSmall (lo:=8806) (a:=232) (b:=232) (joinSmall (lo:=8806) (a:=116) (b:=116) (joinSmall (lo:=8806) (a:=58) (b:=58) sp8806 sp8864) (joinSmall (lo:=8922) (a:=58) (b:=58) sp8922 sp8980)) (joinSmall (lo:=9038) (a:=116) (b:=116) (joinSmall (lo:=9038) (a:=58) (b:=58) sp9038 sp9096) (joinSmall (lo:=9154) (a:=58) (b:=58) sp9154 sp9212))))) (joinSmall (lo:=9270) (a:=927) (b:=927) (joinSmall (lo:=9270) (a:=463) (b:=464) (joinSmall (lo:=9270) (a:=231) (b:=232) (joinSmall (lo:=9270) (a:=115) (b:=116) (joinSmall (lo:=9270) (a:=57) (b:=58) sp9270 sp9327) (joinSmall (lo:=9385) (a:=58) (b:=58) sp9385 sp9443)) (joinSmall (lo:=9501) (a:=116) (b:=116) (joinSmall (lo:=9501) (a:=58) (b:=58) sp9501 sp9559) (joinSmall (lo:=9617) (a:=58) (b:=58) sp9617 sp9675))) (joinSmall (lo:=9733) (a:=232) (b:=232) (joinSmall (lo:=9733) (a:=116) (b:=116) (joinSmall (lo:=9733) (a:=58) (b:=58) sp9733 sp9791) (joinSmall (lo:=9849) (a:=58) (b:=58) sp9849 sp9907)) (joinSmall (lo:=9965) (a:=116) (b:=116) (joinSmall (lo:=9965) (a:=58) (b:=58) sp9965 sp10023) (joinSmall (lo:=10081) (a:=58) (b:=58) sp10081 sp10139)))) (joinSmall (lo:=10197) (a:=463) (b:=464) (joinSmall (lo:=10197) (a:=231) (b:=232) (joinSmall (lo:=10197) (a:=115) (b:=116) (joinSmall (lo:=10197) (a:=57) (b:=58) sp10197 sp10254) (joinSmall (lo:=10312) (a:=58) (b:=58) sp10312 sp10370)) (joinSmall (lo:=10428) (a:=116) (b:=116) (joinSmall (lo:=10428) (a:=58) (b:=58) sp10428 sp10486) (joinSmall (lo:=10544) (a:=58) (b:=58) sp10544 sp10602))) (joinSmall (lo:=10660) (a:=232) (b:=232) (joinSmall (lo:=10660) (a:=116) (b:=116) (joinSmall (lo:=10660) (a:=58) (b:=58) sp10660 sp10718) (joinSmall (lo:=10776) (a:=58) (b:=58) sp10776 sp10834)) (joinSmall (lo:=10892) (a:=116) (b:=116) (joinSmall (lo:=10892) (a:=58) (b:=58) sp10892 sp10950) (joinSmall (lo:=11008) (a:=58) (b:=58) sp11008 sp11066)))))) (joinSmall (lo:=11124) (a:=1854) (b:=1855) (joinSmall (lo:=11124) (a:=927) (b:=927) (joinSmall (lo:=11124) (a:=463) (b:=464) (joinSmall (lo:=11124) (a:=231) (b:=232) (joinSmall (lo:=11124) (a:=115) (b:=116) (joinSmall (lo:=11124) (a:=57) (b:=58) sp11124 sp11181) (joinSmall (lo:=11239) (a:=58) (b:=58) sp11239 sp11297)) (joinSmall (lo:=11355) (a:=116) (b:=116) (joinSmall (lo:=11355) (a:=58) (b:=58) sp11355 sp11413) (joinSmall (lo:=11471) (a:=58) (b:=58) sp11471 sp11529))) (joinSmall (lo:=11587) (a:=232) (b:=232) (joinSmall (lo:=11587) (a:=116) (b:=116) (joinSmall (lo:=11587) (a:=58) (b:=58) sp11587 sp11645) (joinSmall (lo:=11703) (a:=58) (b:=58) sp11703 sp11761)) (joinSmall (lo:=11819) (a:=116) (b:=116) (joinSmall (lo:=11819) (a:=58) (b:=58) sp11819 sp11877) (joinSmall (lo:=11935) (a:=58) (b:=58) sp11935 sp11993)))) (joinSmall (lo:=12051) (a:=463) (b:=464) (joinSmall (lo:=12051) (a:=231) (b:=232) (joinSmall (lo:=12051) (a:=115) (b:=116) (joinSmall (lo:=12051) (a:=57) (b:=58) sp12051 sp12108) (joinSmall (lo:=12166) (a:=58) (b:=58) sp12166 sp12224)) (joinSmall (lo:=12282) (a:=116) (b:=116) (joinSmall (lo:=12282) (a:=58) (b:=58) sp12282 sp12340) (joinSmall (lo:=12398) (a:=58) (b:=58) sp12398 sp12456))) (joinSmall (lo:=12514) (a:=232) (b:=232) (joinSmall (lo:=12514) (a:=116) (b:=116) (joinSmall (lo:=12514) (a:=58) (b:=58) sp12514 sp12572) (joinSmall (lo:=12630) (a:=58) (b:=58) sp12630 sp12688)) (joinSmall (lo:=12746) (a:=116) (b:=116) (joinSmall (lo:=12746) (a:=58) (b:=58) sp12746 sp12804) (joinSmall (lo:=12862) (a:=58) (b:=58) sp12862 sp12920))))) (joinSmall (lo:=12978) (a:=927) (b:=928) (joinSmall (lo:=12978) (a:=463) (b:=464) (joinSmall (lo:=12978) (a:=231) (b:=232) (joinSmall (lo:=12978) (a:=115) (b:=116) (joinSmall (lo:=12978) (a:=57) (b:=58) sp12978 sp13035) (joinSmall (lo:=13093) (a:=58) (b:=58) sp13093 sp13151)) (joinSmall (lo:=13209) (a:=116) (b:=116) (joinSmall (lo:=13209) (a:=58) (b:=58) sp13209 sp13267) (joinSmall (lo:=13325) (a:=58) (b:=58) sp13325 sp13383))) (joinSmall (lo:=13441) (a:=232) (b:=232) (joinSmall (lo:=13441) (a:=116) (b:=116) (joinSmall (lo:=13441) (a:=58) (b:=58) sp13441 sp13499) (joinSmall (lo:=13557) (a:=58) (b:=58) sp13557 sp13615)) (joinSmall (lo:=13673) (a:=116) (b:=116) (joinSmall (lo:=13673) (a:=58) (b:=58) sp13673 sp13731) (joinSmall (lo:=13789) (a:=58) (b:=58) sp13789 sp13847)))) (joinSmall (lo:=13905) (a:=464) (b:=464) (joinSmall (lo:=13905) (a:=232) (b:=232) (joinSmall (lo:=13905) (a:=116) (b:=116) (joinSmall (lo:=13905) (a:=58) (b:=58) sp13905 sp13963) (joinSmall (lo:=14021) (a:=58) (b:=58) sp14021 sp14079)) (joinSmall (lo:=14137) (a:=116) (b:=116) (joinSmall (lo:=14137) (a:=58) (b:=58) sp14137 sp14195) (joinSmall (lo:=14253) (a:=58) (b:=58) sp14253 sp14311))) (joinSmall (lo:=14369) (a:=232) (b:=232) (joinSmall (lo:=14369) (a:=116) (b:=116) (joinSmall (lo:=14369) (a:=58) (b:=58) sp14369 sp14427) (joinSmall (lo:=14485) (a:=58) (b:=58) sp14485 sp14543)) (joinSmall (lo:=14601) (a:=116) (b:=116) (joinSmall (lo:=14601) (a:=58) (b:=58) sp14601 sp14659) (joinSmall (lo:=14717) (a:=58) (b:=58) sp14717 sp14775))))))))
  have good : (List.range 14833).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 220000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 14832 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 14832 := by
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


private def packet (i : ℕ) : ℕ := (if i < 56 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 5 then (if i < 4 then 0 else 0) else (if i < 6 then 0 else 0))) else (if i < 10 then (if i < 8 then 0 else (if i < 9 then 0 else 0)) else (if i < 12 then (if i < 11 then 0 else 0) else (if i < 13 then 0 else 0)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0 else (if i < 16 then 0 else 0)) else (if i < 19 then (if i < 18 then 0 else 0) else (if i < 20 then 0 else 0))) else (if i < 24 then (if i < 22 then 0 else (if i < 23 then 0 else 0)) else (if i < 26 then (if i < 25 then 0 else 0) else (if i < 27 then 0 else 0))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then 0 else (if i < 30 then 0 else 0)) else (if i < 33 then (if i < 32 then 0 else 0) else (if i < 34 then 0 else 0))) else (if i < 38 then (if i < 36 then 0 else (if i < 37 then 0 else 0)) else (if i < 40 then (if i < 39 then 0 else 0) else (if i < 41 then 0 else 0)))) else (if i < 49 then (if i < 45 then (if i < 43 then 0 else (if i < 44 then 0 else 0)) else (if i < 47 then (if i < 46 then 0 else 0) else (if i < 48 then 0 else 0))) else (if i < 52 then (if i < 50 then 0 else (if i < 51 then 0 else 0)) else (if i < 54 then (if i < 53 then 0 else 0) else (if i < 55 then 0 else 0)))))) else (if i < 84 then (if i < 70 then (if i < 63 then (if i < 59 then (if i < 57 then 0 else (if i < 58 then 0 else 0)) else (if i < 61 then (if i < 60 then 0 else 0) else (if i < 62 then 0 else 0))) else (if i < 66 then (if i < 64 then 0 else (if i < 65 then 0 else 0)) else (if i < 68 then (if i < 67 then 0 else 0) else (if i < 69 then 0 else 0)))) else (if i < 77 then (if i < 73 then (if i < 71 then 0 else (if i < 72 then 0 else 0)) else (if i < 75 then (if i < 74 then 0 else 0) else (if i < 76 then 0 else 0))) else (if i < 80 then (if i < 78 then 0 else (if i < 79 then 0 else 0)) else (if i < 82 then (if i < 81 then 0 else 0) else (if i < 83 then 0 else 0))))) else (if i < 98 then (if i < 91 then (if i < 87 then (if i < 85 then 0 else (if i < 86 then 0 else 0)) else (if i < 89 then (if i < 88 then 0 else 0) else (if i < 90 then 0 else 0))) else (if i < 94 then (if i < 92 then 0 else (if i < 93 then 0 else 0)) else (if i < 96 then (if i < 95 then 0 else 0) else (if i < 97 then 0 else 0)))) else (if i < 105 then (if i < 101 then (if i < 99 then 0 else (if i < 100 then 0xa6523e2dc956c9f649821b8f9c700324161098440a19108f83200d6000a64bdf2fd1614a484be233901072c33216589803f419c09c83600d6000a645772fa1638a4e4c322f0fe072a336163899040619109502ec0c8000a63f242f7962ca504c72310ff473032c16009703da187096833c0cc000a638df2ef95fca524be22e0fcc71e32c16489483e418a09683140c8000a632922ee95dca284a821f8f846e830e15389183ea19109503300bc000a62c29305968ca684cc232102475a33f1708a204441c20a503700e0000a625fc2e415a8a244b322c0fe072a327161097c3e218f09302d40b2000a61fc22ea95cca124ac21d8f4c6e231115f09783ec19108f02ec0c4000a619812ee95e0a204ab2238f7c6f032615a091c3c818609383280b4000a613562df95509f648c2198f5c6fa320162899c4141a209d83440c6000a60d432dc95349c648b2130f346d6310154090c3c218709903080c2000a607122e815aca0e4a021d8f306d630515009003c617a09082ec0b6000a600b02ff9648a524c222e8fd072232916089603ec19109282f00b6000a5fa722e615a4a0c4a021c8f306da30d15509383d418f094030c0c0000a5f4422e61594a0c49321a8f546e031815d093c3ca17808a02c40b0000a5ee122e71590a0e4b02280f8c71431a15b895c3f819b09803340d2000a5e7b82fd9634a3c4b12238fc471c32215d09683fc19c09d83500e0000a5e18b2e495849f64952200f7c70432516389643fa18e09603200c6000a5db2730716b4a784da241103473833516a09a44061a609d83340ca000a5d4c52fa162ca5c4c422c8fd070e32115e89603d418a09082f40c4000a5ce7b2ed95c8a204b32278f786ee30b15389403d618808c02d80c2000a5c7fb30b16a8a964e723c104c75e33d16c09c441419a09b033c0de000a5c1bb2f1160ca4c4be22a0fcc71832c16689883fa19e09c835c0ca000a5bb822e895eca484b82288fb070a32216509943f418309082cc0a8000a5b5542e415b8a264b32218f286c42fe14a88d03ac17709083140ca000a5af162f195fca184ac2208f9c6f631415308e83a016a08782d40be000a5a8ee2e395989fc49c2200f9070c31d16109583e418709202fc0cc000a5a26430e16e0a924ee23d903c73e33b166898c4121a409f83600d4000a59c392e195b4a1449e21d8f406da31616009543e419008d83140c8000a596102e615c0a1e4af2248fb070831d15f09583fa198095035c0e8000a58fa53001680a704db238900474a33f16589943f019709583200c8000a5894d3029670a764d5238903074833c16b09cc4221a6095031c0cc000a583212ec15fca244c122a8fd071232d16509a84121a10a083280c8000a57cc32fd1668a684cd23b105075e340169899040e19c09703340c8000a576682ff9654a5a4c62338ff072632216089943f019f09603240da000a570212f515f4a244b02210f7c6f230d15a89243ca18308b82f40b4000a569ee2e7958ca104a121f0f806f031016089743fc19a0a103480d4000a563952fe1660a624ca2361028742332163098c40a19e09c03480da000a55d5e2e895b89ee49f2208f606fa31c16109803e819809683180d2000a557002fb9648a464c522e8fc06fe31816009843e418b08d02e00b4000a550dc2e09590a144a22240f946fe32315f097c408195092831c0c4000a54aa92e6159c9f64902148f506e831115e09903e818a094031c0ce000a544662ee1608a3e4b82288fb86fc32015b09683ec193097032c0d4000a53e3c2e695a0a204ab2270fb470e32516589cc42a1ab0a383780dc000a538192e395a49f64942170f186d430915109283d618b08c82cc0be000a531a930c96b4a844d6235901c74834717209dc41619a09683140c8000a52b802e215949f24a021f8f746e831a156892c3ca18808f83080b2000a525292f215eca0c4b52280fac70432215d89443da184092031c0b8000a51ed22f89640a4a4b92258fac71832b165097c4101a4096830c0c0000a518a32e395a4a104b12250fb470831d15a09643e618d09683200ca000a512642e995a8a184a62208f8070232515e895840219f09a03340cc000a50bf4305167ca764cd2308ff072a32a16489803e018909002e00a8000a5059a2fa164ca4a4b822c101474e33816709ac40c1a109a83500ca000a4ff2a3041650a664cf235901873433316309543ee19709803180d4000a4f8f42e915fca504c22340fe872432816909904061a109883100de000a4f28e2fd1648a544c222e0fec74033316089703e618409103180b0000a4ec2d2fb165ca564c52300fe8738331168097c40a19809803300d4000a4e5d82f61628a584c822e901073a333164898840c19d09e83540d4000a4df7a2f99630a5c4ca235101073833316789a43fa19209b03380c6000a4d92f2f015b8a224ac2288fd471432516309803fc19d09c03440d4000a4d2fd2e515d4a284b42318fe472232b160895c3e018d09282f00c8000a4cc9d3011678a784d9238904474834216e89cc42a1a60a003480cc000a4c6502f495fca4a4b62268f8c71032615c095c3da18909003040b4000 else 0xa7e35e2fd1638a4e4c722c0fc071032c16609b440219a09b83600d6000a7dd122f61620a424bc2278f7c71e330161096c3e8190096032c0c0000a7d6b42fe167ca904de238105076e35217309f442e1a90a8038c100000a7d0662f215f4a2e4af2220f846e830a14f89083c018308e83200d0000a7ca452e1156c9ec48d2168f246d430c15208d43bc18609183140c4000a7c3d23041684a7a4d42300fcc71e31f15c89603ea190099032c0c0000a7bd6c30516b4a7e4d423b105c75433f166898c3f619d09983500d2000a7b7442e51594a0e49521c8f6c6f431515a892c3ce18008d82f40b8000a7b0c230b16b4a984e5240905076834716e89cc4221ae0a303640c6000a7aa8d2e495cca324ae2218f8870031415609583e019609783100c0000a7a4452f395f4a4a4c022d8ff872833916b899c40a19909983440c8000a79dfe2ef15c8a1a4a92240f8871631b15c897840219709903040c8000a79799304167ca604bf231100472433015f89603de19108e83240d2000a791622f015f8a1e4b12248fac722329165099440619b09e03280cc000a78b3a2e595c8a184a72268f646ea315153093c3ca18308f030c0da000a784f62ed95f0a1a4a72200f646f831615d894c3cc18009003040bc000a77eaf2f29630a444b922c8ff8732330160097840c19a09e03540d0000a778722ed95dca1a4a92218fa470232015e098c3e619b09603040da000a7725b2da152c9e44912178f046c230515589183d017f09403180d2000a76c0a2f59614a3c4b52290fac70632716009703ec19809a83200c8000a765af2f215e0a284b522a0fd871e33416789a44041a909c83380be000a75f732e915aca1e4b52278f8c6e0302150891c3ca18809983280d4000a7594b2dc95409de48b2198f386ce30414a88b03aa18c08d02f40b2000a752e1302166ca7a4ce2310fe871433116109703dc188096831c0ce000a74cbb2e015509f04a421d0f746dc30714e08f03b018009102f00aa000a746522ff1638a564c22308fd473032d16389783ec19209602fc0ba000a7400c2f015d0a224b72288fb470232616089703e218b09303240e0000a739d02eb95d8a264aa21f0f686e231f15b89503f019409503280c8000a733a82e59580a0e4ab2220f9470231d15e89483ea19409483100b6000a72d532f69618a424b62288fb872a32a16809883f819309c03700ea000a727212e115a0a0c4a521d0f6c6ee31615d09703d218809503480d6000a721042d9953c9dc4872118ef46a82fa14f09143c218108e83300c2000a71acf2e095789ec49e21b8f606f231815909303e4195092830c0ba000a7147d2f99610a244ae2278fac71432a16409784041a109a03140c4000a70e462ed15eca1c4ad2240fbc73c33916689883f019209603140ba000a708052f51600a3e4c72318fd071631b15f0950404191099034c0c6000a701cb2e895d8a1c4b522a0fd073232d167099c3fa191096032c0ca000a6fb922e895989fc49b2240fa470c31a15909203dc18e09403280d0000a6f55d2e695a4a0c4a62210f746fe31a159895c3f019209783240c4000a6ef382d895309d44912170f186d82fa15188f83ca18109503080ce000a6e8d62fd1654a524be22e0fe873433816589ac3fc19809a03540d0000a6e2842f89624a444c122c0fd473a33f16d89ac40419b09c03480d2000a6dc173029690a7c4cf230100473c332165098040819d09803480cc000a6d5d22f21614a364bd2300fec73233916d89d441219c09903340c0000a6cf972e995b4a0a4b12240f746f631815d097c4081a109983080c6000a6c9402f5962ca4e4c52270fbc71e32d15e09403dc19d09c034c0bc000a6c2ff2ed15d8a284a92250f8c70e31f16089503e618a09302fc0bc000a6bccd2ef15b8a2e4b822f0fb871631e15f89643e419309a83440ce000a6b6822f19628a384b822c8fe471e32215d89703fa19109b83280ba000a6b05f2de15649dc48f21b8f7c6ec30c15408f83b617b08e82d80b8000a6aa152f315eca344b622e0fe072e32f168099c3fe19409a03380d2000a6a3bb2fc1668a624c022a0f9c70e31c15d89703ee19909203180da000a69d712f4961ca344bb22d0fec72a33016509903f219609703280c8000a697412e415c4a1e4a921d0f686f231715889403d618a09503340d0000a691022ef15a49fe49d21b8f806fa31a15f899040219609d83480d8000a68ab12fc1654a604c42330fbc71032115c894c3ba18309082ec09c000a6843431316f4a9a4ec241909076e35216f89dc41219f09703400c6000a67dfb2e81588a124a821e0f9c70e32015b89583cc18d09083000c8000a677982fa964ca604d3235100c72632815d093c3d218c09503200c2000a6716c2e815cca224ab2270f746e631a15c89703ee19e0a203640d8000a66b1c2f115e4a204b22218f80704323161897440e19a099032c0c4000a664d62ee95eca2c4ba22a8fac71231f15d09603d018108e02ec0c4000a65e962ef960ca2a4c622c8fe871c326160897c3ee19009403080b6000a658542ee95e8a2c4b52290fdc72032616309943f219609682ec0ba000)) else (if i < 103 then (if i < 102 then 0xa9755e2f8162ca4e4c622a0fd471432e16809c440e1a80a1834c0e6000a96eef3051694a804da23c106476c34716e89e44341b00a203480d4000a968c42e395689ec49b21c8f306c230214f89083c6187095032c0dc000a9626d2fc962ca444c52300fec730332163098840219d09e834c0e2000a95c312ec95d0a1a4aa2258fa871432a16489943fa19409b036c0d6000a956222db15489ec4912180f686f231815c89403d218d09803180bc000a950082dd9578a0c49b2228f946fc31e15e89543cc185093033c0dc000a949dd2e4957c9f448e2198f606e030d15889203c618a09383140b2000a9439a2ed15f4a2c4a82230f7c70630e158893c3ea18e09a03400d6000a93d492f39634a4c4c022b8fe072832c16009503e018f09603300ca000a936de3001668a664c72298f946e631615709303ec18409002f00ba000a930733049678a884dc23990407723511758a104261a90a003440e2000a92a0d3051694a764da23c906074834217089c44101a409a03480d4000a923c92ed15c4a304bf22d0fe872633616509a84001a10a083500de000a91d882ec95cca1a4ac2250f8470231515b097c3f21a009703680e0000a9171330896c0a7c4cc239103c74634516e89f84401bb0a483a00ea000a910d02ed15cca304b62290fbc70632515e893c3d018c09303240ba000a90a772f51628a424bd22d8ff072832716309683f0194096830c0b4000a904113009664a5a4be22e0fdc73832b16289743f6195099833c0c8000a8fdbe2f9965ca524c122b8fb072432e169096c4041a209c833c0cc000a8f7652f91604a524bc22c8f9c71232415d89703f819309602e80c0000a8f12e2eb157c9f24922180ee86b630015409303d019609483200b6000a8eaf02e715d4a204a82250f8470a31315809303d219109983100c6000a8e49f2f91658a504b722c0fa0710329162096c3f819309603200ca000a8de532f81618a404b822e8fe472032f1640974408197097832c0c8000a8d8212e89598a144a021e8f5c6ec31815909403d418609503100c0000a8d1f32e2956ca0a4a12210f846fc31b15909703dc18c09383000c2000a8cb992f91640a544be22f100473c33916c09c04121a10a103480cc000a8c58f2d315409fc49521a0f486cc31015b09483dc17d09502fc0ba000a8bf482f19614a364ba22c8ff873e33316589c840e1a709c034c0d0000a8b8eb2fd9654a644d6239105074e33f16a89dc41a1af0a403980d2000a8b2b02e815989fe4972198f206da30e157092c3b217f08e03140b6000a8ac523009670a7c4d9235903475434116b099c40619f09e83540e0000a8a6082f51638a564cc2338ff472433a16909c440619e09b83300d2000a89ffe2db15409ce4822158f286de30c155090c3ba17909103000b4000a899b22f59614a484c72368fe472e33616389803fe19409683300bc000a893432ff9690a984e323e103474233c16889c840e1a309d83640e0000a88cee2f49618a444b922a0fbc736325163095c3f219009383140e2000a8868e2f8966ca604cd2310fe071e32e16609bc40a19409682fc0c6000a8803d2f59640a4c4be22b8fc872c33716789ac3fc1a2098034c0ce000a87a022ef15b4a004a92280fc070c32415f89703fe19909a03380c6000a8738d3009674a724cf23c902875234516e09d43fe194099833c0d0000a86d3e2f495eca304a72200f7070432016009703e018909203180c0000a867132e315c4a224b02208f806f231415509003d2188095030c0b8000a860cb2f395fca304b02240fc8710324163099040419509903040c4000a85a912e915d8a244b32290f9c70632415f094c3ce18709503180ce000a8542b3029670a764de23a903c73634316c89e841e1a909d03500e2000a84dec2ef15dca2a4bf22e8ff872832816389a840219709403240d4000a847aa2ec95d8a384bd2278fb86fc322161097c3f818f09402fc0c2000a841672f19604a1e49e2198f106d82fe14e88ec3aa17308e82ec0b2000a83b242ed15d4a344b32278fac71c32616589983ee19909703140bc000a834f22e5958ca0e4a221f0f786ec30f159895c3dc18608f02f00c0000a82e9e2f495fca4c4c222b0fcc72032816389b040a19209b83300d4000a828512f295e4a304b922e0fd073232e1648984406199097836c0d6000a8223a2da1584a0449421e0f7c6fc31f16209803e618d09503380ce000a81c182e395a0a104952188f446d430c15509383de18809282fc0ba000a815cd2f09618a4a4b22250fc871e31a15b894c3c418408b82ec0c6000a80f633041688a5e4c3236104075034617089d44281a509b83680dc000a809202f79614a3c4b22280fa071432415f097c40a1a709b035c0d0000a803022df95689de48a2108f2c6d4312158093c3d018509583140d8000a7fcbe2f21608a244a22210f646ee31d15a89783d217c08a02e40c0000a7f66c2f59630a3a4c62318fec72a32b16289543f419409383140ca000a7f0142fa1624a484b522a0fb470a31915d09784041a809c83140c6000a7e9ba2fb1690a6c4d2237102074c34317089f842c1ad0a3036c0e6000 else 0xab06f12f09608a4e4c122f101075c34e16e09cc4181a80a083580c4000ab00e72d3950c9dc48a2128eec6b630a15589143c217708e02d00a8000aafa932f6161ca4c4c522e0fcc73233716309c44121a809f03400d8000aaf4622e21598a0849b21f0f706e630515409403da19009182f00ae000aaedf43011654a4c4c222c9014744334163097c40419309603180c4000aae7bd2ed15e8a1c4a52248f986fe31c15e09683fc19009a03180de000aae1652fa962ca484ba2280fcc72832d167898c40019809703540d6000aadb352e11584a004942178f3c6e030e15309243b417d08c02fc0bc000aad4d52f99628a424bb22e0fe471432d15e896c3e418f09783280bc000aacea62e295b4a0249f21d0f5c70032215b09483d017e08c02ec0d0000aac85c2f7964ca5c4c92328fe072632715b89603e618d09703080dc000aac20b2fa162ca444bb22a8fdc73033116809a83f819909b83180c6000aabbcd2eb158ca024912170f806f431415109303d218909203140c6000aab5a62e615a0a0e4a82230f906f431415889543dc184092030c0ca000aaaf3f2fd1654a764ce2308fe471a31d159893c3e218f095034c0c8000aaa9152e695dca264bd2270fa0718330165899c4061a909d035c0d8000aaa2e02ea15a4a084a921f0f7c70431a15e098840a1a309f83400d4000aa9c892f19624a5a4c82329018744344166897c3f419c0a083580de000aa96212fe1674a6c4bf22d0fdc71e33716589a840819d0a083780de000aa8fbd2fd1650a544c6233900874434216e899c3e619309182f00c8000aa897f2eb15e8a304b32258f9070432415b09543dc18008f82c00bc000aa832c2f89614a484d02320ff072832616289903ec18e098831c0c6000aa7cda2f91624a564c62300fcc73632716489883e818b093032c0dc000aa76932f51614a524cd238104074633c16b09bc4081af0a5838c0f6000aa70682e115609ea48e21b8f586e230915489203c618d09583280d2000aa69f630a1694a8e4de23e104874e33c16809a83f219609e83680d6000aa63b12f115e4a224ae2290fdc71c32315989743e818c09803440dc000aa5d7f2e595b0a244b92270fb470e31315609403e619909883500ce000aa57462ec95d4a3c4be22e8ff873e33315e09603e2196098032c0d0000aa50bf30d16a4a6c4ca233101473632e15f09803e219209303200c4000aa4aab2de15609d64922180f186d831015509203d018509183240c0000aa44582f49624a2a4bb22a0fc872633916a89b041a19a09a032c0d0000aa3e4f2d395309d448b2168f206dc30114c88f83c018409403200ba000aa38142ea95d4a204b222c0fe072433b16b09a83f618d09303200c0000aa31ce2e695b4a204b02208f846f631515c89483da18c09183040b4000aa2b842f515e0a224aa2260fb070831815c09503d018409102f00ba000aa25292f59658a624c62330ff872a32616089603ea18e09583240ce000aa1ed12fc9620a4c4c02298ff071832816589543da17f08f02e80c8000aa189e2e21598a144ac21f8f686f231215909183d218209103040d4000aa12562f6961ca5a4c32308ff072c32a162898040019509302ec0ba000aa0bf32fd9668a744d32358fec72432716789dc41e1a409a03580d2000aa05e62d315209da48a2138f046b82f514888fc3b818309003240d8000a9ff9d2f51608a2c4b221f0f7c6f8313156092c3d618d08f83180c2000a9f94c2f715f0a1e4a722a0f9870e31d15c09343d418d09603180c6000a9f3092ed95d8a204b822c8ff073633816b89c841a1a609a03400e0000a9ecbe2ef95f4a2c4aa2210f446d430114f892c3d417f09303280e2000a9e6502f89610a384b42288f9870232416209443d217e08f02e00b6000a9e0182e7959c9ee49a2208f846fc31b15b09383d4183093030c0c8000a9d9b92fa962ca484bc2298fbc70c32215e89583fa1a109d032c0c2000a9d36d2f41604a304be2298fa8722331160893c3c418609803080b4000a9cd432e015849ea49221a8f446c030515409043c618109182e40ba000a9c7002f115e4a324bc22b0fb071032e16609b440019309b03680d2000a9c0c12ed95a8a044a321c8f606d630314a08f43be17b08e83000a4000a9ba782f515e8a364bc2270fa871832815f096c3fe19f09903240bc000a9b4402ee95c0a1e4b62288fbc70232316109883f019c09603280c0000a9adfe2ec95eca124b12248f4c6e430c15488f83c618009102f80c8000a9a7a02f71650a4c4b922d0fec72c33816889803f819109583240be000a9a16f2e815a4a204a021b0f286e430e15589303ca189090832c0cc000a99b202f9163ca6c4ba22d900474233c167099c40619b09a03480d4000a994e12ec95cca1a4a121b0f506d230615189303c417a08902e00c2000a98ea12ee15f4a3e4b121d8f686e431815509283ce18809683300be000a988632ef95f4a264b42210f8070831c158094c3b817e08b82f00ba000a9820f2fb1648a664d8240105875a35317289b43fe19008f03200b4000a97bac3001640a5c4cb22f100873232c160095c40219409382f00c0000) else (if i < 104 then 0xac983f3049690a824e123a902474433716b099440c19a09b03300ce000ac92012ed15cca2e4be2290f806fc31f15989503c418309183100c4000ac8ba42fc162ca444bc22c8ffc73a33816789d040a19b09883380e0000ac856f2ec15b0a1a4af21e0f5c70232315f09904061a20a1837c0e6000ac7f2a2ee1614a3c4b422a0fc872432b16589703f018509103040b8000ac78ed2eb95c89fe49a21d8f786fe31915a89503da19309203240d4000ac72bf2e295a8a024ab21f0f6470630a15989283cc18e095831c0ca000ac6c6f2f515fca464c422e8fa870e31715108f43aa172091830c0c4000ac66572d815309e248f21d0f646e2307154090c3cc18109403100c2000ac5ff92fd1658a584bf22b0fe072e33a1658990400195097031c0bc000ac59c92eb15bc9fa49f21e8f646e830e15909303dc18308f82dc0be000ac53902ed15c4a044a12248f986fe315155892c3dc18e09103140da000ac4d4a2ed15c8a2a4ac22b8fb870432c16109843f6190099033c0c6000ac46fd2f415f0a204af2238f8c70a324160097c3fc19709903340ca000ac40b32ee95f8a304b42280fbc70a32515f894c3c8191092833c0e0000ac3a712e895aca104b122b0fe471a32d16309803ee18709183240c4000ac34382e815dca304aa2260f98702332163097c3e618509783100be000ac2dcc2ff1650a644c922e8fd072632c16089803e619109883100ca000ac276e2fa963ca544cf232903475633b16d89e842a1a509d833c0d8000ac212c2f095b09f849e2158f246ca31215a89183d818d09803240c2000ac1adf2f79604a264ac2270f8c70831b15a894c3e019909403000aa000ac14802ff9650a644ca22e0ff074434016e09c84221a109803180c2000ac0e472e995d4a224b222c0fd872432b16509643e218c09502fc0c6000ac07cb30596b4a844d6237101c74033a16c09b43fe1a50a103480ca000ac01b22db155c9ee49821b0f306e631415809503f81a309e834c0c8000abfb473039694a704d2237904474433b16b09e84241ac09f03400dc000abf4ff2f41608a504c622d8fb871a31615989383dc18b09483280c0000abeebf2f115e8a284b62288fb471e326165097040019b098831c0a4000abe8992e21588a044af2270fbc70631b15e89803ec1a009f034c0ce000abe2852e195709ec4942170f206ba2f714908fc3c218909102f40c8000abdc4f2ec15f8a304c122e8fe873c33816389543dc19a09803200c0000abd60a2ef95e4a244a42180f8471031515a89303d618308e02fc0ba000abcfcf2e5158c9ea48d2170f406e830d15509283e218808f82e80c8000abc9a12e1957c9f449621b0f286dc31115989283ca18608f03080ce000abc33c2fc165ca644d2234103875633816489583cc17f09303240ca000abbcea2fa9640a5a4c622d0fc872e32f15e893c3dc19609283100ca000abb68e2f99644a564d22348ff072232716409643e618809683280ba000abb026303968ca804db23a902074033116689843e219e0a083200ca000aba9ea2f19620a544c222d8fe471832415f097840e1a909e835c0e8000aba3c82e615aca0049d21b0f5c6e630915909183ca18108c02e00b8000ab9d882e795b8a184ad2270f8c70c32e15f89503da18609003080c6000ab97522e995a89ea4922178f246be2fa14c890c3c017908f030c0c6000ab90df3051698a7c4d5237102472e33116c09a840a1a109d03280d6000ab8a972f41648a5c4cb2358ffc72432c16089483fc19809b033c0cc000ab84642e61594a1a4a52228f586ee31f15a09703fc1a009983040ce000ab7dee30716a0a6a4d02360ff873432b16709bc4181a509e03440c8000ab77a22f39610a484c72328fdc71432216009543e618309203080ba000ab71542f1160ca3c4b722c0fe4726326161096840419809803440c8000ab6b0c2ef15eca3a4b522b0fa070c32916a09983fe19809283100c8000ab64e32e715a49fc4a921c8f846f431616509883ee19109603280c8000ab5eb12e4958c9fc49b2198f286dc31315b09543c418509103200dc000ab58652f99638a544c8233100873833616209a040019409582f40cc000ab52222ec15d4a1249e21d0f3c6c8309159892c3b417e08d830c0c4000ab4bc82fe1650a5c4d0236103075033f16a09984021a809e83280c2000ab45632fe9650a5a4ba22c0fb070e32515f098440019809a834c0e0000ab3f132f715fca124a92268fb871032215d09183d018109103180c2000ab38fe2da157ca0849b21c0f7870031e15f09583d017d09082f00be000ab32c62ee95e4a324aa2220f846ee313156092c3c418c097833c0d8000ab2c882eb95f0a3e4b92298fc472233116389803fa19309383340b6000ab263a2f61618a384c12328ff872833316689583e418f093830c0a4000ab20122e795cca0e49e21e0f506f830c15909183d419609482fc0c6000ab19b02fd1648a524ce2348ffc72632c16009703e819309c03600d2000ab13712ea15c0a0049c2178f2c6ce30315689303d217c08f03080b4000ab0d372e995dca204ab21e0f386ec31815509383da19009283140d6000 else 0xae29b82ef15eca224a02230f806f431015089003c418409683240dc000ae23732f81608a3e4bc2260fec71c32e16509843e4195097032c0d6000ae1d10302967ca804d5236104c74a33816e09e441e1a509c03000ae000ae16ef2dd15649e649e21f0f5c6f431315589303d018409003200be000ae109a2f81640a4e4b622c0fd871432615c09603d017509203080d2000ae0a542f4961ca3e4b62278fcc71e32d16809983fe19d09b03380ea000ae03e9303969ca724cf2371018728331166899c40819f09783300da000adfd9e2f7963ca624c32300ff872232515a89443d0185096830c0cc000adf7642ec95d4a164b32228f9470631c16389883fa19709a83440e0000adf12b2e795c4a0c4a72268fac71831715b09683ea19c09903200c8000adeaf12ec15949fc49621f0f546dc30415189143c218109503140c0000ade49e2f59628a504c22298fb070833416589703ee19209503200d6000adde622ec15f8a444bf22f8fcc70832215f897c3e819409803180ba000add8292ea95d4a404c42300fd472833616a098c4101a909e83480c6000add1e82ef1608a344ba232100c7503481740a0442a1a709c83640c6000adcba02ef15dca264b42270fa070632216189643e8190093031c0c4000adc5412fb1640a5a4cc233902474233816809904041a209a83480d8000adbf0d2f095f8a4c4c8234901474633e17109e04261a4099832c0d4000adb8cf2e715f0a2c4c522e0fd872633216309a440619909982f80b8000adb2902f015e4a2c4ab21f0f486ea30e15b894c3f4195099033c0d4000adac7d2d695549d247f20d8f046c030a15189003ba17d09003040ca000ada6183019640a6c4cc2320ffc72a32e16689c44241a509d836c0e2000ad9fd82eb15a0a004ac2210f9c70431815d09603dc18709483140c8000ad99852f31600a404b72260fd873633416809943f618808f83080c0000ad933a2f49620a4c4c32338fd471032016009643ec18b09683340c4000ad8d0d2e595789ea49c21b8f286d831315509283c617a08f83040d8000ad86e52e095789fc49e21d8f446e631616609984101a609e83540d2000ad808b2f8160ca3a4bf22c0f9c70231915e099440619409703280d0000ad7a3b2f215d4a2c4b92328fe872e336167898c3f219409683180b8000ad74082e8959ca0649f2218f9471a32615c895c3e818909583340cc000ad6dca2ef1604a2c4b12250fb470c32016089783ec19509b03340c8000ad678d2ef95f0a264ad2230fa070231f15f892c3cc18f08f02f40d0000ad61252fa9644a424b822a0fd872032a16109503f619f0a183680dc000ad5b022e495b4a244aa2220fa070232916209a04001a609983240ca000ad54cb2e915c8a0e4a921c0f446dc30814d08f03b017408a02e40a6000ad4e4430e96aca844e6239904c74a33e16a09b84081a009903580e0000ad48122e695dca2a4b52250f906fc30a15289283c617e08f03340d2000ad41d62f395f4a3e4b322b0fc871a33416589743dc18709183480d2000ad3b742f89634a4c4c5238101474233816d09fc4361a809f83300d2000ad35222f69624a584c6233100c74e34016b89d041a1a909e035c0f0000ad2f012dc95649e048e2110f106d630d15389203dc19009202f80b2000ad288b30e16c4a904d92358fe8740329163095c3e018809283280cc000ad22842cf14cc9a246f2058e6c68e2e714a88e03c817808c82e00b2000ad1c3a2eb95b8a2e4bd22a8fd472e338163098c40219909203140ca000ad15d03059674a6e4d0236901072633d16809c041e1a60a0835c0d0000ad0fce2cc14e89be47f20e0f0c6b82f814b88f03b217708802c00b4000ad09752f59638a684d7232900875034817589f44321b30a8839c0ec000ad03562da9588a0049d21d0f786f0318156892c3be17508b03080b8000acfd142ee95e0a224b42250f6c6f431a15789343e018e095830c0d6000acf6c52f315f4a244af22d0fc071432215e09804041a009d03300ca000acf0712f11610a1e4a12230fd470631515e89143d418509783480c6000acea302ef15a0a104ae21f0f786ee31615909643f019e099832c0c8000ace3e32f59628a444c022f0fd470e32b161096c3da19a09b834c0c6000acdd6c3021660a624c022d0fc070e31a15b89743ee19209682fc0ba000acd7392e795849d648b2190f146ce31115789403d618508b82ec0cc000acd0da2fc1648a684c022e0fac72232715e89943f619209a03600da000acca9c2ee15e4a184b32238f806f430f15588e43be17e09082f80be000acc4562ee15d0a1a4a52210f5c6e031015488f83b617b08e82cc0be000acbe032f39610a284b22250fa472032316489a841419f09a83200cc000acb7c12f59610a264aa2268fd471c327163897c3f419409283040b6000acb1ae2d915109d449921b0f586e631615b898040a1a109e03480ec000acab43305166ca704db2380ff071e32115e097441019e09f834c0d0000aca5062ea15bca2e4b42230f9070231c15e896c3e019509903500b6000ac9ead2f61618a284ae22a0fa470c32415709403e618c09783240d2000))) else (if i < 108 then (if i < 106 then 0xafbaa92ea95d0a0c4a32188f506ee31715a89283d618709403140ba000afb4642eb15b8a1e4ad2230f906ee31815c09543f419209583140b4000afae6b2ce94f49ba48720e8f1c6cc30b15589143d619209803400d6000afa8282ee15f8a324b02260fac71832816309803fa193099833c0c4000afa2082e315889f649821c8f7870832415c89803f2197095031c0d0000af9bc72ee95d0a284a92288fb071c32f16609843fe19e09a035c0dc000af95752f71614a484af2228f906f830d15909343d018c09203140d0000af8f232fb1650a664d02348fd071a32a15e095c3f819f09683300c0000af88d22f815fca4c4b922e8fa872232e169098c3ea193099833c0ca000af82672ff968ca864d7237102875233517109cc4101ac0a383540da000af7c352e695a0a1e4b02280fcc71632a16189683ec18809503100d2000af763d2c915049ac46f2040e806742db138886838c16b08802e80c2000af6fec2f39610a4e4bd22d0fd471031e15c89583e418d09483080cc000af69b32f4161ca4e4b92278fa06f631715589203d817f094832c0dc000af63612fa1630a3e4b62290fbc712324167898c3f419509303140c0000af5d2a2ec95eca2a4b22270fa070631915f89803fa19709a03540de000af56f02ec15a4a084952198f346da31515c092c3cc18008d83140c6000af50b02ec95f0a2a4a72240fb86fa31815e09503f419b097834c0da000af4a752e615a0a124a52258f986ec31015709143dc18709003440d4000af44282fa1634a584c622f0fe872432b16a89b44141a50a303680e0000af3def2e915f4a2a4ae2270fc872833016589743fe18e09302f00c8000af37a22f095f0a2c4b12290f9070231715709283c018509403140c4000af31632ee95f0a264a62248f9470231915a096c3de18e09983380b8000af2b082fb9650a584c42330fd871833416089643f018f09403180c4000af24bd2f195d8a324b82278fb870231115789103b217508e02d40b2000af1e7a2ed15f4a324b02240fa06f431115809343d618909283240d6000af182b2f41618a444b622a0fb470a32715e896c3ec19409483200d8000af11e22ef95eca2e4b42268fb870a327162096c40419809503300d6000af0bb42e795bca164a52200f506ec30b14e08b838a16b08782cc0ae000af05612f29618a404bd22b8fd473633016509703ec19009102f40c4000aeff162f21618a444b32270fcc71032615f09543d818b096032c0da000aef8ab30b96bca944e8244106876235416d899440c1a0096030c0be000aef2612f21604a444ba2288fcc71432c16709883fa19f09d83580dc000aeec102f49614a484c322c0fc471a32516109603e819509a83740de000aee5df2e49594a1a4ab2230f8c6f231e15f096c3e4195098032c0d2000aedf8c2f99620a4c4c52280f8c6ee31415909483f618e09382f00ca000aed9582e915d8a204a82280f9470c32616289a840619909403000b0000aed2e430916c8a844e023f104473834116909d042c1ab09983580ca000aecc922f8962ca544b62270f8871633115e89543d017c09182d80ac000aec6592ea95dca204a721f0f446f430514e891c3c618609203040c6000aec02e2dd95609ee48d21a0f586f231715689283e218008f82ec0c2000aeba082df15489ea4902158f286de31515809443d018309303080ae000aeb3a02fd961ca464ba2260fa070832a16589943ee18d09383040bc000aead5a2f195f8a364ad2258fac71432215c89583e0189095834c0e2000aea72a2e5958ca1c4b32298f946fe31815f89703e6195096031c0c8000aea0fd2e495aca124a42218f6c6fc323160096c3ec19109703300d4000ae9ac32ed95c4a2c4aa21d0f346ce30815a89743ec18e08f83000c2000ae944b30996b4a944e4241107c76c35217389bc41e19e09d83480cc000ae8e092f015e4a344b12230f9871231e15d09643ee19709e035c0e2000ae87e02dc1560a044a52218f746f2314158895c3da187093830c0b8000ae81982ea1594a124aa2258f8870a32215c895c3ea19409903240c0000ae7b372fa9654a684c7236101873832b16989903fa1a209c03380d6000ae74e92f81614a3e4b822e100473232a16089804061ad0a503a80e4000ae6eaf2ee15e0a2c4b22240f8c6fa31e15b09483d8194097835c0d4000ae683730816aca7e4dd239904476a34f17109c04161a109a03440cc000ae620f2e0159c9f849d21b8f1c6be2f614c08dc3ac17609083200d0000ae5bbe2f8961ca364b622d0fb86f431c15d098c3f819e09a03580e4000ae557c2f115e8a284ad21c8f606e630c153092c3e018a09903240b8000ae4f4b2e295889f248a2138ef06c22f815188e03be17908a82e00ba000ae48fd2f49608a444bb231100473232516609983e6197096834c0d0000ae42c12ee9610a444c12240f8c6dc30915309183d818709303200ca000ae3c7f2e8157c9f449d21f0f686fc31b15d09503ee19809583140c6000ae36482ee15c0a244a721f0f6c6ee30915489343c417e08b82d80c8000ae2ff72f61604a344b622c8fe474a33816709a03fa19009683400c0000 else (if i < 107 then 0xb14c012ee95c8a0e4a02220f9870631b15b894c3e619709682fc0ba000b145ae2fc9644a464bc22d8fd070832416109683ee19509503200c8000b13f762e815dca3a4b522b0fc070632015f89583e819a09b03440e2000b1393e2e415a4a0e4a32230f846fa31b15b892c3ec19809b03200b0000b132e92fa1620a3e4b82288f8c70231c15c89303f018d09603240c6000b12ca62ee15e0a2449521b8f5c6e031d15889283ce18809503280ca000b126762e3156c9f24a521f8f646de30714f08f83be18409483100ce000b120153001604a3a4c022b0fe0716323160095c3dc198097831c0be000b119e92e61590a0049e2210f9c708321161098c3fa19809783140c4000b113ba2e8959c9f64972160f406d4309151890c3b818809382fc0b4000b10d732ef95d8a1c4ab2270f8c70031d15a89703e619709b83540e8000b107412eb9608a4a4be2290fc071632815e09783f019109583080c6000b100f52f115eca2e4b32260f9470c31d164898c3f419a09903440c8000b0fabe2ef15e4a2e4c12298fd070631f157091c3ca186095834c0c2000b0f4772f49608a3e4b92298f946fc31b15a89883fa19509d03280c6000b0ee162fc965ca724da23a902c73e333166097c3ee19309083140ba000b0e7d92ef1600a3a4ae2250fac6fe31d15e093c3dc18e09483180c0000b0e1962f31600a444cd231901073033516609903f419309703380d4000b0db5f2ef15f0a404cd2360ffc72e33316209643e418c09883480c8000b0d50e2ef1604a3e4b02288fd071832915d89283ce189091030c0d6000b0ceda2ea95e0a2a4bb22a8fc071832a162899c3ec19209883400ce000b0c8872fb1660a564c722b8fa8704323160896c3dc186097833c0ba000b0c21330916c8a844da23510347643511738a0843a1ad0a203500e6000b0bbc02fb1650a504c62318fe471632616089b03f819c09b83480dc000b0b56f2fb9610a484c2230100873033216489743e819709a03280d0000b0aeff3051690a7c4c82340fe872e32b163897c3f219709b03180c0000b0a8c22e895b4a144a121d0f7c70432416089743e618c094832c0c8000b0a2812ee95c4a084a62218f746e831815609343e019709683200c2000b09c452ef95c0a164ab2270fd073233516709a841819d09c83540c4000b095e32fc167ca644cf236903c75634816e89a44161ac0a183600d4000b08f9c2f115e8a284bc2328fe073a33316b89c041019709203040bc000b089572eb95d4a164a621f8f7c6f031015189303d217e09203100c6000b083432d9150c9d64882158f286c82f614d88d03a216908802cc0c0000b07ccd308969ca7a4db23a105876c34416f09fc42219909683100b8000b076643001664a484c522e8fc871832315e09543f219009c83540ec000b070182f095f8a2e4b62260fa071432316409943fc19e09a03440c8000b069d32eb15f4a284b02290fcc6f831915a09543e219109583380c8000b063b42e49594a204a921d8f586f831815309003c018709783140ce000b05d622f4161ca2c4b822a0fe874033816009583c818608c82d80b4000b057242ef1600a3c4b22270fa870632815f09583da18f09983380d6000b050e32ee15d8a3a4be22b8fb870032115989143be18109003140be000b04a8e2f7162ca424b02230fa071232215f09503e418d09602f40c4000b044582ea159ca084ae2238f9c71831815a893c3e819a09283140d0000b03e2f2e7957c9f849b21e0f3c6d630f15a094c3dc18709502e00bc000b0380a2e015809fe49921e0f586e831115889583dc18c091031c0b4000b031cf2ec15a8a1049d21d0f586e831415388e83aa17708902d80c2000b02b832f295c8a2e4bb2260fb8712320164096c3f4198098030c0c6000b025382f495e0a2e4bc2298f8870232415b090c3d219109603340ce000b01ef82ed15f8a2c4b22238f786fc31e15c89643f018d09583340dc000b018cc2e695809f849b21e0f606f230d15c895c3e019409a831c0ae000b012802f19610a3a4b82280fcc70c32c16889d441819d09a83540da000b00c183029678a4c4bc2278f9c70e32216089743f018a096030c0d8000b005ca2f79600a484be2288fc071c32316289944081a009a83280be000afff623011644a604c12290fa06f832115e89583f018c09602f40b2000aff9422db15649ee49521b8f986f431815809543da18c09383280cc000aff3092ea95e0a224ac2270fe472432b16b09ac40419a09b03280ba000afeca72fd962ca504cc22f0ffc72432f16289743f0191096831c0c2000afe65f2f51608a384af2290fb871a32516889903f8190098830c0be000afe0282ea95c8a324bc2278f706e831215d09343d818509582f00b8000afd9ee2ec15f4a2c4b12260fbc71c320161092c3ce18109102c40b2000afd39d2f39600a2c4b82268fe471a33116909c03f818d09603200d4000afcd782e315a0a204a72248fc071632716089543e2196095030c0cc000afc7372ee15f4a244a92220f9c71a32315a89203dc18909202e80b0000afc0de2ff1674a664c52310fe072032d160095c40a1a509703100d4000 else 0xb2dc442f115d4a3a4c522b8fd071832115c89503e019009503180ce000b2d5d83039674a684ce2331010722329162096c3ea19b09c03640da000b2cfbe2e015549fe4932190f246c230614e89043c018c08d82e80bc000b2c93b3079658a604cb22f8fd072032a15e09483cc18308f82f00c4000b2c3012ea15cc9fc49a21e8f6c6f431315c89583ea19809b03040bc000b2bce32da955c9f64992188f386f231915c09583f0195098033c0e6000b2b6b82e695c4a0a4a021f8f686e630114b89043bc17408b02f00b6000b2b08e2e415789fa4912140f0c6d02fb15089003cc17d093832c0c8000b2aa5c2e315849ec48c2190f5c6f231715f094c3ea19709903340bc000b2a3f72fe9664a6c4ca2350ff071833116609d840e1a40a183640dc000b29dbe2ed95f4a324b72288fc871031a15a89443e018e09783400d6000b297752f59628a524c82318fec74633516689943e818e09b83480d4000b291162f89654a644c122c0fc070832216189803f0184096031c0dc000b28b012d795589fe4a92208fa070432215f094440619b09d03680d8000b284ce2ee95b0a044a321f0f806ec31715689203bc17e08d82e80ba000b27e9c2ed95e0a224b122a0f986f832216189784021a209f834c0d4000b2784a2f4161ca344a021e0f546e630e15489143c017808b02fc0b0000b272462d495049a647f20d8ee86c22f814d08c83a818008c82e40ba000b26bf32f49618a364ae2280f9c70232316089503ea19809a832c0b8000b265803031670a7a4d1239103475034217109dc42c1a60a003500d0000b25f532e795bca084ae2280fb871232616189483e619009683180b6000b2590f2ef9624a404c422e0fec73032d16989683d818609283100b0000b252c02f8963ca684c52300fcc73432b16409883fc19b09b833c0c4000b24c7d2eb95b4a084a22250fc871c33416889c040a196094832c0cc000b2464b2ee15cca104a821d8f506da30e15609143ae17808d83080c8000b2401d2e715c0a224b22290fa472432c16409703de18d09503200c6000b239cd2f595e0a204b62298fa46f831015189203b417b092830c0c2000b233772f7163ca664c9234100c74233c16609a43f618d09803500d4000b22d1d2fd1630a5c4c52308fe471633316009803dc18e091833c0da000b226e82e815c8a184ac226900473434216789c04061a109883100c2000b2209f2f61608a4a4cb2320ff873433716909c441c1a40a203200ca000b21a3e2ff16a0a724d2232900c732323160898c40019909282f80ae000b214002f015f0a2e49e21b0f8c6ec30d15d09403d418509482f40cc000b20da42f89638a5a4c02290fc871c32916689c04241a30a2037c0e8000b2075f2f59640a624c422f900073432b163097c3f4199096832c0bc000b2011f2ec95d0a1a4aa2200f806f431115789303ba17908d02d00bc000b1fae52e815c4a0a4a22208f746f631c15f896c3f218c098032c0c4000b1f4853039678a744da23c901874e33f16a099840619909783300d2000b1ee5d2e49580a1449d21a8f486e630a15489243c218609182e80b6000b1e7ef30716aca8e4cf2310fd071231a15e89543ea19609a83580d2000b1e1972f4960ca2e4ba2218f88702321162095c3dc19909703080c4000b1db852da152c9e44902168f106b42f814a08c83aa16f08c02ec0c4000b1d5442e915aca0a49f2198f4c6ec31915b896441219d09702f00ca000b1cf0e2e715e4a344aa2250fc070a31915e09883da183093031c0c8000b1c8d62e115789fe4a021d8f446ec31215308e83ac17809383080be000b1c28c2fa1658a624ce2300fd071c32315c09683dc18009303200c2000b1bc4f2e715a4a044a72278fa070631e15e89143d418709283040be000b1b5f82f71618a464c722f100073e331167098840019c09983580be000b1afb42f215fca244aa2218f7c6f231315c09283d618609583100c2000b1a9712f31620a424c222b8fcc72433216609b44101a2099033c0cc000b1a3392ea15b4a144a62218fa46fc31e15f89503e019009083000c2000b19ce52f89658a524c52300ff472832316789783f41a309e83440de000b196c12e195b8a1a4a32200f646f830b15489283c818108d02fc0bc000b1907c2f31630a424af2278fb8714324164098c42019409a83440d0000b18a652da153c9ea49c2170f3c6ec30715109003be18008c02e80c2000b1840c2fb1680a684cf230100872a33b16889903f019009883480cc000b17da23041690a8c4e023a101073a33d16e09a440618f09a83380cc000b1777e2e0158ca0649521d0f546f631b16009543e619a09c03500d8000b171522e995cca064a321d8f606ec32115b895c3e017e090830c0ce000b16af13011678a524c322c0fd072832a16309843fc18909582f80cc000b164bd2ed15f8a204b12278fd071a32215f099040419109b03200c2000b15e9d2de95709f249321d0f546e231315e09343de18408f03000c2000b158752e215a0a084ac2258fc471632416389703e218b09583240d0000b152362e595d4a324ba2280fbc71e33215e09443de198098830c0c6000)) else (if i < 110 then (if i < 109 then 0xb46c233001658a544cb2310fe071832b161097c3ea196094831c0c2000b465fc2e515d4a1c4b922f0fd06fc31a15e896c3f619d09683200cc000b45fc52f1960ca204ae2250f7c70032615f09683de18e09903400c4000b459722fe9644a4a4be22f8fc4716334162898c3ee18b09283080c4000b4533c2eb95eca3e4c22270fb471c33116789983f819a09783300d2000b44cf42f115eca3e4c42309014742331165096c3e81a00a003480ce000b446ae2f3160ca4e4c92310fc071632816389a83e0190091832c0d0000b440642f295d8a1249d21c8f5c6ce31115509343be18409183080c6000b43a222f095e0a3c4b62238f9c70e31e161095c3ec18f09283100dc000b433f62e895dca2e4b12278f9070632416009743ec18a09683240c6000b42d933029688a624cf2308ffc73032a16009583ee19909d03580ca000b427642ed95f4a5a4c322d0f9c71033516709b04141a209b03540de000b421152f71618a2a4be22e0fd471032a16389803f819809503140d8000b41aec2de95649f649921e8f4c6ec31615d89583e018609202e40d2000b414872fd1660a764ca22f0ffc74033716509cc41a1a009d83500d4000b40e4a2f115d8a304a221e0f546f231a161098440619a09703300d0000b408182eb95a4a0249c2220f6870031c159094c3e619209183180ca000b401d72ee1610a384bd2298fd471631c16109743e618f09803200da000b3fbca2d695489e248d2118ef06a22fd15008cc3b618008b82d40ba000b3f57f2f6161ca324b922e900873233a17189bc41819f09c83540d6000b3ef412ed15e0a044a82220fac70631b15c892c3c618309082d00a0000b3e9222de956c9fc4a32258fc071632915e896c3f019509d032c0ca000b3e2ff2dd1588a084a921d8f546d831415d09543e618509283140ce000b3dcb92f49604a424c522d8fc8710322160896c40019d09b82fc0c4000b3d6952e315809f249621b8f386d030715209283cc17e08c02cc0a6000b3d05b2e915c8a1e4ab21b8f3c6da319164098440219909a83780e2000b3ca292e515a0a224a821b8f7c6fc31b162098c40819709a833c0e2000b3c3d02fb1640a424b92330fec72232c16789783ea18b09483380d4000b3bd872ed95dca2a4b12280f946ee31915b09383c818408e82ec0b8000b3b7552ed15e8a364b62288fa070832116189984161a109a82f40bc000b3b1022fe1650a4e4c62300fd872632b16589b43fe1a109883100d4000b3aabf2f3961ca4a4c72280fa870632015989583f019609603080b6000b3a48a2ea95b0a204af2248fc070c31915f896c3fa19809683000ba000b39e3f2f415d8a144ba22f0fd072433216589a43f619109883040b6000b398122e295989f649621f8f5c70032015a09683d617d09103000ba000b391c12f79630a3a4c22310fe072a333163897c3f219f09f03500d2000b38ba12e11574a0a49b2200f9470231815d89603e618709803200c4000b3856d2ec15f4a224b822d8fbc72232d16689a03f819a09c03140d6000b37f102f69620a264a621d8f8070831515e095c3de19309583140be000b378d42e995bca184ab2188f546e631515c894c3d018309182ec0b0000b3729a2e815c0a144b42278fa470c32015b095c3dc189090831c0bc000b36c502f115d0a144ad2258fbc71031d15e897c40619b09983580da000b365f42f79618a344c22328ff871831e15d098c3f019a09783180c4000b35f8c2fc9660a624c4234103074e33316a89c44321af09c032c0b6000b359582ec95bca104a921e0f786ec309154892c3c618009483000c2000b352d8305169ca784d3237100472c33a16989ac4021a00a003740ca000b34c9d2ef15c0a1a49f21c0f546dc30d14d88f43bc17a08f82cc0b4000b3466e2e595809de48e21c8f686f631615c095840219d096831c0ba000b340402e49598a0849721c8f406e0310156892c3c018009082f40c2000b339ef2f415eca224b522b8fa870c31b160095c3da193099835c0ce000b333cb2e095b0a304b12230fb871c32916409b442e1aa0a503440d8000b32d942e71590a124a02200f406c630815589343ce17d09383080cc000b3277d2da95609fe4972198f546d831215789343cc17f09183180cc000b3210b3031680a664cb2340fd871833516989a44041a309b833c0e2000b31ad02ed15d8a2e4b522d0f9c70632b16209c040c19d09b83500d0000b3148d2f115f0a4a4b62280fac70031c15689583e418c09582e00c0000b30e6a2db958ca0249c2200f686e830f15589303ce17d09283180b8000b308222f195f4a384b62298fcc71c33916c09e04141ad0a103680d6000b301c72f91614a3e4b62288fb072233116889bc41e1a309f83340be000b2fb712f39604a244ae2258fa46fe31715a09383e019109983200d2000b2f5332eb95aca1449821d0f5c6ca2fb14f08e83b617608b82e40c2000b2eef92e99598a0a4a92258f8c70032915e095c3d018609003080ca000b2e8c42e0157c9f849f2180f646ee31a157095c3de18a09583140c6000b2e28b2ef95e8a2c4af2278fbc71e32916309743f218f09083080a6000 else 0xb5fd293001680a764d62419058758335167897c40019709d83540de000b5f6e62f3161ca404b52290f886fc32316489883f419309f034c0ca000b5f09d2f515e4a304ae2260f8c6e430b15389103d018909283040ac000b5ea622eb15a09f44912168f506e231115d09483ca18809183140c6000b5e42d2e895cca204a821f8f746d630b15689143f019609603200b8000b5ddd42fc1660a564da239906875434417389d44201a309c03240b8000b5d7b22e395549f249420f0f086c62fd14d89243c619209883400cc000b5d15f2f59608a364b02290fc471a31916109803f019309583180c6000b5cb082f69618a444bc2298fb870a31d15e89603e818e09282fc0c2000b5c4af2fa1664a4c4b62268fac70a32515c892c3e218709182fc0c2000b5be762e915b0a064932168f106c630914e890c3ce18409703100c0000b5b8252f71638a3c4b52240f9471232815f899c3fa19a09e83500de000b5b1f92ee1614a4a4b42298fd871432716309883f618f09703200c8000b5abb22ef95f4a244b42270fbc70c30f15809243b818108982c00b8000b5a5672f6961ca3a4bd2268f886f231215709583e018b09182cc0aa000b59f422e015749f849d21a8f686de30715089203ba17b08c83400d6000b599092ef15dca344b522b0fa070232015b09443ee19a09b83540de000b592d52ea95b8a1e4b12230f6c70c32a16489643e218e09b03100c6000b58c802fd1640a5c4cf235102874233016509883e018e09683300d4000b5863b2ef15cca1e4b02290fa871c32d16889a440019109383140c6000b5800a2e49570a084ab2240f9c6f832115b892c3be17f08f82f80b6000b579d82e815f0a224af2240f88700312157893c3da19609603180bc000b573ab2e015909ee49921c8f446d430215009043c4187098031c0bc000b56d592f7963ca664cf236900873c33916809903e619c09903400d2000b567292e295749e649321a8f5c6d430915b89543d218809883380c2000b560dd2f31600a384ab2268fb070432715b89303e218f09283140c6000b55a962fb9638a5e4cb236101473833616689883fe19f09c03380da000b554632ea15c8a0c4a12200f5c6e031515c89583da18209283380cc000b54e2a2ea95cca044a42258f9470632515c095c3e618c09283240ce000b548182d795289c648b2168f486e630d15709183c018508d02dc0c0000b541d72ed95c4a324b32248f746ee314158095c3de18609603200c8000b53b5431016e4a9c4ee241103c74633416309b04241a809c83480ce000b5351e2ec95f0a2e4b92300ffc73232e15d89703f619409b032c0e4000b52ed12f49620a384bf22e8fd872032815c896c3ea18f09782fc0b6000b528842f31608a584b52298fc871a32815e89743e818a09b033c0d2000b5224a2f295f8a4c4c9237103872e33b16a09ac40e19c09583440c8000b51c092f195fca324c6233900073633416a099c3fc1a109683340c0000b515c22ef95f4a284ab2238f7c6da30715509243d018409303000bc000b50fa12d795189be4802148f006c430715489203cc17b09103200c8000b509322fe1650a5c4cc2308fe073233a16d89c840c19a09883580ea000b502e92f09618a3a4b72280fa8726331168097c40c19f09b833c0da000b4fc8c2fc1654a5e4c02310fd471432b16409983f819309703080b6000b4f6462f41624a404b622b8fdc73a33716809984261a509b833c0d0000b4effd2ef9620a3a4b72288fb470632416009283c2185096032c0d2000b4e9da2de95849f64a52228f8c6fe32a15f89443da19109983300be000b4e37a2fa1628a5a4c72300fd071a32615c89503dc18009182ec0be000b4dd173009648a5c4c222a0fa06ea30915a89543da18708e82e80ae000b4d6d62e815a4a0a49f21d0f5c6f232015a89403e218809583140cc000b4d0862ec95fca364c122e8fe872e33116309643de18c09003200c6000b4ca4b2eb95dca344b32278f946f432315d89583fc19709783200d8000b4c3ee2f49648a4c4c92318fd472432d16a09943ea19409703480c8000b4bd81302167ca804ce22e8ffc74033615e89643e619609583500ca000b4b73a2ef1618a464c322d8fe472a33116c89c84221aa0a083640e4000b4b0ea2fe9604a4a4cc233102075a34317289e04221aa0a383440b8000b4aaa22f29624a5e4bd2310ff071e32115e09643dc18408e83040bc000b4a4612e995aca0049b21d8f6c6e431715b09383d818509082fc0ca000b49e252e515c4a224ab2220f686f431815889283cc187097031c0c8000b497f92e49590a124a32218f8071232916989b04281ab09e03740ee000b491a12eb95a89f849821d8f5c6d82fc14d889838616708902bc0ba000b48b642ed95bca284b02248f8c70c32015b89503d817a08b02ac0b4000b485172f295e0a1e4ae21a0f146e030c157097c3f618909002f80e2000b47ee02e815c0a144a52218f786f231d15c89543ee1a009983300ca000b478892f71640a544cb22b8fdc71833216a09d04241a50a1837c0dc000b472862d015289c84872158f106e030b15889343ca18809102f00ba000) else (if i < 111 then 0xb78cf52f31604a424ba2258fa871a327161896c3ee18c09503280d8000b786a32f5161ca544bb2240f9471832315b89643d618f09b83580e0000b780552f115fca284ad2290fac70031715c093c3d818b098833c0d2000b77a172f095eca304b22220f9c6fa31a16209783f218d09803340cc000b773a83031660a7a4c722c8fc871833416409983fa19e09883480da000b76d3e2fe1658a5c4d4235900472a33416409883ee18509303140ce000b767162e11590a0449e2198f446e630f15509283e618d08d02f00be000b760db2ed95e8a2c4a121c8f646c430215789343c417808c82c80bc000b75a9a2f195f0a4e4bf22c8fa470a32015b89243cc18c09183200b6000b7543d2fc1628a3e4c222e8fec73633416a099440c18e09382fc0ba000b74df92f2962ca564c82348fe873433516709ac40a1a309883300ca000b747aa2f415d4a284af2290fc072a332160094c3ea18e09683200c8000b7417d2e615909ec49521b8f646ea31515d89703f818609503300c2000b73b612d895409cc47720e0eec6c030414f09103ce19109702ec0b2000b735562d1951c9d44872148f186cc30415489483de19209883280de000b72efa2f51624a564d623d106074833a168099040619d09a03580de000b728d42dd95709e84912188f0c6e630d15709343d818509203080c4000b7225f3021668a4e4c922f0fec72c33316d09e44281a609a02f80ac000b71c252f11608a2c4ad2238f9870c31c15d094c3d418309983240be000b7160d2e1158c9f649721f0f6c6f832216489844081a409d03440c8000b70fda2ea95c4a0e4ab2230fc472633016a09cc41219b09903200c8000b7099f2ed95d8a3a4c022b0fa86fc31715a89483da18d09002f40d2000b703682eb15e0a244a32208f5c6fc319159892c3d618309383300c6000b6fd372e595609fa49c2200f706ea31515789443f219909d833c0c8000b6f7202dc957c9ea49a21c0f506de31615609283ec18c09382e40ae000b6f0ee2ec95c4a104a62238fa070a31c15e09403ea191095032c0be000b6eaa72f11604a2a4b42290f9870831b15b89603e819909583280c8000b6e4742e915c4a1e4af2258f786f231615889243e618e09b03440d6000b6ddf83069698a904e023c901874232f16889c041c1a309f83440d6000b6d79b3059680a804d5234101473e32f16489c840819309402f00b4000b6d1642e715b4a304ad2280fac70431b15809443cc18c094031c0c0000b6cb122f495fca284b622e8fbc70831b15e09783f219809383080cc000b6c4d82ea15d8a304b02220fb070c31a15b09383e618f093030c0bc000b6be872f21608a404b02298fdc72432315c895c3e219609383100c8000b6b8432f115e0a224ae2200fa470431515b89503e018b091831c0b8000b6b1f32f61634a644ca2320ffc72e330165098c3fa18e09403200b8000b6aba92f51640a544c72310fd873232a164096c3dc18b095033c0c0000b6a56f2ec15e0a184a92240fa071233116489b041e19a09403200ce000b69f2b2f19620a464bf22e0fcc70a32616289743e618b09303000b2000b6990a2e195909fc4a72230f9470832415e09903f218f09503040ac000b692ce2e995dca124a62230f9071031e15d09543d819109803080bc000b68ca62e215709e64922150f1c6c830515389083ae17b09082e80c6000b6866a2eb95e8a1a4b62270f9870631915d89783fe18e09983400cc000b6801e2f31604a3c4b92270fc072a32a15f89383ce18d09403000ba000b679cd2f415e8a224ad2238f646f831415a09883f219f09a83300dc000b673862f6960ca344b722a8fb870031615208ec3b017808882ec0c0000b66d562e415609ee4912108ec469c2e614488c43a017508782a80ac000b6671a2ed95dca224ac2290fbc71c33016089603e018b08f02f00ce000b660ca2f5160ca404ba2329000732339166899c40a1a109a03380ca000b65aa52e7159ca0049a21b8f286d630b15509143b416f08a82e00ba000b6547e2e015a0a1449a21b0f606ee30e156091c3c217708e82cc0ae000b64e242f7963ca464c122e100c73e33616a09a04101a309b83480ca000b648292d194f89a446e2020ecc68c2ed14988c83a617308682d40c0000b641fa2e19590a0049f2168efc6a82f414e08dc3d218a08d82e80b0000b63baf2f0160ca544c922e8ff072831c15a89743fa19509583100da000b6356d2f115fca424b92278fb870a31715f89583e619109703180da000b62f392ea9580a024992198f546c630215789243e419209682f40cc000b6290a2e895d0a2c4b42220fb470832415d89583da19809903340da000b622cd2ed95eca2a4ad2278fb871232616089803f819909a83480d6000b61c51312970cab04ed240106076e34516f89dc41419809d03500e0000b6161f2e195b8a0a4a521a8f3c6ec31415d89603dc18e09503100c6000b60fef2e615b0a104a62268f886fa30f15909343c418609303140b6000b609c12e515a4a0c4a92268f9870e32315b893c3da18c09403080b8000b603892e995a4a224b32278fa46fc31e15a89803fa199099031c0c8000 else 0xb8f69b0000000000000000000000034d17409ec41619f09f836c0d8000b8f06b2ec95e4a1a4a22268fcc71032416409503d218608d02fc0ba000b8ea1d2f71670a6e4ce2340ff873433016489a040a19e09b832c0c6000b8e3f52e195bca224b622c0fb870c32415f897c3f419009302fc0d6000b8dd9a2fe966ca6c4d3236901874233616589bc40219b09703200bc000b8d77b2dc1568a024982200f9471832415f89643f018d09483180bc000b8d1602dd1574a084a521f0f5470230a15008cc3bc17c08d02e00ae000b8cb292ec95cca0c4b12290fac71c32b16889a84121a209983500d8000b8c5092df9588a144a72258f9471832c162098040a19a09803080c8000b8bec72ec95d8a224b12250fc070632616109703fc18e09783380d2000b8b8832f7962ca524be2270f7c6ee30815589183d618709282f00c2000b8b2392f49608a284ae2270fbc6ee30615609383da18909082e00be000b8abf22f11610a2c4ae2268fb870a32415f09743e018e08f02dc0ba000b8a5c42e915c0a204a92230fa86fa31e15809283d818709283040b6000b89f862eb95d8a2c4a82258fbc70232516309743da18609003200ca000b899472ed15d8a2a4aa2248f9871631f15f09503f218e08982d00c0000b893152e715b0a0449d2208f706e030e15108e03bc18209183200b8000b88cb030216a0a6e4e123d101472a32616209843e618d09703340c4000b886892e2958ca0c49c21f0f546f031415689183d417e08e82fc0c4000b880452e5158c9f649221a0f406e8312155893c3dc19109a03340c6000b87a292e015689f449c21e8f786f431c15c09203d018608f031c0ca000b873f62ed15c0a184a12240f906fa31815609243d217208b03080c6000b86dbe2e995c0a304b82290fac72432e15f098c3f618f09303400cc000b867772f095f8a3c4ac2220f8071432a16389944041a409c036c0be000b861202f895e0a264b12268f986e431a15b89483d618609983380d4000b85ae12f39608a3a4c022e100072c33216709d041e1ac0a103600da000b854942f59610a464b82310fa471632916009783e618408f03000ba000b84e652e315949f249821a0f846f432916289843fe18d09503240ac000b8483a2e3157c9fa4a22200f646e830e15609403d418809583200d8000b841f02f31610a444c222d0fec73633816609843f619d09b03180c6000b83ba42ef95e8a144ad2298fc870431f15609103ac16408602f00b8000b8354b2f9162ca3a4c522d0fd872c32f165098c3ee18b09683340de000b82f172e895b4a0449b21e8f706d630f15c09303e618e09303080cc000b8290b2d6152c9d447e20d8f0c6cc312156892c3ca18509283140bc000b822bf2f615fca324ac2218fa070a328163895c3ea18e08e03140c2000b81c513011658a684d12348fec72c33116309883f4192096833c0da000b8161f2ea95a0a0a4a22220f8070831a15b093c3ce17d09083080be000b80fef2e695a0a0e4a221d8f246cc2fb15008f03b217608982f00c6000b809962fa963ca4c4c7234902473234216c09d041e1a109c83440c8000b803522e895bca324b52270fb072032c16489843f419e09b03140ce000b7fcf32f99604a404b92228fb8714323162897c3e619708f83080c8000b7f6c72e495a49f24962160f646ce30214f08f43c418209283240cc000b7f0862ed95aca0049721f8f686fc31d15609243ce18209383200e4000b7ea4c2eb15cca264a62250fa46fe31515b89503ec19309603200ce000b7e4022f1961ca5c4c622d8fe072c33716809a44161a809b83240c2000b7ddcd2e795b8a1a4a72220f7c6ee31815989303d819109683100c0000b7d7762fb9640a4a4c62338fe072a33316809b04081a009e832c0d2000b7d1332ef15eca344b12298fa06f632115e89603f818b09503340dc000b7cb1e2da15489fe4a22228f9870832916309ac41019f09b03480d6000b7c4ea2ed95cca204a221e0f6c6f030d15789383e619009583380d0000b7bea32eb95dca2a4b02278fac70431e15e09503ec19109802f80bc000b7b8812de155c9e248c20f0ec06a82f715008d839a17208502c00a4000b7b24f2eb95f8a144a32218fa071031d15e09383d018909683200d4000b7ac022f81630a5e4c322b8fd072433016589984121a509d034c0d4000b7a5e32d9151c9c64782158f446da30015589603f019909983200c8000b79fbe2e415e0a3c4bb2258f9070232415e093c3d618308e02dc0a6000b7998e2e69594a144b12218f9c70431315789343da18408f82f40b4000b793462ec15bca204a721f8fa070631e157094c3f219809903440d4000)))))))

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



private theorem b101491 : covered 101491 101603 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b101603 : covered 101603 101715 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b101715 : covered 101715 101827 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b101827 : covered 101827 101939 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b101939 : covered 101939 102051 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b102051 : covered 102051 102162 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b102162 : covered 102162 102274 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b102274 : covered 102274 102386 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b102386 : covered 102386 102498 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b102498 : covered 102498 102610 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b102610 : covered 102610 102722 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b102722 : covered 102722 102834 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b102834 : covered 102834 102946 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b102946 : covered 102946 103057 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b103057 : covered 103057 103169 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b103169 : covered 103169 103281 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b103281 : covered 103281 103393 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b103393 : covered 103393 103505 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b103505 : covered 103505 103617 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b103617 : covered 103617 103729 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b103729 : covered 103729 103841 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b103841 : covered 103841 103952 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b103952 : covered 103952 104064 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b104064 : covered 104064 104176 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b104176 : covered 104176 104288 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b104288 : covered 104288 104400 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b104400 : covered 104400 104512 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b104512 : covered 104512 104624 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b104624 : covered 104624 104736 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b104736 : covered 104736 104847 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b104847 : covered 104847 104959 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b104959 : covered 104959 105071 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b105071 : covered 105071 105183 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b105183 : covered 105183 105295 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b105295 : covered 105295 105407 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b105407 : covered 105407 105519 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b105519 : covered 105519 105631 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b105631 : covered 105631 105742 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b105742 : covered 105742 105854 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b105854 : covered 105854 105966 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b105966 : covered 105966 106078 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b106078 : covered 106078 106190 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b106190 : covered 106190 106302 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b106302 : covered 106302 106414 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b106414 : covered 106414 106526 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b106526 : covered 106526 106638 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b106638 : covered 106638 106750 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b106750 : covered 106750 106862 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b106862 : covered 106862 106974 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b106974 : covered 106974 107086 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b107086 : covered 107086 107198 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b107198 : covered 107198 107310 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b107310 : covered 107310 107422 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b107422 : covered 107422 107533 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b107533 : covered 107533 107645 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b107645 : covered 107645 107757 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b107757 : covered 107757 107869 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b107869 : covered 107869 107981 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b107981 : covered 107981 108093 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b108093 : covered 108093 108205 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b108205 : covered 108205 108317 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b108317 : covered 108317 108428 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b108428 : covered 108428 108540 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b108540 : covered 108540 108652 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b108652 : covered 108652 108764 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b108764 : covered 108764 108876 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b108876 : covered 108876 108988 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b108988 : covered 108988 109100 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b109100 : covered 109100 109212 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b109212 : covered 109212 109323 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b109323 : covered 109323 109435 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b109435 : covered 109435 109547 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b109547 : covered 109547 109659 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b109659 : covered 109659 109771 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b109771 : covered 109771 109883 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b109883 : covered 109883 109995 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b109995 : covered 109995 110107 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b110107 : covered 110107 110219 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b110219 : covered 110219 110331 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b110331 : covered 110331 110443 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b110443 : covered 110443 110555 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b110555 : covered 110555 110667 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b110667 : covered 110667 110779 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b110779 : covered 110779 110891 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b110891 : covered 110891 111003 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b111003 : covered 111003 111114 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b111114 : covered 111114 111226 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b111226 : covered 111226 111338 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b111338 : covered 111338 111450 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b111450 : covered 111450 111562 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b111562 : covered 111562 111674 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b111674 : covered 111674 111786 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b111786 : covered 111786 111898 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b111898 : covered 111898 112009 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b112009 : covered 112009 112121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b112121 : covered 112121 112233 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b112233 : covered 112233 112345 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b112345 : covered 112345 112457 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b112457 : covered 112457 112569 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b112569 : covered 112569 112681 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b112681 : covered 112681 112793 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b112793 : covered 112793 112904 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b112904 : covered 112904 113016 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b113016 : covered 113016 113128 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b113128 : covered 113128 113240 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b113240 : covered 113240 113352 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b113352 : covered 113352 113464 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b113464 : covered 113464 113576 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b113576 : covered 113576 113688 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b113688 : covered 113688 113800 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b113800 : covered 113800 113912 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b113912 : covered 113912 114024 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b114024 : covered 114024 114136 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b114136 : covered 114136 114248 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b114248 : covered 114248 114360 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b114360 : covered 114360 114472 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b114472 : covered 114472 114584 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 101491 114584 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b101491 (joinCoverage b101603 b101715)) (joinCoverage (joinCoverage b101827 b101939) (joinCoverage b102051 b102162))) (joinCoverage (joinCoverage b102274 (joinCoverage b102386 b102498)) (joinCoverage (joinCoverage b102610 b102722) (joinCoverage b102834 b102946)))) (joinCoverage (joinCoverage (joinCoverage b103057 (joinCoverage b103169 b103281)) (joinCoverage (joinCoverage b103393 b103505) (joinCoverage b103617 b103729))) (joinCoverage (joinCoverage (joinCoverage b103841 b103952) (joinCoverage b104064 b104176)) (joinCoverage (joinCoverage b104288 b104400) (joinCoverage b104512 b104624))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b104736 (joinCoverage b104847 b104959)) (joinCoverage (joinCoverage b105071 b105183) (joinCoverage b105295 b105407))) (joinCoverage (joinCoverage b105519 (joinCoverage b105631 b105742)) (joinCoverage (joinCoverage b105854 b105966) (joinCoverage b106078 b106190)))) (joinCoverage (joinCoverage (joinCoverage b106302 (joinCoverage b106414 b106526)) (joinCoverage (joinCoverage b106638 b106750) (joinCoverage b106862 b106974))) (joinCoverage (joinCoverage (joinCoverage b107086 b107198) (joinCoverage b107310 b107422)) (joinCoverage (joinCoverage b107533 b107645) (joinCoverage b107757 b107869)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b107981 (joinCoverage b108093 b108205)) (joinCoverage (joinCoverage b108317 b108428) (joinCoverage b108540 b108652))) (joinCoverage (joinCoverage b108764 (joinCoverage b108876 b108988)) (joinCoverage (joinCoverage b109100 b109212) (joinCoverage b109323 b109435)))) (joinCoverage (joinCoverage (joinCoverage b109547 (joinCoverage b109659 b109771)) (joinCoverage (joinCoverage b109883 b109995) (joinCoverage b110107 b110219))) (joinCoverage (joinCoverage (joinCoverage b110331 b110443) (joinCoverage b110555 b110667)) (joinCoverage (joinCoverage b110779 b110891) (joinCoverage b111003 b111114))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b111226 (joinCoverage b111338 b111450)) (joinCoverage (joinCoverage b111562 b111674) (joinCoverage b111786 b111898))) (joinCoverage (joinCoverage (joinCoverage b112009 b112121) (joinCoverage b112233 b112345)) (joinCoverage (joinCoverage b112457 b112569) (joinCoverage b112681 b112793)))) (joinCoverage (joinCoverage (joinCoverage b112904 (joinCoverage b113016 b113128)) (joinCoverage (joinCoverage b113240 b113352) (joinCoverage b113464 b113576))) (joinCoverage (joinCoverage (joinCoverage b113688 b113800) (joinCoverage b113912 b114024)) (joinCoverage (joinCoverage b114136 b114248) (joinCoverage b114360 b114472)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 101491 ≤ index 195000000/512 := by decide +kernel
private theorem starting_value : fast 195000000=10817577 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 195000000=10817577) (n : ℕ) (low : 195000000≤n) (bound : n≤220000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=195000000
    · rw [first,anchor]
      exact starting_value
    · have past : 195000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤220000000 by omega)
        have within : index n / 512 < 114584 := by omega
        have lower : index 195000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤220000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ195000000To220000000
