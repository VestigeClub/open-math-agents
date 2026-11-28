import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ145000000To170000000

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




private def radical : ℕ := 0xc9e78fe6a49be8ed5a2d27bd5089866b0f06ddfa8c44cb4475c513ff3c8d641d4cd95599b719617f2db550adf8d4e57c1e90f9541404715603f8738ee9e31b02852ade191d066333b1db8fcbd59ac271ecfe8de9aaa3f3c6bc744150d7d23180cf474ac126ee1fd70552f50d441389f57046479e48811ab278bd6bc9327bc8ff0c68a7ec52d2fdfcff1d7400e4e748c49a5f76a68ca102a82aab888fbd58b86fcd29eb12e95d59399a488557565b355bf87643eae2e2eab61fa9cf09143af43725db9abe2dd3ec1d7d70b26632fbe67a31ac58eb2cc1d4e5907c138d9ed8e893abf1bebd3164dc0ba607c96ab4586bdaf9873e3156500d97cc1ba44ac464931da5f1ed28c83b964540c5684c9dcf1c07de0dcb59217df20ce14b750d8e67dc11bc403b49a30d67c639b52b4a7a6fb43c68ae23807eb6ff9fc7ea086d7b96c3e4f4f0ac9b1f7fca1f7d8d5cf9821582bed282785d9d4c83c92e28e56cee9bf5e4c7c5564e4200d0c38599c8786caed88f060c484a383926273415f31d51151c1c15c396133cca41607d84cdca11a7fea97edd07e2a70ff5063795b80892a95d1f3eb5e134f7fcbe6fc2ac5d6e413977cb3c217c25b6ab30349b314b987b66579ffafc8a6d764fea6fea32d631a7d6c53c067d71f8333aea2f4c700bad3b860c3a6e47fd6d490ddc66988bf966d98c8337153761bd6e2571469f91cd0744ba28878e64e4bcb8edc5d175c8361e7a01179318de6d207056347afa3a894315d69c8f3dd5d70d9e19a4c6235558fd3ddfb375539680d2eb966d4d57bdca302398c079a1cab17eacc60e4d5531b4f2dbab9aa9cb73e240321c0314a8894da035760aa00ecb64df26616ececd83de3b3a0d5035d439e1c2f84840f5ab31612a79ad3e4214e6e7990109b8b346fc287cceb85b30ad7f5efddb5ca2b8cb54993e76621b6e015fd7a3b1551dbe08eb2e4aa54ec10cb6ad58ba15403fef36c96e6d824f96ff1a3af31e521cb665e928e3c89d3dfb2d0d25a553a52893e9a1a0e3237af5f751cd2819302b988e8db380254be87b7a47a05e8b7877d1a93f41ebe9322386a780ee10fe48cc56b1b9210ded3e8bdaa63fa034a21526b0d7aea1d3bb32e29c857ea5bbe405721561de97d10ff59dcc29db4e8148cab5cf775953b6e2f4a9202b01bd5b54186783f5edd4032d5d3da740a1e997b2f801d4a8d441f1d13ae07a555cefbada406bc7567db2138b272249040698fc9c1ed5865a86bbc1c0aa35dbba65482b3bda03fdbc4af034c9978b4c1f90046c135eafa400ef6a60e0364ff7dd31624865b2d6bbb65da90c23f1f5516df1758c5742c40523c0e1bd1dbb1d155e0efe6aac72133d0fad5af2906a58486b6a8530193afe42fcafc9f6e65a3d60b2e61ba050625f6cf82e41d4f3d0fed76898a8f32f98c1c7eb8a6dc0626dd66a710943dd01c2a2306caf9ccbeebe9158b956012cb87dd47fe19d307758894e48945d708a99ed9eeffd1bb6d1719ae449c802861cd850a7325aa46d06a75300d323bd87e82c55197ea76fe9de4a943df917a4e2dfc8ef0f98936474f8ecaf0db189472e8cfb3c66c4c93f12cab2f64c35851f8b4f94fe12ff2123a5f6aa0d2973e2f21a37b11b36e2751ed7e94cf1c28ce84ba179ff332bf9a9fd7da1e2b3667769848389df37b762c5d2b3267008f8559a731b20e8d0c363d5090d4bcef2b5366f1845564a4a5c5ff4c7a3af77c46a5aced656de41b2fe7008df5b6b9522f3b6fc47d0dd83d467f4e9897c8c92758210c247d81ad8d1431a8b7afe96faae82509e5768d460b8796680ee9a5969110fd552f9a89a383e555eacc0cc9b5335ca79bf928a5fa7a4c7519b2a353b2af8b1a818acab60b68c51b194ffd5f6b5cd1ddc4797d06f3279c2d077edfffda0bc3d3f83c012d92028f5191e3bdec0db7743d1881309309d76b8f7308684ee783c9a2e27e7cd5dddef40a9263070ec5f50a9470f973ade3658fbd7b39b4c7f5c83fd80fb51ffb70375b715ae96c4419044e2480719a3ebedc387f754d7bf5ab0a7bc0f2e706d7aa0228eddedeae2c93e6e466233ed118ec61fde2bb8bbe1c28f9e3d22b9c0af53dcef4be3338c92ea3c9330055bb94605bb9b78edf0698815ce0b327aca5198def9788b4003661027d4ad0bc291fb095af068a589f89ba33bcf2af01fc4866feeffe42e8e26c52b4c8e6f0919279f49fd0a4f595f463afd78bd138b4462ed40b69d18dc08c4652bc0600fd6900df321ff41f35ae2f0fcf991261844e6647554e4449626bc7773e23abd68f0b2d7a628db5b60d20614ca4e72094df479ed39123e581744f3f1843a09d945c022d4d71b27f9875f874d188b5486efef4badd393a0c377929400566fd1691bd72ce83483cc0bb0b6841a82d0f3ff31f1c1190afa241e09bc03bb04a773e6bf41ff4f67d98577d92d01fc33834fbe0fc168e440d56cd6ef442c0810bd5c55495d6e788db06934b1034634623c84ad53b09dd8cf08f14fde3de7942ee3ab0708e90d7439514e98c76452501975ce8781162e4773c55f0777acfca2e08cc2c2ed7c1e3bcb1cd00507a191f91ab2c3912ecd219b6d24a863c9ab3a116b4eebe311d09383935331e8946bb697fc21c3a0ccab79c99d8d07bfec39172f93eaf56a6f8a511e6aff837520dcd8765fce08712f62ee768e914e07a3ad13246d22050b2d94ce3d4c7db33b1f863002f48052f5795968addd6b6cdd29fe2ef78a7464cee2676e169a2ca6cb5279357da398b38a5319b6250ed2496bd02754fe434c56c5a29e39bd9c48891156a70f2dbc0bd6c18726a3ad6af4e5c33e44038eeeb6d5873416c9e31a02bd9b75a98ae9789bc54bfe4711bcd1b1bcbdb8b3c7430224ad478144d4a51fe2e6029fc4bcf4fd91df53c58e05bdf87454679d8be2bbfd55d2bd8f1cfc05f39ac3ad1d2e5e65b0e79b64181ce740778635f1ea1548c2bfb47f664187b34760e64d3573e1b75f4707faf8a1000b45297f519d54487ff372903f7c65f42d84a3153228c510cc068ee107764e18fba65f6f943bd0335fa5641fc5a314d1ac0a90ec4744fbf1f661ffacfaea9d4d460416325a9affe1f3c8ab9afbc19d3a7979f13b6e4932f96da4e81a68267f024854ef31def9b6a423663467cfef5e167f4cbd411a6eceddaa84bdd9d5be533b1259909ee14847a2cec8d16cd1fdcf88e79d48e1c5b922d150a79c237a9bc59b535b2a736da246fd7dadb9b45abf951f7fae5c30407ea81e6d1f1dd56c5c9e1d0ee8c5cd94f7e4268654664a724a

private def light (n : ℕ) : Bool :=
  if n≤114 then decide n.Prime else n.gcd 2543559733472187557120132004189335234812341496026552301496526393412538629248600474981599398141467853800514886431180030568224218435400019580180261753940817530060800000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤13038) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 114 = 2543559733472187557120132004189335234812341496026552301496526393412538629248600474981599398141467853800514886431180030568224218435400019580180261753940817530060800000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 114 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤13038 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 50 := by unfold smallValid; decide +kernel

private theorem sp50 : smallValid 50 51 := by unfold smallValid; decide +kernel

private theorem sp101 : smallValid 101 51 := by unfold smallValid; decide +kernel

private theorem sp152 : smallValid 152 51 := by unfold smallValid; decide +kernel

private theorem sp203 : smallValid 203 51 := by unfold smallValid; decide +kernel

private theorem sp254 : smallValid 254 51 := by unfold smallValid; decide +kernel

private theorem sp305 : smallValid 305 51 := by unfold smallValid; decide +kernel

private theorem sp356 : smallValid 356 51 := by unfold smallValid; decide +kernel

private theorem sp407 : smallValid 407 50 := by unfold smallValid; decide +kernel

private theorem sp457 : smallValid 457 51 := by unfold smallValid; decide +kernel

private theorem sp508 : smallValid 508 51 := by unfold smallValid; decide +kernel

private theorem sp559 : smallValid 559 51 := by unfold smallValid; decide +kernel

private theorem sp610 : smallValid 610 51 := by unfold smallValid; decide +kernel

private theorem sp661 : smallValid 661 51 := by unfold smallValid; decide +kernel

private theorem sp712 : smallValid 712 51 := by unfold smallValid; decide +kernel

private theorem sp763 : smallValid 763 51 := by unfold smallValid; decide +kernel

private theorem sp814 : smallValid 814 50 := by unfold smallValid; decide +kernel

private theorem sp864 : smallValid 864 51 := by unfold smallValid; decide +kernel

private theorem sp915 : smallValid 915 51 := by unfold smallValid; decide +kernel

private theorem sp966 : smallValid 966 51 := by unfold smallValid; decide +kernel

private theorem sp1017 : smallValid 1017 51 := by unfold smallValid; decide +kernel

private theorem sp1068 : smallValid 1068 51 := by unfold smallValid; decide +kernel

private theorem sp1119 : smallValid 1119 51 := by unfold smallValid; decide +kernel

private theorem sp1170 : smallValid 1170 51 := by unfold smallValid; decide +kernel

private theorem sp1221 : smallValid 1221 51 := by unfold smallValid; decide +kernel

private theorem sp1272 : smallValid 1272 51 := by unfold smallValid; decide +kernel

private theorem sp1323 : smallValid 1323 51 := by unfold smallValid; decide +kernel

private theorem sp1374 : smallValid 1374 51 := by unfold smallValid; decide +kernel

private theorem sp1425 : smallValid 1425 51 := by unfold smallValid; decide +kernel

private theorem sp1476 : smallValid 1476 51 := by unfold smallValid; decide +kernel

private theorem sp1527 : smallValid 1527 51 := by unfold smallValid; decide +kernel

private theorem sp1578 : smallValid 1578 51 := by unfold smallValid; decide +kernel

private theorem sp1629 : smallValid 1629 50 := by unfold smallValid; decide +kernel

private theorem sp1679 : smallValid 1679 51 := by unfold smallValid; decide +kernel

private theorem sp1730 : smallValid 1730 51 := by unfold smallValid; decide +kernel

private theorem sp1781 : smallValid 1781 51 := by unfold smallValid; decide +kernel

private theorem sp1832 : smallValid 1832 51 := by unfold smallValid; decide +kernel

private theorem sp1883 : smallValid 1883 51 := by unfold smallValid; decide +kernel

private theorem sp1934 : smallValid 1934 51 := by unfold smallValid; decide +kernel

private theorem sp1985 : smallValid 1985 51 := by unfold smallValid; decide +kernel

private theorem sp2036 : smallValid 2036 51 := by unfold smallValid; decide +kernel

private theorem sp2087 : smallValid 2087 51 := by unfold smallValid; decide +kernel

private theorem sp2138 : smallValid 2138 51 := by unfold smallValid; decide +kernel

private theorem sp2189 : smallValid 2189 51 := by unfold smallValid; decide +kernel

private theorem sp2240 : smallValid 2240 51 := by unfold smallValid; decide +kernel

private theorem sp2291 : smallValid 2291 51 := by unfold smallValid; decide +kernel

private theorem sp2342 : smallValid 2342 51 := by unfold smallValid; decide +kernel

private theorem sp2393 : smallValid 2393 51 := by unfold smallValid; decide +kernel

private theorem sp2444 : smallValid 2444 50 := by unfold smallValid; decide +kernel

private theorem sp2494 : smallValid 2494 51 := by unfold smallValid; decide +kernel

private theorem sp2545 : smallValid 2545 51 := by unfold smallValid; decide +kernel

private theorem sp2596 : smallValid 2596 51 := by unfold smallValid; decide +kernel

private theorem sp2647 : smallValid 2647 51 := by unfold smallValid; decide +kernel

private theorem sp2698 : smallValid 2698 51 := by unfold smallValid; decide +kernel

private theorem sp2749 : smallValid 2749 51 := by unfold smallValid; decide +kernel

private theorem sp2800 : smallValid 2800 51 := by unfold smallValid; decide +kernel

private theorem sp2851 : smallValid 2851 51 := by unfold smallValid; decide +kernel

private theorem sp2902 : smallValid 2902 51 := by unfold smallValid; decide +kernel

private theorem sp2953 : smallValid 2953 51 := by unfold smallValid; decide +kernel

private theorem sp3004 : smallValid 3004 51 := by unfold smallValid; decide +kernel

private theorem sp3055 : smallValid 3055 51 := by unfold smallValid; decide +kernel

private theorem sp3106 : smallValid 3106 51 := by unfold smallValid; decide +kernel

private theorem sp3157 : smallValid 3157 51 := by unfold smallValid; decide +kernel

private theorem sp3208 : smallValid 3208 51 := by unfold smallValid; decide +kernel

private theorem sp3259 : smallValid 3259 50 := by unfold smallValid; decide +kernel

private theorem sp3309 : smallValid 3309 51 := by unfold smallValid; decide +kernel

private theorem sp3360 : smallValid 3360 51 := by unfold smallValid; decide +kernel

private theorem sp3411 : smallValid 3411 51 := by unfold smallValid; decide +kernel

private theorem sp3462 : smallValid 3462 51 := by unfold smallValid; decide +kernel

private theorem sp3513 : smallValid 3513 51 := by unfold smallValid; decide +kernel

private theorem sp3564 : smallValid 3564 51 := by unfold smallValid; decide +kernel

private theorem sp3615 : smallValid 3615 51 := by unfold smallValid; decide +kernel

private theorem sp3666 : smallValid 3666 51 := by unfold smallValid; decide +kernel

private theorem sp3717 : smallValid 3717 51 := by unfold smallValid; decide +kernel

private theorem sp3768 : smallValid 3768 51 := by unfold smallValid; decide +kernel

private theorem sp3819 : smallValid 3819 51 := by unfold smallValid; decide +kernel

private theorem sp3870 : smallValid 3870 51 := by unfold smallValid; decide +kernel

private theorem sp3921 : smallValid 3921 51 := by unfold smallValid; decide +kernel

private theorem sp3972 : smallValid 3972 51 := by unfold smallValid; decide +kernel

private theorem sp4023 : smallValid 4023 51 := by unfold smallValid; decide +kernel

private theorem sp4074 : smallValid 4074 50 := by unfold smallValid; decide +kernel

private theorem sp4124 : smallValid 4124 51 := by unfold smallValid; decide +kernel

private theorem sp4175 : smallValid 4175 51 := by unfold smallValid; decide +kernel

private theorem sp4226 : smallValid 4226 51 := by unfold smallValid; decide +kernel

private theorem sp4277 : smallValid 4277 51 := by unfold smallValid; decide +kernel

private theorem sp4328 : smallValid 4328 51 := by unfold smallValid; decide +kernel

private theorem sp4379 : smallValid 4379 51 := by unfold smallValid; decide +kernel

private theorem sp4430 : smallValid 4430 51 := by unfold smallValid; decide +kernel

private theorem sp4481 : smallValid 4481 51 := by unfold smallValid; decide +kernel

private theorem sp4532 : smallValid 4532 51 := by unfold smallValid; decide +kernel

private theorem sp4583 : smallValid 4583 51 := by unfold smallValid; decide +kernel

private theorem sp4634 : smallValid 4634 51 := by unfold smallValid; decide +kernel

private theorem sp4685 : smallValid 4685 51 := by unfold smallValid; decide +kernel

private theorem sp4736 : smallValid 4736 51 := by unfold smallValid; decide +kernel

private theorem sp4787 : smallValid 4787 51 := by unfold smallValid; decide +kernel

private theorem sp4838 : smallValid 4838 51 := by unfold smallValid; decide +kernel

private theorem sp4889 : smallValid 4889 50 := by unfold smallValid; decide +kernel

private theorem sp4939 : smallValid 4939 51 := by unfold smallValid; decide +kernel

private theorem sp4990 : smallValid 4990 51 := by unfold smallValid; decide +kernel

private theorem sp5041 : smallValid 5041 51 := by unfold smallValid; decide +kernel

private theorem sp5092 : smallValid 5092 51 := by unfold smallValid; decide +kernel

private theorem sp5143 : smallValid 5143 51 := by unfold smallValid; decide +kernel

private theorem sp5194 : smallValid 5194 51 := by unfold smallValid; decide +kernel

private theorem sp5245 : smallValid 5245 51 := by unfold smallValid; decide +kernel

private theorem sp5296 : smallValid 5296 51 := by unfold smallValid; decide +kernel

private theorem sp5347 : smallValid 5347 51 := by unfold smallValid; decide +kernel

private theorem sp5398 : smallValid 5398 51 := by unfold smallValid; decide +kernel

private theorem sp5449 : smallValid 5449 51 := by unfold smallValid; decide +kernel

private theorem sp5500 : smallValid 5500 51 := by unfold smallValid; decide +kernel

private theorem sp5551 : smallValid 5551 51 := by unfold smallValid; decide +kernel

private theorem sp5602 : smallValid 5602 51 := by unfold smallValid; decide +kernel

private theorem sp5653 : smallValid 5653 51 := by unfold smallValid; decide +kernel

private theorem sp5704 : smallValid 5704 50 := by unfold smallValid; decide +kernel

private theorem sp5754 : smallValid 5754 51 := by unfold smallValid; decide +kernel

private theorem sp5805 : smallValid 5805 51 := by unfold smallValid; decide +kernel

private theorem sp5856 : smallValid 5856 51 := by unfold smallValid; decide +kernel

private theorem sp5907 : smallValid 5907 51 := by unfold smallValid; decide +kernel

private theorem sp5958 : smallValid 5958 51 := by unfold smallValid; decide +kernel

private theorem sp6009 : smallValid 6009 51 := by unfold smallValid; decide +kernel

private theorem sp6060 : smallValid 6060 51 := by unfold smallValid; decide +kernel

private theorem sp6111 : smallValid 6111 51 := by unfold smallValid; decide +kernel

private theorem sp6162 : smallValid 6162 51 := by unfold smallValid; decide +kernel

private theorem sp6213 : smallValid 6213 51 := by unfold smallValid; decide +kernel

private theorem sp6264 : smallValid 6264 51 := by unfold smallValid; decide +kernel

private theorem sp6315 : smallValid 6315 51 := by unfold smallValid; decide +kernel

private theorem sp6366 : smallValid 6366 51 := by unfold smallValid; decide +kernel

private theorem sp6417 : smallValid 6417 51 := by unfold smallValid; decide +kernel

private theorem sp6468 : smallValid 6468 51 := by unfold smallValid; decide +kernel

private theorem sp6519 : smallValid 6519 50 := by unfold smallValid; decide +kernel

private theorem sp6569 : smallValid 6569 51 := by unfold smallValid; decide +kernel

private theorem sp6620 : smallValid 6620 51 := by unfold smallValid; decide +kernel

private theorem sp6671 : smallValid 6671 51 := by unfold smallValid; decide +kernel

private theorem sp6722 : smallValid 6722 51 := by unfold smallValid; decide +kernel

private theorem sp6773 : smallValid 6773 51 := by unfold smallValid; decide +kernel

private theorem sp6824 : smallValid 6824 51 := by unfold smallValid; decide +kernel

private theorem sp6875 : smallValid 6875 51 := by unfold smallValid; decide +kernel

private theorem sp6926 : smallValid 6926 51 := by unfold smallValid; decide +kernel

private theorem sp6977 : smallValid 6977 51 := by unfold smallValid; decide +kernel

private theorem sp7028 : smallValid 7028 51 := by unfold smallValid; decide +kernel

private theorem sp7079 : smallValid 7079 51 := by unfold smallValid; decide +kernel

private theorem sp7130 : smallValid 7130 51 := by unfold smallValid; decide +kernel

private theorem sp7181 : smallValid 7181 51 := by unfold smallValid; decide +kernel

private theorem sp7232 : smallValid 7232 51 := by unfold smallValid; decide +kernel

private theorem sp7283 : smallValid 7283 51 := by unfold smallValid; decide +kernel

private theorem sp7334 : smallValid 7334 50 := by unfold smallValid; decide +kernel

private theorem sp7384 : smallValid 7384 51 := by unfold smallValid; decide +kernel

private theorem sp7435 : smallValid 7435 51 := by unfold smallValid; decide +kernel

private theorem sp7486 : smallValid 7486 51 := by unfold smallValid; decide +kernel

private theorem sp7537 : smallValid 7537 51 := by unfold smallValid; decide +kernel

private theorem sp7588 : smallValid 7588 51 := by unfold smallValid; decide +kernel

private theorem sp7639 : smallValid 7639 51 := by unfold smallValid; decide +kernel

private theorem sp7690 : smallValid 7690 51 := by unfold smallValid; decide +kernel

private theorem sp7741 : smallValid 7741 51 := by unfold smallValid; decide +kernel

private theorem sp7792 : smallValid 7792 51 := by unfold smallValid; decide +kernel

private theorem sp7843 : smallValid 7843 51 := by unfold smallValid; decide +kernel

private theorem sp7894 : smallValid 7894 51 := by unfold smallValid; decide +kernel

private theorem sp7945 : smallValid 7945 51 := by unfold smallValid; decide +kernel

private theorem sp7996 : smallValid 7996 51 := by unfold smallValid; decide +kernel

private theorem sp8047 : smallValid 8047 51 := by unfold smallValid; decide +kernel

private theorem sp8098 : smallValid 8098 51 := by unfold smallValid; decide +kernel

private theorem sp8149 : smallValid 8149 50 := by unfold smallValid; decide +kernel

private theorem sp8199 : smallValid 8199 51 := by unfold smallValid; decide +kernel

private theorem sp8250 : smallValid 8250 51 := by unfold smallValid; decide +kernel

private theorem sp8301 : smallValid 8301 51 := by unfold smallValid; decide +kernel

private theorem sp8352 : smallValid 8352 51 := by unfold smallValid; decide +kernel

private theorem sp8403 : smallValid 8403 51 := by unfold smallValid; decide +kernel

private theorem sp8454 : smallValid 8454 51 := by unfold smallValid; decide +kernel

private theorem sp8505 : smallValid 8505 51 := by unfold smallValid; decide +kernel

private theorem sp8556 : smallValid 8556 51 := by unfold smallValid; decide +kernel

private theorem sp8607 : smallValid 8607 51 := by unfold smallValid; decide +kernel

private theorem sp8658 : smallValid 8658 51 := by unfold smallValid; decide +kernel

private theorem sp8709 : smallValid 8709 51 := by unfold smallValid; decide +kernel

private theorem sp8760 : smallValid 8760 51 := by unfold smallValid; decide +kernel

private theorem sp8811 : smallValid 8811 51 := by unfold smallValid; decide +kernel

private theorem sp8862 : smallValid 8862 51 := by unfold smallValid; decide +kernel

private theorem sp8913 : smallValid 8913 51 := by unfold smallValid; decide +kernel

private theorem sp8964 : smallValid 8964 50 := by unfold smallValid; decide +kernel

private theorem sp9014 : smallValid 9014 51 := by unfold smallValid; decide +kernel

private theorem sp9065 : smallValid 9065 51 := by unfold smallValid; decide +kernel

private theorem sp9116 : smallValid 9116 51 := by unfold smallValid; decide +kernel

private theorem sp9167 : smallValid 9167 51 := by unfold smallValid; decide +kernel

private theorem sp9218 : smallValid 9218 51 := by unfold smallValid; decide +kernel

private theorem sp9269 : smallValid 9269 51 := by unfold smallValid; decide +kernel

private theorem sp9320 : smallValid 9320 51 := by unfold smallValid; decide +kernel

private theorem sp9371 : smallValid 9371 51 := by unfold smallValid; decide +kernel

private theorem sp9422 : smallValid 9422 51 := by unfold smallValid; decide +kernel

private theorem sp9473 : smallValid 9473 51 := by unfold smallValid; decide +kernel

private theorem sp9524 : smallValid 9524 51 := by unfold smallValid; decide +kernel

private theorem sp9575 : smallValid 9575 51 := by unfold smallValid; decide +kernel

private theorem sp9626 : smallValid 9626 51 := by unfold smallValid; decide +kernel

private theorem sp9677 : smallValid 9677 51 := by unfold smallValid; decide +kernel

private theorem sp9728 : smallValid 9728 51 := by unfold smallValid; decide +kernel

private theorem sp9779 : smallValid 9779 50 := by unfold smallValid; decide +kernel

private theorem sp9829 : smallValid 9829 51 := by unfold smallValid; decide +kernel

private theorem sp9880 : smallValid 9880 51 := by unfold smallValid; decide +kernel

private theorem sp9931 : smallValid 9931 51 := by unfold smallValid; decide +kernel

private theorem sp9982 : smallValid 9982 51 := by unfold smallValid; decide +kernel

private theorem sp10033 : smallValid 10033 51 := by unfold smallValid; decide +kernel

private theorem sp10084 : smallValid 10084 51 := by unfold smallValid; decide +kernel

private theorem sp10135 : smallValid 10135 51 := by unfold smallValid; decide +kernel

private theorem sp10186 : smallValid 10186 51 := by unfold smallValid; decide +kernel

private theorem sp10237 : smallValid 10237 51 := by unfold smallValid; decide +kernel

private theorem sp10288 : smallValid 10288 51 := by unfold smallValid; decide +kernel

private theorem sp10339 : smallValid 10339 51 := by unfold smallValid; decide +kernel

private theorem sp10390 : smallValid 10390 51 := by unfold smallValid; decide +kernel

private theorem sp10441 : smallValid 10441 51 := by unfold smallValid; decide +kernel

private theorem sp10492 : smallValid 10492 51 := by unfold smallValid; decide +kernel

private theorem sp10543 : smallValid 10543 51 := by unfold smallValid; decide +kernel

private theorem sp10594 : smallValid 10594 50 := by unfold smallValid; decide +kernel

private theorem sp10644 : smallValid 10644 51 := by unfold smallValid; decide +kernel

private theorem sp10695 : smallValid 10695 51 := by unfold smallValid; decide +kernel

private theorem sp10746 : smallValid 10746 51 := by unfold smallValid; decide +kernel

private theorem sp10797 : smallValid 10797 51 := by unfold smallValid; decide +kernel

private theorem sp10848 : smallValid 10848 51 := by unfold smallValid; decide +kernel

private theorem sp10899 : smallValid 10899 51 := by unfold smallValid; decide +kernel

private theorem sp10950 : smallValid 10950 51 := by unfold smallValid; decide +kernel

private theorem sp11001 : smallValid 11001 51 := by unfold smallValid; decide +kernel

private theorem sp11052 : smallValid 11052 51 := by unfold smallValid; decide +kernel

private theorem sp11103 : smallValid 11103 51 := by unfold smallValid; decide +kernel

private theorem sp11154 : smallValid 11154 51 := by unfold smallValid; decide +kernel

private theorem sp11205 : smallValid 11205 51 := by unfold smallValid; decide +kernel

private theorem sp11256 : smallValid 11256 51 := by unfold smallValid; decide +kernel

private theorem sp11307 : smallValid 11307 51 := by unfold smallValid; decide +kernel

private theorem sp11358 : smallValid 11358 51 := by unfold smallValid; decide +kernel

private theorem sp11409 : smallValid 11409 50 := by unfold smallValid; decide +kernel

private theorem sp11459 : smallValid 11459 51 := by unfold smallValid; decide +kernel

private theorem sp11510 : smallValid 11510 51 := by unfold smallValid; decide +kernel

private theorem sp11561 : smallValid 11561 51 := by unfold smallValid; decide +kernel

private theorem sp11612 : smallValid 11612 51 := by unfold smallValid; decide +kernel

private theorem sp11663 : smallValid 11663 51 := by unfold smallValid; decide +kernel

private theorem sp11714 : smallValid 11714 51 := by unfold smallValid; decide +kernel

private theorem sp11765 : smallValid 11765 51 := by unfold smallValid; decide +kernel

private theorem sp11816 : smallValid 11816 51 := by unfold smallValid; decide +kernel

private theorem sp11867 : smallValid 11867 51 := by unfold smallValid; decide +kernel

private theorem sp11918 : smallValid 11918 51 := by unfold smallValid; decide +kernel

private theorem sp11969 : smallValid 11969 51 := by unfold smallValid; decide +kernel

private theorem sp12020 : smallValid 12020 51 := by unfold smallValid; decide +kernel

private theorem sp12071 : smallValid 12071 51 := by unfold smallValid; decide +kernel

private theorem sp12122 : smallValid 12122 51 := by unfold smallValid; decide +kernel

private theorem sp12173 : smallValid 12173 51 := by unfold smallValid; decide +kernel

private theorem sp12224 : smallValid 12224 50 := by unfold smallValid; decide +kernel

private theorem sp12274 : smallValid 12274 51 := by unfold smallValid; decide +kernel

private theorem sp12325 : smallValid 12325 51 := by unfold smallValid; decide +kernel

private theorem sp12376 : smallValid 12376 51 := by unfold smallValid; decide +kernel

private theorem sp12427 : smallValid 12427 51 := by unfold smallValid; decide +kernel

private theorem sp12478 : smallValid 12478 51 := by unfold smallValid; decide +kernel

private theorem sp12529 : smallValid 12529 51 := by unfold smallValid; decide +kernel

private theorem sp12580 : smallValid 12580 51 := by unfold smallValid; decide +kernel

private theorem sp12631 : smallValid 12631 51 := by unfold smallValid; decide +kernel

private theorem sp12682 : smallValid 12682 51 := by unfold smallValid; decide +kernel

private theorem sp12733 : smallValid 12733 51 := by unfold smallValid; decide +kernel

private theorem sp12784 : smallValid 12784 51 := by unfold smallValid; decide +kernel

private theorem sp12835 : smallValid 12835 51 := by unfold smallValid; decide +kernel

private theorem sp12886 : smallValid 12886 51 := by unfold smallValid; decide +kernel

private theorem sp12937 : smallValid 12937 51 := by unfold smallValid; decide +kernel

private theorem sp12988 : smallValid 12988 51 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤13038) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 13039 := (joinSmall (lo:=0) (a:=6519) (b:=6520) (joinSmall (lo:=0) (a:=3259) (b:=3260) (joinSmall (lo:=0) (a:=1629) (b:=1630) (joinSmall (lo:=0) (a:=814) (b:=815) (joinSmall (lo:=0) (a:=407) (b:=407) (joinSmall (lo:=0) (a:=203) (b:=204) (joinSmall (lo:=0) (a:=101) (b:=102) (joinSmall (lo:=0) (a:=50) (b:=51) sp0 sp50) (joinSmall (lo:=101) (a:=51) (b:=51) sp101 sp152)) (joinSmall (lo:=203) (a:=102) (b:=102) (joinSmall (lo:=203) (a:=51) (b:=51) sp203 sp254) (joinSmall (lo:=305) (a:=51) (b:=51) sp305 sp356))) (joinSmall (lo:=407) (a:=203) (b:=204) (joinSmall (lo:=407) (a:=101) (b:=102) (joinSmall (lo:=407) (a:=50) (b:=51) sp407 sp457) (joinSmall (lo:=508) (a:=51) (b:=51) sp508 sp559)) (joinSmall (lo:=610) (a:=102) (b:=102) (joinSmall (lo:=610) (a:=51) (b:=51) sp610 sp661) (joinSmall (lo:=712) (a:=51) (b:=51) sp712 sp763)))) (joinSmall (lo:=814) (a:=407) (b:=408) (joinSmall (lo:=814) (a:=203) (b:=204) (joinSmall (lo:=814) (a:=101) (b:=102) (joinSmall (lo:=814) (a:=50) (b:=51) sp814 sp864) (joinSmall (lo:=915) (a:=51) (b:=51) sp915 sp966)) (joinSmall (lo:=1017) (a:=102) (b:=102) (joinSmall (lo:=1017) (a:=51) (b:=51) sp1017 sp1068) (joinSmall (lo:=1119) (a:=51) (b:=51) sp1119 sp1170))) (joinSmall (lo:=1221) (a:=204) (b:=204) (joinSmall (lo:=1221) (a:=102) (b:=102) (joinSmall (lo:=1221) (a:=51) (b:=51) sp1221 sp1272) (joinSmall (lo:=1323) (a:=51) (b:=51) sp1323 sp1374)) (joinSmall (lo:=1425) (a:=102) (b:=102) (joinSmall (lo:=1425) (a:=51) (b:=51) sp1425 sp1476) (joinSmall (lo:=1527) (a:=51) (b:=51) sp1527 sp1578))))) (joinSmall (lo:=1629) (a:=815) (b:=815) (joinSmall (lo:=1629) (a:=407) (b:=408) (joinSmall (lo:=1629) (a:=203) (b:=204) (joinSmall (lo:=1629) (a:=101) (b:=102) (joinSmall (lo:=1629) (a:=50) (b:=51) sp1629 sp1679) (joinSmall (lo:=1730) (a:=51) (b:=51) sp1730 sp1781)) (joinSmall (lo:=1832) (a:=102) (b:=102) (joinSmall (lo:=1832) (a:=51) (b:=51) sp1832 sp1883) (joinSmall (lo:=1934) (a:=51) (b:=51) sp1934 sp1985))) (joinSmall (lo:=2036) (a:=204) (b:=204) (joinSmall (lo:=2036) (a:=102) (b:=102) (joinSmall (lo:=2036) (a:=51) (b:=51) sp2036 sp2087) (joinSmall (lo:=2138) (a:=51) (b:=51) sp2138 sp2189)) (joinSmall (lo:=2240) (a:=102) (b:=102) (joinSmall (lo:=2240) (a:=51) (b:=51) sp2240 sp2291) (joinSmall (lo:=2342) (a:=51) (b:=51) sp2342 sp2393)))) (joinSmall (lo:=2444) (a:=407) (b:=408) (joinSmall (lo:=2444) (a:=203) (b:=204) (joinSmall (lo:=2444) (a:=101) (b:=102) (joinSmall (lo:=2444) (a:=50) (b:=51) sp2444 sp2494) (joinSmall (lo:=2545) (a:=51) (b:=51) sp2545 sp2596)) (joinSmall (lo:=2647) (a:=102) (b:=102) (joinSmall (lo:=2647) (a:=51) (b:=51) sp2647 sp2698) (joinSmall (lo:=2749) (a:=51) (b:=51) sp2749 sp2800))) (joinSmall (lo:=2851) (a:=204) (b:=204) (joinSmall (lo:=2851) (a:=102) (b:=102) (joinSmall (lo:=2851) (a:=51) (b:=51) sp2851 sp2902) (joinSmall (lo:=2953) (a:=51) (b:=51) sp2953 sp3004)) (joinSmall (lo:=3055) (a:=102) (b:=102) (joinSmall (lo:=3055) (a:=51) (b:=51) sp3055 sp3106) (joinSmall (lo:=3157) (a:=51) (b:=51) sp3157 sp3208)))))) (joinSmall (lo:=3259) (a:=1630) (b:=1630) (joinSmall (lo:=3259) (a:=815) (b:=815) (joinSmall (lo:=3259) (a:=407) (b:=408) (joinSmall (lo:=3259) (a:=203) (b:=204) (joinSmall (lo:=3259) (a:=101) (b:=102) (joinSmall (lo:=3259) (a:=50) (b:=51) sp3259 sp3309) (joinSmall (lo:=3360) (a:=51) (b:=51) sp3360 sp3411)) (joinSmall (lo:=3462) (a:=102) (b:=102) (joinSmall (lo:=3462) (a:=51) (b:=51) sp3462 sp3513) (joinSmall (lo:=3564) (a:=51) (b:=51) sp3564 sp3615))) (joinSmall (lo:=3666) (a:=204) (b:=204) (joinSmall (lo:=3666) (a:=102) (b:=102) (joinSmall (lo:=3666) (a:=51) (b:=51) sp3666 sp3717) (joinSmall (lo:=3768) (a:=51) (b:=51) sp3768 sp3819)) (joinSmall (lo:=3870) (a:=102) (b:=102) (joinSmall (lo:=3870) (a:=51) (b:=51) sp3870 sp3921) (joinSmall (lo:=3972) (a:=51) (b:=51) sp3972 sp4023)))) (joinSmall (lo:=4074) (a:=407) (b:=408) (joinSmall (lo:=4074) (a:=203) (b:=204) (joinSmall (lo:=4074) (a:=101) (b:=102) (joinSmall (lo:=4074) (a:=50) (b:=51) sp4074 sp4124) (joinSmall (lo:=4175) (a:=51) (b:=51) sp4175 sp4226)) (joinSmall (lo:=4277) (a:=102) (b:=102) (joinSmall (lo:=4277) (a:=51) (b:=51) sp4277 sp4328) (joinSmall (lo:=4379) (a:=51) (b:=51) sp4379 sp4430))) (joinSmall (lo:=4481) (a:=204) (b:=204) (joinSmall (lo:=4481) (a:=102) (b:=102) (joinSmall (lo:=4481) (a:=51) (b:=51) sp4481 sp4532) (joinSmall (lo:=4583) (a:=51) (b:=51) sp4583 sp4634)) (joinSmall (lo:=4685) (a:=102) (b:=102) (joinSmall (lo:=4685) (a:=51) (b:=51) sp4685 sp4736) (joinSmall (lo:=4787) (a:=51) (b:=51) sp4787 sp4838))))) (joinSmall (lo:=4889) (a:=815) (b:=815) (joinSmall (lo:=4889) (a:=407) (b:=408) (joinSmall (lo:=4889) (a:=203) (b:=204) (joinSmall (lo:=4889) (a:=101) (b:=102) (joinSmall (lo:=4889) (a:=50) (b:=51) sp4889 sp4939) (joinSmall (lo:=4990) (a:=51) (b:=51) sp4990 sp5041)) (joinSmall (lo:=5092) (a:=102) (b:=102) (joinSmall (lo:=5092) (a:=51) (b:=51) sp5092 sp5143) (joinSmall (lo:=5194) (a:=51) (b:=51) sp5194 sp5245))) (joinSmall (lo:=5296) (a:=204) (b:=204) (joinSmall (lo:=5296) (a:=102) (b:=102) (joinSmall (lo:=5296) (a:=51) (b:=51) sp5296 sp5347) (joinSmall (lo:=5398) (a:=51) (b:=51) sp5398 sp5449)) (joinSmall (lo:=5500) (a:=102) (b:=102) (joinSmall (lo:=5500) (a:=51) (b:=51) sp5500 sp5551) (joinSmall (lo:=5602) (a:=51) (b:=51) sp5602 sp5653)))) (joinSmall (lo:=5704) (a:=407) (b:=408) (joinSmall (lo:=5704) (a:=203) (b:=204) (joinSmall (lo:=5704) (a:=101) (b:=102) (joinSmall (lo:=5704) (a:=50) (b:=51) sp5704 sp5754) (joinSmall (lo:=5805) (a:=51) (b:=51) sp5805 sp5856)) (joinSmall (lo:=5907) (a:=102) (b:=102) (joinSmall (lo:=5907) (a:=51) (b:=51) sp5907 sp5958) (joinSmall (lo:=6009) (a:=51) (b:=51) sp6009 sp6060))) (joinSmall (lo:=6111) (a:=204) (b:=204) (joinSmall (lo:=6111) (a:=102) (b:=102) (joinSmall (lo:=6111) (a:=51) (b:=51) sp6111 sp6162) (joinSmall (lo:=6213) (a:=51) (b:=51) sp6213 sp6264)) (joinSmall (lo:=6315) (a:=102) (b:=102) (joinSmall (lo:=6315) (a:=51) (b:=51) sp6315 sp6366) (joinSmall (lo:=6417) (a:=51) (b:=51) sp6417 sp6468))))))) (joinSmall (lo:=6519) (a:=3260) (b:=3260) (joinSmall (lo:=6519) (a:=1630) (b:=1630) (joinSmall (lo:=6519) (a:=815) (b:=815) (joinSmall (lo:=6519) (a:=407) (b:=408) (joinSmall (lo:=6519) (a:=203) (b:=204) (joinSmall (lo:=6519) (a:=101) (b:=102) (joinSmall (lo:=6519) (a:=50) (b:=51) sp6519 sp6569) (joinSmall (lo:=6620) (a:=51) (b:=51) sp6620 sp6671)) (joinSmall (lo:=6722) (a:=102) (b:=102) (joinSmall (lo:=6722) (a:=51) (b:=51) sp6722 sp6773) (joinSmall (lo:=6824) (a:=51) (b:=51) sp6824 sp6875))) (joinSmall (lo:=6926) (a:=204) (b:=204) (joinSmall (lo:=6926) (a:=102) (b:=102) (joinSmall (lo:=6926) (a:=51) (b:=51) sp6926 sp6977) (joinSmall (lo:=7028) (a:=51) (b:=51) sp7028 sp7079)) (joinSmall (lo:=7130) (a:=102) (b:=102) (joinSmall (lo:=7130) (a:=51) (b:=51) sp7130 sp7181) (joinSmall (lo:=7232) (a:=51) (b:=51) sp7232 sp7283)))) (joinSmall (lo:=7334) (a:=407) (b:=408) (joinSmall (lo:=7334) (a:=203) (b:=204) (joinSmall (lo:=7334) (a:=101) (b:=102) (joinSmall (lo:=7334) (a:=50) (b:=51) sp7334 sp7384) (joinSmall (lo:=7435) (a:=51) (b:=51) sp7435 sp7486)) (joinSmall (lo:=7537) (a:=102) (b:=102) (joinSmall (lo:=7537) (a:=51) (b:=51) sp7537 sp7588) (joinSmall (lo:=7639) (a:=51) (b:=51) sp7639 sp7690))) (joinSmall (lo:=7741) (a:=204) (b:=204) (joinSmall (lo:=7741) (a:=102) (b:=102) (joinSmall (lo:=7741) (a:=51) (b:=51) sp7741 sp7792) (joinSmall (lo:=7843) (a:=51) (b:=51) sp7843 sp7894)) (joinSmall (lo:=7945) (a:=102) (b:=102) (joinSmall (lo:=7945) (a:=51) (b:=51) sp7945 sp7996) (joinSmall (lo:=8047) (a:=51) (b:=51) sp8047 sp8098))))) (joinSmall (lo:=8149) (a:=815) (b:=815) (joinSmall (lo:=8149) (a:=407) (b:=408) (joinSmall (lo:=8149) (a:=203) (b:=204) (joinSmall (lo:=8149) (a:=101) (b:=102) (joinSmall (lo:=8149) (a:=50) (b:=51) sp8149 sp8199) (joinSmall (lo:=8250) (a:=51) (b:=51) sp8250 sp8301)) (joinSmall (lo:=8352) (a:=102) (b:=102) (joinSmall (lo:=8352) (a:=51) (b:=51) sp8352 sp8403) (joinSmall (lo:=8454) (a:=51) (b:=51) sp8454 sp8505))) (joinSmall (lo:=8556) (a:=204) (b:=204) (joinSmall (lo:=8556) (a:=102) (b:=102) (joinSmall (lo:=8556) (a:=51) (b:=51) sp8556 sp8607) (joinSmall (lo:=8658) (a:=51) (b:=51) sp8658 sp8709)) (joinSmall (lo:=8760) (a:=102) (b:=102) (joinSmall (lo:=8760) (a:=51) (b:=51) sp8760 sp8811) (joinSmall (lo:=8862) (a:=51) (b:=51) sp8862 sp8913)))) (joinSmall (lo:=8964) (a:=407) (b:=408) (joinSmall (lo:=8964) (a:=203) (b:=204) (joinSmall (lo:=8964) (a:=101) (b:=102) (joinSmall (lo:=8964) (a:=50) (b:=51) sp8964 sp9014) (joinSmall (lo:=9065) (a:=51) (b:=51) sp9065 sp9116)) (joinSmall (lo:=9167) (a:=102) (b:=102) (joinSmall (lo:=9167) (a:=51) (b:=51) sp9167 sp9218) (joinSmall (lo:=9269) (a:=51) (b:=51) sp9269 sp9320))) (joinSmall (lo:=9371) (a:=204) (b:=204) (joinSmall (lo:=9371) (a:=102) (b:=102) (joinSmall (lo:=9371) (a:=51) (b:=51) sp9371 sp9422) (joinSmall (lo:=9473) (a:=51) (b:=51) sp9473 sp9524)) (joinSmall (lo:=9575) (a:=102) (b:=102) (joinSmall (lo:=9575) (a:=51) (b:=51) sp9575 sp9626) (joinSmall (lo:=9677) (a:=51) (b:=51) sp9677 sp9728)))))) (joinSmall (lo:=9779) (a:=1630) (b:=1630) (joinSmall (lo:=9779) (a:=815) (b:=815) (joinSmall (lo:=9779) (a:=407) (b:=408) (joinSmall (lo:=9779) (a:=203) (b:=204) (joinSmall (lo:=9779) (a:=101) (b:=102) (joinSmall (lo:=9779) (a:=50) (b:=51) sp9779 sp9829) (joinSmall (lo:=9880) (a:=51) (b:=51) sp9880 sp9931)) (joinSmall (lo:=9982) (a:=102) (b:=102) (joinSmall (lo:=9982) (a:=51) (b:=51) sp9982 sp10033) (joinSmall (lo:=10084) (a:=51) (b:=51) sp10084 sp10135))) (joinSmall (lo:=10186) (a:=204) (b:=204) (joinSmall (lo:=10186) (a:=102) (b:=102) (joinSmall (lo:=10186) (a:=51) (b:=51) sp10186 sp10237) (joinSmall (lo:=10288) (a:=51) (b:=51) sp10288 sp10339)) (joinSmall (lo:=10390) (a:=102) (b:=102) (joinSmall (lo:=10390) (a:=51) (b:=51) sp10390 sp10441) (joinSmall (lo:=10492) (a:=51) (b:=51) sp10492 sp10543)))) (joinSmall (lo:=10594) (a:=407) (b:=408) (joinSmall (lo:=10594) (a:=203) (b:=204) (joinSmall (lo:=10594) (a:=101) (b:=102) (joinSmall (lo:=10594) (a:=50) (b:=51) sp10594 sp10644) (joinSmall (lo:=10695) (a:=51) (b:=51) sp10695 sp10746)) (joinSmall (lo:=10797) (a:=102) (b:=102) (joinSmall (lo:=10797) (a:=51) (b:=51) sp10797 sp10848) (joinSmall (lo:=10899) (a:=51) (b:=51) sp10899 sp10950))) (joinSmall (lo:=11001) (a:=204) (b:=204) (joinSmall (lo:=11001) (a:=102) (b:=102) (joinSmall (lo:=11001) (a:=51) (b:=51) sp11001 sp11052) (joinSmall (lo:=11103) (a:=51) (b:=51) sp11103 sp11154)) (joinSmall (lo:=11205) (a:=102) (b:=102) (joinSmall (lo:=11205) (a:=51) (b:=51) sp11205 sp11256) (joinSmall (lo:=11307) (a:=51) (b:=51) sp11307 sp11358))))) (joinSmall (lo:=11409) (a:=815) (b:=815) (joinSmall (lo:=11409) (a:=407) (b:=408) (joinSmall (lo:=11409) (a:=203) (b:=204) (joinSmall (lo:=11409) (a:=101) (b:=102) (joinSmall (lo:=11409) (a:=50) (b:=51) sp11409 sp11459) (joinSmall (lo:=11510) (a:=51) (b:=51) sp11510 sp11561)) (joinSmall (lo:=11612) (a:=102) (b:=102) (joinSmall (lo:=11612) (a:=51) (b:=51) sp11612 sp11663) (joinSmall (lo:=11714) (a:=51) (b:=51) sp11714 sp11765))) (joinSmall (lo:=11816) (a:=204) (b:=204) (joinSmall (lo:=11816) (a:=102) (b:=102) (joinSmall (lo:=11816) (a:=51) (b:=51) sp11816 sp11867) (joinSmall (lo:=11918) (a:=51) (b:=51) sp11918 sp11969)) (joinSmall (lo:=12020) (a:=102) (b:=102) (joinSmall (lo:=12020) (a:=51) (b:=51) sp12020 sp12071) (joinSmall (lo:=12122) (a:=51) (b:=51) sp12122 sp12173)))) (joinSmall (lo:=12224) (a:=407) (b:=408) (joinSmall (lo:=12224) (a:=203) (b:=204) (joinSmall (lo:=12224) (a:=101) (b:=102) (joinSmall (lo:=12224) (a:=50) (b:=51) sp12224 sp12274) (joinSmall (lo:=12325) (a:=51) (b:=51) sp12325 sp12376)) (joinSmall (lo:=12427) (a:=102) (b:=102) (joinSmall (lo:=12427) (a:=51) (b:=51) sp12427 sp12478) (joinSmall (lo:=12529) (a:=51) (b:=51) sp12529 sp12580))) (joinSmall (lo:=12631) (a:=204) (b:=204) (joinSmall (lo:=12631) (a:=102) (b:=102) (joinSmall (lo:=12631) (a:=51) (b:=51) sp12631 sp12682) (joinSmall (lo:=12733) (a:=51) (b:=51) sp12733 sp12784)) (joinSmall (lo:=12835) (a:=102) (b:=102) (joinSmall (lo:=12835) (a:=51) (b:=51) sp12835 sp12886) (joinSmall (lo:=12937) (a:=51) (b:=51) sp12937 sp12988))))))))
  have good : (List.range 13039).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 170000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 13038 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 13038 := by
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


private def packet (i : ℕ) : ℕ := (if i < 43 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 0))) else (if i < 7 then (if i < 6 then 0 else 0) else (if i < 8 then 0 else (if i < 9 then 0 else 0)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0 else 0) else (if i < 13 then 0 else (if i < 14 then 0 else 0))) else (if i < 18 then (if i < 16 then 0 else (if i < 17 then 0 else 0)) else (if i < 19 then 0 else (if i < 20 then 0 else 0))))) else (if i < 32 then (if i < 26 then (if i < 23 then (if i < 22 then 0 else 0) else (if i < 24 then 0 else (if i < 25 then 0 else 0))) else (if i < 29 then (if i < 27 then 0 else (if i < 28 then 0 else 0)) else (if i < 30 then 0 else (if i < 31 then 0 else 0)))) else (if i < 37 then (if i < 34 then (if i < 33 then 0 else 0) else (if i < 35 then 0 else (if i < 36 then 0 else 0))) else (if i < 40 then (if i < 38 then 0 else (if i < 39 then 0 else 0)) else (if i < 41 then 0 else (if i < 42 then 0 else 0)))))) else (if i < 65 then (if i < 54 then (if i < 48 then (if i < 45 then (if i < 44 then 0 else 0) else (if i < 46 then 0 else (if i < 47 then 0 else 0))) else (if i < 51 then (if i < 49 then 0 else (if i < 50 then 0 else 0)) else (if i < 52 then 0 else (if i < 53 then 0 else 0)))) else (if i < 59 then (if i < 56 then (if i < 55 then 0 else 0) else (if i < 57 then 0 else (if i < 58 then 0 else 0))) else (if i < 62 then (if i < 60 then 0 else (if i < 61 then 0 else 0)) else (if i < 63 then 0 else (if i < 64 then 0 else 0))))) else (if i < 76 then (if i < 70 then (if i < 67 then (if i < 66 then 0 else 0) else (if i < 68 then 0 else (if i < 69 then 0 else 0))) else (if i < 73 then (if i < 71 then 0 else (if i < 72 then 0 else 0)) else (if i < 74 then 0x7d2adb2ee15eca304b22288fb470c31915889483de18c09783300d80007d247b2f89638a444c823b904c74e34616c89b840619809a03500d40007d1e0f30516a0a7e4d5236104c75c34216d89d440a19c09903040c20007d17bf2ef95f4a284b02268f7c6ea31115989683e018e09503000ba0007d11583021644a5e4d0232901472832e16089a840a190095831c0bc0007d0af72f89638a544d8233900c71832415e095c3d418409583200c00007d048e3021694a804d22310ff871c32816209803e419809502f80ba0007cfe372fa961ca3c4af2298fb472232515c09443e4187093831c0d00007cf7a33141710ab44f2240108c77233c166099840819f09d83340ba0007cf1872e0957c9fe49f21b8f586f831915889343c617908882d40ba0007ceb262fc9660a6e4ca233102873832e16509a440419d0a003700d40007ce4de2f69604a364bc22d0fc470e321160894c3de18a09083040ca0007cde6f3029670a6c4d0235105877635917709e443c1ac09f833c0c20007cd8033049670a684d9239105474633e16f09e44101a209b03340c00007cd1d42e715b4a1a4ae2230f9470232b160098c40019b09783240c20007ccb3c317972cab64fd24990a478a35b1790a0c40e1a90a3037c0ee0007cc4fb2f11600a3a4b02290fb86fe31115909283c217a094030c0b40007cbea42fb9624a4c4af2248f8c70e32115e89443e419d09c03480c00007cb82330896a8a8c4dc236100c73833016d09f040219d09d03640cc0007cb1d62f51648a504b722a0fb4700324163096c3e418909503200d20007cab9d2ee15dca2a4a92278f886fa32015a094c3e818408d03080c60007ca52d2fd9668a6c4cb2300ff8734332165896c3fa19809c83140c80007c9ed32fd1674a664c622d8fb871a32716609b440e19a09c034c0d20007c9876300167ca5e4c922f0fb071032315e895c3fa19309583300ca0007c923b2f31608a464bf22f8fe0728335165896c3fa19309303100b60007c8bd33021664a704c9234904c74634117089cc40219609a83200bc0007c85832ee95e4a4e4bf2298fc471831f15e09844221a709c83280c80007c7f172fe9660a4a4ca2320ff471a31e15f899040e1ab09f83440d60007c78a4309968ca684cc230901473e33917089b44081a009883540d00007c721c3141730aba4ee247109c7823561788a044241a109c03280ca0007c6bec2ee15f8a404ca22d8fc072a32d16509943f619909883600e80007c657f30796a8a7a4d423b906c75033d16f09c840819409883180d80007c5f402f095f0a444b822d8fd472432116209783f6191097831c0b80007c58f52f215d8a224be22e0fb471832a162095840219709d02fc0ba0007c52843071684a6c4c6230903075033b16809a040a19309403000b60007c4bee31a9734ae04ff25090b477c36417e0a544481bf0a903880dc0007c45862fa9640a4a4b42280fac6fe31d160097c3fa19609683440c60007c3f262fd1658a604c322f0fbc6fe31d16089a03ee19b09b03600c80007c38a930f16c8a884e223e106875c34e1760a0442c1a3099832c0ca0007c326f2f215dca104a121d0f446e431415689383d818f09783240de0007c2bf430916a0a864e123e906076434316b09b841c1a109903380ca0007c258f3051670a704db23d105074a34716c89ac40a197099032c0b80007c1f173099684a6c4d6239103c722321160899040018e09503000bc0007c18ab3051678a584c522e0fd472a32d16209a44181a409883400ba0007c123d3061684a684d123a104873e33a16d09c84041a309f833c0dc0007c0bd72fc9634a524cd2338ff873433115d89543ba17908e02c40ac0007c05862ee95f0a264ab21d8f786f431215089003c017c09203040b60007bff1430416a8a884e9240908876e34d1798a044261af0a5039c0ee0007bf8d42e715e4a284ab21d8f6c6f230515109483d2193095031c0ca0007bf25c30896c0a8e4e323f905075233916b09cc4101ae0a203880ca0007bebe6303968ca7e4d52338ff873033816a89983f619509703240ca0007be5862fb9664a564c222d8ff872e331164898c40c19f09b83200c80007bdeff319972caca4f3244107075e33c16689c041c1ad09d83540d00007bd8c52e595aca1c4b32298fac6fa32515e89783e019609c834c0ca0007bd25430796b0a9e4e5242906474634716e09d04121a009a03400c40007bcbf42ff9680a764dc23c107076634c17389c841c1a20a103500e20007bc58d3019670a5c4be2318ff871c32616509a440c1a709a83300d80007bbf03312170cab84ec240106875633f16e89c84121a6098032c0d40007bb89b30296b8a884cf238103873c33616909b44161a009803200d00007bb26d2e915c4a224ab2270f9c71031f15e894c3be17a08c82e40bc0007bac1a2f095e4a304b22220f7870232215c09603d619809883380d40007ba5b52fb162ca2a4c42268fc871a32b16009443f019a09703280bc0007b9f4d2fc1658a5c4ce2318fc070032816309a44101ab0a183500de0007b98d33061690a664d2236102473833716b09b040a1ab0a1833c0e4000 else (if i < 75 then 0x7ec3ad3019690a7e4d52338ff474033416709a040c19009203080b40007ebd792e895dca264b02250f8070231e15a89443ec18e09203040b80007eb7482e49580a0849a21c8f446e830e15d09643c218709282f00d00007eb0cf30996b4a784e923e104475234316e09dc4201ac0a103500da0007eaa593079674a604bc2300fe871432415d89743f019409783180c80007ea3fc2fd9648a5c4c722e8fcc71a32416009643de19309983400cc0007e9da62f91664a5a4c7233101c74433416609b841e1a30a303740da0007e97413041690a8c4eb244109077435b1798a2c4301ae09983400d20007e90dd3019678a504cb2310fe472632d16789843fc19909f03380ce0007e8a912f59608a384bd22b8fbc72232c15f89883ec19a09803440e00007e84353001674a8a4d523c902474832b164099c3fe19809e83340c80007e7de12f515f4a284ba22c0fdc728331162099840419b09c835c0d20007e775a30a96f8aa64e8241106476834617209bc4101a3098831c0c20007e70f23059684a8c4db241907876834217109cc41e1a509c03380ba0007e6a8e3041644a604ce22c900070e31f15c09443e619909f83840e20007e642e2f91650a624c82348fdc72832b15b094c3ea18409582f80ba0007e5da031296fcaa84f624a10a477a3471750a2442a1bd0a583600d80007e572131016f4a9a4dc236100c744341169099840219009a833c0cc0007e50be303965ca504bb22e8fc872432616089703ea19a09e83340ba0007e4a3a31596e0aa24ea242907476634816d09e44401b30a303380ca0007e44052eb15bca224a82208fa071a329163098440219709503100c20007e3dac2fc965ca824e0239102873233a16889a83f01a009803280d60007e37512f89628a684cb235102873e33616489903fe19a09a83240b80007e30e430616bca8c4d8230900c74633716a09ac40c19a09d83040ae0007e2a713059694a7e4da238901473a33015f89a04241a209c835c0e20007e23f930a16cca7c4e323e905475a34616889a040819709903400d20007e1d9a2ff966ca684cc2330fe473c34316889943fa19d09503200c40007e174f2f39634a324af22b8fe870c31e15c89643ea18e08f83200ca0007e10dd30616b4a8a4e023b105476a33d16c89a440419d09683240d60007e0a872f99628a604c82300fc472a33616609bc41c1a309682ec0bc0007e042a2ff9668a584c722b900074433d16c09a43fa18d09503340d40007dfdb130b169ca6c4cc237102c73a33516b89a040819309883240c40007df7542f81640a604c422a0fb470e323161896c3ec18b09083100c20007df1152ef15f0a244a62268f846e431c15d098c40219409c83300ce0007deab22fc164ca4e4bf22f8fbc710322163098c3e418f09603080cc0007de45c2f8166ca524c42338fb87183321618998400194096032c0c80007dde0d2f495eca344b02248fa470a32c16409703f819609b834c0c40007dd7bb2f315f0a404c122b8f906f8316156892c3ca19109b03340c60007dd14830a96ccaa64e623a900c73e332166897c40019309683100c40007dcacb30b969ca864dd23d104876634916d89f84301a709d033c0c60007dc47a2f91600a304b72280fa471433016709d840c19d095832c0d20007dbdf730a16d0a944e9246106075433a16709843ea18a09083000d20007db7b82ed95c4a124aa2248f7c70431b159091c3d618b09603300d40007db1493029690a724ca2310fe871c32515e09743f419009582f40b80007daabb31016f0aa44e724210b47923531728a204401a90a183600c80007da44c30616b4a824db239103c74c34317009d041619e097832c0ca0007d9e072f195f0a2c4b22288f9c6fe32115e89743f01a309d834c0ca0007d976731b9738aec51024d90a877c35a1760a1043a1b00a203600d40007d91042fd1644a544c32318ffc74032f15e09683e21a0096032c0b20007d8a8b3071694a7a4da240908476634a17009c040e1a109f03540de0007d84332fa9640a564c02290fd873434216c09e440e1a909f035c0da0007d7dd03021668a684d2235102074033416309903f018b09183180ca0007d77942ea95f8a304bc22b8fcc71c32c165897c3ec19409803280ce0007d711c30916a4a784d22340fe871c33316789b040619109383240d00007d6ac32f99634a464bf22f0fc872833a160897c3f218b08f03300d60007d64672ff9684a784d8238104875434216d89ac3f819a09a03200be0007d5e0a2ff9680a664ce234100c73232a15d096040619d09a83400c00007d578a311170cab84f3247908075a34016a09943e419009883340cc0007d51053161700aa04f2246103c75033e16f09d84221af0a183640e40007d4abe2f49658a6e4cf2328fe871e32815e89883fe19609803400dc0007d443f30816c8a8e4db239903c76a34e16b89c04061a509e83700f20007d3de92fb1634a4c4be22e0fe472832e161099c41a1ad09b03180c40007d37882ff1664a684d223b103876434616b89a44101a609c83580dc0007d312b2fe165ca524ca22d0fbc72232d166897c3f0196097831c0c4000 else 0x805bc72f495f8a344b42268fa870432415d89743ec19b09c83780e80008055902e915b0a164b322a8fb070e32a15f095c3e618e09183280ae000804f0131516d8aa44e4241108477634f17089f04301af0a1035c0ec0008048ae2f4963ca504c4233903073633616a89d04281a809f03500ce00080425b2f9961ca404ad2270fb871431b15b094c3d618408f02f00c6000803be630696b0a784d2236101c74633616c89983fc19009702f80b800080356b30996bca8e4dd23e904c75034116f09e44261a90a1034c0c8000802f2b2f415f8a404b72258f9c6f230f15809243c418609082e80ae0008028c52fb9640a4e4ce234103c74233316209983f219f09583500ce00080227f2e995e4a344af22e8fa86ec30f155092c3cc18709402e00b0000801bfc30b16d4a8e4df23c103474433b168098c3f819b09c037c0de0008015c42e815e0a244b72300fe471232316489b440a1a309d03500ce000800f702f99648a644cb230901475234716c09c841419f09a034c0d00008009282f59618a424b72288f9470231215809403ca18108d83080cc0008002b5306967ca824d92350fe872032b16309a43fc19309983100b40007ffc54300966ca644c122d0fe473233316689883fe19a09b032c0c60007ff5fd2fd1658a764cb22e100873e33316589783da191099831c0d00007fefc62e715b0a144a32200f706f2312159890c3c017a09003040c20007fe94330e16e8a924e023d106075c34116909c041a1a509902f80ce0007fe2b23119704abe4f1246109077e34e1710a0c4341a70a183440da0007fdc932e315789f449221a0f5c6ea31815c89543d618d09883440d60007fd6213069690a6c4be22d0fc871e333162898c3f219809c03500da0007fcfba2fd1638a584c42308fd471a32616089683f218d09603180be0007fc95e2fc9620a4c4c12290f7c70432015b094c3ee18c09703300ce0007fc3062f89630a544b722d8fd071832415c89303ce187090834c0ec0007fbc9030896b0aa24d6237102074c33616c89c040419509603340d80007fb6263041680a7e4de23f105c75034816889984081a009e830c0c40007fafc22fa1664a464bb2280fcc70631b15a094c3de19a09d03600c40007fa9732f29640a584b92280f8470232115d095c3ea19309703340c40007fa2f330f16e8a944e223e105475834616a898c4061a109d03400e00007f9c7630f96e0a944da2388fe473033a16809984041a309d836c0ee0007f962e2ee95dca104b322a8fe872432715c09443f018909003040c20007f8feb2eb15b4a224bc22a8fc472032115c89743fc19609a83580dc0007f897c3059694a804dc238101c72433716609783ee18c08d02cc0b80007f83152fa9640a4c4bc2298ffc71632515f09783e8197097033c0cc0007f7cce2f49620a524c72320ff473634416c09bc40e19809a83300c80007f7664301167ca7a4d52358ff072c33016789b040019d09603280b80007f70063009670a664ca22c8fdc71633216409543e619009b03300c00007f69b32f215e8a264ab2268fb86fc30c15889503c618509183040bc0007f63452ff965ca6c4bd22c100473432f15d09843f019509803540e00007f5cfd2f51640a484bf22d0fb8712322161097c40419a09a03080be0007f56992fa163ca3a4be22b8fb470232816109983fe19e09d83640d20007f50412fa963ca664cf2338fe873233616289883ee1a209b03240c40007f49cd3041670a704cc22f8ffc72a33216509983f419809e03380ca0007f436230116a8aa24f124310a877034d17489c84101aa0a283680bc0007f3ce630916b4a964ea241105476834516a89d44101a409683340de0007f36b32e915a0a124b021f0f8070031f15e09703f619009583180c00007f30502fa9634a5a4c62310fdc72032e15d09583f6192096032c0bc0007f29dd307168ca784d8237902873a33916b09e84361b60a8838c0de0007f23463131714ab24f824490ac76a34716b89c04161a109e03600da0007f1d132ec15bca244a92200f5c6f030815489743ec19609a831c0d20007f16b42f415eca2c4a62208f7c6fc30a15c89443d618b09803340c40007f103530f96b0a7e4dc23d10447623561758a0442c1ac0a483800dc0007f0a0f2e395dca3e4b622a8fb872032c16309943ea19709a03200ce0007f03a93001658a684d62310ff470c31f15d89503d8191098834c0c20007efd4c2fc963ca3c4b92278fa070632315d09383ea18a09002dc0c00007ef7092ea95b8a184a82218f906fe31f15b89843fe1a309b83380ca0007ef099304168ca984e923e903474833216689983fe19309983240c80007eea2c306967ca844cf22a100473c33316a09b041e1a50a383440d80007ee3e32f61614a344b32278f84718320162095c3f419709a83280b80007edd793051698a904d52318ff073633616789cc4201a409f835c0e20007ed6ea31c9710aba4f4242108477435e17b0a1c4381b10a783600c60007ed08c2fc9640a5a4bd22c8fd072433615f09a43ec18f09903440c80007eca0431116d0aa24e8243907075e33b16a09b440c1ab09b034c0c0000)))) else (if i < 81 then (if i < 78 then (if i < 77 then 0x81f31b2f49638a4c4bf22e8fe070a31b16009703fa19709903040b800081ecd12f0961ca3c4c222b8f886f231d16309703ec194092031c0d000081e66f2fd1648a564b522b0fb871431915b89283cc18c09483040ba00081e01c2f91614a2e4b12228f80702325162097c40019c09b83280d600081d9b93019658a684da239905c75434916e89d84121a30a003380dc00081d31a31b1728aae4e2242107876634616d89d84321b00a1836c0ce00081ccac30496a0a984e4239903876a35317089f04181a009d035c0e200081c6552fb9688a6c4c82320fdc72432d16789803f819909a833c0b800081bfed30616c0a7a4d823b104c75233a16c89b43e618b09383180d000081b9b32ee962ca3c4c422f101474834a16b09a83fc19109482f80b600081b35f2f295f8a4a4c42298fd071231a15c896c3f019709d031c0c600081acea3069684a704cc232100874033d16809843f419d098034c0d000081a6ab2e495a8a004a92200f8070431e15709483d218a09283240c800081a0522ff164ca664d5236901874033516809cc40a1a70a683900f0000819a062f31628a4c4be2238f706e430214e08d83b2181090830c0c40008193ce2ed95c0a104a22200f7470030f154891c3ca17f09002fc0ba000818d752f61628a4c4c42308f9c70631f15d09503ea19a09b032c0d80008187132fc1644a624c922d8fd071e324159091c3b417608882e40c00008180b6301966ca6a4ce2340fd473433716b09a840c1a80a283900ec000817a3e30796a8a7a4d322d0fd871a32715d89743e618c096831c0ca0008173d13029674a5a4cc232100c71e32216109883f219809883240c0000816d7a2fa160ca2a4af2228f586de30415409243e619709403280b80008167262f91610a384be2308ff471a32e16109dc41c1ab0a303680cc0008160b530796a4a864da23f102874e33b16d0a184321b90a803680d0000815a872e295a0a0c49921b0f246da31815a09583d218c09183140c600081541e2fa9670a664cb22d0ff073232a165899c40619d09a03380c8000814de02ea95e4a1c4a82250fb871a33016c89a84101a109f834c0d20008147832fa163ca564c22318ffc75a34916a89c040819a09c03400c60008141162ff9638a5c4c422c0fe871a32916289b040a1a009b834c0d4000813a9630e96aca8e4e323b106c75e34617309e84201a2098033c0c600081342c302968ca8a4e5242106c75c34217509f442a1ab09d03680d4000812ddb2f495d8a184b22208f606ea31e15e89603f219409703540ca00081279d2f215e4a404ca2308fb871232215c89683f018d09683400c40008121283089678a7a4e223c106c76834e1718a0042e19e09b03540de000811ae52f29628a424bc22e8fec74033916a89b041c1ad09c83500cc0008114802ff9650a604c82310ff073a32d16309643ea19509483140c8000810e2e2fc9634a4c4c422b8fd470c31715c09403e81990a0836c0c60008107ef2ec15d4a2e4b62290f9470031b16009843f0196099832c0ca00081016e30b16d0a984e423c902c76633e16809c44121a70a103600c800080fb1f2f095e4a164a021f0f846ee31515a093c3d218609583200d600080f4b130b16c8ab64f024290807683521758a1842619909303180da00080ee4b306967ca7c4dd23b101474033d16f899c4121a409b03680da00080e7e42fc9648a484be2318fc472832a16389843f219709a03500ca00080e18a2f91628a3a4bd22d0fb872032c16289683ea19609c834c0d000080db11309167ca6c4d1236900072833c16c89bc4041ab0a0836c0c600080d4e22e51594a0e49d21c8f206d230715389403d618309082f00be00080ce7e30716a4a864d72310ff874233d16a09b040e1a40a003480c600080c8262f99648a604d72320fd071c33116689983e619909202f00b000080c1b03059680a804e823f105874433a16d09dc4161aa09c83400d800080bb482ff9644a604cc232901c73033c16909bc40c1a60a083780e200080b4d430b96b4a7e4d6230901473033a16689b841a19a09983240c400080aea62e515bca1a4a22258f8070831415208fc39c17b08a82ec0b200080a86d2e595a4a1a4b52298f9c71a32315e898040a19d09c833c0c600080a1fe306167ca6e4c32320fec72c33216889a03f01a009a83540e8000809b7e3091690a7e4d223b101473a33516389cc4281a20a1834c0c8000809515300165ca5a4b82278fb470a31815689343e218c09803400c0000808eb82f695fca324b92248fa471832415f09603d018209202ec0d000080885330096a0a8e4ef245905c74233716609a840218e095030c0ae0008081df30b16c8aa24ee240904874033816e09b441219709b034c0d4000807b8f2f395f4a3a4c72330ffc72433316689ac3f4193097832c0d600080750431016c4a8e4e6241908477234d17209f84201ab0a483780dc000806ebe2ef9614a384b42278fb870c32c16089583e618d09483540d60008068742f49604a3a4b52268fb070231915589283ce18209102c80b80008062182fd9678a6c4d6232902873a33916889a040a1a209d033c0d2000 else 0x838a612e2957c9e64942130f206d630c150091c3dc18d09483040d00008384062fc9668a524c922f0fec72832015d89583e619209783180c0000837d8e3091694a704cc2338fd070e32716289683da182090830c0c40008377332f71610a3e4c2232900072833216189903f219409503240d40008370ed2f59610a304ae2248fb470631415c09703e218709403080b2000836aba2e8159ca0e4a22228f906fc31b15d894c3d817c08f02e40ce00083643b30c16aca7e4dc239903875a34a17209ec4101a209d83340c2000835dd33041688a864e223a104c76634d16f89c84341a909c03740ec0008357752ff1650a5e4c9231101074033e166099c3e8196096032c0c80008350fa309169ca804da239106475234117009d440e1a909903540d0000834a6f31996fca9a4e323d904076435617389fc4341ae09d03640d80008344262f29614a484b922a8fb871832115b09503d018709303140ba000833ddd2f41628a4a4c42290fb470431b15e89643ee18109302f80c400083375530f16bca9c4e32390fe872432d161096c3e618a09003380d000083312c2de15749ee4922180f006d42fe14b09043bc18009202d40be000832ad22f51620a3e4b22258fa870232015e09703ea19509883540e000083249a2ec95d0a104a722a0fb070632016189a0408195096831c0b8000831e1630b16c4aa24ef243906074c34717089ec41a19f09c03500dc0008317973069680a664c6235100073c32b16789b83ec19809603140c60008311572ef15c8a104ab2290fdc72632b16589743fc19409383200d4000830ada30b96c8a8c4e2239901474033d16989d04221aa09f834c0c80008304862f39624a384b922c0fe872232516009bc3f61a109f03400da00082fe1c302967ca784d5239903875034016b89c44181a209b83300dc00082f78031b1758ae650c24f10a078434b16889b041019d09883480ca00082f10730e16bca7a4d9239102073033015f097c3fa19309903280c800082eacf2e815d0a1a4ab21d8f446de30515189143c818009003000b600082e4692fe9644a664cb233900c74233d16b89d440e1a809b033c0c800082ddfd2fe965ca5c4c722f8fb071632915d09383e418e09903400cc00082d7972f91654a604be2288fbc71832b162899040a197098031c0e200082d1452f3961ca524bc2288fa471231f15f89703ea193092833c0ce00082cae42fe9648a464ba22d100471a32015b09a840419b09c83180a800082c4ae2e695b4a1c49f2208f9471232216089803f218a094834c0c600082be532f7160ca3e4ba22c8fe872632215a895c3e819209282fc0bc00082b7f62fb965ca7c4d52399010746334165899840219c093030c0bc00082b1972fd963ca544c322e0ffc73c33a16c89d041a1a309d83440ce00082ab3e2f91644a5c4cf237902873833d16689a840e19f09e83540ca00082a4d83011658a504b822c8fb472a32d163899440619709f03500d4000829ea52e01574a004a42200f906fe31415c09643ee18c08d82f40ca0008298562ee15e4a264b22270f9c6f631d15e09743fa19309a034c0c40008291e12fd1624a364b52260fdc71e32416489883f619109c03440c4000828b932f91618a4e4b82298fc472833116389443ce18609703340ce0008285482f115e8a344b52248fac70c32815f89743da18909302f80bc000827f0d2e995c8a1e4a02220f906fa31b15c89483ea18d099032c0d400082789e30796a4a824dd237103874c34216f89ec41c1a709e03280bc00082724a2fc966ca684d5236902074c34416e09d44261a70a283880e2000826bed2f8161ca3e4ae2250f8470031a16189543ec18a09102fc0c600082658c2f4161ca444c1234101c74c33d16d09883ec19409283200c2000825f482f31628a4c4c72318ff473032e15f89803f019709703140d00008259012ee9608a244b122a0fdc73a33b16489743d818e09483240c600082528c30716a4a7a4e023b1008732337166897c3fc19a09b833c0cc000824c0f30a96cca9a4e5239101473c33116889a44061a409c03440ca0008245be2f09610a324c02340fd871032515889383f018b09182fc0ca000823f722f5962ca564c522f8fdc724323160897c4161a709a03400d00008239142f09604a404c922e0fe073633516509943f618e09683100d00008232c42f79634a4e4c622f8fe071e32516389883e218109403140d2000822c5230496b0a824df23d907077834f1770a1842e1a509c03500de0008226012f5963ca6a4cf2338ff072e32a16489743f019709c03300ce000821fb02f7161ca444bb2310fd471633716609a43fe1a409e83700d600082194c3011670a5c4db2350fe071232416009703f219609d03380d00008212e43021654a524c923b902c75834a16d89e840619909883300ce000820c6930696bca8c4e423e104476434d17109f441c1a60a083500e200082061a2f4963ca544d723b907876e34b17389e44281b50a083940f400081ffad3021670a684c52310fcc71c32b16709a440619809b83580e200081f9732e915e0a184ac21f8f746fe32615a89703f018c09683080c0000) else (if i < 79 then 0x8521bc30316c8a784d3234901c73e33716509ac40a19b09d03480d8000851b59300166ca5e4ca22b0fb870631415809303e018709703280d80008514ed3011658a4e4c22318fdc72c33416089543e419809483440d2000850e982fd161ca404c12298fd46fa31515309303d018209783380c80008508502f59638a664cc234100c73033a168098c3e819409282e40c80008501ee3011668a624d0235900c73032e16289683fa1a309d03480d000084fb922fb9654a5a4cd239102073633a16489c440a1a109a03400de00084f52030b16a8a964e223d901073e33716889c840e19a09883280c200084eecc2f7161ca4c4cb22d0fe471c32915d89383d4187094030c0ba00084e85f3089654a5a4c022f0fe073233b17089d842a1aa09c83340d200084e20e2f3160ca284ac2238fac71e32d16409b040819409803000c000084dbcd2f295d8a364ae2248fb0716324160097040019d09e03380d800084d55e3029678a6c4c922c0fd873233e16909ac40019a09503080ce00084cef63019684a7e4dd23b103073632715e89903f019509583100ca00084c8b92ec15c0a244ac2280fc070c327160095c3e819d098031c0de00084c2512fe9658a5a4c9231102073633516789843d8190095832c0ce00084bbeb2fb1630a424ba22b0fb471832416809b040819f09d83440cc00084b59a2f89660a564ba2290fa871832316109803f81a0099032c0d200084af462fa9618a4a4bb22d8fcc72432916389904041a0099834c0d200084a9292e49594a104aa2238f706d830315108e83c817a091830c0d000084a2b4303169ca8a4d8234102074a33b16589643fe1a30a183380e4000849c3330e16cca964e823b105476a34f16d89ac3f618d09803400d00008495e22f39604a424b42288f9c70e31e15c093c3dc18809202f40be000848f6f3069698a784ba233101074c33b17189fc4361aa0a103500ce0008489032fd9644a524c1236102073633c16909b43f219909b03540ec00084828c3041660a684c9232900073433a16789843e819009703480de000847c722dd95549e84922180f4c6f830c15509483da18c09282ec0b00008475de3161734ab24f1245108077034e17209b43fa19809d83480d6000846f5c30b9690a7e4d823c103c75634416f89fc4201a709e83700de00084692b2ea95d0a0c4a021b8f706f431615a09443ec19709b83300c60008462b330b96c0a924df23a904475434a16e89e441e1a90a2833c0d2000845c602f41604a1a4aa2218f6c6f831515989543e018409602f40c00008455eb3099678a704c82310fe073a33216a09b44341b209e83700e4000844f7630e16dcaae4f7247107877435b1730a144321ab09f03440d60008449492e615e4a2c4b122a0f8c6fa31715f89803fc19509503340ba0008442f02f89648a424bf22e0fd871e33216509804101a209a032c0d4000843c912fc1634a484be22d8fd473c33416889a84181a40a003540e600084362e2fe1668a6c4cb2318ffc72233616589943fe19b09b83500c8000842fed2ec95d0a1a4a621b8f9070a32715f093c3da189093832c0be00084298b3059688a7c4c92338fbc72233416d09dc4181a90a1836c0cc00084232e2fc1648a624c92330ffc74633716a89783da18c08f83140c4000841cde2f69620a504b822b8f9870e32416289603f418b093031c0c40008416a42ef15a8a004942148f286ca30715589183cc18008882b00a60008410462fc9624a224aa2228f7c6f631715a09503e818b09682ec0b8000840a062e695a8a1e4ac2240f746f031515d89583de189093030c0c60008403ca2ec15eca144a32238f946fc31d15b89583de18d093831c0bc00083fd2b31716fcaa84f124410b07883641798a3044c1b70a503640d200083f6cd2f91610a324c02328fbc72032815d893c3ca18509083200c800083f0503069698a7e4da239102475033e16a09bc42c1ab0a003780d000083e9ed301165ca664c222d8fd471e33216289a04081a109e83480e000083e3893001668a724d6231900872a33316989dc41c1ac0a003800d800083dd1e3049690a864dd23a10407423491740a1c42e1b00a283640d400083d6a830b1698a8c4d1239903073a33616a89b84181a109b03300cc00083d0792e795aca184aa2200f6c6f431e16009783e818e09783100be00083c9fa30b16bca864e8240905474e33f17109cc3fc19009783300d800083c3a12f715eca364b922a8fa471232215e09603da18508902d80b200083bd3130816b0a864ce237901074233116789c040e19b09a03440e200083b6d52f79628a424cf234102474633616b099c4121a509f834c0ce00083b06730516c0a9e4ea23d905876234816e89e04261ac0a103440d400083aa262eb95c4a324b522e0fd472432015d09403c8186092831c0ca00083a3be301167ca764d122d0fd073a32b167099c40a1ad0a3836c0de000839d592fc965ca4e4b92270fc072032c16809ac40819a09383040c400083970f2f31650a5a4bc22b8fc470632015a09503e418c09503200be0008390983089688a7c4cb2320fc072232e16209543d618809103000c0000 else (if i < 80 then 0x86b9122ff9688a684cf235100472e32a161097c3e218109003080d400086b2c22f7962ca524c62319018738334160096c3e418d09483140d000086ac3e31196e8aa64f023e105477234c16c89b43fe19209383180bc00086a5e12fd166ca5a4c522b8fec72433416a09e441819b09903440b8000869fb82e6159ca084a121f8f7c6fc30014f89083cc17f08e03080c000086995a2f3961ca424be22b0fc871632b16189643fa19309b833c0ca0008692e830c96a0a7e4cf233902c73e33816989ac4041a209b83380d8000868c88302163ca4c4c32338fc473432915f099440019609683480e200086863f2f39624a3e4c422e8fe471631d16009844021a309d03580d2000867fe92fd165ca844d82368ff072a32715e09783e618e09802ec0a60008679a02f51618a524c222a8fa470a32115d89743f418309583040a800086733c2fe1658a504c3232900071c32a16389883fe19c09d83400cc000866cd92fe167ca884dd236902c74233917009e44301a309f033c0c40008666703029678a744e323c903c76434916e89e44261a80a183600e400086600d3011680a6c4cb23a104076033f16e09c440a19f099834c0c80008659c82ed95d8a284ad2250f546f031e15f896c3d818a09503300c80008653742fa1634a4a4c022f0fe4724335163093c3d418a09203100c6000864d092fc9670a624d523b901073c32d161098440619709a03380ce0008646b52f31628a464be22d8fec71a31b15a09603f619309483280d200086403530b969ca8a4dd2350fe071c32f165096c3ca17d08d02e00b60008639d62fe964ca604cc238101474233d16909d440819c09a03280c60008633852f69614a3e4be2290fd871432815989503d819009303340dc000862d2c2f71604a3a4b522a8ff0718318160897c3e618309483040cc0008627092dd958c9fe4a32228f8871231f15b89343d618a09783400c000086209230a16b8a8a4d6238902473433016a89b84181a90a303680d4000861a312f9162ca3c4c0231901873e32f16a89d44261a909b83380d00008613ba2fe1630a524c52318fe473c33616609d04201a309b83140c2000860d6c2f395f0a284ab2260f9872232816389883f419c099831c0d4000860705302167ca784ce22d8fe073433b16a09d8406194094832c0c60008600d12ea95b8a044a321c8f4c6d831115789203e419009a03500d000085fa683019674a744d9236901073432f165899c4121a70a3837c0f000085f3fc2ff9658a704d42310fc073033416809983f818e09483180d000085ed833049674a564ca2300fcc72033b16789ac3fc198095831c0c800085e7243009654a584c82330fd471832315a09583e619309903200d400085e0e92ee15d4a1849f21d8f606e8312157892c3dc18209082f00ce00085da8e2fa964ca4a4c122a8fb870a31215589043b418109502f80ac00085d4442ee15c8a2e4af2258fc870a30e15088ec3ac17c08f03000ba00085cde2301966ca5e4c22308fd873233316389643fa19909583340de00085c7563169724acc4fc24b108877035316b89d041419709a835c0e200085c0ea30496a8a9a4e323b908477034717089d44261b009e03580d800085baa02f39600a3e4ba22e0fc471e32416209603f219a09a03500ca00085b4353011690a7c4d7235902073a33716a09bc41e19e09a03240d200085adf02f5161ca404bb22d0fe072031c15f89403ec18609182f00b200085a79d2fe1660a5a4c822b8fdc71232b15d09843fe19b0a283740cc00085a11330d1694a924e023f906078835717b8a104301ab0a183600d4000859aae2fe1654a6c4d323b108876a34d17289dc41819309383180b40008594532fe165ca6a4d32328ff874a33d16609b040a19a09b03600e0000858de830696d0aa84ec23e904075634616c89d04201b60a483740d800085875b31116d0a864e724090907783531758a204321b50a803780ec00085810e2f41620a404b822f8fdc70c31c159893c3cc18708f82fc0ca000857ae82eb15eca464b32248f9870a32315f899040e1ae0a0036c0ce00085749d2f39640a504c82318fe871832c16709b841819a09883400c8000856e3a2fd1650a604ca2308fc871832b16689a83f818f09103100c40008567d12fe1674a5a4c922f0ff873833b16d89a43fc19209983240c000085615f30c169ca824d1235900c74c34817009f44261b30a503580d0000855afb2fd963ca4c4be22a0f9471232415d09543e818f09682f00ae000855483308969ca844d32358ff473a33f16c89d04221a909d03700ce000854e0c308167ca744d923a103873e33015f89603dc19209483140c00008547bb2fb9648a5e4c12300fe871832d16209543ea18d09383380c40008541552fc960ca3e4b62308fd871a32c16309983fe19709283100d0000853b0b2f2960ca484be22a0fb06f431b15a09343d819109403140ca00085349e3059684a704cf22e8fe473233316409803fe19a09b032c0d4000852e692e8159ca144a82248f8c71a32a15f89303de18909303100c00008528222f09620a4a4b822e0fcc72432416609843f01a309c03080be000 else 0x884f602fb1614a464be22b0fcc72a32e16289943f619609a831c0d200088491e2f0960ca0e4a021e8f6871232516009603f818b09103080b40008842bb2fa9620a464bc2290fbc70a32915c896c3e418e09283180b2000883c7b2ed15f0a124b022c8fdc70631e15f09543e6191099031c0ba0008836033099698a904e623b105477035b17709d83fc18d09503200ba000882fa82fe1640a484bd2280f986f832616b09a040a1aa09b03440dc0008829303081698a844da238103c75e34016d099c3f01a209c03480d80008822ca3039658a564c122f0fd073a33216b899441c1a309a83280be000881c682fd9660a644c222e0fe471a32d16689783f019809803400ca0008816072fa1638a504c12300fec73633116789803fa19709983300dc000880f973059690a964e923d904475a34a17009d04201a909f83480cc0008809402f915e8a244ae2260f686ea321160896c3ee18f09403000d60008802d03049670a804db236103073c33316a89944101a50a5035c0de00087fc62306169ca724d3237905076034816f09c84221a60a383680d200087f61e2ef1604a3c4b822d100475a34016f0a0441819309683180cc00087efbc3009690a804d02350ff473832e16609843f219009383140b600087e9782ef9600a304b621f8f706f031515b89443e418b09603380ca00087e3312f31638a524bf22a8fd071c32d15e89783f819809682f80c800087dcd22f71620a584cc232101472632f166099440219e09a03580da00087d6922f195f4a2e4b02258fb872032015989583e018a094831c0ca00087d04c2f29620a484bb22b0fc0720333163896c3ea18709203240d400087ca122e815b4a124a321e0f5c6f6315158095c3ea19308d82f00c000087c3f12e015789f24a821a8f346da31115609243e219c09c833c0c200087bd8b30696a0a8c4e023b102473c332163097c3ee193096034c0da00087b73f2f11600a444c422f8fe8714332160893c3e418609a83480e400087b0d13031678a524c322e0fcc72832b16189603cc17808d02c80b400087aa7d2f195f0a2a4b42290fe472833316b09b840a198099833c0d000087a40f30396b4aa04e9242908476634817109fc4321b10a083340c8000879db02fd1630a3c4bf22f8fe473433816a89683ea195098031c0b400087976b2f59610a4e4c12338ffc73033416509bc40a19d09b83640ee000879103301964ca504c122e0fdc71c32616309884081a809f83440c6000878ab62f71640a424c122a8fcc71e32816609783f819f09e031c0c000087846e2f5162ca504c5231900073c33716989b440c19c09983500ce000877df83091698a824da240905c77235617b0a1043a1ab09d835c0c600087778b3011680a784d32350fe071632d163899440419c09603480cc00087715d2e395609e248920f0ebc6982eb14388c439c178091031c0d2000876b332e395a8a164a92208f9071032215c89543e418809102f40ba0008764ca2fe1678a784d1234900473833b16789d04141a209f83400d4000875e683011658a5e4d5235903874234417009d44101a70a203580dc0008757ec3071698a824df23a907475233e168898440219d09903140c00008751b12e695c0a1049921d8f986e430515489283e819009503280c6000874b3930d16bca804d9238904c75634516a09a84101a609c83300cc0008744da3021658a4e4b722a0fb872233116209803fe19909a03280d2000873e7f2f715eca324b022a0fac70032216189783fe19409783280c40008738272f29610a404c022d0fd870c32015d098441a19c09703200d80008731ca2fd1650a684d7238100474633b16989ec41e1a809f034c0d0000872b732f7965ca5e4c6234101073833816d09e041a1a109d83440c600087250d2fc9634a3c4ba2319034732333164099440019209c03380ca000871ec42f195e0a284b12298fc0702317158093c3d218309483040c400087186630216a8a9c4e4240104875234016b899840219809b03200c40008711fa3009648a684d4237903875434316f09bc3f819c09903780d0000870bb72ec95bca064962188f646d430b15c09603d618709383000c400087055c2fb9654a5e4c7238902c74c34616d09c84121a1099833c0b600086ff2c2e595a89fc49b21d8f6070631415c09883f219509e03340cc00086f8cd2fd1624a4e4c42328ff871831f167098c41419a09a03340d000086f26d2f69614a444b82298fd072a32715c09583f819909683200aa00086ebf83079698a684d2236101473833916889b04181a009c03300cc00086e5983001654a524cc2308fe471a33916809a440e19a09483280da00086df1930b16f0a964e823c9028746339167097c4061a609d030c0c200086d8cf2ef15d8a1649e2228f98702328165099c40a1a10a003600e000086d26c2fe168ca744d3238903075434c17289d44301a60a283400be00086cc022fe9628a404c222d8fc871c32c15b89483dc18209002c80ae00086c5b02f9164ca824e023d103076434c16d09a441a19b09c03740d600086bf7e2e215a8a204b12280fb470e32115e899040818f09603280d6000))) else (if i < 84 then (if i < 82 then 0x89e69b2f51624a4a4bd22e0fd472e33016389803fa19409683440c600089e0422f69610a344b92328fe871231b15c89643e819309683200bc00089da072e715d0a084aa2270f786fa31715489503e019008e82e40be00089d38d30916b8a684c722c0fbc71432b16489903f019909483380c400089cd1a3059698a744df23e105475c34016989cc4201a409d83440e200089c6d62f015cca344bc22d8fb472432e16209a43f619609483300c000089c0692fd963ca504c02300fe474a33716609b04141a409a03440c000089ba212f19608a304ab2268fb472633616a89c441019e099831c0d400089b3b4306968ca784cd236103c75434b1748a144381aa0a1036c0d200089ad642fa1650a544be2308ffc72032915b897440019209683200c000089a70c2fe9660a5a4d2234102474c33f16d09d840e1a409b03240d000089a0b02f71650a5e4cb233900873a33916309603f019609903340c6000899a1b31616ecaa04e3242105874833a16989b840a1a70a283700ec0008993ac2ff9664a4c4cf2340ff472432815e890c3c218709182fc0c4000898d562f9963ca5a4c522f0fc871232115889703fc19c09c036c0c800089871c2e895c8a224ab2298fdc71431e15a89103d218a08e02ec0ae0008980b52fc1630a484bc22b0ff472632f16a89643ee19109583140c2000897a4c2ff967ca7c4cd2320fec73c33316589903f418a09003000ca0008974072ee15fca584d3230100874033b16789a440619e09903280c4000896d8830d96d8ab84f624a90dc7903511750a244281b30a203740e200089670f30e16d4a8c4e2241107876434d17089d84221a909d83440ce0008960d32ed15dca184a62258f886f831b15c89543ee18709783240d0000895a8f2f015fca244aa2268fcc70c314160898440619b09803200cc0008954412f61628a424b422a0fa470a32216109843f218d09382d40a8000894db031016d0a9e4e323f905075434e17509f041019c09e03440d40008947413091694a6a4c6236101c73033416189703ee19909603200c20008940f22f61640a5e4ce237105475633d16209984001a009d83580d6000893aa12f81634a4c4c52298fd871e32415e897c3fc19509b037c0d800089343b3021658a484cb2310fc470631915a09643e618c09403340c6000892df72ef15f4a384af2220f9070a31a15e09583e418e09183000ba0008927c72e995b8a0a4aa2238f846ea31a15689203d018509203040b600089214630c96eca904d9239101474a34016509a83f219309883480e4000891ae430316aca664c9233101472e33616789ac3fe19b09983400d20008914a22ef15e8a3e4af2260f806fe32016109743e418e08f03040c4000890e2330d96f0a7e4e123b902c73033216a09c440a19e09502f80b60008907d62f19614a4c4bd22c8fe071832015e89683e818c09082e00b40008901702ff967ca5e4c5238900c72432b16409643e419109903300ca00088fb202f51660a524c12288fbc72232816209ac3fc19009a83300e000088f4c32fd9670a704c92360ff472232115f89603f019609503180cc00088ee642fb9638a604cc2330fdc73032c15f89703e2189093831c0ca00088e8072fe163ca4c4c22320fd472032c16009443d418a08c831c0d400088e18f30e16cca904e023a104076434416f09e44101a909b83200c200088db3f2f195fca384ac2258fac70632a162899440c1a90a1836c0d200088d50a2ea95c4a104a221e8f8c6f031015b09583f4198099833c0c600088ce9a3031644a604cd2358ff472633416a099c41c1a709f83680da00088c8223049664a824d82320ff073632e163098c3fa1ac0a483640e800088c18f3149704a944e823f903874e33c16909984021a209e03440d600088bb432f71640a544c222e0fa471a33316489683ec18b09403180cc00088b4b930a9690a784d5236103076034616b09903fe19409803240ca00088ae5c2fd1664a664c7236100472c33816e09c04141a209b83240cc00088a8062f89630a4a4bf22a8fc072a32816189403d619009382f00d000088a1d92e495aca144a82210f606e431515489283d818508d82e80c6000889b8f2f095f8a564c8235100c73032f165898c40819709803140c20008895532ee15e4a264b82230f9c70431215889103b817f08f02ec0d2000888ee52ff9650a5e4bc22a0fe873e33a16689a84081a909c03340be0008888812f7961ca364a82238f6c6fc31516009603fe19009483080c40008882452ed15f8a3a4bc22c0fec72e33216a89b43f419709683380b0000887bd33059698a8a4e023d103c75433f16a89a43fc19709883080c000088757f2f61638a504bc22d8fe873432d169099c41419409883440cc000886f412e7959ca1a4a72238f7c6f231c15f09503d618b098834c0ce0008868c430f16f0ab64f7241104075034a16d89dc4181a30a0035c0d40008862632fd9684a784cf236904c76c35317689f44321a109c03500e4000885bfb3021658a664d62358ff474234116d89a43f819409903140ca0008855c32e515d4a2c4af2248fa870c31c15609303d018809803280d0000 else (if i < 83 then 0x8b7c012ee15cca1c4a32240f606c030815609283e619009403280c40008b75b02f99628a524c9236903076234f1750a004301ae0a303600dc0008b6f592fd163ca584cd233901073833516709603de19a09883200d40008b69162ee95d8a104a92218f506dc30615709403d818a09103100c80008b62d32ef95f4a364b02238f846e031215809203c818709583380c60008b5c65302166ca4c4c422c0fe072433416b09803f618c099032c0c20008b561b2f49614a284b02260fac71631f15d093c3c017608d83040cc0008b4fca2f81620a304b02220f9470e31715c09683d6192096033c0d00008b494930f16d0a964e523e105477435017589fc4301b20a283900d80008b43172eb95dca0e4a02248f786f4320160898c3e218608f83080c40008b3c8831216c8a8c4e423e903074a32816409603f419609583200ac0008b36222fc9650a724d62338fe873033116509b03fe19609e83400c60008b2fc72fc1674a7c4cd236101874c33d16a09b441c19c0a083400dc0008b29852f015cca164ab2208f9c70832416089783f619209903480c40008b232f2f495f0a204a62208f906f431415e094c3d8187095030c0be0008b1ce02f315fca4c4c322b8fd871832015c094c3cc19309883300e20008b167c2ff1674a7c4d623b902076033e16f09b84101a809b03400d00008b10242f595e4a364bf22b8fac70a31f15b89503c618409503380c60008b09ce2fb165ca5e4c7235101c75234217089e443e1b40a283340ca0008b036b3059684a904e723f9034748335161897441a1a509803140cc0008afd152f6162ca5a4c8231900472433216609b840e1a309e836c0dc0008af6da2ec15d4a1649d21f0f8c6f231a15b096c40a1a109c03200d80008af0972f71630a3e4bd22b8fe472c32e16309683f819509803240cc0008aea5d2e4158c9f849c2190f406ca2fd15089103c617908e02f80a20008ae3e33021670a7a4d72368fdc72432415b09383da18809002ec0c60008add7c2fd1678a704d22310ff073433015f89803f019c09b03380c00008ad7143011684a844d4235900872c33216589a0402191094832c0ce0008ad0a03039680a824d523b103874e34917309d43fa1a1099030c0ba0008aca1c31016f0aa64e6242107477035016d89e84201a70a003840de0008ac3fb2de1580a024a82250fc06fc31315889243cc19008f83140c40008abdbc2f41614a3e4bf2288fb070632515f09b440c1ab0a1834c0cc0008ab754301966ca6a4d323b104474433a16889a440419809603180c00008ab0ef2fa963ca564be22d8fd073232c16989c84201a309c03480d60008aaa9f2f095e4a224ab2218f6c6fc31515909183c617d09503180bc0008aa441301167ca5e4d2237900c73233316c89dc42a1af0a083680de0008a9dd53081694a6c4cb2300ff472e33b17009d040419a09e83680e20008a97802f9961ca284a821d8f6871231f15889603ca17a08b82e40ba0008a91302f31610a4e4b422b8fd071432815f09683ec18e09403380d80008a8ad42fc964ca724d222e8fe473833b16709a03f81a60a203640ea0008a84842f315dca244b322b8fb470831c15f09683fc19809b83380e20008a7e3d2e995e8a3c4c422b8fdc72e329161896c3ee18b09103000be0008a77e62ef1608a384b52270f746ee31315909643e419809683380c40008a719d2ed9610a4e4ce22f0fc872c32d162098c40419b09603140c80008a6b482fa9634a3a4bd2300ff473e336166898841019c09d83180cc0008a64e62fe9668a6a4d223c900072432c160096c3ee19609883300da0008a5e972f515f0a364b32288fbc70e31915e09603dc18208c83080ce0008a58402f89604a364be231101473632c16389a03f218f097032c0be0008a51f73001654a584cf232901073a33f16989d04381b10a283780dc0008a4b982fb9648a384b92288fa06f631415c89643e018b09703180d60008a45592eb15c4a2a4b22268f846f031315b89683f619609b834c0d20008a3f002fc9644a524c8235101872a33116889a83ec19209403040d00008a388630516b0a724c022f0ff071632816989943fa19c09b83280d80008a32432ee95d0a364b622b0fe070a32115c09443d217908b02dc0b80008a2bf02fa1654a464c82308fd874633116509883f419d09983440c20008a257a30596acaa04df23d103474c35117a0a2c4521c10ad83c00ea0008a1f332ef15c0a0a49e21d8f986f630e15309403cc17e09082f80b20008a18d92f9161ca504b02268fb870431d16089903f419409b83500cc0008a128b2f315e8a2c4aa2260f9c6f231d16009703f0190097034c0de0008a0c6b2df95789da4962150f4c6dc30d15589303cc18209002fc0c20008a06033001668a684ca2328ff473432f16889ac40419b09b83500d400089ffb82fa1664a704d3236901473e34e17009d04241aa09c03400dc00089f97f2e595c4a2a4c022f8fb870231a15b09743e819409603540de00089f33f2f195e8a164ab22d0fd471c33416789b04181a109a83240be00089eceb2f91618a344c022a8fb470232116089443c817a09002f00bc000 else 0x8d124330a9694a8e4e623d105476c34e17109d84281b60a303800d60008d0bfd2ee95e4a364b02208f746f431c15a09543dc19709503100c80008d05a92f495f0a364bd22f8fdc71c32616509783f819809683200c40008cff6b2ea95c8a184a721e8f586dc30e15589143d817808e82f40bc0008cf9342e915a8a0a4a82230fa071a32c16209803f219009302f40b40008cf2bb3071684a744cf237904474c34116e0a0440c1a309c83880e00008cec5e2f5963ca5a4c722c0fc470a31f15689143d418b09403180ca0008ce60f2f215dca2a4b222b8fc8720327160095c3f218609483000c40008cdfb22f59634a544b722c8fdc728335162899440419509803400d20008cd96e2eb95d0a224ac2200f9472032916789983fc19809983140c60008cd31b2f31600a364c322e0fd0716326162097c3fe1a109983580d00008cccc82f49604a304b922f0fb870631315d89703f219f09a03200ba0008cc6623041698a764d1236100473833716b09a840018e09803440b60008cc03c2e895d4a144a92208f686fa32016209983fc18709603240d00008cb9e42fb15f4a364b32270fd473233016509643d418b091030c0bc0008cb38a2fc9658a5a4c422f0fb872e33016309983f0196098034c0ce0008cad222ff9660a784da233101873833e16a89b44061a009d03400bc0008ca6cf2ff1658a664dd23a105876834b17409ec40a1a309f83300cc0008ca07c2f81640a504bf22c8ff874033616909e04141ae0a183580c60008c9a192ff163ca544b02290f7c71231d15e09643dc18708f82e40c00008c938e30916c0a8c4dc237904473e33816309b840e19f09a83280be0008c8d532ee95eca3a4b82230f8470031015c09543e418009383140ca0008c86dc30c96a8a924d0234102073c33b16e89c841219709e03380ce0008c80ac2eb95fca344b32278fa071a32315f09603e418d08e830c0c00008c7a2e3099718aac4f4244909076034c16f09dc4241a1099833c0da0008c74002e3957c9f249f21c0f506e831015689443d818b09002e40c60008c6da82f9164ca504ce2300fe872032e16289903ec18909083040ce0008c67392ff9658a524c822e0fec71a32115e896440c1a009d03300cc0008c60db2fc9664a704d02320fd871a32715f895c3e819109583040c80008c5a952f11610a424bd2278f9070c31a161899440c1a909d83400d60008c54482ee15f8a3e4bc2298fc4732330166899041619a09803380c20008c4df72f7161ca584ca239903875a34717109f040819a09783400d00008c47a52fb9658a5a4c42310fb070032315e89803e2184097035c0de0008c415b2f195c4a164a32228f906fa30f15809403d817c08c02c80b60008c3b092f815f8a2a4a72220f786fc31c15b09283d218808d82f00c00008c34be2f39610a504be231101c72a33116709ac40a1a609e83440da0008c2ea82de156c9ec4982158f246d831315789443da18f09583300da0008c28562f7160ca3c4c32310ffc72e32e16709a840019409683340e60008c21cf31296d8aaa4f224b10ac77c3521730a1c4361b60a4037c0ea0008c1b6c2fc163ca584d3236904473c33d16c09cc40e19f09a833c0c20008c150c2fe9670a784d32358ff872032c164899440619709b03280cc0008c0eb82fb9640a5a4c623b906c7663491758a0c42a1a30a0833c0c20008c08403041694a784d0238102073e33315e89583ea19209803140ae0008c01d93019680a804d3233101474233e16c89ac4181a709d03400da0008bfb752fb1680a964e92419034748337167099c40619809503340d00008bf52a2f295e4a2049b21c0f586f231715809503ce18609403280c40008beee92e995d0a1a4a42250f7470232115c09303d018709002f40bc0008be874305167ca7e4d323a904c7683461720a004421b20a3838c0d80008be2312e995d8a2e4b02280fb471432815e09543ec18f09102f80b40008bdbc630516a8a964dd23e904074a34116b89883f218e099033c0ce0008bd55b3019674a704cf232101072a32915e897c3ec19109783180cc0008bcef730296c8aa44e823d901473632c16009803fa19c09a03400d60008bc8993031660a604c2235901473632a16089883f619809803480c80008bc2343019688a744cc2339008732330166099040e19709c83680f40008bbbf32ed15f4a0e4a42228fa070831615509343d618f09783500d60008bb5932f3964ca504c02328ff073432b16589a840619e09c83440cc0008baf342fc165ca664c92340fec72e33315a893c3ee19a09683300ca0008ba8bb30796a8a924e023c104474433716589983fe19e09603380ca0008ba24030a9688a704c422f8fe4712333168099c40019509783200ce0008b9c142e795d0a264af2268f8c6f0310159890c3c017e08f82e40b60008b95af3019674a5c4c92290fe0710321156895c3cc18809103100c40008b8f2031296dca924e723f105c76034c1738a204341b00a383580d60008b88ae3061668a564bf22a0fb071a32c16309b441419f098032c0ae0008b823f30a9688a764dc239903c7683561758a104381a80a3036c0d4000)) else (if i < 85 then 0x8ea7f62f61638a424b32280fb071632715b89683e019209b83200d40008ea1a72f81618a324be22a8fd470e31d15e097c3f619309283040ac0008e9b5a2f6160ca284b82268f6c6e6310153893c3dc18509102f40ce0008e94c931016d0a9a4e8238903875033d16b09e44141a20a383400de0008e8e722fe1638a3e4bd22c0fc071832716289743f819a09983200ca0008e88242f51608a3e4c2235902c75033716209883f419909b03140c20008e81c13049694a764da23b0ff472632a16409943f819109983200cc0008e7b782f315e0a224ac2288fb46fe31515f89703d618b09302f40b40008e754f2e615a4a124a621b0f786ec30b15709103ce18308c82f80d00008e6efd2f315fca2e4b42290fb471a32c16689a03f619309983380bc0008e688b31196c0a864db23f102474a34116989c041219f09883300ca0008e621a300965ca5e4d5237904075834717189d041e1a80a4835c0c40008e5bf22e6959ca0a49d2268f8c70231b16209603dc18a09382d40b00008e55ad2ea15c8a284b52270fa472032d15f896c40419609203380b60008e4f5f2f29610a3e4bf22e8fc471a32c16589ac4061a109b83300ca0008e48e130e96e4aaa4e4242905076034f17609f041e1af0a0835c0ce0008e42932f195e0a424bb2288fa870031815d095c3e018f09503200dc0008e3c3c2f91614a204a92258fb871e31f16009903fc1a00a003800ea0008e35fd2f015dca3c4a92220f806ee31315589083c817e09403180c20008e2f9230416aca7a4df242906c76834816709783d618f098833c0d60008e291a30316a8a7e4d42338fec71e32716509a440819509283040c00008e22a430716b0a884d7236103c738331167898c40a1a609c03440d20008e1c552f7162ca544c8233902472232b15e89483e419e09803180c40008e15e73031664a7c4da23b0ffc72433716c899c3ee19109603100b20008e0fa22ef95c0a204a92248f8870032715e09703ea19209483140d40008e09552f89600a424ae22c0f9471831315c893c3de18e09203040c20008e02f02fe9670a604c7234100471032916889a84161a809f03500e80008dfc973001678a744d92360ffc73033716989c04261a40a0834c0d60008df61c31216e4a984f3245106875a34b16c09c840c19609b83240c40008def9d3071690a6c4d4239103874833516b099440419a09b83480e20008de9562f41618a4a4ca2308fe8730333166098040619409603140c40008de2f62fc9640a584ba2268fc471a32715e896c3f819209403180d20008ddc952f9164ca5c4cd234900873e33816b09e040c19a09883280c00008dd6502ed95f0a4a4bf22d8fec72832e16409b441219609c03480d40008dd0322de95849e44922170f8071e32616489a83f819909a033c0ce0008dc9e22f595f8a2a4a42248f946fe32716689803f0195098832c0ca0008dc35b30e96c4a9a4e523f102873c33916a09bc4101af09c83480c00008dbd012f79620a4c4ba22b0fd872e32f163099c40a19b09a835c0cc0008db693300967ca6a4d8239100075833c16e09dc42219f09d83700d80008db05f2e795d0a184a72270f806f431c15b89783e019c09783200c40008daa022fd1650a604d9234901c74033916809b840c19e094831c0c00008da3a42fb1610a284b82250f786fe320159093c3d018808c82d40b40008d9d662ee15f0a2c4ad2218f9871632d16709943f219209a83680cc0008d97063021678a5c4ce238901073a33716789dc4101a309e83600cc0008d90923049694a6a4cf230100873832f16209a440019b09683140be0008d8a3a2fa1640a524b82280fa870632115f094c3dc18a09183040ca0008d83f02f59610a404bf22a8fac71032115e096c3e018b09a03040be0008d7dc52e215a8a104a621d8f346dc30515409043b818008982b40b80008d77802fa1618a3a4bb22d0fc871432a16709983fc19909983340c80008d712e2f51604a444bd22e0fc871e32515989303d618e09503040ce0008d6ae22f11640a4a4bd2298fa870431f15a094c3e818e09502f00b60008d64bc2dd15649f04912198f346ca31215a09483e819009583000ce0008d5e4130e96e4aa84f5244907475434a166097840419e09e03340cc0008d57d23019658a624c622f100073433016709b44281af09f03680ea0008d515c30d16e4a9e4ea23d106876835016d09cc41019e0a083300cc0008d4b2e2e4956c9ec4932170f5c6ee31615a89543e618f09683180d40008d44f72e915eca264a52290fa4714326168097840c19c09703400d40008d3e903021668a704d3239903876234e17189d841019a0a283440de0008d384c2ec95d0a1a4bc2288fa4700322164099040418f09382fc0c40008d31f72f19630a544cb2318ff071833016689b040819d09903380de0008d2bb72ea95cca1c4a32228f786f431f15d09403e0191095830c0c00008d254e2fe9650a784d02360ff475033d16d89bc40c1a3096831c0d40008d1f132ec95b4a064912180f206de30c15409183ca190092830c0d00008d18b92f595fca344ae2260f906fe31f15f09703d018409103040b6000 else (if i < 86 then 0x903db73009660a624da23e904874434716e09e042e1a70a003500cc0009037642f5962ca524d023d900873833816509b440619d09903600c80009030f630496b8a844d3239903875233a16709c83fc19b09703100cc000902ab82f195e4a304b42210f486e831715789443dc19709a031c0c80009024572fd967ca5a4c522f8ff872c33616909a440419309a83340d4000901df82ff1664a624ca22b8ff071832916289603ee18a09803040c60009017a02f9161ca464ad22a8f9c70c32515c09443fa19b09683380bc0009011452fb9638a3e4b22288fe071832a16189bc3fa1a309f03200be000900b072ee95f4a384b12290f806f630d151893c3d818c09482f80b80009004a52fa9614a424c82318ff073c33a16909b440e19909803240da0008ffe5f2eb95d8a2c4b822c8fc470e32716089ac4261a509683400ca0008ff8192ec95d4a344ae2238f9070631715a093c3ea18e09403340cc0008ff1bb2fd9648a5c4c122d8ffc73a33c16889a4412196098834c0c60008feb782f3160ca344b322a8fa46f631816189683e418109183180ca0008fe5063039664a604cf238903073832916109603c217c08e83200ca0008fde5d3169704ab44f4244107875834717109f042e1aa0a3036c0c80008fd81d2ec15bca2c4b32278fac70e32016409943f219309a03400c20008fd1e02ea15e8a2a4af2250fa071832f15f09643e819909e83440d60008fcb912f59660a4e4b52298fbc71232c15e09743f2192095830c0b40008fc5472f71604a2e4ba22e8fcc70e32715f894c3fc19609c83340cc0008fbee3301167ca724c9232100073a33916909ac3f819309f83580e20008fb8942f3960ca324b722a0fc071632316009803ec19309603080c40008fb2472f4961ca444ca2300fd471631f160099840e1a909b83300c60008fac022ee95e4a3e4ba2248fbc70a31b15d897c3f818d09503240c40008fa5923001674a584c022c0fb870832216009643ea19609a032c0be0008f9f352fa164ca524bf22d8fe470c328163898840019009b83380ca0008f98cf3021684a864dd23d905875e34717189f04121aa09c83680dc0008f92af2e015649f249121e0f386dc30415709243ca18d09103000c00008f8c48300165ca624da23e905876a34f17189b83fa19a099033c0d20008f85d93071690a8a4d4237901c74234316c89a440a19509883180d00008f7f872f51640a524ce232901474433816509b040e19809b83580c60008f79302f11610a384ae2248fac71432015709283b417d08b02e80ae0008f72d42fa9610a344be22d0fcc720329161899c408194095031c0d40008f6ca82e915d4a164aa2208fa070031c15b89543d018a09203180cc0008f665f2f315f4a344b922c0fcc71432216189643e818b091831c0ce0008f5fe230916a0a9a4f3248908c75a3491728a384541bd0ac03c00fe0008f59992f195e8a284ae2250fa06ee31415789643dc18709182f00ca0008f53572f29604a4e4c72328fc071c32716509b03f619709903440dc0008f4cfd2f99658a764d12378fc0718334167099c3f419709803140c60008f467a3119720aac4fb23f108476634516b89d441019f09603280e20008f40292f415f0a1e4b22290fb071632015a896440e19d09d03700e40008f39ec2e895c0a2a4aa21d8f5c6d830614c89143d217f09003100d00008f336b30b96bca964ea242107076c34c17b8a5444a1bc0a703800ea0008f2d182f5162ca464bb2288fcc71e32e16309843fc19c09903200c20008f26d12ed15e8a244aa2240f9070631715989283d418d097031c0b60008f20852f4961ca3e4bb22a0ff472432916109a03f819709803340ca0008f1a3a2f41604a4c4b82260fa871031b15d89803f019109603080b60008f13de2fd1644a5c4cd232903075234116689a03fa19f096030c0b60008f0d702ff9658a5e4ca2358ff0734339165098840a19c09c83440d40008f073f2e515c8a244b52280f7c6f231a15709243d418709683400c60008f00d33029660a744c82310fc472a33d16c89bc42c1a7099831c0ca0008efa75300165ca804d8234901073633816c89c04181a309f831c0ca0008ef413300162ca584c522d0fd872032716509a83ec18c09803400bc0008eedd12f29610a364bd2278fb870031d15b89403b817e09103040cc0008ee757307168ca764d5234904076a34917209ec41c1aa0a303700e20008ee0f52fd9674a6e4ca2321000726330161099840019d09c03380cc0008edab92e7958ca164ac2248f9871633216689c840a19d09783140c40008ed47f2df95789d24892130f306d4302156896c3e618709483040bc0008ece242f91618a3e4bb22b8ff873e33716d89c040c198099832c0c60008ec7b83059698a6a4cc234101073e34216b89b041019e09b83400d40008ec1712ed95fca344aa2268fa4710325161896c3f019a09a03480cc0008ebafe30b16d0a904e0241907075834917289d441219c09d83400d20008eb4b62f395fca344c222b0fb872032f160897c3ea18509303340c40008eae4a2ff1678a704d32350ffc73c33e16a89d441619e09783340ce000 else 0x90fbe40001670a724cb2300fe472432a16889983ee195097031c0d200090f5c72da1584a144a62248f906fc31915809183c017f09383100d200090ef7d2ee15f4a324af2270fa870a31e15d897440619909583300c600090e9153059670a844d623b904875234b17489e44181ae09e035c0e000090e2da2ec95c0a244b12258f986fe31a15989343de17b09102e00b800090dc4331116d8a9e4eb245907877435516f89d841a1a50a483600de00090d6112eb15d4a204b32280f706f831015689383ee18609383140be00090cfc92f49614a404cc2328ff073233416989d040219409d83680ce00090c9603021678a6c4c72358fd472232716009743ee18e09703100c600090c3272e4957ca064a421e8f7c6e630815589243ce17908a02e00b200090bce32f195d4a1e4b02280fcc72e32915f89843f018a09903240ce00090b6962f99654a724da23f102476034c1708a0441c19e09603000ba00090b04b2f81630a604b722b8fec72432916489983fe1a309e835c0cc00090a9fd2f2961ca524b722b0fa071431d164099c3fe1a409703300d000090a394300163ca604bc22c8fe472632116289843f018f094831c0ca000909d2a2ff9688a724d523a103073a32516109343d619309b83300d40009096cc2fc1648a5c4d323a102473c33816e09b83f619b09b03400be0009090802f115d8a244b12248fa86fa31715c09643c817808802e80a8000908a342f91624a444bd22d8fbc73833216509803ec19409883440d20009083b330a16a8a864e023f107c76e34f16c8a044321b20a583880de000907d3330c16c4a904e023a107077c3521790a084221ab09d03580d80009076d42f89624a504c32268f886f831515909283be18509803100be00090707f2f71618a444c922d0fa470431c15f89403ea18f09203200c0000906a0d3091680a7c4d82368ff4732329161097840c19f09b83300ce00090639830896aca884d5233900874033916b09803fa19a09b03180c4000905d602ea95c0a2c4b322b0fe072232f16409843e818a09003240c800090572f2e4957c9e24a32298fd071632816209a0402193098031c0c60009050c72f6162ca5c4b62268fac71a33116209a040819a09983400c8000904a7f2f415eca3e4c522b8fb0722326160897c40819409a03280d60009044153019690a7c4df23a101074833616d09c840219a09783400c2000)))))))

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



private theorem b75484 : covered 75484 75571 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b75571 : covered 75571 75657 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b75657 : covered 75657 75744 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b75744 : covered 75744 75830 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b75830 : covered 75830 75917 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b75917 : covered 75917 76003 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b76003 : covered 76003 76090 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b76090 : covered 76090 76176 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b76176 : covered 76176 76263 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b76263 : covered 76263 76349 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b76349 : covered 76349 76436 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b76436 : covered 76436 76522 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b76522 : covered 76522 76609 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b76609 : covered 76609 76695 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b76695 : covered 76695 76782 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b76782 : covered 76782 76868 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b76868 : covered 76868 76955 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b76955 : covered 76955 77041 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b77041 : covered 77041 77128 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b77128 : covered 77128 77214 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b77214 : covered 77214 77301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b77301 : covered 77301 77387 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b77387 : covered 77387 77474 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b77474 : covered 77474 77560 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b77560 : covered 77560 77646 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b77646 : covered 77646 77732 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b77732 : covered 77732 77819 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b77819 : covered 77819 77905 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b77905 : covered 77905 77992 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b77992 : covered 77992 78078 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b78078 : covered 78078 78165 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b78165 : covered 78165 78251 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b78251 : covered 78251 78338 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b78338 : covered 78338 78424 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b78424 : covered 78424 78511 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b78511 : covered 78511 78597 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b78597 : covered 78597 78684 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b78684 : covered 78684 78770 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b78770 : covered 78770 78857 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b78857 : covered 78857 78943 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b78943 : covered 78943 79030 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b79030 : covered 79030 79116 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b79116 : covered 79116 79203 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b79203 : covered 79203 79289 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b79289 : covered 79289 79376 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b79376 : covered 79376 79462 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b79462 : covered 79462 79549 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b79549 : covered 79549 79635 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b79635 : covered 79635 79722 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b79722 : covered 79722 79808 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b79808 : covered 79808 79895 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b79895 : covered 79895 79981 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b79981 : covered 79981 80068 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b80068 : covered 80068 80154 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b80154 : covered 80154 80241 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b80241 : covered 80241 80327 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b80327 : covered 80327 80413 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b80413 : covered 80413 80499 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b80499 : covered 80499 80586 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b80586 : covered 80586 80672 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b80672 : covered 80672 80759 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b80759 : covered 80759 80845 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b80845 : covered 80845 80932 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b80932 : covered 80932 81018 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b81018 : covered 81018 81105 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b81105 : covered 81105 81191 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b81191 : covered 81191 81278 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b81278 : covered 81278 81364 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b81364 : covered 81364 81451 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b81451 : covered 81451 81537 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b81537 : covered 81537 81624 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b81624 : covered 81624 81710 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b81710 : covered 81710 81797 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b81797 : covered 81797 81883 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b81883 : covered 81883 81970 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b81970 : covered 81970 82056 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b82056 : covered 82056 82143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b82143 : covered 82143 82229 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b82229 : covered 82229 82316 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b82316 : covered 82316 82402 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b82402 : covered 82402 82489 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b82489 : covered 82489 82575 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b82575 : covered 82575 82662 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b82662 : covered 82662 82748 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b82748 : covered 82748 82835 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b82835 : covered 82835 82921 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b82921 : covered 82921 83008 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b83008 : covered 83008 83094 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b83094 : covered 83094 83180 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b83180 : covered 83180 83266 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b83266 : covered 83266 83353 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b83353 : covered 83353 83439 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b83439 : covered 83439 83526 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b83526 : covered 83526 83612 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b83612 : covered 83612 83699 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b83699 : covered 83699 83785 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b83785 : covered 83785 83872 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b83872 : covered 83872 83958 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b83958 : covered 83958 84045 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b84045 : covered 84045 84131 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b84131 : covered 84131 84218 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b84218 : covered 84218 84304 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b84304 : covered 84304 84391 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b84391 : covered 84391 84477 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b84477 : covered 84477 84564 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b84564 : covered 84564 84650 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b84650 : covered 84650 84737 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b84737 : covered 84737 84823 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b84823 : covered 84823 84910 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b84910 : covered 84910 84996 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b84996 : covered 84996 85083 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b85083 : covered 85083 85169 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b85169 : covered 85169 85256 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b85256 : covered 85256 85342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b85342 : covered 85342 85429 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b85429 : covered 85429 85515 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b85515 : covered 85515 85602 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b85602 : covered 85602 85688 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b85688 : covered 85688 85775 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b85775 : covered 85775 85861 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b85861 : covered 85861 85947 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b85947 : covered 85947 86033 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b86033 : covered 86033 86120 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b86120 : covered 86120 86206 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b86206 : covered 86206 86293 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b86293 : covered 86293 86379 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b86379 : covered 86379 86466 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b86466 : covered 86466 86552 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b86552 : covered 86552 86639 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b86639 : covered 86639 86725 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b86725 : covered 86725 86812 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b86812 : covered 86812 86898 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b86898 : covered 86898 86985 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b86985 : covered 86985 87071 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b87071 : covered 87071 87158 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b87158 : covered 87158 87244 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b87244 : covered 87244 87331 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b87331 : covered 87331 87417 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b87417 : covered 87417 87504 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b87504 : covered 87504 87590 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b87590 : covered 87590 87677 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b87677 : covered 87677 87763 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b87763 : covered 87763 87850 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b87850 : covered 87850 87936 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b87936 : covered 87936 88023 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b88023 : covered 88023 88109 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b88109 : covered 88109 88196 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b88196 : covered 88196 88282 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b88282 : covered 88282 88369 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b88369 : covered 88369 88455 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b88455 : covered 88455 88542 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 75484 88542 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b75484 b75571) (joinCoverage b75657 b75744)) (joinCoverage (joinCoverage b75830 b75917) (joinCoverage b76003 (joinCoverage b76090 b76176)))) (joinCoverage (joinCoverage (joinCoverage b76263 b76349) (joinCoverage b76436 b76522)) (joinCoverage (joinCoverage b76609 b76695) (joinCoverage b76782 (joinCoverage b76868 b76955))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b77041 b77128) (joinCoverage b77214 b77301)) (joinCoverage (joinCoverage b77387 b77474) (joinCoverage b77560 (joinCoverage b77646 b77732)))) (joinCoverage (joinCoverage (joinCoverage b77819 b77905) (joinCoverage b77992 (joinCoverage b78078 b78165))) (joinCoverage (joinCoverage b78251 b78338) (joinCoverage b78424 (joinCoverage b78511 b78597)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b78684 b78770) (joinCoverage b78857 b78943)) (joinCoverage (joinCoverage b79030 b79116) (joinCoverage b79203 (joinCoverage b79289 b79376)))) (joinCoverage (joinCoverage (joinCoverage b79462 b79549) (joinCoverage b79635 (joinCoverage b79722 b79808))) (joinCoverage (joinCoverage b79895 b79981) (joinCoverage b80068 (joinCoverage b80154 b80241))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b80327 b80413) (joinCoverage b80499 b80586)) (joinCoverage (joinCoverage b80672 b80759) (joinCoverage b80845 (joinCoverage b80932 b81018)))) (joinCoverage (joinCoverage (joinCoverage b81105 b81191) (joinCoverage b81278 (joinCoverage b81364 b81451))) (joinCoverage (joinCoverage b81537 b81624) (joinCoverage b81710 (joinCoverage b81797 b81883))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b81970 b82056) (joinCoverage b82143 b82229)) (joinCoverage (joinCoverage b82316 b82402) (joinCoverage b82489 (joinCoverage b82575 b82662)))) (joinCoverage (joinCoverage (joinCoverage b82748 b82835) (joinCoverage b82921 (joinCoverage b83008 b83094))) (joinCoverage (joinCoverage b83180 b83266) (joinCoverage b83353 (joinCoverage b83439 b83526))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b83612 b83699) (joinCoverage b83785 b83872)) (joinCoverage (joinCoverage b83958 b84045) (joinCoverage b84131 (joinCoverage b84218 b84304)))) (joinCoverage (joinCoverage (joinCoverage b84391 b84477) (joinCoverage b84564 (joinCoverage b84650 b84737))) (joinCoverage (joinCoverage b84823 b84910) (joinCoverage b84996 (joinCoverage b85083 b85169)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b85256 b85342) (joinCoverage b85429 b85515)) (joinCoverage (joinCoverage b85602 b85688) (joinCoverage b85775 (joinCoverage b85861 b85947)))) (joinCoverage (joinCoverage (joinCoverage b86033 b86120) (joinCoverage b86206 (joinCoverage b86293 b86379))) (joinCoverage (joinCoverage b86466 b86552) (joinCoverage b86639 (joinCoverage b86725 b86812))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b86898 b86985) (joinCoverage b87071 b87158)) (joinCoverage (joinCoverage b87244 b87331) (joinCoverage b87417 (joinCoverage b87504 b87590)))) (joinCoverage (joinCoverage (joinCoverage b87677 b87763) (joinCoverage b87850 (joinCoverage b87936 b88023))) (joinCoverage (joinCoverage b88109 b88196) (joinCoverage b88282 (joinCoverage b88369 b88455))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 75484 ≤ index 145000000/512 := by decide +kernel
private theorem starting_value : fast 145000000=8178593 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 145000000=8178593) (n : ℕ) (low : 145000000≤n) (bound : n≤170000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=145000000
    · rw [first,anchor]
      exact starting_value
    · have past : 145000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤170000000 by omega)
        have within : index n / 512 < 88542 := by omega
        have lower : index 145000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤170000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ145000000To170000000
