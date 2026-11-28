import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ270000000To295000000

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




private def radical : ℕ := 0xdec2a1aa15f00da4c207c9e2f6bbe115ea97d507204b9cc70907de6fe7b751c225b7148297c5d4fd44a95feec5708db49d4d9bb68b34ef128502a8fe914e07a7751bb32b05997045f9816c288a5d49ddd432c03b43016960e9c42297b0a69718e333e630758b85efe87f18351affc011d831de5cbde56fa9d0c60f5727f57d1186385fb16e403c45d7c35934be411228ade666d06e02d9b9d5d4a9f26dc39e8cc179865a34b1f88ccd509f2ecd76b4d308e4a7b2911e48413fcd012273f2f74ad29953b9b61d2974df92662d0918d0f0d1f6d46f82aa5665b885f33f53b7791eec9771fd0fe39a0ebc0adc68d7a46ec3822711520289d137754dd366fb916bd6d5c05c9d1801462b56508c7c35c44774a0ae708432006370b4ae78832e46268ee37951a0d42136477f243c8fa07814f3ec6eb1ca126814b2ab8270bb5841ce2c988ac3cbff4ad10837ebb498e7b17205591b17756875f06daf2512537d57badc8641218129fafbf39ac3c739330e7fcb954fb3d3cf79d3305739c489679a67d2b6a2a48bb043a16604b3a708f908a22d7dd097c6844fa3162f6b6d9add358573fceb72f6d54909eecbe6e744ea8abc44977acd71a4803688548345afbe5874b7bf9719981e5f9d5759b70521b5fe67fee7d62e9a4196acbbff33a02c5b5175f10c744b85c60acf085f5e408d9fda2b57ae9e2d3a08d2c0a07a1b50ebc68de3f8f8087bdc2b9f450a1d2116ac9d3eeac27b12946cee6c62ab6dd5fa34073cfcd409599c30450988e8901e8c8f376b1a24b8dcf153c7df7d352210a3d91754eb02cfebf1610a1e9fb05f70f7c8908f7dff9086f6c6323cedff761f28ae0a150fe470e1d59e36f47114267535c3230870637d008b61c5db251688f95e0994ee8ba8a34edf508b9361f7c0b7d1a0fae9aa4f1d5a305a65011eda259c3a2a005bab696e6d793e657a44ee7bd5b644ccdda1c5785bdbbf3929f799dc2d32c55fcd11637b70ff7e3bcc4d2fa6eb69adcf7e44eef9b2ac25431e35fbe5c4df90baa41e02963092a6ceb84947f8a5d1961fd67c942264816a40189e8c1e966e92134a10e721794e0dbf2cfc4c505cd80e666d5dea5f5bd6d37a9e46d0d2f20955836172f4b6c677591632f933c240991a5bb9a0402bf95016ad497843457ea4f172564cdf12c6b8bd2cd1097e0bf97ce2d5a525738d3b2de2dfce1a6888628f18e44528c635cecb0cefca395f0f6c3da8d0fd528ee3d947abce191c8e6f85890039942397804fea8f7c4d56a5b011fb40edb406068619b0e93df1a23ac5225e686d88115ef8e7d528e3ff2d542b91d7e9158095042029ae242bd104cc59a6237dbf2b6f0593f229509d0bd916bc7031f469912e2c0a27807855bbca29c368f9218a1c3dc6ea7dc3720a1704f3e90cc68f687e945c4695777e00bac996f12411b788273ceaad505ee27626feaf3f8819b103c3c608a4a9788e7bf835c6b3781d3552f736a044a790449732ab7f01e2661b57b2d89444e92b720d7d63b4d2d9d3d45bad39cc02ff733f8a280a87ca6f1ba00b625c81e508e6aa0b005612f4e294f82407ba4d1cf0c4052fb3b138af2503944d37acf4ebfc3d364e1cb5ba4e9005dd94e42b02eede45fce3298a51f8cf5e22a5ad1b2895b086e96aacd08bfe0f207daa112fc80f65ef567c3418faf3dd4d87a1167df9ade8ccc79f29eb8ac25c5e869c9111f7ed5f86c98854c77bed6fdc06635cae3d75c36c5b0376a0155b5fc9b827c7f0c964a77be3f4eed77b911e592c6643d12ad34b60e68704251e435abf71ef2f7bb3f09656b1d53df272c8d82f4d4aab1e050cb39b010a62160e11ba67b1b60a238f0dd5b2969a08b49b7a7f4b04071063b7a788eb8ff1557bcc5559cf9d5aaf2c9376d9b2a6c461373f10f423b0d973d9cd25ccf8cc00d939663933b6d1c778a6463201195bdef8e99686125e4cf7c7c89cf9d4219b09d5df05a191c9fb7537ba357666146c9400e6e191289cb6cfeb7b6b3690d3ecbe922189d50e32b181dc38242e9dc933622e2ab84d26e02417f6b4807abe122a0b04ad9b85c90bd51261f462b83c23a285fe5aec2de282dba622a07d2365463aadfc81db2f007dc547e29bd3d295589e40d936a9874eef79f2e234b17c889bd2b33dd6cd9f1063790d139603c9ecd1101bb0a63317d6c26e60e122e24303ffb02c14f2e752edee183ebc94478f7770ceb4776f8ee214dc3afb75815b1c44b679a68cf139330c4f3985051d40905b7ad8872ea396f3dd6d55b6e179ddb7e74e23083713aa532f3e57fcb254122f61daa322c506fc1afc13f6fff3952efd68f60381c7258f8fe2fac1d1e145729d2170a4f79daa7081abb2624895847dc92af6aaee5502764a9027792d6820e9d0caab8c79949c99a9bec34e4ccc83ee159ac8ceece6750fc2b17f5b315c065e917a314efd76bfd7ef608401d790d84ae34f3ed40b74560a05d573d1e628e2dd5bcc626ebeeb34746c5b29a9d2268902e872222ea9234c3bf9a6a3614f8f44caa832fea751a27bb94d5da1e74ef3b11670f93aeb6c1a068eb46c505cf62521e5e281403bc84eb7db647bf47dd3ffe1086b9ea311b1b01ee6074c19f9fe0bfb62dcc9637d181e8ee39b9c520ff8d56c60e24218721111de85b8db367cde99b01aef75b994228876135b34e7c08b411576456b87272900616cdc5ebc00f15426e9f264c332dd142c15a5a17247bdb7a92b6e4288d9292954fcc5ca873ff62ae7612a40dedeb5501c31bc1c4961bf16a8646e1a06545a83e5202819476555698b34eb90718e33914acb03509dffc679340816f520caf201a7577db7eb449b608d2ccb4df9e7c2aad192d37bd501fade4249f5365af363bec01e205095c89fa31b453b6ff1296bac6eafab2f679686f1ab985340bf6380ac02852e615fbac9d29d6eb136c9ade1508b7bf65f329228e1b9b55c7c3114634b51f9c71d2b58d50fb33e46bc0e9dd8021e3c639c65e1506f0ff447cf139e7132b39853292fd5f2ed00d24a2cd801fa7952128cba1e126706b341acf617554d83ec9678e84d01a10b84e704fc1e33d1136be95d6ebc24fae1bd441f1a3f83d3f32324e78270b81aac1ce2cdf0f7133eb3b5443b864a18cb1c6ca315c0631526e5ea271d9e1104416e6a4fe2880c450c58674fde2e352143d523f2fdd8e1ab7529154519373ecc77a9cbc7e72af299a674a9114a38144eade9b4f8c607a9b471666e03b37d06e9602d5a27f570159b0a4c3ebcc8b6bbe3a1718b5fc1e5792fbf7859ee8b50a6f641774ad591d67d7c6ea8b12a193c1ccdb8d6bb5c6d62a335c232dbae41ee0322131632522ec701e8cd042a7596b758345b7e58afb0ad76aa87ae6da2164f39e5cfb31fbacea512540d641f3e09147b4a73c98a6d94938cc2712a9bbdb4012f696fae1fd3b0004d4ff9b917ef3d16710b7b26ff34a11168efdb7c4321f248590c88b2051a7290fae447d4bd204456033952e7936db0a0ebd0b69766aca56ef1dc4edac88847aab3ac23c697c33d4a701b356ee158fba955490e0830737d11329de36f7c5f2c6fd0a13ef19c65b7ed0bc2ae37db957fd2ec9f57157e4114dbd1b0840e063697d4d7a3c075d065ee7d781ecacfa55bd037af42bb0ef60031a8fe42f5a04163a84d8916b1fb936bd87547356044feaa49d2993ef2c9fdaa4885cb988d97ed73c3521f6afa02d273e74ea92e9f7f8e1424967624c921220344ea0c2ae52ac4085b274e3bf7dda66fc0934bcc44a3b5cd6c63b303aa89b5b90fe67be28690e4f0542d40580345aa303d6dc5e7eb1e52e1d5d5ec77eefd786c35589483fc2cb6f746acb3e029c51200410b2278c74abebd3587ddcd19d88010ceacfdc0b279624336243c44cbf41961bde5600daeb8f1a47df9a82c3632ae4520a520932b161e32aa09d2050070b38772ac2491d8e1d12d21e2cfedafc8f7992ed2ee73891bbefce9b9d1659e37f77e4e8e2ef449d7783717022f319002a7cd81b639a6b6ffa0c37e784389d78a379ba489065e8c00a575595071ecf5c1b490449662e9073c7645ccc9a0faf678e0223d6f3d307839df4d72e9ffe95b6a9aeb1e4c6c9b5b1b27b9ea624f7766e4a22afadee9cb47278cc0039432b0e054343c8b2425d1f84fc3347133ecbfaa2883cb6a6bbe1927280cd0d13bea6f8527125efd5629960584079aa8dc662ae5f1c60507437b5da1fafaea07d17e8e2a6a4cf68562228db1efd5089a26960edcbf80781936fbd566049c8ef35576b33004a5a02a9322b1035074f76d90251d16094cf4a723b3c2ab624b1cbb08d4c0a02e808d5b26a

private def light (n : ℕ) : Bool :=
  if n≤131 then decide n.Prime else n.gcd 847158069087882051098456875815279568163352087665474498775849754305766436915303927682164623187034167333264599970492141556534816949699515865660644961729169613882287309922474300878212776434073600000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤17175) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 131 = 847158069087882051098456875815279568163352087665474498775849754305766436915303927682164623187034167333264599970492141556534816949699515865660644961729169613882287309922474300878212776434073600000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 131 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤17175 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 33 := by unfold smallValid; decide +kernel

private theorem sp33 : smallValid 33 34 := by unfold smallValid; decide +kernel

private theorem sp67 : smallValid 67 33 := by unfold smallValid; decide +kernel

private theorem sp100 : smallValid 100 34 := by unfold smallValid; decide +kernel

private theorem sp134 : smallValid 134 33 := by unfold smallValid; decide +kernel

private theorem sp167 : smallValid 167 34 := by unfold smallValid; decide +kernel

private theorem sp201 : smallValid 201 33 := by unfold smallValid; decide +kernel

private theorem sp234 : smallValid 234 34 := by unfold smallValid; decide +kernel

private theorem sp268 : smallValid 268 33 := by unfold smallValid; decide +kernel

private theorem sp301 : smallValid 301 34 := by unfold smallValid; decide +kernel

private theorem sp335 : smallValid 335 33 := by unfold smallValid; decide +kernel

private theorem sp368 : smallValid 368 34 := by unfold smallValid; decide +kernel

private theorem sp402 : smallValid 402 33 := by unfold smallValid; decide +kernel

private theorem sp435 : smallValid 435 34 := by unfold smallValid; decide +kernel

private theorem sp469 : smallValid 469 33 := by unfold smallValid; decide +kernel

private theorem sp502 : smallValid 502 34 := by unfold smallValid; decide +kernel

private theorem sp536 : smallValid 536 33 := by unfold smallValid; decide +kernel

private theorem sp569 : smallValid 569 34 := by unfold smallValid; decide +kernel

private theorem sp603 : smallValid 603 33 := by unfold smallValid; decide +kernel

private theorem sp636 : smallValid 636 34 := by unfold smallValid; decide +kernel

private theorem sp670 : smallValid 670 33 := by unfold smallValid; decide +kernel

private theorem sp703 : smallValid 703 34 := by unfold smallValid; decide +kernel

private theorem sp737 : smallValid 737 33 := by unfold smallValid; decide +kernel

private theorem sp770 : smallValid 770 34 := by unfold smallValid; decide +kernel

private theorem sp804 : smallValid 804 33 := by unfold smallValid; decide +kernel

private theorem sp837 : smallValid 837 34 := by unfold smallValid; decide +kernel

private theorem sp871 : smallValid 871 33 := by unfold smallValid; decide +kernel

private theorem sp904 : smallValid 904 34 := by unfold smallValid; decide +kernel

private theorem sp938 : smallValid 938 33 := by unfold smallValid; decide +kernel

private theorem sp971 : smallValid 971 34 := by unfold smallValid; decide +kernel

private theorem sp1005 : smallValid 1005 34 := by unfold smallValid; decide +kernel

private theorem sp1039 : smallValid 1039 34 := by unfold smallValid; decide +kernel

private theorem sp1073 : smallValid 1073 33 := by unfold smallValid; decide +kernel

private theorem sp1106 : smallValid 1106 34 := by unfold smallValid; decide +kernel

private theorem sp1140 : smallValid 1140 33 := by unfold smallValid; decide +kernel

private theorem sp1173 : smallValid 1173 34 := by unfold smallValid; decide +kernel

private theorem sp1207 : smallValid 1207 33 := by unfold smallValid; decide +kernel

private theorem sp1240 : smallValid 1240 34 := by unfold smallValid; decide +kernel

private theorem sp1274 : smallValid 1274 33 := by unfold smallValid; decide +kernel

private theorem sp1307 : smallValid 1307 34 := by unfold smallValid; decide +kernel

private theorem sp1341 : smallValid 1341 33 := by unfold smallValid; decide +kernel

private theorem sp1374 : smallValid 1374 34 := by unfold smallValid; decide +kernel

private theorem sp1408 : smallValid 1408 33 := by unfold smallValid; decide +kernel

private theorem sp1441 : smallValid 1441 34 := by unfold smallValid; decide +kernel

private theorem sp1475 : smallValid 1475 33 := by unfold smallValid; decide +kernel

private theorem sp1508 : smallValid 1508 34 := by unfold smallValid; decide +kernel

private theorem sp1542 : smallValid 1542 34 := by unfold smallValid; decide +kernel

private theorem sp1576 : smallValid 1576 34 := by unfold smallValid; decide +kernel

private theorem sp1610 : smallValid 1610 33 := by unfold smallValid; decide +kernel

private theorem sp1643 : smallValid 1643 34 := by unfold smallValid; decide +kernel

private theorem sp1677 : smallValid 1677 33 := by unfold smallValid; decide +kernel

private theorem sp1710 : smallValid 1710 34 := by unfold smallValid; decide +kernel

private theorem sp1744 : smallValid 1744 33 := by unfold smallValid; decide +kernel

private theorem sp1777 : smallValid 1777 34 := by unfold smallValid; decide +kernel

private theorem sp1811 : smallValid 1811 33 := by unfold smallValid; decide +kernel

private theorem sp1844 : smallValid 1844 34 := by unfold smallValid; decide +kernel

private theorem sp1878 : smallValid 1878 33 := by unfold smallValid; decide +kernel

private theorem sp1911 : smallValid 1911 34 := by unfold smallValid; decide +kernel

private theorem sp1945 : smallValid 1945 33 := by unfold smallValid; decide +kernel

private theorem sp1978 : smallValid 1978 34 := by unfold smallValid; decide +kernel

private theorem sp2012 : smallValid 2012 33 := by unfold smallValid; decide +kernel

private theorem sp2045 : smallValid 2045 34 := by unfold smallValid; decide +kernel

private theorem sp2079 : smallValid 2079 34 := by unfold smallValid; decide +kernel

private theorem sp2113 : smallValid 2113 34 := by unfold smallValid; decide +kernel

private theorem sp2147 : smallValid 2147 33 := by unfold smallValid; decide +kernel

private theorem sp2180 : smallValid 2180 34 := by unfold smallValid; decide +kernel

private theorem sp2214 : smallValid 2214 33 := by unfold smallValid; decide +kernel

private theorem sp2247 : smallValid 2247 34 := by unfold smallValid; decide +kernel

private theorem sp2281 : smallValid 2281 33 := by unfold smallValid; decide +kernel

private theorem sp2314 : smallValid 2314 34 := by unfold smallValid; decide +kernel

private theorem sp2348 : smallValid 2348 33 := by unfold smallValid; decide +kernel

private theorem sp2381 : smallValid 2381 34 := by unfold smallValid; decide +kernel

private theorem sp2415 : smallValid 2415 33 := by unfold smallValid; decide +kernel

private theorem sp2448 : smallValid 2448 34 := by unfold smallValid; decide +kernel

private theorem sp2482 : smallValid 2482 33 := by unfold smallValid; decide +kernel

private theorem sp2515 : smallValid 2515 34 := by unfold smallValid; decide +kernel

private theorem sp2549 : smallValid 2549 33 := by unfold smallValid; decide +kernel

private theorem sp2582 : smallValid 2582 34 := by unfold smallValid; decide +kernel

private theorem sp2616 : smallValid 2616 33 := by unfold smallValid; decide +kernel

private theorem sp2649 : smallValid 2649 34 := by unfold smallValid; decide +kernel

private theorem sp2683 : smallValid 2683 33 := by unfold smallValid; decide +kernel

private theorem sp2716 : smallValid 2716 34 := by unfold smallValid; decide +kernel

private theorem sp2750 : smallValid 2750 33 := by unfold smallValid; decide +kernel

private theorem sp2783 : smallValid 2783 34 := by unfold smallValid; decide +kernel

private theorem sp2817 : smallValid 2817 33 := by unfold smallValid; decide +kernel

private theorem sp2850 : smallValid 2850 34 := by unfold smallValid; decide +kernel

private theorem sp2884 : smallValid 2884 33 := by unfold smallValid; decide +kernel

private theorem sp2917 : smallValid 2917 34 := by unfold smallValid; decide +kernel

private theorem sp2951 : smallValid 2951 33 := by unfold smallValid; decide +kernel

private theorem sp2984 : smallValid 2984 34 := by unfold smallValid; decide +kernel

private theorem sp3018 : smallValid 3018 33 := by unfold smallValid; decide +kernel

private theorem sp3051 : smallValid 3051 34 := by unfold smallValid; decide +kernel

private theorem sp3085 : smallValid 3085 33 := by unfold smallValid; decide +kernel

private theorem sp3118 : smallValid 3118 34 := by unfold smallValid; decide +kernel

private theorem sp3152 : smallValid 3152 34 := by unfold smallValid; decide +kernel

private theorem sp3186 : smallValid 3186 34 := by unfold smallValid; decide +kernel

private theorem sp3220 : smallValid 3220 33 := by unfold smallValid; decide +kernel

private theorem sp3253 : smallValid 3253 34 := by unfold smallValid; decide +kernel

private theorem sp3287 : smallValid 3287 33 := by unfold smallValid; decide +kernel

private theorem sp3320 : smallValid 3320 34 := by unfold smallValid; decide +kernel

private theorem sp3354 : smallValid 3354 33 := by unfold smallValid; decide +kernel

private theorem sp3387 : smallValid 3387 34 := by unfold smallValid; decide +kernel

private theorem sp3421 : smallValid 3421 33 := by unfold smallValid; decide +kernel

private theorem sp3454 : smallValid 3454 34 := by unfold smallValid; decide +kernel

private theorem sp3488 : smallValid 3488 33 := by unfold smallValid; decide +kernel

private theorem sp3521 : smallValid 3521 34 := by unfold smallValid; decide +kernel

private theorem sp3555 : smallValid 3555 33 := by unfold smallValid; decide +kernel

private theorem sp3588 : smallValid 3588 34 := by unfold smallValid; decide +kernel

private theorem sp3622 : smallValid 3622 33 := by unfold smallValid; decide +kernel

private theorem sp3655 : smallValid 3655 34 := by unfold smallValid; decide +kernel

private theorem sp3689 : smallValid 3689 34 := by unfold smallValid; decide +kernel

private theorem sp3723 : smallValid 3723 34 := by unfold smallValid; decide +kernel

private theorem sp3757 : smallValid 3757 33 := by unfold smallValid; decide +kernel

private theorem sp3790 : smallValid 3790 34 := by unfold smallValid; decide +kernel

private theorem sp3824 : smallValid 3824 33 := by unfold smallValid; decide +kernel

private theorem sp3857 : smallValid 3857 34 := by unfold smallValid; decide +kernel

private theorem sp3891 : smallValid 3891 33 := by unfold smallValid; decide +kernel

private theorem sp3924 : smallValid 3924 34 := by unfold smallValid; decide +kernel

private theorem sp3958 : smallValid 3958 33 := by unfold smallValid; decide +kernel

private theorem sp3991 : smallValid 3991 34 := by unfold smallValid; decide +kernel

private theorem sp4025 : smallValid 4025 33 := by unfold smallValid; decide +kernel

private theorem sp4058 : smallValid 4058 34 := by unfold smallValid; decide +kernel

private theorem sp4092 : smallValid 4092 33 := by unfold smallValid; decide +kernel

private theorem sp4125 : smallValid 4125 34 := by unfold smallValid; decide +kernel

private theorem sp4159 : smallValid 4159 33 := by unfold smallValid; decide +kernel

private theorem sp4192 : smallValid 4192 34 := by unfold smallValid; decide +kernel

private theorem sp4226 : smallValid 4226 34 := by unfold smallValid; decide +kernel

private theorem sp4260 : smallValid 4260 34 := by unfold smallValid; decide +kernel

private theorem sp4294 : smallValid 4294 33 := by unfold smallValid; decide +kernel

private theorem sp4327 : smallValid 4327 34 := by unfold smallValid; decide +kernel

private theorem sp4361 : smallValid 4361 33 := by unfold smallValid; decide +kernel

private theorem sp4394 : smallValid 4394 34 := by unfold smallValid; decide +kernel

private theorem sp4428 : smallValid 4428 33 := by unfold smallValid; decide +kernel

private theorem sp4461 : smallValid 4461 34 := by unfold smallValid; decide +kernel

private theorem sp4495 : smallValid 4495 33 := by unfold smallValid; decide +kernel

private theorem sp4528 : smallValid 4528 34 := by unfold smallValid; decide +kernel

private theorem sp4562 : smallValid 4562 33 := by unfold smallValid; decide +kernel

private theorem sp4595 : smallValid 4595 34 := by unfold smallValid; decide +kernel

private theorem sp4629 : smallValid 4629 33 := by unfold smallValid; decide +kernel

private theorem sp4662 : smallValid 4662 34 := by unfold smallValid; decide +kernel

private theorem sp4696 : smallValid 4696 33 := by unfold smallValid; decide +kernel

private theorem sp4729 : smallValid 4729 34 := by unfold smallValid; decide +kernel

private theorem sp4763 : smallValid 4763 33 := by unfold smallValid; decide +kernel

private theorem sp4796 : smallValid 4796 34 := by unfold smallValid; decide +kernel

private theorem sp4830 : smallValid 4830 33 := by unfold smallValid; decide +kernel

private theorem sp4863 : smallValid 4863 34 := by unfold smallValid; decide +kernel

private theorem sp4897 : smallValid 4897 33 := by unfold smallValid; decide +kernel

private theorem sp4930 : smallValid 4930 34 := by unfold smallValid; decide +kernel

private theorem sp4964 : smallValid 4964 33 := by unfold smallValid; decide +kernel

private theorem sp4997 : smallValid 4997 34 := by unfold smallValid; decide +kernel

private theorem sp5031 : smallValid 5031 33 := by unfold smallValid; decide +kernel

private theorem sp5064 : smallValid 5064 34 := by unfold smallValid; decide +kernel

private theorem sp5098 : smallValid 5098 33 := by unfold smallValid; decide +kernel

private theorem sp5131 : smallValid 5131 34 := by unfold smallValid; decide +kernel

private theorem sp5165 : smallValid 5165 33 := by unfold smallValid; decide +kernel

private theorem sp5198 : smallValid 5198 34 := by unfold smallValid; decide +kernel

private theorem sp5232 : smallValid 5232 33 := by unfold smallValid; decide +kernel

private theorem sp5265 : smallValid 5265 34 := by unfold smallValid; decide +kernel

private theorem sp5299 : smallValid 5299 34 := by unfold smallValid; decide +kernel

private theorem sp5333 : smallValid 5333 34 := by unfold smallValid; decide +kernel

private theorem sp5367 : smallValid 5367 33 := by unfold smallValid; decide +kernel

private theorem sp5400 : smallValid 5400 34 := by unfold smallValid; decide +kernel

private theorem sp5434 : smallValid 5434 33 := by unfold smallValid; decide +kernel

private theorem sp5467 : smallValid 5467 34 := by unfold smallValid; decide +kernel

private theorem sp5501 : smallValid 5501 33 := by unfold smallValid; decide +kernel

private theorem sp5534 : smallValid 5534 34 := by unfold smallValid; decide +kernel

private theorem sp5568 : smallValid 5568 33 := by unfold smallValid; decide +kernel

private theorem sp5601 : smallValid 5601 34 := by unfold smallValid; decide +kernel

private theorem sp5635 : smallValid 5635 33 := by unfold smallValid; decide +kernel

private theorem sp5668 : smallValid 5668 34 := by unfold smallValid; decide +kernel

private theorem sp5702 : smallValid 5702 33 := by unfold smallValid; decide +kernel

private theorem sp5735 : smallValid 5735 34 := by unfold smallValid; decide +kernel

private theorem sp5769 : smallValid 5769 33 := by unfold smallValid; decide +kernel

private theorem sp5802 : smallValid 5802 34 := by unfold smallValid; decide +kernel

private theorem sp5836 : smallValid 5836 34 := by unfold smallValid; decide +kernel

private theorem sp5870 : smallValid 5870 34 := by unfold smallValid; decide +kernel

private theorem sp5904 : smallValid 5904 33 := by unfold smallValid; decide +kernel

private theorem sp5937 : smallValid 5937 34 := by unfold smallValid; decide +kernel

private theorem sp5971 : smallValid 5971 33 := by unfold smallValid; decide +kernel

private theorem sp6004 : smallValid 6004 34 := by unfold smallValid; decide +kernel

private theorem sp6038 : smallValid 6038 33 := by unfold smallValid; decide +kernel

private theorem sp6071 : smallValid 6071 34 := by unfold smallValid; decide +kernel

private theorem sp6105 : smallValid 6105 33 := by unfold smallValid; decide +kernel

private theorem sp6138 : smallValid 6138 34 := by unfold smallValid; decide +kernel

private theorem sp6172 : smallValid 6172 33 := by unfold smallValid; decide +kernel

private theorem sp6205 : smallValid 6205 34 := by unfold smallValid; decide +kernel

private theorem sp6239 : smallValid 6239 33 := by unfold smallValid; decide +kernel

private theorem sp6272 : smallValid 6272 34 := by unfold smallValid; decide +kernel

private theorem sp6306 : smallValid 6306 33 := by unfold smallValid; decide +kernel

private theorem sp6339 : smallValid 6339 34 := by unfold smallValid; decide +kernel

private theorem sp6373 : smallValid 6373 34 := by unfold smallValid; decide +kernel

private theorem sp6407 : smallValid 6407 34 := by unfold smallValid; decide +kernel

private theorem sp6441 : smallValid 6441 33 := by unfold smallValid; decide +kernel

private theorem sp6474 : smallValid 6474 34 := by unfold smallValid; decide +kernel

private theorem sp6508 : smallValid 6508 33 := by unfold smallValid; decide +kernel

private theorem sp6541 : smallValid 6541 34 := by unfold smallValid; decide +kernel

private theorem sp6575 : smallValid 6575 33 := by unfold smallValid; decide +kernel

private theorem sp6608 : smallValid 6608 34 := by unfold smallValid; decide +kernel

private theorem sp6642 : smallValid 6642 33 := by unfold smallValid; decide +kernel

private theorem sp6675 : smallValid 6675 34 := by unfold smallValid; decide +kernel

private theorem sp6709 : smallValid 6709 33 := by unfold smallValid; decide +kernel

private theorem sp6742 : smallValid 6742 34 := by unfold smallValid; decide +kernel

private theorem sp6776 : smallValid 6776 33 := by unfold smallValid; decide +kernel

private theorem sp6809 : smallValid 6809 34 := by unfold smallValid; decide +kernel

private theorem sp6843 : smallValid 6843 33 := by unfold smallValid; decide +kernel

private theorem sp6876 : smallValid 6876 34 := by unfold smallValid; decide +kernel

private theorem sp6910 : smallValid 6910 33 := by unfold smallValid; decide +kernel

private theorem sp6943 : smallValid 6943 34 := by unfold smallValid; decide +kernel

private theorem sp6977 : smallValid 6977 33 := by unfold smallValid; decide +kernel

private theorem sp7010 : smallValid 7010 34 := by unfold smallValid; decide +kernel

private theorem sp7044 : smallValid 7044 33 := by unfold smallValid; decide +kernel

private theorem sp7077 : smallValid 7077 34 := by unfold smallValid; decide +kernel

private theorem sp7111 : smallValid 7111 33 := by unfold smallValid; decide +kernel

private theorem sp7144 : smallValid 7144 34 := by unfold smallValid; decide +kernel

private theorem sp7178 : smallValid 7178 33 := by unfold smallValid; decide +kernel

private theorem sp7211 : smallValid 7211 34 := by unfold smallValid; decide +kernel

private theorem sp7245 : smallValid 7245 33 := by unfold smallValid; decide +kernel

private theorem sp7278 : smallValid 7278 34 := by unfold smallValid; decide +kernel

private theorem sp7312 : smallValid 7312 33 := by unfold smallValid; decide +kernel

private theorem sp7345 : smallValid 7345 34 := by unfold smallValid; decide +kernel

private theorem sp7379 : smallValid 7379 33 := by unfold smallValid; decide +kernel

private theorem sp7412 : smallValid 7412 34 := by unfold smallValid; decide +kernel

private theorem sp7446 : smallValid 7446 34 := by unfold smallValid; decide +kernel

private theorem sp7480 : smallValid 7480 34 := by unfold smallValid; decide +kernel

private theorem sp7514 : smallValid 7514 33 := by unfold smallValid; decide +kernel

private theorem sp7547 : smallValid 7547 34 := by unfold smallValid; decide +kernel

private theorem sp7581 : smallValid 7581 33 := by unfold smallValid; decide +kernel

private theorem sp7614 : smallValid 7614 34 := by unfold smallValid; decide +kernel

private theorem sp7648 : smallValid 7648 33 := by unfold smallValid; decide +kernel

private theorem sp7681 : smallValid 7681 34 := by unfold smallValid; decide +kernel

private theorem sp7715 : smallValid 7715 33 := by unfold smallValid; decide +kernel

private theorem sp7748 : smallValid 7748 34 := by unfold smallValid; decide +kernel

private theorem sp7782 : smallValid 7782 33 := by unfold smallValid; decide +kernel

private theorem sp7815 : smallValid 7815 34 := by unfold smallValid; decide +kernel

private theorem sp7849 : smallValid 7849 33 := by unfold smallValid; decide +kernel

private theorem sp7882 : smallValid 7882 34 := by unfold smallValid; decide +kernel

private theorem sp7916 : smallValid 7916 33 := by unfold smallValid; decide +kernel

private theorem sp7949 : smallValid 7949 34 := by unfold smallValid; decide +kernel

private theorem sp7983 : smallValid 7983 34 := by unfold smallValid; decide +kernel

private theorem sp8017 : smallValid 8017 34 := by unfold smallValid; decide +kernel

private theorem sp8051 : smallValid 8051 33 := by unfold smallValid; decide +kernel

private theorem sp8084 : smallValid 8084 34 := by unfold smallValid; decide +kernel

private theorem sp8118 : smallValid 8118 33 := by unfold smallValid; decide +kernel

private theorem sp8151 : smallValid 8151 34 := by unfold smallValid; decide +kernel

private theorem sp8185 : smallValid 8185 33 := by unfold smallValid; decide +kernel

private theorem sp8218 : smallValid 8218 34 := by unfold smallValid; decide +kernel

private theorem sp8252 : smallValid 8252 33 := by unfold smallValid; decide +kernel

private theorem sp8285 : smallValid 8285 34 := by unfold smallValid; decide +kernel

private theorem sp8319 : smallValid 8319 33 := by unfold smallValid; decide +kernel

private theorem sp8352 : smallValid 8352 34 := by unfold smallValid; decide +kernel

private theorem sp8386 : smallValid 8386 33 := by unfold smallValid; decide +kernel

private theorem sp8419 : smallValid 8419 34 := by unfold smallValid; decide +kernel

private theorem sp8453 : smallValid 8453 33 := by unfold smallValid; decide +kernel

private theorem sp8486 : smallValid 8486 34 := by unfold smallValid; decide +kernel

private theorem sp8520 : smallValid 8520 34 := by unfold smallValid; decide +kernel

private theorem sp8554 : smallValid 8554 34 := by unfold smallValid; decide +kernel

private theorem sp8588 : smallValid 8588 33 := by unfold smallValid; decide +kernel

private theorem sp8621 : smallValid 8621 34 := by unfold smallValid; decide +kernel

private theorem sp8655 : smallValid 8655 33 := by unfold smallValid; decide +kernel

private theorem sp8688 : smallValid 8688 34 := by unfold smallValid; decide +kernel

private theorem sp8722 : smallValid 8722 33 := by unfold smallValid; decide +kernel

private theorem sp8755 : smallValid 8755 34 := by unfold smallValid; decide +kernel

private theorem sp8789 : smallValid 8789 33 := by unfold smallValid; decide +kernel

private theorem sp8822 : smallValid 8822 34 := by unfold smallValid; decide +kernel

private theorem sp8856 : smallValid 8856 33 := by unfold smallValid; decide +kernel

private theorem sp8889 : smallValid 8889 34 := by unfold smallValid; decide +kernel

private theorem sp8923 : smallValid 8923 33 := by unfold smallValid; decide +kernel

private theorem sp8956 : smallValid 8956 34 := by unfold smallValid; decide +kernel

private theorem sp8990 : smallValid 8990 33 := by unfold smallValid; decide +kernel

private theorem sp9023 : smallValid 9023 34 := by unfold smallValid; decide +kernel

private theorem sp9057 : smallValid 9057 33 := by unfold smallValid; decide +kernel

private theorem sp9090 : smallValid 9090 34 := by unfold smallValid; decide +kernel

private theorem sp9124 : smallValid 9124 33 := by unfold smallValid; decide +kernel

private theorem sp9157 : smallValid 9157 34 := by unfold smallValid; decide +kernel

private theorem sp9191 : smallValid 9191 33 := by unfold smallValid; decide +kernel

private theorem sp9224 : smallValid 9224 34 := by unfold smallValid; decide +kernel

private theorem sp9258 : smallValid 9258 33 := by unfold smallValid; decide +kernel

private theorem sp9291 : smallValid 9291 34 := by unfold smallValid; decide +kernel

private theorem sp9325 : smallValid 9325 33 := by unfold smallValid; decide +kernel

private theorem sp9358 : smallValid 9358 34 := by unfold smallValid; decide +kernel

private theorem sp9392 : smallValid 9392 33 := by unfold smallValid; decide +kernel

private theorem sp9425 : smallValid 9425 34 := by unfold smallValid; decide +kernel

private theorem sp9459 : smallValid 9459 33 := by unfold smallValid; decide +kernel

private theorem sp9492 : smallValid 9492 34 := by unfold smallValid; decide +kernel

private theorem sp9526 : smallValid 9526 33 := by unfold smallValid; decide +kernel

private theorem sp9559 : smallValid 9559 34 := by unfold smallValid; decide +kernel

private theorem sp9593 : smallValid 9593 34 := by unfold smallValid; decide +kernel

private theorem sp9627 : smallValid 9627 34 := by unfold smallValid; decide +kernel

private theorem sp9661 : smallValid 9661 33 := by unfold smallValid; decide +kernel

private theorem sp9694 : smallValid 9694 34 := by unfold smallValid; decide +kernel

private theorem sp9728 : smallValid 9728 33 := by unfold smallValid; decide +kernel

private theorem sp9761 : smallValid 9761 34 := by unfold smallValid; decide +kernel

private theorem sp9795 : smallValid 9795 33 := by unfold smallValid; decide +kernel

private theorem sp9828 : smallValid 9828 34 := by unfold smallValid; decide +kernel

private theorem sp9862 : smallValid 9862 33 := by unfold smallValid; decide +kernel

private theorem sp9895 : smallValid 9895 34 := by unfold smallValid; decide +kernel

private theorem sp9929 : smallValid 9929 33 := by unfold smallValid; decide +kernel

private theorem sp9962 : smallValid 9962 34 := by unfold smallValid; decide +kernel

private theorem sp9996 : smallValid 9996 33 := by unfold smallValid; decide +kernel

private theorem sp10029 : smallValid 10029 34 := by unfold smallValid; decide +kernel

private theorem sp10063 : smallValid 10063 33 := by unfold smallValid; decide +kernel

private theorem sp10096 : smallValid 10096 34 := by unfold smallValid; decide +kernel

private theorem sp10130 : smallValid 10130 34 := by unfold smallValid; decide +kernel

private theorem sp10164 : smallValid 10164 34 := by unfold smallValid; decide +kernel

private theorem sp10198 : smallValid 10198 33 := by unfold smallValid; decide +kernel

private theorem sp10231 : smallValid 10231 34 := by unfold smallValid; decide +kernel

private theorem sp10265 : smallValid 10265 33 := by unfold smallValid; decide +kernel

private theorem sp10298 : smallValid 10298 34 := by unfold smallValid; decide +kernel

private theorem sp10332 : smallValid 10332 33 := by unfold smallValid; decide +kernel

private theorem sp10365 : smallValid 10365 34 := by unfold smallValid; decide +kernel

private theorem sp10399 : smallValid 10399 33 := by unfold smallValid; decide +kernel

private theorem sp10432 : smallValid 10432 34 := by unfold smallValid; decide +kernel

private theorem sp10466 : smallValid 10466 33 := by unfold smallValid; decide +kernel

private theorem sp10499 : smallValid 10499 34 := by unfold smallValid; decide +kernel

private theorem sp10533 : smallValid 10533 33 := by unfold smallValid; decide +kernel

private theorem sp10566 : smallValid 10566 34 := by unfold smallValid; decide +kernel

private theorem sp10600 : smallValid 10600 33 := by unfold smallValid; decide +kernel

private theorem sp10633 : smallValid 10633 34 := by unfold smallValid; decide +kernel

private theorem sp10667 : smallValid 10667 34 := by unfold smallValid; decide +kernel

private theorem sp10701 : smallValid 10701 34 := by unfold smallValid; decide +kernel

private theorem sp10735 : smallValid 10735 33 := by unfold smallValid; decide +kernel

private theorem sp10768 : smallValid 10768 34 := by unfold smallValid; decide +kernel

private theorem sp10802 : smallValid 10802 33 := by unfold smallValid; decide +kernel

private theorem sp10835 : smallValid 10835 34 := by unfold smallValid; decide +kernel

private theorem sp10869 : smallValid 10869 33 := by unfold smallValid; decide +kernel

private theorem sp10902 : smallValid 10902 34 := by unfold smallValid; decide +kernel

private theorem sp10936 : smallValid 10936 33 := by unfold smallValid; decide +kernel

private theorem sp10969 : smallValid 10969 34 := by unfold smallValid; decide +kernel

private theorem sp11003 : smallValid 11003 33 := by unfold smallValid; decide +kernel

private theorem sp11036 : smallValid 11036 34 := by unfold smallValid; decide +kernel

private theorem sp11070 : smallValid 11070 33 := by unfold smallValid; decide +kernel

private theorem sp11103 : smallValid 11103 34 := by unfold smallValid; decide +kernel

private theorem sp11137 : smallValid 11137 33 := by unfold smallValid; decide +kernel

private theorem sp11170 : smallValid 11170 34 := by unfold smallValid; decide +kernel

private theorem sp11204 : smallValid 11204 33 := by unfold smallValid; decide +kernel

private theorem sp11237 : smallValid 11237 34 := by unfold smallValid; decide +kernel

private theorem sp11271 : smallValid 11271 33 := by unfold smallValid; decide +kernel

private theorem sp11304 : smallValid 11304 34 := by unfold smallValid; decide +kernel

private theorem sp11338 : smallValid 11338 33 := by unfold smallValid; decide +kernel

private theorem sp11371 : smallValid 11371 34 := by unfold smallValid; decide +kernel

private theorem sp11405 : smallValid 11405 33 := by unfold smallValid; decide +kernel

private theorem sp11438 : smallValid 11438 34 := by unfold smallValid; decide +kernel

private theorem sp11472 : smallValid 11472 33 := by unfold smallValid; decide +kernel

private theorem sp11505 : smallValid 11505 34 := by unfold smallValid; decide +kernel

private theorem sp11539 : smallValid 11539 33 := by unfold smallValid; decide +kernel

private theorem sp11572 : smallValid 11572 34 := by unfold smallValid; decide +kernel

private theorem sp11606 : smallValid 11606 33 := by unfold smallValid; decide +kernel

private theorem sp11639 : smallValid 11639 34 := by unfold smallValid; decide +kernel

private theorem sp11673 : smallValid 11673 33 := by unfold smallValid; decide +kernel

private theorem sp11706 : smallValid 11706 34 := by unfold smallValid; decide +kernel

private theorem sp11740 : smallValid 11740 34 := by unfold smallValid; decide +kernel

private theorem sp11774 : smallValid 11774 34 := by unfold smallValid; decide +kernel

private theorem sp11808 : smallValid 11808 33 := by unfold smallValid; decide +kernel

private theorem sp11841 : smallValid 11841 34 := by unfold smallValid; decide +kernel

private theorem sp11875 : smallValid 11875 33 := by unfold smallValid; decide +kernel

private theorem sp11908 : smallValid 11908 34 := by unfold smallValid; decide +kernel

private theorem sp11942 : smallValid 11942 33 := by unfold smallValid; decide +kernel

private theorem sp11975 : smallValid 11975 34 := by unfold smallValid; decide +kernel

private theorem sp12009 : smallValid 12009 33 := by unfold smallValid; decide +kernel

private theorem sp12042 : smallValid 12042 34 := by unfold smallValid; decide +kernel

private theorem sp12076 : smallValid 12076 33 := by unfold smallValid; decide +kernel

private theorem sp12109 : smallValid 12109 34 := by unfold smallValid; decide +kernel

private theorem sp12143 : smallValid 12143 33 := by unfold smallValid; decide +kernel

private theorem sp12176 : smallValid 12176 34 := by unfold smallValid; decide +kernel

private theorem sp12210 : smallValid 12210 33 := by unfold smallValid; decide +kernel

private theorem sp12243 : smallValid 12243 34 := by unfold smallValid; decide +kernel

private theorem sp12277 : smallValid 12277 34 := by unfold smallValid; decide +kernel

private theorem sp12311 : smallValid 12311 34 := by unfold smallValid; decide +kernel

private theorem sp12345 : smallValid 12345 33 := by unfold smallValid; decide +kernel

private theorem sp12378 : smallValid 12378 34 := by unfold smallValid; decide +kernel

private theorem sp12412 : smallValid 12412 33 := by unfold smallValid; decide +kernel

private theorem sp12445 : smallValid 12445 34 := by unfold smallValid; decide +kernel

private theorem sp12479 : smallValid 12479 33 := by unfold smallValid; decide +kernel

private theorem sp12512 : smallValid 12512 34 := by unfold smallValid; decide +kernel

private theorem sp12546 : smallValid 12546 33 := by unfold smallValid; decide +kernel

private theorem sp12579 : smallValid 12579 34 := by unfold smallValid; decide +kernel

private theorem sp12613 : smallValid 12613 33 := by unfold smallValid; decide +kernel

private theorem sp12646 : smallValid 12646 34 := by unfold smallValid; decide +kernel

private theorem sp12680 : smallValid 12680 33 := by unfold smallValid; decide +kernel

private theorem sp12713 : smallValid 12713 34 := by unfold smallValid; decide +kernel

private theorem sp12747 : smallValid 12747 33 := by unfold smallValid; decide +kernel

private theorem sp12780 : smallValid 12780 34 := by unfold smallValid; decide +kernel

private theorem sp12814 : smallValid 12814 34 := by unfold smallValid; decide +kernel

private theorem sp12848 : smallValid 12848 34 := by unfold smallValid; decide +kernel

private theorem sp12882 : smallValid 12882 33 := by unfold smallValid; decide +kernel

private theorem sp12915 : smallValid 12915 34 := by unfold smallValid; decide +kernel

private theorem sp12949 : smallValid 12949 33 := by unfold smallValid; decide +kernel

private theorem sp12982 : smallValid 12982 34 := by unfold smallValid; decide +kernel

private theorem sp13016 : smallValid 13016 33 := by unfold smallValid; decide +kernel

private theorem sp13049 : smallValid 13049 34 := by unfold smallValid; decide +kernel

private theorem sp13083 : smallValid 13083 33 := by unfold smallValid; decide +kernel

private theorem sp13116 : smallValid 13116 34 := by unfold smallValid; decide +kernel

private theorem sp13150 : smallValid 13150 33 := by unfold smallValid; decide +kernel

private theorem sp13183 : smallValid 13183 34 := by unfold smallValid; decide +kernel

private theorem sp13217 : smallValid 13217 33 := by unfold smallValid; decide +kernel

private theorem sp13250 : smallValid 13250 34 := by unfold smallValid; decide +kernel

private theorem sp13284 : smallValid 13284 33 := by unfold smallValid; decide +kernel

private theorem sp13317 : smallValid 13317 34 := by unfold smallValid; decide +kernel

private theorem sp13351 : smallValid 13351 33 := by unfold smallValid; decide +kernel

private theorem sp13384 : smallValid 13384 34 := by unfold smallValid; decide +kernel

private theorem sp13418 : smallValid 13418 33 := by unfold smallValid; decide +kernel

private theorem sp13451 : smallValid 13451 34 := by unfold smallValid; decide +kernel

private theorem sp13485 : smallValid 13485 33 := by unfold smallValid; decide +kernel

private theorem sp13518 : smallValid 13518 34 := by unfold smallValid; decide +kernel

private theorem sp13552 : smallValid 13552 33 := by unfold smallValid; decide +kernel

private theorem sp13585 : smallValid 13585 34 := by unfold smallValid; decide +kernel

private theorem sp13619 : smallValid 13619 33 := by unfold smallValid; decide +kernel

private theorem sp13652 : smallValid 13652 34 := by unfold smallValid; decide +kernel

private theorem sp13686 : smallValid 13686 33 := by unfold smallValid; decide +kernel

private theorem sp13719 : smallValid 13719 34 := by unfold smallValid; decide +kernel

private theorem sp13753 : smallValid 13753 33 := by unfold smallValid; decide +kernel

private theorem sp13786 : smallValid 13786 34 := by unfold smallValid; decide +kernel

private theorem sp13820 : smallValid 13820 33 := by unfold smallValid; decide +kernel

private theorem sp13853 : smallValid 13853 34 := by unfold smallValid; decide +kernel

private theorem sp13887 : smallValid 13887 34 := by unfold smallValid; decide +kernel

private theorem sp13921 : smallValid 13921 34 := by unfold smallValid; decide +kernel

private theorem sp13955 : smallValid 13955 33 := by unfold smallValid; decide +kernel

private theorem sp13988 : smallValid 13988 34 := by unfold smallValid; decide +kernel

private theorem sp14022 : smallValid 14022 33 := by unfold smallValid; decide +kernel

private theorem sp14055 : smallValid 14055 34 := by unfold smallValid; decide +kernel

private theorem sp14089 : smallValid 14089 33 := by unfold smallValid; decide +kernel

private theorem sp14122 : smallValid 14122 34 := by unfold smallValid; decide +kernel

private theorem sp14156 : smallValid 14156 33 := by unfold smallValid; decide +kernel

private theorem sp14189 : smallValid 14189 34 := by unfold smallValid; decide +kernel

private theorem sp14223 : smallValid 14223 33 := by unfold smallValid; decide +kernel

private theorem sp14256 : smallValid 14256 34 := by unfold smallValid; decide +kernel

private theorem sp14290 : smallValid 14290 33 := by unfold smallValid; decide +kernel

private theorem sp14323 : smallValid 14323 34 := by unfold smallValid; decide +kernel

private theorem sp14357 : smallValid 14357 33 := by unfold smallValid; decide +kernel

private theorem sp14390 : smallValid 14390 34 := by unfold smallValid; decide +kernel

private theorem sp14424 : smallValid 14424 34 := by unfold smallValid; decide +kernel

private theorem sp14458 : smallValid 14458 34 := by unfold smallValid; decide +kernel

private theorem sp14492 : smallValid 14492 33 := by unfold smallValid; decide +kernel

private theorem sp14525 : smallValid 14525 34 := by unfold smallValid; decide +kernel

private theorem sp14559 : smallValid 14559 33 := by unfold smallValid; decide +kernel

private theorem sp14592 : smallValid 14592 34 := by unfold smallValid; decide +kernel

private theorem sp14626 : smallValid 14626 33 := by unfold smallValid; decide +kernel

private theorem sp14659 : smallValid 14659 34 := by unfold smallValid; decide +kernel

private theorem sp14693 : smallValid 14693 33 := by unfold smallValid; decide +kernel

private theorem sp14726 : smallValid 14726 34 := by unfold smallValid; decide +kernel

private theorem sp14760 : smallValid 14760 33 := by unfold smallValid; decide +kernel

private theorem sp14793 : smallValid 14793 34 := by unfold smallValid; decide +kernel

private theorem sp14827 : smallValid 14827 33 := by unfold smallValid; decide +kernel

private theorem sp14860 : smallValid 14860 34 := by unfold smallValid; decide +kernel

private theorem sp14894 : smallValid 14894 33 := by unfold smallValid; decide +kernel

private theorem sp14927 : smallValid 14927 34 := by unfold smallValid; decide +kernel

private theorem sp14961 : smallValid 14961 34 := by unfold smallValid; decide +kernel

private theorem sp14995 : smallValid 14995 34 := by unfold smallValid; decide +kernel

private theorem sp15029 : smallValid 15029 33 := by unfold smallValid; decide +kernel

private theorem sp15062 : smallValid 15062 34 := by unfold smallValid; decide +kernel

private theorem sp15096 : smallValid 15096 33 := by unfold smallValid; decide +kernel

private theorem sp15129 : smallValid 15129 34 := by unfold smallValid; decide +kernel

private theorem sp15163 : smallValid 15163 33 := by unfold smallValid; decide +kernel

private theorem sp15196 : smallValid 15196 34 := by unfold smallValid; decide +kernel

private theorem sp15230 : smallValid 15230 33 := by unfold smallValid; decide +kernel

private theorem sp15263 : smallValid 15263 34 := by unfold smallValid; decide +kernel

private theorem sp15297 : smallValid 15297 33 := by unfold smallValid; decide +kernel

private theorem sp15330 : smallValid 15330 34 := by unfold smallValid; decide +kernel

private theorem sp15364 : smallValid 15364 33 := by unfold smallValid; decide +kernel

private theorem sp15397 : smallValid 15397 34 := by unfold smallValid; decide +kernel

private theorem sp15431 : smallValid 15431 33 := by unfold smallValid; decide +kernel

private theorem sp15464 : smallValid 15464 34 := by unfold smallValid; decide +kernel

private theorem sp15498 : smallValid 15498 33 := by unfold smallValid; decide +kernel

private theorem sp15531 : smallValid 15531 34 := by unfold smallValid; decide +kernel

private theorem sp15565 : smallValid 15565 33 := by unfold smallValid; decide +kernel

private theorem sp15598 : smallValid 15598 34 := by unfold smallValid; decide +kernel

private theorem sp15632 : smallValid 15632 33 := by unfold smallValid; decide +kernel

private theorem sp15665 : smallValid 15665 34 := by unfold smallValid; decide +kernel

private theorem sp15699 : smallValid 15699 33 := by unfold smallValid; decide +kernel

private theorem sp15732 : smallValid 15732 34 := by unfold smallValid; decide +kernel

private theorem sp15766 : smallValid 15766 33 := by unfold smallValid; decide +kernel

private theorem sp15799 : smallValid 15799 34 := by unfold smallValid; decide +kernel

private theorem sp15833 : smallValid 15833 33 := by unfold smallValid; decide +kernel

private theorem sp15866 : smallValid 15866 34 := by unfold smallValid; decide +kernel

private theorem sp15900 : smallValid 15900 33 := by unfold smallValid; decide +kernel

private theorem sp15933 : smallValid 15933 34 := by unfold smallValid; decide +kernel

private theorem sp15967 : smallValid 15967 33 := by unfold smallValid; decide +kernel

private theorem sp16000 : smallValid 16000 34 := by unfold smallValid; decide +kernel

private theorem sp16034 : smallValid 16034 34 := by unfold smallValid; decide +kernel

private theorem sp16068 : smallValid 16068 34 := by unfold smallValid; decide +kernel

private theorem sp16102 : smallValid 16102 33 := by unfold smallValid; decide +kernel

private theorem sp16135 : smallValid 16135 34 := by unfold smallValid; decide +kernel

private theorem sp16169 : smallValid 16169 33 := by unfold smallValid; decide +kernel

private theorem sp16202 : smallValid 16202 34 := by unfold smallValid; decide +kernel

private theorem sp16236 : smallValid 16236 33 := by unfold smallValid; decide +kernel

private theorem sp16269 : smallValid 16269 34 := by unfold smallValid; decide +kernel

private theorem sp16303 : smallValid 16303 33 := by unfold smallValid; decide +kernel

private theorem sp16336 : smallValid 16336 34 := by unfold smallValid; decide +kernel

private theorem sp16370 : smallValid 16370 33 := by unfold smallValid; decide +kernel

private theorem sp16403 : smallValid 16403 34 := by unfold smallValid; decide +kernel

private theorem sp16437 : smallValid 16437 33 := by unfold smallValid; decide +kernel

private theorem sp16470 : smallValid 16470 34 := by unfold smallValid; decide +kernel

private theorem sp16504 : smallValid 16504 33 := by unfold smallValid; decide +kernel

private theorem sp16537 : smallValid 16537 34 := by unfold smallValid; decide +kernel

private theorem sp16571 : smallValid 16571 34 := by unfold smallValid; decide +kernel

private theorem sp16605 : smallValid 16605 34 := by unfold smallValid; decide +kernel

private theorem sp16639 : smallValid 16639 33 := by unfold smallValid; decide +kernel

private theorem sp16672 : smallValid 16672 34 := by unfold smallValid; decide +kernel

private theorem sp16706 : smallValid 16706 33 := by unfold smallValid; decide +kernel

private theorem sp16739 : smallValid 16739 34 := by unfold smallValid; decide +kernel

private theorem sp16773 : smallValid 16773 33 := by unfold smallValid; decide +kernel

private theorem sp16806 : smallValid 16806 34 := by unfold smallValid; decide +kernel

private theorem sp16840 : smallValid 16840 33 := by unfold smallValid; decide +kernel

private theorem sp16873 : smallValid 16873 34 := by unfold smallValid; decide +kernel

private theorem sp16907 : smallValid 16907 33 := by unfold smallValid; decide +kernel

private theorem sp16940 : smallValid 16940 34 := by unfold smallValid; decide +kernel

private theorem sp16974 : smallValid 16974 33 := by unfold smallValid; decide +kernel

private theorem sp17007 : smallValid 17007 34 := by unfold smallValid; decide +kernel

private theorem sp17041 : smallValid 17041 33 := by unfold smallValid; decide +kernel

private theorem sp17074 : smallValid 17074 34 := by unfold smallValid; decide +kernel

private theorem sp17108 : smallValid 17108 34 := by unfold smallValid; decide +kernel

private theorem sp17142 : smallValid 17142 34 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤17175) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 17176 := (joinSmall (lo:=0) (a:=8588) (b:=8588) (joinSmall (lo:=0) (a:=4294) (b:=4294) (joinSmall (lo:=0) (a:=2147) (b:=2147) (joinSmall (lo:=0) (a:=1073) (b:=1074) (joinSmall (lo:=0) (a:=536) (b:=537) (joinSmall (lo:=0) (a:=268) (b:=268) (joinSmall (lo:=0) (a:=134) (b:=134) (joinSmall (lo:=0) (a:=67) (b:=67) (joinSmall (lo:=0) (a:=33) (b:=34) sp0 sp33) (joinSmall (lo:=67) (a:=33) (b:=34) sp67 sp100)) (joinSmall (lo:=134) (a:=67) (b:=67) (joinSmall (lo:=134) (a:=33) (b:=34) sp134 sp167) (joinSmall (lo:=201) (a:=33) (b:=34) sp201 sp234))) (joinSmall (lo:=268) (a:=134) (b:=134) (joinSmall (lo:=268) (a:=67) (b:=67) (joinSmall (lo:=268) (a:=33) (b:=34) sp268 sp301) (joinSmall (lo:=335) (a:=33) (b:=34) sp335 sp368)) (joinSmall (lo:=402) (a:=67) (b:=67) (joinSmall (lo:=402) (a:=33) (b:=34) sp402 sp435) (joinSmall (lo:=469) (a:=33) (b:=34) sp469 sp502)))) (joinSmall (lo:=536) (a:=268) (b:=269) (joinSmall (lo:=536) (a:=134) (b:=134) (joinSmall (lo:=536) (a:=67) (b:=67) (joinSmall (lo:=536) (a:=33) (b:=34) sp536 sp569) (joinSmall (lo:=603) (a:=33) (b:=34) sp603 sp636)) (joinSmall (lo:=670) (a:=67) (b:=67) (joinSmall (lo:=670) (a:=33) (b:=34) sp670 sp703) (joinSmall (lo:=737) (a:=33) (b:=34) sp737 sp770))) (joinSmall (lo:=804) (a:=134) (b:=135) (joinSmall (lo:=804) (a:=67) (b:=67) (joinSmall (lo:=804) (a:=33) (b:=34) sp804 sp837) (joinSmall (lo:=871) (a:=33) (b:=34) sp871 sp904)) (joinSmall (lo:=938) (a:=67) (b:=68) (joinSmall (lo:=938) (a:=33) (b:=34) sp938 sp971) (joinSmall (lo:=1005) (a:=34) (b:=34) sp1005 sp1039))))) (joinSmall (lo:=1073) (a:=537) (b:=537) (joinSmall (lo:=1073) (a:=268) (b:=269) (joinSmall (lo:=1073) (a:=134) (b:=134) (joinSmall (lo:=1073) (a:=67) (b:=67) (joinSmall (lo:=1073) (a:=33) (b:=34) sp1073 sp1106) (joinSmall (lo:=1140) (a:=33) (b:=34) sp1140 sp1173)) (joinSmall (lo:=1207) (a:=67) (b:=67) (joinSmall (lo:=1207) (a:=33) (b:=34) sp1207 sp1240) (joinSmall (lo:=1274) (a:=33) (b:=34) sp1274 sp1307))) (joinSmall (lo:=1341) (a:=134) (b:=135) (joinSmall (lo:=1341) (a:=67) (b:=67) (joinSmall (lo:=1341) (a:=33) (b:=34) sp1341 sp1374) (joinSmall (lo:=1408) (a:=33) (b:=34) sp1408 sp1441)) (joinSmall (lo:=1475) (a:=67) (b:=68) (joinSmall (lo:=1475) (a:=33) (b:=34) sp1475 sp1508) (joinSmall (lo:=1542) (a:=34) (b:=34) sp1542 sp1576)))) (joinSmall (lo:=1610) (a:=268) (b:=269) (joinSmall (lo:=1610) (a:=134) (b:=134) (joinSmall (lo:=1610) (a:=67) (b:=67) (joinSmall (lo:=1610) (a:=33) (b:=34) sp1610 sp1643) (joinSmall (lo:=1677) (a:=33) (b:=34) sp1677 sp1710)) (joinSmall (lo:=1744) (a:=67) (b:=67) (joinSmall (lo:=1744) (a:=33) (b:=34) sp1744 sp1777) (joinSmall (lo:=1811) (a:=33) (b:=34) sp1811 sp1844))) (joinSmall (lo:=1878) (a:=134) (b:=135) (joinSmall (lo:=1878) (a:=67) (b:=67) (joinSmall (lo:=1878) (a:=33) (b:=34) sp1878 sp1911) (joinSmall (lo:=1945) (a:=33) (b:=34) sp1945 sp1978)) (joinSmall (lo:=2012) (a:=67) (b:=68) (joinSmall (lo:=2012) (a:=33) (b:=34) sp2012 sp2045) (joinSmall (lo:=2079) (a:=34) (b:=34) sp2079 sp2113)))))) (joinSmall (lo:=2147) (a:=1073) (b:=1074) (joinSmall (lo:=2147) (a:=536) (b:=537) (joinSmall (lo:=2147) (a:=268) (b:=268) (joinSmall (lo:=2147) (a:=134) (b:=134) (joinSmall (lo:=2147) (a:=67) (b:=67) (joinSmall (lo:=2147) (a:=33) (b:=34) sp2147 sp2180) (joinSmall (lo:=2214) (a:=33) (b:=34) sp2214 sp2247)) (joinSmall (lo:=2281) (a:=67) (b:=67) (joinSmall (lo:=2281) (a:=33) (b:=34) sp2281 sp2314) (joinSmall (lo:=2348) (a:=33) (b:=34) sp2348 sp2381))) (joinSmall (lo:=2415) (a:=134) (b:=134) (joinSmall (lo:=2415) (a:=67) (b:=67) (joinSmall (lo:=2415) (a:=33) (b:=34) sp2415 sp2448) (joinSmall (lo:=2482) (a:=33) (b:=34) sp2482 sp2515)) (joinSmall (lo:=2549) (a:=67) (b:=67) (joinSmall (lo:=2549) (a:=33) (b:=34) sp2549 sp2582) (joinSmall (lo:=2616) (a:=33) (b:=34) sp2616 sp2649)))) (joinSmall (lo:=2683) (a:=268) (b:=269) (joinSmall (lo:=2683) (a:=134) (b:=134) (joinSmall (lo:=2683) (a:=67) (b:=67) (joinSmall (lo:=2683) (a:=33) (b:=34) sp2683 sp2716) (joinSmall (lo:=2750) (a:=33) (b:=34) sp2750 sp2783)) (joinSmall (lo:=2817) (a:=67) (b:=67) (joinSmall (lo:=2817) (a:=33) (b:=34) sp2817 sp2850) (joinSmall (lo:=2884) (a:=33) (b:=34) sp2884 sp2917))) (joinSmall (lo:=2951) (a:=134) (b:=135) (joinSmall (lo:=2951) (a:=67) (b:=67) (joinSmall (lo:=2951) (a:=33) (b:=34) sp2951 sp2984) (joinSmall (lo:=3018) (a:=33) (b:=34) sp3018 sp3051)) (joinSmall (lo:=3085) (a:=67) (b:=68) (joinSmall (lo:=3085) (a:=33) (b:=34) sp3085 sp3118) (joinSmall (lo:=3152) (a:=34) (b:=34) sp3152 sp3186))))) (joinSmall (lo:=3220) (a:=537) (b:=537) (joinSmall (lo:=3220) (a:=268) (b:=269) (joinSmall (lo:=3220) (a:=134) (b:=134) (joinSmall (lo:=3220) (a:=67) (b:=67) (joinSmall (lo:=3220) (a:=33) (b:=34) sp3220 sp3253) (joinSmall (lo:=3287) (a:=33) (b:=34) sp3287 sp3320)) (joinSmall (lo:=3354) (a:=67) (b:=67) (joinSmall (lo:=3354) (a:=33) (b:=34) sp3354 sp3387) (joinSmall (lo:=3421) (a:=33) (b:=34) sp3421 sp3454))) (joinSmall (lo:=3488) (a:=134) (b:=135) (joinSmall (lo:=3488) (a:=67) (b:=67) (joinSmall (lo:=3488) (a:=33) (b:=34) sp3488 sp3521) (joinSmall (lo:=3555) (a:=33) (b:=34) sp3555 sp3588)) (joinSmall (lo:=3622) (a:=67) (b:=68) (joinSmall (lo:=3622) (a:=33) (b:=34) sp3622 sp3655) (joinSmall (lo:=3689) (a:=34) (b:=34) sp3689 sp3723)))) (joinSmall (lo:=3757) (a:=268) (b:=269) (joinSmall (lo:=3757) (a:=134) (b:=134) (joinSmall (lo:=3757) (a:=67) (b:=67) (joinSmall (lo:=3757) (a:=33) (b:=34) sp3757 sp3790) (joinSmall (lo:=3824) (a:=33) (b:=34) sp3824 sp3857)) (joinSmall (lo:=3891) (a:=67) (b:=67) (joinSmall (lo:=3891) (a:=33) (b:=34) sp3891 sp3924) (joinSmall (lo:=3958) (a:=33) (b:=34) sp3958 sp3991))) (joinSmall (lo:=4025) (a:=134) (b:=135) (joinSmall (lo:=4025) (a:=67) (b:=67) (joinSmall (lo:=4025) (a:=33) (b:=34) sp4025 sp4058) (joinSmall (lo:=4092) (a:=33) (b:=34) sp4092 sp4125)) (joinSmall (lo:=4159) (a:=67) (b:=68) (joinSmall (lo:=4159) (a:=33) (b:=34) sp4159 sp4192) (joinSmall (lo:=4226) (a:=34) (b:=34) sp4226 sp4260))))))) (joinSmall (lo:=4294) (a:=2147) (b:=2147) (joinSmall (lo:=4294) (a:=1073) (b:=1074) (joinSmall (lo:=4294) (a:=536) (b:=537) (joinSmall (lo:=4294) (a:=268) (b:=268) (joinSmall (lo:=4294) (a:=134) (b:=134) (joinSmall (lo:=4294) (a:=67) (b:=67) (joinSmall (lo:=4294) (a:=33) (b:=34) sp4294 sp4327) (joinSmall (lo:=4361) (a:=33) (b:=34) sp4361 sp4394)) (joinSmall (lo:=4428) (a:=67) (b:=67) (joinSmall (lo:=4428) (a:=33) (b:=34) sp4428 sp4461) (joinSmall (lo:=4495) (a:=33) (b:=34) sp4495 sp4528))) (joinSmall (lo:=4562) (a:=134) (b:=134) (joinSmall (lo:=4562) (a:=67) (b:=67) (joinSmall (lo:=4562) (a:=33) (b:=34) sp4562 sp4595) (joinSmall (lo:=4629) (a:=33) (b:=34) sp4629 sp4662)) (joinSmall (lo:=4696) (a:=67) (b:=67) (joinSmall (lo:=4696) (a:=33) (b:=34) sp4696 sp4729) (joinSmall (lo:=4763) (a:=33) (b:=34) sp4763 sp4796)))) (joinSmall (lo:=4830) (a:=268) (b:=269) (joinSmall (lo:=4830) (a:=134) (b:=134) (joinSmall (lo:=4830) (a:=67) (b:=67) (joinSmall (lo:=4830) (a:=33) (b:=34) sp4830 sp4863) (joinSmall (lo:=4897) (a:=33) (b:=34) sp4897 sp4930)) (joinSmall (lo:=4964) (a:=67) (b:=67) (joinSmall (lo:=4964) (a:=33) (b:=34) sp4964 sp4997) (joinSmall (lo:=5031) (a:=33) (b:=34) sp5031 sp5064))) (joinSmall (lo:=5098) (a:=134) (b:=135) (joinSmall (lo:=5098) (a:=67) (b:=67) (joinSmall (lo:=5098) (a:=33) (b:=34) sp5098 sp5131) (joinSmall (lo:=5165) (a:=33) (b:=34) sp5165 sp5198)) (joinSmall (lo:=5232) (a:=67) (b:=68) (joinSmall (lo:=5232) (a:=33) (b:=34) sp5232 sp5265) (joinSmall (lo:=5299) (a:=34) (b:=34) sp5299 sp5333))))) (joinSmall (lo:=5367) (a:=537) (b:=537) (joinSmall (lo:=5367) (a:=268) (b:=269) (joinSmall (lo:=5367) (a:=134) (b:=134) (joinSmall (lo:=5367) (a:=67) (b:=67) (joinSmall (lo:=5367) (a:=33) (b:=34) sp5367 sp5400) (joinSmall (lo:=5434) (a:=33) (b:=34) sp5434 sp5467)) (joinSmall (lo:=5501) (a:=67) (b:=67) (joinSmall (lo:=5501) (a:=33) (b:=34) sp5501 sp5534) (joinSmall (lo:=5568) (a:=33) (b:=34) sp5568 sp5601))) (joinSmall (lo:=5635) (a:=134) (b:=135) (joinSmall (lo:=5635) (a:=67) (b:=67) (joinSmall (lo:=5635) (a:=33) (b:=34) sp5635 sp5668) (joinSmall (lo:=5702) (a:=33) (b:=34) sp5702 sp5735)) (joinSmall (lo:=5769) (a:=67) (b:=68) (joinSmall (lo:=5769) (a:=33) (b:=34) sp5769 sp5802) (joinSmall (lo:=5836) (a:=34) (b:=34) sp5836 sp5870)))) (joinSmall (lo:=5904) (a:=268) (b:=269) (joinSmall (lo:=5904) (a:=134) (b:=134) (joinSmall (lo:=5904) (a:=67) (b:=67) (joinSmall (lo:=5904) (a:=33) (b:=34) sp5904 sp5937) (joinSmall (lo:=5971) (a:=33) (b:=34) sp5971 sp6004)) (joinSmall (lo:=6038) (a:=67) (b:=67) (joinSmall (lo:=6038) (a:=33) (b:=34) sp6038 sp6071) (joinSmall (lo:=6105) (a:=33) (b:=34) sp6105 sp6138))) (joinSmall (lo:=6172) (a:=134) (b:=135) (joinSmall (lo:=6172) (a:=67) (b:=67) (joinSmall (lo:=6172) (a:=33) (b:=34) sp6172 sp6205) (joinSmall (lo:=6239) (a:=33) (b:=34) sp6239 sp6272)) (joinSmall (lo:=6306) (a:=67) (b:=68) (joinSmall (lo:=6306) (a:=33) (b:=34) sp6306 sp6339) (joinSmall (lo:=6373) (a:=34) (b:=34) sp6373 sp6407)))))) (joinSmall (lo:=6441) (a:=1073) (b:=1074) (joinSmall (lo:=6441) (a:=536) (b:=537) (joinSmall (lo:=6441) (a:=268) (b:=268) (joinSmall (lo:=6441) (a:=134) (b:=134) (joinSmall (lo:=6441) (a:=67) (b:=67) (joinSmall (lo:=6441) (a:=33) (b:=34) sp6441 sp6474) (joinSmall (lo:=6508) (a:=33) (b:=34) sp6508 sp6541)) (joinSmall (lo:=6575) (a:=67) (b:=67) (joinSmall (lo:=6575) (a:=33) (b:=34) sp6575 sp6608) (joinSmall (lo:=6642) (a:=33) (b:=34) sp6642 sp6675))) (joinSmall (lo:=6709) (a:=134) (b:=134) (joinSmall (lo:=6709) (a:=67) (b:=67) (joinSmall (lo:=6709) (a:=33) (b:=34) sp6709 sp6742) (joinSmall (lo:=6776) (a:=33) (b:=34) sp6776 sp6809)) (joinSmall (lo:=6843) (a:=67) (b:=67) (joinSmall (lo:=6843) (a:=33) (b:=34) sp6843 sp6876) (joinSmall (lo:=6910) (a:=33) (b:=34) sp6910 sp6943)))) (joinSmall (lo:=6977) (a:=268) (b:=269) (joinSmall (lo:=6977) (a:=134) (b:=134) (joinSmall (lo:=6977) (a:=67) (b:=67) (joinSmall (lo:=6977) (a:=33) (b:=34) sp6977 sp7010) (joinSmall (lo:=7044) (a:=33) (b:=34) sp7044 sp7077)) (joinSmall (lo:=7111) (a:=67) (b:=67) (joinSmall (lo:=7111) (a:=33) (b:=34) sp7111 sp7144) (joinSmall (lo:=7178) (a:=33) (b:=34) sp7178 sp7211))) (joinSmall (lo:=7245) (a:=134) (b:=135) (joinSmall (lo:=7245) (a:=67) (b:=67) (joinSmall (lo:=7245) (a:=33) (b:=34) sp7245 sp7278) (joinSmall (lo:=7312) (a:=33) (b:=34) sp7312 sp7345)) (joinSmall (lo:=7379) (a:=67) (b:=68) (joinSmall (lo:=7379) (a:=33) (b:=34) sp7379 sp7412) (joinSmall (lo:=7446) (a:=34) (b:=34) sp7446 sp7480))))) (joinSmall (lo:=7514) (a:=537) (b:=537) (joinSmall (lo:=7514) (a:=268) (b:=269) (joinSmall (lo:=7514) (a:=134) (b:=134) (joinSmall (lo:=7514) (a:=67) (b:=67) (joinSmall (lo:=7514) (a:=33) (b:=34) sp7514 sp7547) (joinSmall (lo:=7581) (a:=33) (b:=34) sp7581 sp7614)) (joinSmall (lo:=7648) (a:=67) (b:=67) (joinSmall (lo:=7648) (a:=33) (b:=34) sp7648 sp7681) (joinSmall (lo:=7715) (a:=33) (b:=34) sp7715 sp7748))) (joinSmall (lo:=7782) (a:=134) (b:=135) (joinSmall (lo:=7782) (a:=67) (b:=67) (joinSmall (lo:=7782) (a:=33) (b:=34) sp7782 sp7815) (joinSmall (lo:=7849) (a:=33) (b:=34) sp7849 sp7882)) (joinSmall (lo:=7916) (a:=67) (b:=68) (joinSmall (lo:=7916) (a:=33) (b:=34) sp7916 sp7949) (joinSmall (lo:=7983) (a:=34) (b:=34) sp7983 sp8017)))) (joinSmall (lo:=8051) (a:=268) (b:=269) (joinSmall (lo:=8051) (a:=134) (b:=134) (joinSmall (lo:=8051) (a:=67) (b:=67) (joinSmall (lo:=8051) (a:=33) (b:=34) sp8051 sp8084) (joinSmall (lo:=8118) (a:=33) (b:=34) sp8118 sp8151)) (joinSmall (lo:=8185) (a:=67) (b:=67) (joinSmall (lo:=8185) (a:=33) (b:=34) sp8185 sp8218) (joinSmall (lo:=8252) (a:=33) (b:=34) sp8252 sp8285))) (joinSmall (lo:=8319) (a:=134) (b:=135) (joinSmall (lo:=8319) (a:=67) (b:=67) (joinSmall (lo:=8319) (a:=33) (b:=34) sp8319 sp8352) (joinSmall (lo:=8386) (a:=33) (b:=34) sp8386 sp8419)) (joinSmall (lo:=8453) (a:=67) (b:=68) (joinSmall (lo:=8453) (a:=33) (b:=34) sp8453 sp8486) (joinSmall (lo:=8520) (a:=34) (b:=34) sp8520 sp8554)))))))) (joinSmall (lo:=8588) (a:=4294) (b:=4294) (joinSmall (lo:=8588) (a:=2147) (b:=2147) (joinSmall (lo:=8588) (a:=1073) (b:=1074) (joinSmall (lo:=8588) (a:=536) (b:=537) (joinSmall (lo:=8588) (a:=268) (b:=268) (joinSmall (lo:=8588) (a:=134) (b:=134) (joinSmall (lo:=8588) (a:=67) (b:=67) (joinSmall (lo:=8588) (a:=33) (b:=34) sp8588 sp8621) (joinSmall (lo:=8655) (a:=33) (b:=34) sp8655 sp8688)) (joinSmall (lo:=8722) (a:=67) (b:=67) (joinSmall (lo:=8722) (a:=33) (b:=34) sp8722 sp8755) (joinSmall (lo:=8789) (a:=33) (b:=34) sp8789 sp8822))) (joinSmall (lo:=8856) (a:=134) (b:=134) (joinSmall (lo:=8856) (a:=67) (b:=67) (joinSmall (lo:=8856) (a:=33) (b:=34) sp8856 sp8889) (joinSmall (lo:=8923) (a:=33) (b:=34) sp8923 sp8956)) (joinSmall (lo:=8990) (a:=67) (b:=67) (joinSmall (lo:=8990) (a:=33) (b:=34) sp8990 sp9023) (joinSmall (lo:=9057) (a:=33) (b:=34) sp9057 sp9090)))) (joinSmall (lo:=9124) (a:=268) (b:=269) (joinSmall (lo:=9124) (a:=134) (b:=134) (joinSmall (lo:=9124) (a:=67) (b:=67) (joinSmall (lo:=9124) (a:=33) (b:=34) sp9124 sp9157) (joinSmall (lo:=9191) (a:=33) (b:=34) sp9191 sp9224)) (joinSmall (lo:=9258) (a:=67) (b:=67) (joinSmall (lo:=9258) (a:=33) (b:=34) sp9258 sp9291) (joinSmall (lo:=9325) (a:=33) (b:=34) sp9325 sp9358))) (joinSmall (lo:=9392) (a:=134) (b:=135) (joinSmall (lo:=9392) (a:=67) (b:=67) (joinSmall (lo:=9392) (a:=33) (b:=34) sp9392 sp9425) (joinSmall (lo:=9459) (a:=33) (b:=34) sp9459 sp9492)) (joinSmall (lo:=9526) (a:=67) (b:=68) (joinSmall (lo:=9526) (a:=33) (b:=34) sp9526 sp9559) (joinSmall (lo:=9593) (a:=34) (b:=34) sp9593 sp9627))))) (joinSmall (lo:=9661) (a:=537) (b:=537) (joinSmall (lo:=9661) (a:=268) (b:=269) (joinSmall (lo:=9661) (a:=134) (b:=134) (joinSmall (lo:=9661) (a:=67) (b:=67) (joinSmall (lo:=9661) (a:=33) (b:=34) sp9661 sp9694) (joinSmall (lo:=9728) (a:=33) (b:=34) sp9728 sp9761)) (joinSmall (lo:=9795) (a:=67) (b:=67) (joinSmall (lo:=9795) (a:=33) (b:=34) sp9795 sp9828) (joinSmall (lo:=9862) (a:=33) (b:=34) sp9862 sp9895))) (joinSmall (lo:=9929) (a:=134) (b:=135) (joinSmall (lo:=9929) (a:=67) (b:=67) (joinSmall (lo:=9929) (a:=33) (b:=34) sp9929 sp9962) (joinSmall (lo:=9996) (a:=33) (b:=34) sp9996 sp10029)) (joinSmall (lo:=10063) (a:=67) (b:=68) (joinSmall (lo:=10063) (a:=33) (b:=34) sp10063 sp10096) (joinSmall (lo:=10130) (a:=34) (b:=34) sp10130 sp10164)))) (joinSmall (lo:=10198) (a:=268) (b:=269) (joinSmall (lo:=10198) (a:=134) (b:=134) (joinSmall (lo:=10198) (a:=67) (b:=67) (joinSmall (lo:=10198) (a:=33) (b:=34) sp10198 sp10231) (joinSmall (lo:=10265) (a:=33) (b:=34) sp10265 sp10298)) (joinSmall (lo:=10332) (a:=67) (b:=67) (joinSmall (lo:=10332) (a:=33) (b:=34) sp10332 sp10365) (joinSmall (lo:=10399) (a:=33) (b:=34) sp10399 sp10432))) (joinSmall (lo:=10466) (a:=134) (b:=135) (joinSmall (lo:=10466) (a:=67) (b:=67) (joinSmall (lo:=10466) (a:=33) (b:=34) sp10466 sp10499) (joinSmall (lo:=10533) (a:=33) (b:=34) sp10533 sp10566)) (joinSmall (lo:=10600) (a:=67) (b:=68) (joinSmall (lo:=10600) (a:=33) (b:=34) sp10600 sp10633) (joinSmall (lo:=10667) (a:=34) (b:=34) sp10667 sp10701)))))) (joinSmall (lo:=10735) (a:=1073) (b:=1074) (joinSmall (lo:=10735) (a:=536) (b:=537) (joinSmall (lo:=10735) (a:=268) (b:=268) (joinSmall (lo:=10735) (a:=134) (b:=134) (joinSmall (lo:=10735) (a:=67) (b:=67) (joinSmall (lo:=10735) (a:=33) (b:=34) sp10735 sp10768) (joinSmall (lo:=10802) (a:=33) (b:=34) sp10802 sp10835)) (joinSmall (lo:=10869) (a:=67) (b:=67) (joinSmall (lo:=10869) (a:=33) (b:=34) sp10869 sp10902) (joinSmall (lo:=10936) (a:=33) (b:=34) sp10936 sp10969))) (joinSmall (lo:=11003) (a:=134) (b:=134) (joinSmall (lo:=11003) (a:=67) (b:=67) (joinSmall (lo:=11003) (a:=33) (b:=34) sp11003 sp11036) (joinSmall (lo:=11070) (a:=33) (b:=34) sp11070 sp11103)) (joinSmall (lo:=11137) (a:=67) (b:=67) (joinSmall (lo:=11137) (a:=33) (b:=34) sp11137 sp11170) (joinSmall (lo:=11204) (a:=33) (b:=34) sp11204 sp11237)))) (joinSmall (lo:=11271) (a:=268) (b:=269) (joinSmall (lo:=11271) (a:=134) (b:=134) (joinSmall (lo:=11271) (a:=67) (b:=67) (joinSmall (lo:=11271) (a:=33) (b:=34) sp11271 sp11304) (joinSmall (lo:=11338) (a:=33) (b:=34) sp11338 sp11371)) (joinSmall (lo:=11405) (a:=67) (b:=67) (joinSmall (lo:=11405) (a:=33) (b:=34) sp11405 sp11438) (joinSmall (lo:=11472) (a:=33) (b:=34) sp11472 sp11505))) (joinSmall (lo:=11539) (a:=134) (b:=135) (joinSmall (lo:=11539) (a:=67) (b:=67) (joinSmall (lo:=11539) (a:=33) (b:=34) sp11539 sp11572) (joinSmall (lo:=11606) (a:=33) (b:=34) sp11606 sp11639)) (joinSmall (lo:=11673) (a:=67) (b:=68) (joinSmall (lo:=11673) (a:=33) (b:=34) sp11673 sp11706) (joinSmall (lo:=11740) (a:=34) (b:=34) sp11740 sp11774))))) (joinSmall (lo:=11808) (a:=537) (b:=537) (joinSmall (lo:=11808) (a:=268) (b:=269) (joinSmall (lo:=11808) (a:=134) (b:=134) (joinSmall (lo:=11808) (a:=67) (b:=67) (joinSmall (lo:=11808) (a:=33) (b:=34) sp11808 sp11841) (joinSmall (lo:=11875) (a:=33) (b:=34) sp11875 sp11908)) (joinSmall (lo:=11942) (a:=67) (b:=67) (joinSmall (lo:=11942) (a:=33) (b:=34) sp11942 sp11975) (joinSmall (lo:=12009) (a:=33) (b:=34) sp12009 sp12042))) (joinSmall (lo:=12076) (a:=134) (b:=135) (joinSmall (lo:=12076) (a:=67) (b:=67) (joinSmall (lo:=12076) (a:=33) (b:=34) sp12076 sp12109) (joinSmall (lo:=12143) (a:=33) (b:=34) sp12143 sp12176)) (joinSmall (lo:=12210) (a:=67) (b:=68) (joinSmall (lo:=12210) (a:=33) (b:=34) sp12210 sp12243) (joinSmall (lo:=12277) (a:=34) (b:=34) sp12277 sp12311)))) (joinSmall (lo:=12345) (a:=268) (b:=269) (joinSmall (lo:=12345) (a:=134) (b:=134) (joinSmall (lo:=12345) (a:=67) (b:=67) (joinSmall (lo:=12345) (a:=33) (b:=34) sp12345 sp12378) (joinSmall (lo:=12412) (a:=33) (b:=34) sp12412 sp12445)) (joinSmall (lo:=12479) (a:=67) (b:=67) (joinSmall (lo:=12479) (a:=33) (b:=34) sp12479 sp12512) (joinSmall (lo:=12546) (a:=33) (b:=34) sp12546 sp12579))) (joinSmall (lo:=12613) (a:=134) (b:=135) (joinSmall (lo:=12613) (a:=67) (b:=67) (joinSmall (lo:=12613) (a:=33) (b:=34) sp12613 sp12646) (joinSmall (lo:=12680) (a:=33) (b:=34) sp12680 sp12713)) (joinSmall (lo:=12747) (a:=67) (b:=68) (joinSmall (lo:=12747) (a:=33) (b:=34) sp12747 sp12780) (joinSmall (lo:=12814) (a:=34) (b:=34) sp12814 sp12848))))))) (joinSmall (lo:=12882) (a:=2147) (b:=2147) (joinSmall (lo:=12882) (a:=1073) (b:=1074) (joinSmall (lo:=12882) (a:=536) (b:=537) (joinSmall (lo:=12882) (a:=268) (b:=268) (joinSmall (lo:=12882) (a:=134) (b:=134) (joinSmall (lo:=12882) (a:=67) (b:=67) (joinSmall (lo:=12882) (a:=33) (b:=34) sp12882 sp12915) (joinSmall (lo:=12949) (a:=33) (b:=34) sp12949 sp12982)) (joinSmall (lo:=13016) (a:=67) (b:=67) (joinSmall (lo:=13016) (a:=33) (b:=34) sp13016 sp13049) (joinSmall (lo:=13083) (a:=33) (b:=34) sp13083 sp13116))) (joinSmall (lo:=13150) (a:=134) (b:=134) (joinSmall (lo:=13150) (a:=67) (b:=67) (joinSmall (lo:=13150) (a:=33) (b:=34) sp13150 sp13183) (joinSmall (lo:=13217) (a:=33) (b:=34) sp13217 sp13250)) (joinSmall (lo:=13284) (a:=67) (b:=67) (joinSmall (lo:=13284) (a:=33) (b:=34) sp13284 sp13317) (joinSmall (lo:=13351) (a:=33) (b:=34) sp13351 sp13384)))) (joinSmall (lo:=13418) (a:=268) (b:=269) (joinSmall (lo:=13418) (a:=134) (b:=134) (joinSmall (lo:=13418) (a:=67) (b:=67) (joinSmall (lo:=13418) (a:=33) (b:=34) sp13418 sp13451) (joinSmall (lo:=13485) (a:=33) (b:=34) sp13485 sp13518)) (joinSmall (lo:=13552) (a:=67) (b:=67) (joinSmall (lo:=13552) (a:=33) (b:=34) sp13552 sp13585) (joinSmall (lo:=13619) (a:=33) (b:=34) sp13619 sp13652))) (joinSmall (lo:=13686) (a:=134) (b:=135) (joinSmall (lo:=13686) (a:=67) (b:=67) (joinSmall (lo:=13686) (a:=33) (b:=34) sp13686 sp13719) (joinSmall (lo:=13753) (a:=33) (b:=34) sp13753 sp13786)) (joinSmall (lo:=13820) (a:=67) (b:=68) (joinSmall (lo:=13820) (a:=33) (b:=34) sp13820 sp13853) (joinSmall (lo:=13887) (a:=34) (b:=34) sp13887 sp13921))))) (joinSmall (lo:=13955) (a:=537) (b:=537) (joinSmall (lo:=13955) (a:=268) (b:=269) (joinSmall (lo:=13955) (a:=134) (b:=134) (joinSmall (lo:=13955) (a:=67) (b:=67) (joinSmall (lo:=13955) (a:=33) (b:=34) sp13955 sp13988) (joinSmall (lo:=14022) (a:=33) (b:=34) sp14022 sp14055)) (joinSmall (lo:=14089) (a:=67) (b:=67) (joinSmall (lo:=14089) (a:=33) (b:=34) sp14089 sp14122) (joinSmall (lo:=14156) (a:=33) (b:=34) sp14156 sp14189))) (joinSmall (lo:=14223) (a:=134) (b:=135) (joinSmall (lo:=14223) (a:=67) (b:=67) (joinSmall (lo:=14223) (a:=33) (b:=34) sp14223 sp14256) (joinSmall (lo:=14290) (a:=33) (b:=34) sp14290 sp14323)) (joinSmall (lo:=14357) (a:=67) (b:=68) (joinSmall (lo:=14357) (a:=33) (b:=34) sp14357 sp14390) (joinSmall (lo:=14424) (a:=34) (b:=34) sp14424 sp14458)))) (joinSmall (lo:=14492) (a:=268) (b:=269) (joinSmall (lo:=14492) (a:=134) (b:=134) (joinSmall (lo:=14492) (a:=67) (b:=67) (joinSmall (lo:=14492) (a:=33) (b:=34) sp14492 sp14525) (joinSmall (lo:=14559) (a:=33) (b:=34) sp14559 sp14592)) (joinSmall (lo:=14626) (a:=67) (b:=67) (joinSmall (lo:=14626) (a:=33) (b:=34) sp14626 sp14659) (joinSmall (lo:=14693) (a:=33) (b:=34) sp14693 sp14726))) (joinSmall (lo:=14760) (a:=134) (b:=135) (joinSmall (lo:=14760) (a:=67) (b:=67) (joinSmall (lo:=14760) (a:=33) (b:=34) sp14760 sp14793) (joinSmall (lo:=14827) (a:=33) (b:=34) sp14827 sp14860)) (joinSmall (lo:=14894) (a:=67) (b:=68) (joinSmall (lo:=14894) (a:=33) (b:=34) sp14894 sp14927) (joinSmall (lo:=14961) (a:=34) (b:=34) sp14961 sp14995)))))) (joinSmall (lo:=15029) (a:=1073) (b:=1074) (joinSmall (lo:=15029) (a:=536) (b:=537) (joinSmall (lo:=15029) (a:=268) (b:=268) (joinSmall (lo:=15029) (a:=134) (b:=134) (joinSmall (lo:=15029) (a:=67) (b:=67) (joinSmall (lo:=15029) (a:=33) (b:=34) sp15029 sp15062) (joinSmall (lo:=15096) (a:=33) (b:=34) sp15096 sp15129)) (joinSmall (lo:=15163) (a:=67) (b:=67) (joinSmall (lo:=15163) (a:=33) (b:=34) sp15163 sp15196) (joinSmall (lo:=15230) (a:=33) (b:=34) sp15230 sp15263))) (joinSmall (lo:=15297) (a:=134) (b:=134) (joinSmall (lo:=15297) (a:=67) (b:=67) (joinSmall (lo:=15297) (a:=33) (b:=34) sp15297 sp15330) (joinSmall (lo:=15364) (a:=33) (b:=34) sp15364 sp15397)) (joinSmall (lo:=15431) (a:=67) (b:=67) (joinSmall (lo:=15431) (a:=33) (b:=34) sp15431 sp15464) (joinSmall (lo:=15498) (a:=33) (b:=34) sp15498 sp15531)))) (joinSmall (lo:=15565) (a:=268) (b:=269) (joinSmall (lo:=15565) (a:=134) (b:=134) (joinSmall (lo:=15565) (a:=67) (b:=67) (joinSmall (lo:=15565) (a:=33) (b:=34) sp15565 sp15598) (joinSmall (lo:=15632) (a:=33) (b:=34) sp15632 sp15665)) (joinSmall (lo:=15699) (a:=67) (b:=67) (joinSmall (lo:=15699) (a:=33) (b:=34) sp15699 sp15732) (joinSmall (lo:=15766) (a:=33) (b:=34) sp15766 sp15799))) (joinSmall (lo:=15833) (a:=134) (b:=135) (joinSmall (lo:=15833) (a:=67) (b:=67) (joinSmall (lo:=15833) (a:=33) (b:=34) sp15833 sp15866) (joinSmall (lo:=15900) (a:=33) (b:=34) sp15900 sp15933)) (joinSmall (lo:=15967) (a:=67) (b:=68) (joinSmall (lo:=15967) (a:=33) (b:=34) sp15967 sp16000) (joinSmall (lo:=16034) (a:=34) (b:=34) sp16034 sp16068))))) (joinSmall (lo:=16102) (a:=537) (b:=537) (joinSmall (lo:=16102) (a:=268) (b:=269) (joinSmall (lo:=16102) (a:=134) (b:=134) (joinSmall (lo:=16102) (a:=67) (b:=67) (joinSmall (lo:=16102) (a:=33) (b:=34) sp16102 sp16135) (joinSmall (lo:=16169) (a:=33) (b:=34) sp16169 sp16202)) (joinSmall (lo:=16236) (a:=67) (b:=67) (joinSmall (lo:=16236) (a:=33) (b:=34) sp16236 sp16269) (joinSmall (lo:=16303) (a:=33) (b:=34) sp16303 sp16336))) (joinSmall (lo:=16370) (a:=134) (b:=135) (joinSmall (lo:=16370) (a:=67) (b:=67) (joinSmall (lo:=16370) (a:=33) (b:=34) sp16370 sp16403) (joinSmall (lo:=16437) (a:=33) (b:=34) sp16437 sp16470)) (joinSmall (lo:=16504) (a:=67) (b:=68) (joinSmall (lo:=16504) (a:=33) (b:=34) sp16504 sp16537) (joinSmall (lo:=16571) (a:=34) (b:=34) sp16571 sp16605)))) (joinSmall (lo:=16639) (a:=268) (b:=269) (joinSmall (lo:=16639) (a:=134) (b:=134) (joinSmall (lo:=16639) (a:=67) (b:=67) (joinSmall (lo:=16639) (a:=33) (b:=34) sp16639 sp16672) (joinSmall (lo:=16706) (a:=33) (b:=34) sp16706 sp16739)) (joinSmall (lo:=16773) (a:=67) (b:=67) (joinSmall (lo:=16773) (a:=33) (b:=34) sp16773 sp16806) (joinSmall (lo:=16840) (a:=33) (b:=34) sp16840 sp16873))) (joinSmall (lo:=16907) (a:=134) (b:=135) (joinSmall (lo:=16907) (a:=67) (b:=67) (joinSmall (lo:=16907) (a:=33) (b:=34) sp16907 sp16940) (joinSmall (lo:=16974) (a:=33) (b:=34) sp16974 sp17007)) (joinSmall (lo:=17041) (a:=67) (b:=68) (joinSmall (lo:=17041) (a:=33) (b:=34) sp17041 sp17074) (joinSmall (lo:=17108) (a:=34) (b:=34) sp17108 sp17142)))))))))
  have good : (List.range 17176).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 295000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 17175 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 17175 := by
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


private def packet (i : ℕ) : ℕ := (if i < 75 then (if i < 37 then (if i < 18 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else (if i < 8 then 0 else 0)))) else (if i < 13 then (if i < 11 then (if i < 10 then 0 else 0) else (if i < 12 then 0 else 0)) else (if i < 15 then (if i < 14 then 0 else 0) else (if i < 16 then 0 else (if i < 17 then 0 else 0))))) else (if i < 27 then (if i < 22 then (if i < 20 then (if i < 19 then 0 else 0) else (if i < 21 then 0 else 0)) else (if i < 24 then (if i < 23 then 0 else 0) else (if i < 25 then 0 else (if i < 26 then 0 else 0)))) else (if i < 32 then (if i < 29 then (if i < 28 then 0 else 0) else (if i < 30 then 0 else (if i < 31 then 0 else 0))) else (if i < 34 then (if i < 33 then 0 else 0) else (if i < 35 then 0 else (if i < 36 then 0 else 0)))))) else (if i < 56 then (if i < 46 then (if i < 41 then (if i < 39 then (if i < 38 then 0 else 0) else (if i < 40 then 0 else 0)) else (if i < 43 then (if i < 42 then 0 else 0) else (if i < 44 then 0 else (if i < 45 then 0 else 0)))) else (if i < 51 then (if i < 48 then (if i < 47 then 0 else 0) else (if i < 49 then 0 else (if i < 50 then 0 else 0))) else (if i < 53 then (if i < 52 then 0 else 0) else (if i < 54 then 0 else (if i < 55 then 0 else 0))))) else (if i < 65 then (if i < 60 then (if i < 58 then (if i < 57 then 0 else 0) else (if i < 59 then 0 else 0)) else (if i < 62 then (if i < 61 then 0 else 0) else (if i < 63 then 0 else (if i < 64 then 0 else 0)))) else (if i < 70 then (if i < 67 then (if i < 66 then 0 else 0) else (if i < 68 then 0 else (if i < 69 then 0 else 0))) else (if i < 72 then (if i < 71 then 0 else 0) else (if i < 73 then 0 else (if i < 74 then 0 else 0))))))) else (if i < 113 then (if i < 94 then (if i < 84 then (if i < 79 then (if i < 77 then (if i < 76 then 0 else 0) else (if i < 78 then 0 else 0)) else (if i < 81 then (if i < 80 then 0 else 0) else (if i < 82 then 0 else (if i < 83 then 0 else 0)))) else (if i < 89 then (if i < 86 then (if i < 85 then 0 else 0) else (if i < 87 then 0 else (if i < 88 then 0 else 0))) else (if i < 91 then (if i < 90 then 0 else 0) else (if i < 92 then 0 else (if i < 93 then 0 else 0))))) else (if i < 103 then (if i < 98 then (if i < 96 then (if i < 95 then 0 else 0) else (if i < 97 then 0 else 0)) else (if i < 100 then (if i < 99 then 0 else 0) else (if i < 101 then 0 else (if i < 102 then 0 else 0)))) else (if i < 108 then (if i < 105 then (if i < 104 then 0 else 0) else (if i < 106 then 0 else (if i < 107 then 0 else 0))) else (if i < 110 then (if i < 109 then 0 else 0) else (if i < 111 then 0 else (if i < 112 then 0 else 0)))))) else (if i < 132 then (if i < 122 then (if i < 117 then (if i < 115 then (if i < 114 then 0 else 0) else (if i < 116 then 0 else 0)) else (if i < 119 then (if i < 118 then 0 else 0) else (if i < 120 then 0 else (if i < 121 then 0 else 0)))) else (if i < 127 then (if i < 124 then (if i < 123 then 0 else 0) else (if i < 125 then 0 else (if i < 126 then 0 else 0))) else (if i < 129 then (if i < 128 then 0 else 0) else (if i < 130 then 0 else (if i < 131 then 0 else 0))))) else (if i < 141 then (if i < 136 then (if i < 134 then (if i < 133 then 0 else 0) else (if i < 135 then 0 else 0)) else (if i < 138 then (if i < 137 then 0 else 0xe17cc32e215809f849e21e0f506cc2fd152890c3c818a08f02f00a6000e176812ed15dca264b222a0fd473a33b16c09e442c1b00a583800f6000e1703e2f49600a504db234902475034d16c89a43f419b09683040c0000e16a432cb94d89a447920e0efc6b22f414f08fc3a417408c02dc0aa000e1643e2d395089ac47f2138f246e0308154090c3b618a091030c0c0000e15e052ec95c8a384ac2248fbc714318159894c3f018609603280d2000e157e12e1158ca0a4a52230f846fe31915d89603ec19609683300d4000e151be2e315709ee4a121e8f486d431015989103da18809282fc0c4000e14bc72ce15009ac47b20d0ed46b62fc15289483ea19c09983400d0000e145c02d295249be47720d0edc6b82fe14c88f03b018008d82d00aa000e13fbf2ce15009aa47a20e0f086be2fa14788ac3ac17608d82f80ca000e1398c2ea95bca1a4a421e0f886f631a159093c3f018f09903480e0000e1334c2ee95c8a2a4b22228fb0716322162097c3ee19009583400dc000e12d232e41570a084a72240f8472033416789643ce17d09603340c2000e127102dd155c9ee49521a0f446de30b152892c3c617708e83040b2000e120ce2e515889f249e2230f686ec31c15f098c3fe1a409b034c0d2000e11a862f41600a4c4ce234102473c33816589943fa19e09783240d8000e114742d895609f849221d8f686d830c14e88fc3d219309583080c2000e10e5a2db958ca0649c2198f106be30215008fc3d618008f83140d2000e108282e4959ca0a4a52178f486c830c15409243b217208c83040c8000e102152de1574a0849b21d0f686f631b15c095c3e219709a83440e0000e0fbe92e615989fc4a72200fb470431d15b89643fc193096032c0c2000e0f5b02ed159ca1c4a72218f506e631515c09643de18f09503240ba000e0ef6d2ee15a49f249921c8f6c6d230c15689703d819d09783400ce000e0e9282f2960ca3e4c12288fc872233216109483d018e09583140d2000e0e2f12eb15cca1c4ae2238fc070c32b16589903fe19709983140c2000e0dcc42e1959c9e648b2198f906f2316158893c3da18309203040c8000e0d6892eb15c8a0e4a521d0f7470032315c895c3f618608c82c00ae000e0d0322f715fca344b62288fd471232e16a09bc41e1aa0a083480d6000e0ca0b2e495749f84922218f8c70431515b89283cc18d09083380d4000e0c3e12e415849f64932190f306c430315009243e218c098832c0d4000e0bdbc2e495749f04922148f3c6d030514c08f43ba17c09082e00ae000e0b7b72d3952c9e04942168f146cc30315689083ba17909002d40ae000e0b1692f39608a344b62278f9c70c32a167898c40019c09803100c6000e0ab4f2e095709e249b21a0f186f831715a89043b817a08902f40c8000e0a5102f015e4a2c4a52248fa070e32715c89503e819609183080c4000e09ef32e115589d648c21a0f186c630615689203ce180093833c0d8000e098c02e9959ca204ab21b8f686f231515d09483da18a09503240ce000e092792f79630a544c222d0fe472432e16889c43fc1990a003380c4000e08c392e595c0a144a42180f406ee317157095c3ee18e09583440d8000e086412cd94d49a447a2120f286da30114988d03ae17809383080cc000e0803c2d615349e84a821e8f486d2315157893c3f419409683280bc000e079f92ed95e0a264b02228f906fc31815d89483f0198098030c0b8000e073be2eb95a8a184a521c0f686f2313158091c3da19309383340cc000e06d872e4158ca0449b21a8f346c430415209043c0186092831c0cc000e067622e515709ea48c20e8ef86d830615109343d418909483100ce000e061272f015f4a304a92228f8c6e231b15209203d418609182f00b8000e05ae62ed15f0a2e4ae2268f786ea32215c097c3e618a09083080c6000e054e52d015049b64852120f406de30c15389103c618c08f83100bc000e04ebc2e215b8a184ab2290fc072c33416709c441a19809b03500c6000e0488d2e515c0a104b022c8fd4710324163099c4081a109c03540cc000e0429c2cd150c9e448e2168f446d630d158093c3d218809202f80c8000e03c662ea95c0a0649f2220f7c6f231c15d09543dc18b09403300ce000e036402e0957ca084b22270f906f631816489ac4181a309c03540d8000e030272df9578a1649e21d8f646e830d14d89143c218c08e82d40c2000e02a192d495049c84862138f206dc31015809303d818009203000c8000e024072d415309d44922198f4c6f231015389003ba17508c02f80ac000e01de42de95649ec48a20f8f106dc31215d09543de18c09282d00b6000e017b62ea95bca284a72248f8c70831615b09643de19209c03200c6000e0119e2d715509da48e2188f586ec31215b09343d018408f03080c8000e00b792dc15649ec49d21e8f746ec31d15789003bc17e08b82b80ac000e005592da152c9da48f2170f146be2fa14a88e43ae17808a02f00c2000dfff392dc95689ea48f2180f586cc30915809343dc19309583500d6000dff8f62f2160ca3e4cc22f8fc471632516089843ee18209303040c6000) else (if i < 139 then 0xe3080f2f095e8a324b52250fa471632416689ac40819d09703100ca000e301f02e315609f849c2208f646e630b15008ec3b617408b83180c2000e2fbdc2d415249b848120b8ec06ae30514b08c439216c08882cc0c0000e2f5c92dc15209c04822140f146dc30f14f09043ba18a09e032c0ca000e2ef9f2e415ac9f84962188f746e030d15b89003c417608d82f80bc000e2e97e2e015a8a244ac2258fa070832016109743ea19209403200b2000e2e35c2dd15349de49421b8f146c02fb15289043a617308a02f40c2000e2dd022fd9634a5a4c222f8ff471232715e09403e419609903140c4000e2d6d02e59598a244b82270f9870a325166097c3fa19309403140ce000e2d09e2ea95bca224ad2230f8070031c15d093c3c017f09202f40ca000e2ca8a2df15889e848e2198f486e6314157892c3dc18909103080c0000e2c4732dd953c9ce4832130efc6b82f5147889c39817d08b02c00b8000e2be3f2e995bca1449e21d8f606ee31115a89383e618209283040c4000e2b8222dd1578a044912168f1c6d830e15989303c418208e03080b2000e2b1da2f295f0a284b02230f88718322160095c3d218509983140c0000e2abb12df9578a0449a21b0f2c6d2310159892c3d418808f83080c8000e2a5862e9958c9ee49921c0f94708323159893c3de18908e82dc0ac000e29f652e295b0a204a62250fb471e333163899440a19e09a83240c6000e299532e1954c9ea4a021f0f646f231815d89203d418809683100be000e2933c2d995189e248d2178f446ba2f114c08f03d818309183240d0000e28d1e2d715349d649121a0f706f630f15309243e019109603340cc000e286e72ed9624a464c122f8ff872e33d168097c3de193098031c0c8000e28071308968ca7c4d42388ff874834517109cc40e19e0a183840d0000e27a4b2df95a09fe49c21d0f3c6f631115209183ce18a09a03280d4000e274282e095a0a0a4a52260f886ea31d159894c3ec19009983140ca000e26ddb2f6160ca424c12328fdc74034316f89ec4321ae0a303580c0000e267b62e095709ea4962180f046c02ff156092c3d418b08d82e40b2000e261772f11600a464c42310ff873e343170899c3fe19509903280c8000e25b4f2eb95c0a1449d21e0f9870c31815389183d018b09583140ac000e255092f215e8a384b32280fbc71432b16489a440819c09e83540d2000e24ed02ea95e8a304b02250fc8714326160898c3fe19609683200c2000e248b22de1578a104a72208f5c6f831015788f03c817408a82c40b2000e2427f2eb95b09fc4aa2288f9870431315509143ce18709083340c2000e23c542e715a0a044a22228f646e631515f099c3ee19209383100cc000e236102ec15cca324bc231102473e32e16209944121b40a383800ea000e22fcd2f01604a4a4c122f8fbc71432015c89703f419309983200d0000e229af2da15289ce48120c0ec86b4301152891c3ce18b09303280d0000e223912dd9580a0249d2188f3c6e231115489283da18f093830c0b8000e21d592e895e4a204af2240fa46f6319157093c3ca18a09083040b0000e2174c2d395089c047c20f0eec6ac2fd152090c3c817d08682ec0c6000e211272e215709f449021a0f546d430a15389543fe194096030c0c8000e20b182d9151c9b24872128f106d430414e89043d417f08702b80ac000e204df2eb15b0a1449f21d0f346e030915089003c417708e02fc0c8000e1feca2d915349c84882178f406f031515b09543e619509883100c0000e1f89b2e395d8a264b02210f6c6f631815989483de18109082e00ae000e1f27b2e115a4a024a02208f9071232115d09303c618a093831c0d0000e1ec292f51638a4a4b62210f846fa32015b09143d218709303040c8000e1e6052db95509e248b2180f046e031515689403e418709483200d6000e1dfc22f315f4a2c4ac22e8fec73c32d16489bc4141a209d03300c8000e1d9a82d495109cc4882120ef86b82fc15109043b218309703300b6000e1d3602f515fca1c4b722c0fe472a32315b89483d018809282fc0b8000e1cd172ef95f0a2c4b42268fb471032016089743fe19c09c835c0c4000e1c6e42e6157c9d649b2250f546ea30c15789343d218f09583200ce000e1c0c52df158c9f249521c0f646fe31f15589183c618709183180b0000e1ba6d2fa9670a764d3235900c72433315f89903ea18909082e40ae000e1b4182f69630a484bf22c0fe473c33116889ac4261ae0a103340d4000e1adf32e315989fc4962178f286e031115889103d018309382fc0aa000e1a7f62cc94f49d047a20b8ef06b62fc14d89003a617908c82e80ce000e1a1c62e895a8a2049b21d0f546f231915909643dc18808f82fc0b6000e19b902ef9608a4a4b622a0fac70e32a161898c40619e09e83400ca000e195812da95649f649821a8f4c6da310150090c3d618909803100c2000e18f6b2dd95589e44942168f386ce30d15389043be17e09083080bc000e189272ed15e4a344aa2210f686ea30b159092c3d4188091832c0d8000e182e62f095f8a464cf2318fa8712325169099040419909a834c0d2000 else (if i < 140 then 0xe494112f91624a4c4d223b103475834c16c89d442a1a90a583340dc000e48de82de157c9fe4972160f446c6308150090c3dc18509683180d2000e487d22da15609d648c2160f206ae2fd14b88f83ac17508d02e80b6000e481b32dd956c9f249e21c0f446ea30015008f83c218609182e80ac000e47b502fa160ca444c122e0fdc72232515989343c817708f02f00bc000e475412d695189ca47820e0ec06a02f815008f43cc18a09403240ca000e46f452d095289da47a2100f4c6e230915289183b617a08e02e40ca000e469252dd95a0a044a921f0f9470031715909603e218809403240d0000e462cb3021640a5c4cf23b102c75033e16c09b840c1a009b031c0d2000e45c962e215809f849d21e8f746f031015809403d218b08a82d40ca000e456522f29608a544bb22d0fe872e334168899c3fc18e094833c0d0000e450202e715a09fc4a021f8f646e631515a895c3c817f08f02e80ce000e44a062d995489de4982140f306cc2fb14b09083ca18209383380d6000e443f92e01564a0049321a0f646fe31e160097840619b09503240d8000e43dd82e51570a184a221c0f286e230a15a09203d218509002e40c0000e437c52db954c9d248720e8ee46b42fa14e89243da18c098033c0ce000e431a02e515789f249321d8f8470a32015809243be18709883480dc000e42b762e615a0a0849221a8f446d030a153891c3d619009683300c6000e425572df15689f848a2118ee86b62fc14b08ec3ba18209002c80be000e41f132f19610a3e4ae2220f646e230d15d89403e219209883280c4000e418d32ea15c4a164ab2210f5c6f831715b893c3ce18f09883180c8000e412c42da15709f649e2240f9870032116489844081a009c037c0e4000e40c8d2e895849f849721a8f506d830815709143ca17d08f02f80b6000e406522eb1600a324a12200f706fc31515b09343bc18809583280ca000e400172f015e4a1e4ac2220f88700328160894c3de18609002e40b8000e3f9da2f195f8a324b32298f886fa31a15789583e819a09b032c0c4000e3f3b52df15649ca4842148f346d430615089483e419009383000c4000e3ed692f0960ca4e4c622a0fc472432316089583de18c09502fc0c2000e3e7402dd95789dc4872160f106d030d15608fc3b417908c82e40ba000e3e11d2e395889fa49b21c0f586f231615689283d618f09203000be000e3daed2e69580a064a42200f6c6e631b15689483e818d09302f00b6000e3d4a62f1160ca4c4b622a0fcc71831b160098c3f819e09d83340d8000e3ce7a2e395909f64982198f646f631915709343c817709382e40a8000e3c81e2f71620a4e4b12268f846fe31c15d09503da18e09683340ce000e3c1d52f71630a504ca22e8fd872833016509c440c19a09b83300d2000e3bbc32d995409f049f21f8fa46fe32715f09483e018a098832c0be000e3b58a2ef15dca184a221f0f7c6fa32115e893c3da18509103000d8000e3af7b2d695389d84852100f146dc31715889243d618909183040be000e3a9582e315aca264b92238f8c70431b15d89383da18208d02ec0ae000e3a31c2ea15a0a0449621f8f646ea30615489283cc18b09303080d0000e39cfc2df95809f249121c0f706f631715909183de18c09c03340e6000e3968c302967ca5c4c8236101c75634517189d840e1a009d835c0da000e390292fd1630a604ca2300fe872432516709683f219309783240ca000e38a242d415089da48020d8ef46c62fc15389183c617a08f02e00c0000e383e92f195f8a284a32218f886fa32015d89403ec19209503180b6000e37dca2d915389de4932138f206d4307155892c3b617908c82ec0ba000e377832f51604a3c4c02260f8471632015d89643dc18609a834c0ea000e3715c2ea95cca224b622e8fdc73a33616c09b44241ae0a3037c0da000e36b342e29584a144a221a8f3c6e431115709203d0188090831c0be000e365132df95709f248b2170f146c42fa15008d83ca18108c83040c0000e35eb52fb163ca544bf22f8fe872432416089783f4192097833c0cc000e358922de15689ee49721b8f406ec30a14b88e838a16b08b02c80c2000e352622ec95e0a164ae2230f8470631915909343de18c09783240ca000e34c2d2ed15eca2e4b82290fdc71231d15e097440a1a609983380ce000e3461a2da15409d848420a8ed069c2f714888ec3aa17e08a02d80be000e3400b2d995509e648a20b0ed46b22f014608d83c218c09303140c8000e339c52ef15e4a264c122c0fdc71832716509783f619909c03380d0000e333b32d495189aa4812130f006be30114f09383da18509282f80a8000e32d732e39594a1a4a92238f9470c32115c89583e419209803180c4000e3272e2eb9604a344b32298fa4720320159894c3f018e09783440c8000e320e12f315e0a3c4bb22b0ff873033616289643fc19909d83440ce000e31ace2d9957c9e84882150f186be2fe14e08fc3c017909002f00c0000e314692fe166ca604bf22e8fec73c33d16e09c0406198097831c0c6000e30e4f2dc95389d64812140f186d630715188fc3d418309203340da000 else 0xe61f902d395309f649d21f8f886ee30815589283ca18009302f80b4000e6197f2cf14f49a84712078edc6aa2f414688b439416a08a02f40b8000e613582e0959ca0c4a62238f5c6da31515d098040219709a03040b6000e60d1d2ea15b4a1c4b82258f9070631d162099c4121a309f83440d2000e607052d815449dc4912178f346dc31515989483e019009583200c8000e600d52e095a49fc4ac2220f7070c31f159092c3f218909483340c2000e5fab02de954c9d84852120ef86be2fc14f09043d218909503180da000e5f47f2eb15bca324b422c8fcc71833416509a84041a209e83400c0000e5ee582e515809ec4962170f0c6d630815109183ce18108e03080c8000e5e8392da956ca0049c2170ef46ce30015008e83c217b08d83000c0000e5e2062e695b0a2c4ad2228f5c6f630f15908ec3c218509202dc0aa000e5dbc82e895d0a104a42230f9c70832815e89643e419209903500d8000e5d59c2e01574a0c4a22210f8c6f231515909303ce19209703240c6000e5cf5a2e51584a0249b21d0f346d830e159092c3da17d09483080c6000e5c9332dd95689f849b2190f4c6f831115b090c3c418909302fc0be000e5c2d12fb9630a304b52250fa470431215408f03b217e09202e00c2000e5bc583059688a5c4c8231900472c32f164099c40e19c098832c0cc000e5b6062f59644a624d32338ffc72432a15e09804201ac0a003380ca000e5afeb2db15609cc4882110f1c6c030c14e08f03b618009202ec0bc000e5a9b92e715a49fc4a52260fa471032516009843e218509683340ce000e5a3b02d815489da48f2168f506ea31d15708f43b017908c82c80b6000e59d9d2da95409de4912160f2c6d830b15008f03d619209a83300c0000e597622e615c4a244b622d0fd471a32516209743fa19809c03240c6000e591222e995d8a264ae2220f7c6f831d15989243d417d08f82e40c0000e58b192d695209c248020f0f1c6d430615609403d218909283200c0000e584fb2e39574a004a12200f5c6ec30c15809643f419909583540ce000e57efb2cd95049d04902180f2c6d030715889443ea19609c83240bc000e578c22e995c4a1c4ae22c8fb46fa31a15e89a03f619509383200cc000e572902ec15c8a124a921d0f8c70a32a15e09583ec18f09303300c8000e56c582eb15989fe4942160f1c6b02fa14d89183ca18609303080ce000e5665b2d495649e24912178f386d430b15409083ce17908e02f40b6000e560232ec95cca284a721d8fd06ec31015909103ca18508f82f00b8000e559e42ec15e8a384a72248fa86fa32915d096c3e018c09683280cc000e553a52ec95eca344b92230f7c70a31715809383da19509a83280d6000e54d832e015989fc48e2190f486e2311152091c3d419409a03580dc000e5476d2dd95449da48d2108f2c6bc2ff14a08bc3aa17508b03180ce000e541512d795489ea49c2198f506e631815889603e018b08e82f80ca000e53b252e6158ca124a521d0f706f831b15809243da18b08f82e80c4000e535072e415a4a1c4a721f8f8470231d15f096c3f018c09503140ce000e52ef52d895309d64822138f386ca30b157095c3d618f098832c0c2000e528ba2e995b0a144a32218f8c6fa31715789303d618108f03080ca000e522762e89598a0049e21a8f486ea312151891c3da18d09583080bc000e51c612d915649e64902178f346d230d15489003d019209703140d2000e5162f2e895b0a264b922e8fe872833216989c441e1a109e03380ca000e50ff82e595dca1a4af2288fa86de31d16089983e018609002e40be000e509dc2d495009ba4872130ee46b830415689443e619209783700e8000e503b62e09574a124a421c8f646ee30f15609283e4193093031c0c2000e4fd812e615b4a344b22290fb070631915d89483ce18208d82d40a8000e4f74f2e9959ca104a52230f586ee31415b095c3e019309583200c0000e4f1232e19580a0c4a62280fc072632b16289803f418b09703140be000e4eaed2e995b4a1a4a92278f786ee30f15109183cc18f095830c0d2000e4e4d82da15549e44942178f446de30a15788ec3ae17f09283280c4000e4deb82dd95689fc49d2210f4c6d830015209043c2183091831c0bc000e4d8592fd9650a624d3237104475634416a09904141a10a103840d6000e4d2212ee15c4a264a42220f9c70c31f15e09483d818709703000c0000e4cbe52eb15c4a144ad2238fa46f031f15b092c3ce18609383140b4000e4c5b32e895bca0a4aa21f0f546ee313159094c3ec19409803200c6000e4bf832e715a49fc49121e8f5c6dc305153090c3c418009302f80c4000e4b9682da152c9c44792088eb869c2f514d88d43aa17908c02f00d0000e4b33a2e995aca184ae2268f6c6ec30d15309083c018308f82e40ba000e4acfd2ee1610a304aa2208f606ee31115989683f219309a03240d6000e4a6ab2f5962ca424c322f8fc471231a15889283ec19609703240c8000e4a0992d695249dc4922200fa8720330163897040419a09803300d0000e49a652ec15f0a384bf2290fa470832115d09583da19209483340c8000)))) else (if i < 146 then (if i < 143 then (if i < 142 then 0xe7aa262ec15f0a344af2258f90700318159093c3f619709603100cc000e7a40f2de156c9fe4912138f406c2303154093c3e018d09502fc0b2000e79deb2e915b0a1049a21f8f8870a31d15809443c418108c82f80b6000e797c72e695a8a044a421f8f846f031a15e896840019f09c033c0e8000e7918e2ec15a0a124ac2220f706e831e15d09743e219409903440d4000e78b7e2d6952c9dc4922140f206d4306153890c3b417a08a82ec0b8000e7856d2d495289e249921d0f606e230415309343de18e09103000c8000e77f212f31604a544bf22c0fe470c32516209683f619a099035c0de000e778cc2f99624a444b62270f946fc32115f89843ec19409d030c0c2000e772b32d895289b64842150f406c42fb14e08cc39e17108902ac0b8000e76ca02dd95809fc4992210f906ea31715d09683fe19309003140c6000e7667c2e215c0a084a82208fbc70e31915709583d618609303180d8000e760562e715a0a124a02218f7870631e164897c3f619b09a03040da000e75a2e2e215689ec4932170f246bc2fa14d09043b817909102f00c8000e754082e515b8a244b422b0fac70831f161897c3de18609283240cc000e74dd42ed15f4a204af22a8ff873233b17089e44221a80a383700de000e747bb2e915c0a104a32248fbc72433016189703ec19509483140c6000e741a72d615309f049e2160f486e231415909603e818f092031c0d2000e73b952dd958c9ea4882168f1c6d630a15008f03c017908f03040b0000e735522f215d4a204b12228f746f831315809743f219809703040ba000e72f1c2eb95fca224c1234900874433116a89bc410197094832c0d8000e728f22e715bca1a4b12248fb071432d161897c3f418f09803380d2000e722d02df158ca0e49f21f8f7c6de30e15b09643f218c09103280d2000e71ce82c294b098c46d2070ea868a2ed14788c83a4176090031c0b8000e716b32e51584a0c49e2268f8c6f831d15a09303cc186093031c0c2000e710a92d595289ca4882158f2c6e0309151092c3de18a09203140d6000e70a872da9564a024a92258fa070c31c15589583dc18909002f80ba000e704662df1554a0449b21a0f506e030a15589443d418108c82e80c8000e6fe232f01608a404bc2250f946e431515909503ea19e09e83840e0000e6f7ed2eb1614a4e4c4234901c72633016109884141a209803180c2000e6f1be2eb15e0a204af2280fd071432b16509843fe18f09403240d0000e6eb762f7964ca544c322e8fc471e32b16309883ee19209703140d2000e6e53a2e815d4a284a52220fa070a32d16989d041a1a409883300be000e6df3a2cf94e89d04852148f446e230f15809503e018609303140d0000e6d9202df15509ee48a2110ef46bc2f414908f43a617308a82e80c8000e6d2d92ef95f0a344a42270f686ee31915609183d418a09203340d6000e6ccb72e395cca244ab22a0fc071832916389943fa19109903580d6000e6c6712eb95fca4c4c32308ff473a33d16b89a440619e09a03380c8000e6c0522dc95409e048f2160f286dc30e15889483fa18809183340ce000e6ba392db15589dc4922178f346e031315609083c618409603080c0000e6b4212d815689ca48f20e0eec6c82f314688e03be18409002e00bc000e6ade82eb95bc9f849921e0f446f230f15d89343c618c09583240cc000e6a7e72cb14c49ac4812100ef06b82f6152091c3c017f08b83140da000e6a1a52f39628a2c4a72268f9c71232316009603e418809783500d8000e69b732e9159c9fe49f21c8f3c6d830a15b09483f018f0a003580e2000e695622dc95649f849a2230f88716332165898c3f419809903080b8000e68f412dc15509e04832148f306dc30f14f893c3be18309102f00c0000e689202e0156c9ee4922140f046d830b15609103b817408a02dc0b8000e682dd2ec15e0a1a4ad2260f8c70831b15e89703f0194096832c0c4000e67c942f095c0a1c4ac2230f8c72833816989ac41019909683140c0000e6766b2e895d4a2c4b02238f8c70a31e15c89443e619109383100be000e6702c2ed15eca304b62290fc871832c16709843f419309603140be000e669f02eb95dca2c4bd22d0fcc72232e160895c3e218a09703080c4000e663b62e615909f84a021a0f3c6d631015409243bc17808f83000c2000e65d772ec15c8a2c4b02268f906f631815d89303da18d09203280ce000e657312f1960ca3a4bc2288ff871231e15c890c3be17b08c82d80ac000e650f12ef95dca204b222c8ff072a32316209583da18309002f00b4000e64ac72e495b49f849c2218f646e430f15609283d418c09303280c6000e644a32e81604a2c4b72280fd471632916009943fe19f09583100c0000e63e642e795c8a0c4aa2268f8c70231915709203ce180092830c0c2000e6385b2d294ec9b84742090e9c6a62fc14e08ec3ae17e08d02fc0b4000e632362e09594a144aa2240f886e430715789583e418f09383200be000e62c002e895d0a284a621f0f406d830815409203d418b09602f40be000e625992f59600a284b02270fc472e32f16189643e619709683200c4000 else 0xe935842ef161ca484ca2318fd870432815f09683e018909183000c2000e92f672d815349e44942200f7c6fe30d153091c3d419709a033c0ba000e9292d2e6959ca044a82228f706f231115a894c3d418409803180c0000e922ef2f0960ca324b32220fb471632c163899c3ec19009383280ba000e91cb52ea15b8a1e4ab22b0fdc72e32f16489bc40619a0a083580cc000e916a92d094f09b647b20b0e8c6882df14188e03ae17608c83000c0000e910952db152c9be48020d0f106b830214e08e03b817e08e02f80c8000e90a522f3961ca3c4b722b8fcc73032a16309a04141a209903340d4000e9043f2d715209ea48c2180f306d830915a09403ea18a09203100c6000e8fe482cc14d49bc4802098ec46a62ed14408d83c818309182e00be000e8f80d2e615d0a224ac2218f806f031b15c09743f819d09a031c0da000e8f1e22e29584a024972190f406e8316157891c3c617f091830c0c0000e8ebae2e695b8a144ad2270fd872432c16109543e018709503100d8000e8e5912d895449d848a2110f246ce2fc15489143c418109603240b8000e8df7c2d815209d448c20f8f186ee31e15c89643d618c09483140c2000e8d9602df955c9d64892138f3c6e030314d89003d018a09303180b6000e8d3232f115fca204a121d0f406ba30115289103ce17408d02dc0b2000e8ccf52e695bca2a4af2280fb470832716189503e219509883280d2000e8c6be2e895eca3a4b922a0f9871c31815a897c3ea19409382f00a8000e8c08f2e995a8a104a62238f9c70c31315909383da18e09803240c4000e8ba372f59658a544c822d8ff072633516689bc4041a609e03400c4000e8b3fd2e7959ca184a82258fc872633916509b03f219609703280bc000e8adbd2ee960ca384c42340fe471e33315d09703d617d09383000cc000e8a76e2f7962ca584c22300fc072632e16689843ee19409d03440ca000e8a1662d014f49ba47e2130f346c62fe14f88c0398166088830c0cc000e89b7c2c795289ce47920f0ebc6ae2fc14b08d03b017a08d03180d2000e895542e415689e24912180f646ee32216089503e618a09203080b6000e88f1b2eb15d8a284aa2240f786fe32c16409a44041a109d833c0da000e8890a2d815249c048c2188f3c6d030315388ec3b217708882e00a2000e882b62fb9620a584c8233101c75234216a09a040219b09783200c0000e87c8e2e195b4a104aa2270fb870e32715d89343d818409583200d4000e876602e815a0a0649b21b8f386e830b15309243d618509183180c2000e870002fa162ca384b722b8fac70831d15b09603f619409683200dc000e869e32dc95349e248c2148f0c6d630e15089103c417f09002cc0bc000e863c22d995589e048b2128f386d430e15709143c218309183200be000e85d972e495a49fa4942198f586e630e15389143dc18a09803480dc000e857692ec95c8a164a421b0f6c6e230f15889403d017e08d82f00c4000e851232ee15fca484c122d0fb872a31b15a894c40219d09c83300cc000e84b122d795249da4942190f346c830014e090c3ba17808b82dc0b6000e844c22f9161ca404b62228f686d630714f08f83ac16f08602b40b8000e83e942db154c9e64952188f446dc30a15309083c8188092033c0be000e8389e2ce94f899e47520a0edc6a42ed142088c39416e08682c80c0000e832872d615389e24942160f206d830114f88fc3ca185093030c0c8000e82c662e1957c9ec49b2218f6c6f4316154892c3e418409202f80bc000e8262b2f19608a344b822d8f9c70232315d89943fc19409183480c6000e81ffd2ec95d8a304ab2258fac71032c15c89943fa19409983240c4000e819a32f49610a4c4c822f8fac6f831115889403de19109903240ba000e8136c2e695a8a024a521f8f686e230a15989443ba17b08f82e00b4000e80d2b2ee9620a444c2232900072232e163897840419309103040be000e806fa2ef15c8a1c4aa2230f706f431c15e09883f81a1093830c0bc000e80094305965ca704e0237900c74034516d8a0042c1ad0a183700cc000e7fa422f6162ca6e4c822c8fdc72e336167098c3e218e09483000b8000e7f44c2cf14f49d64812118ee86be2fc14c08e43b617e09082fc0d6000e7edfe2f015b8a064a321e0f746f831615d091c3d218809283280d8000e7e7e32d794f49b84802108efc6be2f714a88c03c218109703240c0000e7e1e82cb94d899e4712090eb86a42f914f88e43b017909283200ba000e7db833069690a744cf232100474033316389bc40c19609a83380cc000e7d56c2db155c9ec48b21b0f746fa31d15989643f619509583180b4000e7cf2a2f195f0a1c4ad2268fb072233716909b43f419e09e83480c4000e7c8fb2e915d4a284bf2298fd072232615f09743ea18d09703280cc000e7c2d02e315849f44942188f4c6ec31915b89483e019009503180e0000e7bca92e395a4a1249d21d8f9070c32c16089543e419109483340c6000e7b6812e715d4a2e4ad2238f646d230215108d03be17e095832c0dc000e7b0622e0953c9ec4912108ee46b02f8154094c3c818e09583440d6000) else (if i < 144 then 0xeac02e2eb15c0a1c4b622f8fd871c32c16589bc4121a209a82f80bc000eaba1c2df95649fa49a21e8f9070e32f16889a04101aa09d030c0c6000eab3e22ec95b4a144a92228f7070432415f89784001a309802f80b8000eaadb32ec15b4a124a72200f986f631d15d89a440018a09b03140ca000eaa7912d515049c047520c8ee86aa2e714308cc3c017b08d82e80c4000eaa14b2ef161ca384c022d8ff873632e15f89443c8181094032c0d2000ea9b4a2d515409d248820f0ee06c02fe15309403c6183097031c0da000ea952c2df15aca0849321a8f4c6d830214b08ec3c217d08e02e00c2000ea8f002e615709e649121a8f646e830f152091c3d417b08c02d80ba000ea88e22dc95489da4812138f2c6ea31615889183c218109603440d8000ea82d62d895449f249921b0f706f030d15809003c418409403400d4000ea7cb12e115449e64862140f086c830515489383d418709403280d0000ea76a32d2953c9c848d2148f446d230315109543e018709383080ce000ea70362ff1680a744ca233901073233a16d098840019a09a83240cc000ea6a172df157ca0849e21c0f606dc30f15809403e418608e82ec0b8000ea64022d5152c9dc48d2168f306e2316159094c3d018208d83040be000ea5dd42e49580a0a4a82218f9870c32816609843ec19209483080c0000ea57982e515a8a0c4a12210f98706327161098040219b09b83180ca000ea514b2f81628a364ba22e8fdc72832715e89683f419309403400c0000ea4b222e215bca204ba2300fe072232715b09643f619809c03100c4000ea44ef2e895cca264a72220f746f230b153090c3d418b09183240d2000ea3ee62d815409cc47820c0ed06c430215008ec3c018d08f82e00bc000ea389d2f115cca204b222b8fa070e32b16289703f2195093031c0ce000ea32852d995549e64912168f086cc30714d08f43b818109503300b4000ea2c372f61628a464bc2270f9c70e32915c897c3ea189090030c0ca000ea26112df156c9f44a521f0f586ee31f16009743e819109683100c4000ea1fe42eb15c8a1049b21f0f88700307154891c3bc18a09383000c2000ea19ad2ea95d8a284ab21f8f546cc30815709203ee18c08f83540d2000ea138a2d915249ce48a2168f446e431115589003d218b09103000ac000ea0d612e295589e24942190f406fc30f15609203cc19009182d00c6000ea07652d715389da48f2158f206c830415209283ca18108b02cc0b4000ea01252ef95dca0a4a62218f8c6ec31115589683e018c09682f80b0000e9faed2e795b4a164a52270fb470432516489a43f419009183340da000e9f4d62de9590a044ab2298fa871031b16089283de18d09282f00ba000e9eed02d6954c9e84902158f3c6ea30f15a095c3e6191095831c0ca000e9e8de2d2153c9e248d2120ef46c231115309343dc189090831c0d8000e9e2962f215f0a364ba22e8fe8740335168898040419d09e03480ec000e9dc5e2e995a4a064a22240fa870c32115609303ca17c08f03040c2000e9d63f2dd15689f649521e0fa870832c15d096c3e419309a83280d0000e9d0092ec1614a2e4a82248f90714327165099841c1a509f03400b8000e9c9e52e815cca0e4aa2238f746ec31815909443d617f09202dc0ba000e9c3b72e595b8a204bc2228f8470431d15f893c3d418909283040b8000e9bd922e4957c9e848e21b0f586ee316156093c3de18d096031c0d0000e9b76e2e0158c9fa49a2198f586cc2fa14b08f43c417908c02e40ca000e9b1412e495c0a1049421a0f5c6e231115409283d818409683100c4000e9ab272e11588a0649521b8f546d830515189103d218509403280d2000e9a4d42fc163ca424b522c0fec72632215c89643ea18709703200d4000e99eb82dd95449c647b20b8ed46a22fe14d88d03b017408a02ac0be000e998732ec95cca1a4b021e0f646f030f15589303d818b09583080c0000e9923d2de154c9e049021c0f546e831815a09143ce17c08a82e80ba000e98c222de95509f04a021e0f746e231115a091c3c818209303400d4000e9860d2de95249e84892140f746f231915b09683f41a50a383600ce000e97fe12e615909f84a62228f546e631715e097c3fa191094830c0be000e979b02e515b8a1249f21e0f606e231915f094c3de193095831c0ce000e9737f2e515c8a2249d21d0f686e4311156092c3ce18109282f40c4000e96d3c2f49634a384be2248f9c6f631915d89583d418f09683280c6000e9670b2e69598a184a62220f9870032615c09843e018709883500de000e960f22de9598a0649c21a8f546fa31b15f097c3fc19b09803540d0000e95ad82d995b4a1a4a62208f686e831515809403ca17f08f82f00c4000e9549b2f19618a3a4c2235905c74833116809903f419609803140ce000e94e5d2ef1604a264ad2220f906f030a154092c3dc19309a03200bc000e948142f115f8a304b22238f706d830515189283cc18508e82d40b6000e941f02dc9584a0a4962178f646e231715809503e218a09103200c6000e93bc62e19580a0a4a121d0f686ec31815d09383d6185094033c0d0000 else (if i < 145 then 0xec4a222e795c8a1c49e2160f146e631715e09643dc18809583080b6000ec441c2d094c899a46d2088e8c6862e8147889c38416108282c409e000ec3dc43021670a7e4d5236901073633216489904041a109b035c0d6000ec37cd2cb94e49a046e2088ed06c430014a88dc3c418909783240c4000ec31b12e1952c9c44822100ef46ba30815489183d418509103080c6000ec2b9d2de95549cc4802118ee86ba2f714e09043b817a09403240de000ec25732e4157c9f04962180f2c6ca30a155091c3d217f092833c0e8000ec1f5a2dc9568a004b12268fa06fa31c15c094c3e218e09483300ba000ec19042f89640a584cb236901073832d161899040c19a09703480d0000ec12ed2d715489f849221a0f6c6da30d15689343e0196098834c0d4000ec0ccd2e0157ca084a421d0f446b82fd14d08c83b617e09002e80c4000ec06962e295649e84982150f1c6c630014a88cc3ba18409383000b4000ec006c2e595bc9fe4a62218f706e631115a89583d617a08a03080be000ebfa242fa161ca404be22a8ff471c32b16d09c840819f09a83140c2000ebf40c2d815509d64882130f246ea31415d89643f2197095830c0dc000ebedde2e695c4a264a72278fac70c32116109544041a609f838c0fa000ebe7ab2e795e4a364b12278f986fa31c15b095c3de18f09303480ca000ebe1822e19594a0049221b0f5c6e631815c09303e419609a03040da000ebdb6c2d7951c9d448e21c8f786d230b15309003c218609383080c2000ebd5722c814c49924632020ebc6a22f714c08b039016d09102f40c2000ebcf7a2ca14d09b847d20e0ee86bc2fe15289003d418109483200c8000ebc9562df95849f64912180f346cc30014a889438616708182a409e000ebc3112ee9608a3c4bf22d0fec74032d16509b04081a009883240c8000ebbcdc2ec95b4a124a321f0f786f230c15909143cc17808d82e80a6000ebb6ac2ec15aca2e4b22298fa470a31c15b89543f619109703300ca000ebb0952d915189b44842158f086e030a15489003d417e09082e80b8000ebaa652e2956c9ec4992210f906f8315155891c3d618c09102f40ac000eba42f2e6159ca104a22200f8870a314156094c3e818e09a83440ce000eb9e252d6152c9d448b2190f086c42f914f88ec3ae17308d02cc0da000eb97f82e495aca264b42240fac6fc32b16509a83f8193099833c0d6000eb91c82e415a8a104a02148f306e630715008f43a416d08802d80b4000eb8b932e59570a0a4a72250fa070231315d09703d819f09f03600c6000eb857a2dd95549d048820f8ef46cc30815109343de18c09503280ce000eb7f5d2df156c9fc49d2190f446d230615389183e818e093831c0e2000eb79412dd15349cc49521b0f5c6de30b15589403ce18709282e40c8000eb73362d395289c64852198fa06f232615e89943e618d09683240cc000eb6d0e2e615909f84982170f346e230b15088fc3c617809202f80c8000eb66ff2d8954c9ea48320b0ed46ba2ff14f88f43bc18209882f80b0000eb60c02ef95dca204ad2220f846ea31015789443cc18d09583300d2000eb5a9b2e515609da4892168f406e030915509143bc18309002f00c4000eb54702ec15b0a044a021f0f986ee30f15109083ce18109202f00d0000eb4e432e3959c9f049621b0f5c6e4316159894c3e018509503300d0000eb48262e315b0a0a4a62218f8871632315d09503dc19a09a83480d4000eb41d82f1960ca404bc2268f9c6f431a15f894c3d819109883180c6000eb3ba82e415789ec48c2150f246ce30615889283e219709d83300c2000eb357b2e815a8a044a92240f986fa32716209803e619709303140a8000eb2f4e2e995aca0449b21b8f6c6f231b15689443e6189094032c0c6000eb290c2ee95c0a204ac2220f546ea31715a096040219e09b03140ba000eb22b72f89644a464b82290fe071a31b15d09703ee19b09983480d2000eb1c6e2f59610a2c4aa2230f706f431615209443f019709783140bc000eb16482d995509e04882150f2c6cc30815409083be17708902c40b0000eb100e2eb95a4a0c4a22200f646e230c15408e83b817108a02e80ba000eb09ee2d615309da4952188f446e030b156893c3c418c09103040c0000eb03f22ce15049b648120d8f1c6e830415689143c017f08e83180c8000eafdb42ec15d0a144a62208f706ee31a15c09383ce18709383000d0000eaf79c2de9574a0449f21c0f6c6ea30a15b89243e619c09b030c0d0000eaf15f2f015cca244aa2228f7470a31f15b093c3ce18c08f02f00a8000eaeb0a2f215f0a0e4ac2218f4c6e230815409303ba18008a02c80b6000eae4e22e915bca324bf22a8fbc72e32616109603e219509583180c0000eadebb2e195649da48b2150f086d02fd15408f83c618508f031c0d8000ead8b22d015149c447d2110f0c6bc2fd14e09003c018d097031c0e6000ead2912dd954c9fa49b21b0f3c6be30314e08dc3c218a09003140be000eacc8a2cd94fc9d447f20f0f106b430114d88d83a417408c03100b8000eac6672dd15549e24922188f3c6d431115309403de18a09783140d2000 else 0xedd3ea2e795b4a1a4a92260f9471832116589ac40e1a509d83300c8000edcdac2ee95e0a364bb2248f8c70231b15d09403ee18f09483280c8000edc7922dd95589f849b21c0f606f431715508d83b217b08782f00bc000edc1872d494ec9d248921a0f406ea313158890c3b417708982d40be000edbb5c2e21594a0a4a021b8f6c70031915b09643fe19909983200ca000edb5102f5964ca4a4ca2290fb071832a161097c3f819a09903540ca000edaef82e29580a0249f21e8f906ea31115d89783ee18d09983680ce000eda8c42eb95d8a244b52218f746fa31315489583f419909e035c0d6000eda2892ec95e0a1e4ae22b8fd070a31615889243ca18009783240b6000ed9c732da153c9ee49b21a0f446ea30e15689383de19409003040c8000ed965e2dd15409dc49521c8f486c430114e09043b017c08e03140c6000ed90552da15349d44822100f046ba2ff14f89003c6179090030c0c6000ed8a1e2eb15c4a104a521f8f506e630915d096840019609b83380c6000ed83f52e515d0a284a42248f886fa31a15c094c40019e09d834c0ca000ed7dd22e315a4a284a92220f806fa30e15689383c417f09082d80b4000ed77a82e515dca264b822d8ff073032915f097c3ea191092832c0e4000ed71832de15649f249d21c0f646ec31e15689343d418809503100be000ed6b632e2157c9f24922150f6c6ea30d15589043e218408c82ec0aa000ed652c2e695b4a164a22210f986da2fa14c88d83a816908682dc0ba000ed5eef2e495b0a0449c2178f586e830c15b09343ca182094032c0ce000ed58ed2d515289c84842100ed46a830515208f43be18108e82fc0ba000ed52ac2f015e0a0e4ad2200f586d431515509203c418909683240d6000ed4c9d2d515149be48420d8ef46b22fd15489103a017208f02f40ba000ed466a2eb15b0a0249a2190f486ea30e15a09243d018409102f40c4000ed404f2dc9588a104a62240f6c70231a16009503da18f094831c0c4000ed3a1f2e615e0a3a4ba2298fb071432a16009803ec19009183000c4000ed34142ce150c9b047f20e8f0c6cc31515909103c218209282f40c4000ed2dd92e895b4a224b02278f9c71c32516009543e618309182f00c6000ed27c42d3952c9d24792100f146ce30714b89103c617508c82f00ac000ed21cc2c714b49884611ff0e8869c2ec14588e43b017108c83200c6000ed1baf2e595889f84902178f546ec31815f89bc40019609783340c8000ed15702e51564a0049a21f0f9871e32b163099c40419409803280c6000ed0f342ec15a09fa4a62258fc071c32215b096840019609983040d4000ed09152de955c9cc4872188f6c6f031314f08d438816708402d00c0000ed02c82f6166ca6e4d122f0fd06fa31815f09643e219a09803240ce000ecfc932e915f8a424b12268f786e631715889243ce191090030c0c6000ecf6522ee95c4a1249521c0f6c70c32c16609ac4101a009b835c0d6000ecf0332de15549e84922160f046d230b15709403e819809103080b0000ece9fc2e815a8a064a62220f346ea31415d09543f619509903480c0000ece3e62d89580a104ab2238fbc706314155893c3e218209582f80bc000ecddbe2e795c4a1449a2218f786f432616609943f819f09b83480d4000ecd79f2dd15649ea49721c0f546ca2fa14d88f83b218109103240d0000ecd17e2e615dca1a49f2200f706f432016089443f218708e02d80c0000eccb292fb1660a664d1236900871e33716a09d040c19409783080be000ecc50f2d695109dc4962198f586fc31115989243d418209403180c4000ecbee62e495e4a364bd2280fb071032615c89483d218509383080bc000ecb8c92d995689e449421b0f4c6e630d15b89483e819109303100b8000ecb28a2ef95f4a384ba22d8fe071032416409b44001a009d83280ca000ecac582e515a8a0a4a72230fb470030c15a09383d418a09102fc0c6000eca6422de15489ec49421d8f686f631c15e098c40619e09a03240ce000eca0012eb15f0a384bf22f8fd871e32316109683e418109282dc0be000ec99e22d615509e249421a0f706e6311157894c3ec18b09602fc0b8000ec93e22d295249e449621d8f4c6de30915088e83bc18709182f80b4000ec8db02de9570a124a82230f8470032515a89683e419c09a03300b6000ec87772e5957c9fa4962178f006ba30b15308f43b217c08f03000c8000ec813b2ed15dca304b722c0fc071832b15e09503ca18609a03480c6000ec7ae02fb1650a4e4c52300fe872833916e89b84141a709c03400c2000ec74cf2d815409ee4912180f4c6d831615809403e018f09703240c8000ec6eb22df957ca0649921c8f7c6fe31d15c09483e618d09182f40c2000ec687f2e795a8a0a4a021c8f446e430a15008f83d0186092832c0ca000ec62792d615409e449721a0f4c6c630314f88d83b417b08d02ec0c0000ec5c5e2e395689f24952168f186c030514c890c3c018409203100d0000ec56562d194f89be4882148f506d430b15409183d019209883400c0000ec50432d6951c9c647b20d8ed869a2fa14588cc3a816f08e02f40aa000))) else (if i < 148 then (if i < 147 then 0xef5ee72e215809e447d20e0eec69e2e9143087c39e17708b02dc0b6000ef58b32e6158c9f44972150ef86bc2f614a08a439a17208d82cc0a8000ef529e2db15589e44882158f586ea31815989343ea19109103140b6000ef4c672e395a4a064942128ebc6aa2f614908c03b217808982d00aa000ef462c2ef95e0a184b22248fa070431c15e89783e818608e03180c0000ef3ff62e915bc9f249321a0f446c42fb14f88f03bc17b08c03000ba000ef39bc2ea15b4a0e4a721d0f486de30d15d89483d618909883300d8000ef33962e6159ca004a62260fbc71032515f89a440019e0a1836c0e2000ef2d7a2e115b8a064a32230f806f030f15509043d818b09303280ca000ef27602df9574a084962200f786e0307158091c3b617f08f83140b8000ef21512d495209d64862120ee86b82f614e89043c417608c82e00bc000ef1afd2f9961ca304b12268fa46fa31e15d89483e418709683200d4000ef14a02fb164ca604d2239103474232e16689c840419d09d03440ce000ef0e832df95449ec4902160f206ce31415d09683de18909302f80ac000ef086e2da15389e44972190f206ca30f155894c3de18409003100c6000ef022d2f295f0a344bc2290fb871833516809ac41a1a60a2036c0d6000eefc002e51584a184a92220f6c6ea30b15208f03b6180090830c0cc000eef5d22e595989ee49d2188f086ca2fe14d89003ba17d08f83100d6000eeef872f515f8a2a4b82250f9c70031e15e89843fa19809803340ce000eee95e2e49584a024982118f246d430015108f43c817e09303080b4000eee3142f4160ca3a4b222a0fac71632d15e89883fe199093032c0ba000eedcd42ee95e8a2a4b222c8fbc70431b15b895c3fe19e09883500d2000eed6cd2d215149ca4862178f206ce2fd14d09083b417c09303040ca000eed0982e295c0a1e4aa21e0f7c6f2310158094c3e218609083280ce000eeca9c2cd94e09b247120b8ec46a62f414d08dc3a417708e83000c0000eec4732e095789fa4902158f646e430d15089043cc17708c02e40c4000eebe302f415f8a144b02288f9470232316289903e018709403140d8000eeb83a2cc94f49ba4802138efc6c830615489143ca19609803100c8000eeb2392ca15049c44772108ed06ac2f815088f83b617708c82e80a6000eeac0a2ea15d4a244a72218f5c6e230615188d83b018609003080ba000eea5cb2ec15d8a324b82298fb471431d15689143c818b094830c0cc000ee9fb42de15389e248c2108f306de307155091c3c619009a83200c2000ee99682f39634a6c4c92338fc470c32416089403fe19909903180ba000ee93382e1157c9f849421a0f486ce2f615108fc3b418609383240d2000ee8d292db15709f24912188f646e630715388f83ac17208d82e00c2000ee86f72e61588a1c49b21e0f9070e32315d893c3c017c08d02f40c4000ee80bf2e815d4a244a72228f9c70e32315e095c3e218d09a834c0d4000ee7aa22e2958c9f84982190f546ea321161895c4061a409d83300d2000ee74562fa1624a604c622d8fe872c32816089943f019409883300d2000ee6e532cc95009cc48a2128f2c6ca2fb15308d83a017108f02f00ba000ee68192e915789d848e2148f5c6ea31715709083bc17d09182dc0b0000ee61ee2e5158c9f249d2250f8c70431715a09683f019909803480dc000ee5bc12e3958ca124a521c8f546f631815989483ea18a09182f80b4000ee55ae2d695249c44832118f046b430815489403ba17908c02ec0be000ee4f942d9951c9c647d2118f086d431915209283cc17d08d02ec0be000ee497c2db95249c447420b8ed46ba2fd14b89043be17908d02c00ba000ee435c2db156ca0049a21c8f2c6ce30a15008f03b418208e02ec0ba000ee3d2c2eb15cca144a82220f846ee31b16509683da19109583240da000ee371a2d595589da48b2130f106cc2fc14b88fc3c218d09803200cc000ee30da2ee15eca244bc22d0fa870031615a89583e618809083280c4000ee2a912f215fca244a421a8f706dc31515888f83ba17808c02f80be000ee24692e29588a1e4ad2278fac72432d166099040819f09d03200c8000ee1e522da15409c648a2138f406ec31515a096c3f419909703140be000ee182c2df15a0a1c4a42258f9470c31c16189603f61980a0034c0dc000ee121f2d415209d848d20e0ed86c430615489103c817f08d02ec0b2000ee0bd22f315f0a2e4b32258fbc704324161095c3f818a09803280c8000ee059f2e995749ec48e2158f3c6c830314e88c03a217609002cc0a0000edff5c2f19610a444b72270f8870031a15d098c40419d09b03300d4000edf9412d7155ca004a42210f486de316162896c4001a309903540d8000edf3362d294e09ae4722080ec06922df142888c39616408002a00b6000edecde2f39644a704e023f104075033f1700a0c42c1a709f83600e0000ede6a62eb95f0a344b722a0fa871e32c16289543ec190094034c0d0000ede0672f11620a4c4c62310fd870c31f15d89483d418f09583180c4000edda252f095dca324af22a0fd872a32716309803f618e09703400cc000 else 0xf0e89c2ec95c4a1c4a22210f9870032216089783ec196098830c0c4000f0e25d2ec15b0a2c4ad2218fa071232315c09a83f419309903180d6000f0dc322ef15e4a324b72260fb471632b15f89703ee19209983400d6000f0d5fc2ea15aca1c4b12240fd472432915989043e218c09783240ca000f0cfb42f21610a384ac2258fdc70e31c167099c4081a409e03440e0000f0c9852e8957ca0e4aa2218f8470a32416109743e618709403300d4000f0c3682da15749ec49121d8f446ec31d15989383da18409383140ca000f0bd3d2e915a8a024a82238f8c70831a15d89603d418708d830c0d0000f0b6ef2f39604a3a4b62288fac70c32615f89383d819009783100c0000f0b0bc2e795a4a004a721e0f746fa31815a094c3ea19509583400c2000f0aacc2c814cc9b247920c8ecc6b82f814c08cc3b617708902d00b4000f0a4be2ce14fc9cc47f20d0ef46bc30014d88dc39c17109002f80ca000f09e972e495909fa49e21e8f806fe31f15a89183d418d09782fc0c4000f098922d494f09d64902190f4c6e231815a895c3ea18f093832c0c6000f092692df15489ea49a2158f2c6da311158892c3d818d09683180d0000f08c432e095789fa49821c8f306f231315d89383d418308c82d40a4000f0861f2e495c8a084ad2270fd471a33516a09ac3fc19409a03200c8000f07ff52e3157c9e649821e0f9871432515f09b040a19909c83500d2000f07a0d2c914c49b847c20c8ee86a82f914b88b43a417809603180ce000f073c62ed15e4a304bb2270fa470432015e893c3de19709683400dc000f06d8d2e915aca1449f2190f446ee31d15e09a03ea19209403240c6000f0676a2dc95409da49421a0f406e630e15308fc3b617708a82e00ba000f0612f2e715709fa49621a0f646f631a15909343e819009583340e4000f05b0e2e0957c9fc49d2220f9870c31a15a89483c418109303140c4000f0550e2d7955c9de4892168f546e030e15709403e218208f82e00b2000f04ed62e315609fa4b02268fa06e430714f08fc3c818109302e80b8000f048b52e115549d448c2138f346c6308150092c3dc18909002fc0a8000f042b72cc94c89aa48120c8f0c6be30214c88d83a617b08c82d40b2000f03ca92dd1574a104ac2228f906fa31115909083d6188094031c0ca000f036962da954c9f448c2178f086ce30c156893c3e0189093831c0ae000f0307c2dd15409ea48e2198f606e231715989183d818c09383100c6000f02a682db15489e648e21b0f786fa32215d09303e619809a03140ca000f024312ef15f4a3a4ab2230f6870432816009543e019409a83300d6000f01e242d795609fa4a82200f7c6f231715989243c0183094032c0ba000f017fd2e015449e44892128f286c630415609283d018709082e40ce000f011d22e6957ca0c49b2138f206c22fe15309103d617f09183200c4000f00bae2e615849f84962180f506ce30815289243d618208f03000c8000f005752eb95d4a204b22288f806f230f15789243d418308e02e80aa000efff4c2e915a89f048d21a8f586f231415a89503f019509803280ca000eff9302da95409d84852130f346f4314153091c3c618009083140b6000eff2d82f99610a484bc2308fa470a33116e89b840819809c83540e2000efec713029688a804dc238903074434517109d841a1a40a003600e4000efe64b2e515a4a0249321a8f506fe31f15809103da18a095032c0d8000efe0062f59614a484c122d0fa471032415f09583e619509703200d0000efd9eb2db155c9ec4902180f346c8306156895c3e819a09a83580d2000efd3c12e615609e449421a0f4c6e630a15289003b818309202f40b4000efcd852ee15dca0e4ab2248f9070c31d15d894c3e618c09683340d6000efc7652d715189d047820b8efc6ca30215188e83d418909583200d4000efc1502d415109c84832128f146be30515108fc3c218a08b02e40b0000efbb082f015dca344b42260f9c71032315f898c40419b09503240d0000efb4c82ee95d8a224af2240fb06fc31e160898440219e097832c0d4000efaeaa2e0956c9fe49d21e8f5c6e631715488f83c218c09203000d2000efa8812e015a0a044972200f706f431c15a09643da19309483280d0000efa2482e915dca284af2218f9470c31b15e89783ee19b09603380d2000ef9c0a2f115dca2e4bb22e0fd873233416609ac3fe19709683040c6000ef96102ca94dc9c848420f0f206c030415789283ca18309203140c8000ef8fd92ed15c8a364b92250fdc71833316709a03ec19309503400ca000ef89a12e615cca184a72220f6c6f030a15088e43c418309082e00a0000ef837d2dc95489ec49a21d0f806e230015309203ca17a09003180cc000ef7d5d2e395789f84a221d0f746f631915809483e018509403080cc000ef77622d295149ce48b20f0f0c6ca30314f88cc3a017108e03140ca000ef715d2d294f89b64852108ef46b02f214c08c03b218009003280ca000ef6b362e515c8a1a4b02278fb4702323162098c4061a009d03380e4000ef65092e695989fe49921b8f606ec311159096c3e619809c035c0de000) else (if i < 149 then 0xf273052e11588a0449f21f8f9070a32215b89343d4187095832c0c0000f26ce62e1958c9fa49921b8f686dc308155893c3f019309203340d2000f266c02e415cca104af2250f846fc30e15e89583d618509283280c8000f260b72d314f89c448120b0f086c02fb14d08d03c418608f02f40c6000f25a792ee95cca184a82258f946f231615f89603dc19b09b035c0e8000f254612de952c9d848f21e8f746f431515a0944400199095832c0c0000f24e372e595909f849a2200f4c6ea30f159095c3e818d09102dc0ac000f2481b2da95489d24882110f206ca30415509243cc18408c82e00be000f241f52dc15549f048c21a0f3c6c82f815389283e018308c02dc0ca000f23bc22e815bca144ae2238f806fc30e15689183d017f09282f80bc000f235af2d415309d048d21b0f4c6de31215789283d219009102e80cc000f22f7f2eb95bca084992188f5870432416289443ee19209c035c0d4000f229592e615aca0c4aa2200f906f431b160095c3ec19c09583280bc000f223392dd153c9ee49e21e8f746f831d155091c3da18409302f00be000f21d072ec15f4a1c4ae2270fb071832d15c097c3f619b09c836c0e4000f216ea2dc95489f449521a0f686f031915e09703ee19609703300ba000f210dd2d395109bc47d2098ebc6a42f614f08ec39016e08a03080b6000f20a9f2ef15c8a1e4ae2270fcc73033a16889b84281a50a603780d8000f204682ea15dca144a72218f6c6e031015889343da18f09603300c6000f1fe432e3954c9ea4922158f346e830b156893c3ee19a09703040c8000f1f8212e615b0a164a62210f7c6fa31a15189003b217a08b02d40be000f1f2092da955c9ee49821a8f286dc30415009283c818809303340c4000f1ebc72ec9600a424c52338ff871c33415c89503da191095032c0d6000f1e59b2e495789ec49221c8f606f431c15709203d218a096833c0ca000f1df892d615589f849b2200f6c6f631515989403d018609383380d4000f1d9762d8953c9d24902150f146da30d15609283cc18709603180ba000f1d310308967ca6c4ce232100c74c34317089bc40c19d09502f40c4000f1ccd82eb95b4a1a4a52220f686f831815889143d0186091030c0d0000f1c6d22cd94e499e46d2060eb06ac2f514488e43be17e08f02d80b8000f1c0902ed15e4a2a4af21e8f646f831715809443e619c09903300cc000f1ba3d2fd1664a564c022c8ff072e32b15989483ce18208f03280d4000f1b4222db95349da48c2100f006e0305157892c3ca18309003180d2000f1adc42f81650a664c72318fd872832715c89583ea18709102fc0c0000f1a7a12e51594a0c4a72268f7c6fc31315408fc3ba17f08f82ec0be000f1a18b2da95709f049b21c8f706e631b15589543c417f08f03040d0000f19b572eb15c4a1049d2200f446ca30b159895c3e419909c83240ce000f195182eb95dca384b02268fc472433216b09b042019d09b83340c8000f18eea2e615b4a144a521d8f506ee32315d895c3d418609182ec0a2000f188a52ea95a49f24982140f3c6d630e15489203b817609083080b6000f182662f215dca1c4a521f0f346ee31916209643fa19509702fc0c6000f17c422e615a0a084a12238fb06f631815e89543f619c09803240c4000f176392cc14c49bc48e2100f1c6b82ff151095c3e219309903380bc000f16ff72ed95dca2a4b82290fc872632416509703fe19309b03400de000f169d82e615c8a2a4a72200f806fa31e15e09683f0199095833c0cc000f163c72d995689f64992180f306d630115389203d418909403240ca000f15d9f2df156c9f249621b8f5c6de31315589443d017e09383180d6000f1577e2df956c9fe49821e8f606ee31115489243d418709282ec0c2000f151912c894d89ae4772078ec469e2f414588b83a816708902fc0bc000f14b642e715909de48b2160f406d031115b894c3ec19409b033c0c0000f145342e495b4a1a4af2218f9870232916189783fc19909b032c0c8000f13efd2e915b0a1c4ae2298fd073232f16009943ee19a09d033c0dc000f138e62de959ca044a72268f906f2323163896c3ec18c09103000ba000f132d32d8154c9e24922140f1c6cc30015008e43be17d08e02f80c2000f12cb12df95549da48a2168f006d6318159092c3ee19d09d032c0e0000f126832e11574a1c4a62290fac70e326160096840219b09a03500d6000f120522e41594a0c49b21f0f806e831515489503e618a09203000bc000f11a242e395789f84a121e8f586e831915a89343b817b08882c40b4000f113df2f0161ca3e4c422c8ffc72c33116609a03fe19b09a03200c4000f10db52e2159ca1e4ab2250f9c6fe31815d89803f419409603280ba000f107842e895a8a004a52248fa870431c16089603f619a09c83180c6000f101772da15349de4882158f286b830315089003b017308f031c0bc000f0fb222f5961ca6a4ca2318fac70431c15b09403e619009803300c8000f0f5022dd155c9f048e21c0f5c6e631815c89403e819809b834c0ce000f0eed22e595aca224b42298fa46ea30c15609283d219409503140ac000 else (if i < 150 then 0xf3fd7c2d715489f84932178f246be2fe15689203d418509183100c4000f3f7782d295309e248c2190f406ba30a15388f43ae17a08f03040aa000f3f1212f69648a664c52320fd872433616b09a43fe19009783280be000f3eb0c2d9956c9ea49c2208f706f831715989443ce18409603240c0000f3e4d22e915b4a224a821e8f646ee31816009683e819609883200c2000f3de7f2fa164ca684ce236102c750337162895c3ea194096834c0d2000f3d8662d7153c9de4882190f346e030a15188e43b017808c03080ce000f3d2542d9956c9f249d21d0f446d631015989443ce18309a83540e0000f3cc2d2e39598a104a121f8f606ea31015909483f61a80a083580ca000f3c60f2e515649f849b21e8f7c6fa31d15a09443cc188092032c0c4000f3bffc2d895589e24872150f606d830e15909243d418c09182f80b2000f3b9c42e915cca244af2298fd0714321160095c3e419309502f80c4000f3b3872e995bc9f649e2218f5c6f231815b09803e618c096835c0d6000f3ad752d915449d048220f0ef86c230215109043ae18408e831c0ce000f3a74d2e615b4a084a621f0f546de31115789243c418508e02f80bc000f3a12d2e29594a0249f21d8f486de30815888f43c617308e83040b0000f39aea2f295f8a2c4b02290fb870832215e89303e818e09403240c2000f394ae2ea95c0a2c4b422b0fb870631b15b09703d818d096033c0d2000f38e8b2dd95589f24972188f486fc31715989243cc190095833c0cc000f388642dd956c9d84872130f006b830115209203cc17909603040c0000f3822f2e815c0a184ac2230fa06f631815e89403d619209683480ce000f37c042e015709f849f21f0f8870631f15789383d418709503240ce000f375cc2e59590a0c4942148f046b02f414d88d839e17608882f40be000f36f992ec15eca344bf22b8fc072432d16409803da18a09083280bc000f3696b2e695a8a0e4a221f8f3c6f830f15909183d218809283200da000f363442e2156c9f04a82218f5c6e430a15809543c818908c02f80b8000f35d492ce95009a44692068ecc68a2e2142886437e15e08482c80c8000f357532c694ec9ae4742128f086aa2ee14909043b217308b02f80c6000f3510e2ee15d8a264af2250f746ca30815389083d218608f82f40b8000f34ac22f31610a364b52258f706de30f15789383d618a09202e80ba000f344c02d014f89c848321a8f686e030a15c09543fc19909603180d8000f33e603029680a724d723b907476a35117189d841a19809a03340d4000f338342ea15c8a204b52260f7c70431715e89243c017f08c82ec0cc000f331f92ec95c0a1449d21a8f606f632115889103c216a08782b80b0000f32bd12e315b0a0a49c21e8f646fa30f15809203ca18b09203200ca000f325812f215e8a384b722a0fb871232a16389b04101a709f83500d4000f31f532e895bca164a02240f846fe31c15e895c3f018a09503040c0000f319282dd15649f048e2150f2c6e430915409283d818909583240c2000f313182d315349f448b2128f286c830a14e89043c818309583080c0000f30d042df156c9fa49521f8f7c6f2316158093c3e818d09483180bc000f306b52f39614a264af2208f646e631215e09483da18d095032c0c2000f300742ef15e0a264a321d0f686e0308154892c3c217e08e02dc0b2000f2fa572de157ca024952198f746fa32515a897c3fe19709703080d0000f2f41f2ec15d4a324ad2238f806f631615909343d818909082ec0c8000f2ee022db95549de4832178f306d030b15209183b218308f82e80ba000f2e7be2ef1604a444bb22e0ff0722332166897c3f819d09c03780de000f2e1a82d915489f648e2100ef86c22fe15009003a217308d02fc0c8000f2db9c2d495389cc48e2158f306ce30c150090c3d818709282f80b6000f2d56c2e59578a0249d2210f8470032015c09103c418008e02b809e000f2cf372e995b0a0249821b8f286d630815909403d218e09003000ae000f2c91b2db15409e84812150f206c030a15189543f618d09a83340b8000f2c31c2d515289d648720d8ee86b42fb14f89243e219109603400de000f2bd0c2d394f89ae47f2100ef06a62ea144889038a17308802a80ae000f2b6ca2f31638a5c4c72340ffc72c32915e89503e219609783300cc000f2b09b2e715b0a244b12280fac70e31a15909203d618309703100b8000f2aa8e2d315289be47e2138f246c82fe14c88ec3b617808d82e40d2000f2a4562f015f8a284ae2220f646e4319157892c3d218609503280d2000f29e3f2de15709f249f2210f9471232616389b04141a30a003440d4000f298282d695089c447e2100ecc6c030814d08fc3c218409183500d2000f291f12ec95d0a164a721d8f446e830e15589343e019609983300e2000f28ba92f095fca304b42280fb871232016109643f619109303100d2000f285622f115d0a1e4a62258f7070431615909583d618e09483100bc000f27f602d314d89b446b2048ec069a2f314e88e439817108b02e40b2000f279282ef15e0a464ba22b0fb470631e15e09483f619809a83400e6000 else 0xf40fe800015489dc4852158f186de30a158090c3ba17f08f82e80ae000f409e42cc94cc9be47f20b8ebc6982f614b09203de18909583080bc000f4038b2fb165ca5a4cd230900472c33a16689943f219209383040b6000))))))))

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



private theorem b140591 : covered 140591 140666 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140666 : covered 140666 140741 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140741 : covered 140741 140816 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140816 : covered 140816 140891 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140891 : covered 140891 140966 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140966 : covered 140966 141041 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141041 : covered 141041 141116 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141116 : covered 141116 141191 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141191 : covered 141191 141266 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141266 : covered 141266 141341 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141341 : covered 141341 141416 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141416 : covered 141416 141491 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141491 : covered 141491 141566 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141566 : covered 141566 141642 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141642 : covered 141642 141717 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141717 : covered 141717 141792 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141792 : covered 141792 141867 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141867 : covered 141867 141942 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141942 : covered 141942 142017 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142017 : covered 142017 142092 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142092 : covered 142092 142167 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142167 : covered 142167 142242 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142242 : covered 142242 142317 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142317 : covered 142317 142392 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142392 : covered 142392 142467 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142467 : covered 142467 142542 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142542 : covered 142542 142617 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142617 : covered 142617 142692 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142692 : covered 142692 142767 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142767 : covered 142767 142842 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142842 : covered 142842 142917 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142917 : covered 142917 142992 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b142992 : covered 142992 143067 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143067 : covered 143067 143142 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143142 : covered 143142 143217 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143217 : covered 143217 143292 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143292 : covered 143292 143367 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143367 : covered 143367 143442 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143442 : covered 143442 143517 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143517 : covered 143517 143592 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143592 : covered 143592 143667 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143667 : covered 143667 143742 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143742 : covered 143742 143817 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143817 : covered 143817 143892 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143892 : covered 143892 143967 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b143967 : covered 143967 144043 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144043 : covered 144043 144118 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144118 : covered 144118 144193 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144193 : covered 144193 144268 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144268 : covered 144268 144343 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144343 : covered 144343 144418 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144418 : covered 144418 144493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144493 : covered 144493 144568 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144568 : covered 144568 144643 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144643 : covered 144643 144718 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144718 : covered 144718 144793 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144793 : covered 144793 144868 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144868 : covered 144868 144943 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b144943 : covered 144943 145018 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145018 : covered 145018 145093 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145093 : covered 145093 145168 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145168 : covered 145168 145243 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145243 : covered 145243 145318 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145318 : covered 145318 145393 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145393 : covered 145393 145468 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145468 : covered 145468 145543 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145543 : covered 145543 145618 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145618 : covered 145618 145693 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145693 : covered 145693 145768 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145768 : covered 145768 145843 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145843 : covered 145843 145918 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145918 : covered 145918 145993 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b145993 : covered 145993 146068 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146068 : covered 146068 146143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146143 : covered 146143 146218 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146218 : covered 146218 146293 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146293 : covered 146293 146368 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146368 : covered 146368 146443 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146443 : covered 146443 146518 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146518 : covered 146518 146593 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146593 : covered 146593 146668 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146668 : covered 146668 146743 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146743 : covered 146743 146818 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146818 : covered 146818 146893 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146893 : covered 146893 146968 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b146968 : covered 146968 147043 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147043 : covered 147043 147118 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147118 : covered 147118 147193 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147193 : covered 147193 147268 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147268 : covered 147268 147343 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147343 : covered 147343 147418 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147418 : covered 147418 147493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147493 : covered 147493 147568 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147568 : covered 147568 147643 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147643 : covered 147643 147718 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147718 : covered 147718 147793 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147793 : covered 147793 147868 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147868 : covered 147868 147943 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b147943 : covered 147943 148018 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148018 : covered 148018 148093 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148093 : covered 148093 148168 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148168 : covered 148168 148243 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148243 : covered 148243 148318 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148318 : covered 148318 148393 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148393 : covered 148393 148468 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148468 : covered 148468 148543 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148543 : covered 148543 148618 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148618 : covered 148618 148693 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148693 : covered 148693 148768 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148768 : covered 148768 148844 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148844 : covered 148844 148919 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148919 : covered 148919 148994 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b148994 : covered 148994 149069 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149069 : covered 149069 149144 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149144 : covered 149144 149219 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149219 : covered 149219 149294 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149294 : covered 149294 149369 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149369 : covered 149369 149444 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149444 : covered 149444 149519 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149519 : covered 149519 149594 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149594 : covered 149594 149669 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149669 : covered 149669 149744 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149744 : covered 149744 149819 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149819 : covered 149819 149894 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149894 : covered 149894 149969 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b149969 : covered 149969 150044 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150044 : covered 150044 150119 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150119 : covered 150119 150194 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150194 : covered 150194 150269 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150269 : covered 150269 150344 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150344 : covered 150344 150419 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150419 : covered 150419 150494 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150494 : covered 150494 150569 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150569 : covered 150569 150644 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150644 : covered 150644 150719 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150719 : covered 150719 150794 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150794 : covered 150794 150869 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150869 : covered 150869 150944 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b150944 : covered 150944 151019 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151019 : covered 151019 151094 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151094 : covered 151094 151169 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151169 : covered 151169 151245 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151245 : covered 151245 151320 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151320 : covered 151320 151395 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151395 : covered 151395 151470 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151470 : covered 151470 151545 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151545 : covered 151545 151620 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151620 : covered 151620 151695 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151695 : covered 151695 151770 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151770 : covered 151770 151845 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151845 : covered 151845 151920 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151920 : covered 151920 151995 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b151995 : covered 151995 152070 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152070 : covered 152070 152145 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152145 : covered 152145 152220 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152220 : covered 152220 152295 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152295 : covered 152295 152370 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152370 : covered 152370 152445 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152445 : covered 152445 152520 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152520 : covered 152520 152595 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152595 : covered 152595 152670 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152670 : covered 152670 152745 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152745 : covered 152745 152820 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152820 : covered 152820 152895 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152895 : covered 152895 152970 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b152970 : covered 152970 153045 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b153045 : covered 153045 153120 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b153120 : covered 153120 153195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b153195 : covered 153195 153270 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b153270 : covered 153270 153345 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b153345 : covered 153345 153420 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b153420 : covered 153420 153495 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b153495 : covered 153495 153570 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b153570 : covered 153570 153646 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 140591 153646 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b140591 b140666) (joinCoverage b140741 (joinCoverage b140816 b140891))) (joinCoverage (joinCoverage b140966 b141041) (joinCoverage b141116 (joinCoverage b141191 b141266)))) (joinCoverage (joinCoverage (joinCoverage b141341 b141416) (joinCoverage b141491 (joinCoverage b141566 b141642))) (joinCoverage (joinCoverage b141717 (joinCoverage b141792 b141867)) (joinCoverage b141942 (joinCoverage b142017 b142092))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b142167 b142242) (joinCoverage b142317 (joinCoverage b142392 b142467))) (joinCoverage (joinCoverage b142542 (joinCoverage b142617 b142692)) (joinCoverage b142767 (joinCoverage b142842 b142917)))) (joinCoverage (joinCoverage (joinCoverage b142992 b143067) (joinCoverage b143142 (joinCoverage b143217 b143292))) (joinCoverage (joinCoverage b143367 (joinCoverage b143442 b143517)) (joinCoverage b143592 (joinCoverage b143667 b143742)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b143817 b143892) (joinCoverage b143967 (joinCoverage b144043 b144118))) (joinCoverage (joinCoverage b144193 (joinCoverage b144268 b144343)) (joinCoverage b144418 (joinCoverage b144493 b144568)))) (joinCoverage (joinCoverage (joinCoverage b144643 b144718) (joinCoverage b144793 (joinCoverage b144868 b144943))) (joinCoverage (joinCoverage b145018 (joinCoverage b145093 b145168)) (joinCoverage b145243 (joinCoverage b145318 b145393))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b145468 b145543) (joinCoverage b145618 (joinCoverage b145693 b145768))) (joinCoverage (joinCoverage b145843 (joinCoverage b145918 b145993)) (joinCoverage b146068 (joinCoverage b146143 b146218)))) (joinCoverage (joinCoverage (joinCoverage b146293 b146368) (joinCoverage b146443 (joinCoverage b146518 b146593))) (joinCoverage (joinCoverage b146668 (joinCoverage b146743 b146818)) (joinCoverage b146893 (joinCoverage b146968 b147043))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b147118 b147193) (joinCoverage b147268 (joinCoverage b147343 b147418))) (joinCoverage (joinCoverage b147493 b147568) (joinCoverage b147643 (joinCoverage b147718 b147793)))) (joinCoverage (joinCoverage (joinCoverage b147868 b147943) (joinCoverage b148018 (joinCoverage b148093 b148168))) (joinCoverage (joinCoverage b148243 (joinCoverage b148318 b148393)) (joinCoverage b148468 (joinCoverage b148543 b148618))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b148693 b148768) (joinCoverage b148844 (joinCoverage b148919 b148994))) (joinCoverage (joinCoverage b149069 (joinCoverage b149144 b149219)) (joinCoverage b149294 (joinCoverage b149369 b149444)))) (joinCoverage (joinCoverage (joinCoverage b149519 b149594) (joinCoverage b149669 (joinCoverage b149744 b149819))) (joinCoverage (joinCoverage b149894 (joinCoverage b149969 b150044)) (joinCoverage b150119 (joinCoverage b150194 b150269)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b150344 b150419) (joinCoverage b150494 (joinCoverage b150569 b150644))) (joinCoverage (joinCoverage b150719 (joinCoverage b150794 b150869)) (joinCoverage b150944 (joinCoverage b151019 b151094)))) (joinCoverage (joinCoverage (joinCoverage b151169 b151245) (joinCoverage b151320 (joinCoverage b151395 b151470))) (joinCoverage (joinCoverage b151545 (joinCoverage b151620 b151695)) (joinCoverage b151770 (joinCoverage b151845 b151920))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b151995 b152070) (joinCoverage b152145 (joinCoverage b152220 b152295))) (joinCoverage (joinCoverage b152370 (joinCoverage b152445 b152520)) (joinCoverage b152595 (joinCoverage b152670 b152745)))) (joinCoverage (joinCoverage (joinCoverage b152820 b152895) (joinCoverage b152970 (joinCoverage b153045 b153120))) (joinCoverage (joinCoverage b153195 (joinCoverage b153270 b153345)) (joinCoverage b153420 (joinCoverage b153495 b153570))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 140591 ≤ index 270000000/512 := by decide +kernel
private theorem starting_value : fast 270000000=14711384 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 270000000=14711384) (n : ℕ) (low : 270000000≤n) (bound : n≤295000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=270000000
    · rw [first,anchor]
      exact starting_value
    · have past : 270000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤295000000 by omega)
        have within : index n / 512 < 153646 := by omega
        have lower : index 270000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤295000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ270000000To295000000
