import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ295000000To320000000

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




private def radical : ℕ := 0x6addf451ceb69a60087dee0d0a70f969e3a7238bbad4c085bf9e10c9ef972440a2c5882838e1139295786418fd22b4f4726092b874a3229054d99f6bbe9bd9ebbbd18ca7548173efedc071707cbf69af8e2d118b21ee67c540afb1a41d32f31151b8a32eadb31e660a38482f998a61864f17d359c0268e6e9b50188c7671206aece0b2806be0a056c70eb182fd1513b97347183cd9a1311a81a476a8a34c62802e0d734b33de2b1713f93d3ad3308cfe92e29965e14f333da4661ebc5fc36bdceb8764c1c15a45bb077591785be5ad9538935fbf369208c116c97e658e8b47de5fe62943785a6d8e061bb7d0e6693debe072538cbb1210b89dcc6b7b5f6f8e9ac33b8a9061700fb2fc1b784deb8aeb106c4279025ad6c0d0e398f841f73721fd2c28fa580b70dc9ba3254d34eb007d3f4c90d63dd011c2b15487656cf33d53003c97830710a4ee5b0be160e6bb46cf8d1379e1d898b1fe01dcd286486fac2ff7e4274ad8460af76dbe9446e68c006199313b26bb55df57f28be7771c242232243631ff094f0d4f85e5f9232f339356d18c31a09272bc196cc7658e6e2da0a6eafae0310cea46c915134fc8281db6f46e7e3beb621ebf9aa1101206d43954d5f9e73553e843011e4632e1fc6cc9ab5f08b45b96fe06029cc3a6eb2e920d8f8659adea9c482b1c3aaafa9f6b5f69dbefdbc7ece1601e4a3d14becccb9aea2994487af4e73a16f713e3a2a2ac1eeaedde34682ef75cb4b0ad3c445a05827aa74d53485af831fad384e5d5e45d5a8e68d2220bb2a3b0430186cd9b584a8a14b0fbfd8dc49eddff8b61235dbc66054302ff700e87fad2d7e5ef9e4a4f5a04a945a4992f6828ed2430c476738bb811eb7be06a3e1c1110ffe5c90382f776571140db3c803bc6534dbaad71c422eecf3cba667c2b0aba610904339372886f3aeb825bc4be7745f30470723391d537c5f4242bd788b9a13cce9791622516d473efc5f59a44dc4f515a1024144d01ee2ec2f2403fe410bf354bf8ecab4489c3a39620a8c56d734e2c641605e311820e28f83cdec37592cb134590644ed8002b8a16cfdba6cbacc1c88f0adb1a6452abfc206f33bfd10e082736c850697600803c786b70916acd2b58d32dfcce96418b5891aefaf77a029b076755a8b6c580b6a9a61ef72a5829a1729e6bd62d48e04936fdfbd193a0ce5dc29d50ebb5b3bcda24d84c850f66a700854100e6641550eade1227d6539fb672bde39218d42b1c0c800a473098f605ed8462ab1b40085d41f8ca8fbd9472b6f8cba37a59cfca333a90e4a76d41fc7c8f56f984731395e964de68c9203c5bc58896eea253e71877160a697017128d883cb20997d30fdffe898481110b0f0f518d297c7138ae504de7f3212f4529b388f7434b0ff04073eba016da76f7351b7c5ef200eac8fa52aee06c786606969b716122565332f5db48db5fe8399eb35c7e021285dd4be2fdb7f5043678cc1ba637881b2f836136a7aa7ffd5f7b268af1d1065ef0cfcd4a6a242569e5e2263003d194915f8f683b5de28b5a83bf4d89bbdbdeb95fe4809123fc04601771a9f2cb4f2a096308800906297228aa1f09186059965995ee2860f956f8802381b4d63bb9533d3446017c8d98cd1dfb2af1fe6c99914241d70e5fd0cb243e48c57041b14ecc4c406754196ae896a96c99ffae41afd79be3d9d111041a0e58f0cf7c03cb90a12df20cdecf055c8f83444412cfe56d54867add387cd846f75c323e8c5ae95098cf67d2a9df10a18c132aca7a76659dc1310a23c360ab9accee8afc522933a856c220694462daa769375042e2cb66ee2c659a47d2fe2024513b3e3f01499dc48e34388c891d0ca05fcca8c05df8c7285a43da9bd3f275f9c06c24620302732c42659880edc925106ec5467c16dd6407d6fb0abe87c6b5eb9c64a1f3db211a0ac8d113cb6b08ab21dcc7e497eb1299573933394c445fcf8cd7a1267e381d04c39eef7bd54a005e413069eec813d7161a4064c2c283a50e8e6b3bb7c66492a153ea8cbb79707daca1a74e09e2f1e527d187e7beb51a87e3b37fc77d30f9efb22f80253b27741d72b4932db2d8df1a740b6f5c57be91684e4a09c05b76281665d5e2c4f6a707f6d1c7a80fde5a28842bf29a099f6df1a7b41b95ae5a8af945fbbe19fe36a9952123f0d5b8bc65e0e696fa9edf297f1aeb52de86d8616a83c5ebc76307c4e7bbe74326cdaf819c716c3fefc27315294c8e5cf03f142e0eacbf9cc8b2d505a75bccfd4b759b58afc1436451e718428b2ad07b6fc54f74396e523f2685ef995fdcf84730e39f087857f3d9c222e78995e61ae831593d753ff309df55c81c9078215faa3ef891aac7f38a08afe7315fed1dbb7b982bc9620fe994a1314eb0b6b23d95a4d371117bd7da97755eca6d0ccaf94128e15cc8a0753174fe8407693325cf9c373675496d96d0d3d5108fb23aaee05a82706e4f532953086f250e4a59fbdebd2f4c1178cb898ebbff6aa97c78a8ac900ad5682f0f8e6eff46a423acbcc644896fc53bdc606eac6138d25192a64a4a2e6af0ce3cd41a4a384e955d6f1d76d9bee7b7a71ef9eb1367ca7312aa8939bf0e2fdd3b45bdb4747c7c0f38794f6e37115dfb3615ee438251147150452c2729bbbf75a6a9da229a095931d23fd6b52dd16b8f18e86889a402da5c4280aa3fd2353f74b2a21bf3fbec82ab814efea8fba3a4c0d85e923f6a4c27c3fe288e9db95e90b4e7adc9e1d56f05c082103537d944bab030b90b2008e6f2113113c80027010e30b538f1920d66808e6f85ea4659f552fe277609fd4591f6a0c0b2bc51903338a5e4232c6a19ac6730510cce3f00257e58ed60efbd01df3ac931896e83a5f5a735a92de7ead3b82a19f2c08df34cf1535c0e1cb7767c6c93107fc2d94034833509c0f05e0e5a4f1e337056f0fd11ba5211853f543eb77b3d0bd3e325a73466ca797724eff48d36dc91f78dcc55db16a9ed0d555faeb4814c903e73dee42b70e778bc6c75bbb6ea30092dbafdd41f4a92b15e241ace1283af6dd7c773e351545004f5f14471896a04e4af5a5d8d80ede0503d815945ded729bc7184a37b8d81d7ff9504b2541d563f07e4daa0355bf3ee849ca0ce8215d30fac4eb5b1fd491098235262a1d6ee6c983fd0f6429d3b00037993aef7b79ff4c0c8f110111acd4a985dc4364ed7bea4e7bbf87d031a25017a7552d033683f65513449651779e0affd2a512988902d6c36db2cb36d3ee3f883a994e115ca14bdb612237bc7a9232ca3031e0aff563f0b6aff5e662e5209d39f401cbfca336ee1929452cafe5001ffcb7a331fe305f49a5e94b37053addf0d860b37349de81ad686beb10f02def58cc5e8db9ff24aadcf7e838f43e73c7b4d537c40180acc054f1da02fdfa42d1cf10f2c04cb671689a8345dacae81532e2dd621995355f2d2e55b86fb983c4bd391d337dd341409c5646d4d2518f2ad5a568497abdf22c7abad6448735b303f012e9f86e076854bbb36ac3f317016ab7b0441df54f751f43e26886edf9ac73f923ff1897cf8700b093531b41d9d7d6b6addaeeb5d4b783b87150f4d4f7c862caa40dfa034c74e25373a74a7bbb85423606dbabd42dc610a2589994dbf1afe6a48794ad89d02cd5c5203383f163d3001124cfc89c770538cd1775819e28834b344e1ea6ad6917cd0212c0e56fbead98782404b17e11611c4696036f9e1095308435a2ffc5364ec6c747170b3a6ad298d6b5735a75f258143b4f8bd02ca60da9e9258eb4d80d14c558d8a958c95d28929cb0203f2156b5406ab34d9a30a0103f7ea29f47c77168d385b0d9664c2678c4c5301592912707abcc17229a18de8de28b6cf5f5bcaed93598a31f6cb0feb3d358e042b812a26fcdeaeed0e1f45c19455c13360a5dc5b84bff6ae963800d820533696ce78195fa5cdcb528c184ff859f7d669009d482e995568c51fd46803ff8d015345cce587d2c3b8845d1e648218acff0cf89cea913f0581cc10280efbf139c2aff4d9f8dc3d0eee0f82b4725993376c052480a418133fd7777ff494f105753e1a71bb35f11503562b75583fe1f32c8c0f60d4625070ed8be1145a2546314e7f37e9cb540291e28c777f3cab963403e71019465699c621a4170e153ba99fe003ca2ed56ad93046a1c61969e3992c547aa63617b6eaeb21be8070d3d669c5463103765ce6385d948c730a3c921b4c980ceab870d66d7a2be677ce227475b54b1986731bd9e81270b75ee62ebd22f6706a39c9dd8fb5fbbbdfc870b62d1dc249639613bad2d89ff544eaecd1554ce14e76c7bfa93e1cb25f8fe9378038a9386788702613b312550f55113aa2de95483b7f49ca4bd9436ef0c2b84aead036f8dab17a01f081c5bd8311493661824344d37574c8cd37438914772db69268218faa0f2a7133a33ba98ca40e169e7a18a041131ace09dbd7e851e05e25d14f0534663b73fc688919f5ae0177195cdb2ce03bd441b82

private def light (n : ℕ) : Bool :=
  if n≤133 then decide n.Prime else n.gcd 14872707060906857289084508911813048098675809251055070300508818286592035566485075754388082124671571841702793317081960037166525246368924700537538282948117301741317436012998958826217903503076596121600000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤17888) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 133 = 14872707060906857289084508911813048098675809251055070300508818286592035566485075754388082124671571841702793317081960037166525246368924700537538282948117301741317436012998958826217903503076596121600000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 133 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤17888 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 34 := by unfold smallValid; decide +kernel

private theorem sp34 : smallValid 34 35 := by unfold smallValid; decide +kernel

private theorem sp69 : smallValid 69 35 := by unfold smallValid; decide +kernel

private theorem sp104 : smallValid 104 35 := by unfold smallValid; decide +kernel

private theorem sp139 : smallValid 139 35 := by unfold smallValid; decide +kernel

private theorem sp174 : smallValid 174 35 := by unfold smallValid; decide +kernel

private theorem sp209 : smallValid 209 35 := by unfold smallValid; decide +kernel

private theorem sp244 : smallValid 244 35 := by unfold smallValid; decide +kernel

private theorem sp279 : smallValid 279 35 := by unfold smallValid; decide +kernel

private theorem sp314 : smallValid 314 35 := by unfold smallValid; decide +kernel

private theorem sp349 : smallValid 349 35 := by unfold smallValid; decide +kernel

private theorem sp384 : smallValid 384 35 := by unfold smallValid; decide +kernel

private theorem sp419 : smallValid 419 35 := by unfold smallValid; decide +kernel

private theorem sp454 : smallValid 454 35 := by unfold smallValid; decide +kernel

private theorem sp489 : smallValid 489 35 := by unfold smallValid; decide +kernel

private theorem sp524 : smallValid 524 35 := by unfold smallValid; decide +kernel

private theorem sp559 : smallValid 559 34 := by unfold smallValid; decide +kernel

private theorem sp593 : smallValid 593 35 := by unfold smallValid; decide +kernel

private theorem sp628 : smallValid 628 35 := by unfold smallValid; decide +kernel

private theorem sp663 : smallValid 663 35 := by unfold smallValid; decide +kernel

private theorem sp698 : smallValid 698 35 := by unfold smallValid; decide +kernel

private theorem sp733 : smallValid 733 35 := by unfold smallValid; decide +kernel

private theorem sp768 : smallValid 768 35 := by unfold smallValid; decide +kernel

private theorem sp803 : smallValid 803 35 := by unfold smallValid; decide +kernel

private theorem sp838 : smallValid 838 35 := by unfold smallValid; decide +kernel

private theorem sp873 : smallValid 873 35 := by unfold smallValid; decide +kernel

private theorem sp908 : smallValid 908 35 := by unfold smallValid; decide +kernel

private theorem sp943 : smallValid 943 35 := by unfold smallValid; decide +kernel

private theorem sp978 : smallValid 978 35 := by unfold smallValid; decide +kernel

private theorem sp1013 : smallValid 1013 35 := by unfold smallValid; decide +kernel

private theorem sp1048 : smallValid 1048 35 := by unfold smallValid; decide +kernel

private theorem sp1083 : smallValid 1083 35 := by unfold smallValid; decide +kernel

private theorem sp1118 : smallValid 1118 34 := by unfold smallValid; decide +kernel

private theorem sp1152 : smallValid 1152 35 := by unfold smallValid; decide +kernel

private theorem sp1187 : smallValid 1187 35 := by unfold smallValid; decide +kernel

private theorem sp1222 : smallValid 1222 35 := by unfold smallValid; decide +kernel

private theorem sp1257 : smallValid 1257 35 := by unfold smallValid; decide +kernel

private theorem sp1292 : smallValid 1292 35 := by unfold smallValid; decide +kernel

private theorem sp1327 : smallValid 1327 35 := by unfold smallValid; decide +kernel

private theorem sp1362 : smallValid 1362 35 := by unfold smallValid; decide +kernel

private theorem sp1397 : smallValid 1397 35 := by unfold smallValid; decide +kernel

private theorem sp1432 : smallValid 1432 35 := by unfold smallValid; decide +kernel

private theorem sp1467 : smallValid 1467 35 := by unfold smallValid; decide +kernel

private theorem sp1502 : smallValid 1502 35 := by unfold smallValid; decide +kernel

private theorem sp1537 : smallValid 1537 35 := by unfold smallValid; decide +kernel

private theorem sp1572 : smallValid 1572 35 := by unfold smallValid; decide +kernel

private theorem sp1607 : smallValid 1607 35 := by unfold smallValid; decide +kernel

private theorem sp1642 : smallValid 1642 35 := by unfold smallValid; decide +kernel

private theorem sp1677 : smallValid 1677 34 := by unfold smallValid; decide +kernel

private theorem sp1711 : smallValid 1711 35 := by unfold smallValid; decide +kernel

private theorem sp1746 : smallValid 1746 35 := by unfold smallValid; decide +kernel

private theorem sp1781 : smallValid 1781 35 := by unfold smallValid; decide +kernel

private theorem sp1816 : smallValid 1816 35 := by unfold smallValid; decide +kernel

private theorem sp1851 : smallValid 1851 35 := by unfold smallValid; decide +kernel

private theorem sp1886 : smallValid 1886 35 := by unfold smallValid; decide +kernel

private theorem sp1921 : smallValid 1921 35 := by unfold smallValid; decide +kernel

private theorem sp1956 : smallValid 1956 35 := by unfold smallValid; decide +kernel

private theorem sp1991 : smallValid 1991 35 := by unfold smallValid; decide +kernel

private theorem sp2026 : smallValid 2026 35 := by unfold smallValid; decide +kernel

private theorem sp2061 : smallValid 2061 35 := by unfold smallValid; decide +kernel

private theorem sp2096 : smallValid 2096 35 := by unfold smallValid; decide +kernel

private theorem sp2131 : smallValid 2131 35 := by unfold smallValid; decide +kernel

private theorem sp2166 : smallValid 2166 35 := by unfold smallValid; decide +kernel

private theorem sp2201 : smallValid 2201 35 := by unfold smallValid; decide +kernel

private theorem sp2236 : smallValid 2236 34 := by unfold smallValid; decide +kernel

private theorem sp2270 : smallValid 2270 35 := by unfold smallValid; decide +kernel

private theorem sp2305 : smallValid 2305 35 := by unfold smallValid; decide +kernel

private theorem sp2340 : smallValid 2340 35 := by unfold smallValid; decide +kernel

private theorem sp2375 : smallValid 2375 35 := by unfold smallValid; decide +kernel

private theorem sp2410 : smallValid 2410 35 := by unfold smallValid; decide +kernel

private theorem sp2445 : smallValid 2445 35 := by unfold smallValid; decide +kernel

private theorem sp2480 : smallValid 2480 35 := by unfold smallValid; decide +kernel

private theorem sp2515 : smallValid 2515 35 := by unfold smallValid; decide +kernel

private theorem sp2550 : smallValid 2550 35 := by unfold smallValid; decide +kernel

private theorem sp2585 : smallValid 2585 35 := by unfold smallValid; decide +kernel

private theorem sp2620 : smallValid 2620 35 := by unfold smallValid; decide +kernel

private theorem sp2655 : smallValid 2655 35 := by unfold smallValid; decide +kernel

private theorem sp2690 : smallValid 2690 35 := by unfold smallValid; decide +kernel

private theorem sp2725 : smallValid 2725 35 := by unfold smallValid; decide +kernel

private theorem sp2760 : smallValid 2760 35 := by unfold smallValid; decide +kernel

private theorem sp2795 : smallValid 2795 34 := by unfold smallValid; decide +kernel

private theorem sp2829 : smallValid 2829 35 := by unfold smallValid; decide +kernel

private theorem sp2864 : smallValid 2864 35 := by unfold smallValid; decide +kernel

private theorem sp2899 : smallValid 2899 35 := by unfold smallValid; decide +kernel

private theorem sp2934 : smallValid 2934 35 := by unfold smallValid; decide +kernel

private theorem sp2969 : smallValid 2969 35 := by unfold smallValid; decide +kernel

private theorem sp3004 : smallValid 3004 35 := by unfold smallValid; decide +kernel

private theorem sp3039 : smallValid 3039 35 := by unfold smallValid; decide +kernel

private theorem sp3074 : smallValid 3074 35 := by unfold smallValid; decide +kernel

private theorem sp3109 : smallValid 3109 35 := by unfold smallValid; decide +kernel

private theorem sp3144 : smallValid 3144 35 := by unfold smallValid; decide +kernel

private theorem sp3179 : smallValid 3179 35 := by unfold smallValid; decide +kernel

private theorem sp3214 : smallValid 3214 35 := by unfold smallValid; decide +kernel

private theorem sp3249 : smallValid 3249 35 := by unfold smallValid; decide +kernel

private theorem sp3284 : smallValid 3284 35 := by unfold smallValid; decide +kernel

private theorem sp3319 : smallValid 3319 35 := by unfold smallValid; decide +kernel

private theorem sp3354 : smallValid 3354 34 := by unfold smallValid; decide +kernel

private theorem sp3388 : smallValid 3388 35 := by unfold smallValid; decide +kernel

private theorem sp3423 : smallValid 3423 35 := by unfold smallValid; decide +kernel

private theorem sp3458 : smallValid 3458 35 := by unfold smallValid; decide +kernel

private theorem sp3493 : smallValid 3493 35 := by unfold smallValid; decide +kernel

private theorem sp3528 : smallValid 3528 35 := by unfold smallValid; decide +kernel

private theorem sp3563 : smallValid 3563 35 := by unfold smallValid; decide +kernel

private theorem sp3598 : smallValid 3598 35 := by unfold smallValid; decide +kernel

private theorem sp3633 : smallValid 3633 35 := by unfold smallValid; decide +kernel

private theorem sp3668 : smallValid 3668 35 := by unfold smallValid; decide +kernel

private theorem sp3703 : smallValid 3703 35 := by unfold smallValid; decide +kernel

private theorem sp3738 : smallValid 3738 35 := by unfold smallValid; decide +kernel

private theorem sp3773 : smallValid 3773 35 := by unfold smallValid; decide +kernel

private theorem sp3808 : smallValid 3808 35 := by unfold smallValid; decide +kernel

private theorem sp3843 : smallValid 3843 35 := by unfold smallValid; decide +kernel

private theorem sp3878 : smallValid 3878 35 := by unfold smallValid; decide +kernel

private theorem sp3913 : smallValid 3913 34 := by unfold smallValid; decide +kernel

private theorem sp3947 : smallValid 3947 35 := by unfold smallValid; decide +kernel

private theorem sp3982 : smallValid 3982 35 := by unfold smallValid; decide +kernel

private theorem sp4017 : smallValid 4017 35 := by unfold smallValid; decide +kernel

private theorem sp4052 : smallValid 4052 35 := by unfold smallValid; decide +kernel

private theorem sp4087 : smallValid 4087 35 := by unfold smallValid; decide +kernel

private theorem sp4122 : smallValid 4122 35 := by unfold smallValid; decide +kernel

private theorem sp4157 : smallValid 4157 35 := by unfold smallValid; decide +kernel

private theorem sp4192 : smallValid 4192 35 := by unfold smallValid; decide +kernel

private theorem sp4227 : smallValid 4227 35 := by unfold smallValid; decide +kernel

private theorem sp4262 : smallValid 4262 35 := by unfold smallValid; decide +kernel

private theorem sp4297 : smallValid 4297 35 := by unfold smallValid; decide +kernel

private theorem sp4332 : smallValid 4332 35 := by unfold smallValid; decide +kernel

private theorem sp4367 : smallValid 4367 35 := by unfold smallValid; decide +kernel

private theorem sp4402 : smallValid 4402 35 := by unfold smallValid; decide +kernel

private theorem sp4437 : smallValid 4437 35 := by unfold smallValid; decide +kernel

private theorem sp4472 : smallValid 4472 34 := by unfold smallValid; decide +kernel

private theorem sp4506 : smallValid 4506 35 := by unfold smallValid; decide +kernel

private theorem sp4541 : smallValid 4541 35 := by unfold smallValid; decide +kernel

private theorem sp4576 : smallValid 4576 35 := by unfold smallValid; decide +kernel

private theorem sp4611 : smallValid 4611 35 := by unfold smallValid; decide +kernel

private theorem sp4646 : smallValid 4646 35 := by unfold smallValid; decide +kernel

private theorem sp4681 : smallValid 4681 35 := by unfold smallValid; decide +kernel

private theorem sp4716 : smallValid 4716 35 := by unfold smallValid; decide +kernel

private theorem sp4751 : smallValid 4751 35 := by unfold smallValid; decide +kernel

private theorem sp4786 : smallValid 4786 35 := by unfold smallValid; decide +kernel

private theorem sp4821 : smallValid 4821 35 := by unfold smallValid; decide +kernel

private theorem sp4856 : smallValid 4856 35 := by unfold smallValid; decide +kernel

private theorem sp4891 : smallValid 4891 35 := by unfold smallValid; decide +kernel

private theorem sp4926 : smallValid 4926 35 := by unfold smallValid; decide +kernel

private theorem sp4961 : smallValid 4961 35 := by unfold smallValid; decide +kernel

private theorem sp4996 : smallValid 4996 35 := by unfold smallValid; decide +kernel

private theorem sp5031 : smallValid 5031 34 := by unfold smallValid; decide +kernel

private theorem sp5065 : smallValid 5065 35 := by unfold smallValid; decide +kernel

private theorem sp5100 : smallValid 5100 35 := by unfold smallValid; decide +kernel

private theorem sp5135 : smallValid 5135 35 := by unfold smallValid; decide +kernel

private theorem sp5170 : smallValid 5170 35 := by unfold smallValid; decide +kernel

private theorem sp5205 : smallValid 5205 35 := by unfold smallValid; decide +kernel

private theorem sp5240 : smallValid 5240 35 := by unfold smallValid; decide +kernel

private theorem sp5275 : smallValid 5275 35 := by unfold smallValid; decide +kernel

private theorem sp5310 : smallValid 5310 35 := by unfold smallValid; decide +kernel

private theorem sp5345 : smallValid 5345 35 := by unfold smallValid; decide +kernel

private theorem sp5380 : smallValid 5380 35 := by unfold smallValid; decide +kernel

private theorem sp5415 : smallValid 5415 35 := by unfold smallValid; decide +kernel

private theorem sp5450 : smallValid 5450 35 := by unfold smallValid; decide +kernel

private theorem sp5485 : smallValid 5485 35 := by unfold smallValid; decide +kernel

private theorem sp5520 : smallValid 5520 35 := by unfold smallValid; decide +kernel

private theorem sp5555 : smallValid 5555 35 := by unfold smallValid; decide +kernel

private theorem sp5590 : smallValid 5590 34 := by unfold smallValid; decide +kernel

private theorem sp5624 : smallValid 5624 35 := by unfold smallValid; decide +kernel

private theorem sp5659 : smallValid 5659 35 := by unfold smallValid; decide +kernel

private theorem sp5694 : smallValid 5694 35 := by unfold smallValid; decide +kernel

private theorem sp5729 : smallValid 5729 35 := by unfold smallValid; decide +kernel

private theorem sp5764 : smallValid 5764 35 := by unfold smallValid; decide +kernel

private theorem sp5799 : smallValid 5799 35 := by unfold smallValid; decide +kernel

private theorem sp5834 : smallValid 5834 35 := by unfold smallValid; decide +kernel

private theorem sp5869 : smallValid 5869 35 := by unfold smallValid; decide +kernel

private theorem sp5904 : smallValid 5904 35 := by unfold smallValid; decide +kernel

private theorem sp5939 : smallValid 5939 35 := by unfold smallValid; decide +kernel

private theorem sp5974 : smallValid 5974 35 := by unfold smallValid; decide +kernel

private theorem sp6009 : smallValid 6009 35 := by unfold smallValid; decide +kernel

private theorem sp6044 : smallValid 6044 35 := by unfold smallValid; decide +kernel

private theorem sp6079 : smallValid 6079 35 := by unfold smallValid; decide +kernel

private theorem sp6114 : smallValid 6114 35 := by unfold smallValid; decide +kernel

private theorem sp6149 : smallValid 6149 34 := by unfold smallValid; decide +kernel

private theorem sp6183 : smallValid 6183 35 := by unfold smallValid; decide +kernel

private theorem sp6218 : smallValid 6218 35 := by unfold smallValid; decide +kernel

private theorem sp6253 : smallValid 6253 35 := by unfold smallValid; decide +kernel

private theorem sp6288 : smallValid 6288 35 := by unfold smallValid; decide +kernel

private theorem sp6323 : smallValid 6323 35 := by unfold smallValid; decide +kernel

private theorem sp6358 : smallValid 6358 35 := by unfold smallValid; decide +kernel

private theorem sp6393 : smallValid 6393 35 := by unfold smallValid; decide +kernel

private theorem sp6428 : smallValid 6428 35 := by unfold smallValid; decide +kernel

private theorem sp6463 : smallValid 6463 35 := by unfold smallValid; decide +kernel

private theorem sp6498 : smallValid 6498 35 := by unfold smallValid; decide +kernel

private theorem sp6533 : smallValid 6533 35 := by unfold smallValid; decide +kernel

private theorem sp6568 : smallValid 6568 35 := by unfold smallValid; decide +kernel

private theorem sp6603 : smallValid 6603 35 := by unfold smallValid; decide +kernel

private theorem sp6638 : smallValid 6638 35 := by unfold smallValid; decide +kernel

private theorem sp6673 : smallValid 6673 35 := by unfold smallValid; decide +kernel

private theorem sp6708 : smallValid 6708 34 := by unfold smallValid; decide +kernel

private theorem sp6742 : smallValid 6742 35 := by unfold smallValid; decide +kernel

private theorem sp6777 : smallValid 6777 35 := by unfold smallValid; decide +kernel

private theorem sp6812 : smallValid 6812 35 := by unfold smallValid; decide +kernel

private theorem sp6847 : smallValid 6847 35 := by unfold smallValid; decide +kernel

private theorem sp6882 : smallValid 6882 35 := by unfold smallValid; decide +kernel

private theorem sp6917 : smallValid 6917 35 := by unfold smallValid; decide +kernel

private theorem sp6952 : smallValid 6952 35 := by unfold smallValid; decide +kernel

private theorem sp6987 : smallValid 6987 35 := by unfold smallValid; decide +kernel

private theorem sp7022 : smallValid 7022 35 := by unfold smallValid; decide +kernel

private theorem sp7057 : smallValid 7057 35 := by unfold smallValid; decide +kernel

private theorem sp7092 : smallValid 7092 35 := by unfold smallValid; decide +kernel

private theorem sp7127 : smallValid 7127 35 := by unfold smallValid; decide +kernel

private theorem sp7162 : smallValid 7162 35 := by unfold smallValid; decide +kernel

private theorem sp7197 : smallValid 7197 35 := by unfold smallValid; decide +kernel

private theorem sp7232 : smallValid 7232 35 := by unfold smallValid; decide +kernel

private theorem sp7267 : smallValid 7267 34 := by unfold smallValid; decide +kernel

private theorem sp7301 : smallValid 7301 35 := by unfold smallValid; decide +kernel

private theorem sp7336 : smallValid 7336 35 := by unfold smallValid; decide +kernel

private theorem sp7371 : smallValid 7371 35 := by unfold smallValid; decide +kernel

private theorem sp7406 : smallValid 7406 35 := by unfold smallValid; decide +kernel

private theorem sp7441 : smallValid 7441 35 := by unfold smallValid; decide +kernel

private theorem sp7476 : smallValid 7476 35 := by unfold smallValid; decide +kernel

private theorem sp7511 : smallValid 7511 35 := by unfold smallValid; decide +kernel

private theorem sp7546 : smallValid 7546 35 := by unfold smallValid; decide +kernel

private theorem sp7581 : smallValid 7581 35 := by unfold smallValid; decide +kernel

private theorem sp7616 : smallValid 7616 35 := by unfold smallValid; decide +kernel

private theorem sp7651 : smallValid 7651 35 := by unfold smallValid; decide +kernel

private theorem sp7686 : smallValid 7686 35 := by unfold smallValid; decide +kernel

private theorem sp7721 : smallValid 7721 35 := by unfold smallValid; decide +kernel

private theorem sp7756 : smallValid 7756 35 := by unfold smallValid; decide +kernel

private theorem sp7791 : smallValid 7791 35 := by unfold smallValid; decide +kernel

private theorem sp7826 : smallValid 7826 34 := by unfold smallValid; decide +kernel

private theorem sp7860 : smallValid 7860 35 := by unfold smallValid; decide +kernel

private theorem sp7895 : smallValid 7895 35 := by unfold smallValid; decide +kernel

private theorem sp7930 : smallValid 7930 35 := by unfold smallValid; decide +kernel

private theorem sp7965 : smallValid 7965 35 := by unfold smallValid; decide +kernel

private theorem sp8000 : smallValid 8000 35 := by unfold smallValid; decide +kernel

private theorem sp8035 : smallValid 8035 35 := by unfold smallValid; decide +kernel

private theorem sp8070 : smallValid 8070 35 := by unfold smallValid; decide +kernel

private theorem sp8105 : smallValid 8105 35 := by unfold smallValid; decide +kernel

private theorem sp8140 : smallValid 8140 35 := by unfold smallValid; decide +kernel

private theorem sp8175 : smallValid 8175 35 := by unfold smallValid; decide +kernel

private theorem sp8210 : smallValid 8210 35 := by unfold smallValid; decide +kernel

private theorem sp8245 : smallValid 8245 35 := by unfold smallValid; decide +kernel

private theorem sp8280 : smallValid 8280 35 := by unfold smallValid; decide +kernel

private theorem sp8315 : smallValid 8315 35 := by unfold smallValid; decide +kernel

private theorem sp8350 : smallValid 8350 35 := by unfold smallValid; decide +kernel

private theorem sp8385 : smallValid 8385 34 := by unfold smallValid; decide +kernel

private theorem sp8419 : smallValid 8419 35 := by unfold smallValid; decide +kernel

private theorem sp8454 : smallValid 8454 35 := by unfold smallValid; decide +kernel

private theorem sp8489 : smallValid 8489 35 := by unfold smallValid; decide +kernel

private theorem sp8524 : smallValid 8524 35 := by unfold smallValid; decide +kernel

private theorem sp8559 : smallValid 8559 35 := by unfold smallValid; decide +kernel

private theorem sp8594 : smallValid 8594 35 := by unfold smallValid; decide +kernel

private theorem sp8629 : smallValid 8629 35 := by unfold smallValid; decide +kernel

private theorem sp8664 : smallValid 8664 35 := by unfold smallValid; decide +kernel

private theorem sp8699 : smallValid 8699 35 := by unfold smallValid; decide +kernel

private theorem sp8734 : smallValid 8734 35 := by unfold smallValid; decide +kernel

private theorem sp8769 : smallValid 8769 35 := by unfold smallValid; decide +kernel

private theorem sp8804 : smallValid 8804 35 := by unfold smallValid; decide +kernel

private theorem sp8839 : smallValid 8839 35 := by unfold smallValid; decide +kernel

private theorem sp8874 : smallValid 8874 35 := by unfold smallValid; decide +kernel

private theorem sp8909 : smallValid 8909 35 := by unfold smallValid; decide +kernel

private theorem sp8944 : smallValid 8944 34 := by unfold smallValid; decide +kernel

private theorem sp8978 : smallValid 8978 35 := by unfold smallValid; decide +kernel

private theorem sp9013 : smallValid 9013 35 := by unfold smallValid; decide +kernel

private theorem sp9048 : smallValid 9048 35 := by unfold smallValid; decide +kernel

private theorem sp9083 : smallValid 9083 35 := by unfold smallValid; decide +kernel

private theorem sp9118 : smallValid 9118 35 := by unfold smallValid; decide +kernel

private theorem sp9153 : smallValid 9153 35 := by unfold smallValid; decide +kernel

private theorem sp9188 : smallValid 9188 35 := by unfold smallValid; decide +kernel

private theorem sp9223 : smallValid 9223 35 := by unfold smallValid; decide +kernel

private theorem sp9258 : smallValid 9258 35 := by unfold smallValid; decide +kernel

private theorem sp9293 : smallValid 9293 35 := by unfold smallValid; decide +kernel

private theorem sp9328 : smallValid 9328 35 := by unfold smallValid; decide +kernel

private theorem sp9363 : smallValid 9363 35 := by unfold smallValid; decide +kernel

private theorem sp9398 : smallValid 9398 35 := by unfold smallValid; decide +kernel

private theorem sp9433 : smallValid 9433 35 := by unfold smallValid; decide +kernel

private theorem sp9468 : smallValid 9468 35 := by unfold smallValid; decide +kernel

private theorem sp9503 : smallValid 9503 34 := by unfold smallValid; decide +kernel

private theorem sp9537 : smallValid 9537 35 := by unfold smallValid; decide +kernel

private theorem sp9572 : smallValid 9572 35 := by unfold smallValid; decide +kernel

private theorem sp9607 : smallValid 9607 35 := by unfold smallValid; decide +kernel

private theorem sp9642 : smallValid 9642 35 := by unfold smallValid; decide +kernel

private theorem sp9677 : smallValid 9677 35 := by unfold smallValid; decide +kernel

private theorem sp9712 : smallValid 9712 35 := by unfold smallValid; decide +kernel

private theorem sp9747 : smallValid 9747 35 := by unfold smallValid; decide +kernel

private theorem sp9782 : smallValid 9782 35 := by unfold smallValid; decide +kernel

private theorem sp9817 : smallValid 9817 35 := by unfold smallValid; decide +kernel

private theorem sp9852 : smallValid 9852 35 := by unfold smallValid; decide +kernel

private theorem sp9887 : smallValid 9887 35 := by unfold smallValid; decide +kernel

private theorem sp9922 : smallValid 9922 35 := by unfold smallValid; decide +kernel

private theorem sp9957 : smallValid 9957 35 := by unfold smallValid; decide +kernel

private theorem sp9992 : smallValid 9992 35 := by unfold smallValid; decide +kernel

private theorem sp10027 : smallValid 10027 35 := by unfold smallValid; decide +kernel

private theorem sp10062 : smallValid 10062 34 := by unfold smallValid; decide +kernel

private theorem sp10096 : smallValid 10096 35 := by unfold smallValid; decide +kernel

private theorem sp10131 : smallValid 10131 35 := by unfold smallValid; decide +kernel

private theorem sp10166 : smallValid 10166 35 := by unfold smallValid; decide +kernel

private theorem sp10201 : smallValid 10201 35 := by unfold smallValid; decide +kernel

private theorem sp10236 : smallValid 10236 35 := by unfold smallValid; decide +kernel

private theorem sp10271 : smallValid 10271 35 := by unfold smallValid; decide +kernel

private theorem sp10306 : smallValid 10306 35 := by unfold smallValid; decide +kernel

private theorem sp10341 : smallValid 10341 35 := by unfold smallValid; decide +kernel

private theorem sp10376 : smallValid 10376 35 := by unfold smallValid; decide +kernel

private theorem sp10411 : smallValid 10411 35 := by unfold smallValid; decide +kernel

private theorem sp10446 : smallValid 10446 35 := by unfold smallValid; decide +kernel

private theorem sp10481 : smallValid 10481 35 := by unfold smallValid; decide +kernel

private theorem sp10516 : smallValid 10516 35 := by unfold smallValid; decide +kernel

private theorem sp10551 : smallValid 10551 35 := by unfold smallValid; decide +kernel

private theorem sp10586 : smallValid 10586 35 := by unfold smallValid; decide +kernel

private theorem sp10621 : smallValid 10621 34 := by unfold smallValid; decide +kernel

private theorem sp10655 : smallValid 10655 35 := by unfold smallValid; decide +kernel

private theorem sp10690 : smallValid 10690 35 := by unfold smallValid; decide +kernel

private theorem sp10725 : smallValid 10725 35 := by unfold smallValid; decide +kernel

private theorem sp10760 : smallValid 10760 35 := by unfold smallValid; decide +kernel

private theorem sp10795 : smallValid 10795 35 := by unfold smallValid; decide +kernel

private theorem sp10830 : smallValid 10830 35 := by unfold smallValid; decide +kernel

private theorem sp10865 : smallValid 10865 35 := by unfold smallValid; decide +kernel

private theorem sp10900 : smallValid 10900 35 := by unfold smallValid; decide +kernel

private theorem sp10935 : smallValid 10935 35 := by unfold smallValid; decide +kernel

private theorem sp10970 : smallValid 10970 35 := by unfold smallValid; decide +kernel

private theorem sp11005 : smallValid 11005 35 := by unfold smallValid; decide +kernel

private theorem sp11040 : smallValid 11040 35 := by unfold smallValid; decide +kernel

private theorem sp11075 : smallValid 11075 35 := by unfold smallValid; decide +kernel

private theorem sp11110 : smallValid 11110 35 := by unfold smallValid; decide +kernel

private theorem sp11145 : smallValid 11145 35 := by unfold smallValid; decide +kernel

private theorem sp11180 : smallValid 11180 34 := by unfold smallValid; decide +kernel

private theorem sp11214 : smallValid 11214 35 := by unfold smallValid; decide +kernel

private theorem sp11249 : smallValid 11249 35 := by unfold smallValid; decide +kernel

private theorem sp11284 : smallValid 11284 35 := by unfold smallValid; decide +kernel

private theorem sp11319 : smallValid 11319 35 := by unfold smallValid; decide +kernel

private theorem sp11354 : smallValid 11354 35 := by unfold smallValid; decide +kernel

private theorem sp11389 : smallValid 11389 35 := by unfold smallValid; decide +kernel

private theorem sp11424 : smallValid 11424 35 := by unfold smallValid; decide +kernel

private theorem sp11459 : smallValid 11459 35 := by unfold smallValid; decide +kernel

private theorem sp11494 : smallValid 11494 35 := by unfold smallValid; decide +kernel

private theorem sp11529 : smallValid 11529 35 := by unfold smallValid; decide +kernel

private theorem sp11564 : smallValid 11564 35 := by unfold smallValid; decide +kernel

private theorem sp11599 : smallValid 11599 35 := by unfold smallValid; decide +kernel

private theorem sp11634 : smallValid 11634 35 := by unfold smallValid; decide +kernel

private theorem sp11669 : smallValid 11669 35 := by unfold smallValid; decide +kernel

private theorem sp11704 : smallValid 11704 35 := by unfold smallValid; decide +kernel

private theorem sp11739 : smallValid 11739 34 := by unfold smallValid; decide +kernel

private theorem sp11773 : smallValid 11773 35 := by unfold smallValid; decide +kernel

private theorem sp11808 : smallValid 11808 35 := by unfold smallValid; decide +kernel

private theorem sp11843 : smallValid 11843 35 := by unfold smallValid; decide +kernel

private theorem sp11878 : smallValid 11878 35 := by unfold smallValid; decide +kernel

private theorem sp11913 : smallValid 11913 35 := by unfold smallValid; decide +kernel

private theorem sp11948 : smallValid 11948 35 := by unfold smallValid; decide +kernel

private theorem sp11983 : smallValid 11983 35 := by unfold smallValid; decide +kernel

private theorem sp12018 : smallValid 12018 35 := by unfold smallValid; decide +kernel

private theorem sp12053 : smallValid 12053 35 := by unfold smallValid; decide +kernel

private theorem sp12088 : smallValid 12088 35 := by unfold smallValid; decide +kernel

private theorem sp12123 : smallValid 12123 35 := by unfold smallValid; decide +kernel

private theorem sp12158 : smallValid 12158 35 := by unfold smallValid; decide +kernel

private theorem sp12193 : smallValid 12193 35 := by unfold smallValid; decide +kernel

private theorem sp12228 : smallValid 12228 35 := by unfold smallValid; decide +kernel

private theorem sp12263 : smallValid 12263 35 := by unfold smallValid; decide +kernel

private theorem sp12298 : smallValid 12298 34 := by unfold smallValid; decide +kernel

private theorem sp12332 : smallValid 12332 35 := by unfold smallValid; decide +kernel

private theorem sp12367 : smallValid 12367 35 := by unfold smallValid; decide +kernel

private theorem sp12402 : smallValid 12402 35 := by unfold smallValid; decide +kernel

private theorem sp12437 : smallValid 12437 35 := by unfold smallValid; decide +kernel

private theorem sp12472 : smallValid 12472 35 := by unfold smallValid; decide +kernel

private theorem sp12507 : smallValid 12507 35 := by unfold smallValid; decide +kernel

private theorem sp12542 : smallValid 12542 35 := by unfold smallValid; decide +kernel

private theorem sp12577 : smallValid 12577 35 := by unfold smallValid; decide +kernel

private theorem sp12612 : smallValid 12612 35 := by unfold smallValid; decide +kernel

private theorem sp12647 : smallValid 12647 35 := by unfold smallValid; decide +kernel

private theorem sp12682 : smallValid 12682 35 := by unfold smallValid; decide +kernel

private theorem sp12717 : smallValid 12717 35 := by unfold smallValid; decide +kernel

private theorem sp12752 : smallValid 12752 35 := by unfold smallValid; decide +kernel

private theorem sp12787 : smallValid 12787 35 := by unfold smallValid; decide +kernel

private theorem sp12822 : smallValid 12822 35 := by unfold smallValid; decide +kernel

private theorem sp12857 : smallValid 12857 34 := by unfold smallValid; decide +kernel

private theorem sp12891 : smallValid 12891 35 := by unfold smallValid; decide +kernel

private theorem sp12926 : smallValid 12926 35 := by unfold smallValid; decide +kernel

private theorem sp12961 : smallValid 12961 35 := by unfold smallValid; decide +kernel

private theorem sp12996 : smallValid 12996 35 := by unfold smallValid; decide +kernel

private theorem sp13031 : smallValid 13031 35 := by unfold smallValid; decide +kernel

private theorem sp13066 : smallValid 13066 35 := by unfold smallValid; decide +kernel

private theorem sp13101 : smallValid 13101 35 := by unfold smallValid; decide +kernel

private theorem sp13136 : smallValid 13136 35 := by unfold smallValid; decide +kernel

private theorem sp13171 : smallValid 13171 35 := by unfold smallValid; decide +kernel

private theorem sp13206 : smallValid 13206 35 := by unfold smallValid; decide +kernel

private theorem sp13241 : smallValid 13241 35 := by unfold smallValid; decide +kernel

private theorem sp13276 : smallValid 13276 35 := by unfold smallValid; decide +kernel

private theorem sp13311 : smallValid 13311 35 := by unfold smallValid; decide +kernel

private theorem sp13346 : smallValid 13346 35 := by unfold smallValid; decide +kernel

private theorem sp13381 : smallValid 13381 35 := by unfold smallValid; decide +kernel

private theorem sp13416 : smallValid 13416 34 := by unfold smallValid; decide +kernel

private theorem sp13450 : smallValid 13450 35 := by unfold smallValid; decide +kernel

private theorem sp13485 : smallValid 13485 35 := by unfold smallValid; decide +kernel

private theorem sp13520 : smallValid 13520 35 := by unfold smallValid; decide +kernel

private theorem sp13555 : smallValid 13555 35 := by unfold smallValid; decide +kernel

private theorem sp13590 : smallValid 13590 35 := by unfold smallValid; decide +kernel

private theorem sp13625 : smallValid 13625 35 := by unfold smallValid; decide +kernel

private theorem sp13660 : smallValid 13660 35 := by unfold smallValid; decide +kernel

private theorem sp13695 : smallValid 13695 35 := by unfold smallValid; decide +kernel

private theorem sp13730 : smallValid 13730 35 := by unfold smallValid; decide +kernel

private theorem sp13765 : smallValid 13765 35 := by unfold smallValid; decide +kernel

private theorem sp13800 : smallValid 13800 35 := by unfold smallValid; decide +kernel

private theorem sp13835 : smallValid 13835 35 := by unfold smallValid; decide +kernel

private theorem sp13870 : smallValid 13870 35 := by unfold smallValid; decide +kernel

private theorem sp13905 : smallValid 13905 35 := by unfold smallValid; decide +kernel

private theorem sp13940 : smallValid 13940 35 := by unfold smallValid; decide +kernel

private theorem sp13975 : smallValid 13975 34 := by unfold smallValid; decide +kernel

private theorem sp14009 : smallValid 14009 35 := by unfold smallValid; decide +kernel

private theorem sp14044 : smallValid 14044 35 := by unfold smallValid; decide +kernel

private theorem sp14079 : smallValid 14079 35 := by unfold smallValid; decide +kernel

private theorem sp14114 : smallValid 14114 35 := by unfold smallValid; decide +kernel

private theorem sp14149 : smallValid 14149 35 := by unfold smallValid; decide +kernel

private theorem sp14184 : smallValid 14184 35 := by unfold smallValid; decide +kernel

private theorem sp14219 : smallValid 14219 35 := by unfold smallValid; decide +kernel

private theorem sp14254 : smallValid 14254 35 := by unfold smallValid; decide +kernel

private theorem sp14289 : smallValid 14289 35 := by unfold smallValid; decide +kernel

private theorem sp14324 : smallValid 14324 35 := by unfold smallValid; decide +kernel

private theorem sp14359 : smallValid 14359 35 := by unfold smallValid; decide +kernel

private theorem sp14394 : smallValid 14394 35 := by unfold smallValid; decide +kernel

private theorem sp14429 : smallValid 14429 35 := by unfold smallValid; decide +kernel

private theorem sp14464 : smallValid 14464 35 := by unfold smallValid; decide +kernel

private theorem sp14499 : smallValid 14499 35 := by unfold smallValid; decide +kernel

private theorem sp14534 : smallValid 14534 34 := by unfold smallValid; decide +kernel

private theorem sp14568 : smallValid 14568 35 := by unfold smallValid; decide +kernel

private theorem sp14603 : smallValid 14603 35 := by unfold smallValid; decide +kernel

private theorem sp14638 : smallValid 14638 35 := by unfold smallValid; decide +kernel

private theorem sp14673 : smallValid 14673 35 := by unfold smallValid; decide +kernel

private theorem sp14708 : smallValid 14708 35 := by unfold smallValid; decide +kernel

private theorem sp14743 : smallValid 14743 35 := by unfold smallValid; decide +kernel

private theorem sp14778 : smallValid 14778 35 := by unfold smallValid; decide +kernel

private theorem sp14813 : smallValid 14813 35 := by unfold smallValid; decide +kernel

private theorem sp14848 : smallValid 14848 35 := by unfold smallValid; decide +kernel

private theorem sp14883 : smallValid 14883 35 := by unfold smallValid; decide +kernel

private theorem sp14918 : smallValid 14918 35 := by unfold smallValid; decide +kernel

private theorem sp14953 : smallValid 14953 35 := by unfold smallValid; decide +kernel

private theorem sp14988 : smallValid 14988 35 := by unfold smallValid; decide +kernel

private theorem sp15023 : smallValid 15023 35 := by unfold smallValid; decide +kernel

private theorem sp15058 : smallValid 15058 35 := by unfold smallValid; decide +kernel

private theorem sp15093 : smallValid 15093 34 := by unfold smallValid; decide +kernel

private theorem sp15127 : smallValid 15127 35 := by unfold smallValid; decide +kernel

private theorem sp15162 : smallValid 15162 35 := by unfold smallValid; decide +kernel

private theorem sp15197 : smallValid 15197 35 := by unfold smallValid; decide +kernel

private theorem sp15232 : smallValid 15232 35 := by unfold smallValid; decide +kernel

private theorem sp15267 : smallValid 15267 35 := by unfold smallValid; decide +kernel

private theorem sp15302 : smallValid 15302 35 := by unfold smallValid; decide +kernel

private theorem sp15337 : smallValid 15337 35 := by unfold smallValid; decide +kernel

private theorem sp15372 : smallValid 15372 35 := by unfold smallValid; decide +kernel

private theorem sp15407 : smallValid 15407 35 := by unfold smallValid; decide +kernel

private theorem sp15442 : smallValid 15442 35 := by unfold smallValid; decide +kernel

private theorem sp15477 : smallValid 15477 35 := by unfold smallValid; decide +kernel

private theorem sp15512 : smallValid 15512 35 := by unfold smallValid; decide +kernel

private theorem sp15547 : smallValid 15547 35 := by unfold smallValid; decide +kernel

private theorem sp15582 : smallValid 15582 35 := by unfold smallValid; decide +kernel

private theorem sp15617 : smallValid 15617 35 := by unfold smallValid; decide +kernel

private theorem sp15652 : smallValid 15652 34 := by unfold smallValid; decide +kernel

private theorem sp15686 : smallValid 15686 35 := by unfold smallValid; decide +kernel

private theorem sp15721 : smallValid 15721 35 := by unfold smallValid; decide +kernel

private theorem sp15756 : smallValid 15756 35 := by unfold smallValid; decide +kernel

private theorem sp15791 : smallValid 15791 35 := by unfold smallValid; decide +kernel

private theorem sp15826 : smallValid 15826 35 := by unfold smallValid; decide +kernel

private theorem sp15861 : smallValid 15861 35 := by unfold smallValid; decide +kernel

private theorem sp15896 : smallValid 15896 35 := by unfold smallValid; decide +kernel

private theorem sp15931 : smallValid 15931 35 := by unfold smallValid; decide +kernel

private theorem sp15966 : smallValid 15966 35 := by unfold smallValid; decide +kernel

private theorem sp16001 : smallValid 16001 35 := by unfold smallValid; decide +kernel

private theorem sp16036 : smallValid 16036 35 := by unfold smallValid; decide +kernel

private theorem sp16071 : smallValid 16071 35 := by unfold smallValid; decide +kernel

private theorem sp16106 : smallValid 16106 35 := by unfold smallValid; decide +kernel

private theorem sp16141 : smallValid 16141 35 := by unfold smallValid; decide +kernel

private theorem sp16176 : smallValid 16176 35 := by unfold smallValid; decide +kernel

private theorem sp16211 : smallValid 16211 34 := by unfold smallValid; decide +kernel

private theorem sp16245 : smallValid 16245 35 := by unfold smallValid; decide +kernel

private theorem sp16280 : smallValid 16280 35 := by unfold smallValid; decide +kernel

private theorem sp16315 : smallValid 16315 35 := by unfold smallValid; decide +kernel

private theorem sp16350 : smallValid 16350 35 := by unfold smallValid; decide +kernel

private theorem sp16385 : smallValid 16385 35 := by unfold smallValid; decide +kernel

private theorem sp16420 : smallValid 16420 35 := by unfold smallValid; decide +kernel

private theorem sp16455 : smallValid 16455 35 := by unfold smallValid; decide +kernel

private theorem sp16490 : smallValid 16490 35 := by unfold smallValid; decide +kernel

private theorem sp16525 : smallValid 16525 35 := by unfold smallValid; decide +kernel

private theorem sp16560 : smallValid 16560 35 := by unfold smallValid; decide +kernel

private theorem sp16595 : smallValid 16595 35 := by unfold smallValid; decide +kernel

private theorem sp16630 : smallValid 16630 35 := by unfold smallValid; decide +kernel

private theorem sp16665 : smallValid 16665 35 := by unfold smallValid; decide +kernel

private theorem sp16700 : smallValid 16700 35 := by unfold smallValid; decide +kernel

private theorem sp16735 : smallValid 16735 35 := by unfold smallValid; decide +kernel

private theorem sp16770 : smallValid 16770 34 := by unfold smallValid; decide +kernel

private theorem sp16804 : smallValid 16804 35 := by unfold smallValid; decide +kernel

private theorem sp16839 : smallValid 16839 35 := by unfold smallValid; decide +kernel

private theorem sp16874 : smallValid 16874 35 := by unfold smallValid; decide +kernel

private theorem sp16909 : smallValid 16909 35 := by unfold smallValid; decide +kernel

private theorem sp16944 : smallValid 16944 35 := by unfold smallValid; decide +kernel

private theorem sp16979 : smallValid 16979 35 := by unfold smallValid; decide +kernel

private theorem sp17014 : smallValid 17014 35 := by unfold smallValid; decide +kernel

private theorem sp17049 : smallValid 17049 35 := by unfold smallValid; decide +kernel

private theorem sp17084 : smallValid 17084 35 := by unfold smallValid; decide +kernel

private theorem sp17119 : smallValid 17119 35 := by unfold smallValid; decide +kernel

private theorem sp17154 : smallValid 17154 35 := by unfold smallValid; decide +kernel

private theorem sp17189 : smallValid 17189 35 := by unfold smallValid; decide +kernel

private theorem sp17224 : smallValid 17224 35 := by unfold smallValid; decide +kernel

private theorem sp17259 : smallValid 17259 35 := by unfold smallValid; decide +kernel

private theorem sp17294 : smallValid 17294 35 := by unfold smallValid; decide +kernel

private theorem sp17329 : smallValid 17329 35 := by unfold smallValid; decide +kernel

private theorem sp17364 : smallValid 17364 35 := by unfold smallValid; decide +kernel

private theorem sp17399 : smallValid 17399 35 := by unfold smallValid; decide +kernel

private theorem sp17434 : smallValid 17434 35 := by unfold smallValid; decide +kernel

private theorem sp17469 : smallValid 17469 35 := by unfold smallValid; decide +kernel

private theorem sp17504 : smallValid 17504 35 := by unfold smallValid; decide +kernel

private theorem sp17539 : smallValid 17539 35 := by unfold smallValid; decide +kernel

private theorem sp17574 : smallValid 17574 35 := by unfold smallValid; decide +kernel

private theorem sp17609 : smallValid 17609 35 := by unfold smallValid; decide +kernel

private theorem sp17644 : smallValid 17644 35 := by unfold smallValid; decide +kernel

private theorem sp17679 : smallValid 17679 35 := by unfold smallValid; decide +kernel

private theorem sp17714 : smallValid 17714 35 := by unfold smallValid; decide +kernel

private theorem sp17749 : smallValid 17749 35 := by unfold smallValid; decide +kernel

private theorem sp17784 : smallValid 17784 35 := by unfold smallValid; decide +kernel

private theorem sp17819 : smallValid 17819 35 := by unfold smallValid; decide +kernel

private theorem sp17854 : smallValid 17854 35 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤17888) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 17889 := (joinSmall (lo:=0) (a:=8944) (b:=8945) (joinSmall (lo:=0) (a:=4472) (b:=4472) (joinSmall (lo:=0) (a:=2236) (b:=2236) (joinSmall (lo:=0) (a:=1118) (b:=1118) (joinSmall (lo:=0) (a:=559) (b:=559) (joinSmall (lo:=0) (a:=279) (b:=280) (joinSmall (lo:=0) (a:=139) (b:=140) (joinSmall (lo:=0) (a:=69) (b:=70) (joinSmall (lo:=0) (a:=34) (b:=35) sp0 sp34) (joinSmall (lo:=69) (a:=35) (b:=35) sp69 sp104)) (joinSmall (lo:=139) (a:=70) (b:=70) (joinSmall (lo:=139) (a:=35) (b:=35) sp139 sp174) (joinSmall (lo:=209) (a:=35) (b:=35) sp209 sp244))) (joinSmall (lo:=279) (a:=140) (b:=140) (joinSmall (lo:=279) (a:=70) (b:=70) (joinSmall (lo:=279) (a:=35) (b:=35) sp279 sp314) (joinSmall (lo:=349) (a:=35) (b:=35) sp349 sp384)) (joinSmall (lo:=419) (a:=70) (b:=70) (joinSmall (lo:=419) (a:=35) (b:=35) sp419 sp454) (joinSmall (lo:=489) (a:=35) (b:=35) sp489 sp524)))) (joinSmall (lo:=559) (a:=279) (b:=280) (joinSmall (lo:=559) (a:=139) (b:=140) (joinSmall (lo:=559) (a:=69) (b:=70) (joinSmall (lo:=559) (a:=34) (b:=35) sp559 sp593) (joinSmall (lo:=628) (a:=35) (b:=35) sp628 sp663)) (joinSmall (lo:=698) (a:=70) (b:=70) (joinSmall (lo:=698) (a:=35) (b:=35) sp698 sp733) (joinSmall (lo:=768) (a:=35) (b:=35) sp768 sp803))) (joinSmall (lo:=838) (a:=140) (b:=140) (joinSmall (lo:=838) (a:=70) (b:=70) (joinSmall (lo:=838) (a:=35) (b:=35) sp838 sp873) (joinSmall (lo:=908) (a:=35) (b:=35) sp908 sp943)) (joinSmall (lo:=978) (a:=70) (b:=70) (joinSmall (lo:=978) (a:=35) (b:=35) sp978 sp1013) (joinSmall (lo:=1048) (a:=35) (b:=35) sp1048 sp1083))))) (joinSmall (lo:=1118) (a:=559) (b:=559) (joinSmall (lo:=1118) (a:=279) (b:=280) (joinSmall (lo:=1118) (a:=139) (b:=140) (joinSmall (lo:=1118) (a:=69) (b:=70) (joinSmall (lo:=1118) (a:=34) (b:=35) sp1118 sp1152) (joinSmall (lo:=1187) (a:=35) (b:=35) sp1187 sp1222)) (joinSmall (lo:=1257) (a:=70) (b:=70) (joinSmall (lo:=1257) (a:=35) (b:=35) sp1257 sp1292) (joinSmall (lo:=1327) (a:=35) (b:=35) sp1327 sp1362))) (joinSmall (lo:=1397) (a:=140) (b:=140) (joinSmall (lo:=1397) (a:=70) (b:=70) (joinSmall (lo:=1397) (a:=35) (b:=35) sp1397 sp1432) (joinSmall (lo:=1467) (a:=35) (b:=35) sp1467 sp1502)) (joinSmall (lo:=1537) (a:=70) (b:=70) (joinSmall (lo:=1537) (a:=35) (b:=35) sp1537 sp1572) (joinSmall (lo:=1607) (a:=35) (b:=35) sp1607 sp1642)))) (joinSmall (lo:=1677) (a:=279) (b:=280) (joinSmall (lo:=1677) (a:=139) (b:=140) (joinSmall (lo:=1677) (a:=69) (b:=70) (joinSmall (lo:=1677) (a:=34) (b:=35) sp1677 sp1711) (joinSmall (lo:=1746) (a:=35) (b:=35) sp1746 sp1781)) (joinSmall (lo:=1816) (a:=70) (b:=70) (joinSmall (lo:=1816) (a:=35) (b:=35) sp1816 sp1851) (joinSmall (lo:=1886) (a:=35) (b:=35) sp1886 sp1921))) (joinSmall (lo:=1956) (a:=140) (b:=140) (joinSmall (lo:=1956) (a:=70) (b:=70) (joinSmall (lo:=1956) (a:=35) (b:=35) sp1956 sp1991) (joinSmall (lo:=2026) (a:=35) (b:=35) sp2026 sp2061)) (joinSmall (lo:=2096) (a:=70) (b:=70) (joinSmall (lo:=2096) (a:=35) (b:=35) sp2096 sp2131) (joinSmall (lo:=2166) (a:=35) (b:=35) sp2166 sp2201)))))) (joinSmall (lo:=2236) (a:=1118) (b:=1118) (joinSmall (lo:=2236) (a:=559) (b:=559) (joinSmall (lo:=2236) (a:=279) (b:=280) (joinSmall (lo:=2236) (a:=139) (b:=140) (joinSmall (lo:=2236) (a:=69) (b:=70) (joinSmall (lo:=2236) (a:=34) (b:=35) sp2236 sp2270) (joinSmall (lo:=2305) (a:=35) (b:=35) sp2305 sp2340)) (joinSmall (lo:=2375) (a:=70) (b:=70) (joinSmall (lo:=2375) (a:=35) (b:=35) sp2375 sp2410) (joinSmall (lo:=2445) (a:=35) (b:=35) sp2445 sp2480))) (joinSmall (lo:=2515) (a:=140) (b:=140) (joinSmall (lo:=2515) (a:=70) (b:=70) (joinSmall (lo:=2515) (a:=35) (b:=35) sp2515 sp2550) (joinSmall (lo:=2585) (a:=35) (b:=35) sp2585 sp2620)) (joinSmall (lo:=2655) (a:=70) (b:=70) (joinSmall (lo:=2655) (a:=35) (b:=35) sp2655 sp2690) (joinSmall (lo:=2725) (a:=35) (b:=35) sp2725 sp2760)))) (joinSmall (lo:=2795) (a:=279) (b:=280) (joinSmall (lo:=2795) (a:=139) (b:=140) (joinSmall (lo:=2795) (a:=69) (b:=70) (joinSmall (lo:=2795) (a:=34) (b:=35) sp2795 sp2829) (joinSmall (lo:=2864) (a:=35) (b:=35) sp2864 sp2899)) (joinSmall (lo:=2934) (a:=70) (b:=70) (joinSmall (lo:=2934) (a:=35) (b:=35) sp2934 sp2969) (joinSmall (lo:=3004) (a:=35) (b:=35) sp3004 sp3039))) (joinSmall (lo:=3074) (a:=140) (b:=140) (joinSmall (lo:=3074) (a:=70) (b:=70) (joinSmall (lo:=3074) (a:=35) (b:=35) sp3074 sp3109) (joinSmall (lo:=3144) (a:=35) (b:=35) sp3144 sp3179)) (joinSmall (lo:=3214) (a:=70) (b:=70) (joinSmall (lo:=3214) (a:=35) (b:=35) sp3214 sp3249) (joinSmall (lo:=3284) (a:=35) (b:=35) sp3284 sp3319))))) (joinSmall (lo:=3354) (a:=559) (b:=559) (joinSmall (lo:=3354) (a:=279) (b:=280) (joinSmall (lo:=3354) (a:=139) (b:=140) (joinSmall (lo:=3354) (a:=69) (b:=70) (joinSmall (lo:=3354) (a:=34) (b:=35) sp3354 sp3388) (joinSmall (lo:=3423) (a:=35) (b:=35) sp3423 sp3458)) (joinSmall (lo:=3493) (a:=70) (b:=70) (joinSmall (lo:=3493) (a:=35) (b:=35) sp3493 sp3528) (joinSmall (lo:=3563) (a:=35) (b:=35) sp3563 sp3598))) (joinSmall (lo:=3633) (a:=140) (b:=140) (joinSmall (lo:=3633) (a:=70) (b:=70) (joinSmall (lo:=3633) (a:=35) (b:=35) sp3633 sp3668) (joinSmall (lo:=3703) (a:=35) (b:=35) sp3703 sp3738)) (joinSmall (lo:=3773) (a:=70) (b:=70) (joinSmall (lo:=3773) (a:=35) (b:=35) sp3773 sp3808) (joinSmall (lo:=3843) (a:=35) (b:=35) sp3843 sp3878)))) (joinSmall (lo:=3913) (a:=279) (b:=280) (joinSmall (lo:=3913) (a:=139) (b:=140) (joinSmall (lo:=3913) (a:=69) (b:=70) (joinSmall (lo:=3913) (a:=34) (b:=35) sp3913 sp3947) (joinSmall (lo:=3982) (a:=35) (b:=35) sp3982 sp4017)) (joinSmall (lo:=4052) (a:=70) (b:=70) (joinSmall (lo:=4052) (a:=35) (b:=35) sp4052 sp4087) (joinSmall (lo:=4122) (a:=35) (b:=35) sp4122 sp4157))) (joinSmall (lo:=4192) (a:=140) (b:=140) (joinSmall (lo:=4192) (a:=70) (b:=70) (joinSmall (lo:=4192) (a:=35) (b:=35) sp4192 sp4227) (joinSmall (lo:=4262) (a:=35) (b:=35) sp4262 sp4297)) (joinSmall (lo:=4332) (a:=70) (b:=70) (joinSmall (lo:=4332) (a:=35) (b:=35) sp4332 sp4367) (joinSmall (lo:=4402) (a:=35) (b:=35) sp4402 sp4437))))))) (joinSmall (lo:=4472) (a:=2236) (b:=2236) (joinSmall (lo:=4472) (a:=1118) (b:=1118) (joinSmall (lo:=4472) (a:=559) (b:=559) (joinSmall (lo:=4472) (a:=279) (b:=280) (joinSmall (lo:=4472) (a:=139) (b:=140) (joinSmall (lo:=4472) (a:=69) (b:=70) (joinSmall (lo:=4472) (a:=34) (b:=35) sp4472 sp4506) (joinSmall (lo:=4541) (a:=35) (b:=35) sp4541 sp4576)) (joinSmall (lo:=4611) (a:=70) (b:=70) (joinSmall (lo:=4611) (a:=35) (b:=35) sp4611 sp4646) (joinSmall (lo:=4681) (a:=35) (b:=35) sp4681 sp4716))) (joinSmall (lo:=4751) (a:=140) (b:=140) (joinSmall (lo:=4751) (a:=70) (b:=70) (joinSmall (lo:=4751) (a:=35) (b:=35) sp4751 sp4786) (joinSmall (lo:=4821) (a:=35) (b:=35) sp4821 sp4856)) (joinSmall (lo:=4891) (a:=70) (b:=70) (joinSmall (lo:=4891) (a:=35) (b:=35) sp4891 sp4926) (joinSmall (lo:=4961) (a:=35) (b:=35) sp4961 sp4996)))) (joinSmall (lo:=5031) (a:=279) (b:=280) (joinSmall (lo:=5031) (a:=139) (b:=140) (joinSmall (lo:=5031) (a:=69) (b:=70) (joinSmall (lo:=5031) (a:=34) (b:=35) sp5031 sp5065) (joinSmall (lo:=5100) (a:=35) (b:=35) sp5100 sp5135)) (joinSmall (lo:=5170) (a:=70) (b:=70) (joinSmall (lo:=5170) (a:=35) (b:=35) sp5170 sp5205) (joinSmall (lo:=5240) (a:=35) (b:=35) sp5240 sp5275))) (joinSmall (lo:=5310) (a:=140) (b:=140) (joinSmall (lo:=5310) (a:=70) (b:=70) (joinSmall (lo:=5310) (a:=35) (b:=35) sp5310 sp5345) (joinSmall (lo:=5380) (a:=35) (b:=35) sp5380 sp5415)) (joinSmall (lo:=5450) (a:=70) (b:=70) (joinSmall (lo:=5450) (a:=35) (b:=35) sp5450 sp5485) (joinSmall (lo:=5520) (a:=35) (b:=35) sp5520 sp5555))))) (joinSmall (lo:=5590) (a:=559) (b:=559) (joinSmall (lo:=5590) (a:=279) (b:=280) (joinSmall (lo:=5590) (a:=139) (b:=140) (joinSmall (lo:=5590) (a:=69) (b:=70) (joinSmall (lo:=5590) (a:=34) (b:=35) sp5590 sp5624) (joinSmall (lo:=5659) (a:=35) (b:=35) sp5659 sp5694)) (joinSmall (lo:=5729) (a:=70) (b:=70) (joinSmall (lo:=5729) (a:=35) (b:=35) sp5729 sp5764) (joinSmall (lo:=5799) (a:=35) (b:=35) sp5799 sp5834))) (joinSmall (lo:=5869) (a:=140) (b:=140) (joinSmall (lo:=5869) (a:=70) (b:=70) (joinSmall (lo:=5869) (a:=35) (b:=35) sp5869 sp5904) (joinSmall (lo:=5939) (a:=35) (b:=35) sp5939 sp5974)) (joinSmall (lo:=6009) (a:=70) (b:=70) (joinSmall (lo:=6009) (a:=35) (b:=35) sp6009 sp6044) (joinSmall (lo:=6079) (a:=35) (b:=35) sp6079 sp6114)))) (joinSmall (lo:=6149) (a:=279) (b:=280) (joinSmall (lo:=6149) (a:=139) (b:=140) (joinSmall (lo:=6149) (a:=69) (b:=70) (joinSmall (lo:=6149) (a:=34) (b:=35) sp6149 sp6183) (joinSmall (lo:=6218) (a:=35) (b:=35) sp6218 sp6253)) (joinSmall (lo:=6288) (a:=70) (b:=70) (joinSmall (lo:=6288) (a:=35) (b:=35) sp6288 sp6323) (joinSmall (lo:=6358) (a:=35) (b:=35) sp6358 sp6393))) (joinSmall (lo:=6428) (a:=140) (b:=140) (joinSmall (lo:=6428) (a:=70) (b:=70) (joinSmall (lo:=6428) (a:=35) (b:=35) sp6428 sp6463) (joinSmall (lo:=6498) (a:=35) (b:=35) sp6498 sp6533)) (joinSmall (lo:=6568) (a:=70) (b:=70) (joinSmall (lo:=6568) (a:=35) (b:=35) sp6568 sp6603) (joinSmall (lo:=6638) (a:=35) (b:=35) sp6638 sp6673)))))) (joinSmall (lo:=6708) (a:=1118) (b:=1118) (joinSmall (lo:=6708) (a:=559) (b:=559) (joinSmall (lo:=6708) (a:=279) (b:=280) (joinSmall (lo:=6708) (a:=139) (b:=140) (joinSmall (lo:=6708) (a:=69) (b:=70) (joinSmall (lo:=6708) (a:=34) (b:=35) sp6708 sp6742) (joinSmall (lo:=6777) (a:=35) (b:=35) sp6777 sp6812)) (joinSmall (lo:=6847) (a:=70) (b:=70) (joinSmall (lo:=6847) (a:=35) (b:=35) sp6847 sp6882) (joinSmall (lo:=6917) (a:=35) (b:=35) sp6917 sp6952))) (joinSmall (lo:=6987) (a:=140) (b:=140) (joinSmall (lo:=6987) (a:=70) (b:=70) (joinSmall (lo:=6987) (a:=35) (b:=35) sp6987 sp7022) (joinSmall (lo:=7057) (a:=35) (b:=35) sp7057 sp7092)) (joinSmall (lo:=7127) (a:=70) (b:=70) (joinSmall (lo:=7127) (a:=35) (b:=35) sp7127 sp7162) (joinSmall (lo:=7197) (a:=35) (b:=35) sp7197 sp7232)))) (joinSmall (lo:=7267) (a:=279) (b:=280) (joinSmall (lo:=7267) (a:=139) (b:=140) (joinSmall (lo:=7267) (a:=69) (b:=70) (joinSmall (lo:=7267) (a:=34) (b:=35) sp7267 sp7301) (joinSmall (lo:=7336) (a:=35) (b:=35) sp7336 sp7371)) (joinSmall (lo:=7406) (a:=70) (b:=70) (joinSmall (lo:=7406) (a:=35) (b:=35) sp7406 sp7441) (joinSmall (lo:=7476) (a:=35) (b:=35) sp7476 sp7511))) (joinSmall (lo:=7546) (a:=140) (b:=140) (joinSmall (lo:=7546) (a:=70) (b:=70) (joinSmall (lo:=7546) (a:=35) (b:=35) sp7546 sp7581) (joinSmall (lo:=7616) (a:=35) (b:=35) sp7616 sp7651)) (joinSmall (lo:=7686) (a:=70) (b:=70) (joinSmall (lo:=7686) (a:=35) (b:=35) sp7686 sp7721) (joinSmall (lo:=7756) (a:=35) (b:=35) sp7756 sp7791))))) (joinSmall (lo:=7826) (a:=559) (b:=559) (joinSmall (lo:=7826) (a:=279) (b:=280) (joinSmall (lo:=7826) (a:=139) (b:=140) (joinSmall (lo:=7826) (a:=69) (b:=70) (joinSmall (lo:=7826) (a:=34) (b:=35) sp7826 sp7860) (joinSmall (lo:=7895) (a:=35) (b:=35) sp7895 sp7930)) (joinSmall (lo:=7965) (a:=70) (b:=70) (joinSmall (lo:=7965) (a:=35) (b:=35) sp7965 sp8000) (joinSmall (lo:=8035) (a:=35) (b:=35) sp8035 sp8070))) (joinSmall (lo:=8105) (a:=140) (b:=140) (joinSmall (lo:=8105) (a:=70) (b:=70) (joinSmall (lo:=8105) (a:=35) (b:=35) sp8105 sp8140) (joinSmall (lo:=8175) (a:=35) (b:=35) sp8175 sp8210)) (joinSmall (lo:=8245) (a:=70) (b:=70) (joinSmall (lo:=8245) (a:=35) (b:=35) sp8245 sp8280) (joinSmall (lo:=8315) (a:=35) (b:=35) sp8315 sp8350)))) (joinSmall (lo:=8385) (a:=279) (b:=280) (joinSmall (lo:=8385) (a:=139) (b:=140) (joinSmall (lo:=8385) (a:=69) (b:=70) (joinSmall (lo:=8385) (a:=34) (b:=35) sp8385 sp8419) (joinSmall (lo:=8454) (a:=35) (b:=35) sp8454 sp8489)) (joinSmall (lo:=8524) (a:=70) (b:=70) (joinSmall (lo:=8524) (a:=35) (b:=35) sp8524 sp8559) (joinSmall (lo:=8594) (a:=35) (b:=35) sp8594 sp8629))) (joinSmall (lo:=8664) (a:=140) (b:=140) (joinSmall (lo:=8664) (a:=70) (b:=70) (joinSmall (lo:=8664) (a:=35) (b:=35) sp8664 sp8699) (joinSmall (lo:=8734) (a:=35) (b:=35) sp8734 sp8769)) (joinSmall (lo:=8804) (a:=70) (b:=70) (joinSmall (lo:=8804) (a:=35) (b:=35) sp8804 sp8839) (joinSmall (lo:=8874) (a:=35) (b:=35) sp8874 sp8909)))))))) (joinSmall (lo:=8944) (a:=4472) (b:=4473) (joinSmall (lo:=8944) (a:=2236) (b:=2236) (joinSmall (lo:=8944) (a:=1118) (b:=1118) (joinSmall (lo:=8944) (a:=559) (b:=559) (joinSmall (lo:=8944) (a:=279) (b:=280) (joinSmall (lo:=8944) (a:=139) (b:=140) (joinSmall (lo:=8944) (a:=69) (b:=70) (joinSmall (lo:=8944) (a:=34) (b:=35) sp8944 sp8978) (joinSmall (lo:=9013) (a:=35) (b:=35) sp9013 sp9048)) (joinSmall (lo:=9083) (a:=70) (b:=70) (joinSmall (lo:=9083) (a:=35) (b:=35) sp9083 sp9118) (joinSmall (lo:=9153) (a:=35) (b:=35) sp9153 sp9188))) (joinSmall (lo:=9223) (a:=140) (b:=140) (joinSmall (lo:=9223) (a:=70) (b:=70) (joinSmall (lo:=9223) (a:=35) (b:=35) sp9223 sp9258) (joinSmall (lo:=9293) (a:=35) (b:=35) sp9293 sp9328)) (joinSmall (lo:=9363) (a:=70) (b:=70) (joinSmall (lo:=9363) (a:=35) (b:=35) sp9363 sp9398) (joinSmall (lo:=9433) (a:=35) (b:=35) sp9433 sp9468)))) (joinSmall (lo:=9503) (a:=279) (b:=280) (joinSmall (lo:=9503) (a:=139) (b:=140) (joinSmall (lo:=9503) (a:=69) (b:=70) (joinSmall (lo:=9503) (a:=34) (b:=35) sp9503 sp9537) (joinSmall (lo:=9572) (a:=35) (b:=35) sp9572 sp9607)) (joinSmall (lo:=9642) (a:=70) (b:=70) (joinSmall (lo:=9642) (a:=35) (b:=35) sp9642 sp9677) (joinSmall (lo:=9712) (a:=35) (b:=35) sp9712 sp9747))) (joinSmall (lo:=9782) (a:=140) (b:=140) (joinSmall (lo:=9782) (a:=70) (b:=70) (joinSmall (lo:=9782) (a:=35) (b:=35) sp9782 sp9817) (joinSmall (lo:=9852) (a:=35) (b:=35) sp9852 sp9887)) (joinSmall (lo:=9922) (a:=70) (b:=70) (joinSmall (lo:=9922) (a:=35) (b:=35) sp9922 sp9957) (joinSmall (lo:=9992) (a:=35) (b:=35) sp9992 sp10027))))) (joinSmall (lo:=10062) (a:=559) (b:=559) (joinSmall (lo:=10062) (a:=279) (b:=280) (joinSmall (lo:=10062) (a:=139) (b:=140) (joinSmall (lo:=10062) (a:=69) (b:=70) (joinSmall (lo:=10062) (a:=34) (b:=35) sp10062 sp10096) (joinSmall (lo:=10131) (a:=35) (b:=35) sp10131 sp10166)) (joinSmall (lo:=10201) (a:=70) (b:=70) (joinSmall (lo:=10201) (a:=35) (b:=35) sp10201 sp10236) (joinSmall (lo:=10271) (a:=35) (b:=35) sp10271 sp10306))) (joinSmall (lo:=10341) (a:=140) (b:=140) (joinSmall (lo:=10341) (a:=70) (b:=70) (joinSmall (lo:=10341) (a:=35) (b:=35) sp10341 sp10376) (joinSmall (lo:=10411) (a:=35) (b:=35) sp10411 sp10446)) (joinSmall (lo:=10481) (a:=70) (b:=70) (joinSmall (lo:=10481) (a:=35) (b:=35) sp10481 sp10516) (joinSmall (lo:=10551) (a:=35) (b:=35) sp10551 sp10586)))) (joinSmall (lo:=10621) (a:=279) (b:=280) (joinSmall (lo:=10621) (a:=139) (b:=140) (joinSmall (lo:=10621) (a:=69) (b:=70) (joinSmall (lo:=10621) (a:=34) (b:=35) sp10621 sp10655) (joinSmall (lo:=10690) (a:=35) (b:=35) sp10690 sp10725)) (joinSmall (lo:=10760) (a:=70) (b:=70) (joinSmall (lo:=10760) (a:=35) (b:=35) sp10760 sp10795) (joinSmall (lo:=10830) (a:=35) (b:=35) sp10830 sp10865))) (joinSmall (lo:=10900) (a:=140) (b:=140) (joinSmall (lo:=10900) (a:=70) (b:=70) (joinSmall (lo:=10900) (a:=35) (b:=35) sp10900 sp10935) (joinSmall (lo:=10970) (a:=35) (b:=35) sp10970 sp11005)) (joinSmall (lo:=11040) (a:=70) (b:=70) (joinSmall (lo:=11040) (a:=35) (b:=35) sp11040 sp11075) (joinSmall (lo:=11110) (a:=35) (b:=35) sp11110 sp11145)))))) (joinSmall (lo:=11180) (a:=1118) (b:=1118) (joinSmall (lo:=11180) (a:=559) (b:=559) (joinSmall (lo:=11180) (a:=279) (b:=280) (joinSmall (lo:=11180) (a:=139) (b:=140) (joinSmall (lo:=11180) (a:=69) (b:=70) (joinSmall (lo:=11180) (a:=34) (b:=35) sp11180 sp11214) (joinSmall (lo:=11249) (a:=35) (b:=35) sp11249 sp11284)) (joinSmall (lo:=11319) (a:=70) (b:=70) (joinSmall (lo:=11319) (a:=35) (b:=35) sp11319 sp11354) (joinSmall (lo:=11389) (a:=35) (b:=35) sp11389 sp11424))) (joinSmall (lo:=11459) (a:=140) (b:=140) (joinSmall (lo:=11459) (a:=70) (b:=70) (joinSmall (lo:=11459) (a:=35) (b:=35) sp11459 sp11494) (joinSmall (lo:=11529) (a:=35) (b:=35) sp11529 sp11564)) (joinSmall (lo:=11599) (a:=70) (b:=70) (joinSmall (lo:=11599) (a:=35) (b:=35) sp11599 sp11634) (joinSmall (lo:=11669) (a:=35) (b:=35) sp11669 sp11704)))) (joinSmall (lo:=11739) (a:=279) (b:=280) (joinSmall (lo:=11739) (a:=139) (b:=140) (joinSmall (lo:=11739) (a:=69) (b:=70) (joinSmall (lo:=11739) (a:=34) (b:=35) sp11739 sp11773) (joinSmall (lo:=11808) (a:=35) (b:=35) sp11808 sp11843)) (joinSmall (lo:=11878) (a:=70) (b:=70) (joinSmall (lo:=11878) (a:=35) (b:=35) sp11878 sp11913) (joinSmall (lo:=11948) (a:=35) (b:=35) sp11948 sp11983))) (joinSmall (lo:=12018) (a:=140) (b:=140) (joinSmall (lo:=12018) (a:=70) (b:=70) (joinSmall (lo:=12018) (a:=35) (b:=35) sp12018 sp12053) (joinSmall (lo:=12088) (a:=35) (b:=35) sp12088 sp12123)) (joinSmall (lo:=12158) (a:=70) (b:=70) (joinSmall (lo:=12158) (a:=35) (b:=35) sp12158 sp12193) (joinSmall (lo:=12228) (a:=35) (b:=35) sp12228 sp12263))))) (joinSmall (lo:=12298) (a:=559) (b:=559) (joinSmall (lo:=12298) (a:=279) (b:=280) (joinSmall (lo:=12298) (a:=139) (b:=140) (joinSmall (lo:=12298) (a:=69) (b:=70) (joinSmall (lo:=12298) (a:=34) (b:=35) sp12298 sp12332) (joinSmall (lo:=12367) (a:=35) (b:=35) sp12367 sp12402)) (joinSmall (lo:=12437) (a:=70) (b:=70) (joinSmall (lo:=12437) (a:=35) (b:=35) sp12437 sp12472) (joinSmall (lo:=12507) (a:=35) (b:=35) sp12507 sp12542))) (joinSmall (lo:=12577) (a:=140) (b:=140) (joinSmall (lo:=12577) (a:=70) (b:=70) (joinSmall (lo:=12577) (a:=35) (b:=35) sp12577 sp12612) (joinSmall (lo:=12647) (a:=35) (b:=35) sp12647 sp12682)) (joinSmall (lo:=12717) (a:=70) (b:=70) (joinSmall (lo:=12717) (a:=35) (b:=35) sp12717 sp12752) (joinSmall (lo:=12787) (a:=35) (b:=35) sp12787 sp12822)))) (joinSmall (lo:=12857) (a:=279) (b:=280) (joinSmall (lo:=12857) (a:=139) (b:=140) (joinSmall (lo:=12857) (a:=69) (b:=70) (joinSmall (lo:=12857) (a:=34) (b:=35) sp12857 sp12891) (joinSmall (lo:=12926) (a:=35) (b:=35) sp12926 sp12961)) (joinSmall (lo:=12996) (a:=70) (b:=70) (joinSmall (lo:=12996) (a:=35) (b:=35) sp12996 sp13031) (joinSmall (lo:=13066) (a:=35) (b:=35) sp13066 sp13101))) (joinSmall (lo:=13136) (a:=140) (b:=140) (joinSmall (lo:=13136) (a:=70) (b:=70) (joinSmall (lo:=13136) (a:=35) (b:=35) sp13136 sp13171) (joinSmall (lo:=13206) (a:=35) (b:=35) sp13206 sp13241)) (joinSmall (lo:=13276) (a:=70) (b:=70) (joinSmall (lo:=13276) (a:=35) (b:=35) sp13276 sp13311) (joinSmall (lo:=13346) (a:=35) (b:=35) sp13346 sp13381))))))) (joinSmall (lo:=13416) (a:=2236) (b:=2237) (joinSmall (lo:=13416) (a:=1118) (b:=1118) (joinSmall (lo:=13416) (a:=559) (b:=559) (joinSmall (lo:=13416) (a:=279) (b:=280) (joinSmall (lo:=13416) (a:=139) (b:=140) (joinSmall (lo:=13416) (a:=69) (b:=70) (joinSmall (lo:=13416) (a:=34) (b:=35) sp13416 sp13450) (joinSmall (lo:=13485) (a:=35) (b:=35) sp13485 sp13520)) (joinSmall (lo:=13555) (a:=70) (b:=70) (joinSmall (lo:=13555) (a:=35) (b:=35) sp13555 sp13590) (joinSmall (lo:=13625) (a:=35) (b:=35) sp13625 sp13660))) (joinSmall (lo:=13695) (a:=140) (b:=140) (joinSmall (lo:=13695) (a:=70) (b:=70) (joinSmall (lo:=13695) (a:=35) (b:=35) sp13695 sp13730) (joinSmall (lo:=13765) (a:=35) (b:=35) sp13765 sp13800)) (joinSmall (lo:=13835) (a:=70) (b:=70) (joinSmall (lo:=13835) (a:=35) (b:=35) sp13835 sp13870) (joinSmall (lo:=13905) (a:=35) (b:=35) sp13905 sp13940)))) (joinSmall (lo:=13975) (a:=279) (b:=280) (joinSmall (lo:=13975) (a:=139) (b:=140) (joinSmall (lo:=13975) (a:=69) (b:=70) (joinSmall (lo:=13975) (a:=34) (b:=35) sp13975 sp14009) (joinSmall (lo:=14044) (a:=35) (b:=35) sp14044 sp14079)) (joinSmall (lo:=14114) (a:=70) (b:=70) (joinSmall (lo:=14114) (a:=35) (b:=35) sp14114 sp14149) (joinSmall (lo:=14184) (a:=35) (b:=35) sp14184 sp14219))) (joinSmall (lo:=14254) (a:=140) (b:=140) (joinSmall (lo:=14254) (a:=70) (b:=70) (joinSmall (lo:=14254) (a:=35) (b:=35) sp14254 sp14289) (joinSmall (lo:=14324) (a:=35) (b:=35) sp14324 sp14359)) (joinSmall (lo:=14394) (a:=70) (b:=70) (joinSmall (lo:=14394) (a:=35) (b:=35) sp14394 sp14429) (joinSmall (lo:=14464) (a:=35) (b:=35) sp14464 sp14499))))) (joinSmall (lo:=14534) (a:=559) (b:=559) (joinSmall (lo:=14534) (a:=279) (b:=280) (joinSmall (lo:=14534) (a:=139) (b:=140) (joinSmall (lo:=14534) (a:=69) (b:=70) (joinSmall (lo:=14534) (a:=34) (b:=35) sp14534 sp14568) (joinSmall (lo:=14603) (a:=35) (b:=35) sp14603 sp14638)) (joinSmall (lo:=14673) (a:=70) (b:=70) (joinSmall (lo:=14673) (a:=35) (b:=35) sp14673 sp14708) (joinSmall (lo:=14743) (a:=35) (b:=35) sp14743 sp14778))) (joinSmall (lo:=14813) (a:=140) (b:=140) (joinSmall (lo:=14813) (a:=70) (b:=70) (joinSmall (lo:=14813) (a:=35) (b:=35) sp14813 sp14848) (joinSmall (lo:=14883) (a:=35) (b:=35) sp14883 sp14918)) (joinSmall (lo:=14953) (a:=70) (b:=70) (joinSmall (lo:=14953) (a:=35) (b:=35) sp14953 sp14988) (joinSmall (lo:=15023) (a:=35) (b:=35) sp15023 sp15058)))) (joinSmall (lo:=15093) (a:=279) (b:=280) (joinSmall (lo:=15093) (a:=139) (b:=140) (joinSmall (lo:=15093) (a:=69) (b:=70) (joinSmall (lo:=15093) (a:=34) (b:=35) sp15093 sp15127) (joinSmall (lo:=15162) (a:=35) (b:=35) sp15162 sp15197)) (joinSmall (lo:=15232) (a:=70) (b:=70) (joinSmall (lo:=15232) (a:=35) (b:=35) sp15232 sp15267) (joinSmall (lo:=15302) (a:=35) (b:=35) sp15302 sp15337))) (joinSmall (lo:=15372) (a:=140) (b:=140) (joinSmall (lo:=15372) (a:=70) (b:=70) (joinSmall (lo:=15372) (a:=35) (b:=35) sp15372 sp15407) (joinSmall (lo:=15442) (a:=35) (b:=35) sp15442 sp15477)) (joinSmall (lo:=15512) (a:=70) (b:=70) (joinSmall (lo:=15512) (a:=35) (b:=35) sp15512 sp15547) (joinSmall (lo:=15582) (a:=35) (b:=35) sp15582 sp15617)))))) (joinSmall (lo:=15652) (a:=1118) (b:=1119) (joinSmall (lo:=15652) (a:=559) (b:=559) (joinSmall (lo:=15652) (a:=279) (b:=280) (joinSmall (lo:=15652) (a:=139) (b:=140) (joinSmall (lo:=15652) (a:=69) (b:=70) (joinSmall (lo:=15652) (a:=34) (b:=35) sp15652 sp15686) (joinSmall (lo:=15721) (a:=35) (b:=35) sp15721 sp15756)) (joinSmall (lo:=15791) (a:=70) (b:=70) (joinSmall (lo:=15791) (a:=35) (b:=35) sp15791 sp15826) (joinSmall (lo:=15861) (a:=35) (b:=35) sp15861 sp15896))) (joinSmall (lo:=15931) (a:=140) (b:=140) (joinSmall (lo:=15931) (a:=70) (b:=70) (joinSmall (lo:=15931) (a:=35) (b:=35) sp15931 sp15966) (joinSmall (lo:=16001) (a:=35) (b:=35) sp16001 sp16036)) (joinSmall (lo:=16071) (a:=70) (b:=70) (joinSmall (lo:=16071) (a:=35) (b:=35) sp16071 sp16106) (joinSmall (lo:=16141) (a:=35) (b:=35) sp16141 sp16176)))) (joinSmall (lo:=16211) (a:=279) (b:=280) (joinSmall (lo:=16211) (a:=139) (b:=140) (joinSmall (lo:=16211) (a:=69) (b:=70) (joinSmall (lo:=16211) (a:=34) (b:=35) sp16211 sp16245) (joinSmall (lo:=16280) (a:=35) (b:=35) sp16280 sp16315)) (joinSmall (lo:=16350) (a:=70) (b:=70) (joinSmall (lo:=16350) (a:=35) (b:=35) sp16350 sp16385) (joinSmall (lo:=16420) (a:=35) (b:=35) sp16420 sp16455))) (joinSmall (lo:=16490) (a:=140) (b:=140) (joinSmall (lo:=16490) (a:=70) (b:=70) (joinSmall (lo:=16490) (a:=35) (b:=35) sp16490 sp16525) (joinSmall (lo:=16560) (a:=35) (b:=35) sp16560 sp16595)) (joinSmall (lo:=16630) (a:=70) (b:=70) (joinSmall (lo:=16630) (a:=35) (b:=35) sp16630 sp16665) (joinSmall (lo:=16700) (a:=35) (b:=35) sp16700 sp16735))))) (joinSmall (lo:=16770) (a:=559) (b:=560) (joinSmall (lo:=16770) (a:=279) (b:=280) (joinSmall (lo:=16770) (a:=139) (b:=140) (joinSmall (lo:=16770) (a:=69) (b:=70) (joinSmall (lo:=16770) (a:=34) (b:=35) sp16770 sp16804) (joinSmall (lo:=16839) (a:=35) (b:=35) sp16839 sp16874)) (joinSmall (lo:=16909) (a:=70) (b:=70) (joinSmall (lo:=16909) (a:=35) (b:=35) sp16909 sp16944) (joinSmall (lo:=16979) (a:=35) (b:=35) sp16979 sp17014))) (joinSmall (lo:=17049) (a:=140) (b:=140) (joinSmall (lo:=17049) (a:=70) (b:=70) (joinSmall (lo:=17049) (a:=35) (b:=35) sp17049 sp17084) (joinSmall (lo:=17119) (a:=35) (b:=35) sp17119 sp17154)) (joinSmall (lo:=17189) (a:=70) (b:=70) (joinSmall (lo:=17189) (a:=35) (b:=35) sp17189 sp17224) (joinSmall (lo:=17259) (a:=35) (b:=35) sp17259 sp17294)))) (joinSmall (lo:=17329) (a:=280) (b:=280) (joinSmall (lo:=17329) (a:=140) (b:=140) (joinSmall (lo:=17329) (a:=70) (b:=70) (joinSmall (lo:=17329) (a:=35) (b:=35) sp17329 sp17364) (joinSmall (lo:=17399) (a:=35) (b:=35) sp17399 sp17434)) (joinSmall (lo:=17469) (a:=70) (b:=70) (joinSmall (lo:=17469) (a:=35) (b:=35) sp17469 sp17504) (joinSmall (lo:=17539) (a:=35) (b:=35) sp17539 sp17574))) (joinSmall (lo:=17609) (a:=140) (b:=140) (joinSmall (lo:=17609) (a:=70) (b:=70) (joinSmall (lo:=17609) (a:=35) (b:=35) sp17609 sp17644) (joinSmall (lo:=17679) (a:=35) (b:=35) sp17679 sp17714)) (joinSmall (lo:=17749) (a:=70) (b:=70) (joinSmall (lo:=17749) (a:=35) (b:=35) sp17749 sp17784) (joinSmall (lo:=17819) (a:=35) (b:=35) sp17819 sp17854)))))))))
  have good : (List.range 17889).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 320000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 17888 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 17888 := by
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


private def packet (i : ℕ) : ℕ := (if i < 81 then (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 0))) else (if i < 7 then (if i < 6 then 0 else 0) else (if i < 8 then 0 else (if i < 9 then 0 else 0)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0 else 0) else (if i < 13 then 0 else (if i < 14 then 0 else 0))) else (if i < 17 then (if i < 16 then 0 else 0) else (if i < 18 then 0 else (if i < 19 then 0 else 0))))) else (if i < 30 then (if i < 25 then (if i < 22 then (if i < 21 then 0 else 0) else (if i < 23 then 0 else (if i < 24 then 0 else 0))) else (if i < 27 then (if i < 26 then 0 else 0) else (if i < 28 then 0 else (if i < 29 then 0 else 0)))) else (if i < 35 then (if i < 32 then (if i < 31 then 0 else 0) else (if i < 33 then 0 else (if i < 34 then 0 else 0))) else (if i < 37 then (if i < 36 then 0 else 0) else (if i < 38 then 0 else (if i < 39 then 0 else 0)))))) else (if i < 60 then (if i < 50 then (if i < 45 then (if i < 42 then (if i < 41 then 0 else 0) else (if i < 43 then 0 else (if i < 44 then 0 else 0))) else (if i < 47 then (if i < 46 then 0 else 0) else (if i < 48 then 0 else (if i < 49 then 0 else 0)))) else (if i < 55 then (if i < 52 then (if i < 51 then 0 else 0) else (if i < 53 then 0 else (if i < 54 then 0 else 0))) else (if i < 57 then (if i < 56 then 0 else 0) else (if i < 58 then 0 else (if i < 59 then 0 else 0))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then 0 else 0) else (if i < 63 then 0 else (if i < 64 then 0 else 0))) else (if i < 67 then (if i < 66 then 0 else 0) else (if i < 68 then 0 else (if i < 69 then 0 else 0)))) else (if i < 75 then (if i < 72 then (if i < 71 then 0 else 0) else (if i < 73 then 0 else (if i < 74 then 0 else 0))) else (if i < 78 then (if i < 76 then 0 else (if i < 77 then 0 else 0)) else (if i < 79 then 0 else (if i < 80 then 0 else 0))))))) else (if i < 122 then (if i < 101 then (if i < 91 then (if i < 86 then (if i < 83 then (if i < 82 then 0 else 0) else (if i < 84 then 0 else (if i < 85 then 0 else 0))) else (if i < 88 then (if i < 87 then 0 else 0) else (if i < 89 then 0 else (if i < 90 then 0 else 0)))) else (if i < 96 then (if i < 93 then (if i < 92 then 0 else 0) else (if i < 94 then 0 else (if i < 95 then 0 else 0))) else (if i < 98 then (if i < 97 then 0 else 0) else (if i < 99 then 0 else (if i < 100 then 0 else 0))))) else (if i < 111 then (if i < 106 then (if i < 103 then (if i < 102 then 0 else 0) else (if i < 104 then 0 else (if i < 105 then 0 else 0))) else (if i < 108 then (if i < 107 then 0 else 0) else (if i < 109 then 0 else (if i < 110 then 0 else 0)))) else (if i < 116 then (if i < 113 then (if i < 112 then 0 else 0) else (if i < 114 then 0 else (if i < 115 then 0 else 0))) else (if i < 119 then (if i < 117 then 0 else (if i < 118 then 0 else 0)) else (if i < 120 then 0 else (if i < 121 then 0 else 0)))))) else (if i < 142 then (if i < 132 then (if i < 127 then (if i < 124 then (if i < 123 then 0 else 0) else (if i < 125 then 0 else (if i < 126 then 0 else 0))) else (if i < 129 then (if i < 128 then 0 else 0) else (if i < 130 then 0 else (if i < 131 then 0 else 0)))) else (if i < 137 then (if i < 134 then (if i < 133 then 0 else 0) else (if i < 135 then 0 else (if i < 136 then 0 else 0))) else (if i < 139 then (if i < 138 then 0 else 0) else (if i < 140 then 0 else (if i < 141 then 0 else 0))))) else (if i < 152 then (if i < 147 then (if i < 144 then (if i < 143 then 0 else 0) else (if i < 145 then 0 else (if i < 146 then 0 else 0))) else (if i < 149 then (if i < 148 then 0 else 0) else (if i < 150 then 0 else (if i < 151 then 0xf586982e095449ea48b20e8ef46d230615208f43ae17d08d02f40c800000f5809d2cf94f09d04852110ef46b62f914c08d43b617d09403140d000000f57a8b2d615449f048c2108f0c6d230c14f88e03a417508982fc0c000000f5744a2eb15e0a1e4af2270fac70430e159891c3c418209003100c000000f56e282e415689f24a02230f906e230415008f43be176093030c0be00000f568162da95249f048f2160f206c430014f08ec3cc18f09203140bc00000f561f02dd15609fc4912178f146ce30c15489183d418a09583200c000000f55bbd2ea15b8a1649e21b0f586de30b15809383da18309402f40aa00000f5559a2e3958ca044a72208f6c70a31c15e89883f419a099031c0d000000f54f5d2ed15f8a1e4ad2260fac722325162095c3d418d09502f80c600000f5494b2d715109d04842148f186c630714c08d03a817208d82ec0be00000f5431b2e615749f249b2148f3c6d230214c88f03b418609283380d000000f53ced2e395a4a0e4a12190f506c82ff15409103ba18309703300ce00000f536e72cd94d09b247a20b8f0c6ca30814d89003b618509283100cc00000f530b02eb15c8a224af2200f7c6f632115a892c3f819c09483100ce00000f52a742e595eca284ae2218f6c6e831915b09583d418e09302fc0be00000f524572d895449e048e2120f246c030015008f43c0186090831c0d000000f51e1f2ec15d8a224a82248fbc70832a16189703f6192097831c0d800000f517d72f49618a3a4b62250f8070032115789503ea19409803480d800000f511b92dd95509dc48d2120f286d031b160095c3c018309703380c200000f50b932e095689ee4972170f206d230a14e89103c218308e03100bc00000f505682e495bc9fe4a82248fac71031e15f89883fc19c09a034c0d400000f4ff3c2e795cca204b12290fcc72a32415e09603d819209103200c800000f4f9062ec1604a1e4a82278fc472632c16589a03f419709b83400cc00000f4f2ec2e015b4a1a49f2188f446e8314160097c3ea19509783480ce00000f4ecd82d415289c64812138f346e231215b09483ea19509683140ca00000f4e6a02f095d0a2c4ae2290fbc70831e160897840219f096032c0d600000f4e07c2e315b4a204ab2258fbc72433216389783d2185092831c0d000000f4da2f2f41600a404b221f0f8c70031015889403e818509103180ba00000f4d3f92e2959ca184a82240f886fa31e15589183c417f08982dc0b800000f4cde52d695509e44842148f586da30e15009203c6182095031c0c000000f4c7bf2e595c8a224aa2228f9070631715b89143ba17d09102f40ba00000f4c1c02d395049ca47e2120ef46c830414f89083c018708f82fc0b600000f4bbad2db95209d047d2118ed46ae2fc14c89103c818809303100c800000f4b5812e51598a064ab21f8f786e230d15589083c618f095830c0b800000f4af212fa960ca464c322f8fec72632c162099c41e1b00a683740dc00000f4a8fd2df95549d84922140f386d430015008e43b418008c02c40b400000f4a2dd2e19594a0849f21e8f8070032c16289783f818d093030c0ce00000f49cdc2cd94e09ac47d20e0f086ca30215008fc3c018209302f80ba00000f496ca2da95589d649521c0f746f831a15b89603c017f09183300d200000f490622fd163ca444c522a8fb471632b15e89483f419909a03300da00000f48a422e31590a0849921f8f486f431415889303be17d08f032c0e000000f484192e815e0a1e4ae2278f7c71c32615f89743dc18709483240c400000f47e092d2950c9c84932190f486d4304155094c3e819a09303100c400000f477b92fa164ca684d223b904075a33d16509a040a1aa0a183480ce00000f471b72ca94e89c24762050ea86902e1145889039c17108982bc0a400000f46b912e295789f64872148f306ce2ff14e88fc3ce18908c030c0d000000f465842d615109c84882100efc6c4308150092c3dc18c09503040bc00000f45f542e21588a004a32240fb46f431c15a892c3d018109582fc0ba00000f4591f2ef15f0a1449f2220f7c6fe316158895c3ec19909703100c200000f452e82e5958ca044a021e0f6871232c16489803ec19509783300c000000f44cc62dc1598a0e4a121d8f806f831315889343be18609903640cc00000f446a12de15609d248120e8ef46c830a15108ec3ae17908c82b40ac00000f440812e21578a0a4a121c0f246c430515309403e818008f02c80b200000f43a742d5953c9e249e21a8f3c6f831615709383c817b09183240c400000f434512e115689ee49421a0f646e031615e09403ce18b09583040ba00000f42e452d395549c248320f8eec6c230214d08e03a416d08602c40c400000f4282b2da95349e04832118ed46b02fa14e09183cc18c09183040c800000f4220c2db95749ec4992188f406ec30d15809583e6191096831c0c600000f41c142cb94cc9ae4722100efc6b22f615189103c218b09503240c600000f416082db15709fc4972170f486e230915088e83a417308c82f40b400000f40fe82de15489dc4852158f186de30a158090c3ba17f08f82e80ae00000f409e42cc94cc9be47f20b8ebc6982f614b09203de18909583080bc00000f4038b2fb165ca5a4cd230900472c33a16689943f219209383040b6000 else 0xf7101a2c794bc9984652010e906802e914508b83a217908802dc0b400000f709f92de95709e24912168f246ba2fa15009143c817a08902bc0b000000f703aa2f5162ca3a4b321e8f7470a32716289743e618e09883140c400000f6fdbe2c694c499e47620e8ed46ac2fb14d89043d418608f83140d200000f6f76d2f79604a3e4c1233901874433e16809c040419e09f03740ca00000f6f1822ca94bc98e46e2040ec06942ec14a88e43ae17808c02f40cc00000f6eb862d595389cc48b2148f186c430415009003b017708f030c0c000000f6e55d2e39598a144982158f346f231215509183ac17c08b02d80bc00000f6df662ca94d098846d20b0ea86902f314a88e83c018108e03100c400000f6d9342e295949ee49321c8f74710328161097440219008f82e80c400000f6d3062e41594a0e4aa2220f646f030a152892c3d2190097031c0c600000f6ccdf2e0155c9e449421a0f506d031015909183d418608f03080ae00000f6c6bc2e2956c9fc4962148f006aa2fc14c88f43b818108f02e00c200000f6c0842ea15c4a1a4af2240f8c70831d15c89583ec18c09683300c200000f6ba592e595a8a284b42280f8c71432116109ac40a19009803600d400000f6b4272ed15cca1e4af2248f8870032316109783f218009302f80ba00000f6addd2f315eca464bd22e100c72c32f16609b03fe19c09a03580da00000f6a7b02e4958c9fe4a621e0f706e032615f09343d018108d03300c400000f6a15f2fa1630a444bc22b0fa470032316009783f018e09583140ba00000f69b622cd951c9d048720b8edc6ac2e514688a039617308302900a200000f695442d995489e048d2108f006c430d15489183d618c09603400d000000f68f342d795749ee48e21a0f406dc30a15489343de18508f03000b800000f689102df95789f64a02238fc06f231515a895c3da18009083340d200000f683002d595209d04802170f206d630014b88e43ba18008f031c0cc00000f67ce92da95209e64812100f2c6c030415008e83b217608782dc0ae00000f676d82da15389d64872100ee46b22f314888a839c16f08582dc0b600000f670b12e1158c9fe4922178f246dc30415388e43b217b08a82e40b400000f66a752ed95d0a0e49e21d8f9871c32715e09503ee19009302f40bc00000f664452e01590a024ab2220f8c6e630a15189243d218609282dc0b000000f65e062ee95d4a304b32248f7470431815909343e418f09583380da00000f657bb2f115e4a2c4b32278fcc6fe31415809383b617408d83000ba00000f651802eb15cca164972170f146c830115809403cc18209283380c600000f64b6e2d695409e44862168f586d030f15909283d218909503200d800000f645402e415a89fe4992210f686e831515889283d018208d02ec0c000000f63f312de15489e44972208f606f631515d09503e419509903340d000000f638e22f7162ca5a4d823a900873033616709943f218f09a03240c600000f632af2e695989fc4922158f4c6f431515889183c617d09102f40bc00000f62c862e415b4a0c4a62248f7470632516209a040a19b09d03480ce00000f6266f2de15409d849021a8f246ea31315a09643fe19409503280cc00000f6204e2dc15549ea4962198f586da312155893c3ce18b09482f00bc00000f61a242e015809e649f21a8f406e830915389043dc18e09983480cc00000f614082dc15549da4842110f186d630915a095c3f218c096832c0be00000f60dd72e315789f84902100ef06d430e15889443dc19109a035c0de00000f607da2cd15089c647520a0ea869e2f414408843a217408782d80ba00000f6019d2e695bca164b32278f946fe31615c89983f018f09783340e000000f5fb9e2d515489ce48a2138f306d830715208d439017408f02f80c200000f5f5992d114f89aa47720a0edc6b62f414988cc3a817508d82f40b000000f5ef752df958c9fa4a021e0f4c6f2313157891c3da190095032c0cc00000f5e9512df155c9dc48e2128ef86d830c15a89683c616f08582f00ae00000f5e32c2e31590a0e4a72270fc870031b15e893c3e418e094830c0d000000f5dd0c2e1159ca0049f21e8f846de30a15509203d617e09303340ae00000f5d6c22f31600a2a4aa2238f946fe31615089243dc19109503280c000000f5d0712f91600a3e4ac2218f706ee31815d0954402197099832c0b800000f5ca252f79630a424ad2260fc871e32d15f09603e419509783380cc00000f5c4142d915049b247120b8ee46a62f014a88c83a017a08a82fc0c000000f5bdeb2e09594a044a52238f846f430c158895c3e618f096832c0c400000f5b7d62d915289e649421c0f4c6de31315309103c218609782f80b000000f5b1962f11610a3c4b82260fbc71e32f16389803f419a09d03140ba00000f5ab6d2e995c4a0849e21b8f586d82fc14e08e03b617a08b82f00c600000f5a5542de1598a1249a21f0f7070031615689303c818e09583140c800000f59f142f11610a344b52220fac71232f168899c40a19d09c83600de00000f599032dd1574a024952178f146c630814f88bc3b418108b02f40bc00000f592d92e715dca3a4ba22f8fbc7043291660990402190099033c0de00000f58cb92e215b4a0c4982170f5c6e630315208fc3c217c08e02c80ae000)))) else (if i < 157 then (if i < 154 then (if i < 153 then 0xf899ad2ef15dca2c4af22f8fdc72c32d16409c840e1ad0a483480e400000f8937b2ea95aca144ab2248f886f0313157891c3d618d09603180b800000f88d572df157c9f24922150f046dc31115b89643da18909002e80ae00000f887422da15309e649221d8f546ee31715c09643f8197098032c0be00000f8811f2e515689f449321e0f6c6fa31b15b89683ee18f09403000cc00000f87b142d795349dc48e2140f386d630615008f03b018409002ec0ac00000f874e02e1156c9e64932138f286cc30d15889143c618509002e80bc00000f86ec42d7954c9f649d21d8f906fe31915a09043c218509302fc0d200000f868912e7959c9f449421b8f586e031915f09783e218c09602e80b600000f8626a2de95589dc48e2100ed86a62f314c88f03ce18108d83000ca00000f85c542d995309dc48320d8f186ca306156891c3c618308f02f40b600000f856342e095709fe4a521d8f506de2fd15009283cc18309503100be00000f84ffd2e39590a0849d21e8f486da30c15b09583e218808c82d40b600000f849c32eb1598a064a92230f806fc31915308f83cc18809502f00a800000f843922e595a4a204ae2270f84700311155090c3a417808a02bc0a600000f83d612e51590a0649721d0f406d6311154890c3bc18008d82f80b400000f837662cf952c9dc4862110f246c831115489243dc19109403180d000000f831422e615d8a224a92240fc071c332166899440219f09d83300de00000f82b182de15649d448a2180f3c6e631a15a893c3e218809203100d000000f824d62f2961ca2c4b22268fa472433116689a440218e09803240ce00000f81ea92e61580a1a49e2220f6c6f031115809243ca18108f03280c600000f818802dd15749dc48d20d0ee06b02fa14908dc39c17c098830c0be00000f812912c814cc99c46c20b0ee06ae2f914e091c3c618909102f00c200000f80c562ee95eca2c4b722a8fc472c32c162899c3fc18e094831c0ca00000f806332e115689fa4a021c8f6870631a15b09583d418b094833c0d000000f7fff72ec95cca244a92220f60704325160898440019609c83700e000000f7f9f42d314f49c04752078eb86982ef14488d43bc17a094830c0ca00000f7f3b02f715f0a2c4ad21c0f8070632216589d040a19909783340c200000f7ed6f2f195eca284b02210f9c6ec316159894c3e418f09403440ce00000f7e75b2d795389d248120f0ee86c22fb15789303c818c09a03440d800000f7e12b2e815cca264b92260f9c6fe32415d09443e419409b83400e000000f7db1c2d795689fe49721c0f306be2ff15309143d0187092030c0be00000f7d4ed2e395709fe4a221b8f646f031815f89743f419909b03400d000000f7ce952ff167ca724d7237901c73433515f89983fa19609783280de00000f7c8652e215809fa49c2210f8870031a15589283d618309503180b200000f7c22e2e695a4a0a4a82240f9470032516289303da18a09783100ca00000f7bbff2e795a0a124a021d0f9470431a15a09343d617f09503100d000000f7b5e42da95889f049a2190f2c6ce30d155891c3d418b08e02e80b200000f7afd12db95589ea4952180f4c6d0305150090c3d818a097032c0ce00000f7a9b82d715509ea48d21d8f646e830c15889603fa19d09a03240b200000f7a3812ed1620a564c82300fec71233016109883e218b09403080b600000f79d5c2df9584a064922160f386e631815709543dc17e09283000bc00000f797612ce951c9be47d20d0ef06c02fe15009003d619409b032c0c400000f7910d2fb9640a6a4c722f900073c33215d89483ea18d098831c0d800000f78ac42f21604a544ca22f8fdc70e32016409703fa18d09c03440ce00000f7849f2df959c9fc49521e0f8870631e16289403de18c09083080e000000f77e7b2de956c9fe4a02190f7c6f631515909403da19109703340cc00000f778362f095c0a204ba2288f8870431215709083de19709583280c800000f7720c2e515849fa4a121e8f5c6f031a15d09683f8196095834c0da00000f76c132d194f09b04762160f406da30515209083c018009083000b400000f765e92e815a4a1c4a72238f8870831715709503d218509683180ce00000f75fb02ed95b8a244b62270f886fe32a16789a041819209c83640e000000f759a22d5955c9cc47b2100f046ce30615889243d818a09383300ca00000f753972d195109bc4822130f1c6c22f615088ec3a616b08e030c0c800000f74d5f2e995c8a304b52290fc070c32116009483ee18909102e80b800000f7471d2f31620a424b722c0ff4722335167898c40419809a834c0ee00000f741082d8151c9ca47c2138f346ca30b151891c3b617c09083040be00000f73ae22e715bca1a4aa21e8f406d831315289443ca189091031c0b400000f734863041680a724cf2310fd073033216509703f219609883340ce00000f72e7e2d114e49ae47220a8ec06c02fd15108ec3be18608f03040ba00000f728622de95409de49a2158efc6a22ed14708c839c16e08c03140c000000f7224c2db15509e249b21d8f646f0317156094c3ee196098031c0c600000f71c2f2e315a4a0a4b12238f746fa31f158893c3d018709883480d400000f716122df95a8a164b22250f8c70632b16289803f0194099830c0c2000 else 0xfa233f2e19590a024982190f446ba30314f08f43be17e09202f40c200000fa1d382cd94ec99245c2048eb06a42f7153093c3f819309883280d800000fa17102e195a09f649d21e8f506f031315a09383ec18809783380c200000fa10df2e715889f249c21f0f9470031c15e09683f219d09b03440cc00000fa0ac22de155c9ee48a20f8f0c6c030615609103e019009783100c400000fa04822ef15c0a2a4b32288fb072e33216809bc40a1a109f83540de00000f9fe672de15689ea48b2140ee06a22f214608ec3b817d08a02ec0b600000f9f8402db15409de49c2168f306de31715d09303d419209503040c400000f9f2062ef15d4a364af2248f906fc31e15b89443e818308d82f40c000000f9ebe72da1568a0049a21b8f6870231a15a89583da18d09483000b800000f9e5c52e415a8a0e4ab2208f9c70232015b09783e218809183240be00000f9dfab2dc95689f849f21e0f4c6e430c15a895c3ea19009803000ba00000f9d9962da15449ea4842168f606de313156092c3be17e08b82ac0a800000f9d3642e595749e24892158f286c830714e88e43c018408c83080cc00000f9cd2c2e615aca1e4a02220fac71a32915f89303de18c09182fc0ca00000f9c6f52e49588a044a52248f9871433016609703e618f09403000b400000f9c0f62d815009ce4842168f1c6ca2f9154090c3d618f09682f80ba00000f9bac82e615a8a104a221f8f5c6d630514a88e83c417c08c82d00b200000f9b4ba2d295289d44892120f306ce30614e88f03be18808f03140c000000f9aea72db15489f84982200f706f231d15589283ca18609002f80b400000f9a8962db95409e049721b0f6c70031715f09583e419609a83080c200000f9a2512f015e0a304b22288f9c70c32c16109703f019409783300d000000f99c252e815c8a244a82288fbc71032916289743f418f096832c0c800000f9960f2d4951c9b84782090eb06942e514408a439a17308d02e40aa00000f98fdf2ec15b8a1e4ae2258fa470031e15b896c3fa18e09b83700d600000f989be2e71598a124a421d0f5c6dc31916189783e819609183140c200000f983852e69580a0e4ac2278f8c6f832315a89383ea18e096831c0cc00000f97d772d715349d247c2128f246b82fb14808dc39a17308782dc0c000000f9772a2f315f8a304bc2280f8c6f031815f09783f219b09b03240bc00000f970f02ea9610a304b12288fc0722325165897c3f019809a83480cc00000f96ac22eb95b4a224b32258fa06fe31c15e096c3f018f09903640e000000f964be2cb95089d448e2138f206da30c15689443f819109683280c000000f95eac2de95509e048c2198f786f431b15b89503fe19e09603340b800000f958b72cb14e49c44742090ef06b030115789243c217608a03080ca00000f952882e515bc9ee49a21c0f4c6e030815389143c617c08d830c0ce00000f94c3b2ef95e8a144b32260fa071832415e09643ee19809903280c800000f9462b2d4950c9c04842108ed06962e014388b43ac17308d03080c000000f9400f2d9151c9e248b2170f206e231a157090c3ca18808d83040b800000f939ff2d795349f649821d0f4c6de31215d09403da18d09182f00be00000f933b42ec15cc9fa49721e8f74708324160898c3e819709903140d000000f92d852eb95d4a424bd2288fb871e32115789543d218909383280c000000f927962c314ac98e4682020e906802db140088039417208d02fc0b200000f9214d2ef95e4a1e4a521f8fb8704320163095c3e818e08e02e40c200000f91b292db155c9e449821a0f5c6c230115589303bc17708b82d40b800000f9150b2dc95649e24902168f246c42fa14c09143da18009182d40aa00000f90eca2f095e8a1e4a72200f746e830214e890c3c6179090031c0ca00000f908b32d595249d04892198f406ec31b15a89243e218c09703240c600000f9028b2e015789f84a121b8f5c6de30115489003b817e08f82f809c00000f8fc452ef95b0a204ae2270fd072232616109703fe19909383240d600000f8f5f22f61608a364bf22d0fb870a32e16389843ee19409b03200b800000f8efce2e795a8a184a92258fb870c32c16489703f418d09c03440d600000f8e99d2eb15e0a284b12288fc471c32e166099c3f419309983380d800000f8e3a42c894d09ac47c20f8ee06bc2f914e090c3d218f09903480d000000f8dd882db15689da4882150f246ca30715309083ae17a09383240d200000f8d7572e3956c9fa4902198f6c6fe31e15c09603fa19809703240c800000f8d1322dd956c9f04952198f446e0307150890c3c217e09282ec0b000000f8cb312ce14fc9c248220e0f046c830314808f43be17e08f83140b400000f8c4f42e995e4a344b02230f9c70432516189783e618108e82fc0b400000f8bee92d494e49ac48220f8ee86c430815309043b818909783200c000000f8b8cf2d615349d64902118f106b42f515009283d419009102f40b000000f8b2952ec15d4a244aa21f8f446da30f159093c3d418c09383000c200000f8ac562ef15d8a0c4a82248f9c71631b15889383d618e09803340c600000f8a63b2e01598a064a021e8f486c42f814788c83a017208502a00a200000f89ff92ec15f4a2c4ae2208f746de30f15688fc3aa17708c82f80de000) else (if i < 155 then 0xfbac002f01600a304bf22c8fc470c31f15e89603e8185095032c0cc00000fba6042d214f89c248a2108ee86a02f214888c03a616a08f03040be00000fb9fcd2e915e0a244ae2258f906e431615989203da18509303200de00000fb99912f115fca2c4aa22e8fd0720324163898440a19a09703400ce00000fb93722e095909f44972198f4c70a31d15e892c3ce18509683280c400000fb8d3a2e3159ca0849421f0f786f231415b094440218d09583240ce00000fb87172e095b0a0849721a8f2c6ce31315109243c217c095833c0d000000fb80ec2e095aca224a321b8f7c71232215b09643ee19909a03480e800000fb7ab72eb15bca164a42200f786ea30f15309143b817d09103040b000000fb74822e715aca144a92238f9c71a32a165098840c1a10a283680d000000fb6e712d8154c9ee49e2198f3c6da31715d898c40019f09b833c0d400000fb682d2f31600a3c4b82298fc06f831e16209803fc19709b83240cc00000fb61f82ec15c4a164a02208f906ee30b15209083c817708a82d40b400000fb5bcc2e195389de47f20c8f0c6c430f15389143b617b09602f80d200000fb55702fb963ca604d823b903c75c34d16e89d04281ae0a283400ca00000fb4f582d7953c9dc4872100f186d630715308f43d618709103100be00000fb49362df1578a084a92238f706ee31215489483ea191094830c0ac00000fb43082e995b8a144af2268f746fc31815b89743e418109183080be00000fb3d142cd94e49ae46e20a8f086b02f514b89043bc17908d03040b600000fb36eb2e395a8a104a121c8f486ec30f15488e83b617f09003300d000000fb308c2f89628a3a4bb22f0fe873833016809a43f219409703480d600000fb2a692eb15bca0c4a82250f986f030a15989443da18409703100b200000fb245a2d315309e84872168f146be30315509283dc18a09283040b000000fb1e5e2cb14c49c248520d8efc6ba2fb15088fc3c218209083240d400000fb18322e695d0a1c4a82188f346c82fc14f09003ae16a08682a00b600000fb12222d295209d84872118f246b62ff152090c3c218d095035c0e200000fb0bfc2e195589dc4922158f346ee31315a09743ee19309b034c0be00000fb05ee2d9953c9ee4952188f446de30c15209143d019009403280be00000faff8e2fe1658a564bd22a8fd071432a163095c3f618a09503240c600000faf96f2df15889ee49a2220fd4716323161098c3f619f09a83400ce00000faf36f2cd95189be47d2110f1c6c830615189203da18709182f40b600000faed5e2d695189ce4852100ef86c42fe14c88f83ba18909283000c400000fae75a2d694f89bc47a20d8ee46a42f414388c039616908382bc0ae00000fae1722c794bc9924622040e9068a2e4140088c39c17308d02e00b800000fadb3e2ea95dca3c4b52228fa06fc322164896c3f819c09c034c0d800000fad5102e6959ca0649d21c0f606f430a15789083c619909803440ea00000facefb2dc15549da48f21a0f446ec30c15409103b217208b82f40b600000fac8e12d715349de49d2230f8c6fa31b15c09543d218609383040bc00000fac2c02e215a0a144a32220f406ea30c15789583ea18909002fc0be00000fabc912ea95d8a264ad2238fa06f430e15609203ce17b08d030c0cc00000fab65b2e715809ec48b2198f386e2313158891c3d218a09683100ba00000fab03f2dc156c9f249c21b0f5c6ec31215889343c218208e02f40c000000faaa3e2cd95109b84882118f1c6d430615489203de18e08e82e80be00000faa43d2d094fc9b647c2100ed06c22fc14988d03b417608682b00b000000fa9dec2f69628a4a4c12318ff473633f17009c441619b09983300c400000fa97bc2e9158ca0c4aa2268fd474033816789b841e1a509a03440d200000fa91972de15489e24982138eec6d430815589543d218809602f80be00000fa8b9f2c494cc9a84872148f386de31515e09503e818c092832c0d000000fa85532f19624a2c4a52228f7c6ee31115589203ca18108e03040b400000fa7f292df15789ee48f2168f0c6c230715308d039a17208e83100c600000fa79192d9954c9fa4a32220fa071632816009503c017a09183280ca00000fa72fd2d795289ce47f20c0f006d230715189183d017a09282e80c000000fa6cd82dc95409da49521d8f7c70032415e89743ea19309803200c400000fa66952ec15bca124af2228f906fa31915a893c3ec18f095834c0de00000fa60812d695449e048820f8ec86be30214988c83b217c08d82fc0c400000fa5a622d615149d04872140f086c230314f09143e018909403000ba00000fa54272eb95e8a2a4b32260fc472432916089743e8188093031c0ca00000fa4e162e095709f44952148f306b22fa14f08dc3bc17b08882cc0ac00000fa47ca2f295dca304b22270fb072433716389783ec19109503140b800000fa41ad2da95709ea4902140f106d430d15589283c617808782bc0b600000fa3ba62d495389d048420f8f106b82fa14b08b439816f08882ec0ae00000fa35692ec15c8a244b62288fa471632315f09883fa1a509b832c0ce00000fa2f672d215149d04822098ed06be2fb15289443ea19b09b032c0ca00000fa29652cc14d09be4882118f386d831215d89543e619b09b831c0c0000 else (if i < 156 then 0xfd35512ea15bca2c4ab2270f9470c32715f09383cc18209282f00c000000fd2f302d9156ca0849821d0f606dc30c15389183ca181093830c0c000000fd29232d095109bc4782118ef06ae30815989443d618308f03040be00000fd23162d694f49ba4842130f286cc2fb14a88e43a417108602e40be00000fd1d032d9953c9fa49821d8f6c6dc30d15389183cc18309183080b200000fd16f22d2151c9cc4892130f386e830d15789643e218809403280ba00000fd10d82d9955c9f24a021b8f386d230915509343be18208f02d80b600000fd0a9d2f115e4a144a82280f9c72433616b09a441219108f82f00b000000fd04902d515449d648b2190f306c030714e09183d618a09583280dc00000fcfe882d915489ca48320e0f186b82ff15108e43a617d08a82e80a600000fcf8452ef95c0a124a121e0f606e831815609303be18709303180b200000fcf22f2e015889fc49d21a8f406e231a15e89583e219509a03440c800000fcebc73011644a4e4c822b0fe874233d16c89983f619909f03740d800000fce5972eb15f0a364b42290fac70631e15d09543f619909983480c000000fcdf7b2de15489e64892110f406e231015509583d818c09202ec0c200000fcd94c2e395aca124a82220f7c70432215d09603f219709b83380e400000fcd32d2e2957ca0e4a62258f9071a32515e89603d817c08982ec0b200000fccd182de95689f448e21a8f646ec30c15489183c017e09003100d000000fcc72c2c414c89a047b20c8f006ca30115109243e018909b033c0d800000fcc1132dc955c9ec4a421c8f646f030f15489283ce18509182e00c600000fcbac12fc9674a6c4cf234100472e33916e09e441619c09b03240d000000fcb47e2ef15e4a344b62238fa070631e15d09343ca18b09603080be00000fcae532e6959ca0a4a82230fa0714333166096c3fc19b08e02dc0ae00000fca80e2f31600a4c4c622f100873a33316509984041a009e03480ce00000fca1ef2e215709ec4912100f246d430814c88e43c017308e03040c400000fc9bc22eb15c4a044aa2250f9c704310155093c3ea18e09083200c200000fc95a52d615349ca49321a0f606ea31815809183d617d08d030c0c400000fc8fac2c914e89c448a2130f046b82fe14b88c839c16e08702cc0bc00000fc89852e2959ca144a92270f8471432a165899841019209302ec0c200000fc83492ec95e0a0e4b02248f7870431815a093c3da18a09383080ca00000fc7d292e095789f24a121f0f6c6f631c15a09083c617c08d03040c800000fc76e62f015eca2e4ab2268f986f031715b090c3ba17c08e82ec0b800000fc70d52d4151c9d048120f8ef46c02fc14a08c03a817209183080ca00000fc6ab32df15909f84882148f306da30715789243ca18608f030c0d800000fc647f2ee15d8a1849c21b0f406d830f15709483e419509d83440c000000fc5e292f415f0a2a4b82270fd873233f16d89c040219809c83500d000000fc581f2d695249b847e20b0ebc67e2de13e088c39816d08b83100c400000fc51f72e515e0a1a4ac2258fd073633b16e09dc4241a809a83540d400000fc4bc62e795989fc4a721d0f446de30415009183c018709303100b400000fc45ab2d8953c9d64912170f286ce304151890c3ac17608a02ec0c600000fc3f662f99650a604c922b8ff873033816809c44121aa09e83480d400000fc393f2e795d8a324b72270fec72233616089603f219d092832c0ce00000fc33082ef9628a4c4c4237903875833916b89d042e1ad0a1033c0d000000fc2cff2d2953c9f048f2170f386da30a15709483e819b09b83240c200000fc26ca2ea15d8a3a4b72280fb471232c16109703fc19c09b03480d800000fc20952e815aca0a4a52230f706fc31d15b895c3d818d08e83080b800000fc1a8d2d6153c9c84852118f206cc30d15408f03a817308c82e80b000000fc14972c994d09aa47020c8ef46ce31415989303d019009883300ce00000fc0e862da15249d448020e8eec69e2f014788cc3be18509403380d000000fc088f2cf15009ae4822150f106b630515989503de18c09903280c000000fc02692de15749e449521f0f7470232215b097c3f41a009a83340d600000fbfc552da95449ce48720d0f146be2fa14f08fc3cc189095830c0ac00000fbf6332e015809ec4942198f046ac2fa15308f43ca18f091830c0b600000fbf0042e79590a164ac2278f606de31715c896c3e61a0096031c0cc00000fbe9d12ed95c0a124ac2258fa870831f16409b040019c09a83380c400000fbe39c2f195dca1e4a62250fb0720329161096c3f219809b03580d400000fbdd412f3961ca3e4c32350fb872032815b89383d018c09503240cc00000fbd7362d6951c9d64902198f586e431e15d09583d618809603040d000000fbd10d2e39598a104aa2228f8c70031d16409a04121a20a183740d600000fbcae12e695bca184a02228f646e030c159894c3e819309903240c000000fbc4c22de955ca004932168f2c6c630214f890c3ce18709503040c000000fbbeac2d294f09be48120a8ef46be2fc14e88f83c417808e82e00be00000fbb87e2e515a8a144aa2238f9070431c161099c4001a309b030c0b600000fbb2422ee15e8a2e4b32280fbc72433916309683e618809b03540ee000 else 0xfebf5d2d114fc9d24842120efc6d830215288dc3ac17808b02dc0bc00000feb9362df9588a044a12228f9c70831b161098440019e09903340e400000feb3062e295e0a264b72290fd471232816009683ee19c09c83340ce00000feacc82ee95eca2e4b422a8fbc71233216889c041a1a509b83480e800000fea6a82de956c9f448e21b8f286d430615609243d218309103100b000000fea0ab2ca14dc99e4772108f186d630815089003c217c09482f80ce00000fe9a5b2fc965ca5a4c12320fe871e32a16189ac4081ab09f83500cc00000fe94062f4160ca524ba2340ff473e34216c09d04241a80a3836c0e800000fe8de52de15989de4922118f2c6dc31215589443e418c09202f00ba00000fe87e52d094dc9ba47e2110f186ba303151892c3ce18209003000c000000fe81c22dc15789f44a121e8f506f4319157893c3e218f09583280c800000fe7bb52ce15009a047a2108f186be2fd14b08c83b417e09102f80b800000fe75642fc9680a7c4d6234101873833c16409783d818809283340c600000fe6f392e11594a1c4ae2258fc872233016609983fc19709683140cc00000fe68f22f9165ca644cb235901073633816b09a03ec18b09282dc0c800000fe62ce2df95a89f24962180f3c6da307157096c3d819809502f80b400000fe5cab2dd155c9dc48e2170f486e031415b09383ca18608f02ec0b200000fe567d2e895a4a0a4a421f0f8071031e15e09403ea18e09503080bc00000fe50572e095589e848b2160efc6be2fd15209003de18c09602f80c600000fe4a252e915f4a204b72230f886f831d158094c3d217b09003080be00000fe43f12e915e0a164a721c0f6470a31c15989443e2193096830c0c400000fe3d8e3039680a604d4238102473e33716989c041419a09603100c600000fe374f2e895cca184a521c0f586e6321158091c3c618c09083380cc00000fe31192e4958c9fc4902148f086c22f614c88e83a818108f03080d000000fe2af72e295949f24942180f146cc30415488fc3b618109003040d000000fe24dd2e015849fa4972190f3c6fa31715d892c3c818209282e00ae00000fe1ea42e19584a184a82230fac72432e16609b04141a609c03280d600000fe188d2da15309c247b2138f386d631115909383e819209903340be00000fe127c2d89568a024a82250fbc71e32c16309803ea19b0a003880e200000fe0c522e895d0a2e4b822a8fb071a31a15989483d418d09903580d600000fe064e2d715089e249021b0f2c6cc306154093c3d218909402fc0c000000fe00342dc15489ec4932180f506fe31915c89243c618408f83000c000000fdf9f32ee95f8a324b722a0fec72033316309543d218409503280cc00000fdf3e42da15349cc48a2168f546ce2fe14f09083b818109002f00b400000fdede42d595249a247c20e0ecc69a2f314b88bc3ac18108e02e80ba00000fde7dd2d014e09b848621b8f806fe32616509803e618b09603200c400000fde1c42db95489dc48120f8ed06a42fb14a88e03c417d091030c0bc00000fddb9b2e3156c9fc4a72248f906fa31f15b097c40019809603340c000000fdd5672e89594a1c4a72238f6470031415b09203cc18608d82d80be00000fdcf3d2e395a0a204a321c8f4c70032315b89343e81a009c83440ca00000fdc90d2e415a4a164ad2248f686ea31315a09183cc18709403080c200000fdc2f82e19580a0649f21d8f386d830d15589083c618b08e03040ba00000fdbcda2da156c9fc49a2190f286ce30915b09483c218409103240d000000fdb6b42e815b4a1e4a221a8f3c6d830b15409043c617d08902ec0c200000fdb07a2ec95eca444ca22c8fd872a32e15e89743f01a209c03600d800000fdaa402ef15e4a344a62238fa06fa32115989443e218e098030c0ce00000fda4312d995709f849b21c0f606f831d15e89583fa192096832c0d200000fd9e142e01580a0649f21b8f486d431c158893c3d818409583100c000000fd97c22fa95e8a284ae2268f906e631315789143cc18609203000cc00000fd919b2e695aca284b22248f806fc31d16109643e218f09603180c200000fd8b7d2e3158c9f049821c8f406e430d15209283e4192096834c0c600000fd85382e5158ca0649921e8f686ee30d15709243ce18108c82fc0d800000fd7f132e015c0a184a821c0f5c6ec31f15c09483ea18d09783340c400000fd78ff2d995249c848a2178f3c6e230d15989443ce18008e03040d200000fd72d82e695c0a124a92210f586dc31615888f83b617c09103180c600000fd6caf2de956c9fe49821d8f5c6ce2fd14988e039616f08802f40c400000fd668d2db95809f44982188f3c6d630e15809503d618509102ec0ba00000fd606b2e415a8a1249d21d0f7c70432515c09343da18509603340cc00000fd5a602d595409e04882188f346d630c15389103a416d08902dc0b400000fd542f2e895c0a1e4ab2240f9c71031915b89603f019709783440d000000fd4ddc2f81600a3a4c822c8f9c6f831815c09243d017e08e02e00bc00000fd47c82d695449c848b2168f686fa31b15b89403da18609703300c600000fd419c2e715aca244ad2228f9070231b15e899c40c19b09803340c800000fd3b852da95409e249c2218fa871a32b15f09683ee192097030c0b6000))) else (if i < 160 then (if i < 158 then 0x10047f12dd95649f24902140f146d030d15389143c618808d02e00ae000010041b02f115f4a204a92208f6c6f4317159895c3d819509983240da00001003b972d515589f049521f0f606e630d154892c3c217e08b03100d00000100354c2f215e8a204a92238fb46fa31d15d89583ec18a09283300d400001002f932ac93dc94643f1f28e2c65a2d6140088c37a16c08902d80ae0000100298e2d295189d64862100f086de30c14f88dc3b217908c82fc0a0000010023812d595349d648a2148ef86bc30515088f03c417808c83040c400001001d542e395549e848a2158f586d2305152091c3ce18808e03240cc0000100173e2db15409e44872108f006b22f414508bc3b017f08b02f80b00000100111b2e3157c9fc49e21a0f406d030e15789443e018b09683480c800001000aed2e595a8a0e4ac2228f7470031715c89343d217a09383340d2000010004b72e715cca224a82238fa070031f16189643f619309803280d000000fffea22e1955c9d248e21b0f206d430315409083d818108d02e40c600000fff8672ed15aca204b12248f886f431a15809583e4185091030c0c000000fff24b2dd95649f649b2168f406e630b151090c3c418709403440ce00000ffec3d2d595189ac47a20c0eec6ba2f614888f03c617508882c00ae00000ffe64f2c294909904602008e6c6802da14308bc3b017708c83080ce00000ffe00c2f015e0a0a4a12268f9c6f2311154093040219609c83780e000000ffda082c914a49a847220a8ecc6ae2f714b08f43a016c08402b809200000ffd3ab2ef15dca284b52290ff471e322163098c40019909c03500e000000ffcd7b2e4958ca1e4b62268fa471032815b09703f219f09683100d600000ffc7582e215789e64952198f586f430f15408e83c017108d82f40ba00000ffc1342d915649f04932120f386f631315889383d818e09483040ce00000ffbb122de1574a0649f21f0f646ec318158094c3da19c09b03480d400000ffb4fc2d795549ea4932180f806f431215989443e419209603280ba00000ffaef22d595449e04952180f606dc30815209203ce189092832c0c000000ffa8b82ef1618a584c822e8fc872031d15c094c3dc19409603200c400000ffa2922df9594a0a49b21a0f646dc30b15589403e019409383080ce00000ff9c482f09610a344b62258f8870431115789343d618909382f80bc00000ff96322d8153c9ea4a12200f506e630a15c89603f619b09d83680ce00000ff900c2db95209ce4912210f746fe31815b098c3f219709d033c0de00000ff89d02f09600a3e4a92240f9870e32016189643e618309083280be00000ff83b72d694fc9b847520e0ed06d230114c08dc3ac17708982e00c600000ff7da92d094e49be48320f8efc6b62fa15189183ce18308b02fc0c800000ff779d2d114f49be48a2160f4c70031c15a89303e218f09583240d400000ff71892d215109d84892148f206ca30b14d88c43a016908602a00aa00000ff6b502eb959ca024a121e8f706e430c156092c3ce17b09282fc0ba00000ff65152ed95f4a284ba2290f986f831b15a09403e018a09603100c400000ff5efc2d994f89c24852120f186ea31215509303e419709403180be00000ff58de2dd15389d849921a8f386e430f15708fc3b817f08b82ec0ca00000ff52a72ec95c8a124a821c8f7870830e15689183e418a09683340ce00000ff4ca12d615049ba4872108ef06c230215008d03ae18009183040c400000ff465c2ef95e8a284b42270fa071432115e09583ec18a092031c0c400000ff404b2d9153c9d24832158f1c6da30e15109003bc19109702fc0d600000ff3a202e8959ca0c49a2190f6870032816089903ec18a09382e40b800000ff33fe2dd15709e84922140f186b22f314a88ec3b017e08c02dc0a400000ff2dcf2e595e0a204a72260f80710327162898c40e19709a03540d200000ff27b72df15809f049c21d8f7c6e630a15909343dc19209783400d400000ff217d2e915b89f44a02230f8070a32916089443da18709483180d000000ff1b872cd14f49c84832098ee06b82f914f89103ca18209082e40b400000ff15702df95589ea49c2150f306ca30415289103be17d08c82ec0c600000ff0f412ec15c4a0e4ae2260f986ee314159095c3f018c09002d80c000000ff08fe2f015dca1a4a52268fa86fa30e15888fc3dc18c09603280be00000ff02e72dc954c9d047d20e0edc6982fc15209103c217b09082f40a800000fefcb62e015649f44a121c8f406d030a15488fc3d418709003040bc00000fef6be2cc94b49ac46f1ff8ea06a22ec143888c38e17109103100b800000fef0862f115c4a184a12210f7c708326160098c3f619a097833c0be00000feea532e895b0a1849d21c0f646fe324162098c3f818e09283300d600000fee4262e615a89fa49b21b8f546ea30d15288fc3ae17a08e82e80b800000fede212d214f89b248020d0ef86c030914d88fc3b4185094830c0c000000fed7fb2dd95689fe4a621f0f886e8316159894c3e218c08d83180ca00000fed1bd2f115f0a3e4b42290fc472432a16189783d618a08f82f80ca00000fecb9f2e395dca1e4a72258fa06fa32215a095c3e018908d02f80ce00000fec55e2ec95e0a264a82260fac71c32515e094c3cc18609603200d8000 else (if i < 159 then 0x101d0a62ec95c4a1c4a32230fb4714323163097c3dc18609203180b00000101ca992da95589dc4832120f186d631215809483d417a08982c40a20000101c4502f315f4a204b32278f806f032015d09543e618a096035c0d20000101be382dd15709f848d2160f346d430b155891c3b017b08e83080c60000101b82d2d8951c9c848c2168f4c6e430c15689503de18a09983580d00000101b20d2e01594a124a421e0f7071c32715f09943fc19809883440d60000101abca2eb959c9ee4942180f786d230315509343c417e09283000d40000101a5922e995b4a144a92238fa471632b16589843f419909403240ca00001019f432f5160ca3c4af2270f9070632d16509643e018d09303200c80000101993c2d415149b647320b8ee86c42f714e08f03bc18409283100b4000010193062e515849f44922198f606e6309156890c3ce18609002c40b800001018cfa2d215389c847f2100ef46c630615509403ea18509103040c2000010186e02d795249c24872110f0c6c030315309043d218909383300d6000010180b32e695849fc49921c0f706de30f15709483da19009283180c600001017a772e795bca0c4a32208f6c6f230215689703dc17808983000ca0000101744b2e015aca204ac2248f886e82fd15809283d619109783200ce00001016e3a2d895289de49021b0f346e631415c89343d017908b82f00b2000010168142e395889f64992178ee86a62f014a08ac39017508d02e40ca000010161f02df9584a0049321d8f806fa31215589343d818a09503140b600001015bc52e695a8a0e4a92218f80706323156892c3c817e08a83180b8000010155a72de15449e849b21e8f806f630f15709443ec18c099834c0e200001014f6d2ea15d8a324b22238f7870031715c094c3cc18e09583280d20000101493e2e115809ec49e21c0f8c6fe31a15f09703f219009083080ca000010142f22f21614a4c4be230100074034816e09d841a19709703480ca00001013cd02e39558a0c4a52228f986ea31815789403e018509503040ca000010136ba2d715249e04882108f1c6da30514d88dc3b017708e03300ca0000101309d2de95609e648e21b8f4c6f431b161097c3f019609703180c800001012a812de957c9dc48a2178f486dc30a15409183c617d08582e00ca000010124592e2959c9fe4982200f6c6ea31216109503da19509683440d200001011e0e2fb9634a284af2220f606f031d15789203cc18409283100c6000010118232bf946898e4612038ea46b02f614908cc3b217608982c80ae000010112112d7952c9c648e2180f446ee31115a09483d418509103200be00001010be92df95bca144a72200f746ea31815a892c3f218d091831c0bc000010105c72e015609f449021a0f2c6ee31315809183cc188098834c0e40000100ffcf2c8146c97445d2020ea869a2f214808c03b417c09382f80ce0000100f97b2f7963ca484bd22c8fb870632316309603f219c09d836c0dc0000100f3a52c014a49a84722060eac6922e314488c43a217208682e40b40000100ed4f2f31610a4c4c9232900874233916789c44141a309c03280d20000100e7112eb9614a3e4bc2308fd070832815e0960402194092030c0c40000100e0f82de1590a0849d21f0f9c6f831215909343ee19109602fc0ba0000100dae02dd95609da48e20f0f106b22f414e88c03a817c09403180c00000100d4cb2d715409dc48e21c8f586e631515909703e219209683100d80000100ced42c894d89bc4802110f0c6b42f814808a039617008c02fc0be0000100c8932e815c8a244b22260fa86f231615589343bc18009002fc0b80000100c28d2cc14fc9cc48b21a8f0c6d030f15909443de19709b83200d40000100bc9e2cb14e89be4802120f2c6b830215308e43b817e09102e40c20000100b6882df15389f44912198f586e231215709843fc19b09082e00b20000100b0702d494f09b247a2108f286cc310156093c3c818209183100b80000100aa382ea15b8a1e4b922d0ff4744334162099c3e219409a83600ec0000100a42d2d595049c04862120ef06b22f314f89003ce187091831c0bc00001009e3a2c714d89a047920b8ef06b22f914d09043c217d09183040c8000010097f62f49604a364be2318ff471e33216489b440c19d09b03580ce000010091bb2ea95a49f849f2230f946f631d15d89303ac17a08902d80b800001008b862e59598a0849b21e0f6c70231215d897c3fe19f09c832c0ca000010085442f115dca284b02248f9c708316159899440418209483080c200001007f1d2dd95b4a184b22228f9070e31415809743f819909583180be000010079092db9568a0449b21a0f886fe32115d095c3e018108f82cc0bc000010072cc2e715cca104ae2298ff873832c16e89ac41e1a109f83300ca00001006ca52e915b89f44992198f706f431b15f095c3f019009103200d8000010066882da9588a0249d2278fa471232d16189543e618a09503240de0000100605a2ea15bca264bc22d0fc071631916109703fa19d09c832c0d800001005a352de1574a144ab2270f7c6e631715a09583f619509a03300cc000010054262d6955c9f84932150f306cc30d15809483d018b09282e80bc00001004e142d815349ca4812108f246ca30c155092c3d618109183080c8000 else 0x103595f2dc95389ca4872168f446c82fc14b889439816a08982bc0b4000010353332e3958ca024a32230fa06fe312158093c3dc18909703300c200001034d1d2db15409e848f2178f146d030a15088d83b418009403200d40000103471b2cf94f49b848120d0ed46902e514908ec3c617a09002f40d0000010340f92db15289b647b2150f0c6be2ed14808e03b217308d02f80ba00001033ace2e69594a0c49c21a0f486dc30014e89303ea18909482fc0c6000010334902ee1608a2c4bb22c0fac71832815f093c3c6188091830c0c400001032e382f91634a524c72340ff4726329160898040819f09a033c0da0000103282b2d6956c9f049a21b0f446ee2ff14f09003c018108e02ec0b0000010321f02e815cca0e4a121f8f386cc305155892c3da18309182fc0ca00001031bcc2e395909fe4a72200fa871c328160898c3f419209583000cc000010315b72db955c9fa49921a0f4c6e831715b09343e018909603280c400001030fa72d515389dc48a21e0f4c6ea30b159093c3ce187090830c0be000010309942d7151c9c04872140f0c6aa2fd15008e43d418e09703400d6000010303772dc154c9ea4962168f446da30415889403e2192097830c0c20000102fd5a2e015549e448020f0ee86c82f114b08d83a617d08f02e00c20000102f72b2e41598a124b722d8fd471e32e16209683ea19309b83300c80000102f1082de15549e44972190f3c6e831515309183c818809283000ba0000102eace2ec15c4a1a4b32268fbc71631e15c09583ea18709183080c60000102e4ab2e0957c9f849c21e0f586e430014d08e83ba18309102ec0c40000102de982dc952c9cc4942190f4870c32816089783ce18109383200c40000102d86e2e795889fc4a82238fa070e323160899040419e09983480de0000102d2492dd15649fc49f21e8f6c70632116409a440019609a83340c20000102cc1e2e115909e24a42218f886fa31a157893c3ea19009583240d60000102c61f2ce94bc9b248220d8ed06b22fd14d890c3ce17e08f83280c80000102c01a2d095309d44872118f146ca30315308e83c018309503200cc0000102b9ee2e015b0a0a49f2168f406dc30715009103c417808b83000b60000102b3b22ed95dca204b12228f606e430515609303d418709583000c20000102ad7d2ea95c0a224aa21f0f846e831815c095c3de18809603100c60000102a7622dc9550a0449b21d0f286d430915b89583e818508e82f00ba0000102a1432df95889f84912138f106ca30f14e09003bc17208482d80c200001029b152e715c89f649c21a0f486fa31d15b894c3e819209402fc0d0000010294c52f31628a304b32238f946f631b15b09543e619209a034c0c800001028eba2d615389d84852118f406d631215889303e218c09302e40b00000102888b2e8958c9f649e2230f846f630e15408e03b617208802c40ae000010282962cb94b49a847e2118efc6d230015a09203ba18309082f00c400001027c932cf15049b846e2020ea86a42e7144088838816708582e80ba000010276862d695509de4882118eac68c2e414108a839217809202ec0b80000102706b2e015889f04982168f406e630e15009083ce182091031c0c000001026a1f2f095e8a1c4af2248f646f230f15809383c018809483080ae000010264202d114ec9ca4832120f6070231515689243cc17d08b83000c800001025df02e715b8a0a49e2198f2c6ce30515209243a617b092031c0d0000010257c62eb95eca344b72298fb871c32115e89683ee18a09683540ce000010251cb2ce15109b24802138f206c42fe154891c3c818109383080b800001024b892ec15dca444bb22e8ff473833716909a83fe19809483000b0000010245702db955c9dc4952180f586ea31c15a09483d418909503240ca00001023f262f01610a264ba2258fb46fe32716089383c217908f03080c2000010239232ce951c9ca4862130ef06bc2f814a88dc3c217f08e03040b8000010232f02e7157c9fe4a021a0f446ea30d15589483e219209b03500d000001022ce92ce95009d047d20c0ecc6ac2f314a089c39e17308c02dc0b4000010226b22ee15fca4e4cf231901473a33c16989a040c1a009c03200d6000010220852e595b4a004902158f246e431e16289d041a1a40a083500da00001021a2f2ff1634a564c62310ff871031d15e09703ec19909b83480c6000010214092dd95609fc49d2238f746e831415f09744161a009903400ce00001020e0b2d215109ae47520a0ef06cc30915708fc3e018709503480da000010207dd2e615c8a064912138f3c6ca2ff15108fc3ae17c09303140c4000010201be2e095789e449621a0f206d431215409043c218208f82ec0b60000101fb952e5158c9f04952190f506ee31c15989283cc17e08d02fc0b40000101f5732e21590a044a22230f746fc31a16089783e018509a03300ce0000101ef732d094ec9a84752090ecc68a2ed14688b039617108d030c0ca0000101e9682d9152c9c647f20c0f0c6ce31115688fc3a817208d02b80b40000101e3192f115dca464b722c8fd070e32615e095c3fe19b09683000cc0000101dcf92d995589d84872138f3c6d430c15909483d417a08a82e00ba0000101d6d32de954c9ce4842158f486e231315c097c3f619509903340d4000)) else (if i < 161 then 0x104e1882d795109d849121a8f3c6d230314f88e43d619109a83040d00000104db4e2e595c4a264ab21e8f746ea30b15909243b818309502f40b60000104d51f2e09588a0e4a821c8f746e231415689583d818c098032c0d00000104ceee2e695a4a164af2280fec72031d15e894c3ee19809783380da0000104c8b22f2160ca3e4b522f900475233a16589a8412198098833c0c60000104c2782ec15e4a244b12298fa870c323165899840a19909a03500d00000104bc612d995089ca48420d8ee86b82fb14f091c3d218908e03040b80000104b60c2fc963ca364b72248f9870432215f89743f619809c033c0d40000104b0252c314b899c47920b8ebc6b22fa15289143ce18609803200bc0000104a9e42ee95e8a224a22270f8c6f231415a09243c818308f83080c80000104a3da2d795449e048e2130f0c6bc304151091c3b818009083100ca00001049dd72cd95109c84842138f246ca30615209103c618209302fc0c2000010497d12d7153c9ce48d2100f086c830115409283de18509002e80cc000010491bf2d315389ee49c2210f686e031315909403e619509903400da00001048bac2db95349d44852140f286d831215a09643dc18a08f83200c60000104858b2dd958c9e648b2170f246be30314f89003ca18108f831c0c000001047f4c2f0160ca2e4b72260fa871432f166099840018d09383040b2000010479632c714a09ae47420a8ee46bc2f914b08bc3a417108e03100cc000010473202f39614a3e4c3231901474233a163099840818a094830c0c000001046d122d795549e24922148efc6b22ff14e88f83ce18409483000c0000010467222cd950c9d049321b0f386d231215c89303d218609303040ca000010460d72f095cca224a82288f946fe31415809403f218d09703100c200001045ab72de95589f049921c8f386e431015089043c017a08c82e40a2000010454912e115409da4952160f406dc2ff14e09183ca18f09503080cc00001044e7d2de95a49f849421a0f686ee30f15689243ce17a08e82f40bc0000104485f2e195789fe49b2178f4c6bc2fd15189283d618609283140c20000104424d2db955c9da48d2158ee46ac30215309103d8192097030c0bc00001043c032ed95d8a1a4a32260f9871a33516509943f619309102f80b6000010435f22d4152c9e448a2128ed86a22ee14608f03b617408702f00c000001042fc42e115a0a0a4962178f246e231215689243c017608b02e00b0000010429a72dc15449d24872118f106b62f714a88c43ae17808702c40ba0000104237f2e595c8a0a4a021d8f606f432015b09203de18b09883040c000001041d1d2fd963ca504c122e0fd471c32b16389a840c19109a03140ba000010416f02e4156c9e848e2168f446d8305157092c3d819409a83380cc000010410d12e295c4a0a4a62248fd0728329164096c3f019909683400da00001040aa12e71590a024a62228f7c70631c15d89303cc18409102dc0b20000104047c2de954c9e849a21e8f886f431415d09543e818a08f83200de0000103fe782cd94c099a4742108f486e231a156892c3d018d094832c0c20000103f8642da15549e248f2160f446c62fd14f88e43a417508882e40c20000103f23a2e195709f049721e8f486e831315889203ce18509403280e00000103ebf82e49584a0c4a921b8f586f030915589183d818c098831c0c40000103e5d32e01594a084a321e0f686fe32916589883fa19a09a83100b40000103dfc72da9590a0449e21f0f486f832315889643f61a009c03480e00000103d9bc2d615289da48d2170f306da30d15089343ce18709082f80ca0000103d3be2cc94e49b847a2078eb86942ea14688ac39e17a08e83040bc0000103cd622fd1650a624cd2310fd073233e168099c4181a40a003600e20000103c7612d1950c9ae47120a8ec869a2f414588a038416f08d02f00be0000103c1412e415989fc4a021c8f646fe31b15809343d818c09503140bc0000103bb332d194f09d64902170f2c6da30715308f03c417e08e02e00b20000103b5172db95a49fc4a82220f9870e322160098440419d09c033c0ca0000103af182d114f09bc47d2118f106a22f014688d43b817e08f02fc0b00000103a8e22ed15c4a244ae22a8fb471032716489843f6193093831c0c80000103a2d32d6950c9cc4802120f346cc30715309203e419a0a2835c0e400001039cb52e1158ca1a4ae2238f7c6f431915c09703ee19209302d40aa0000103967f2e995cca164af2268f9c70031a15a09644021a109b03340d80000103904e2e995cca024a42250fa870032315e09383de18809003040d000001038a582c894e49bc47c20a8ef06a22f915189243c218509303400ce0000103843f2db15609f24982170f286d630b150890c3bc18308a82e40ae00001037e112ee15d8a1a4ac22b0fa471431615d89343d218609282dc0be000010378082d5952c9da48e21a8f546e831215989483e619409402f40b0000010371c62f315f4a404c422f0ffc72832416189903fc19209482e40a000001036bbc2d61540a044ac21e8f786f831b15e09703e018909503240c0000010365912e915a89f84942168f246d831815709183d818009003280d200001035f8b2d695449f84992198f446c6303157894c3ce18309002f40be000 else (if i < 162 then 0x10669752d5953c9c248320d8f106ce30115009303c618c09703100c6000010663692d9954c9f649221a8f1c6ea31c15a89343d018408903000c200001065d4d2d315049b44762080ed06b22f614b88d43ba17e08b02d40bc000010657282de9584a1049b2220f906fe31415909443d818e09583100c8000010651112dc95749f84952168f406d630f15589243d819609803240b400001064b222c3948c98245d2038eac6922ee14688b43bc17608a02b40b4000010645012e595c8a1e4a42218f606fa31715789343d418908d830c0c200001063ee52db158ca004a221d8fb46f431f15989143ba18709202f00bc000010638ce2d7152c9d448b2180f2c6da30b15689183c217d09302fc0ba000010632a02e615c0a144a32198f706fc322164897c40019f09883380d600001062c752e495bc9f649a21e0f386cc300157891c3c6183092832c0d80000106265a2d695349da48c2100f086cc2fb14b88e83aa17108c83040c80000106203c2da95649e848b2188f186d02f714788f03b417a09182fc0c2000010619fb2ef1600a464c42310fdc71831c15c09343cc18908d02e40b6000010613da2de15649e048a2128f106c22fb14d08d03b816f08882ec0b800001060dbe2df156c9ec49d21c0f486e4315154895c3d618f096832c0c6000010607bb2d81548a0c4a221e8f7c70432215a09643d819309583240c6000010601772f3961ca464b92280fc070c31a15989303f819709883480ca0000105fb382f315e8a484ab2248fb071e32916289603e818d09883300d60000105f5112dd1578a024a22208fa071432215d09543de18609403140b80000105eefa2dc954c9e649221b8f506ea30c159892c3d218f093030c0d60000105e8ec2d815689f84962170f5c6fe31615909403de17b08f02f40ba0000105e2c52e295709fc49321d8f886f4316155094c3e218409583240c60000105dc922e795d4a164a82258f9870832716689bc40c1a609c03440d60000105d68c2cf94f49a847e2080eb06962fb146889839a16f08e02ec0a60000105d0782dd95349be4882168f206d430d15389043c618708f02ec0cc0000105ca4c2f115f4a2e4af2240f9c70c32716209403dc19209483300c00000105c43b2da95549d848c2130f2c6e831d16089883f818e09a83280c80000105be182e0155c9f44992220f8871432516709903ee19109603280c20000105b7c22fc9664a6e4c5232102474033215e89703f819909e834c0ce0000105b1832e795b8a0a4a52210f6c70431d15889483ce17c08d02e00b80000105ab652e015509d24892130ef86cc2f714688e83ba18d09683180ba0000105a5392e215789e849621d8f6c6f430f15a89683ec1910a103440e600001059f1f2dd95649ec49a21a8f7c6e22fd14988e43b817908b02f00ae000010599192d114fc9ce4802118ecc6ae2f214988c83b817709082f40b2000010592eb2e815cca304b52288fe072633116009643f418709483140c400001058cd82d895249e449a21c8f6c70a321161898c3ea18a08e83040b8000010586ce2d094f89ce48020f0ecc69c2ee14888c03a217108703040b8000010580992e91604a384b22270fa471a32e15f89843f218909203000ac00001057a7f2e295609e44902158f446dc30614e88d43ae17808a83000be000010574632dd9598a124a02210f606ea31715d89503ea19909783400d000001056e482e0955c9ee49f2210f786da31115809743e419009603340d6000010568302da95509de4932160f3c6e631815a894c3f219909903640ce0000105621a2d695209ca4832110ef46ba2f915109083ba17b08e02ec0b400001055bf52e095649ea49c21d0f846e2314159893c3ca18d09383380d6000010555be2eb15b4a104a521e8f486de30d15a09443cc18d09983040ce00001054fd92c3148c98846a1fd0e746802d513c887838616c08903000b4000010549c32d695409f449b21b0f7c6f431f15f89683d218c09303380d8000010543902e395889f049921e8f346c830915709383f619a098032c0e200001053d6b2e395709da4872170f306b630115409283e019309b83340c00000105376c2ce15209e04982198f406f432516709883ee19109703380e60000105315f2da1568a0849d2190f2c6da31215a89283c417c08c02f80c000001052b1e2ef1608a244b32250fa071031a159895c3ea19209983080ce000010525012df9584a004a22200f606f030d158893c3c818d09503100c000001051ef22d395349dc48d2140f346e230915509343de18609282f80d0000010518b32f095e0a324bf22a0fc071232616209543e418f09082fc0c0000010512a22dc955c9e24952190f586de30414d88f03b817d09183180c200001050c622f015f4a164ad2280fd072833016589a440e19e09b833c0da000010506152f4161ca4e4bc2290fa86fc31915b09804001a209c83580d80000105000b2d515289dc4902148f546f430d15709443e2188095830c0c60000104f9fb2d715349be47e2070ea06962ea13e889839617208d83280ba0000104f4062c994c09b648020c0ec86ae2f714d89243c418308e82f00b00000104ede82e1958ca1c4ab2270f9470831f15c89543f219309603240d60000104e7912fb9618a3a4b42208f746de30915289143c017d09103040d2000 else 0x107952a000000000000021b8f506f832416109783e41970a0037c0f600001078f252d6954c9e448c2160f406d230714f08f83be17c08e82e40ac000010788f92e795a8a0c4982130f106b830215089103c618a09203080c8000010782e02d895309d848b2188f5c6e831d15a89303e618d09403200cc00001077cb32e295589ec49821c0f4c6ec30815288ec3c018109302ec0a80000107767d2ea95c0a284ad2260fa872633216889944041a309983300cc000010770712d295189d04852170f1c6e631815789383e618d09403380ca00001076a6f2ce95049be4812138f2c6de31015609303ca186090830c0c20000107643c2df955c9fc49c2178f346ec31815689243dc18a094030c0c800001075e252e115749ea4942228f7470831f15f09703fc19209483280ca000010757e12f015f0a464b722b0fec72c32516209803fc19509203000c6000010751d92d4953c9d048d21a8f606f831315b097840c19b09703200ce00001074bb42dc155c9f048e2190f306fa31915a89703fe19709b03240c8000010745912e315749fc4962198f346c82ff15089383e418909183340ca00001073f712dc9560a064962188f2c6c02fb153892c3e218b09902f40ac000010739462e295689f64a92210f706ea31315008e83a417d08c82e40ba000010733462d115109d44862160f4c6d030e15889483d018709403300d600001072d2b2da15449dc48f2178f386ee31115c09443e418908f02f80c2000010727152de15609ea49521b8f586f231114e08ec3c618a09503380cc000010720e82e695c8a224b822b0fbc6fc315158893c3dc18409083180da00001071aad2eb95c0a244ac2250f8070431515f09603e618e09502dc0b4000010714632f095e4a0a4a22200f9070631c15d095c3f618709483140ca00001070e5c2d595209d84822110f046c02fb14b88bc3ac17f090030c0ca0000107084b2d8156ca0249c21a8f3c6d830614d89043c818008a82f80b8000010702402ce94f49bc47e20d0ee86ae305158095c3e018809783100ca0000106fc0a2e31584a104ad2250f646e8311156096c40e19909e03740d20000106f5bb2f6961ca3c4c32280fac6fe31c15d896c3d017a08d03300d40000106efae2d895249d048e2158f406ba30015209183ca18709383400c80000106e9822e595b8a0c49c21d0f8870e32015709403e2191095030c0ca0000106e3992c914bc9b64762098edc6c430715489183ae17308b02f40c00000106dd6c2e39594a084a12220f9870831715d09583ea191096830c0ca0000106d7672d595089d048420e8ef46c82fe14d08d43aa16f08882ac09c0000106d1432e095609f84962198f546d630c15809743f019b09c03400be0000106cb3d2d615209de48b2158f106d030715489343ce18608f83080c20000106c5352d194fc9ba47c2140f146d230815589143c218008d02d40cc0000106bf1d2db157c9f649921c0f506d430414c08c43a017708c82e40c60000106b9082dd956c9dc4912178f1c6d230815109343d618d09202ec0ae0000106b2bb2f015d8a244b22288fc472c334167099c40819b098832c0ca0000106acc22d4150c9ce48e2128f086aa30815009243be17408f83000c60000106a6aa2de153c9e04942188f386dc30e15589043c017a09002f00b80000106a0822e395a4a084a421f0f546ea31415a09503fa19609903280d800001069a4e2eb95c8a024992190f206da31b158093c3d018809603300c6000010694312df15a09f24a32200f846d630f15109083c818b09083080b600001068e092e315889fc49a21b8f5c6e230d15409303dc18d09603240d8000010688022d415189d84882170f306d031015709143da17d08e02d80a6000010681f12d7153c9e649f2190f446d630f15488ec3a416e08a82cc0be00001067bc32e915aca324b22278fc871631f163099441019709a033c0cc0000106757c2f49610a3a4c52318ff872232a16689984101a60a083740d600001066f6c2d795349c84822120f206de30d15b09583d618b095032c0d8000))))))))

private def checkpoint (i : ℕ) : ℕ :=
  let word := (packet (i/1024) >>> (240*((i%1024)/16))) % (2^240)
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



private theorem b153645 : covered 153645 153726 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b153726 : covered 153726 153807 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b153807 : covered 153807 153888 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b153888 : covered 153888 153970 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b153970 : covered 153970 154051 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b154051 : covered 154051 154133 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b154133 : covered 154133 154214 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b154214 : covered 154214 154296 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b154296 : covered 154296 154377 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b154377 : covered 154377 154458 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b154458 : covered 154458 154539 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b154539 : covered 154539 154621 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b154621 : covered 154621 154702 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b154702 : covered 154702 154784 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b154784 : covered 154784 154865 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b154865 : covered 154865 154947 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b154947 : covered 154947 155028 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b155028 : covered 155028 155109 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b155109 : covered 155109 155190 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b155190 : covered 155190 155272 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b155272 : covered 155272 155353 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b155353 : covered 155353 155435 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b155435 : covered 155435 155516 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b155516 : covered 155516 155598 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b155598 : covered 155598 155679 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b155679 : covered 155679 155761 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b155761 : covered 155761 155842 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b155842 : covered 155842 155924 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b155924 : covered 155924 156005 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156005 : covered 156005 156087 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156087 : covered 156087 156168 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156168 : covered 156168 156250 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156250 : covered 156250 156331 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156331 : covered 156331 156412 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156412 : covered 156412 156493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156493 : covered 156493 156575 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156575 : covered 156575 156656 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156656 : covered 156656 156738 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156738 : covered 156738 156819 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156819 : covered 156819 156901 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156901 : covered 156901 156982 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b156982 : covered 156982 157063 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b157063 : covered 157063 157144 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b157144 : covered 157144 157226 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b157226 : covered 157226 157307 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b157307 : covered 157307 157389 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b157389 : covered 157389 157470 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b157470 : covered 157470 157552 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b157552 : covered 157552 157633 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b157633 : covered 157633 157714 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b157714 : covered 157714 157795 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b157795 : covered 157795 157877 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b157877 : covered 157877 157958 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b157958 : covered 157958 158040 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b158040 : covered 158040 158121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b158121 : covered 158121 158203 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b158203 : covered 158203 158284 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b158284 : covered 158284 158365 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b158365 : covered 158365 158446 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b158446 : covered 158446 158528 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b158528 : covered 158528 158609 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b158609 : covered 158609 158691 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b158691 : covered 158691 158772 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b158772 : covered 158772 158854 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b158854 : covered 158854 158935 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b158935 : covered 158935 159016 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159016 : covered 159016 159097 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159097 : covered 159097 159179 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159179 : covered 159179 159260 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159260 : covered 159260 159342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159342 : covered 159342 159423 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159423 : covered 159423 159505 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159505 : covered 159505 159586 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159586 : covered 159586 159667 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159667 : covered 159667 159748 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159748 : covered 159748 159830 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159830 : covered 159830 159911 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159911 : covered 159911 159993 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b159993 : covered 159993 160074 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b160074 : covered 160074 160156 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b160156 : covered 160156 160237 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b160237 : covered 160237 160318 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b160318 : covered 160318 160399 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b160399 : covered 160399 160481 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b160481 : covered 160481 160562 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b160562 : covered 160562 160644 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b160644 : covered 160644 160725 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b160725 : covered 160725 160807 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b160807 : covered 160807 160888 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b160888 : covered 160888 160969 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b160969 : covered 160969 161050 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b161050 : covered 161050 161132 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b161132 : covered 161132 161213 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b161213 : covered 161213 161295 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b161295 : covered 161295 161376 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b161376 : covered 161376 161458 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b161458 : covered 161458 161539 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b161539 : covered 161539 161620 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b161620 : covered 161620 161701 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b161701 : covered 161701 161783 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b161783 : covered 161783 161864 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b161864 : covered 161864 161946 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b161946 : covered 161946 162027 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b162027 : covered 162027 162109 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b162109 : covered 162109 162190 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b162190 : covered 162190 162271 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b162271 : covered 162271 162352 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b162352 : covered 162352 162434 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b162434 : covered 162434 162515 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b162515 : covered 162515 162597 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b162597 : covered 162597 162678 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b162678 : covered 162678 162760 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b162760 : covered 162760 162841 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b162841 : covered 162841 162922 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b162922 : covered 162922 163003 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163003 : covered 163003 163085 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163085 : covered 163085 163166 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163166 : covered 163166 163248 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163248 : covered 163248 163329 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163329 : covered 163329 163411 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163411 : covered 163411 163492 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163492 : covered 163492 163573 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163573 : covered 163573 163654 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163654 : covered 163654 163736 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163736 : covered 163736 163817 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163817 : covered 163817 163899 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163899 : covered 163899 163980 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b163980 : covered 163980 164062 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b164062 : covered 164062 164143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b164143 : covered 164143 164224 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b164224 : covered 164224 164305 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b164305 : covered 164305 164387 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b164387 : covered 164387 164468 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b164468 : covered 164468 164550 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b164550 : covered 164550 164631 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b164631 : covered 164631 164713 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b164713 : covered 164713 164794 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b164794 : covered 164794 164875 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b164875 : covered 164875 164956 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b164956 : covered 164956 165038 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b165038 : covered 165038 165119 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b165119 : covered 165119 165201 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b165201 : covered 165201 165282 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b165282 : covered 165282 165364 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b165364 : covered 165364 165445 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b165445 : covered 165445 165526 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b165526 : covered 165526 165607 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b165607 : covered 165607 165689 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b165689 : covered 165689 165770 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b165770 : covered 165770 165852 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b165852 : covered 165852 165933 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b165933 : covered 165933 166015 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b166015 : covered 166015 166096 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b166096 : covered 166096 166178 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b166178 : covered 166178 166259 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b166259 : covered 166259 166341 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b166341 : covered 166341 166422 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b166422 : covered 166422 166504 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b166504 : covered 166504 166585 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b166585 : covered 166585 166667 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 153645 166667 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b153645 b153726) (joinCoverage b153807 (joinCoverage b153888 b153970))) (joinCoverage (joinCoverage b154051 b154133) (joinCoverage b154214 (joinCoverage b154296 b154377)))) (joinCoverage (joinCoverage (joinCoverage b154458 b154539) (joinCoverage b154621 (joinCoverage b154702 b154784))) (joinCoverage (joinCoverage b154865 b154947) (joinCoverage b155028 (joinCoverage b155109 b155190))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b155272 b155353) (joinCoverage b155435 (joinCoverage b155516 b155598))) (joinCoverage (joinCoverage b155679 b155761) (joinCoverage b155842 (joinCoverage b155924 b156005)))) (joinCoverage (joinCoverage (joinCoverage b156087 b156168) (joinCoverage b156250 (joinCoverage b156331 b156412))) (joinCoverage (joinCoverage b156493 b156575) (joinCoverage b156656 (joinCoverage b156738 b156819)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b156901 b156982) (joinCoverage b157063 (joinCoverage b157144 b157226))) (joinCoverage (joinCoverage b157307 b157389) (joinCoverage b157470 (joinCoverage b157552 b157633)))) (joinCoverage (joinCoverage (joinCoverage b157714 b157795) (joinCoverage b157877 (joinCoverage b157958 b158040))) (joinCoverage (joinCoverage b158121 b158203) (joinCoverage b158284 (joinCoverage b158365 b158446))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b158528 b158609) (joinCoverage b158691 (joinCoverage b158772 b158854))) (joinCoverage (joinCoverage b158935 b159016) (joinCoverage b159097 (joinCoverage b159179 b159260)))) (joinCoverage (joinCoverage (joinCoverage b159342 b159423) (joinCoverage b159505 (joinCoverage b159586 b159667))) (joinCoverage (joinCoverage b159748 b159830) (joinCoverage b159911 (joinCoverage b159993 b160074))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b160156 b160237) (joinCoverage b160318 (joinCoverage b160399 b160481))) (joinCoverage (joinCoverage b160562 b160644) (joinCoverage b160725 (joinCoverage b160807 b160888)))) (joinCoverage (joinCoverage (joinCoverage b160969 b161050) (joinCoverage b161132 (joinCoverage b161213 b161295))) (joinCoverage (joinCoverage b161376 b161458) (joinCoverage b161539 (joinCoverage b161620 b161701))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b161783 b161864) (joinCoverage b161946 (joinCoverage b162027 b162109))) (joinCoverage (joinCoverage b162190 b162271) (joinCoverage b162352 (joinCoverage b162434 b162515)))) (joinCoverage (joinCoverage (joinCoverage b162597 b162678) (joinCoverage b162760 (joinCoverage b162841 b162922))) (joinCoverage (joinCoverage b163003 b163085) (joinCoverage b163166 (joinCoverage b163248 b163329)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b163411 b163492) (joinCoverage b163573 (joinCoverage b163654 b163736))) (joinCoverage (joinCoverage b163817 b163899) (joinCoverage b163980 (joinCoverage b164062 b164143)))) (joinCoverage (joinCoverage (joinCoverage b164224 b164305) (joinCoverage b164387 (joinCoverage b164468 b164550))) (joinCoverage (joinCoverage b164631 b164713) (joinCoverage b164794 (joinCoverage b164875 b164956))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b165038 b165119) (joinCoverage b165201 (joinCoverage b165282 b165364))) (joinCoverage (joinCoverage b165445 b165526) (joinCoverage b165607 (joinCoverage b165689 b165770)))) (joinCoverage (joinCoverage (joinCoverage b165852 b165933) (joinCoverage b166015 (joinCoverage b166096 b166178))) (joinCoverage (joinCoverage b166259 b166341) (joinCoverage b166422 (joinCoverage b166504 b166585))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 153645 ≤ index 295000000/512 := by decide +kernel
private theorem starting_value : fast 295000000=15996202 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 295000000=15996202) (n : ℕ) (low : 295000000≤n) (bound : n≤320000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=295000000
    · rw [first,anchor]
      exact starting_value
    · have past : 295000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤320000000 by omega)
        have within : index n / 512 < 166667 := by omega
        have lower : index 295000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤320000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ295000000To320000000
