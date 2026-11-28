import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ445000000To470000000

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




private def radical : ℕ := 0x56048585ad736393127a9c0c2022dcf3278b23a34bfe2039b98598ecb03073a89b9f20eb857cdc0f04b2808460a686a46099e6f78870b40aecd6011d16d0d8ae3195bca0f49eedf7967a6c107b795c5ccbf3f0d9b213aea9c19acb27e581b5cbbd7984a35816be189b0e1e535245c84d29c64e7d34e16b492fd58e3e83d98ed1e87fc35c4c3f2168818e39ddaaaedd86a496c4d5af638a4b0d56a6c750520af3917850f6601ebda318534563620919dccff15aec0295546a5f0a301a286a687142978f9f48e7784f8c99ebe22868716727af34c82fd0e3367a437b4371ce9a68c2f50294478cfe842e9f84ca0aa6aae3d3df77fb62344e79794ad8e37848baf3c3a8b5bf25b9d90d4f0eab059f71abe04cd277b07d9d23a1bc259ee9f2ddeca74894fb75886420ba9f8986b0903b85849bb3c1321b928e1a03d6791f779f512f0a09edbf9f314e3707185c9db1c3d0545f8ec53194078dba0d795f82a7e3aaacae89c5555668a8a55dab37cbcf2a40480a179b06558b34e68009e6cffe9bdf764353aa44288b491661a4cbb24a5ebf124c051cdd92702a87648ecce515dfc568e1d270e5252bb86ff97e75bcea660f010736096337e01108bc5b34f01ac717c4281ffc6a9eeb697da222cdf8a3c9c84eaf555741d30d9f1ec464b0cfab57ed02359601d0d161ace8287413874fdd8b06d3e1d71c57ad1c4194e13d92acd9768e94f7eaa7dcc2ee3ee9bfb8ca153d27938fb331aaf68472142c5c668d9fdad514f79c0e9d048d75f823373a357d68888bef249b8032d3ffbe9b3a5dfbdee35a6eb0789d9cf5e31388a5da9ad78586a614af0ee3a8a19350ded56d50bb1d5ab530b862d41d0ba4b771a53120818dd02300c0d75dcbb248ce158a8277a789df73d372a83cd7e900d9d176dad63c84a7776f06df29473bf112247866a03d01e1b969996e87898869bf6ecd1276f4913f60bc24f4ff0f765ef5410eb47fa959376b428b8642547d579dadff426c7472f1d239813c8908a707bdc3f9b580185e8316f25560b04055231cf99cb0bdb377db24e08b15ce078ff3f11ef85cfc61fef310e0280c4d4642e0f02a917939f63d65b682b17ea56978fe7b93dc4922ffe788e9b855da985924e6328062a7422fb2466f454f4ffaff5dac9ce63f8609ab5735a2f9a65c058977da635c07cd03f002589813906bc4bf2ac61dedcb8f5b7c3551325335a7ea5dfa40b02f603d3ddc6629bcadbc94dbd0400fc01c15cd6794dad6bddaf05df11dbbdbb87e0f78dc59b1c3bd98e6b66bbffcb77bf44fa6e23c0f08cc3302282b21ffeb08bc114636f6b46b756048ab496cdd498ec7cec28af7e9710630322f88c6144c35a20020fd63d38ce9cefa96b3b10288dd343a5630cdaa17d8575303fdce575341b01fe8e59ff8c6935339cd554fd3be315c706af082487202eb6d4d17f31f967632e6c198fa405f0fdb568b11ebadbd5505869df79a1967b9c5003933ebd88151bdb645d2c07773e5c0e8e9bf1584f97f35fd6c596bdfa638a9abde1613cb7e13247c8b1501fd0f0ea75d1bbf551603251059fbc5773b473f6e8c93fd8d07c22afcf7964b255f5a2b68e39719ce889b0cf35b961d1d54a28666986c9981dfb3101838c0a13e513e7a9e84b84c7cdcea2f52cd8ef3b6df122add7ba7e246f5931c808e7d1530a4b250db2634d9c24c760daaac7f125b38e2c07471c999eeb5c91eec3a431c26e2a417dda27f5fa310b05d2bc0cbf8963547cb8765d8778c90be7f79450ff2f9052f67321347aad9a0c4e635e7df1ffcfa06185bc0453c02260620c2df224f5eebab372b5aa9e3c32002dc5b1567011ce9f4bca449f597c12ea46cb8d2640396944e09c52619c7c5ab7da35175f6914f4cf61dba696c7a87465a2e7d4edbd5f6fec200a392d7a4c4ddf611010a7734c5ec2665afa3bbfb1c842ebc490004348061b82248cdafebbf8f0f2acd1144f93f4bc8c61c87dd6167830825df55bf27e36c3296645213f09a52439fdf194a132c50c910ad821b3d3b90b54d6097e221cc495c02da642171e2247c99d2e7dd3722353c194719d3e1bebc2ea3e33fe58602d78772e7fb312da4fbc400390f71287ece0293f300b750c321b491b526e3743b9cb3fb0ecb1c744e0aa92a173de705d20c2a8bfc7b115f0b164dfa5f29bb8aa1411f4098100b0fa91a26b64ee787e17e3868e80fe44d8ae90c28e6386189946a8d3b097bf06ce40f8debff98cda95898313efd653680f7ebe700ce9c131b5be35c613d116bbf27610c2bf5e25b281048118eba338e56e137e9ce4d76f059c234c3290379b9de7a420aed9856d84590f86113e2119c1efcfd36b30b0f5eaf6af0c68ad558377d36ab066228b31c67b75163a7830115b2935bb5bf0795dd833b2c78b7dfe981b0bd30c6fac3487a3c8178d0560232ce99c5e22bb98ad47a08b3a240f3a5f5a25942a9e50d547bd5ebfabf9dbb77f3527bca5d48872125f34b3be8c9577d1915cf54861d02b3be3544e639c4e3444da1497cf08486c25c39250cc86996613a7abe3d6ddfbe4edb6f1d610c030c2632ad2e2622b493e183f512cfb38017e87ba304b017aba0c849f92f160c16e05d79c9af4355e3a40ab9c07988194d6ee47844447ab6d7978cc718d600972644986afbd74613325b734c5eaa8d4209637b2266f48df3d3bfe21d5f632243d37d5af27d35139c3fea8f4a81116e944490a39caec2fbf9063cf7394f1492b3f8652c2f7a2c3d5bedd52c61597d5e6125883a23a01a5d2f711e851eeee979c4eeccf87cf1333368b96ede3e26ed552bda5a275adb3ad3ebfcfa0589afd6a1249ff18c77dfe1da2578fdb3f05612967588b744ec4af2e64ee8f4ae519ea2048252bcd9879a2d860bb0949330604d704b71dfeddc0423523c10cb4adda33921ad532ee223137ac07708aa5155ab283f6a96e8a2a469980047d655c65a88fabb37c70956aa34241104e1859d7e4759160ecd234e6579e222c1c2d9d21bb30d528cd995d46edf7751e4ad42561f692486a65e15e4ffeb964a1bec10f64fcb7619dfc44cb6672b44675542c3a4e90c10f02cec03082e49ebacafe93d56b3334abfba6d33d7eae5399e902cbb1c71930a67ef60160ccc55a451205ab51ad1a2b87078c197a1de3b2e00700e6dd3556175dbc229bbe377066a56e8387676c7ed1e27915d1d2dbda1d5b5dc75067646df7321d8f6358e5a460f7ba578e566f04ab192da4e76ee91c0d44ebb20df6e66173898746acdf917943891ae494bde9e954f00c06a622cc6f65d4ea0b5f4d4f472e089a39ee60d318fb052eabd7ece66f1b5636675aea4cdd4ff5dc2132fe89525b30c8e61b7cc923fa7878e72dd06dcf5b1b8ead71a5a8b03ed0a0bf3163b732b8355b9303c9d65a684138347bc13a9bc93f7db00c972d5fff6e33637f764fb16a8e678b682a42233f2a6b99d03ebc5ac9fd4f4276a68f02df7d78294532ad0d17db25333e12c7cfda74879821c8c0fdc8eafafd3bbe9e67b6824eb0276e8b474082f8a285cb9c123cf6f4acd94a546c2bbf1fa219fa1d1505ee46191045fc951c6e25a00ba675b81fe61653aa4837de34fcf6c0a954bbda0180d427ea86c8eb9498b37c80a265bca3a24a305153f653e8ab89d17298beb62eb1aa6d862ad420963cc02736e955acbe328c677181b93e4916344dbf6abd1493771ebfd7c1e4a2255bc0fb41d1e39c5170d6f8fe942612e5ff7f51bbbf565c4298763975e14bb50863b57b157c441eef0a371513b9e85e4298276f08b83bb3603e7ff5a180578365d033b88e4e68f6179bee406ca1c8fac634a0f983034ce369fce90232369ef31d7144788d570822315f6a10070453acd57231cf738ab7979588fdcefe21a9dd057d977f715f58529cf00ea99e0387c7b78f4d2fa81ec84cf086225ab6f7eb6ee4fb30d4adfe709bbb11a16dff1bdcca7d8335b295a3db37f18057647a1d458828030e14ee5a205e9afeb589d4b5c8bc5da5facc1576700c0e236233f46408bf146955597b0d447bc4f27ce734e7f8de6920293e4188ef15c6296a0bcfbf21979b3408ddbe3b819c626eb99bee64643ea26f70e48af97fa13f417f1d9508e9ba2b49072c4ab65e0b8a9c9a69f7104bd02588f18295c1fbb442019a4e84e94dbabbc621df3a0d149e5cc9f9b0e3c88014ecd5441fcaaf54c0f29201d11f631c2e3156425c5093a9b61268e9ff327efa17fc3f562133a532b4ad424165ba43e33c9e24a9a6bf1d5f348d8c437cb3c65878bb908a5a3ce487b224ee4cd5f9261f6ba9a7aa44e75b4587492b4f6a4ced336310fb58c0b58d28e71f57481e2cbd5702420fa9889592bc79f621f99171e3afe8ae12451ab6c7bcab84454c9b1c0865aac3c156d84e2ae819b8fc9ed627953dfee89f2ead77a28cdd2cf018221c604418cfdef5a92edaa7857f1a45fd697d75d58e772d058d013e71812580c02636e179e45a60afc12e144745aa3762f680a5ca834610ff468f330f87e952e16fb29d7f2feed23c7ee2376987c3b7ef9f304ea892b93c5798c4cf683253486a0b93eeb1ba0c0d0b964cea9ae0049e4bc1731c63a2a373db3308563718768458f5e3ee75d11ed94c0b4bb03229f0312d8d1bf3c6522ca887300c0862ab7a0791317fa4f6580039f4cc7feb5a5ba47e26de8a73b65770dd12a5059e5b124157563bc34fd6fbe6ffa301d75d57678693cf815ce8253510600a9628beee930a223c117dadcdfa166814dc67d14d9c55bd1ee15733288de86955ba33524561f012f10a5ee4fe605f07c921bdd666ffbe3067339a25e000b7512f52488beea4f29938fd396d18da4bf79643d1457d789808a4cb333388ad913a4ecdcda9718135ec0fc4c19f6e378188350e685ddd0e79b73f861932515161ce5453dcc02ce89cad6c0c58ddb4955f091876983936b1b9d4d81ce2522212a9bcc03cc38ec57fad36e11d45488fae8c75c522dbb4edfa48d3763aed1299882fdc3a99c6cac92856e4211b925ced7a2a180a0ed2109f6ca8d9d6304d3848dacca61704f39900b85df9039ce4ea838740ed7a97417d1ec7d6b73330cc385573b155496ea7e7549ee628b2f6997f6c723ec915a0bb1e4a0c72e27e4b9296c0a0445ed9a14ecbd6ccdf5f13a91b71c543cb4c717b411d0ad173df2b0b794c72bb37eee16a830e4579035ec22655a842b1e6cd34f3ca32d6e24c45b87f8d3e2f0c121b22d7c934ff7b583c40d2242d8fe414ab235f474044b5898c0f0c355d1c3cab58e953d8b2f0e1963d0f9a73c8e3be53399a5f8dfb047abe63ccd7998d5323f8ee49a5b97e8c88ae5a92b7d3749a2f53efcf25c1af136ebf9ecb77571cae825235ddfb2b7dc840e42c31d891df0aebf5c8f14567663f742325725bf8d3c38a387f9f4e7f02669e431d0f4b87ac7ec18c1a4b57dc3c75a2fe242575c45b1c922d3d13d800b540cf6a4474c75a

private def light (n : ℕ) : Bool :=
  if n≤147 then decide n.Prime else n.gcd 17272458904546389112034986593086202319334765035978978227990923221833190980363201642519673042105118551719302218618675314155228928653088005461743741821126448568517622617974417718521481737240752909004600275325629858346067558400000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤21679) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 147 = 17272458904546389112034986593086202319334765035978978227990923221833190980363201642519673042105118551719302218618675314155228928653088005461743741821126448568517622617974417718521481737240752909004600275325629858346067558400000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 147 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤21679 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 42 := by unfold smallValid; decide +kernel

private theorem sp42 : smallValid 42 42 := by unfold smallValid; decide +kernel

private theorem sp84 : smallValid 84 42 := by unfold smallValid; decide +kernel

private theorem sp126 : smallValid 126 43 := by unfold smallValid; decide +kernel

private theorem sp169 : smallValid 169 42 := by unfold smallValid; decide +kernel

private theorem sp211 : smallValid 211 42 := by unfold smallValid; decide +kernel

private theorem sp253 : smallValid 253 42 := by unfold smallValid; decide +kernel

private theorem sp295 : smallValid 295 43 := by unfold smallValid; decide +kernel

private theorem sp338 : smallValid 338 42 := by unfold smallValid; decide +kernel

private theorem sp380 : smallValid 380 42 := by unfold smallValid; decide +kernel

private theorem sp422 : smallValid 422 42 := by unfold smallValid; decide +kernel

private theorem sp464 : smallValid 464 43 := by unfold smallValid; decide +kernel

private theorem sp507 : smallValid 507 42 := by unfold smallValid; decide +kernel

private theorem sp549 : smallValid 549 43 := by unfold smallValid; decide +kernel

private theorem sp592 : smallValid 592 42 := by unfold smallValid; decide +kernel

private theorem sp634 : smallValid 634 43 := by unfold smallValid; decide +kernel

private theorem sp677 : smallValid 677 42 := by unfold smallValid; decide +kernel

private theorem sp719 : smallValid 719 42 := by unfold smallValid; decide +kernel

private theorem sp761 : smallValid 761 42 := by unfold smallValid; decide +kernel

private theorem sp803 : smallValid 803 43 := by unfold smallValid; decide +kernel

private theorem sp846 : smallValid 846 42 := by unfold smallValid; decide +kernel

private theorem sp888 : smallValid 888 43 := by unfold smallValid; decide +kernel

private theorem sp931 : smallValid 931 42 := by unfold smallValid; decide +kernel

private theorem sp973 : smallValid 973 43 := by unfold smallValid; decide +kernel

private theorem sp1016 : smallValid 1016 42 := by unfold smallValid; decide +kernel

private theorem sp1058 : smallValid 1058 42 := by unfold smallValid; decide +kernel

private theorem sp1100 : smallValid 1100 42 := by unfold smallValid; decide +kernel

private theorem sp1142 : smallValid 1142 43 := by unfold smallValid; decide +kernel

private theorem sp1185 : smallValid 1185 42 := by unfold smallValid; decide +kernel

private theorem sp1227 : smallValid 1227 43 := by unfold smallValid; decide +kernel

private theorem sp1270 : smallValid 1270 42 := by unfold smallValid; decide +kernel

private theorem sp1312 : smallValid 1312 43 := by unfold smallValid; decide +kernel

private theorem sp1355 : smallValid 1355 42 := by unfold smallValid; decide +kernel

private theorem sp1397 : smallValid 1397 42 := by unfold smallValid; decide +kernel

private theorem sp1439 : smallValid 1439 42 := by unfold smallValid; decide +kernel

private theorem sp1481 : smallValid 1481 43 := by unfold smallValid; decide +kernel

private theorem sp1524 : smallValid 1524 42 := by unfold smallValid; decide +kernel

private theorem sp1566 : smallValid 1566 42 := by unfold smallValid; decide +kernel

private theorem sp1608 : smallValid 1608 42 := by unfold smallValid; decide +kernel

private theorem sp1650 : smallValid 1650 43 := by unfold smallValid; decide +kernel

private theorem sp1693 : smallValid 1693 42 := by unfold smallValid; decide +kernel

private theorem sp1735 : smallValid 1735 42 := by unfold smallValid; decide +kernel

private theorem sp1777 : smallValid 1777 42 := by unfold smallValid; decide +kernel

private theorem sp1819 : smallValid 1819 43 := by unfold smallValid; decide +kernel

private theorem sp1862 : smallValid 1862 42 := by unfold smallValid; decide +kernel

private theorem sp1904 : smallValid 1904 43 := by unfold smallValid; decide +kernel

private theorem sp1947 : smallValid 1947 42 := by unfold smallValid; decide +kernel

private theorem sp1989 : smallValid 1989 43 := by unfold smallValid; decide +kernel

private theorem sp2032 : smallValid 2032 42 := by unfold smallValid; decide +kernel

private theorem sp2074 : smallValid 2074 42 := by unfold smallValid; decide +kernel

private theorem sp2116 : smallValid 2116 42 := by unfold smallValid; decide +kernel

private theorem sp2158 : smallValid 2158 43 := by unfold smallValid; decide +kernel

private theorem sp2201 : smallValid 2201 42 := by unfold smallValid; decide +kernel

private theorem sp2243 : smallValid 2243 43 := by unfold smallValid; decide +kernel

private theorem sp2286 : smallValid 2286 42 := by unfold smallValid; decide +kernel

private theorem sp2328 : smallValid 2328 43 := by unfold smallValid; decide +kernel

private theorem sp2371 : smallValid 2371 42 := by unfold smallValid; decide +kernel

private theorem sp2413 : smallValid 2413 42 := by unfold smallValid; decide +kernel

private theorem sp2455 : smallValid 2455 42 := by unfold smallValid; decide +kernel

private theorem sp2497 : smallValid 2497 43 := by unfold smallValid; decide +kernel

private theorem sp2540 : smallValid 2540 42 := by unfold smallValid; decide +kernel

private theorem sp2582 : smallValid 2582 43 := by unfold smallValid; decide +kernel

private theorem sp2625 : smallValid 2625 42 := by unfold smallValid; decide +kernel

private theorem sp2667 : smallValid 2667 43 := by unfold smallValid; decide +kernel

private theorem sp2710 : smallValid 2710 42 := by unfold smallValid; decide +kernel

private theorem sp2752 : smallValid 2752 42 := by unfold smallValid; decide +kernel

private theorem sp2794 : smallValid 2794 42 := by unfold smallValid; decide +kernel

private theorem sp2836 : smallValid 2836 43 := by unfold smallValid; decide +kernel

private theorem sp2879 : smallValid 2879 42 := by unfold smallValid; decide +kernel

private theorem sp2921 : smallValid 2921 42 := by unfold smallValid; decide +kernel

private theorem sp2963 : smallValid 2963 42 := by unfold smallValid; decide +kernel

private theorem sp3005 : smallValid 3005 43 := by unfold smallValid; decide +kernel

private theorem sp3048 : smallValid 3048 42 := by unfold smallValid; decide +kernel

private theorem sp3090 : smallValid 3090 42 := by unfold smallValid; decide +kernel

private theorem sp3132 : smallValid 3132 42 := by unfold smallValid; decide +kernel

private theorem sp3174 : smallValid 3174 43 := by unfold smallValid; decide +kernel

private theorem sp3217 : smallValid 3217 42 := by unfold smallValid; decide +kernel

private theorem sp3259 : smallValid 3259 43 := by unfold smallValid; decide +kernel

private theorem sp3302 : smallValid 3302 42 := by unfold smallValid; decide +kernel

private theorem sp3344 : smallValid 3344 43 := by unfold smallValid; decide +kernel

private theorem sp3387 : smallValid 3387 42 := by unfold smallValid; decide +kernel

private theorem sp3429 : smallValid 3429 42 := by unfold smallValid; decide +kernel

private theorem sp3471 : smallValid 3471 42 := by unfold smallValid; decide +kernel

private theorem sp3513 : smallValid 3513 43 := by unfold smallValid; decide +kernel

private theorem sp3556 : smallValid 3556 42 := by unfold smallValid; decide +kernel

private theorem sp3598 : smallValid 3598 43 := by unfold smallValid; decide +kernel

private theorem sp3641 : smallValid 3641 42 := by unfold smallValid; decide +kernel

private theorem sp3683 : smallValid 3683 43 := by unfold smallValid; decide +kernel

private theorem sp3726 : smallValid 3726 42 := by unfold smallValid; decide +kernel

private theorem sp3768 : smallValid 3768 42 := by unfold smallValid; decide +kernel

private theorem sp3810 : smallValid 3810 42 := by unfold smallValid; decide +kernel

private theorem sp3852 : smallValid 3852 43 := by unfold smallValid; decide +kernel

private theorem sp3895 : smallValid 3895 42 := by unfold smallValid; decide +kernel

private theorem sp3937 : smallValid 3937 43 := by unfold smallValid; decide +kernel

private theorem sp3980 : smallValid 3980 42 := by unfold smallValid; decide +kernel

private theorem sp4022 : smallValid 4022 43 := by unfold smallValid; decide +kernel

private theorem sp4065 : smallValid 4065 42 := by unfold smallValid; decide +kernel

private theorem sp4107 : smallValid 4107 42 := by unfold smallValid; decide +kernel

private theorem sp4149 : smallValid 4149 42 := by unfold smallValid; decide +kernel

private theorem sp4191 : smallValid 4191 43 := by unfold smallValid; decide +kernel

private theorem sp4234 : smallValid 4234 42 := by unfold smallValid; decide +kernel

private theorem sp4276 : smallValid 4276 42 := by unfold smallValid; decide +kernel

private theorem sp4318 : smallValid 4318 42 := by unfold smallValid; decide +kernel

private theorem sp4360 : smallValid 4360 43 := by unfold smallValid; decide +kernel

private theorem sp4403 : smallValid 4403 42 := by unfold smallValid; decide +kernel

private theorem sp4445 : smallValid 4445 42 := by unfold smallValid; decide +kernel

private theorem sp4487 : smallValid 4487 42 := by unfold smallValid; decide +kernel

private theorem sp4529 : smallValid 4529 43 := by unfold smallValid; decide +kernel

private theorem sp4572 : smallValid 4572 42 := by unfold smallValid; decide +kernel

private theorem sp4614 : smallValid 4614 43 := by unfold smallValid; decide +kernel

private theorem sp4657 : smallValid 4657 42 := by unfold smallValid; decide +kernel

private theorem sp4699 : smallValid 4699 43 := by unfold smallValid; decide +kernel

private theorem sp4742 : smallValid 4742 42 := by unfold smallValid; decide +kernel

private theorem sp4784 : smallValid 4784 42 := by unfold smallValid; decide +kernel

private theorem sp4826 : smallValid 4826 42 := by unfold smallValid; decide +kernel

private theorem sp4868 : smallValid 4868 43 := by unfold smallValid; decide +kernel

private theorem sp4911 : smallValid 4911 42 := by unfold smallValid; decide +kernel

private theorem sp4953 : smallValid 4953 43 := by unfold smallValid; decide +kernel

private theorem sp4996 : smallValid 4996 42 := by unfold smallValid; decide +kernel

private theorem sp5038 : smallValid 5038 43 := by unfold smallValid; decide +kernel

private theorem sp5081 : smallValid 5081 42 := by unfold smallValid; decide +kernel

private theorem sp5123 : smallValid 5123 42 := by unfold smallValid; decide +kernel

private theorem sp5165 : smallValid 5165 42 := by unfold smallValid; decide +kernel

private theorem sp5207 : smallValid 5207 43 := by unfold smallValid; decide +kernel

private theorem sp5250 : smallValid 5250 42 := by unfold smallValid; decide +kernel

private theorem sp5292 : smallValid 5292 43 := by unfold smallValid; decide +kernel

private theorem sp5335 : smallValid 5335 42 := by unfold smallValid; decide +kernel

private theorem sp5377 : smallValid 5377 43 := by unfold smallValid; decide +kernel

private theorem sp5420 : smallValid 5420 42 := by unfold smallValid; decide +kernel

private theorem sp5462 : smallValid 5462 42 := by unfold smallValid; decide +kernel

private theorem sp5504 : smallValid 5504 42 := by unfold smallValid; decide +kernel

private theorem sp5546 : smallValid 5546 43 := by unfold smallValid; decide +kernel

private theorem sp5589 : smallValid 5589 42 := by unfold smallValid; decide +kernel

private theorem sp5631 : smallValid 5631 42 := by unfold smallValid; decide +kernel

private theorem sp5673 : smallValid 5673 42 := by unfold smallValid; decide +kernel

private theorem sp5715 : smallValid 5715 43 := by unfold smallValid; decide +kernel

private theorem sp5758 : smallValid 5758 42 := by unfold smallValid; decide +kernel

private theorem sp5800 : smallValid 5800 42 := by unfold smallValid; decide +kernel

private theorem sp5842 : smallValid 5842 42 := by unfold smallValid; decide +kernel

private theorem sp5884 : smallValid 5884 43 := by unfold smallValid; decide +kernel

private theorem sp5927 : smallValid 5927 42 := by unfold smallValid; decide +kernel

private theorem sp5969 : smallValid 5969 43 := by unfold smallValid; decide +kernel

private theorem sp6012 : smallValid 6012 42 := by unfold smallValid; decide +kernel

private theorem sp6054 : smallValid 6054 43 := by unfold smallValid; decide +kernel

private theorem sp6097 : smallValid 6097 42 := by unfold smallValid; decide +kernel

private theorem sp6139 : smallValid 6139 42 := by unfold smallValid; decide +kernel

private theorem sp6181 : smallValid 6181 42 := by unfold smallValid; decide +kernel

private theorem sp6223 : smallValid 6223 43 := by unfold smallValid; decide +kernel

private theorem sp6266 : smallValid 6266 42 := by unfold smallValid; decide +kernel

private theorem sp6308 : smallValid 6308 43 := by unfold smallValid; decide +kernel

private theorem sp6351 : smallValid 6351 42 := by unfold smallValid; decide +kernel

private theorem sp6393 : smallValid 6393 43 := by unfold smallValid; decide +kernel

private theorem sp6436 : smallValid 6436 42 := by unfold smallValid; decide +kernel

private theorem sp6478 : smallValid 6478 42 := by unfold smallValid; decide +kernel

private theorem sp6520 : smallValid 6520 42 := by unfold smallValid; decide +kernel

private theorem sp6562 : smallValid 6562 43 := by unfold smallValid; decide +kernel

private theorem sp6605 : smallValid 6605 42 := by unfold smallValid; decide +kernel

private theorem sp6647 : smallValid 6647 43 := by unfold smallValid; decide +kernel

private theorem sp6690 : smallValid 6690 42 := by unfold smallValid; decide +kernel

private theorem sp6732 : smallValid 6732 43 := by unfold smallValid; decide +kernel

private theorem sp6775 : smallValid 6775 42 := by unfold smallValid; decide +kernel

private theorem sp6817 : smallValid 6817 42 := by unfold smallValid; decide +kernel

private theorem sp6859 : smallValid 6859 42 := by unfold smallValid; decide +kernel

private theorem sp6901 : smallValid 6901 43 := by unfold smallValid; decide +kernel

private theorem sp6944 : smallValid 6944 42 := by unfold smallValid; decide +kernel

private theorem sp6986 : smallValid 6986 42 := by unfold smallValid; decide +kernel

private theorem sp7028 : smallValid 7028 42 := by unfold smallValid; decide +kernel

private theorem sp7070 : smallValid 7070 43 := by unfold smallValid; decide +kernel

private theorem sp7113 : smallValid 7113 42 := by unfold smallValid; decide +kernel

private theorem sp7155 : smallValid 7155 42 := by unfold smallValid; decide +kernel

private theorem sp7197 : smallValid 7197 42 := by unfold smallValid; decide +kernel

private theorem sp7239 : smallValid 7239 43 := by unfold smallValid; decide +kernel

private theorem sp7282 : smallValid 7282 42 := by unfold smallValid; decide +kernel

private theorem sp7324 : smallValid 7324 43 := by unfold smallValid; decide +kernel

private theorem sp7367 : smallValid 7367 42 := by unfold smallValid; decide +kernel

private theorem sp7409 : smallValid 7409 43 := by unfold smallValid; decide +kernel

private theorem sp7452 : smallValid 7452 42 := by unfold smallValid; decide +kernel

private theorem sp7494 : smallValid 7494 42 := by unfold smallValid; decide +kernel

private theorem sp7536 : smallValid 7536 42 := by unfold smallValid; decide +kernel

private theorem sp7578 : smallValid 7578 43 := by unfold smallValid; decide +kernel

private theorem sp7621 : smallValid 7621 42 := by unfold smallValid; decide +kernel

private theorem sp7663 : smallValid 7663 43 := by unfold smallValid; decide +kernel

private theorem sp7706 : smallValid 7706 42 := by unfold smallValid; decide +kernel

private theorem sp7748 : smallValid 7748 43 := by unfold smallValid; decide +kernel

private theorem sp7791 : smallValid 7791 42 := by unfold smallValid; decide +kernel

private theorem sp7833 : smallValid 7833 42 := by unfold smallValid; decide +kernel

private theorem sp7875 : smallValid 7875 42 := by unfold smallValid; decide +kernel

private theorem sp7917 : smallValid 7917 43 := by unfold smallValid; decide +kernel

private theorem sp7960 : smallValid 7960 42 := by unfold smallValid; decide +kernel

private theorem sp8002 : smallValid 8002 43 := by unfold smallValid; decide +kernel

private theorem sp8045 : smallValid 8045 42 := by unfold smallValid; decide +kernel

private theorem sp8087 : smallValid 8087 43 := by unfold smallValid; decide +kernel

private theorem sp8130 : smallValid 8130 42 := by unfold smallValid; decide +kernel

private theorem sp8172 : smallValid 8172 42 := by unfold smallValid; decide +kernel

private theorem sp8214 : smallValid 8214 42 := by unfold smallValid; decide +kernel

private theorem sp8256 : smallValid 8256 43 := by unfold smallValid; decide +kernel

private theorem sp8299 : smallValid 8299 42 := by unfold smallValid; decide +kernel

private theorem sp8341 : smallValid 8341 42 := by unfold smallValid; decide +kernel

private theorem sp8383 : smallValid 8383 42 := by unfold smallValid; decide +kernel

private theorem sp8425 : smallValid 8425 43 := by unfold smallValid; decide +kernel

private theorem sp8468 : smallValid 8468 42 := by unfold smallValid; decide +kernel

private theorem sp8510 : smallValid 8510 42 := by unfold smallValid; decide +kernel

private theorem sp8552 : smallValid 8552 42 := by unfold smallValid; decide +kernel

private theorem sp8594 : smallValid 8594 43 := by unfold smallValid; decide +kernel

private theorem sp8637 : smallValid 8637 42 := by unfold smallValid; decide +kernel

private theorem sp8679 : smallValid 8679 43 := by unfold smallValid; decide +kernel

private theorem sp8722 : smallValid 8722 42 := by unfold smallValid; decide +kernel

private theorem sp8764 : smallValid 8764 43 := by unfold smallValid; decide +kernel

private theorem sp8807 : smallValid 8807 42 := by unfold smallValid; decide +kernel

private theorem sp8849 : smallValid 8849 42 := by unfold smallValid; decide +kernel

private theorem sp8891 : smallValid 8891 42 := by unfold smallValid; decide +kernel

private theorem sp8933 : smallValid 8933 43 := by unfold smallValid; decide +kernel

private theorem sp8976 : smallValid 8976 42 := by unfold smallValid; decide +kernel

private theorem sp9018 : smallValid 9018 43 := by unfold smallValid; decide +kernel

private theorem sp9061 : smallValid 9061 42 := by unfold smallValid; decide +kernel

private theorem sp9103 : smallValid 9103 43 := by unfold smallValid; decide +kernel

private theorem sp9146 : smallValid 9146 42 := by unfold smallValid; decide +kernel

private theorem sp9188 : smallValid 9188 42 := by unfold smallValid; decide +kernel

private theorem sp9230 : smallValid 9230 42 := by unfold smallValid; decide +kernel

private theorem sp9272 : smallValid 9272 43 := by unfold smallValid; decide +kernel

private theorem sp9315 : smallValid 9315 42 := by unfold smallValid; decide +kernel

private theorem sp9357 : smallValid 9357 43 := by unfold smallValid; decide +kernel

private theorem sp9400 : smallValid 9400 42 := by unfold smallValid; decide +kernel

private theorem sp9442 : smallValid 9442 43 := by unfold smallValid; decide +kernel

private theorem sp9485 : smallValid 9485 42 := by unfold smallValid; decide +kernel

private theorem sp9527 : smallValid 9527 42 := by unfold smallValid; decide +kernel

private theorem sp9569 : smallValid 9569 42 := by unfold smallValid; decide +kernel

private theorem sp9611 : smallValid 9611 43 := by unfold smallValid; decide +kernel

private theorem sp9654 : smallValid 9654 42 := by unfold smallValid; decide +kernel

private theorem sp9696 : smallValid 9696 42 := by unfold smallValid; decide +kernel

private theorem sp9738 : smallValid 9738 42 := by unfold smallValid; decide +kernel

private theorem sp9780 : smallValid 9780 43 := by unfold smallValid; decide +kernel

private theorem sp9823 : smallValid 9823 42 := by unfold smallValid; decide +kernel

private theorem sp9865 : smallValid 9865 42 := by unfold smallValid; decide +kernel

private theorem sp9907 : smallValid 9907 42 := by unfold smallValid; decide +kernel

private theorem sp9949 : smallValid 9949 43 := by unfold smallValid; decide +kernel

private theorem sp9992 : smallValid 9992 42 := by unfold smallValid; decide +kernel

private theorem sp10034 : smallValid 10034 43 := by unfold smallValid; decide +kernel

private theorem sp10077 : smallValid 10077 42 := by unfold smallValid; decide +kernel

private theorem sp10119 : smallValid 10119 43 := by unfold smallValid; decide +kernel

private theorem sp10162 : smallValid 10162 42 := by unfold smallValid; decide +kernel

private theorem sp10204 : smallValid 10204 42 := by unfold smallValid; decide +kernel

private theorem sp10246 : smallValid 10246 42 := by unfold smallValid; decide +kernel

private theorem sp10288 : smallValid 10288 43 := by unfold smallValid; decide +kernel

private theorem sp10331 : smallValid 10331 42 := by unfold smallValid; decide +kernel

private theorem sp10373 : smallValid 10373 43 := by unfold smallValid; decide +kernel

private theorem sp10416 : smallValid 10416 42 := by unfold smallValid; decide +kernel

private theorem sp10458 : smallValid 10458 43 := by unfold smallValid; decide +kernel

private theorem sp10501 : smallValid 10501 42 := by unfold smallValid; decide +kernel

private theorem sp10543 : smallValid 10543 42 := by unfold smallValid; decide +kernel

private theorem sp10585 : smallValid 10585 42 := by unfold smallValid; decide +kernel

private theorem sp10627 : smallValid 10627 43 := by unfold smallValid; decide +kernel

private theorem sp10670 : smallValid 10670 42 := by unfold smallValid; decide +kernel

private theorem sp10712 : smallValid 10712 43 := by unfold smallValid; decide +kernel

private theorem sp10755 : smallValid 10755 42 := by unfold smallValid; decide +kernel

private theorem sp10797 : smallValid 10797 43 := by unfold smallValid; decide +kernel

private theorem sp10840 : smallValid 10840 42 := by unfold smallValid; decide +kernel

private theorem sp10882 : smallValid 10882 42 := by unfold smallValid; decide +kernel

private theorem sp10924 : smallValid 10924 42 := by unfold smallValid; decide +kernel

private theorem sp10966 : smallValid 10966 43 := by unfold smallValid; decide +kernel

private theorem sp11009 : smallValid 11009 42 := by unfold smallValid; decide +kernel

private theorem sp11051 : smallValid 11051 42 := by unfold smallValid; decide +kernel

private theorem sp11093 : smallValid 11093 42 := by unfold smallValid; decide +kernel

private theorem sp11135 : smallValid 11135 43 := by unfold smallValid; decide +kernel

private theorem sp11178 : smallValid 11178 42 := by unfold smallValid; decide +kernel

private theorem sp11220 : smallValid 11220 42 := by unfold smallValid; decide +kernel

private theorem sp11262 : smallValid 11262 42 := by unfold smallValid; decide +kernel

private theorem sp11304 : smallValid 11304 43 := by unfold smallValid; decide +kernel

private theorem sp11347 : smallValid 11347 42 := by unfold smallValid; decide +kernel

private theorem sp11389 : smallValid 11389 43 := by unfold smallValid; decide +kernel

private theorem sp11432 : smallValid 11432 42 := by unfold smallValid; decide +kernel

private theorem sp11474 : smallValid 11474 43 := by unfold smallValid; decide +kernel

private theorem sp11517 : smallValid 11517 42 := by unfold smallValid; decide +kernel

private theorem sp11559 : smallValid 11559 42 := by unfold smallValid; decide +kernel

private theorem sp11601 : smallValid 11601 42 := by unfold smallValid; decide +kernel

private theorem sp11643 : smallValid 11643 43 := by unfold smallValid; decide +kernel

private theorem sp11686 : smallValid 11686 42 := by unfold smallValid; decide +kernel

private theorem sp11728 : smallValid 11728 43 := by unfold smallValid; decide +kernel

private theorem sp11771 : smallValid 11771 42 := by unfold smallValid; decide +kernel

private theorem sp11813 : smallValid 11813 43 := by unfold smallValid; decide +kernel

private theorem sp11856 : smallValid 11856 42 := by unfold smallValid; decide +kernel

private theorem sp11898 : smallValid 11898 42 := by unfold smallValid; decide +kernel

private theorem sp11940 : smallValid 11940 42 := by unfold smallValid; decide +kernel

private theorem sp11982 : smallValid 11982 43 := by unfold smallValid; decide +kernel

private theorem sp12025 : smallValid 12025 42 := by unfold smallValid; decide +kernel

private theorem sp12067 : smallValid 12067 43 := by unfold smallValid; decide +kernel

private theorem sp12110 : smallValid 12110 42 := by unfold smallValid; decide +kernel

private theorem sp12152 : smallValid 12152 43 := by unfold smallValid; decide +kernel

private theorem sp12195 : smallValid 12195 42 := by unfold smallValid; decide +kernel

private theorem sp12237 : smallValid 12237 42 := by unfold smallValid; decide +kernel

private theorem sp12279 : smallValid 12279 42 := by unfold smallValid; decide +kernel

private theorem sp12321 : smallValid 12321 43 := by unfold smallValid; decide +kernel

private theorem sp12364 : smallValid 12364 42 := by unfold smallValid; decide +kernel

private theorem sp12406 : smallValid 12406 42 := by unfold smallValid; decide +kernel

private theorem sp12448 : smallValid 12448 42 := by unfold smallValid; decide +kernel

private theorem sp12490 : smallValid 12490 43 := by unfold smallValid; decide +kernel

private theorem sp12533 : smallValid 12533 42 := by unfold smallValid; decide +kernel

private theorem sp12575 : smallValid 12575 42 := by unfold smallValid; decide +kernel

private theorem sp12617 : smallValid 12617 42 := by unfold smallValid; decide +kernel

private theorem sp12659 : smallValid 12659 43 := by unfold smallValid; decide +kernel

private theorem sp12702 : smallValid 12702 42 := by unfold smallValid; decide +kernel

private theorem sp12744 : smallValid 12744 43 := by unfold smallValid; decide +kernel

private theorem sp12787 : smallValid 12787 42 := by unfold smallValid; decide +kernel

private theorem sp12829 : smallValid 12829 43 := by unfold smallValid; decide +kernel

private theorem sp12872 : smallValid 12872 42 := by unfold smallValid; decide +kernel

private theorem sp12914 : smallValid 12914 42 := by unfold smallValid; decide +kernel

private theorem sp12956 : smallValid 12956 42 := by unfold smallValid; decide +kernel

private theorem sp12998 : smallValid 12998 43 := by unfold smallValid; decide +kernel

private theorem sp13041 : smallValid 13041 42 := by unfold smallValid; decide +kernel

private theorem sp13083 : smallValid 13083 43 := by unfold smallValid; decide +kernel

private theorem sp13126 : smallValid 13126 42 := by unfold smallValid; decide +kernel

private theorem sp13168 : smallValid 13168 43 := by unfold smallValid; decide +kernel

private theorem sp13211 : smallValid 13211 42 := by unfold smallValid; decide +kernel

private theorem sp13253 : smallValid 13253 42 := by unfold smallValid; decide +kernel

private theorem sp13295 : smallValid 13295 42 := by unfold smallValid; decide +kernel

private theorem sp13337 : smallValid 13337 43 := by unfold smallValid; decide +kernel

private theorem sp13380 : smallValid 13380 42 := by unfold smallValid; decide +kernel

private theorem sp13422 : smallValid 13422 43 := by unfold smallValid; decide +kernel

private theorem sp13465 : smallValid 13465 42 := by unfold smallValid; decide +kernel

private theorem sp13507 : smallValid 13507 43 := by unfold smallValid; decide +kernel

private theorem sp13550 : smallValid 13550 42 := by unfold smallValid; decide +kernel

private theorem sp13592 : smallValid 13592 42 := by unfold smallValid; decide +kernel

private theorem sp13634 : smallValid 13634 42 := by unfold smallValid; decide +kernel

private theorem sp13676 : smallValid 13676 43 := by unfold smallValid; decide +kernel

private theorem sp13719 : smallValid 13719 42 := by unfold smallValid; decide +kernel

private theorem sp13761 : smallValid 13761 42 := by unfold smallValid; decide +kernel

private theorem sp13803 : smallValid 13803 42 := by unfold smallValid; decide +kernel

private theorem sp13845 : smallValid 13845 43 := by unfold smallValid; decide +kernel

private theorem sp13888 : smallValid 13888 42 := by unfold smallValid; decide +kernel

private theorem sp13930 : smallValid 13930 42 := by unfold smallValid; decide +kernel

private theorem sp13972 : smallValid 13972 42 := by unfold smallValid; decide +kernel

private theorem sp14014 : smallValid 14014 43 := by unfold smallValid; decide +kernel

private theorem sp14057 : smallValid 14057 42 := by unfold smallValid; decide +kernel

private theorem sp14099 : smallValid 14099 43 := by unfold smallValid; decide +kernel

private theorem sp14142 : smallValid 14142 42 := by unfold smallValid; decide +kernel

private theorem sp14184 : smallValid 14184 43 := by unfold smallValid; decide +kernel

private theorem sp14227 : smallValid 14227 42 := by unfold smallValid; decide +kernel

private theorem sp14269 : smallValid 14269 42 := by unfold smallValid; decide +kernel

private theorem sp14311 : smallValid 14311 42 := by unfold smallValid; decide +kernel

private theorem sp14353 : smallValid 14353 43 := by unfold smallValid; decide +kernel

private theorem sp14396 : smallValid 14396 42 := by unfold smallValid; decide +kernel

private theorem sp14438 : smallValid 14438 43 := by unfold smallValid; decide +kernel

private theorem sp14481 : smallValid 14481 42 := by unfold smallValid; decide +kernel

private theorem sp14523 : smallValid 14523 43 := by unfold smallValid; decide +kernel

private theorem sp14566 : smallValid 14566 42 := by unfold smallValid; decide +kernel

private theorem sp14608 : smallValid 14608 42 := by unfold smallValid; decide +kernel

private theorem sp14650 : smallValid 14650 42 := by unfold smallValid; decide +kernel

private theorem sp14692 : smallValid 14692 43 := by unfold smallValid; decide +kernel

private theorem sp14735 : smallValid 14735 42 := by unfold smallValid; decide +kernel

private theorem sp14777 : smallValid 14777 43 := by unfold smallValid; decide +kernel

private theorem sp14820 : smallValid 14820 42 := by unfold smallValid; decide +kernel

private theorem sp14862 : smallValid 14862 43 := by unfold smallValid; decide +kernel

private theorem sp14905 : smallValid 14905 42 := by unfold smallValid; decide +kernel

private theorem sp14947 : smallValid 14947 42 := by unfold smallValid; decide +kernel

private theorem sp14989 : smallValid 14989 42 := by unfold smallValid; decide +kernel

private theorem sp15031 : smallValid 15031 43 := by unfold smallValid; decide +kernel

private theorem sp15074 : smallValid 15074 42 := by unfold smallValid; decide +kernel

private theorem sp15116 : smallValid 15116 42 := by unfold smallValid; decide +kernel

private theorem sp15158 : smallValid 15158 42 := by unfold smallValid; decide +kernel

private theorem sp15200 : smallValid 15200 43 := by unfold smallValid; decide +kernel

private theorem sp15243 : smallValid 15243 42 := by unfold smallValid; decide +kernel

private theorem sp15285 : smallValid 15285 42 := by unfold smallValid; decide +kernel

private theorem sp15327 : smallValid 15327 42 := by unfold smallValid; decide +kernel

private theorem sp15369 : smallValid 15369 43 := by unfold smallValid; decide +kernel

private theorem sp15412 : smallValid 15412 42 := by unfold smallValid; decide +kernel

private theorem sp15454 : smallValid 15454 43 := by unfold smallValid; decide +kernel

private theorem sp15497 : smallValid 15497 42 := by unfold smallValid; decide +kernel

private theorem sp15539 : smallValid 15539 43 := by unfold smallValid; decide +kernel

private theorem sp15582 : smallValid 15582 42 := by unfold smallValid; decide +kernel

private theorem sp15624 : smallValid 15624 42 := by unfold smallValid; decide +kernel

private theorem sp15666 : smallValid 15666 42 := by unfold smallValid; decide +kernel

private theorem sp15708 : smallValid 15708 43 := by unfold smallValid; decide +kernel

private theorem sp15751 : smallValid 15751 42 := by unfold smallValid; decide +kernel

private theorem sp15793 : smallValid 15793 43 := by unfold smallValid; decide +kernel

private theorem sp15836 : smallValid 15836 42 := by unfold smallValid; decide +kernel

private theorem sp15878 : smallValid 15878 43 := by unfold smallValid; decide +kernel

private theorem sp15921 : smallValid 15921 42 := by unfold smallValid; decide +kernel

private theorem sp15963 : smallValid 15963 42 := by unfold smallValid; decide +kernel

private theorem sp16005 : smallValid 16005 42 := by unfold smallValid; decide +kernel

private theorem sp16047 : smallValid 16047 43 := by unfold smallValid; decide +kernel

private theorem sp16090 : smallValid 16090 42 := by unfold smallValid; decide +kernel

private theorem sp16132 : smallValid 16132 43 := by unfold smallValid; decide +kernel

private theorem sp16175 : smallValid 16175 42 := by unfold smallValid; decide +kernel

private theorem sp16217 : smallValid 16217 43 := by unfold smallValid; decide +kernel

private theorem sp16260 : smallValid 16260 42 := by unfold smallValid; decide +kernel

private theorem sp16302 : smallValid 16302 42 := by unfold smallValid; decide +kernel

private theorem sp16344 : smallValid 16344 42 := by unfold smallValid; decide +kernel

private theorem sp16386 : smallValid 16386 43 := by unfold smallValid; decide +kernel

private theorem sp16429 : smallValid 16429 42 := by unfold smallValid; decide +kernel

private theorem sp16471 : smallValid 16471 42 := by unfold smallValid; decide +kernel

private theorem sp16513 : smallValid 16513 42 := by unfold smallValid; decide +kernel

private theorem sp16555 : smallValid 16555 43 := by unfold smallValid; decide +kernel

private theorem sp16598 : smallValid 16598 42 := by unfold smallValid; decide +kernel

private theorem sp16640 : smallValid 16640 42 := by unfold smallValid; decide +kernel

private theorem sp16682 : smallValid 16682 42 := by unfold smallValid; decide +kernel

private theorem sp16724 : smallValid 16724 43 := by unfold smallValid; decide +kernel

private theorem sp16767 : smallValid 16767 42 := by unfold smallValid; decide +kernel

private theorem sp16809 : smallValid 16809 43 := by unfold smallValid; decide +kernel

private theorem sp16852 : smallValid 16852 42 := by unfold smallValid; decide +kernel

private theorem sp16894 : smallValid 16894 43 := by unfold smallValid; decide +kernel

private theorem sp16937 : smallValid 16937 42 := by unfold smallValid; decide +kernel

private theorem sp16979 : smallValid 16979 42 := by unfold smallValid; decide +kernel

private theorem sp17021 : smallValid 17021 42 := by unfold smallValid; decide +kernel

private theorem sp17063 : smallValid 17063 43 := by unfold smallValid; decide +kernel

private theorem sp17106 : smallValid 17106 42 := by unfold smallValid; decide +kernel

private theorem sp17148 : smallValid 17148 43 := by unfold smallValid; decide +kernel

private theorem sp17191 : smallValid 17191 42 := by unfold smallValid; decide +kernel

private theorem sp17233 : smallValid 17233 43 := by unfold smallValid; decide +kernel

private theorem sp17276 : smallValid 17276 42 := by unfold smallValid; decide +kernel

private theorem sp17318 : smallValid 17318 42 := by unfold smallValid; decide +kernel

private theorem sp17360 : smallValid 17360 42 := by unfold smallValid; decide +kernel

private theorem sp17402 : smallValid 17402 43 := by unfold smallValid; decide +kernel

private theorem sp17445 : smallValid 17445 42 := by unfold smallValid; decide +kernel

private theorem sp17487 : smallValid 17487 43 := by unfold smallValid; decide +kernel

private theorem sp17530 : smallValid 17530 42 := by unfold smallValid; decide +kernel

private theorem sp17572 : smallValid 17572 43 := by unfold smallValid; decide +kernel

private theorem sp17615 : smallValid 17615 42 := by unfold smallValid; decide +kernel

private theorem sp17657 : smallValid 17657 42 := by unfold smallValid; decide +kernel

private theorem sp17699 : smallValid 17699 42 := by unfold smallValid; decide +kernel

private theorem sp17741 : smallValid 17741 43 := by unfold smallValid; decide +kernel

private theorem sp17784 : smallValid 17784 42 := by unfold smallValid; decide +kernel

private theorem sp17826 : smallValid 17826 42 := by unfold smallValid; decide +kernel

private theorem sp17868 : smallValid 17868 42 := by unfold smallValid; decide +kernel

private theorem sp17910 : smallValid 17910 43 := by unfold smallValid; decide +kernel

private theorem sp17953 : smallValid 17953 42 := by unfold smallValid; decide +kernel

private theorem sp17995 : smallValid 17995 42 := by unfold smallValid; decide +kernel

private theorem sp18037 : smallValid 18037 42 := by unfold smallValid; decide +kernel

private theorem sp18079 : smallValid 18079 43 := by unfold smallValid; decide +kernel

private theorem sp18122 : smallValid 18122 42 := by unfold smallValid; decide +kernel

private theorem sp18164 : smallValid 18164 43 := by unfold smallValid; decide +kernel

private theorem sp18207 : smallValid 18207 42 := by unfold smallValid; decide +kernel

private theorem sp18249 : smallValid 18249 43 := by unfold smallValid; decide +kernel

private theorem sp18292 : smallValid 18292 42 := by unfold smallValid; decide +kernel

private theorem sp18334 : smallValid 18334 42 := by unfold smallValid; decide +kernel

private theorem sp18376 : smallValid 18376 42 := by unfold smallValid; decide +kernel

private theorem sp18418 : smallValid 18418 43 := by unfold smallValid; decide +kernel

private theorem sp18461 : smallValid 18461 42 := by unfold smallValid; decide +kernel

private theorem sp18503 : smallValid 18503 43 := by unfold smallValid; decide +kernel

private theorem sp18546 : smallValid 18546 42 := by unfold smallValid; decide +kernel

private theorem sp18588 : smallValid 18588 43 := by unfold smallValid; decide +kernel

private theorem sp18631 : smallValid 18631 42 := by unfold smallValid; decide +kernel

private theorem sp18673 : smallValid 18673 42 := by unfold smallValid; decide +kernel

private theorem sp18715 : smallValid 18715 42 := by unfold smallValid; decide +kernel

private theorem sp18757 : smallValid 18757 43 := by unfold smallValid; decide +kernel

private theorem sp18800 : smallValid 18800 42 := by unfold smallValid; decide +kernel

private theorem sp18842 : smallValid 18842 43 := by unfold smallValid; decide +kernel

private theorem sp18885 : smallValid 18885 42 := by unfold smallValid; decide +kernel

private theorem sp18927 : smallValid 18927 43 := by unfold smallValid; decide +kernel

private theorem sp18970 : smallValid 18970 42 := by unfold smallValid; decide +kernel

private theorem sp19012 : smallValid 19012 42 := by unfold smallValid; decide +kernel

private theorem sp19054 : smallValid 19054 42 := by unfold smallValid; decide +kernel

private theorem sp19096 : smallValid 19096 43 := by unfold smallValid; decide +kernel

private theorem sp19139 : smallValid 19139 42 := by unfold smallValid; decide +kernel

private theorem sp19181 : smallValid 19181 42 := by unfold smallValid; decide +kernel

private theorem sp19223 : smallValid 19223 42 := by unfold smallValid; decide +kernel

private theorem sp19265 : smallValid 19265 43 := by unfold smallValid; decide +kernel

private theorem sp19308 : smallValid 19308 42 := by unfold smallValid; decide +kernel

private theorem sp19350 : smallValid 19350 42 := by unfold smallValid; decide +kernel

private theorem sp19392 : smallValid 19392 42 := by unfold smallValid; decide +kernel

private theorem sp19434 : smallValid 19434 43 := by unfold smallValid; decide +kernel

private theorem sp19477 : smallValid 19477 42 := by unfold smallValid; decide +kernel

private theorem sp19519 : smallValid 19519 43 := by unfold smallValid; decide +kernel

private theorem sp19562 : smallValid 19562 42 := by unfold smallValid; decide +kernel

private theorem sp19604 : smallValid 19604 43 := by unfold smallValid; decide +kernel

private theorem sp19647 : smallValid 19647 42 := by unfold smallValid; decide +kernel

private theorem sp19689 : smallValid 19689 42 := by unfold smallValid; decide +kernel

private theorem sp19731 : smallValid 19731 42 := by unfold smallValid; decide +kernel

private theorem sp19773 : smallValid 19773 43 := by unfold smallValid; decide +kernel

private theorem sp19816 : smallValid 19816 42 := by unfold smallValid; decide +kernel

private theorem sp19858 : smallValid 19858 43 := by unfold smallValid; decide +kernel

private theorem sp19901 : smallValid 19901 42 := by unfold smallValid; decide +kernel

private theorem sp19943 : smallValid 19943 43 := by unfold smallValid; decide +kernel

private theorem sp19986 : smallValid 19986 42 := by unfold smallValid; decide +kernel

private theorem sp20028 : smallValid 20028 42 := by unfold smallValid; decide +kernel

private theorem sp20070 : smallValid 20070 42 := by unfold smallValid; decide +kernel

private theorem sp20112 : smallValid 20112 43 := by unfold smallValid; decide +kernel

private theorem sp20155 : smallValid 20155 42 := by unfold smallValid; decide +kernel

private theorem sp20197 : smallValid 20197 43 := by unfold smallValid; decide +kernel

private theorem sp20240 : smallValid 20240 42 := by unfold smallValid; decide +kernel

private theorem sp20282 : smallValid 20282 43 := by unfold smallValid; decide +kernel

private theorem sp20325 : smallValid 20325 42 := by unfold smallValid; decide +kernel

private theorem sp20367 : smallValid 20367 42 := by unfold smallValid; decide +kernel

private theorem sp20409 : smallValid 20409 42 := by unfold smallValid; decide +kernel

private theorem sp20451 : smallValid 20451 43 := by unfold smallValid; decide +kernel

private theorem sp20494 : smallValid 20494 42 := by unfold smallValid; decide +kernel

private theorem sp20536 : smallValid 20536 42 := by unfold smallValid; decide +kernel

private theorem sp20578 : smallValid 20578 42 := by unfold smallValid; decide +kernel

private theorem sp20620 : smallValid 20620 43 := by unfold smallValid; decide +kernel

private theorem sp20663 : smallValid 20663 42 := by unfold smallValid; decide +kernel

private theorem sp20705 : smallValid 20705 42 := by unfold smallValid; decide +kernel

private theorem sp20747 : smallValid 20747 42 := by unfold smallValid; decide +kernel

private theorem sp20789 : smallValid 20789 43 := by unfold smallValid; decide +kernel

private theorem sp20832 : smallValid 20832 42 := by unfold smallValid; decide +kernel

private theorem sp20874 : smallValid 20874 43 := by unfold smallValid; decide +kernel

private theorem sp20917 : smallValid 20917 42 := by unfold smallValid; decide +kernel

private theorem sp20959 : smallValid 20959 43 := by unfold smallValid; decide +kernel

private theorem sp21002 : smallValid 21002 42 := by unfold smallValid; decide +kernel

private theorem sp21044 : smallValid 21044 42 := by unfold smallValid; decide +kernel

private theorem sp21086 : smallValid 21086 42 := by unfold smallValid; decide +kernel

private theorem sp21128 : smallValid 21128 43 := by unfold smallValid; decide +kernel

private theorem sp21171 : smallValid 21171 42 := by unfold smallValid; decide +kernel

private theorem sp21213 : smallValid 21213 43 := by unfold smallValid; decide +kernel

private theorem sp21256 : smallValid 21256 42 := by unfold smallValid; decide +kernel

private theorem sp21298 : smallValid 21298 43 := by unfold smallValid; decide +kernel

private theorem sp21341 : smallValid 21341 42 := by unfold smallValid; decide +kernel

private theorem sp21383 : smallValid 21383 42 := by unfold smallValid; decide +kernel

private theorem sp21425 : smallValid 21425 42 := by unfold smallValid; decide +kernel

private theorem sp21467 : smallValid 21467 43 := by unfold smallValid; decide +kernel

private theorem sp21510 : smallValid 21510 42 := by unfold smallValid; decide +kernel

private theorem sp21552 : smallValid 21552 43 := by unfold smallValid; decide +kernel

private theorem sp21595 : smallValid 21595 42 := by unfold smallValid; decide +kernel

private theorem sp21637 : smallValid 21637 43 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤21679) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 21680 := (joinSmall (lo:=0) (a:=10840) (b:=10840) (joinSmall (lo:=0) (a:=5420) (b:=5420) (joinSmall (lo:=0) (a:=2710) (b:=2710) (joinSmall (lo:=0) (a:=1355) (b:=1355) (joinSmall (lo:=0) (a:=677) (b:=678) (joinSmall (lo:=0) (a:=338) (b:=339) (joinSmall (lo:=0) (a:=169) (b:=169) (joinSmall (lo:=0) (a:=84) (b:=85) (joinSmall (lo:=0) (a:=42) (b:=42) sp0 sp42) (joinSmall (lo:=84) (a:=42) (b:=43) sp84 sp126)) (joinSmall (lo:=169) (a:=84) (b:=85) (joinSmall (lo:=169) (a:=42) (b:=42) sp169 sp211) (joinSmall (lo:=253) (a:=42) (b:=43) sp253 sp295))) (joinSmall (lo:=338) (a:=169) (b:=170) (joinSmall (lo:=338) (a:=84) (b:=85) (joinSmall (lo:=338) (a:=42) (b:=42) sp338 sp380) (joinSmall (lo:=422) (a:=42) (b:=43) sp422 sp464)) (joinSmall (lo:=507) (a:=85) (b:=85) (joinSmall (lo:=507) (a:=42) (b:=43) sp507 sp549) (joinSmall (lo:=592) (a:=42) (b:=43) sp592 sp634)))) (joinSmall (lo:=677) (a:=339) (b:=339) (joinSmall (lo:=677) (a:=169) (b:=170) (joinSmall (lo:=677) (a:=84) (b:=85) (joinSmall (lo:=677) (a:=42) (b:=42) sp677 sp719) (joinSmall (lo:=761) (a:=42) (b:=43) sp761 sp803)) (joinSmall (lo:=846) (a:=85) (b:=85) (joinSmall (lo:=846) (a:=42) (b:=43) sp846 sp888) (joinSmall (lo:=931) (a:=42) (b:=43) sp931 sp973))) (joinSmall (lo:=1016) (a:=169) (b:=170) (joinSmall (lo:=1016) (a:=84) (b:=85) (joinSmall (lo:=1016) (a:=42) (b:=42) sp1016 sp1058) (joinSmall (lo:=1100) (a:=42) (b:=43) sp1100 sp1142)) (joinSmall (lo:=1185) (a:=85) (b:=85) (joinSmall (lo:=1185) (a:=42) (b:=43) sp1185 sp1227) (joinSmall (lo:=1270) (a:=42) (b:=43) sp1270 sp1312))))) (joinSmall (lo:=1355) (a:=677) (b:=678) (joinSmall (lo:=1355) (a:=338) (b:=339) (joinSmall (lo:=1355) (a:=169) (b:=169) (joinSmall (lo:=1355) (a:=84) (b:=85) (joinSmall (lo:=1355) (a:=42) (b:=42) sp1355 sp1397) (joinSmall (lo:=1439) (a:=42) (b:=43) sp1439 sp1481)) (joinSmall (lo:=1524) (a:=84) (b:=85) (joinSmall (lo:=1524) (a:=42) (b:=42) sp1524 sp1566) (joinSmall (lo:=1608) (a:=42) (b:=43) sp1608 sp1650))) (joinSmall (lo:=1693) (a:=169) (b:=170) (joinSmall (lo:=1693) (a:=84) (b:=85) (joinSmall (lo:=1693) (a:=42) (b:=42) sp1693 sp1735) (joinSmall (lo:=1777) (a:=42) (b:=43) sp1777 sp1819)) (joinSmall (lo:=1862) (a:=85) (b:=85) (joinSmall (lo:=1862) (a:=42) (b:=43) sp1862 sp1904) (joinSmall (lo:=1947) (a:=42) (b:=43) sp1947 sp1989)))) (joinSmall (lo:=2032) (a:=339) (b:=339) (joinSmall (lo:=2032) (a:=169) (b:=170) (joinSmall (lo:=2032) (a:=84) (b:=85) (joinSmall (lo:=2032) (a:=42) (b:=42) sp2032 sp2074) (joinSmall (lo:=2116) (a:=42) (b:=43) sp2116 sp2158)) (joinSmall (lo:=2201) (a:=85) (b:=85) (joinSmall (lo:=2201) (a:=42) (b:=43) sp2201 sp2243) (joinSmall (lo:=2286) (a:=42) (b:=43) sp2286 sp2328))) (joinSmall (lo:=2371) (a:=169) (b:=170) (joinSmall (lo:=2371) (a:=84) (b:=85) (joinSmall (lo:=2371) (a:=42) (b:=42) sp2371 sp2413) (joinSmall (lo:=2455) (a:=42) (b:=43) sp2455 sp2497)) (joinSmall (lo:=2540) (a:=85) (b:=85) (joinSmall (lo:=2540) (a:=42) (b:=43) sp2540 sp2582) (joinSmall (lo:=2625) (a:=42) (b:=43) sp2625 sp2667)))))) (joinSmall (lo:=2710) (a:=1355) (b:=1355) (joinSmall (lo:=2710) (a:=677) (b:=678) (joinSmall (lo:=2710) (a:=338) (b:=339) (joinSmall (lo:=2710) (a:=169) (b:=169) (joinSmall (lo:=2710) (a:=84) (b:=85) (joinSmall (lo:=2710) (a:=42) (b:=42) sp2710 sp2752) (joinSmall (lo:=2794) (a:=42) (b:=43) sp2794 sp2836)) (joinSmall (lo:=2879) (a:=84) (b:=85) (joinSmall (lo:=2879) (a:=42) (b:=42) sp2879 sp2921) (joinSmall (lo:=2963) (a:=42) (b:=43) sp2963 sp3005))) (joinSmall (lo:=3048) (a:=169) (b:=170) (joinSmall (lo:=3048) (a:=84) (b:=85) (joinSmall (lo:=3048) (a:=42) (b:=42) sp3048 sp3090) (joinSmall (lo:=3132) (a:=42) (b:=43) sp3132 sp3174)) (joinSmall (lo:=3217) (a:=85) (b:=85) (joinSmall (lo:=3217) (a:=42) (b:=43) sp3217 sp3259) (joinSmall (lo:=3302) (a:=42) (b:=43) sp3302 sp3344)))) (joinSmall (lo:=3387) (a:=339) (b:=339) (joinSmall (lo:=3387) (a:=169) (b:=170) (joinSmall (lo:=3387) (a:=84) (b:=85) (joinSmall (lo:=3387) (a:=42) (b:=42) sp3387 sp3429) (joinSmall (lo:=3471) (a:=42) (b:=43) sp3471 sp3513)) (joinSmall (lo:=3556) (a:=85) (b:=85) (joinSmall (lo:=3556) (a:=42) (b:=43) sp3556 sp3598) (joinSmall (lo:=3641) (a:=42) (b:=43) sp3641 sp3683))) (joinSmall (lo:=3726) (a:=169) (b:=170) (joinSmall (lo:=3726) (a:=84) (b:=85) (joinSmall (lo:=3726) (a:=42) (b:=42) sp3726 sp3768) (joinSmall (lo:=3810) (a:=42) (b:=43) sp3810 sp3852)) (joinSmall (lo:=3895) (a:=85) (b:=85) (joinSmall (lo:=3895) (a:=42) (b:=43) sp3895 sp3937) (joinSmall (lo:=3980) (a:=42) (b:=43) sp3980 sp4022))))) (joinSmall (lo:=4065) (a:=677) (b:=678) (joinSmall (lo:=4065) (a:=338) (b:=339) (joinSmall (lo:=4065) (a:=169) (b:=169) (joinSmall (lo:=4065) (a:=84) (b:=85) (joinSmall (lo:=4065) (a:=42) (b:=42) sp4065 sp4107) (joinSmall (lo:=4149) (a:=42) (b:=43) sp4149 sp4191)) (joinSmall (lo:=4234) (a:=84) (b:=85) (joinSmall (lo:=4234) (a:=42) (b:=42) sp4234 sp4276) (joinSmall (lo:=4318) (a:=42) (b:=43) sp4318 sp4360))) (joinSmall (lo:=4403) (a:=169) (b:=170) (joinSmall (lo:=4403) (a:=84) (b:=85) (joinSmall (lo:=4403) (a:=42) (b:=42) sp4403 sp4445) (joinSmall (lo:=4487) (a:=42) (b:=43) sp4487 sp4529)) (joinSmall (lo:=4572) (a:=85) (b:=85) (joinSmall (lo:=4572) (a:=42) (b:=43) sp4572 sp4614) (joinSmall (lo:=4657) (a:=42) (b:=43) sp4657 sp4699)))) (joinSmall (lo:=4742) (a:=339) (b:=339) (joinSmall (lo:=4742) (a:=169) (b:=170) (joinSmall (lo:=4742) (a:=84) (b:=85) (joinSmall (lo:=4742) (a:=42) (b:=42) sp4742 sp4784) (joinSmall (lo:=4826) (a:=42) (b:=43) sp4826 sp4868)) (joinSmall (lo:=4911) (a:=85) (b:=85) (joinSmall (lo:=4911) (a:=42) (b:=43) sp4911 sp4953) (joinSmall (lo:=4996) (a:=42) (b:=43) sp4996 sp5038))) (joinSmall (lo:=5081) (a:=169) (b:=170) (joinSmall (lo:=5081) (a:=84) (b:=85) (joinSmall (lo:=5081) (a:=42) (b:=42) sp5081 sp5123) (joinSmall (lo:=5165) (a:=42) (b:=43) sp5165 sp5207)) (joinSmall (lo:=5250) (a:=85) (b:=85) (joinSmall (lo:=5250) (a:=42) (b:=43) sp5250 sp5292) (joinSmall (lo:=5335) (a:=42) (b:=43) sp5335 sp5377))))))) (joinSmall (lo:=5420) (a:=2710) (b:=2710) (joinSmall (lo:=5420) (a:=1355) (b:=1355) (joinSmall (lo:=5420) (a:=677) (b:=678) (joinSmall (lo:=5420) (a:=338) (b:=339) (joinSmall (lo:=5420) (a:=169) (b:=169) (joinSmall (lo:=5420) (a:=84) (b:=85) (joinSmall (lo:=5420) (a:=42) (b:=42) sp5420 sp5462) (joinSmall (lo:=5504) (a:=42) (b:=43) sp5504 sp5546)) (joinSmall (lo:=5589) (a:=84) (b:=85) (joinSmall (lo:=5589) (a:=42) (b:=42) sp5589 sp5631) (joinSmall (lo:=5673) (a:=42) (b:=43) sp5673 sp5715))) (joinSmall (lo:=5758) (a:=169) (b:=170) (joinSmall (lo:=5758) (a:=84) (b:=85) (joinSmall (lo:=5758) (a:=42) (b:=42) sp5758 sp5800) (joinSmall (lo:=5842) (a:=42) (b:=43) sp5842 sp5884)) (joinSmall (lo:=5927) (a:=85) (b:=85) (joinSmall (lo:=5927) (a:=42) (b:=43) sp5927 sp5969) (joinSmall (lo:=6012) (a:=42) (b:=43) sp6012 sp6054)))) (joinSmall (lo:=6097) (a:=339) (b:=339) (joinSmall (lo:=6097) (a:=169) (b:=170) (joinSmall (lo:=6097) (a:=84) (b:=85) (joinSmall (lo:=6097) (a:=42) (b:=42) sp6097 sp6139) (joinSmall (lo:=6181) (a:=42) (b:=43) sp6181 sp6223)) (joinSmall (lo:=6266) (a:=85) (b:=85) (joinSmall (lo:=6266) (a:=42) (b:=43) sp6266 sp6308) (joinSmall (lo:=6351) (a:=42) (b:=43) sp6351 sp6393))) (joinSmall (lo:=6436) (a:=169) (b:=170) (joinSmall (lo:=6436) (a:=84) (b:=85) (joinSmall (lo:=6436) (a:=42) (b:=42) sp6436 sp6478) (joinSmall (lo:=6520) (a:=42) (b:=43) sp6520 sp6562)) (joinSmall (lo:=6605) (a:=85) (b:=85) (joinSmall (lo:=6605) (a:=42) (b:=43) sp6605 sp6647) (joinSmall (lo:=6690) (a:=42) (b:=43) sp6690 sp6732))))) (joinSmall (lo:=6775) (a:=677) (b:=678) (joinSmall (lo:=6775) (a:=338) (b:=339) (joinSmall (lo:=6775) (a:=169) (b:=169) (joinSmall (lo:=6775) (a:=84) (b:=85) (joinSmall (lo:=6775) (a:=42) (b:=42) sp6775 sp6817) (joinSmall (lo:=6859) (a:=42) (b:=43) sp6859 sp6901)) (joinSmall (lo:=6944) (a:=84) (b:=85) (joinSmall (lo:=6944) (a:=42) (b:=42) sp6944 sp6986) (joinSmall (lo:=7028) (a:=42) (b:=43) sp7028 sp7070))) (joinSmall (lo:=7113) (a:=169) (b:=170) (joinSmall (lo:=7113) (a:=84) (b:=85) (joinSmall (lo:=7113) (a:=42) (b:=42) sp7113 sp7155) (joinSmall (lo:=7197) (a:=42) (b:=43) sp7197 sp7239)) (joinSmall (lo:=7282) (a:=85) (b:=85) (joinSmall (lo:=7282) (a:=42) (b:=43) sp7282 sp7324) (joinSmall (lo:=7367) (a:=42) (b:=43) sp7367 sp7409)))) (joinSmall (lo:=7452) (a:=339) (b:=339) (joinSmall (lo:=7452) (a:=169) (b:=170) (joinSmall (lo:=7452) (a:=84) (b:=85) (joinSmall (lo:=7452) (a:=42) (b:=42) sp7452 sp7494) (joinSmall (lo:=7536) (a:=42) (b:=43) sp7536 sp7578)) (joinSmall (lo:=7621) (a:=85) (b:=85) (joinSmall (lo:=7621) (a:=42) (b:=43) sp7621 sp7663) (joinSmall (lo:=7706) (a:=42) (b:=43) sp7706 sp7748))) (joinSmall (lo:=7791) (a:=169) (b:=170) (joinSmall (lo:=7791) (a:=84) (b:=85) (joinSmall (lo:=7791) (a:=42) (b:=42) sp7791 sp7833) (joinSmall (lo:=7875) (a:=42) (b:=43) sp7875 sp7917)) (joinSmall (lo:=7960) (a:=85) (b:=85) (joinSmall (lo:=7960) (a:=42) (b:=43) sp7960 sp8002) (joinSmall (lo:=8045) (a:=42) (b:=43) sp8045 sp8087)))))) (joinSmall (lo:=8130) (a:=1355) (b:=1355) (joinSmall (lo:=8130) (a:=677) (b:=678) (joinSmall (lo:=8130) (a:=338) (b:=339) (joinSmall (lo:=8130) (a:=169) (b:=169) (joinSmall (lo:=8130) (a:=84) (b:=85) (joinSmall (lo:=8130) (a:=42) (b:=42) sp8130 sp8172) (joinSmall (lo:=8214) (a:=42) (b:=43) sp8214 sp8256)) (joinSmall (lo:=8299) (a:=84) (b:=85) (joinSmall (lo:=8299) (a:=42) (b:=42) sp8299 sp8341) (joinSmall (lo:=8383) (a:=42) (b:=43) sp8383 sp8425))) (joinSmall (lo:=8468) (a:=169) (b:=170) (joinSmall (lo:=8468) (a:=84) (b:=85) (joinSmall (lo:=8468) (a:=42) (b:=42) sp8468 sp8510) (joinSmall (lo:=8552) (a:=42) (b:=43) sp8552 sp8594)) (joinSmall (lo:=8637) (a:=85) (b:=85) (joinSmall (lo:=8637) (a:=42) (b:=43) sp8637 sp8679) (joinSmall (lo:=8722) (a:=42) (b:=43) sp8722 sp8764)))) (joinSmall (lo:=8807) (a:=339) (b:=339) (joinSmall (lo:=8807) (a:=169) (b:=170) (joinSmall (lo:=8807) (a:=84) (b:=85) (joinSmall (lo:=8807) (a:=42) (b:=42) sp8807 sp8849) (joinSmall (lo:=8891) (a:=42) (b:=43) sp8891 sp8933)) (joinSmall (lo:=8976) (a:=85) (b:=85) (joinSmall (lo:=8976) (a:=42) (b:=43) sp8976 sp9018) (joinSmall (lo:=9061) (a:=42) (b:=43) sp9061 sp9103))) (joinSmall (lo:=9146) (a:=169) (b:=170) (joinSmall (lo:=9146) (a:=84) (b:=85) (joinSmall (lo:=9146) (a:=42) (b:=42) sp9146 sp9188) (joinSmall (lo:=9230) (a:=42) (b:=43) sp9230 sp9272)) (joinSmall (lo:=9315) (a:=85) (b:=85) (joinSmall (lo:=9315) (a:=42) (b:=43) sp9315 sp9357) (joinSmall (lo:=9400) (a:=42) (b:=43) sp9400 sp9442))))) (joinSmall (lo:=9485) (a:=677) (b:=678) (joinSmall (lo:=9485) (a:=338) (b:=339) (joinSmall (lo:=9485) (a:=169) (b:=169) (joinSmall (lo:=9485) (a:=84) (b:=85) (joinSmall (lo:=9485) (a:=42) (b:=42) sp9485 sp9527) (joinSmall (lo:=9569) (a:=42) (b:=43) sp9569 sp9611)) (joinSmall (lo:=9654) (a:=84) (b:=85) (joinSmall (lo:=9654) (a:=42) (b:=42) sp9654 sp9696) (joinSmall (lo:=9738) (a:=42) (b:=43) sp9738 sp9780))) (joinSmall (lo:=9823) (a:=169) (b:=170) (joinSmall (lo:=9823) (a:=84) (b:=85) (joinSmall (lo:=9823) (a:=42) (b:=42) sp9823 sp9865) (joinSmall (lo:=9907) (a:=42) (b:=43) sp9907 sp9949)) (joinSmall (lo:=9992) (a:=85) (b:=85) (joinSmall (lo:=9992) (a:=42) (b:=43) sp9992 sp10034) (joinSmall (lo:=10077) (a:=42) (b:=43) sp10077 sp10119)))) (joinSmall (lo:=10162) (a:=339) (b:=339) (joinSmall (lo:=10162) (a:=169) (b:=170) (joinSmall (lo:=10162) (a:=84) (b:=85) (joinSmall (lo:=10162) (a:=42) (b:=42) sp10162 sp10204) (joinSmall (lo:=10246) (a:=42) (b:=43) sp10246 sp10288)) (joinSmall (lo:=10331) (a:=85) (b:=85) (joinSmall (lo:=10331) (a:=42) (b:=43) sp10331 sp10373) (joinSmall (lo:=10416) (a:=42) (b:=43) sp10416 sp10458))) (joinSmall (lo:=10501) (a:=169) (b:=170) (joinSmall (lo:=10501) (a:=84) (b:=85) (joinSmall (lo:=10501) (a:=42) (b:=42) sp10501 sp10543) (joinSmall (lo:=10585) (a:=42) (b:=43) sp10585 sp10627)) (joinSmall (lo:=10670) (a:=85) (b:=85) (joinSmall (lo:=10670) (a:=42) (b:=43) sp10670 sp10712) (joinSmall (lo:=10755) (a:=42) (b:=43) sp10755 sp10797)))))))) (joinSmall (lo:=10840) (a:=5420) (b:=5420) (joinSmall (lo:=10840) (a:=2710) (b:=2710) (joinSmall (lo:=10840) (a:=1355) (b:=1355) (joinSmall (lo:=10840) (a:=677) (b:=678) (joinSmall (lo:=10840) (a:=338) (b:=339) (joinSmall (lo:=10840) (a:=169) (b:=169) (joinSmall (lo:=10840) (a:=84) (b:=85) (joinSmall (lo:=10840) (a:=42) (b:=42) sp10840 sp10882) (joinSmall (lo:=10924) (a:=42) (b:=43) sp10924 sp10966)) (joinSmall (lo:=11009) (a:=84) (b:=85) (joinSmall (lo:=11009) (a:=42) (b:=42) sp11009 sp11051) (joinSmall (lo:=11093) (a:=42) (b:=43) sp11093 sp11135))) (joinSmall (lo:=11178) (a:=169) (b:=170) (joinSmall (lo:=11178) (a:=84) (b:=85) (joinSmall (lo:=11178) (a:=42) (b:=42) sp11178 sp11220) (joinSmall (lo:=11262) (a:=42) (b:=43) sp11262 sp11304)) (joinSmall (lo:=11347) (a:=85) (b:=85) (joinSmall (lo:=11347) (a:=42) (b:=43) sp11347 sp11389) (joinSmall (lo:=11432) (a:=42) (b:=43) sp11432 sp11474)))) (joinSmall (lo:=11517) (a:=339) (b:=339) (joinSmall (lo:=11517) (a:=169) (b:=170) (joinSmall (lo:=11517) (a:=84) (b:=85) (joinSmall (lo:=11517) (a:=42) (b:=42) sp11517 sp11559) (joinSmall (lo:=11601) (a:=42) (b:=43) sp11601 sp11643)) (joinSmall (lo:=11686) (a:=85) (b:=85) (joinSmall (lo:=11686) (a:=42) (b:=43) sp11686 sp11728) (joinSmall (lo:=11771) (a:=42) (b:=43) sp11771 sp11813))) (joinSmall (lo:=11856) (a:=169) (b:=170) (joinSmall (lo:=11856) (a:=84) (b:=85) (joinSmall (lo:=11856) (a:=42) (b:=42) sp11856 sp11898) (joinSmall (lo:=11940) (a:=42) (b:=43) sp11940 sp11982)) (joinSmall (lo:=12025) (a:=85) (b:=85) (joinSmall (lo:=12025) (a:=42) (b:=43) sp12025 sp12067) (joinSmall (lo:=12110) (a:=42) (b:=43) sp12110 sp12152))))) (joinSmall (lo:=12195) (a:=677) (b:=678) (joinSmall (lo:=12195) (a:=338) (b:=339) (joinSmall (lo:=12195) (a:=169) (b:=169) (joinSmall (lo:=12195) (a:=84) (b:=85) (joinSmall (lo:=12195) (a:=42) (b:=42) sp12195 sp12237) (joinSmall (lo:=12279) (a:=42) (b:=43) sp12279 sp12321)) (joinSmall (lo:=12364) (a:=84) (b:=85) (joinSmall (lo:=12364) (a:=42) (b:=42) sp12364 sp12406) (joinSmall (lo:=12448) (a:=42) (b:=43) sp12448 sp12490))) (joinSmall (lo:=12533) (a:=169) (b:=170) (joinSmall (lo:=12533) (a:=84) (b:=85) (joinSmall (lo:=12533) (a:=42) (b:=42) sp12533 sp12575) (joinSmall (lo:=12617) (a:=42) (b:=43) sp12617 sp12659)) (joinSmall (lo:=12702) (a:=85) (b:=85) (joinSmall (lo:=12702) (a:=42) (b:=43) sp12702 sp12744) (joinSmall (lo:=12787) (a:=42) (b:=43) sp12787 sp12829)))) (joinSmall (lo:=12872) (a:=339) (b:=339) (joinSmall (lo:=12872) (a:=169) (b:=170) (joinSmall (lo:=12872) (a:=84) (b:=85) (joinSmall (lo:=12872) (a:=42) (b:=42) sp12872 sp12914) (joinSmall (lo:=12956) (a:=42) (b:=43) sp12956 sp12998)) (joinSmall (lo:=13041) (a:=85) (b:=85) (joinSmall (lo:=13041) (a:=42) (b:=43) sp13041 sp13083) (joinSmall (lo:=13126) (a:=42) (b:=43) sp13126 sp13168))) (joinSmall (lo:=13211) (a:=169) (b:=170) (joinSmall (lo:=13211) (a:=84) (b:=85) (joinSmall (lo:=13211) (a:=42) (b:=42) sp13211 sp13253) (joinSmall (lo:=13295) (a:=42) (b:=43) sp13295 sp13337)) (joinSmall (lo:=13380) (a:=85) (b:=85) (joinSmall (lo:=13380) (a:=42) (b:=43) sp13380 sp13422) (joinSmall (lo:=13465) (a:=42) (b:=43) sp13465 sp13507)))))) (joinSmall (lo:=13550) (a:=1355) (b:=1355) (joinSmall (lo:=13550) (a:=677) (b:=678) (joinSmall (lo:=13550) (a:=338) (b:=339) (joinSmall (lo:=13550) (a:=169) (b:=169) (joinSmall (lo:=13550) (a:=84) (b:=85) (joinSmall (lo:=13550) (a:=42) (b:=42) sp13550 sp13592) (joinSmall (lo:=13634) (a:=42) (b:=43) sp13634 sp13676)) (joinSmall (lo:=13719) (a:=84) (b:=85) (joinSmall (lo:=13719) (a:=42) (b:=42) sp13719 sp13761) (joinSmall (lo:=13803) (a:=42) (b:=43) sp13803 sp13845))) (joinSmall (lo:=13888) (a:=169) (b:=170) (joinSmall (lo:=13888) (a:=84) (b:=85) (joinSmall (lo:=13888) (a:=42) (b:=42) sp13888 sp13930) (joinSmall (lo:=13972) (a:=42) (b:=43) sp13972 sp14014)) (joinSmall (lo:=14057) (a:=85) (b:=85) (joinSmall (lo:=14057) (a:=42) (b:=43) sp14057 sp14099) (joinSmall (lo:=14142) (a:=42) (b:=43) sp14142 sp14184)))) (joinSmall (lo:=14227) (a:=339) (b:=339) (joinSmall (lo:=14227) (a:=169) (b:=170) (joinSmall (lo:=14227) (a:=84) (b:=85) (joinSmall (lo:=14227) (a:=42) (b:=42) sp14227 sp14269) (joinSmall (lo:=14311) (a:=42) (b:=43) sp14311 sp14353)) (joinSmall (lo:=14396) (a:=85) (b:=85) (joinSmall (lo:=14396) (a:=42) (b:=43) sp14396 sp14438) (joinSmall (lo:=14481) (a:=42) (b:=43) sp14481 sp14523))) (joinSmall (lo:=14566) (a:=169) (b:=170) (joinSmall (lo:=14566) (a:=84) (b:=85) (joinSmall (lo:=14566) (a:=42) (b:=42) sp14566 sp14608) (joinSmall (lo:=14650) (a:=42) (b:=43) sp14650 sp14692)) (joinSmall (lo:=14735) (a:=85) (b:=85) (joinSmall (lo:=14735) (a:=42) (b:=43) sp14735 sp14777) (joinSmall (lo:=14820) (a:=42) (b:=43) sp14820 sp14862))))) (joinSmall (lo:=14905) (a:=677) (b:=678) (joinSmall (lo:=14905) (a:=338) (b:=339) (joinSmall (lo:=14905) (a:=169) (b:=169) (joinSmall (lo:=14905) (a:=84) (b:=85) (joinSmall (lo:=14905) (a:=42) (b:=42) sp14905 sp14947) (joinSmall (lo:=14989) (a:=42) (b:=43) sp14989 sp15031)) (joinSmall (lo:=15074) (a:=84) (b:=85) (joinSmall (lo:=15074) (a:=42) (b:=42) sp15074 sp15116) (joinSmall (lo:=15158) (a:=42) (b:=43) sp15158 sp15200))) (joinSmall (lo:=15243) (a:=169) (b:=170) (joinSmall (lo:=15243) (a:=84) (b:=85) (joinSmall (lo:=15243) (a:=42) (b:=42) sp15243 sp15285) (joinSmall (lo:=15327) (a:=42) (b:=43) sp15327 sp15369)) (joinSmall (lo:=15412) (a:=85) (b:=85) (joinSmall (lo:=15412) (a:=42) (b:=43) sp15412 sp15454) (joinSmall (lo:=15497) (a:=42) (b:=43) sp15497 sp15539)))) (joinSmall (lo:=15582) (a:=339) (b:=339) (joinSmall (lo:=15582) (a:=169) (b:=170) (joinSmall (lo:=15582) (a:=84) (b:=85) (joinSmall (lo:=15582) (a:=42) (b:=42) sp15582 sp15624) (joinSmall (lo:=15666) (a:=42) (b:=43) sp15666 sp15708)) (joinSmall (lo:=15751) (a:=85) (b:=85) (joinSmall (lo:=15751) (a:=42) (b:=43) sp15751 sp15793) (joinSmall (lo:=15836) (a:=42) (b:=43) sp15836 sp15878))) (joinSmall (lo:=15921) (a:=169) (b:=170) (joinSmall (lo:=15921) (a:=84) (b:=85) (joinSmall (lo:=15921) (a:=42) (b:=42) sp15921 sp15963) (joinSmall (lo:=16005) (a:=42) (b:=43) sp16005 sp16047)) (joinSmall (lo:=16090) (a:=85) (b:=85) (joinSmall (lo:=16090) (a:=42) (b:=43) sp16090 sp16132) (joinSmall (lo:=16175) (a:=42) (b:=43) sp16175 sp16217))))))) (joinSmall (lo:=16260) (a:=2710) (b:=2710) (joinSmall (lo:=16260) (a:=1355) (b:=1355) (joinSmall (lo:=16260) (a:=677) (b:=678) (joinSmall (lo:=16260) (a:=338) (b:=339) (joinSmall (lo:=16260) (a:=169) (b:=169) (joinSmall (lo:=16260) (a:=84) (b:=85) (joinSmall (lo:=16260) (a:=42) (b:=42) sp16260 sp16302) (joinSmall (lo:=16344) (a:=42) (b:=43) sp16344 sp16386)) (joinSmall (lo:=16429) (a:=84) (b:=85) (joinSmall (lo:=16429) (a:=42) (b:=42) sp16429 sp16471) (joinSmall (lo:=16513) (a:=42) (b:=43) sp16513 sp16555))) (joinSmall (lo:=16598) (a:=169) (b:=170) (joinSmall (lo:=16598) (a:=84) (b:=85) (joinSmall (lo:=16598) (a:=42) (b:=42) sp16598 sp16640) (joinSmall (lo:=16682) (a:=42) (b:=43) sp16682 sp16724)) (joinSmall (lo:=16767) (a:=85) (b:=85) (joinSmall (lo:=16767) (a:=42) (b:=43) sp16767 sp16809) (joinSmall (lo:=16852) (a:=42) (b:=43) sp16852 sp16894)))) (joinSmall (lo:=16937) (a:=339) (b:=339) (joinSmall (lo:=16937) (a:=169) (b:=170) (joinSmall (lo:=16937) (a:=84) (b:=85) (joinSmall (lo:=16937) (a:=42) (b:=42) sp16937 sp16979) (joinSmall (lo:=17021) (a:=42) (b:=43) sp17021 sp17063)) (joinSmall (lo:=17106) (a:=85) (b:=85) (joinSmall (lo:=17106) (a:=42) (b:=43) sp17106 sp17148) (joinSmall (lo:=17191) (a:=42) (b:=43) sp17191 sp17233))) (joinSmall (lo:=17276) (a:=169) (b:=170) (joinSmall (lo:=17276) (a:=84) (b:=85) (joinSmall (lo:=17276) (a:=42) (b:=42) sp17276 sp17318) (joinSmall (lo:=17360) (a:=42) (b:=43) sp17360 sp17402)) (joinSmall (lo:=17445) (a:=85) (b:=85) (joinSmall (lo:=17445) (a:=42) (b:=43) sp17445 sp17487) (joinSmall (lo:=17530) (a:=42) (b:=43) sp17530 sp17572))))) (joinSmall (lo:=17615) (a:=677) (b:=678) (joinSmall (lo:=17615) (a:=338) (b:=339) (joinSmall (lo:=17615) (a:=169) (b:=169) (joinSmall (lo:=17615) (a:=84) (b:=85) (joinSmall (lo:=17615) (a:=42) (b:=42) sp17615 sp17657) (joinSmall (lo:=17699) (a:=42) (b:=43) sp17699 sp17741)) (joinSmall (lo:=17784) (a:=84) (b:=85) (joinSmall (lo:=17784) (a:=42) (b:=42) sp17784 sp17826) (joinSmall (lo:=17868) (a:=42) (b:=43) sp17868 sp17910))) (joinSmall (lo:=17953) (a:=169) (b:=170) (joinSmall (lo:=17953) (a:=84) (b:=85) (joinSmall (lo:=17953) (a:=42) (b:=42) sp17953 sp17995) (joinSmall (lo:=18037) (a:=42) (b:=43) sp18037 sp18079)) (joinSmall (lo:=18122) (a:=85) (b:=85) (joinSmall (lo:=18122) (a:=42) (b:=43) sp18122 sp18164) (joinSmall (lo:=18207) (a:=42) (b:=43) sp18207 sp18249)))) (joinSmall (lo:=18292) (a:=339) (b:=339) (joinSmall (lo:=18292) (a:=169) (b:=170) (joinSmall (lo:=18292) (a:=84) (b:=85) (joinSmall (lo:=18292) (a:=42) (b:=42) sp18292 sp18334) (joinSmall (lo:=18376) (a:=42) (b:=43) sp18376 sp18418)) (joinSmall (lo:=18461) (a:=85) (b:=85) (joinSmall (lo:=18461) (a:=42) (b:=43) sp18461 sp18503) (joinSmall (lo:=18546) (a:=42) (b:=43) sp18546 sp18588))) (joinSmall (lo:=18631) (a:=169) (b:=170) (joinSmall (lo:=18631) (a:=84) (b:=85) (joinSmall (lo:=18631) (a:=42) (b:=42) sp18631 sp18673) (joinSmall (lo:=18715) (a:=42) (b:=43) sp18715 sp18757)) (joinSmall (lo:=18800) (a:=85) (b:=85) (joinSmall (lo:=18800) (a:=42) (b:=43) sp18800 sp18842) (joinSmall (lo:=18885) (a:=42) (b:=43) sp18885 sp18927)))))) (joinSmall (lo:=18970) (a:=1355) (b:=1355) (joinSmall (lo:=18970) (a:=677) (b:=678) (joinSmall (lo:=18970) (a:=338) (b:=339) (joinSmall (lo:=18970) (a:=169) (b:=169) (joinSmall (lo:=18970) (a:=84) (b:=85) (joinSmall (lo:=18970) (a:=42) (b:=42) sp18970 sp19012) (joinSmall (lo:=19054) (a:=42) (b:=43) sp19054 sp19096)) (joinSmall (lo:=19139) (a:=84) (b:=85) (joinSmall (lo:=19139) (a:=42) (b:=42) sp19139 sp19181) (joinSmall (lo:=19223) (a:=42) (b:=43) sp19223 sp19265))) (joinSmall (lo:=19308) (a:=169) (b:=170) (joinSmall (lo:=19308) (a:=84) (b:=85) (joinSmall (lo:=19308) (a:=42) (b:=42) sp19308 sp19350) (joinSmall (lo:=19392) (a:=42) (b:=43) sp19392 sp19434)) (joinSmall (lo:=19477) (a:=85) (b:=85) (joinSmall (lo:=19477) (a:=42) (b:=43) sp19477 sp19519) (joinSmall (lo:=19562) (a:=42) (b:=43) sp19562 sp19604)))) (joinSmall (lo:=19647) (a:=339) (b:=339) (joinSmall (lo:=19647) (a:=169) (b:=170) (joinSmall (lo:=19647) (a:=84) (b:=85) (joinSmall (lo:=19647) (a:=42) (b:=42) sp19647 sp19689) (joinSmall (lo:=19731) (a:=42) (b:=43) sp19731 sp19773)) (joinSmall (lo:=19816) (a:=85) (b:=85) (joinSmall (lo:=19816) (a:=42) (b:=43) sp19816 sp19858) (joinSmall (lo:=19901) (a:=42) (b:=43) sp19901 sp19943))) (joinSmall (lo:=19986) (a:=169) (b:=170) (joinSmall (lo:=19986) (a:=84) (b:=85) (joinSmall (lo:=19986) (a:=42) (b:=42) sp19986 sp20028) (joinSmall (lo:=20070) (a:=42) (b:=43) sp20070 sp20112)) (joinSmall (lo:=20155) (a:=85) (b:=85) (joinSmall (lo:=20155) (a:=42) (b:=43) sp20155 sp20197) (joinSmall (lo:=20240) (a:=42) (b:=43) sp20240 sp20282))))) (joinSmall (lo:=20325) (a:=677) (b:=678) (joinSmall (lo:=20325) (a:=338) (b:=339) (joinSmall (lo:=20325) (a:=169) (b:=169) (joinSmall (lo:=20325) (a:=84) (b:=85) (joinSmall (lo:=20325) (a:=42) (b:=42) sp20325 sp20367) (joinSmall (lo:=20409) (a:=42) (b:=43) sp20409 sp20451)) (joinSmall (lo:=20494) (a:=84) (b:=85) (joinSmall (lo:=20494) (a:=42) (b:=42) sp20494 sp20536) (joinSmall (lo:=20578) (a:=42) (b:=43) sp20578 sp20620))) (joinSmall (lo:=20663) (a:=169) (b:=170) (joinSmall (lo:=20663) (a:=84) (b:=85) (joinSmall (lo:=20663) (a:=42) (b:=42) sp20663 sp20705) (joinSmall (lo:=20747) (a:=42) (b:=43) sp20747 sp20789)) (joinSmall (lo:=20832) (a:=85) (b:=85) (joinSmall (lo:=20832) (a:=42) (b:=43) sp20832 sp20874) (joinSmall (lo:=20917) (a:=42) (b:=43) sp20917 sp20959)))) (joinSmall (lo:=21002) (a:=339) (b:=339) (joinSmall (lo:=21002) (a:=169) (b:=170) (joinSmall (lo:=21002) (a:=84) (b:=85) (joinSmall (lo:=21002) (a:=42) (b:=42) sp21002 sp21044) (joinSmall (lo:=21086) (a:=42) (b:=43) sp21086 sp21128)) (joinSmall (lo:=21171) (a:=85) (b:=85) (joinSmall (lo:=21171) (a:=42) (b:=43) sp21171 sp21213) (joinSmall (lo:=21256) (a:=42) (b:=43) sp21256 sp21298))) (joinSmall (lo:=21341) (a:=169) (b:=170) (joinSmall (lo:=21341) (a:=84) (b:=85) (joinSmall (lo:=21341) (a:=42) (b:=42) sp21341 sp21383) (joinSmall (lo:=21425) (a:=42) (b:=43) sp21425 sp21467)) (joinSmall (lo:=21510) (a:=85) (b:=85) (joinSmall (lo:=21510) (a:=42) (b:=43) sp21510 sp21552) (joinSmall (lo:=21595) (a:=42) (b:=43) sp21595 sp21637)))))))))
  have good : (List.range 21680).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 470000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 21679 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 21679 := by
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


private def packet (i : ℕ) : ℕ := (if i < 120 then (if i < 60 then (if i < 30 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 5 then (if i < 4 then 0 else 0) else (if i < 6 then 0 else 0))) else (if i < 11 then (if i < 9 then (if i < 8 then 0 else 0) else (if i < 10 then 0 else 0)) else (if i < 13 then (if i < 12 then 0 else 0) else (if i < 14 then 0 else 0)))) else (if i < 22 then (if i < 18 then (if i < 16 then 0 else (if i < 17 then 0 else 0)) else (if i < 20 then (if i < 19 then 0 else 0) else (if i < 21 then 0 else 0))) else (if i < 26 then (if i < 24 then (if i < 23 then 0 else 0) else (if i < 25 then 0 else 0)) else (if i < 28 then (if i < 27 then 0 else 0) else (if i < 29 then 0 else 0))))) else (if i < 45 then (if i < 37 then (if i < 33 then (if i < 31 then 0 else (if i < 32 then 0 else 0)) else (if i < 35 then (if i < 34 then 0 else 0) else (if i < 36 then 0 else 0))) else (if i < 41 then (if i < 39 then (if i < 38 then 0 else 0) else (if i < 40 then 0 else 0)) else (if i < 43 then (if i < 42 then 0 else 0) else (if i < 44 then 0 else 0)))) else (if i < 52 then (if i < 48 then (if i < 46 then 0 else (if i < 47 then 0 else 0)) else (if i < 50 then (if i < 49 then 0 else 0) else (if i < 51 then 0 else 0))) else (if i < 56 then (if i < 54 then (if i < 53 then 0 else 0) else (if i < 55 then 0 else 0)) else (if i < 58 then (if i < 57 then 0 else 0) else (if i < 59 then 0 else 0)))))) else (if i < 90 then (if i < 75 then (if i < 67 then (if i < 63 then (if i < 61 then 0 else (if i < 62 then 0 else 0)) else (if i < 65 then (if i < 64 then 0 else 0) else (if i < 66 then 0 else 0))) else (if i < 71 then (if i < 69 then (if i < 68 then 0 else 0) else (if i < 70 then 0 else 0)) else (if i < 73 then (if i < 72 then 0 else 0) else (if i < 74 then 0 else 0)))) else (if i < 82 then (if i < 78 then (if i < 76 then 0 else (if i < 77 then 0 else 0)) else (if i < 80 then (if i < 79 then 0 else 0) else (if i < 81 then 0 else 0))) else (if i < 86 then (if i < 84 then (if i < 83 then 0 else 0) else (if i < 85 then 0 else 0)) else (if i < 88 then (if i < 87 then 0 else 0) else (if i < 89 then 0 else 0))))) else (if i < 105 then (if i < 97 then (if i < 93 then (if i < 91 then 0 else (if i < 92 then 0 else 0)) else (if i < 95 then (if i < 94 then 0 else 0) else (if i < 96 then 0 else 0))) else (if i < 101 then (if i < 99 then (if i < 98 then 0 else 0) else (if i < 100 then 0 else 0)) else (if i < 103 then (if i < 102 then 0 else 0) else (if i < 104 then 0 else 0)))) else (if i < 112 then (if i < 108 then (if i < 106 then 0 else (if i < 107 then 0 else 0)) else (if i < 110 then (if i < 109 then 0 else 0) else (if i < 111 then 0 else 0))) else (if i < 116 then (if i < 114 then (if i < 113 then 0 else 0) else (if i < 115 then 0 else 0)) else (if i < 118 then (if i < 117 then 0 else 0) else (if i < 119 then 0 else 0))))))) else (if i < 180 then (if i < 150 then (if i < 135 then (if i < 127 then (if i < 123 then (if i < 121 then 0 else (if i < 122 then 0 else 0)) else (if i < 125 then (if i < 124 then 0 else 0) else (if i < 126 then 0 else 0))) else (if i < 131 then (if i < 129 then (if i < 128 then 0 else 0) else (if i < 130 then 0 else 0)) else (if i < 133 then (if i < 132 then 0 else 0) else (if i < 134 then 0 else 0)))) else (if i < 142 then (if i < 138 then (if i < 136 then 0 else (if i < 137 then 0 else 0)) else (if i < 140 then (if i < 139 then 0 else 0) else (if i < 141 then 0 else 0))) else (if i < 146 then (if i < 144 then (if i < 143 then 0 else 0) else (if i < 145 then 0 else 0)) else (if i < 148 then (if i < 147 then 0 else 0) else (if i < 149 then 0 else 0))))) else (if i < 165 then (if i < 157 then (if i < 153 then (if i < 151 then 0 else (if i < 152 then 0 else 0)) else (if i < 155 then (if i < 154 then 0 else 0) else (if i < 156 then 0 else 0))) else (if i < 161 then (if i < 159 then (if i < 158 then 0 else 0) else (if i < 160 then 0 else 0)) else (if i < 163 then (if i < 162 then 0 else 0) else (if i < 164 then 0 else 0)))) else (if i < 172 then (if i < 168 then (if i < 166 then 0 else (if i < 167 then 0 else 0)) else (if i < 170 then (if i < 169 then 0 else 0) else (if i < 171 then 0 else 0))) else (if i < 176 then (if i < 174 then (if i < 173 then 0 else 0) else (if i < 175 then 0 else 0)) else (if i < 178 then (if i < 177 then 0 else 0) else (if i < 179 then 0 else 0)))))) else (if i < 210 then (if i < 195 then (if i < 187 then (if i < 183 then (if i < 181 then 0 else (if i < 182 then 0 else 0)) else (if i < 185 then (if i < 184 then 0 else 0) else (if i < 186 then 0 else 0))) else (if i < 191 then (if i < 189 then (if i < 188 then 0 else 0) else (if i < 190 then 0 else 0)) else (if i < 193 then (if i < 192 then 0 else 0) else (if i < 194 then 0 else 0)))) else (if i < 202 then (if i < 198 then (if i < 196 then 0 else (if i < 197 then 0 else 0)) else (if i < 200 then (if i < 199 then 0 else 0) else (if i < 201 then 0 else 0))) else (if i < 206 then (if i < 204 then (if i < 203 then 0 else 0) else (if i < 205 then 0 else 0)) else (if i < 208 then (if i < 207 then 0 else 0) else (if i < 209 then 0 else 0))))) else (if i < 225 then (if i < 217 then (if i < 213 then (if i < 211 then 0 else (if i < 212 then 0 else 0)) else (if i < 215 then (if i < 214 then 0 else 0) else (if i < 216 then 0 else 0))) else (if i < 221 then (if i < 219 then (if i < 218 then 0 else 0) else (if i < 220 then 0 else 0)) else (if i < 223 then (if i < 222 then 0 else 0) else (if i < 224 then 0 else 0)))) else (if i < 232 then (if i < 228 then (if i < 226 then 0 else (if i < 227 then 0x1691bee2db957c9e849a21b0f386e630315509443ea18a08f82dc0aa000016915d42e19584a0c4aa2220f9070e321160099440e19809d03580ca00001690fe12ca94b09a64772120f106da30814e890c3be18309103000b4000016909dc2ce14e89ba47a20d8ef46bc2f714888f43c218708f02e40b8000016903e52c394b89a447a20d8f046c830215188e439a17108f82fc0c40000168fdea2cb14dc9b64782120ec06b22f214a88d43a017508882f00cc0000168f7ca2da15489f249121a8f546e231215709203c618708982c40b60000168f19a2e89598a1049921d0f5870232816009843fc19709803540d00000168eb842db15489e048d2150f2c6e230c15009103c818d08f82f80bc0000168e5892ce15249ca48f2170f346c42fe14c890c3b417708b02f00b20000168df8a2cb94b89a447820c0ef86c22fc14b08d43b617708f82fc0c60000168d98a2cc94e09ba48220d0ee46b22f414c88ec3b216908b02e80ba0000168d3a12c394949924622030e886822e014288c83b417f08d030c0da0000168cdbb2cb94a098845b2030e9c6982f514b88f43c417c08d02d80ba0000168c7b72cf94e49ce4862160f046c030514e89103be17908b82f80bc0000168c1de2c0148498e4701ff8ea468e2f314e88bc39e17608c02cc0aa0000168bbca2dc95449da4892178f646ea31815c09683de18609303140dc0000168b59d2df9568a0c4a72240f6c70a322161096c3e618f095030c0ce0000168af772e29598a1a4a52240f9470832515e098841619f09983480d60000168a9852c714a49924702030e9c67a2ea14488e039e17b08e02f80ba0000168a39f2c114849644581ff0eb469a2e9143087038a16107d82a80b200001689d762e195749ee4962148f006b62fa14e08d83aa16908c82f40a60000168975a2dd156ca0249521b0f146c82fc14c08f03ce17808982f80ba000016891562d8151c9ca48520f0edc6ae2fe14908d03a417b08e02e80ba00001688b392df1588a0c49821c0f406e630c15a09483da18e099831c0bc0000168853e2c914bc9a44742098ec86a82fc14e88e438817108982f00b600001687f522c914ac99a4622010ea86a02ed13c889439616c08802c80a8000016879402d715089ce47e2110ef46c42f214a08f03be18108c82c40a4000016873572c0145897245e1fd8e786982ec144089c39817208b02e00a600001686d582cd14dc9ae46f2070eb46822d413c087c37816608482c40a40000168675b2d0152c9d248e21a0f546e630a15609243d4186096031c0cc0000168613a2d99548a0049d2238fb0706325165099c3f619b09d03580e400001685b3a2ce95189ec4982190f486d030815309043bc188094032c0be000016855332d715309e04902180f4c6ee31b15c896c3e819a09603080b200001684f4c2c8148c98e46c2078eb86bc2f914d08f43c618e09483400da0000168494c2ce95089ba47b2110f106cc30615689483e218c09b83480c80000168433d2d615009b847f20d8f206b62f614a89183d818c09503340ca00001683d552c294b09a046b20a8ef86ca30515089203d218408f030c0bc000016837422d195209e249621a8f646d030815408f03e418a09403440ce0000168313f2d295009d049521f0f686f831d159891c3cc18108e82f80be00001682b362d095389d44932208f8470632916709b440819109283100cc000016825592c514c49aa46e20b0e806882e414908d03ba17909082d40b200001681f502d295389dc4892198f386ca2fe15109203da18d09003100c0000016819452d5951c9e84942188ef86c22ff14e88d83c218209003100be0000168135c2c694cc99c45c2030ec46882e614a08f43c418209283380b800001680d732c894b498447120a0ec06b22f914808b839617708702f40c20000168077e2cb94bc99c4742088ea869a2f114708cc3ae17c08d02c80a8000016801622e6959ca004a721e8f686de30b15589203ce19509303180dc0000167fb2d2e3959ca164a42248f746e831415789543dc18b094032c0c60000167f5242d795109b64722080ee86a02ed142089438016608b02dc0cc0000167ef202d014c49a447e2108f106d231015989683da18909583180c60000167e92b2cd14e89bc47c20d8f146cc30815b094c3da18f093030c0be0000167e3232d214f89c447620b8ee06b42f814d88e03ba18009402fc0cc0000167dd362c714dc99c4752080e986842eb14308a038416608502d40be0000167d71f2dc95789f84952160ee06c830b15809143d418d09083040ba0000167d11c2ce94e09a047820c8ef46ca2fa14708c03b817408b830c0d00000167cb0c2d515189d449221e0f346d431415b894c3e419109503200b40000167c5372b794489664562030e9c6922e214188b039216908802b409a0000167bef12ed95b4a2a4ad2288fb46f231815d09603e618809703480d00000167b8d82d995409e84982178f506e230915589143d817a09503300c60000167b2b62df15549f049c21e8f446de31315a09303d819b09203280c00000167ac9e2d8952c9cc4922198f086d030915809303d818a09603200d20000167a6752ea15c0a0649e2190f646d430715308ec3c418208e83080b80000167a0952bf947c9804641ff8e7867c2ee14488cc39e177091831c0bc000 else 0x16a9e242bc147c99047320a8ef06c430915689203c019109303240ce000016a98162d795009c84882158f386b42fc14e09203b818008f83000ca000016a92032d615349d04952190f446e630e15a89684041a409b03540da000016a8c0b2cf14fc9bc4812138f246c42fd14c08d43b617f08f82fc0c6000016a86102c894bc9a64752080ee06b42f714e08d439e17808982e80ac000016a7ff82db95609da4942180f506f230c15489003cc18309282e80b8000016a79fc2c614809944672030ecc6ac2f914588e03b417d09002e00b0000016a73f22cf15189b647f2110ed86ae2ef14888ac39817f08e83000be000016a6de22dd95649f24862150f086b22fd14c08e43a217008882e00ba000016a67f82c814c498a47020a0f186e431215809083ce17f08a82e80aa000016a61fa2cc94e09a647c2158f506fa32215f893c3e418a09502f40b8000016a5bbe2ee1620a464c3230900473e33916e09e84241a409b03400c8000016a55c52c314a499c4792098ec46962f314f88e83c217c08c02c80b0000016a4f9d2e115589de49d21e8f546e631315408fc39817108d03140bc000016a49a82c914c099247d2108ef46b82f614c88e83b017c08d82fc0c2000016a43c82bb94849704501fa8e5c6622d513e887c38815d08182bc0a4000016a3da82e395749f049d21e8f646f431c15909643e219109803080c6000016a37892e1156c9f84932178f4c6ce30d15889403e619109c035c0ca000016a31792d395249ce48e2140f286f0313158093c3d418309182e40a8000016a2b5c2df1594a204b522c8fb46f631415b09643f019209283180c4000016a256c2c994e49ba47d2078eb46a02f014c08b43a618008c03140be000016a1f432e695e0a284af2260fbc71e33316809c040a1a209d035c0d8000016a19472c994c49a84712070eb869c2f4145889838a16408582cc0ae000016a133d2cf95009cc4862148f146d031315809403ca18d09483300cc000016a0d2d2d315189e649b2238f8c70c317166899440819f09a83480dc000016a07302d0951c9de4922230fd472433b17009b040619709c03440d6000016a01162e095a4a204a72210f486d030114e88f03b417c08f02f00ba0000169fb012d695109b24742070eb069c2e514508c83a417109003000a20000169f4bd2ef95c4a284b52280fa471031715b09543de18f09383140c00000169ee7d2f115f8a424be22a8fc871232315d092c3d018909383240c20000169e8792ce14c89b646e20b0eb069c2f014b88d43b417909203240bc0000169e2c92aa942494e44a1f28e2065a2d3140086c37a16108982e80b80000169dcc32d115109d048f2158f186cc30214d08d43b218c09603080c40000169d69f2de9574a1249d2200f406d430a15189243c617d08682cc0b20000169d0af2c0148496c45f2058eb46a42eb14408a039c17408b82f40d80000169caab2d615189cc47e2130f046ca310154094c3e619809983300d00000169c4b42cf94e89c24832138f146b830015309283dc189092833c0d40000169beca2cc94a499e47f2090eb46b62f914d08dc3a217608f03180d00000169b8892ed15e8a1a4c32328fd071632016389643fc19a09803280ce0000169b2a02c894e09b447c20e8ed46a42ef14988b03ac17108d02f80c80000169acc72ba147898c4602088ea86a42e614908f43b617308e03240ce0000169a6ab2d915049be48420f8f186be30915609143ba17508d02f40b20000169a0bb2c5948499246a20d0ef86b22fa14d88d83ae17708c82ec0be00001699abb2d115189ca49321c8f306ca30a15788f83b618409383340ce000016994a42e115809fa49f21b0f786fa31c15f89983f419e09b83400dc00001698ea02d194fc9ca4862148f506ce304152090c3c818b09103080ca000016988942d6152c9ac4772018ec06a62f714a88dc39a17308d02fc0d0000016982892d515109d248b2100f386be2fb15188f83b217d08982f00b600001697c742dc15689ea48f21a0f786f631615d898c3ea19209683440c60000169767f2cd14e09b247a2058ea06982f314808b838817508e82f80a0000016970852cb94d49c048220e0ed86ac2fa14e08dc3a617208b82e40b600001696a7c2d4153c9e84832128f086cc30415589203d418308d82cc0c4000016964972c794c89a846c2030e986a62f414988fc3dc18209683300c400001695ea72cb14f09b247c20d0ed06b830014a88fc3ac17908e03180c4000016958912dd15449f249521b0f846fc31b15d09483d8192096032c0c40000169529a2cf15089da4822108f0c6c830815909383e618b09082ec0c800001694c4f2eb95c8a1a4b02260fa470431615709303d018309403140c00000169465d2ca14d49ac46d2080ed46ae2fa14c08f03b818009482ec0b0000016940612d095589e049221f8f646ee31715b09803ee19109383200b800001693a512d7950c9be47e2140ed06b02f715089043c818809803200c4000016934312dc95689f449f2220f846f031215889283c417d08b82ec0a200001692e492c714909924652000e8c6982ed14c08d83b418309503440d2000016927fd2f315f0a3c4a92200f786fe31a15a094c3f419109903140ca000016922062cd14fc9ac4742088ed46a82eb14808e83a2175089031c0be000)) else (if i < 230 then (if i < 229 then 0x16c1eee2da952c9d648d2158f206da30a15889603f219009403000c6000016c18e52cf952c9cc48220e8ee86c630915209083d818d09603280c4000016c131c2b3941093e4421f48e386722e9141087437c16908082880a6000016c0d1c2d095089c447e20c0ee46b62fc15109103cc188095031c0c8000016c071a2d615249da48f2160f346ce30614f89183bc18b09082fc0c8000016c01182d114f49a847c20e0ef06b8307158095c3dc18208d830c0d2000016bfb102d194e89a847420c8edc69e2f614b88dc3b617308f02fc0c0000016bf56e2ac13e493a4441f80e546702d913e887037616408402e00b4000016bef302e815789f64a021b8f706ec30b15408f83be17608b83000ce000016be9302ce15089c247f20a0eb46922ee14c88f83c618308f82cc0ae000016be3652b8946095a4512008e986862e614388bc39e16d08602d80b0000016bdd4d2db955c9e249921b0f6c6e630715389283ee18d09782fc0ba000016bd7462cf95009aa46e2080ec06aa2f114608c438c17308d02ec0ac000016bd1582cf14fc9c24902198f6071a32715909443e019309883200d2000016bcb702c2948898246a2078ea46a02ea14908cc3a417408482b80a8000016bc5682d995589fe4a32220f946f231115689283ca19009883200bc000016bbf262ee15dca344b822a8f986fc31e15f89803f818909182dc0c0000016bb90a2df956c9ee49e21b8f786f632a16289943fa192094030c0ae000016bb2f62d4154c9e24962130f146e430d15088bc3a417608a82e80b0000016bacfd2cf14f09a247b2128f246b82f814e89003ae17f08d030c0c0000016ba7112c694c49a24742058e9468a2db139889038c17508d02f80bc000016ba11c2c7149097245f1ff8e646742d713f888838015f08182b00ba000016b9aea2e9158c9f649c21d0f746ea32015f09543e219109903400c2000016b94f12d114fc9ba47c20f0ef06c430815909283d217d08f82f80ba000016b8ed02de1574a004942220f746fa31115d09283da18309302ec0ba000016b88a62e41574a0049221a8f6c6f431a15e89643f419609a032c0c6000016b82cc2bc147c97c4652070ec46962ea143889c39417108c82e00c2000016b7cce2d295209b447820c8ef46a82f114f88f03b817d09483280d6000016b76b82da95609f249b21c0f646e231115b09543da18d099034c0d4000016b708b2e615b8a144a221e8f5c6f031b16109743ec19909403100d2000016b6a962c714e89ac47f20c8ef86c430914f08d43ba18009383080be000016b648b2cf15089b847b2098ee46ba2fe14d89043ea18d08f03140c6000016b5e812d394fc9cc4872108f006e630115489043b817d08e830c0ba000016b58762d014e89b247620a8edc6b22fa14b08e03a616f08702b80a2000016b52632d695309e64842110ef46d430415389143ce18b09383140ce000016b4c742c794bc9964612040e7c6862ea14888bc3ac16e08682980a8000016b466a2d8953c9d649421c0f806f030915388f43ac18008f83180c2000016b40a52b294249584531fe8e8c66c2df14508a039a17808c82d00be000016b3a8a2e215a0a0449d2198f8470831d157092c3d818a09403440d8000016b34842d99574a024a72228f486dc302151092c3d4192099033c0d0000016b2e8c2cd94d09b647920d0ec86b02ff14f89043ae17809082dc0c0000016b286c2e015409d847a20f0ee46a42eb14a88e83b816e08e03080be000016b22502e51598a144a621f8f686f031d15909383dc18709182ec0ac000016b1c472d395149dc48b2130f446da30d15309183ce18308e02ec0ce000016b16472d194f49b44712020e686762dc13c085036e15c08102b40b4000016b10472d5151c9d04822170f206d02f714988cc3ba17908e02e80b4000016b0a1f2e295509f64942178f506da30215188f43ce18509102f40b0000016b04322c994b899a46b2038ec46a22e714288b43be17708f82f00ca000016afe002e51580a044a521f8fa071031d15909303fe19209983140c6000016af80e2c794c899c4802120f0c6ca30714e890c3d218308d03140b8000016af2312be947098a4632040eb46a22f514788c839e17508702b00aa000016aec3d2cc14ac9a246f2070ec86b830615489183d018909a83600d4000016ae65a2c614b49b047d20b0ee46a42f214988a838e17108b03080d6000016ae0492d614fc9ba47b2138f286d4312155893c3c218609603100ce000016ada562d315109ba48320e0ee46b22ff15008e83d217b09083100b8000016ad42b2ea15b8a184b42278fc071232415d89403e218b09703200ce000016ace2f2c694d09a447a20f0ef46a02ee14b88ec3b4184093030c0d2000016ac82c2d2950c9ba48020f0ee86c22f214a08d43a817909203040be000016ac23b2c714e09ac47f2118f086c430515589243ce18a09083100c4000016abc522c2947496c4672068eb06ae2fe14e08e43ba18109403040c6000016ab62e2dd9578a004aa2268fb072233516809ac4101a209e83540de000016ab01d2db156c9f449a21b0f406cc30314e88f43be16f08d82ec0b8000016aaa182d695109ba4792100eec6bc2fb14f08dc39e17608c83180bc000016aa4072d695389e049a2188f306d630f15209003ca17f09002ec0c2000 else 0x16da0ab2da95689e048a2198f2c6d831815989483d818b09182f80c0000016d9abe2c994ec9ac47e20e0ef46ba2fa14888c83b017908d83180c2000016d947e2f115dca2e4b822d8fec726334166898c3ec18d09a83340d0000016d8e8a2c994e09b647720f8ef86cc30a15709283d618408f02e40c0000016d88a52c594c89b04832168f086b630815309143ba17908e03140ca000016d82a22d015109b047720a8ecc6a82e814c88b039417108c82f40c4000016d7c902d995609f44a021d0f686d630015609703e618908f031c0cc000016d76952d1150c9d84952180f286d830a15389043b417909103240bc000016d70822d9952c9ce4852190f486c42f014c88d43aa17609203200d0000016d6a562e71594a044ad2210f8c70231f159092040019d09c83480d0000016d64862b594349744622010e746802eb14808d039e16808102880aa000016d5eb32ba144c96444c1f60e606602d713c887c38215d08c02e40ba000016d58ba2c994e49d448c2188f4c6e430b15188d83b617708e02fc0ba000016d52bc2ca94ec9be4842108f006b830515489003da18409583200d6000016d4c9a2e11570a0649421a8f2c6ce30215188e03a017708c82e80b4000016d46922d1951c9b848420f8ed46a62f314508c039416a08302a80a4000016d40b12c194849664552010ea86a42f614c88cc3b018309083000b8000016d3a712ee95d4a244ac2208f946ee312156092c3dc19809a834c0cc000016d34732cc14f499e4642008eb46942e414588bc39816608182bc0ae000016d2e6b2d515189b448420e0ef46ae2fb15088e03b817c09483300c4000016d285c2d6151c9ce48a2148f446e630915789303c618209082f40b6000016d223d2dc15789f44972210f746fc31915d09743ea19209703340cc000016d1c222dc95809f049b21a0f406ce30415409303e018e09203080c6000016d16172d795849f649621b0f586f2311153891c3d2189096032c0c2000016d10272c814d09a847620e8f086d630014e88e83b017508882c00be000016d0a292cb14fc9bc4732098ee86ae30a15189083c618a09482f40b2000016d041e2d595249e248e2148f3c6d82f914f09083cc17e09302f80ca000016cfe222ce94e49ac4812178f146ce30215088f83a817c09203040ca000016cf8002e195a0a1a4a92270fd471c32b16009703e819109883140c8000016cf1e32d9155c9f048921b0f5c6dc30f15a09483cc18f09d03380da000016cebd82d415349de49021a8f386ce30914f08e43b417d09202f00d0000016ce5d02d1151c9ca48c2140f006b830115289103be18909283040c0000016cdfac2df158c9f249d2140f606ea32615c89683dc199098032c0c4000016cd9db2ba145896244f1fb0e706742d813c089c3a217d09183140c6000016cd3db2cf94d89b247f2110f046ba2fa14708d03ae18309603240dc000016ccdc52dd15809fa4a22200f846f232315a89383da18809203280d6000016cc7b82d4950c9c047a20c8ed06bc30914e08ec3b818609182f00c2000016cc1dc2c494a498e4601fd0e686802ea14408d43a817a08a02d00ae000016cbbc22e195a4a0c49b2208f9c72432b15e09703f219709602f80c2000016cb5a92dd15549f249121a8f506da312158891c3d417e08e831c0c2000016cafb32d1950c9be47920b0ef86c030715088f43ca18409483080b8000016ca9882e795f4a384b422c0ff472832a16009603e4193096833c0ca000016ca3832d8951c9d048220e0eec6d830814f890c39a16a08782c40c0000016c9d712d895609ea4962190f186d631015c895c3e418508782e80ae000016c979e2b4945c98a4622020e9c68e2e414608ac3a417508e830c0b6000016c918d2d614d49a447520c0efc6bc2fa14e090c3c818709082e80aa000016c8b722db15249c848b21b0f3c6e030214f89183be17b08f83080be000016c85612d2151c9ba4742108efc6ce2f915089043b818909383080c6000016c7f772cb94c09ba4762080ee46b230415109083ae17908e02f80c0000016c79882c614ac98e4732028ea06922f114808f83ae16e08902d40b8000016c735d2e115909ee49521a8f2c6de30a155094c3e218b09283100b4000016c6d692cb94cc9a847220b8ef06be2f914988b43a817008e82f40ce000016c67612d515249b847e2100f186ca30a15409183ce18809382e40b8000016c614d2d3150c9bc48120d0ef06c230114a891c3d018608f82f80b6000016c5b392d99580a0c4ac2268fa070831f160097c3fc19609983500cc000016c55252d995309e449021a8f0c6cc30a15409183d218209403340d4000016c4f292d295189d448020f0f186bc2f714908bc39217308702cc0a6000016c49322c314c09a04712030e6c6882e814808dc3a417708e031c0de000016c43422c914bc99446a2020ec86aa2f014788d83b217e08c82f00c4000016c3d012e715b0a0449e2210f8c6f431b15609003b817f09083100d6000016c36ee2d5951c9d449621c0f486e830e15689343c618709403100c0000016c30da2d695349ca4862140f186ce30d15789483e81950a383500d0000016c2b002c294c89ae46a2060e986922e514288a03a016f09083180ca000016c24fd2d515249cc47e20b0ed06a82f314789003c218909282f40b6000) else (if i < 231 then 0x16f21cb2cd95189da4942148f146d030a15509383b417d08f83240be000016f1bd22c914ec9ae47720f0f006bc2fa15109003d418a09383040b4000016f15e82c794c099046b2050ec86b630115089143ca17b09282f00cc000016f0ff82cd94d49b246e2078eb469a2f014688b038e16f08882f00bc000016f09fd2cf95089bc47a20a8ed469c2f014608c039616508682b80b4000016f040e2c914d49a047520a8edc6ae2ee14a08e43a816f08b02c40a4000016efdde2e915b8a2c4b62238fac72a33116409783fc19b09a83240c0000016ef7d22d5152c9c64812118edc6ba2f815108ec3ae17f08b83040b8000016ef1c02de15709ec4882138f246dc30e15309203de189091831c0ce000016eebbd2cf94f49d448a2170f686e830f15989303c018508f02f80b8000016ee5b92d194ec9aa47a20a0eac6a02f014588d83ae17b08c02f40c2000016edfdc2b994649744561fd0e5065e2c9136885c36c16508682c00ac000016ed9d62d895389e448c2150f106c830114f88ec3ae18009082d40be000016ed3c02da95389c448120c8efc6c230a14f08f03ae17308802e00aa000016ecd982e995e8a344aa21f8fa470831f15a897c3f619d09c03300ca000016ec7792df15a0a144a82198f4c6de30a152891c3b218d09002fc0c6000016ec16a2da15589ee49421d0f7c6fa31d15d09643e618609583180b6000016ebb6e2cd14ac9964712088ec46942eb14e88f03ba18a09a030c0c0000016eb53d2e915bca1c4a82240f9870432416189583ea18d09483200ce000016eaf3b2ca14f49a847620b8edc6b82f814808bc39a17508a82d00bc000016ea93c2cf94cc9aa4762098ef46c230415009183cc18209583380c2000016ea3152df957ca124ac2200f606e031715c895c3de19309a03300d6000016e9d432bc947896e4541f70e5467a2e113f085437016708802d00ba000016e972b2dd1558a024992210f406d631215689383d218c094030c0c0000016e914b2bf149898e46a20e0ef06a42f014808a839c16b08502f40b8000016e8b4d2cd151c9dc48920e0ed46aa2ff14d08e83a218009282f80b2000016e85542cc15089c648a2190f3c6f231715f89844021a409903380cc000016e7f672c214b899047220b8edc6ac2fa14c08e83d218609083000c4000016e79432e2959ca004a521a8f446ec31615989583ea19609783140ce000016e735f2c194a498c46420b8ef06b62f514988d03ac17808a02c80b4000016e6d662cf14fc9c84862108f146c030015008d83b817f09102ec0ba000016e67422e1956ca0c49b21d8f606f031215609083c2183092832c0ce000016e61432d095449d04912128f186ea2fd14c89183cc19009503380cc000016e5b492cd94f09b847720e0ed469e30115309303ea19e09f03280bc000016e55002f015e0a304b52298fa86fa32115c89443d418708f83280ca000016e4f1f2c914bc9bc4772090ecc6962e814888c83ae17d08e02ec0c2000016e490d2d515389ba4832130f186d030615209043a018009403100c8000016e42eb2de15689f249b2180f286d830015289283d219309783180ce000016e3cf32cd14e09aa47320c0eec6d630214e08e43ac16b07f82ac09e000016e36f62cc14e09b448520e8ec46a22f914908d83aa17c09283140e6000016e30f12d515489e048d2150f2c6d4302155090c3c217a08d82d00a4000016e2aef2c914e899e4641fe8e7468a2dd14088b839217108682d00a2000016e24f62ce14c89a447220d0f006cc2f614b88ec3be17708d830c0ba000016e1ed72e0157c9ee4912138ef46c230015509183c217708b032c0ba000016e18d02d214e09ba4822120f006be30514e88cc3b217b08d02f40be000016e12c92d3950c9b647920e0efc6b830214e08ec3b817d09283340d6000016e0cac2de15889d848e2130f206cc30814f08f83c818b08e82f00c8000016e06a72d6951c9b847420d0f1c6d22fa14d89143c017a08f03040c2000016e00bb2c514d499e4702058e9067a2e414108a439a16608482cc0aa000016dfabe2d495389d44882128f046a22ff14f88fc3a816e08e02ec0ce000016df4b92d394fc9c44802108eec6b02fa14988e83b617908e82f00ba000016dee9b2dc15a4a184a72220f7c6fe31115689143b618209103040da000016de8b92cc94f09a64822120f146b22fa156092c3c618809003080b6000016de2cc2c114a099647420b8eb86982f314b08d43a617608e83040bc000016ddcc82d4953c9dc4912180f1c6c0303152090c3d818109202d40be000016dd6b12dd956c9da49721a8f586e430b14e08e43c418109183140d8000016dd0b02d514e49ba4822118f206de30f15d09783e418209203200ca000016dcab22c994f09a64732010e886942ef14588c83b017708702d40a2000016dc4d62c2148c96c4622060e746842dc14708a83ae18209683340be000016dbebb2da95589ec4912158f2c6cc30815108e83be18909482f80c6000016db8bc2ca94d89ae4692060ebc6942f714d08d43c018809403140c0000016db2b72d315089be47920e0eec6ce31615409403c017e08f03080d4000016dacc32ce94d09c64842128ed86aa2f914d89303d218009203180c6000016da6c62ca14d49ac47620d8ed46a02ee14c88cc3b217b08e03080b4000 else 0x170a3812c994bc98a46f2068ec46ae2fa150891c3c417e09003100ac00001709d6b2d495049b24812100f006c4305154092c3d217a08b82c00a8000017097762cc14e89b447d20e0ed86a02ee14e08c03b218008d82f00b0000017091892c994b89a246b20c0eb46a62ea14508b439a17808982d809a00001708b8c2cc94cc9a84722048ed06a02f414888ec3b018508c82fc0ba0000170859f2c794b899a4672058e8c6a02f814c08c43a617008c02f80ba00001707f862de153c9d24832150f406c430515089003ba17909083000b4000017079962cb94e89b046c20f8f246d22fc14c88f83ba17e09103100d40000170736d2e6157ca024a321e8f806fc32415d097440619e0a203700e000001706d612d4150c9da48c2180ef86bc2f914988a839c16b08b83000b2000017067602d215209ca48620f0f186be2fc14908dc39c16a08802c40ae000017061442e295889f649821b0f606e831815889043c817a08f82f80c000001705b3b2d315209da49721b8f686d030f154093c3d818a09182fc0d80000170550b2e595dca304b62278fa071232916589984161aa09e03280ca00001704f162cb94e89b04802108f3c6d230714b88c439e17a08582c00ba000017048ea2e49580a0449b21c0f6470431c16009603ec19509783280c6000017042e62d5151c9dc4912140f146ac2f814988e03d018109103080ca00001703cec2d0951c9da4822100ef86c82ff15188d83b818109003300d6000017036f22d115109b44752060ea86a22f2150890c3cc18409682f00b8000017030e62da15709fc49c2200fa070c32415a89443de194092030c0ca00001702afd2c114c498e4692070ec86a22f314b08dc3c618609683140b0000017024f62d5153c9cc48a21a0f3c6d630615689483ec18f09602f00be00001701eeb2d094c89b647b2110f206da30e15289283e618909803380ca000017018eb2cc14fc9b24782080ec069c2e414188943a617608e03080c0000017012d12da15289cc48b2158f386e230615108fc3b618009303000b800001700cb82db157ca0a4a121c0f7c6ec31615809243d8182093032c0c8000017006ab2d415209d84912178f446e631115789403da182092030c0bc000017000a32d895549e44882118ed86b42f915109183e018909a034c0ce000016ffa7e2e4958ca0c49721d0f286c42f714a88d03bc18709303440ca000016ff44d2e51590a1649a2208f286c830714e08dc3b018308f02e40c8000016fee1f2e69590a0e4ac2228fac6fe31815a09783fa19509583100c6000016fe8322c894c09a24732088ed06ae2fe153890c3c817808b02cc0a8000016fe2422c4147498045d2010ec86942e013e088439416808602bc0b2000016fdc342d1151c9da4872150f286ca30615489203de17f08f82e80be000016fd6292d695509e048c21c8f406dc30e15409343d618a09482dc0c0000016fd04a2c914e89b648420e8ef46c22fb15209083c018c08f03000b6000016fca6b2c694bc9b447820a0eec6b82fa15089103ca181094033c0ce000016fc47f2c814c49b047220a8eb068e2e814508b038e16708682c40c2000016fbe472e795d4a1649c21d0f2c6d430915d897c40a1ad0a303500c8000016fb85c2c994e49c847d2128f2c6de31915589283d818409403200c4000016fb23b2e095389e649121a8f706e832315b09303c217d09183140c8000016fac382d4954c9d84852198f586e230815989383c617e08e82ec0b4000016fa6232da953c9e849e2218f6c6ea31715989203d818d09403380d4000016fa02d2cd95309c04792118ef86ca30515089143c818b09383100cc000016f9a1f2d395289de49b21c0f486d230d15789383dc17d09103280cc000016f94272c8949c98e4752068ec86aa2f814d08f43b617c08d03000b8000016f8e112da95509ee49921d0f786fa31a16009843e619309803280dc000016f880d2dd957c9f449621c0f246ca31315689583f2189092833c0cc000016f81eb2dc156c9e44952228f846fe325162097c3fa19a09b83440c0000016f7be92d2150c9bc47d20c8edc6a82f715289083c217d08a82ec0b4000016f76112bc94889904662038ea86a42f614988c439c16908982f80be000016f70342b7944c96e4621fc8e586742d813c086c39a16d08482900aa000016f6a162e59584a0e4a321d8f786f430b14b08b83aa17108882c40a8000016f63f82d815189ec4952138f206d430815609183ca17608f82e00c6000016f5dec2d114f49bc47620b0ef06c22ff14f08fc3b817d09102e00b8000016f57b72e115889f649b21f0f506e431415589303dc19309883240c2000016f51af2d595389e44922180f486cc303153893c3c218808a829c0a8000016f4bad2ce14e49b84892140ef46de31015809083b418208a82ec0b2000016f45cc2c694a09924672010e9068a2ee14a089c39e17a08a82dc0b4000016f3fbb2cd15049c64832118f046ba2fd14d08f03ba17a08f82e00ae000016f39b92d015409d44852130f1c6d630715008e03b817c09003280c6000016f33b52d394fc9d24862130f2c6c630615a09143c818a09a830c0b8000016f2dc32cd14dc99447b20f0ef46be2ff15109043a817f08f03040b8000016f27bc2d515009b847d2120f106c42fe15008f43be18709583140ca000))) else (if i < 236 then (if i < 234 then (if i < 233 then 0x17224342de95949fa49521b8f7c71632b16189883ee18809103040bc00001721e332ce94f09c247f2118f086c430515109083c218709403200b40000172182c2d795249d048a2150f006d630115609403d217d08a82d80b0000017212422c514ac9a04762048eb86ac2fe14f89143ae17308e02ec0b600001720c592c1947896045a1f90e7067a2f014c08e03b817808c02c40b6000017206672cd14e49ba4842118ef46b82f114588903a216c08702e40c2000017200642d495289cc47b20b8ee86b8300153892c3d418408c82e80c60000171fa552da95449b847420e0ec46982f414d09283d218c096031c0c80000171f4702c4948098e4612038ed06ae2f814889103ca19009703040b60000171ee622d194e89be4822138f0c6ca30915489383ee190095831c0d80000171e8552d415109aa4782088ee86a82fb14f09283da190094831c0ce0000171e2432d715389e249721f0f7470e31e15809683fa19f09b032c0d00000171dc602bd146498c45e2020e8c68c2e914008a83ae17f09483100be0000171d64a2d194ec9c247b2120f4c6d62ff15809383c818b09983140c40000171d04d2cb94dc9a847b20f0ee06b230b15389183cc18408f02e40b80000171ca542d014ec9ca4852138f1c6ba30014b89103ca18208f83000a60000171c43b2d815549da48b2138ef06bc2ff14e09303da18609a03240e20000171be422cd94c49b84802150eec6a22f114988f43b017808802dc0b60000171b82d2d7950c9b64742050e846922ea142089838416008202980b00000171b2262d615209d448e21e8f6c6fa31915909403dc18d09402f40cc0000171ac382c6148c99246c20a0ed86c030014d88f43d818208e02dc0b00000171a61a2dd15749ee4992220f6c6d830014b090c3ca17e08f02d80ae0000171a0332c4948895e4572010e946942fb15009483c617b08e82d00b200001719a5f2c214a898a4702040e9c6922ec14788e83ca18009383240d0000017194792c4947c99246a2088ea069c2eb14508a43a417e08a83080b400001718e752d8156ca084a521e0f8c70a320166098c3f819c09883040d2000017188632d9952c9dc4922170f106b830115189203b817808a02e80bc0000171825d2d595089d44842118f306e231715b89683e817b08d83080d600001717c6a2c294c09a847c2070ec46ae30014f88e83a817608c82e00b20000171765a2d915449d04902190f246c62f815109143ce17e08e82e80c2000017170572cc14e09a64692038e9c6922de14608b83ae17708e02d40ae00001716a832bc94849784662078ec469c2f014888bc3ac17608d02e80c4000017164712d895389d44932148ef46ba2fc14f891c3b818509203080b600001715e982b994249784581fd8e546842d714008ac39c17308702c80b2000017158a02ce94e49b84712060ea06a22ec14a08d03b616e08c02c40b6000017152c02c714e89ae47d2130f0c6c02fd14908fc3d218509203100d200001714cb32d495589f449520f0ef06c030414b89243b818709503140ce000017146d12c494f49a447920d8ee46ae2f114c08ec3c018308f82f80be000017140b42da95189da48b2158f0c6b62fa15009143c818009182e00b600001713ac92c214949844571fa8e8467e2e114188b839a17208902d00a2000017134b22d815309da4952178f306e230f157894c3cc18409103080c600001712ead2d215009c64832100f0c6ce2fa14e89143c818309303240be000017128ac2d515289ce4832100f086ba2fd15008e03b217908782b40b4000017122ab2cc94a09a846e2088ed46b02ec14b08e43ba17b08d83080bc00001711ca72d214e49c64802178f4c6d430915209143cc19009b834c0da000017116a22d415589e649621d8f906fe31115609443ee18909182f40ca000017110802de158c9fa4962228f8c70c329158091c3ce181091030c0c400001710a842cf15089ce4872160f106d230e15689443e218d09382f80d6000017104422f115d4a304b922d0fb870e32916589b041c1a709c83280bc0000170fe4d2c794f09b246e2068ec46902f014708c83a617309003240d60000170f8442d715149c64772070ebc6962fa14d88f03a818209183300e20000170f2122e595b4a084a22248fbc71232515f09883fc19b09983280de0000170ebf52dd15349da49721e8f9c70a32915c89583da18c08d83080be0000170e5e02db95709f049a2190f4c6ec31815a894c3d0188099031c0d00000170dfc42dd15449d848a2130f286e831215208fc3b617c08c03140ba0000170d9be2cc14d899c47620c0edc6962e114488ac39417909303000bc0000170d3a12e215889f04a32258fd871032015d094c3ee19409883240ca0000170cdac2c4147c9664591fc0e6c67c2d6140888839016d08b02ec0c40000170c7b42d215109d24802108f006ae30414d08e43a017508a82e00ce0000170c1ca2c414b89a44682068ec46b22fb14e09003d217e08e031c0c40000170bba62e29570a024a02208f8470833016209543de18d09603480dc0000170b5872dc9574a044ae2260f646e6311157095c3d818808d83180c40000170af822d195009c24882170f1c6d431915b89703e61a009c03380ae0000170a97a2d395489d04832168f246d6306153090c3b217708d82cc0a4000 else 0x173a5482c714d49a04732110ef46b42f114788bc3ac17c08782ec0c000001739f2c2d9153c9d04892130f386d230715209083bc17b08e82d40bc000017399402c614a49984672018ea46862e714408ac3a817708b82c00b00000173932b2d495009a64712070ebc6a02ec14a89043c417b08d83100ba00001738d4c2ba947498245f2018e8467c2e9143889839e17308b02d00ac000017387502cd951c9c648220c0ed06a42f414708e43b617408882b80b0000017381572cd94d89aa47b20b8ef06ac2fb14a08d03a417508b82ec0be00001737b322e2957c9fa4a12198f6c6e831415809583de18e095030c0c40000173751f2d715509de48a2148f246e4317159892c3ba18008b02b40aa00001736f352c414d89a446d2080ef86be30315289043c418209003180d80000173694c2c914d09984642068eac6a62f714688d03b618008a82f80be000017363432d214f09c44842168f4c6f231315a89443da17c08f83240ba00001735d562c814c098e4642040eb869a2ee146089c39e17108982f80be0000173574c2d5151c9c449121d0f606dc30a15509283e617c090030c0c0000017351262e315589ea49e21c8f546d62ff15089083cc18609303000cc00001734b162da1564a0049d21e8f606e030215088f43b618208c02d00b4000017345112d215049c447e2120f086be2fe14d89003b017b08d02e40c800001733f162ca14f49ce4822110f146c630414e89003d018c09903140ce0000173391e2ca14d49b647720d0efc6b42fb14c08e03bc17c08e030c0ac0000173332a2d094dc9a64742118f246d02fb15009103b217c09082fc0c600001732d212d9154c9ec49421b8f246d42ff15089083b417c09003000bc000017327372c594989864622028eac6942ef14808d83c218009402f40ac000017321362cd95009a447220c0ed46a82fb14a090c3ca17c08a02ec0b400001731b1b2db95809fe4a62208f906fe31215989883f019c09583300c6000017314f42e315749f64a62228f786ea30d15989483e618c094032c0c800001730f022c894c499847120a0ed86ca2fc14908e43c218209203300d0000017309002cd14f89ba47c20a8f006c030015088e43c017f08f83040ba000017302f22da155c9ea49821e0f646e631415509083b618308d83080b40000172fceb2d494f09b448320e8f006d62fe14e08d83b217408e03000cc0000172f6db2d115349dc4882108f106ca30c15509443d018409103180d60000172f0c12dd15649e649921e0f5c6f631c16009543e819209503340ca0000172eaac2e0957c9ee4972190f3c6d831215309303d018609403000c80000172e4982d7954c9d847e20a8efc6b62fb14d08e43b818109083080c80000172de902d495149c047e20e8edc6b02fb14e89103c017e08882d80c60000172d8942d015109c84812100f3c6f831915889483e418d09383200c60000172d2a42ca14a89864692028e7c6882e5143889c39c17c09182f00b00000172ccd02b7142494843e1f10e306542d9142888c38c17308702d00c00000172c6bf2d2151c9ee49921e8f8c71832616509683fc19609a833c0e20000172c0aa2d915649ee4952180f486de31315589403d218409283180bc0000172ba9b2db15409dc47720c8ec86942f814c88e03a417a08f83100b60000172b49c2ce14bc99446e2038ea06982ee14808c43b417508b82c40a80000172ae982d315249d848120f0ef86bc2fd15388f83d218b09583280b40000172a8c82bc14749784662048eac6842da13f087839e17708902c80aa0000172a2a72e095849f448d2188f1c6c02fb14e08e83ac17c095830c0c800001729ca42d0951c9ce4842118f186d82fb14e89003c418f09803100d80000172968f2df9570a164a021d8f546e830f15489183c818809302f00ba000017290562ea95bca224bc2268fc871e322165896c3ea189097830c0cc00001728a6b2c1149c99846d2060edc6ba2fb14f89003ca18a09883440d2000017284462e295c4a0449821b8f906f6326166099040e19c09703300c800001727e602c594b899a46c2050eb46a62f714f89043b417f08f82f00ba000017278702c694f49bc47b2120ee469e2f514788e03c018409583000b8000017272652da95349dc49d2198f486f230f15789183d018608d82ec0ba00001726c802c114a099646c2058eb86a22eb14508b039816f08702dc0ac000017266622d794f89c447d2110f286c02f914d890c3b617508d82d40c40000172608d2b8945098646120c0eac6962f014c89203cc18809583000b400001725a962d094ec9ba4732078ee06ac2f714688b439a16f085829c0b0000017254b92c594ac97c4631fd8e846922e514488a838c16b08782d80b800001724e982db15409de48c2188f146d030615089083c018309302e40ae0000172488d2d295349f049621b8f706e030d15309103ba18508e82e00bc000017242872d195149c447c2120f246ca2fe15289003be18109083040ba00001723c6a2e0158c9e449921b8f406ee31415489383d419409683340d2000017236522e195489dc4a02208f8c6fc318158895c3e818e09502fc0b60000172305c2ca14b89924682040eb469e2fd153091c3a817e08e03140ac00001722a472dc156c9ec49b21f0f686f632115d89583ee18208e03040b4000) else (if i < 235 then 0x17525fa2d795349d84872150f206b42f714e89183d418608f83200c600001751ff82d114f89ca4812138f246f030f15609143be17908f03040b2000017519cf2e215689fe4892100eec6c02f715089343ec19a09c036c0dc000017513f02be949099046f2080eb86a22ef14588dc3ba17908902f40b200001750ddb2dd95709ec4972198f3c6f231715209343d619009703400da000017507da2cc94d89be4732080eb86902e715209083d818809203000be000017501a82e995aca164a62280fe872632315689343d017c09183180be0000174fb962dc156c9f249821c8f606e631015b894c3d618909203280c40000174f58b2da1558a0049d2228f706f031415189343c817908c82e40aa0000174ef972ce14dc9ac47320a0ec06ba30814e08e43b417a08e82fc0ce0000174e9b72c1949c99a4762120f486d4307153891c3b418008f02bc0ac0000174e3d42be14b899a4792098ec86ae30014f08f03c618509482e00c00000174ddd12d715249dc48b2178f1c6de31615688ec3aa17508903140c80000174d7af2e095749f44902170f1c6d430614b08bc3a417608702c00b00000174d1942df9568a0a49c21c0f586ea31616289783ee19209883300d40000174cb6d2e59598a0449c2228f6470a328163099c3fe19709583100d20000174c57d2c714a89a446c2080edc6c030815308e43b817508a82dc0bc0000174bf982c414c49944692068ee06a62ed147888838e16708482c00b00000174b9b42bc943897445f2000e7c68c2ef14888b839617408682c00b00000174b3c42c394c898c4632080ecc6be2fa15088fc3b817a08a02d80cc0000174ade02c714e09bc4722040e6868e2f114788b839e175090030c0c60000174a7df2d314fc9b046e2010ea86a22ee145088839a17008502bc0b60000174a1d22d695609f44932178f406e8310159092c3d2183094830c0c000001749ba82e495b89fa49f21e0f446d230314f88fc3cc18a09102ec0be000017495c82c294889944641fd0e5465a2dd13c889c3aa17009082f80b000001748fbe2d095149c04812140f046b42ef14408a439817a08d82f80bc000017489942e095549e048e21b0f606d230615189003d218d09402fc0c6000017483b32be946897645c2008e7c68a2f214b88fc3c617608802dc0b600001747da72d315209d048220f8edc6ae2f413d889839216708802bc0bc000017477932da15289d248220d8eec6be30c15889343d218b09282fc0c6000017471a82c794d89ae47d20c8efc6c230a155093c3dc19609583040ca00001746b822df15709e048e2190f386d6307157094c3ec19a09d03380d40000174656b2de15509cc48920f0ef86c430014f890c3d618609003000b000001745f8c2b9944898044c1fa8e786962f214788c439417408b03040bc0000174596b2df15849ea49b2158f486f231615b09383ce18809583240ca000017453692ce14e89b647820a0ed06aa2f414a08e43b017608a02d00aa00001744d622d415189e048e2188f246d02fc14b88e03cc18208f03100d00000174479b2b314389704521fe8e986922e714588a839817208582d80c2000017441a32cb14ec9be47620e0f0c6c82f914f08ec3ba17908782b40b200001743b702eb95c8a364b82290f986ee31115809483d218e09283080ce0000174358b2bd148c9864602008ea068c2e514908f43c618109102f80b400001742f8d2cd94fc9b04732088ebc6ac2f2144089039416908702e00bc0000174296b2e195a0a0a4a02200f8471031b15a89343c417908b82e40ce0000174232b2f215e4a264a92290fb871c32d16889bc40a19f09e03380c200001741d052dd956c9f24992170f086d430414988c83a217308682e40b20000174171f2c114a499245c1fd8ecc6942dc13e886037a16d08a82e40ba000017411392c814d09b647220e0efc6c230c15209003b618209603180c400001740b342d614f89c647820f0f046c82fa14e08b839a17408d02e40a6000017405352cf14dc9bc47b20f0ed06b62ef14508d03b018108f82fc0bc0000173ff372da157ca0e49a21e0f8c6f031415989683ee19909a03400e40000173f96e2b7946c97645d2010ea869c2f114f09103d418309583140cc0000173f35e2d615609f848e2168f2c6c62ff14d08f43b017708902ec0c20000173ed0a2fb9660a5c4c02308fe471e32d16689b842a1ac0a203400d80000173e71f2c394b09964642060e9c6882ed14188cc3ac17d09002f00ca0000173e12b2ce94f499e46f2058eac69a2f314a88d43b217a08b82e40b40000173db272d815389de4932170f246ec31e15d095c3e818909403400ce0000173d5132d695109c647a20d0ed06ce30d15408e43ac17208982e00c20000173cf052d59578a0449b2208f7c70632216089543ec18b09003080cc0000173c9042c914b499a47020b8ee86c030014a88c03ba17e08e82f40ca0000173c3272bc942896244b1f78e7c6882e614608f43ae17a09483300cc0000173bd302cd94f09bc4802100f086b62fa15389203d418a09403040b60000173b7192d915689f649f21b0f5c6e4310156894c3e219309703180c80000173b1172ce14c09a846f20a8ef06c030215189043ba174090831c0c40000173ab3b2ba144495c4451ee0e046382c8134085038216708282b80b8000 else 0x176a7bc2da95349e448f21a0f586ee31515f89743f619709a035c0e40000176a1c72cc14d09c047e20d8ef86b830615008f03b417308a02ac0b400001769ba12df15489dc4812128f186d82fc14c08d83b817e09082fc0c0000017695a62d315209b046c2048ed86ae2f614508e43ac17f08e02d80b200001768f882da15549f449821b0f406d631215409283dc18b09403240da0000176896b2df1590a0049721a0f146cc30815308fc3ba17608802e80b0000017683522de15649d448f2158f206e631515a89543da187096032c0d600001767d572d015149b64762060ea06862e414908c439216808902dc0a40000176775c2c694cc9984752090ebc69c2f314a89043b217a09102f40a8000017671792bd145c9744551fd0e9c68c2de142888838815d08502ac0b200001766b672dc15549de4832150f446de30215308e83be17508c02f80cc0000176655e2dc95649dc4852160f286cc30415208e43be18109483180c000001765f542d515189c84852198f8470232015b89643d6187096031c0c8000017659572ca94c899a4682028ed86a82f314a08e03a617908c82cc0b8000017653602c5147c99447220a8edc6a02f314588c83a416b08682d40a800001764d4e2d795249ce48a2170f246d430d157093c3dc18f094831c0ce000017647272e69590a044942188f646e030e155090c3bc17d093030c0b8000017641352cd94c89a847820d8f046be30515489103dc18f09283100d000001763b412c714b499a47320c8ee46b42fa14a08e83b417a09383240ba0000176354e2d295089b64722058ebc6982ed14288b03ac17a08b02e00bc00001762f3d2d815449d048c2128f186c030214e89303ce18d09883000c00000176292d2dd15689e24882138edc6b42f9145888838e16a08482dc0c2000017623252d2951c9c647c2100f046bc2fd15389083dc18209102fc0d400001761d172d215109b247720d8f006c030215409043c618e09203080c4000017617242c5949c98846c20a8f206ca30514b09083ca18809483000a8000017611012e215709ec4962160f6c6e430d15889283d418108d02cc0c800001760b012d294fc9c64832158f0c6d42fd14f88f03ac17408a82dc0be000017605422ac13f49384431f18de86382c3130881c36215a08582d40c20000175ff412d015109c847e2110f006c030515489043cc18c09503100c00000175f93c2d095089c04862138f346ca30315309043ce18509583200bc0000175f32e2d995549ec4922158f386c830315409383ec18e09e03540d00000175ed002e815c0a0e4aa2248fa46fe31315909143d418309102e40b40000175e7022cb94a898c47b20c0ee06be30414b08c43ba17a09983380cc0000175e0d92e595c09fc49e21a8f606d430e15189143ba17d09002f80d80000175dadc2cd14f09c048020f8f406de30e15609183e619509c03400ce0000175d4d02d415049ac4742050ecc6b22fe15188c43a016b08782c80b40000175cecc2cf94fc9ae47720f8ef46b22f414d89203c217e08e82f80bc0000175c8cb2ce95089be4882118f2c6d030b154891c3ba183092030c0ca0000175c2e32c994cc9ae47720c8ee46b02f914908dc3a817708c02d00ac0000175bcff2bd947899246b2058ee469c2f914f89083a017508502b40aa0000175b6fc2d515249d047f20a8ee86b22f314908c83b617c09082f80c80000175b0ef2cf95289d048320d0ed46ba2f915208fc3ba17908b02f40b60000175aaeb2d115049c448f2198f3c6e630b15d89603ee19409403140ce0000175a4c02e09578a0049e21d8f406e831315689103e618d09583340d200001759ea72df159ca0849c2200f7c70231b157892c3ca18209002e80bc000017598792df9570a044ad22a8fbc6f431615889483cc18909103080c0000017592692d0950c9ba4772078ed86ac2f414c08e03b417408882c00b600001758c422e295b0a0a49921a8f7c6fe31a15c895c3e418d09582f00d0000017586312da15609f849d21b0f306c62fc14b08cc3a617c08a82d00a6000017580062e715789f849721d0f586ea318158095c3e218608e02d40a200001757a192cc14b89a046e2070ec06ae2ff15088f83b817808f02e80b4000017573fe2dd95749f048f2158f146c02f014508c43a616d08f02f40aa00001756dc52ea15c4a344b82238f2c6d230d15489203dc18809503140c0000017567fa2bd948497646e2030e906b02fa14f09083d418709382f00be000017562102c914ac99e47220b0ed46c02fe14d09003c2182093831c0c800001755c102cd14e89b24742050ea068c2e714588d03a217408c02f80ba0000175561c2d095149d048d2168f346e830714e08c43ae17a08c02e00b4000017550332c514989724632020e606782e713f88b83a816908d83280d000001754a0a2df958ca144a62210f586fc31415c096c3ee19309583300cc0000175443a2b6943497445c1fc8e4c6702d914188a03ae17308982e40ba00001753e1e2e115749f849c21e8f606fe317159895c3fc19909d03500e20000175380d2d7153c9dc4912130f086cc30d15989603fc19b09a83180b60000175322b2c614e09be47e20e8ecc6ae2f414d89283c018708e03240c400001752c082db952c9f249e21a0f4c6e231315d89643d017d08f82f40b8000)) else (if i < 238 then (if i < 237 then 0x17828382df956c9e849321d0f406ea31315689443ce17f08e82f80ac000017822442ce14dc9cc48a2138f246e030f15689483ce17f08f83000cc00001781c3b2d915509e04952170f3c6ce313155090c3ca18c093031c0c6000017816512be14789604451f78e546602db143887c39416f08d02d00c20000178101a2ea15bca204b62250f8471a32216089703ee19909e83680c600001780a362c314ac9944622020ec06b42ee14788cc3b216f08702f40b00000178042a2cd15009c047e2098ed86ba2fb15189203ca17e08f82f40b60000177fe072e0957c9fa49821d0f846fc31d15c89543e218a09703180d40000177f8062d695209ca48a2188f606fc31715909783e618f097032c0d20000177f2042cf15089c248420e0ec869c2ef14988d03bc17e08702d80b40000177ec0c2cc94f09a647a2150f186b62fe15489343d418809583180b00000177e6212c3947898c4682058eac68a2dd14108b83a817208882f80b80000177dfe52eb95cca104ad2280fa070432715c89403c618a09202f00a40000177d9ce2e115649fe4a221f0f7c6ee31215c89443ec19109883340c40000177d3f92ba945498446620a8ea86b02f914b88b03a617008b82ac09a0000177ce0f2c714c09964612020e686782d813f085c35e15808982d00b40000177c81c2c894a49944642010e886922e414408b03a817d08f02ec0c20000177c2142ce950c9c24852120f1c6a42ff14b89283d418c09703400d20000177bc112cf151c9b24862190f746e831315a89703fc19a09383180c20000177b5f72df15649de48b2190f486e831215609183c617b08d82d80c20000177afe82d4150c9da48f2148f386b42f814908e03b417008b02f40d60000177aa072c2148497e46f2078eb06ac2f814a88d039617108882dc0bc0000177a4232c4148098047020c0ea46922ee15088d43a616a08602c40bc00001779e192d815709fe49b21e8f246d8316159094c3e419909b030c0ac000017797fb2db95449ea49721d8f506d832015a09503e018b09c835c0da000017791f02d8953c9ce48020c8ee86c22f814c88f43c618e09203180b200001778c012c514b89ac47420e8ec86a82ee14788a839817308782ec0c8000017785fd2d015289d84842138f306d0307159894c3da18a09003140b800001777ff92d495049d448d2190f3c6ea30f15c09283d618309503100c6000017779e32da15309d64902170f4c6d630d15c093c3cc188091830c0c0000017773ad2e995d4a1c4a62230f606f031315a09343ec18a09102c40c800001776da72d295109c247b20f0ed46b831115b89543e418809183000c8000017767c22c294889844642048eb86aa2fc14f88fc3b817908f02ec0c2000017761dd2c214789624501f58e2c6582d4139886437a16608582ac0b600001775bcf2d5951c9ba48120d8f046ba30215289143f019b09683000c6000017755b42da15609f649a21e0f9471032315e09984081a509f833c0d000001774fad2db154c9e849021b8f5c6ea30915088f83ba18309403300de000017749a32d095309d048b2108ee06b42fc14f08e83ae17d08782d40a2000017743c22c094a499446f20a0f0c6c030f15809283c618e09a03340d200001773dbe2d194e09aa47c20d0ee86c830915709283dc18609683200c6000017737992e5156c9f849a21c8f5c6d430e152092c3c818008d82e80be000017731992d014d89aa47520f0f0c6c230314b88dc3b217908e82c00a200001772b892dc95749ea49521a8f586f231815a894c3f21a009c03440ca0000177259e2c714989984642048eb46a82f114e08e03b616d08c82e40bc00001771f9d2d094f09ca48b2190f446ce30615809643f219009683340d00000177198f2d415409cc4822108ef86a22f614708dc3b617408e03100c0000017713c72b3141c95c4531fe8e706802e314888d03b217608d03000ae00001770dd32ca14a89864621fe0e7c68a2e314688a439e17f08f82fc0c8000017707ca2d5953c9f24a32208f986fc31715c09243da18909083240dc000017701c32d195149d048f2118f586f031215909483ec19809a833c0d80000176fbc02d595149b448420d0f086d231215709343d018409202f00da0000176f5a92d895549f04902168f386ca30f15309083c818609682fc0c60000176efb42cc95009da4902140f146ca30515189083c618c09b03240d80000176e99d2e0956c9f44962180f506dc30c15809443ee19509503140c60000176e3982d094e09be4772020ed86ba2ef14c890c3d818d09383180b60000176dd852d795309ce48220f0ef86c22fe14f89103ca183097034c0de0000176d7912c894f09aa47320b8ed46a22eb14a88e03b416f08602e40bc0000176d1782da9588a0049e2220f586f030f15709443e018b09503040cc0000176cb812ca14a499c4762128f306c830114708b43aa17c09083240c80000176c5832ce14e09ac47420b8e986a82fc153092c3d418609402e00b20000176bf802d095189c648520f0ef06c230c15789383dc18509383040c20000176b9bc2b4941c94c44c1f78e806962f014a88e43a617108c02ec0be0000176b3ba2cd94fc9c248c2100ef469a2fd14c89083c617e09102f40b80000176adc52cc14dc99e47720d0efc6b02f714d08d03a616a08802f40ae000 else 0x179a9a52e695bca0c4a42248fa870e31f15f09403da18309302f80c40000179a3b42c8149c9864672088ec469e2fb14b08b039e17308a02d40a800001799d8b2e5958c9f449e2250fb070231715d099040018d09483240c80000179978f2d114e09a44872108ebc6b62ed14288a83a817a09003180d2000017991582ea95eca1a4b22278fe471c32a15f09403e619309802f80bc00001798b582ce15089c64812158f046cc2fb14e88f03ca18a09082ec0ba000017985682c914a897645f1ff8ea06a02f014408a438c16608a82e80ca00001797f742cd14e09a247520f0ef06c42f214c08d839e17509183180b4000017979932c294749724571fc8e5867a2e313d08903a417708b82e40b0000017973872d6953c9c848a2180f206d430715589383e819509b83540d000001796d412f415e8a2249f2220fc472632b15e89783f219a09b03480e2000017967282df95609e649e21a8f746ee30b156891c3c217e09203000d40000179611f2cf95189d648220e8ef06ae30015008f43ac18509003100ba00001795b092dd954c9dc4872100f206cc304153890c3cc17a08d02cc0bc0000179551e2c6949099446e20c8ed46aa2f1146089c39817608b82e00b600001794eed2e615809f04982220f6070831815e0974404197094832c0d8000017948eb2cf95189cc49a21b8f746f831d15608f03c017808b82c00a2000017942db2d5151c9d24902180f586f631e158891c3bc17a08882e00ba00001793d112b9948098e46a2088ec46a82fd150091c3b417e08f83100bc000017937062d695289d048420d0eb468a2e714888f83b617e09082f40bc000017931212c5947897e45e2020e986922ea14708a439a17808d02d40ac00001792ada2f49604a404bb22c0fcc72832a16189944041aa0a203580dc000017924e92c914d49b04792090ea46942ed14408a439a17a08b03000d000001791ed42d615489ec48c21b0f8c70431b15c093c3d4185092830c0d8000017919002b8946898a45a1fc0e686882e6143089439216908c03040be000017912ed2d515189bc47520a8ecc6962f814a89003c418609282e80c800001790d312af141c9624591fd8e6c6842eb143888439816a08a830c0be000017907612be14a09aa47920a0ec46b62fe14e08d83ae18108d82e40ba000017901562d795389cc48820c0f186ba2f614d89043c0189095831c0ba0000178fb2b2e795a4a104a521a8f686e6305154891c3de19009202f80c00000178f4ff2e695b4a1049e2200f946f230d15889183d4180092830c0c60000178eef72d415389c84872100ec06ac2f914f09103aa17b09082fc0ce0000178e8eb2d4157c9f84962178f2c6d831215608f83b617308482b80a80000178e2bd2e915a0a084a521f8f846fa32115e09583e419709c834c0cc0000178dcb12d7151c9ce4922170f2c6d830414f09183c018509202ec0ae0000178d6b52cc14f89bc4802130ed06b62fc14a89083d618309002f00bc0000178d0cb2ca14e89b647720a0ec06c0302151891c3d618c09783300ca0000178cac72d5152c9d048520d0ec46ae2f114c08ec3c418509082fc0bc0000178c4ce2ce14dc9ae4792080eb86a82f415008c83b218309202f00b60000178beb72dc95589cc48c2160f50702321159896440419909e03380d40000178b8c72c514949924652000e7067e2e614588b83a217208d02f40ba0000178b2b02d715689f249121a0f286ee31a15b89583e619609b03240ca0000178accb2c0149499a4631fe8e946a22fa14f89003de18109002fc0c00000178a6c52cf15089d64892170f206cc30f15789183d418709382dc0c00000178a0da2c814c899c46d2060ed86ba30615409603ea19609483240cc00001789ada2d095009c44802070edc6b02fc14a08e83b417908d82f40da000017894b22ed15a8a0c4a42200f906fa32215f89583e818e09703500e400001788eab2d315049cc4782098ee06ac30214f08f03c418108e82fc0bc000017888c52bc945098845f1fd0e846962ed14288a438016508682e40b0000017882862f095cca264ba22a8fd472632f16209983fe19d09d83500c200001787c972c594c09924702078f046b230515309083c418309303040ce000017876952d315049d248c2108ef46ae2f514908a83a818109383100b80000178707a2e2159c9ea48c2158efc6c630b15609583d818509002fc0ba00001786a742d3154c9d848c2138efc6c630715289203be18608c82e40b40000178648c2c794ac99247020c8f086e2315156094c3ec191099835c0e800001785e9c2c494a098646d2040eb46a02f014a88c839016a08802f40a80000178589b2ce95089ba4702058eb466a2df140889038216408402dc0b60000178527d2de15749e04952188f386d430815309143ae17208a82e00ae00001784c652da15609f048c2118f346ce310154893c3e618c09883280c40000178467e2c794cc9b24702060ec46ac2ef14e88e83b817808e82f80b6000017840772d115149c04802090ee86bc30315309303c817d08e03100d400001783a882cd94e49be4782028ea46902f014c08dc3a817008602dc0b2000017834562e495989fe49d21e8f6c6e6315156093c3e418e09282f40b600001782e5b2cc14f09b44772140f1c6c030115109183d418008c02dc0aa000) else (if i < 239 then 0x17b29992cd14fc9b04722100ee06be2fb14d88dc3aa175090030c0c8000017b23952d795289da48520e0ee86b22fb14e88f43c0180090030c0d2000017b1db62bb145095a4511f70e306782de14288a439817c09083180d4000017b17b62c894bc9ac47720d0eec6b630115088dc3ba17008602f80be000017b11cf2c3148497c4642070efc6c230214f89003c817608982e40a8000017b0ba42da15549e449721d0f5c6cc30215889503d418609603340d4000017b059e2d215049c247a20e8ef46c230815108f83c418109103040ce000017affc82bb946896c4652038eac6982f514908c438c17208802f00b0000017af9e72c3149898c4642040eb06a82ec14508bc3b617c08982ec0b4000017af4052c0947898c46b2090ea86882f414b08fc3bc18109303040c4000017aee022d695409d84842128f186c630115088f43c016f08b82f00b0000017ae7f22d5151c9c247820c0f106c630014f88dc3a217508b82c80c0000017ae1dc2d7953c9d648d2170f506d030b14f89143ce18309403100c4000017adbe52cf94fc9be47720a0ed46a22f614e88f43b618409202f80c8000017ad5e82d095089cc4792138f306cc30e15b09503ec19209703240c8000017acfd52d715549e848c2190f446d030415008e83c018108b830c0ae000017ac9b02e19598a0c4a721b0f606ec30e15909403d618209403180ba000017ac3bd2ca14d49a446c2030e906922f114708c83c4181091030c0c4000017abdd12ca14c89a44732068eb06982f314d88f83b217d08b83040ba000017ab7c62d795249b847820b8f006ce30215308d43a017708602cc0c8000017ab1e52c614b098e4642000ea069e2f114f88e43b217508a03040ba000017aabcd2da15109aa4732048e9c6942eb14808c439417108a02dc0ba000017aa5f22c394b499c4752098edc6ac2ec14188943a217609203040b4000017a9fe92da95489ea4932180f106ce30f15a89483e818609803300d4000017a99f32cb14e09a847920a0ecc6ae2fc14d88f43b417108582b40ae000017a93d32de955c9dc48e2178f306e431116189683e418909383140ba000017a8df22c014c09a847c2180f386ce30a14f89083d418809483180ba000017a881d2bc14549764652018ea068c2e714708c03ac17608982e40b2000017a82142cc94c098c45d2068eb86a02f814c08e83b217109102e80c0000017a7c0d2cf94ec9bc47620a8efc6ac2fc14e08e03a617c08f03100d0000017a761a2cc14dc9904772090eac6902f414f891c3c417e08a02dc0b0000017a6fff2dd15409e449521e0f1c6b0304155093c3d818809083200c2000017a69eb2d395189d04872130f046bc2fd14c88f03be17f09003040c6000017a63d62dd15389ba47a20f0f086c030114e88ec3b417f09102ec0c2000017a5de02cf94bc99647020a0ef06b42f614888d43b217108802e80c8000017a57e12cf95049c44812148f0c6da31215789143ae17208802e00b4000017a51f42c614a898a47320b8f006c430b15509403e818f09703340d4000017a4be92da94fc9dc4882130efc6c430e15809383d818809103100c6000017a45e62d7150c9ca48a2138f046e630e15308f43bc17a08d82ec0b2000017a3fe22d795589ec4992140ef86d22f714f88f83ac17a09083080ae000017a39d92d4954c9ec4902188f186bc30515209043b818008f82d40aa000017a33e52c494b49ba48620d8ec86bc2fc15088d03c0182092030c0ec000017a2dc32de95709e648e2190f646dc30215189103b818709283240c8000017a27af2d995149d04902170f046c6304153890c3c218b08e82cc0c2000017a21c02c714b49a24822160f286d631215689383e218808f83100ce000017a1bca2cc14a49924692068ea86962e614608b839a17808902e80b2000017a15b02da958ca0048f2188f486de31b15709543f018e09603240a8000017a0f9c2d8150c9b848a20c8ee06a02f914c88fc3c8189093031c0d6000017a09982cf15209cc4812170f3c6e0304155093c3ea18c09283140ca000017a036d2e19580a164ac2248fc47483521748a0841a1a80a283780d40000179fd762d1150c9c24852138f146ca30814f89243ba17908c82e00ae0000179f7752ce94fc9bc47a2068edc6a82f315108e83ac17408c02bc0be0000179f1832ca94d099e48020a8ef46b430214c88b83be17d09002fc0c60000179eb892cb94d49b847c20e0f046aa2f414e090c3c018409283200da0000179e5a52c714b899e47620b8ef86ca30115188fc3d218609302f00bc0000179dfc62c094b498e46e2060eac6a42eb144889837e16708902e00a60000179d9c52c894b898e46920b0ebc68e2e314608dc3ae17709002e40b40000179d3be2cc14d49b84802098ec46a42f315089083c417f08e83100ca0000179cdbf2ce15049c64822108ebc6b030015309143d217b08e82e80b60000179c7ae2d594fc9de4872138f0c6c830915208f43b017d09183440c60000179c1d12b6944c9704571fe8ea86942f915088f83b817f08782d80ac0000179bbbd2d515289d448b2150f4c6e231415689043c018709083080c60000179b5b72d5951c9ca4892178f4c6ea30b15289143c818108c82e00c40000179afd12c614a49884612060ee46942ed14708c039e17608a82e80b2000 else 0x17b419300000000000000000000000331169099c4121a40a503740ea000017b3bb22c614e09ac4742078eac6ac2f214608a83b018108f82e80d0000017b35ae2cf95189d24852110f186d2310153091c3da19209403000ce000017b2f892e5959ca144b02258fb4716320160898040019b09a830c0c8000))))))))

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



private theorem b231762 : covered 231762 231882 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b231882 : covered 231882 232001 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b232001 : covered 232001 232121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b232121 : covered 232121 232240 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b232240 : covered 232240 232360 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b232360 : covered 232360 232479 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b232479 : covered 232479 232599 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b232599 : covered 232599 232718 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b232718 : covered 232718 232838 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b232838 : covered 232838 232957 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b232957 : covered 232957 233077 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b233077 : covered 233077 233197 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b233197 : covered 233197 233317 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b233317 : covered 233317 233436 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b233436 : covered 233436 233556 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b233556 : covered 233556 233675 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b233675 : covered 233675 233795 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b233795 : covered 233795 233914 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b233914 : covered 233914 234034 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b234034 : covered 234034 234153 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b234153 : covered 234153 234273 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b234273 : covered 234273 234392 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b234392 : covered 234392 234512 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b234512 : covered 234512 234631 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b234631 : covered 234631 234751 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b234751 : covered 234751 234870 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b234870 : covered 234870 234990 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b234990 : covered 234990 235109 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b235109 : covered 235109 235229 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b235229 : covered 235229 235348 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b235348 : covered 235348 235468 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b235468 : covered 235468 235587 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b235587 : covered 235587 235707 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b235707 : covered 235707 235826 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b235826 : covered 235826 235946 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b235946 : covered 235946 236065 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b236065 : covered 236065 236185 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b236185 : covered 236185 236304 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b236304 : covered 236304 236424 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b236424 : covered 236424 236543 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b236543 : covered 236543 236663 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b236663 : covered 236663 236782 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b236782 : covered 236782 236902 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b236902 : covered 236902 237022 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b237022 : covered 237022 237142 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b237142 : covered 237142 237261 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b237261 : covered 237261 237381 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b237381 : covered 237381 237500 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b237500 : covered 237500 237620 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b237620 : covered 237620 237739 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b237739 : covered 237739 237859 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b237859 : covered 237859 237978 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b237978 : covered 237978 238098 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b238098 : covered 238098 238217 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b238217 : covered 238217 238337 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b238337 : covered 238337 238456 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b238456 : covered 238456 238576 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b238576 : covered 238576 238695 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b238695 : covered 238695 238815 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b238815 : covered 238815 238934 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b238934 : covered 238934 239054 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b239054 : covered 239054 239173 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b239173 : covered 239173 239293 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b239293 : covered 239293 239412 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b239412 : covered 239412 239532 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b239532 : covered 239532 239651 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b239651 : covered 239651 239771 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b239771 : covered 239771 239890 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b239890 : covered 239890 240010 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b240010 : covered 240010 240129 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b240129 : covered 240129 240249 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b240249 : covered 240249 240368 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b240368 : covered 240368 240488 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b240488 : covered 240488 240607 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b240607 : covered 240607 240727 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b240727 : covered 240727 240847 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b240847 : covered 240847 240967 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b240967 : covered 240967 241086 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b241086 : covered 241086 241206 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b241206 : covered 241206 241325 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b241325 : covered 241325 241445 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b241445 : covered 241445 241564 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b241564 : covered 241564 241684 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b241684 : covered 241684 241803 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b241803 : covered 241803 241923 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b241923 : covered 241923 242042 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b242042 : covered 242042 242162 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b242162 : covered 242162 242281 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b242281 : covered 242281 242401 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b242401 : covered 242401 242520 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b242520 : covered 242520 242640 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b242640 : covered 242640 242759 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b242759 : covered 242759 242879 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b242879 : covered 242879 242998 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b242998 : covered 242998 243118 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b243118 : covered 243118 243237 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b243237 : covered 243237 243357 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b243357 : covered 243357 243476 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b243476 : covered 243476 243596 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b243596 : covered 243596 243715 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b243715 : covered 243715 243835 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b243835 : covered 243835 243954 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b243954 : covered 243954 244074 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b244074 : covered 244074 244193 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b244193 : covered 244193 244313 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b244313 : covered 244313 244432 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b244432 : covered 244432 244552 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b244552 : covered 244552 244672 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b244672 : covered 244672 244792 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 231762 244792 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b231762 (joinCoverage b231882 b232001)) (joinCoverage b232121 (joinCoverage b232240 b232360))) (joinCoverage (joinCoverage b232479 (joinCoverage b232599 b232718)) (joinCoverage (joinCoverage b232838 b232957) (joinCoverage b233077 b233197)))) (joinCoverage (joinCoverage (joinCoverage b233317 (joinCoverage b233436 b233556)) (joinCoverage (joinCoverage b233675 b233795) (joinCoverage b233914 b234034))) (joinCoverage (joinCoverage b234153 (joinCoverage b234273 b234392)) (joinCoverage (joinCoverage b234512 b234631) (joinCoverage b234751 b234870))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b234990 (joinCoverage b235109 b235229)) (joinCoverage b235348 (joinCoverage b235468 b235587))) (joinCoverage (joinCoverage b235707 (joinCoverage b235826 b235946)) (joinCoverage (joinCoverage b236065 b236185) (joinCoverage b236304 b236424)))) (joinCoverage (joinCoverage (joinCoverage b236543 (joinCoverage b236663 b236782)) (joinCoverage (joinCoverage b236902 b237022) (joinCoverage b237142 b237261))) (joinCoverage (joinCoverage b237381 (joinCoverage b237500 b237620)) (joinCoverage (joinCoverage b237739 b237859) (joinCoverage b237978 b238098)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b238217 (joinCoverage b238337 b238456)) (joinCoverage b238576 (joinCoverage b238695 b238815))) (joinCoverage (joinCoverage b238934 (joinCoverage b239054 b239173)) (joinCoverage (joinCoverage b239293 b239412) (joinCoverage b239532 b239651)))) (joinCoverage (joinCoverage (joinCoverage b239771 (joinCoverage b239890 b240010)) (joinCoverage (joinCoverage b240129 b240249) (joinCoverage b240368 b240488))) (joinCoverage (joinCoverage b240607 (joinCoverage b240727 b240847)) (joinCoverage (joinCoverage b240967 b241086) (joinCoverage b241206 b241325))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b241445 (joinCoverage b241564 b241684)) (joinCoverage (joinCoverage b241803 b241923) (joinCoverage b242042 b242162))) (joinCoverage (joinCoverage b242281 (joinCoverage b242401 b242520)) (joinCoverage (joinCoverage b242640 b242759) (joinCoverage b242879 b242998)))) (joinCoverage (joinCoverage (joinCoverage b243118 (joinCoverage b243237 b243357)) (joinCoverage (joinCoverage b243476 b243596) (joinCoverage b243715 b243835))) (joinCoverage (joinCoverage b243954 (joinCoverage b244074 b244193)) (joinCoverage (joinCoverage b244313 b244432) (joinCoverage b244552 b244672)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 231762 ≤ index 445000000/512 := by decide +kernel
private theorem starting_value : fast 445000000=23602035 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 445000000=23602035) (n : ℕ) (low : 445000000≤n) (bound : n≤470000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=445000000
    · rw [first,anchor]
      exact starting_value
    · have past : 445000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤470000000 by omega)
        have within : index n / 512 < 244792 := by omega
        have lower : index 445000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤470000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ445000000To470000000
