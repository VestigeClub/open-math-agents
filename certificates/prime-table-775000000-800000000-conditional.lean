import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ775000000To800000000

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




private def radical : ℕ := 0x3e482d04af8365123c153b085140a29d00f4a3a60c71d5ddbe25fc85e34bd82083ceb063c28b99eeb11a9db068cce6499c455708c6cfd387e69a3d2439cc4ed4c7ed7dd9edf83265e2bf5c2d5a568130f1be7d19324127217918f2dc346776bc343a4066d1544b294418b96f07ff3c83de9437e63a851c372f1ea6739ee11d67887b77b2079501098c3524c6fca8c2766215946b7c0898668edf8e786fbae02658efe827726a02b50bfef784e301a014ece23fce9610f3054d0d617feb6512f0ef2238db9bc06d0e8480932a93e4e6b32024897644fdb6696edbf70a587b36af38c55dc36ba63f390d063bcaa9bc38cc84b3c36b06e6e49a3bad75efa542449491d8eec38527af300f4a9e3fc6cacd5e455981bfd97dd9e4e678a06cc7e8d3348480105805f0e71bc14db5862fa88a08ea5c1ee1a5613b338a275d107b6b84bebd647ece0ec8abab3efee9d394ebc0dd534ee6ae616b9a1a30a1dd99b5c26bd3e456b0d87419082c80f295379e97acff5611aa6d8b98e5e4d3e1300d374048cfba518120b4f5092bd612714705c41da9d1bf0a0a9116e7e15420c218a92468eae62e8775b375f041a1aabaf6098a897c4a17ce708b46af21b74f5be1af718cb0e4000f601c9944a7e22d05bbbcc07d39f1d93d082cc51014d7b1bcd6cf7721dfb67e65bbe63e8de01ba03496d0882efbe3eadf355fa33093b07db05d4ba79fe5b42f7ca4280fa88358e2d2a0c738f45e7ae2506f68537b016cdf659fede7ddfa56b8db2d28343638829bf07c7c805896a5addddc48cf22258d93225631bddb28e68957cef29161cf8da4eefe43e3f4de8802a59395797c86bc47d067e9825b2d29d25b8fd2e147739eae4a7ea83718b03a7194d8fb563f307840b3d8d9497c563f6f8368a0c46ff885e7133254757ca04c5c03449aaa340e353998ead93d888e58810f407da47823fc09dcdc63c1b4600ba6b678c913c37710f3d7cd41335342f50389d6d64127aee8a0f41cafa9668685ea8a5141f26914e3ba10120a8a401763208ed25b454d95c5b51569a512d55b90c6cadc224999f7f78d88500750810f8b6d2ab4445eff66c0b6f4b44771c79cc12d0e236fc7c2484b90b18af48ebe024b2321a9a424adef77f694e65f4a5cbe16130ca758c6e58d59d0cd80688235b7b07a3bba55c7d92deececa8a182d93b5b5dbdb19703db2ebcbc22b547e83ef62a5fb37b98f0837e93cfca1e7314d4c833061c624993904feaff80973dea36ad6043d66c5338780dd36aed42c644a3e3466d349363d1e948fa99f2b9bc2bc7708695ce1cb1619cf31dfee876c996a35a1723f5a4385d07ae35cadc7f54fdb40802a8cbfbd47ef37a77f4783778a531de27736c88b2cac3b3b34abab3bb035cf26d416c3ac3ddb40d5cfd0d66f18cdf4ac677405da643544432355ad9841c4715b8fdd2077fb2d797ad0c5f1c409466cca44783bc0efcd55d9e63bc1177119fe2c417f32ddd6f88dc776ec081bcfa0ff645a045613eb94ba775a251a59e221c99401a881663ca375ee48e7c5b2536c53ba85df3204f0eb08aa8b2c708734c0fc264a1564107e6881c3d0c68d12c2696f41bd814b51fbf9e8c8f58a1c924a6f8165a21a14b61fa157efce93d41f5ac40efabfb6cd445dc118e7407e2a33dea430853ed0514b76385813f59be7055574643281107d08d390b5dbac3c3f6ace15c861ed8ee2757575431b85fa9fda597bdd18920ba60e5d6a33c3f33b312d945b672994f5aedfd0c5f2a59c3530fed83ea83fbe7f730deae08ab6c7d3a95c95f284d24bcdaf66aeb6531fa5ac195c211b52bff519f22aa9efaeedb125e167cc0b49076c53726001d6e458bcbbf702abf572cffb265fb108d063bdf81dafe2718a884e63b0394d1d48cf29e764260cd441afb6f9ceb0d57335d3da596d6b27c2e96bafac095ac19c2ddbd484a6524d09a5e761377ece1289b517107f2764c53d88600eebc7f9b8079316efa17704a6741df0b7982b59ef508b3f0870e80b10d2ac994d9d439b5e69904df97ddb12343fb365655ba32c5df9b3c3c3b25a0eb4a1801479d8dfc6db966ee06bfe82b905cad4ac632591ad9ad86a938ba84cd61b970069a71da3ccd346c872076a190291a7d62717d486ee836911cf92ff2b3ee7b3cccd64ef87df8fb934319e25136eb42ace08ed56eada98c22e7eb177b487731c241273543eaf5fd6ac2c59a96ebad229fad7442ec134ffbfc63de9653dda7ccb95d9fa26ebbee42a38a933024aa73c243cfea4c95c6da656ba785dfb2ca3556f975d643b80520e5a8c9b89f264c8a9e6a389f61fe4ec1107e3839f13f1cf9a67792f9ba3dc8eaf92dc28f5e6db59e88a1f9cd9aafc2e122d41cbea2229a6b4a3e1c84c04da7c6353d72ae44c91042900ef8c3310bf0aa1ee2f0d390f5b2d18724e5737bc4dd0c6e493a07db7d170bd883934619914f5c5362eedbd81b97ea1e97e1098d794cef6f21e4630a9dea4739d29739c28b2f7d20930aaaabfbf896d403aefe0990e2f119df4b74bf69c9fa08a5c53943725d7c7e81fccd96dabe5108d924e0c486c2ba44e8e3953188dd4fbf0d08bd65bd9decb1d0bc065d724e0a6f665538a818a96e2dfe99cb9f841b684c6f54a03ba2985584327301270bb2f3448c901706418190a741c29206058187f8829d3c71beb015785c9874cae97be076a859bad3002b33fc1f1fe424697f77ccb615a13b8d4480d6b10b8052614e059736edec8a16f73b05c96057aefa378889fee584994dd7d87b777a919b276dcff99e642a5df30dd26cd78882535700c14c23776a51e28afff8798ac9b69e231fb0af62d555975c0361b1ff7c15942e93cc788f1461914a110898348db9264fd3679085654dc6caf323a3ec5921fb3ebbfa3c3f73aedd1956a79a68176af117bebda3bb5c3eff15c6de12ead1142f300278be18f03b15e0d58582b14e8f99bb33a776e75b1899a3c7d72214f567192d59eaacdf99a2b274bd92df6e5e4418bb64aa55c161f82e1bb0717a80b12c866116dcb7ef016015adedeaece1605c6aa840c20d659d1a05532b9a49d7e6ea90d1ebd9179a94387cb39bcc742c434d9eb19d819b556300b50fc0a145a000cec6a172d088ef2abe37aa6f1ddb0ec7c9959f98b00f713010167274b6ac27151be8ffb98fdcaaa3031385b3ae97c5e8a8b0ce6610109ba2b892f9237e4545ea8fb325914482ca71a100cc4e4dd447df3e04ad51bb9fa7ef5c80c9777f6eb458ee23b6770a652e75f9b796f07ff9777ffac576b4a9861a3426ff618836493ea251a5ebdb16773f81d0321f3440632118bcdd91373cbc42683df108ebba033f222c422545febfe2dc01d6efc011961fa3900fc74d008772f7c60ac1b1e35d7adefa9835e2020cd063436cd4677e5a3b16784b2675cd6bfcc309dc21980922d609a0b8725a98dbf52cb9c3a7673ab9d9440b2d6f17f9d28dcf58586acdc5ec24dd39d06f0aa4d7bcf90cadd4717bbb5abcd1cfd2d9e15f08666c08aa30c1ed3c9da463e89b0f4d3afbf7e4af84c8a2baafa40367cc8f8741d65cb38f0afcd454edd9626a949d61796514fa8e1657c131e3d20e017f6ec4373abb325ae2ad93823b50accf5e3a9a76eab12216f6634824f6d81fa97422d61a6ebb2acb56d0976d639a12e6ef6905b8c963b456d6c6820ae1f0a673bcca2479685e94ace240216da5f7aae1be80c1ceab73c27dde92b7f9e6a83145953c28eb295f42377e023de0158b799b72019f3f05e10f26568f594371c27b80f3ce9bf0721e0255c0edefb5b6a23e4e46047116cf1d0ffc3f9cac84bee60f8a13042747b1ca9258f813b0b98b17c52d0c8ce5bc81fc96b45d46023c894fe5d68583a40bcbb71619fe3f9c5bed993afbe27ce5c71fd37eb96aa1bd4a4f416fcc192ec0a1fbcc5ae2f7858e29bd86e45a2b4352c539c4f1126c0525f37b05b94fdeb51db225ef4d6a3ba0a8a4a5104298b2802269972530163e9d1dcf690353d6bae39f60efc5a3cfe0f7d730c7882e0d2050921acf1dc377a972bbf1c842ef327f7447f0f05141b10a0736afd3623c5600ef7bec29e9919d78799039d2dd46699d8088255fcd29fc4ab485349eedc59fb74bd56f6d1d68304203330c2f27a543efea84c9d2a906c05e2d752912048abe7b186679615b3d6582d815a17095e7fbb92e5660c4bdffb79b342be34222ca15e5c54115a679e390571bb1f9d17ce76a36123930fe90640e194da03fdfb9aba06b4458e905b3caa1e0f6a471ea48dfd5a4ced6250e1c9407780ce60dc880ee3671f9243c2f2a86d60f788968a8053b7b13636ed2477a242825781f307e2614b30d2ed512dc42ff34a3741c3ad7aebf19f28e0bfab45689924ba78ff85936b89cbb552c6b1520099b396e2bdaed7cd4b7b6f9fcdf4f44b91b405abf32e064d4dbb1750d30b931076680f52d14b98a7a726a6ff682755c19c419c6f346d60793faa192dd10532bdfbb9f8e58b30f11dbe4eba41a570901c806eb6b4ad8a951526162b94170baa02f590d44a06191ddbb8ec0abcf6a8e2010be69c6bc3831c2ae6d29bdbe0bec33ca8f952ab3138e70eb97388bdcaba6f8734e2b903d8ff1a6182972b6d160c00e3f58259a4c7cd5c4a3b28afa2ad7ad5e56046e267c8b5b9e81280065fce280f23eba378e27dd080c37924da5aa3fba3bfbdf1e37f28b5ce74a7919eae9974eec7dd21ca9679111150552ae19e32c8ade2acf8959b0007207f38a43d41da509e8172c229d96a8c9135409adbe253a356ff313ab89831afa164d3163195c3bd9716ce4382a1f30022e2ff1756a0f2d7813f5d19ddcf631514ea7d319936858af4ddc96c7c916a4476ac0b4ea110b8370bfa4d7f4d0c9c1eca6108ebab9714bee6f96a70cdf49ee7e3fb00e10b1b6feaa46db2198d2dcde393e647e833f39eaf15572c767d6102f09e2e8a81c08486cced0af2150e22d736090baed4d9c9a4b96d3db1c0a65a8ac8485ece20e09398e44b1b4f9d531c070dc7a1a5c688c0ff4173d9f50caff496d74b4b94372fc316818428e590f72fed22eafcd57c2ae5d47e2ae3e2ca413b9c71da39f2314bb49f0c5163d25699a6be7a0a2a5f9600a4cac4ff8222531b6fad9ec624d46d033fe2cd7c0c4aaf6f9d2b812608c947ead698a982ae58be6bba3dbea6a8a9f50496aeb692afd58d393a23d6bffdd9aa8726266776e29377637e68ad04579750d2cefb5499c119132d3d1b81269fa298866f5bfb5bdf924b9dce7ab9c1c82327e9f98e169187d14d05cfd2ed80b4642abe9d5c8015bcc560809e8ea12137adbd8106feec8656afcbe2ec572d4e4c68e5602aa7f7fc4c8df5b98ec981b8624d1a9b843ee83e0904e0f58e66f421b5c2101d0b90238f26f69f0bcc15cca4fb7a1f577dc32ac65bd93cb209b59d537abc285cdb34a94361eb46f101957e3a776ebffbde189283ba31067c83a2449200e22fde4fb64b3b8dfa50783599f9eafc3a035966eb7bc88e95cd45bacc8c0a47bcfdcd482d827ab4fcc1202b3a42a6a3f652bad65a38234183e2903ab5d03d32416540bc64903f1eb0fa6cf2c52c3f22f021740a17e7bb703bdd632cafb2bf10fffde86e7f9440ceec1309dc8889f0e0304a8ee46632fc8bddf8a9a8eb2b0cfa8508b89941acb64e5d76539b687aa7a735cfa33c5e77d053948502e0535a974b1e20750a098f4d7611cb0ed703013389c4e7a8489aa5feda3f3663f5441871f2d38b3b0396fa679c1ea461d5741367edc9a4e19f640c6793058b4c31f065ee52396073572109d57444dfc5eba69460d20d12bd2acc93b47ac664eb93eb0fd7833d03022fe07a7289116bf2aea147af2eac3d32995361c0e96a9d30b1e9d4e494fa7247ae612d86387e90d93023a508377f6cfcef5910d282363489409d1de70118a63c969233fb01bd5f564e74fd4e600861d4f633ccf5a13b4630269f662095e1ccf80c70b6a822f2587c8e52bd2ad0c613316d5fa77181c9ccabc52854e7f27f9750603fa10e49ecf262e734585e6f9a91c0f13e3e48b88163558e7de196db4cb0b64fc9111c74fbb1b1c77e58e45f90a7a10ca68cdad48bdf232b30ab8d7d7694b716f1e12621cb85ca009ca5ab87b38a40a906e3f71dd65e4fea048f97c8f434d3ee42de173df88995fc189d76e5ae8d458b073da89e01648031781043318db505ac0501869a51b2925eda5649c89fb82aed4311e672aecc74a6c4bacfa0a121723fdd79fe7f07f96e8b55aefb9d39a4a6eadd8193cbfe8a1a5a68bc72c5aab335e90cf8624b7aa611cd36791c6fbb2bed3925206c2fae463761a2999b79d8f62ce6a74ce44cc7502faa5be520e2c5c18b51b79ab7cfb645c07a706d6da0922c2bce8bdf7d5259521ef37bdfec12f2e249e29a703fb259ef95d70da06e316cf27ea4f3bf2be9959f1aa86760556afb454ed835615c8cbe751da33517f483923adcf253b1503130dfb174840d0d0cb6b553873dc6a18930c300dbdd20e851a3f90b718a14e8fb81a7278ab58521d17cd201103f8cbf86bbe647f88e7faee2d156e585fea8ad73eac7beba99c24aa1f9b08176eaa206d5974f09d4c765b63c7d97215f35240c01ff86b0a0ddd219ae1681d60389ddcce0511ee852268b83332ab4b55842d996e5c8a54eec9a536cbf5b84e3b96a686b6c76878bc7ca8dc21c05a55729fa87ca4e3b75910a22ff9e0ff71b639130d12b26560a4a0985af37ae9385f152a0445956e40011ff98f38418bef23637d8c4427e7f3a8f9c1a522c09731c645ddfe17df171bc22599b0e0a2903b3a5e0c41d76537e6a357c5357db48a9020072dc22097a45c72afe496b323cadd9f687790429053758293ffaaa97d2ac20376b4b9c5e8682a61162679824ed382f647cb9ac17cb621368ca37cc4650134d8f3f53f7528607d19b0db418f28266c603e08400d74262725e4cf4588d1e5fd65a84ab1c01d157dcd015623583a75e369ea85578d389fa03e0b2f600362ef938aa2adafaeba4d708f47fe7da6b1869fbb6d0050d39595c4be003cffee2e8a98d481c2c90523dab2ab831d7da63ec88037ea838e354a0cebbfc8babc98bf82deadb0743428c24fe4702e1a443d6c6087d732109155b1d5982e

private def light (n : ℕ) : Bool :=
  if n≤168 then decide n.Prime else n.gcd 252607574497319838753801886917134114678628321660161899636045172255501630469951484784279524860515748677740723676917456344471493998101035608260664837215715659672830848592352788164518364067464570288846442542901808782229015393754650015551921726612213033664926565007360000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤28284) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 168 = 252607574497319838753801886917134114678628321660161899636045172255501630469951484784279524860515748677740723676917456344471493998101035608260664837215715659672830848592352788164518364067464570288846442542901808782229015393754650015551921726612213033664926565007360000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 168 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤28284 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 55 := by unfold smallValid; decide +kernel

private theorem sp55 : smallValid 55 55 := by unfold smallValid; decide +kernel

private theorem sp110 : smallValid 110 55 := by unfold smallValid; decide +kernel

private theorem sp165 : smallValid 165 55 := by unfold smallValid; decide +kernel

private theorem sp220 : smallValid 220 55 := by unfold smallValid; decide +kernel

private theorem sp275 : smallValid 275 55 := by unfold smallValid; decide +kernel

private theorem sp330 : smallValid 330 55 := by unfold smallValid; decide +kernel

private theorem sp385 : smallValid 385 56 := by unfold smallValid; decide +kernel

private theorem sp441 : smallValid 441 55 := by unfold smallValid; decide +kernel

private theorem sp496 : smallValid 496 55 := by unfold smallValid; decide +kernel

private theorem sp551 : smallValid 551 55 := by unfold smallValid; decide +kernel

private theorem sp606 : smallValid 606 56 := by unfold smallValid; decide +kernel

private theorem sp662 : smallValid 662 55 := by unfold smallValid; decide +kernel

private theorem sp717 : smallValid 717 55 := by unfold smallValid; decide +kernel

private theorem sp772 : smallValid 772 55 := by unfold smallValid; decide +kernel

private theorem sp827 : smallValid 827 56 := by unfold smallValid; decide +kernel

private theorem sp883 : smallValid 883 55 := by unfold smallValid; decide +kernel

private theorem sp938 : smallValid 938 55 := by unfold smallValid; decide +kernel

private theorem sp993 : smallValid 993 55 := by unfold smallValid; decide +kernel

private theorem sp1048 : smallValid 1048 56 := by unfold smallValid; decide +kernel

private theorem sp1104 : smallValid 1104 55 := by unfold smallValid; decide +kernel

private theorem sp1159 : smallValid 1159 55 := by unfold smallValid; decide +kernel

private theorem sp1214 : smallValid 1214 55 := by unfold smallValid; decide +kernel

private theorem sp1269 : smallValid 1269 56 := by unfold smallValid; decide +kernel

private theorem sp1325 : smallValid 1325 55 := by unfold smallValid; decide +kernel

private theorem sp1380 : smallValid 1380 55 := by unfold smallValid; decide +kernel

private theorem sp1435 : smallValid 1435 55 := by unfold smallValid; decide +kernel

private theorem sp1490 : smallValid 1490 56 := by unfold smallValid; decide +kernel

private theorem sp1546 : smallValid 1546 55 := by unfold smallValid; decide +kernel

private theorem sp1601 : smallValid 1601 55 := by unfold smallValid; decide +kernel

private theorem sp1656 : smallValid 1656 55 := by unfold smallValid; decide +kernel

private theorem sp1711 : smallValid 1711 56 := by unfold smallValid; decide +kernel

private theorem sp1767 : smallValid 1767 55 := by unfold smallValid; decide +kernel

private theorem sp1822 : smallValid 1822 55 := by unfold smallValid; decide +kernel

private theorem sp1877 : smallValid 1877 55 := by unfold smallValid; decide +kernel

private theorem sp1932 : smallValid 1932 56 := by unfold smallValid; decide +kernel

private theorem sp1988 : smallValid 1988 55 := by unfold smallValid; decide +kernel

private theorem sp2043 : smallValid 2043 55 := by unfold smallValid; decide +kernel

private theorem sp2098 : smallValid 2098 55 := by unfold smallValid; decide +kernel

private theorem sp2153 : smallValid 2153 56 := by unfold smallValid; decide +kernel

private theorem sp2209 : smallValid 2209 55 := by unfold smallValid; decide +kernel

private theorem sp2264 : smallValid 2264 55 := by unfold smallValid; decide +kernel

private theorem sp2319 : smallValid 2319 55 := by unfold smallValid; decide +kernel

private theorem sp2374 : smallValid 2374 56 := by unfold smallValid; decide +kernel

private theorem sp2430 : smallValid 2430 55 := by unfold smallValid; decide +kernel

private theorem sp2485 : smallValid 2485 55 := by unfold smallValid; decide +kernel

private theorem sp2540 : smallValid 2540 55 := by unfold smallValid; decide +kernel

private theorem sp2595 : smallValid 2595 56 := by unfold smallValid; decide +kernel

private theorem sp2651 : smallValid 2651 55 := by unfold smallValid; decide +kernel

private theorem sp2706 : smallValid 2706 55 := by unfold smallValid; decide +kernel

private theorem sp2761 : smallValid 2761 55 := by unfold smallValid; decide +kernel

private theorem sp2816 : smallValid 2816 56 := by unfold smallValid; decide +kernel

private theorem sp2872 : smallValid 2872 55 := by unfold smallValid; decide +kernel

private theorem sp2927 : smallValid 2927 55 := by unfold smallValid; decide +kernel

private theorem sp2982 : smallValid 2982 55 := by unfold smallValid; decide +kernel

private theorem sp3037 : smallValid 3037 56 := by unfold smallValid; decide +kernel

private theorem sp3093 : smallValid 3093 55 := by unfold smallValid; decide +kernel

private theorem sp3148 : smallValid 3148 55 := by unfold smallValid; decide +kernel

private theorem sp3203 : smallValid 3203 55 := by unfold smallValid; decide +kernel

private theorem sp3258 : smallValid 3258 56 := by unfold smallValid; decide +kernel

private theorem sp3314 : smallValid 3314 55 := by unfold smallValid; decide +kernel

private theorem sp3369 : smallValid 3369 55 := by unfold smallValid; decide +kernel

private theorem sp3424 : smallValid 3424 55 := by unfold smallValid; decide +kernel

private theorem sp3479 : smallValid 3479 56 := by unfold smallValid; decide +kernel

private theorem sp3535 : smallValid 3535 55 := by unfold smallValid; decide +kernel

private theorem sp3590 : smallValid 3590 55 := by unfold smallValid; decide +kernel

private theorem sp3645 : smallValid 3645 55 := by unfold smallValid; decide +kernel

private theorem sp3700 : smallValid 3700 56 := by unfold smallValid; decide +kernel

private theorem sp3756 : smallValid 3756 55 := by unfold smallValid; decide +kernel

private theorem sp3811 : smallValid 3811 55 := by unfold smallValid; decide +kernel

private theorem sp3866 : smallValid 3866 55 := by unfold smallValid; decide +kernel

private theorem sp3921 : smallValid 3921 56 := by unfold smallValid; decide +kernel

private theorem sp3977 : smallValid 3977 55 := by unfold smallValid; decide +kernel

private theorem sp4032 : smallValid 4032 55 := by unfold smallValid; decide +kernel

private theorem sp4087 : smallValid 4087 55 := by unfold smallValid; decide +kernel

private theorem sp4142 : smallValid 4142 56 := by unfold smallValid; decide +kernel

private theorem sp4198 : smallValid 4198 55 := by unfold smallValid; decide +kernel

private theorem sp4253 : smallValid 4253 55 := by unfold smallValid; decide +kernel

private theorem sp4308 : smallValid 4308 55 := by unfold smallValid; decide +kernel

private theorem sp4363 : smallValid 4363 56 := by unfold smallValid; decide +kernel

private theorem sp4419 : smallValid 4419 55 := by unfold smallValid; decide +kernel

private theorem sp4474 : smallValid 4474 55 := by unfold smallValid; decide +kernel

private theorem sp4529 : smallValid 4529 55 := by unfold smallValid; decide +kernel

private theorem sp4584 : smallValid 4584 56 := by unfold smallValid; decide +kernel

private theorem sp4640 : smallValid 4640 55 := by unfold smallValid; decide +kernel

private theorem sp4695 : smallValid 4695 55 := by unfold smallValid; decide +kernel

private theorem sp4750 : smallValid 4750 55 := by unfold smallValid; decide +kernel

private theorem sp4805 : smallValid 4805 56 := by unfold smallValid; decide +kernel

private theorem sp4861 : smallValid 4861 55 := by unfold smallValid; decide +kernel

private theorem sp4916 : smallValid 4916 55 := by unfold smallValid; decide +kernel

private theorem sp4971 : smallValid 4971 55 := by unfold smallValid; decide +kernel

private theorem sp5026 : smallValid 5026 56 := by unfold smallValid; decide +kernel

private theorem sp5082 : smallValid 5082 55 := by unfold smallValid; decide +kernel

private theorem sp5137 : smallValid 5137 55 := by unfold smallValid; decide +kernel

private theorem sp5192 : smallValid 5192 55 := by unfold smallValid; decide +kernel

private theorem sp5247 : smallValid 5247 56 := by unfold smallValid; decide +kernel

private theorem sp5303 : smallValid 5303 55 := by unfold smallValid; decide +kernel

private theorem sp5358 : smallValid 5358 55 := by unfold smallValid; decide +kernel

private theorem sp5413 : smallValid 5413 55 := by unfold smallValid; decide +kernel

private theorem sp5468 : smallValid 5468 56 := by unfold smallValid; decide +kernel

private theorem sp5524 : smallValid 5524 55 := by unfold smallValid; decide +kernel

private theorem sp5579 : smallValid 5579 55 := by unfold smallValid; decide +kernel

private theorem sp5634 : smallValid 5634 55 := by unfold smallValid; decide +kernel

private theorem sp5689 : smallValid 5689 56 := by unfold smallValid; decide +kernel

private theorem sp5745 : smallValid 5745 55 := by unfold smallValid; decide +kernel

private theorem sp5800 : smallValid 5800 55 := by unfold smallValid; decide +kernel

private theorem sp5855 : smallValid 5855 55 := by unfold smallValid; decide +kernel

private theorem sp5910 : smallValid 5910 56 := by unfold smallValid; decide +kernel

private theorem sp5966 : smallValid 5966 55 := by unfold smallValid; decide +kernel

private theorem sp6021 : smallValid 6021 55 := by unfold smallValid; decide +kernel

private theorem sp6076 : smallValid 6076 55 := by unfold smallValid; decide +kernel

private theorem sp6131 : smallValid 6131 56 := by unfold smallValid; decide +kernel

private theorem sp6187 : smallValid 6187 55 := by unfold smallValid; decide +kernel

private theorem sp6242 : smallValid 6242 55 := by unfold smallValid; decide +kernel

private theorem sp6297 : smallValid 6297 55 := by unfold smallValid; decide +kernel

private theorem sp6352 : smallValid 6352 56 := by unfold smallValid; decide +kernel

private theorem sp6408 : smallValid 6408 55 := by unfold smallValid; decide +kernel

private theorem sp6463 : smallValid 6463 55 := by unfold smallValid; decide +kernel

private theorem sp6518 : smallValid 6518 55 := by unfold smallValid; decide +kernel

private theorem sp6573 : smallValid 6573 56 := by unfold smallValid; decide +kernel

private theorem sp6629 : smallValid 6629 55 := by unfold smallValid; decide +kernel

private theorem sp6684 : smallValid 6684 55 := by unfold smallValid; decide +kernel

private theorem sp6739 : smallValid 6739 55 := by unfold smallValid; decide +kernel

private theorem sp6794 : smallValid 6794 56 := by unfold smallValid; decide +kernel

private theorem sp6850 : smallValid 6850 55 := by unfold smallValid; decide +kernel

private theorem sp6905 : smallValid 6905 55 := by unfold smallValid; decide +kernel

private theorem sp6960 : smallValid 6960 55 := by unfold smallValid; decide +kernel

private theorem sp7015 : smallValid 7015 56 := by unfold smallValid; decide +kernel

private theorem sp7071 : smallValid 7071 55 := by unfold smallValid; decide +kernel

private theorem sp7126 : smallValid 7126 55 := by unfold smallValid; decide +kernel

private theorem sp7181 : smallValid 7181 55 := by unfold smallValid; decide +kernel

private theorem sp7236 : smallValid 7236 55 := by unfold smallValid; decide +kernel

private theorem sp7291 : smallValid 7291 55 := by unfold smallValid; decide +kernel

private theorem sp7346 : smallValid 7346 55 := by unfold smallValid; decide +kernel

private theorem sp7401 : smallValid 7401 55 := by unfold smallValid; decide +kernel

private theorem sp7456 : smallValid 7456 56 := by unfold smallValid; decide +kernel

private theorem sp7512 : smallValid 7512 55 := by unfold smallValid; decide +kernel

private theorem sp7567 : smallValid 7567 55 := by unfold smallValid; decide +kernel

private theorem sp7622 : smallValid 7622 55 := by unfold smallValid; decide +kernel

private theorem sp7677 : smallValid 7677 56 := by unfold smallValid; decide +kernel

private theorem sp7733 : smallValid 7733 55 := by unfold smallValid; decide +kernel

private theorem sp7788 : smallValid 7788 55 := by unfold smallValid; decide +kernel

private theorem sp7843 : smallValid 7843 55 := by unfold smallValid; decide +kernel

private theorem sp7898 : smallValid 7898 56 := by unfold smallValid; decide +kernel

private theorem sp7954 : smallValid 7954 55 := by unfold smallValid; decide +kernel

private theorem sp8009 : smallValid 8009 55 := by unfold smallValid; decide +kernel

private theorem sp8064 : smallValid 8064 55 := by unfold smallValid; decide +kernel

private theorem sp8119 : smallValid 8119 56 := by unfold smallValid; decide +kernel

private theorem sp8175 : smallValid 8175 55 := by unfold smallValid; decide +kernel

private theorem sp8230 : smallValid 8230 55 := by unfold smallValid; decide +kernel

private theorem sp8285 : smallValid 8285 55 := by unfold smallValid; decide +kernel

private theorem sp8340 : smallValid 8340 56 := by unfold smallValid; decide +kernel

private theorem sp8396 : smallValid 8396 55 := by unfold smallValid; decide +kernel

private theorem sp8451 : smallValid 8451 55 := by unfold smallValid; decide +kernel

private theorem sp8506 : smallValid 8506 55 := by unfold smallValid; decide +kernel

private theorem sp8561 : smallValid 8561 56 := by unfold smallValid; decide +kernel

private theorem sp8617 : smallValid 8617 55 := by unfold smallValid; decide +kernel

private theorem sp8672 : smallValid 8672 55 := by unfold smallValid; decide +kernel

private theorem sp8727 : smallValid 8727 55 := by unfold smallValid; decide +kernel

private theorem sp8782 : smallValid 8782 56 := by unfold smallValid; decide +kernel

private theorem sp8838 : smallValid 8838 55 := by unfold smallValid; decide +kernel

private theorem sp8893 : smallValid 8893 55 := by unfold smallValid; decide +kernel

private theorem sp8948 : smallValid 8948 55 := by unfold smallValid; decide +kernel

private theorem sp9003 : smallValid 9003 56 := by unfold smallValid; decide +kernel

private theorem sp9059 : smallValid 9059 55 := by unfold smallValid; decide +kernel

private theorem sp9114 : smallValid 9114 55 := by unfold smallValid; decide +kernel

private theorem sp9169 : smallValid 9169 55 := by unfold smallValid; decide +kernel

private theorem sp9224 : smallValid 9224 56 := by unfold smallValid; decide +kernel

private theorem sp9280 : smallValid 9280 55 := by unfold smallValid; decide +kernel

private theorem sp9335 : smallValid 9335 55 := by unfold smallValid; decide +kernel

private theorem sp9390 : smallValid 9390 55 := by unfold smallValid; decide +kernel

private theorem sp9445 : smallValid 9445 56 := by unfold smallValid; decide +kernel

private theorem sp9501 : smallValid 9501 55 := by unfold smallValid; decide +kernel

private theorem sp9556 : smallValid 9556 55 := by unfold smallValid; decide +kernel

private theorem sp9611 : smallValid 9611 55 := by unfold smallValid; decide +kernel

private theorem sp9666 : smallValid 9666 56 := by unfold smallValid; decide +kernel

private theorem sp9722 : smallValid 9722 55 := by unfold smallValid; decide +kernel

private theorem sp9777 : smallValid 9777 55 := by unfold smallValid; decide +kernel

private theorem sp9832 : smallValid 9832 55 := by unfold smallValid; decide +kernel

private theorem sp9887 : smallValid 9887 56 := by unfold smallValid; decide +kernel

private theorem sp9943 : smallValid 9943 55 := by unfold smallValid; decide +kernel

private theorem sp9998 : smallValid 9998 55 := by unfold smallValid; decide +kernel

private theorem sp10053 : smallValid 10053 55 := by unfold smallValid; decide +kernel

private theorem sp10108 : smallValid 10108 56 := by unfold smallValid; decide +kernel

private theorem sp10164 : smallValid 10164 55 := by unfold smallValid; decide +kernel

private theorem sp10219 : smallValid 10219 55 := by unfold smallValid; decide +kernel

private theorem sp10274 : smallValid 10274 55 := by unfold smallValid; decide +kernel

private theorem sp10329 : smallValid 10329 56 := by unfold smallValid; decide +kernel

private theorem sp10385 : smallValid 10385 55 := by unfold smallValid; decide +kernel

private theorem sp10440 : smallValid 10440 55 := by unfold smallValid; decide +kernel

private theorem sp10495 : smallValid 10495 55 := by unfold smallValid; decide +kernel

private theorem sp10550 : smallValid 10550 56 := by unfold smallValid; decide +kernel

private theorem sp10606 : smallValid 10606 55 := by unfold smallValid; decide +kernel

private theorem sp10661 : smallValid 10661 55 := by unfold smallValid; decide +kernel

private theorem sp10716 : smallValid 10716 55 := by unfold smallValid; decide +kernel

private theorem sp10771 : smallValid 10771 56 := by unfold smallValid; decide +kernel

private theorem sp10827 : smallValid 10827 55 := by unfold smallValid; decide +kernel

private theorem sp10882 : smallValid 10882 55 := by unfold smallValid; decide +kernel

private theorem sp10937 : smallValid 10937 55 := by unfold smallValid; decide +kernel

private theorem sp10992 : smallValid 10992 56 := by unfold smallValid; decide +kernel

private theorem sp11048 : smallValid 11048 55 := by unfold smallValid; decide +kernel

private theorem sp11103 : smallValid 11103 55 := by unfold smallValid; decide +kernel

private theorem sp11158 : smallValid 11158 55 := by unfold smallValid; decide +kernel

private theorem sp11213 : smallValid 11213 56 := by unfold smallValid; decide +kernel

private theorem sp11269 : smallValid 11269 55 := by unfold smallValid; decide +kernel

private theorem sp11324 : smallValid 11324 55 := by unfold smallValid; decide +kernel

private theorem sp11379 : smallValid 11379 55 := by unfold smallValid; decide +kernel

private theorem sp11434 : smallValid 11434 56 := by unfold smallValid; decide +kernel

private theorem sp11490 : smallValid 11490 55 := by unfold smallValid; decide +kernel

private theorem sp11545 : smallValid 11545 55 := by unfold smallValid; decide +kernel

private theorem sp11600 : smallValid 11600 55 := by unfold smallValid; decide +kernel

private theorem sp11655 : smallValid 11655 56 := by unfold smallValid; decide +kernel

private theorem sp11711 : smallValid 11711 55 := by unfold smallValid; decide +kernel

private theorem sp11766 : smallValid 11766 55 := by unfold smallValid; decide +kernel

private theorem sp11821 : smallValid 11821 55 := by unfold smallValid; decide +kernel

private theorem sp11876 : smallValid 11876 56 := by unfold smallValid; decide +kernel

private theorem sp11932 : smallValid 11932 55 := by unfold smallValid; decide +kernel

private theorem sp11987 : smallValid 11987 55 := by unfold smallValid; decide +kernel

private theorem sp12042 : smallValid 12042 55 := by unfold smallValid; decide +kernel

private theorem sp12097 : smallValid 12097 56 := by unfold smallValid; decide +kernel

private theorem sp12153 : smallValid 12153 55 := by unfold smallValid; decide +kernel

private theorem sp12208 : smallValid 12208 55 := by unfold smallValid; decide +kernel

private theorem sp12263 : smallValid 12263 55 := by unfold smallValid; decide +kernel

private theorem sp12318 : smallValid 12318 56 := by unfold smallValid; decide +kernel

private theorem sp12374 : smallValid 12374 55 := by unfold smallValid; decide +kernel

private theorem sp12429 : smallValid 12429 55 := by unfold smallValid; decide +kernel

private theorem sp12484 : smallValid 12484 55 := by unfold smallValid; decide +kernel

private theorem sp12539 : smallValid 12539 56 := by unfold smallValid; decide +kernel

private theorem sp12595 : smallValid 12595 55 := by unfold smallValid; decide +kernel

private theorem sp12650 : smallValid 12650 55 := by unfold smallValid; decide +kernel

private theorem sp12705 : smallValid 12705 55 := by unfold smallValid; decide +kernel

private theorem sp12760 : smallValid 12760 56 := by unfold smallValid; decide +kernel

private theorem sp12816 : smallValid 12816 55 := by unfold smallValid; decide +kernel

private theorem sp12871 : smallValid 12871 55 := by unfold smallValid; decide +kernel

private theorem sp12926 : smallValid 12926 55 := by unfold smallValid; decide +kernel

private theorem sp12981 : smallValid 12981 56 := by unfold smallValid; decide +kernel

private theorem sp13037 : smallValid 13037 55 := by unfold smallValid; decide +kernel

private theorem sp13092 : smallValid 13092 55 := by unfold smallValid; decide +kernel

private theorem sp13147 : smallValid 13147 55 := by unfold smallValid; decide +kernel

private theorem sp13202 : smallValid 13202 56 := by unfold smallValid; decide +kernel

private theorem sp13258 : smallValid 13258 55 := by unfold smallValid; decide +kernel

private theorem sp13313 : smallValid 13313 55 := by unfold smallValid; decide +kernel

private theorem sp13368 : smallValid 13368 55 := by unfold smallValid; decide +kernel

private theorem sp13423 : smallValid 13423 56 := by unfold smallValid; decide +kernel

private theorem sp13479 : smallValid 13479 55 := by unfold smallValid; decide +kernel

private theorem sp13534 : smallValid 13534 55 := by unfold smallValid; decide +kernel

private theorem sp13589 : smallValid 13589 55 := by unfold smallValid; decide +kernel

private theorem sp13644 : smallValid 13644 56 := by unfold smallValid; decide +kernel

private theorem sp13700 : smallValid 13700 55 := by unfold smallValid; decide +kernel

private theorem sp13755 : smallValid 13755 55 := by unfold smallValid; decide +kernel

private theorem sp13810 : smallValid 13810 55 := by unfold smallValid; decide +kernel

private theorem sp13865 : smallValid 13865 56 := by unfold smallValid; decide +kernel

private theorem sp13921 : smallValid 13921 55 := by unfold smallValid; decide +kernel

private theorem sp13976 : smallValid 13976 55 := by unfold smallValid; decide +kernel

private theorem sp14031 : smallValid 14031 55 := by unfold smallValid; decide +kernel

private theorem sp14086 : smallValid 14086 56 := by unfold smallValid; decide +kernel

private theorem sp14142 : smallValid 14142 55 := by unfold smallValid; decide +kernel

private theorem sp14197 : smallValid 14197 55 := by unfold smallValid; decide +kernel

private theorem sp14252 : smallValid 14252 55 := by unfold smallValid; decide +kernel

private theorem sp14307 : smallValid 14307 55 := by unfold smallValid; decide +kernel

private theorem sp14362 : smallValid 14362 55 := by unfold smallValid; decide +kernel

private theorem sp14417 : smallValid 14417 55 := by unfold smallValid; decide +kernel

private theorem sp14472 : smallValid 14472 55 := by unfold smallValid; decide +kernel

private theorem sp14527 : smallValid 14527 56 := by unfold smallValid; decide +kernel

private theorem sp14583 : smallValid 14583 55 := by unfold smallValid; decide +kernel

private theorem sp14638 : smallValid 14638 55 := by unfold smallValid; decide +kernel

private theorem sp14693 : smallValid 14693 55 := by unfold smallValid; decide +kernel

private theorem sp14748 : smallValid 14748 56 := by unfold smallValid; decide +kernel

private theorem sp14804 : smallValid 14804 55 := by unfold smallValid; decide +kernel

private theorem sp14859 : smallValid 14859 55 := by unfold smallValid; decide +kernel

private theorem sp14914 : smallValid 14914 55 := by unfold smallValid; decide +kernel

private theorem sp14969 : smallValid 14969 56 := by unfold smallValid; decide +kernel

private theorem sp15025 : smallValid 15025 55 := by unfold smallValid; decide +kernel

private theorem sp15080 : smallValid 15080 55 := by unfold smallValid; decide +kernel

private theorem sp15135 : smallValid 15135 55 := by unfold smallValid; decide +kernel

private theorem sp15190 : smallValid 15190 56 := by unfold smallValid; decide +kernel

private theorem sp15246 : smallValid 15246 55 := by unfold smallValid; decide +kernel

private theorem sp15301 : smallValid 15301 55 := by unfold smallValid; decide +kernel

private theorem sp15356 : smallValid 15356 55 := by unfold smallValid; decide +kernel

private theorem sp15411 : smallValid 15411 56 := by unfold smallValid; decide +kernel

private theorem sp15467 : smallValid 15467 55 := by unfold smallValid; decide +kernel

private theorem sp15522 : smallValid 15522 55 := by unfold smallValid; decide +kernel

private theorem sp15577 : smallValid 15577 55 := by unfold smallValid; decide +kernel

private theorem sp15632 : smallValid 15632 56 := by unfold smallValid; decide +kernel

private theorem sp15688 : smallValid 15688 55 := by unfold smallValid; decide +kernel

private theorem sp15743 : smallValid 15743 55 := by unfold smallValid; decide +kernel

private theorem sp15798 : smallValid 15798 55 := by unfold smallValid; decide +kernel

private theorem sp15853 : smallValid 15853 56 := by unfold smallValid; decide +kernel

private theorem sp15909 : smallValid 15909 55 := by unfold smallValid; decide +kernel

private theorem sp15964 : smallValid 15964 55 := by unfold smallValid; decide +kernel

private theorem sp16019 : smallValid 16019 55 := by unfold smallValid; decide +kernel

private theorem sp16074 : smallValid 16074 56 := by unfold smallValid; decide +kernel

private theorem sp16130 : smallValid 16130 55 := by unfold smallValid; decide +kernel

private theorem sp16185 : smallValid 16185 55 := by unfold smallValid; decide +kernel

private theorem sp16240 : smallValid 16240 55 := by unfold smallValid; decide +kernel

private theorem sp16295 : smallValid 16295 56 := by unfold smallValid; decide +kernel

private theorem sp16351 : smallValid 16351 55 := by unfold smallValid; decide +kernel

private theorem sp16406 : smallValid 16406 55 := by unfold smallValid; decide +kernel

private theorem sp16461 : smallValid 16461 55 := by unfold smallValid; decide +kernel

private theorem sp16516 : smallValid 16516 56 := by unfold smallValid; decide +kernel

private theorem sp16572 : smallValid 16572 55 := by unfold smallValid; decide +kernel

private theorem sp16627 : smallValid 16627 55 := by unfold smallValid; decide +kernel

private theorem sp16682 : smallValid 16682 55 := by unfold smallValid; decide +kernel

private theorem sp16737 : smallValid 16737 56 := by unfold smallValid; decide +kernel

private theorem sp16793 : smallValid 16793 55 := by unfold smallValid; decide +kernel

private theorem sp16848 : smallValid 16848 55 := by unfold smallValid; decide +kernel

private theorem sp16903 : smallValid 16903 55 := by unfold smallValid; decide +kernel

private theorem sp16958 : smallValid 16958 56 := by unfold smallValid; decide +kernel

private theorem sp17014 : smallValid 17014 55 := by unfold smallValid; decide +kernel

private theorem sp17069 : smallValid 17069 55 := by unfold smallValid; decide +kernel

private theorem sp17124 : smallValid 17124 55 := by unfold smallValid; decide +kernel

private theorem sp17179 : smallValid 17179 56 := by unfold smallValid; decide +kernel

private theorem sp17235 : smallValid 17235 55 := by unfold smallValid; decide +kernel

private theorem sp17290 : smallValid 17290 55 := by unfold smallValid; decide +kernel

private theorem sp17345 : smallValid 17345 55 := by unfold smallValid; decide +kernel

private theorem sp17400 : smallValid 17400 56 := by unfold smallValid; decide +kernel

private theorem sp17456 : smallValid 17456 55 := by unfold smallValid; decide +kernel

private theorem sp17511 : smallValid 17511 55 := by unfold smallValid; decide +kernel

private theorem sp17566 : smallValid 17566 55 := by unfold smallValid; decide +kernel

private theorem sp17621 : smallValid 17621 56 := by unfold smallValid; decide +kernel

private theorem sp17677 : smallValid 17677 55 := by unfold smallValid; decide +kernel

private theorem sp17732 : smallValid 17732 55 := by unfold smallValid; decide +kernel

private theorem sp17787 : smallValid 17787 55 := by unfold smallValid; decide +kernel

private theorem sp17842 : smallValid 17842 56 := by unfold smallValid; decide +kernel

private theorem sp17898 : smallValid 17898 55 := by unfold smallValid; decide +kernel

private theorem sp17953 : smallValid 17953 55 := by unfold smallValid; decide +kernel

private theorem sp18008 : smallValid 18008 55 := by unfold smallValid; decide +kernel

private theorem sp18063 : smallValid 18063 56 := by unfold smallValid; decide +kernel

private theorem sp18119 : smallValid 18119 55 := by unfold smallValid; decide +kernel

private theorem sp18174 : smallValid 18174 55 := by unfold smallValid; decide +kernel

private theorem sp18229 : smallValid 18229 55 := by unfold smallValid; decide +kernel

private theorem sp18284 : smallValid 18284 56 := by unfold smallValid; decide +kernel

private theorem sp18340 : smallValid 18340 55 := by unfold smallValid; decide +kernel

private theorem sp18395 : smallValid 18395 55 := by unfold smallValid; decide +kernel

private theorem sp18450 : smallValid 18450 55 := by unfold smallValid; decide +kernel

private theorem sp18505 : smallValid 18505 56 := by unfold smallValid; decide +kernel

private theorem sp18561 : smallValid 18561 55 := by unfold smallValid; decide +kernel

private theorem sp18616 : smallValid 18616 55 := by unfold smallValid; decide +kernel

private theorem sp18671 : smallValid 18671 55 := by unfold smallValid; decide +kernel

private theorem sp18726 : smallValid 18726 56 := by unfold smallValid; decide +kernel

private theorem sp18782 : smallValid 18782 55 := by unfold smallValid; decide +kernel

private theorem sp18837 : smallValid 18837 55 := by unfold smallValid; decide +kernel

private theorem sp18892 : smallValid 18892 55 := by unfold smallValid; decide +kernel

private theorem sp18947 : smallValid 18947 56 := by unfold smallValid; decide +kernel

private theorem sp19003 : smallValid 19003 55 := by unfold smallValid; decide +kernel

private theorem sp19058 : smallValid 19058 55 := by unfold smallValid; decide +kernel

private theorem sp19113 : smallValid 19113 55 := by unfold smallValid; decide +kernel

private theorem sp19168 : smallValid 19168 56 := by unfold smallValid; decide +kernel

private theorem sp19224 : smallValid 19224 55 := by unfold smallValid; decide +kernel

private theorem sp19279 : smallValid 19279 55 := by unfold smallValid; decide +kernel

private theorem sp19334 : smallValid 19334 55 := by unfold smallValid; decide +kernel

private theorem sp19389 : smallValid 19389 56 := by unfold smallValid; decide +kernel

private theorem sp19445 : smallValid 19445 55 := by unfold smallValid; decide +kernel

private theorem sp19500 : smallValid 19500 55 := by unfold smallValid; decide +kernel

private theorem sp19555 : smallValid 19555 55 := by unfold smallValid; decide +kernel

private theorem sp19610 : smallValid 19610 56 := by unfold smallValid; decide +kernel

private theorem sp19666 : smallValid 19666 55 := by unfold smallValid; decide +kernel

private theorem sp19721 : smallValid 19721 55 := by unfold smallValid; decide +kernel

private theorem sp19776 : smallValid 19776 55 := by unfold smallValid; decide +kernel

private theorem sp19831 : smallValid 19831 56 := by unfold smallValid; decide +kernel

private theorem sp19887 : smallValid 19887 55 := by unfold smallValid; decide +kernel

private theorem sp19942 : smallValid 19942 55 := by unfold smallValid; decide +kernel

private theorem sp19997 : smallValid 19997 55 := by unfold smallValid; decide +kernel

private theorem sp20052 : smallValid 20052 56 := by unfold smallValid; decide +kernel

private theorem sp20108 : smallValid 20108 55 := by unfold smallValid; decide +kernel

private theorem sp20163 : smallValid 20163 55 := by unfold smallValid; decide +kernel

private theorem sp20218 : smallValid 20218 55 := by unfold smallValid; decide +kernel

private theorem sp20273 : smallValid 20273 56 := by unfold smallValid; decide +kernel

private theorem sp20329 : smallValid 20329 55 := by unfold smallValid; decide +kernel

private theorem sp20384 : smallValid 20384 55 := by unfold smallValid; decide +kernel

private theorem sp20439 : smallValid 20439 55 := by unfold smallValid; decide +kernel

private theorem sp20494 : smallValid 20494 56 := by unfold smallValid; decide +kernel

private theorem sp20550 : smallValid 20550 55 := by unfold smallValid; decide +kernel

private theorem sp20605 : smallValid 20605 55 := by unfold smallValid; decide +kernel

private theorem sp20660 : smallValid 20660 55 := by unfold smallValid; decide +kernel

private theorem sp20715 : smallValid 20715 56 := by unfold smallValid; decide +kernel

private theorem sp20771 : smallValid 20771 55 := by unfold smallValid; decide +kernel

private theorem sp20826 : smallValid 20826 55 := by unfold smallValid; decide +kernel

private theorem sp20881 : smallValid 20881 55 := by unfold smallValid; decide +kernel

private theorem sp20936 : smallValid 20936 56 := by unfold smallValid; decide +kernel

private theorem sp20992 : smallValid 20992 55 := by unfold smallValid; decide +kernel

private theorem sp21047 : smallValid 21047 55 := by unfold smallValid; decide +kernel

private theorem sp21102 : smallValid 21102 55 := by unfold smallValid; decide +kernel

private theorem sp21157 : smallValid 21157 56 := by unfold smallValid; decide +kernel

private theorem sp21213 : smallValid 21213 55 := by unfold smallValid; decide +kernel

private theorem sp21268 : smallValid 21268 55 := by unfold smallValid; decide +kernel

private theorem sp21323 : smallValid 21323 55 := by unfold smallValid; decide +kernel

private theorem sp21378 : smallValid 21378 56 := by unfold smallValid; decide +kernel

private theorem sp21434 : smallValid 21434 55 := by unfold smallValid; decide +kernel

private theorem sp21489 : smallValid 21489 55 := by unfold smallValid; decide +kernel

private theorem sp21544 : smallValid 21544 55 := by unfold smallValid; decide +kernel

private theorem sp21599 : smallValid 21599 56 := by unfold smallValid; decide +kernel

private theorem sp21655 : smallValid 21655 55 := by unfold smallValid; decide +kernel

private theorem sp21710 : smallValid 21710 55 := by unfold smallValid; decide +kernel

private theorem sp21765 : smallValid 21765 55 := by unfold smallValid; decide +kernel

private theorem sp21820 : smallValid 21820 56 := by unfold smallValid; decide +kernel

private theorem sp21876 : smallValid 21876 55 := by unfold smallValid; decide +kernel

private theorem sp21931 : smallValid 21931 55 := by unfold smallValid; decide +kernel

private theorem sp21986 : smallValid 21986 55 := by unfold smallValid; decide +kernel

private theorem sp22041 : smallValid 22041 56 := by unfold smallValid; decide +kernel

private theorem sp22097 : smallValid 22097 55 := by unfold smallValid; decide +kernel

private theorem sp22152 : smallValid 22152 55 := by unfold smallValid; decide +kernel

private theorem sp22207 : smallValid 22207 55 := by unfold smallValid; decide +kernel

private theorem sp22262 : smallValid 22262 56 := by unfold smallValid; decide +kernel

private theorem sp22318 : smallValid 22318 55 := by unfold smallValid; decide +kernel

private theorem sp22373 : smallValid 22373 55 := by unfold smallValid; decide +kernel

private theorem sp22428 : smallValid 22428 55 := by unfold smallValid; decide +kernel

private theorem sp22483 : smallValid 22483 56 := by unfold smallValid; decide +kernel

private theorem sp22539 : smallValid 22539 55 := by unfold smallValid; decide +kernel

private theorem sp22594 : smallValid 22594 55 := by unfold smallValid; decide +kernel

private theorem sp22649 : smallValid 22649 55 := by unfold smallValid; decide +kernel

private theorem sp22704 : smallValid 22704 56 := by unfold smallValid; decide +kernel

private theorem sp22760 : smallValid 22760 55 := by unfold smallValid; decide +kernel

private theorem sp22815 : smallValid 22815 55 := by unfold smallValid; decide +kernel

private theorem sp22870 : smallValid 22870 55 := by unfold smallValid; decide +kernel

private theorem sp22925 : smallValid 22925 56 := by unfold smallValid; decide +kernel

private theorem sp22981 : smallValid 22981 55 := by unfold smallValid; decide +kernel

private theorem sp23036 : smallValid 23036 55 := by unfold smallValid; decide +kernel

private theorem sp23091 : smallValid 23091 55 := by unfold smallValid; decide +kernel

private theorem sp23146 : smallValid 23146 56 := by unfold smallValid; decide +kernel

private theorem sp23202 : smallValid 23202 55 := by unfold smallValid; decide +kernel

private theorem sp23257 : smallValid 23257 55 := by unfold smallValid; decide +kernel

private theorem sp23312 : smallValid 23312 55 := by unfold smallValid; decide +kernel

private theorem sp23367 : smallValid 23367 56 := by unfold smallValid; decide +kernel

private theorem sp23423 : smallValid 23423 55 := by unfold smallValid; decide +kernel

private theorem sp23478 : smallValid 23478 55 := by unfold smallValid; decide +kernel

private theorem sp23533 : smallValid 23533 55 := by unfold smallValid; decide +kernel

private theorem sp23588 : smallValid 23588 56 := by unfold smallValid; decide +kernel

private theorem sp23644 : smallValid 23644 55 := by unfold smallValid; decide +kernel

private theorem sp23699 : smallValid 23699 55 := by unfold smallValid; decide +kernel

private theorem sp23754 : smallValid 23754 55 := by unfold smallValid; decide +kernel

private theorem sp23809 : smallValid 23809 56 := by unfold smallValid; decide +kernel

private theorem sp23865 : smallValid 23865 55 := by unfold smallValid; decide +kernel

private theorem sp23920 : smallValid 23920 55 := by unfold smallValid; decide +kernel

private theorem sp23975 : smallValid 23975 55 := by unfold smallValid; decide +kernel

private theorem sp24030 : smallValid 24030 56 := by unfold smallValid; decide +kernel

private theorem sp24086 : smallValid 24086 55 := by unfold smallValid; decide +kernel

private theorem sp24141 : smallValid 24141 55 := by unfold smallValid; decide +kernel

private theorem sp24196 : smallValid 24196 55 := by unfold smallValid; decide +kernel

private theorem sp24251 : smallValid 24251 56 := by unfold smallValid; decide +kernel

private theorem sp24307 : smallValid 24307 55 := by unfold smallValid; decide +kernel

private theorem sp24362 : smallValid 24362 55 := by unfold smallValid; decide +kernel

private theorem sp24417 : smallValid 24417 55 := by unfold smallValid; decide +kernel

private theorem sp24472 : smallValid 24472 56 := by unfold smallValid; decide +kernel

private theorem sp24528 : smallValid 24528 55 := by unfold smallValid; decide +kernel

private theorem sp24583 : smallValid 24583 55 := by unfold smallValid; decide +kernel

private theorem sp24638 : smallValid 24638 55 := by unfold smallValid; decide +kernel

private theorem sp24693 : smallValid 24693 56 := by unfold smallValid; decide +kernel

private theorem sp24749 : smallValid 24749 55 := by unfold smallValid; decide +kernel

private theorem sp24804 : smallValid 24804 55 := by unfold smallValid; decide +kernel

private theorem sp24859 : smallValid 24859 55 := by unfold smallValid; decide +kernel

private theorem sp24914 : smallValid 24914 56 := by unfold smallValid; decide +kernel

private theorem sp24970 : smallValid 24970 55 := by unfold smallValid; decide +kernel

private theorem sp25025 : smallValid 25025 55 := by unfold smallValid; decide +kernel

private theorem sp25080 : smallValid 25080 55 := by unfold smallValid; decide +kernel

private theorem sp25135 : smallValid 25135 56 := by unfold smallValid; decide +kernel

private theorem sp25191 : smallValid 25191 55 := by unfold smallValid; decide +kernel

private theorem sp25246 : smallValid 25246 55 := by unfold smallValid; decide +kernel

private theorem sp25301 : smallValid 25301 55 := by unfold smallValid; decide +kernel

private theorem sp25356 : smallValid 25356 56 := by unfold smallValid; decide +kernel

private theorem sp25412 : smallValid 25412 55 := by unfold smallValid; decide +kernel

private theorem sp25467 : smallValid 25467 55 := by unfold smallValid; decide +kernel

private theorem sp25522 : smallValid 25522 55 := by unfold smallValid; decide +kernel

private theorem sp25577 : smallValid 25577 56 := by unfold smallValid; decide +kernel

private theorem sp25633 : smallValid 25633 55 := by unfold smallValid; decide +kernel

private theorem sp25688 : smallValid 25688 55 := by unfold smallValid; decide +kernel

private theorem sp25743 : smallValid 25743 55 := by unfold smallValid; decide +kernel

private theorem sp25798 : smallValid 25798 56 := by unfold smallValid; decide +kernel

private theorem sp25854 : smallValid 25854 55 := by unfold smallValid; decide +kernel

private theorem sp25909 : smallValid 25909 55 := by unfold smallValid; decide +kernel

private theorem sp25964 : smallValid 25964 55 := by unfold smallValid; decide +kernel

private theorem sp26019 : smallValid 26019 56 := by unfold smallValid; decide +kernel

private theorem sp26075 : smallValid 26075 55 := by unfold smallValid; decide +kernel

private theorem sp26130 : smallValid 26130 55 := by unfold smallValid; decide +kernel

private theorem sp26185 : smallValid 26185 55 := by unfold smallValid; decide +kernel

private theorem sp26240 : smallValid 26240 56 := by unfold smallValid; decide +kernel

private theorem sp26296 : smallValid 26296 55 := by unfold smallValid; decide +kernel

private theorem sp26351 : smallValid 26351 55 := by unfold smallValid; decide +kernel

private theorem sp26406 : smallValid 26406 55 := by unfold smallValid; decide +kernel

private theorem sp26461 : smallValid 26461 56 := by unfold smallValid; decide +kernel

private theorem sp26517 : smallValid 26517 55 := by unfold smallValid; decide +kernel

private theorem sp26572 : smallValid 26572 55 := by unfold smallValid; decide +kernel

private theorem sp26627 : smallValid 26627 55 := by unfold smallValid; decide +kernel

private theorem sp26682 : smallValid 26682 56 := by unfold smallValid; decide +kernel

private theorem sp26738 : smallValid 26738 55 := by unfold smallValid; decide +kernel

private theorem sp26793 : smallValid 26793 55 := by unfold smallValid; decide +kernel

private theorem sp26848 : smallValid 26848 55 := by unfold smallValid; decide +kernel

private theorem sp26903 : smallValid 26903 56 := by unfold smallValid; decide +kernel

private theorem sp26959 : smallValid 26959 55 := by unfold smallValid; decide +kernel

private theorem sp27014 : smallValid 27014 55 := by unfold smallValid; decide +kernel

private theorem sp27069 : smallValid 27069 55 := by unfold smallValid; decide +kernel

private theorem sp27124 : smallValid 27124 56 := by unfold smallValid; decide +kernel

private theorem sp27180 : smallValid 27180 55 := by unfold smallValid; decide +kernel

private theorem sp27235 : smallValid 27235 55 := by unfold smallValid; decide +kernel

private theorem sp27290 : smallValid 27290 55 := by unfold smallValid; decide +kernel

private theorem sp27345 : smallValid 27345 56 := by unfold smallValid; decide +kernel

private theorem sp27401 : smallValid 27401 55 := by unfold smallValid; decide +kernel

private theorem sp27456 : smallValid 27456 55 := by unfold smallValid; decide +kernel

private theorem sp27511 : smallValid 27511 55 := by unfold smallValid; decide +kernel

private theorem sp27566 : smallValid 27566 56 := by unfold smallValid; decide +kernel

private theorem sp27622 : smallValid 27622 55 := by unfold smallValid; decide +kernel

private theorem sp27677 : smallValid 27677 55 := by unfold smallValid; decide +kernel

private theorem sp27732 : smallValid 27732 55 := by unfold smallValid; decide +kernel

private theorem sp27787 : smallValid 27787 56 := by unfold smallValid; decide +kernel

private theorem sp27843 : smallValid 27843 55 := by unfold smallValid; decide +kernel

private theorem sp27898 : smallValid 27898 55 := by unfold smallValid; decide +kernel

private theorem sp27953 : smallValid 27953 55 := by unfold smallValid; decide +kernel

private theorem sp28008 : smallValid 28008 56 := by unfold smallValid; decide +kernel

private theorem sp28064 : smallValid 28064 55 := by unfold smallValid; decide +kernel

private theorem sp28119 : smallValid 28119 55 := by unfold smallValid; decide +kernel

private theorem sp28174 : smallValid 28174 55 := by unfold smallValid; decide +kernel

private theorem sp28229 : smallValid 28229 56 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤28284) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 28285 := (joinSmall (lo:=0) (a:=14142) (b:=14143) (joinSmall (lo:=0) (a:=7071) (b:=7071) (joinSmall (lo:=0) (a:=3535) (b:=3536) (joinSmall (lo:=0) (a:=1767) (b:=1768) (joinSmall (lo:=0) (a:=883) (b:=884) (joinSmall (lo:=0) (a:=441) (b:=442) (joinSmall (lo:=0) (a:=220) (b:=221) (joinSmall (lo:=0) (a:=110) (b:=110) (joinSmall (lo:=0) (a:=55) (b:=55) sp0 sp55) (joinSmall (lo:=110) (a:=55) (b:=55) sp110 sp165)) (joinSmall (lo:=220) (a:=110) (b:=111) (joinSmall (lo:=220) (a:=55) (b:=55) sp220 sp275) (joinSmall (lo:=330) (a:=55) (b:=56) sp330 sp385))) (joinSmall (lo:=441) (a:=221) (b:=221) (joinSmall (lo:=441) (a:=110) (b:=111) (joinSmall (lo:=441) (a:=55) (b:=55) sp441 sp496) (joinSmall (lo:=551) (a:=55) (b:=56) sp551 sp606)) (joinSmall (lo:=662) (a:=110) (b:=111) (joinSmall (lo:=662) (a:=55) (b:=55) sp662 sp717) (joinSmall (lo:=772) (a:=55) (b:=56) sp772 sp827)))) (joinSmall (lo:=883) (a:=442) (b:=442) (joinSmall (lo:=883) (a:=221) (b:=221) (joinSmall (lo:=883) (a:=110) (b:=111) (joinSmall (lo:=883) (a:=55) (b:=55) sp883 sp938) (joinSmall (lo:=993) (a:=55) (b:=56) sp993 sp1048)) (joinSmall (lo:=1104) (a:=110) (b:=111) (joinSmall (lo:=1104) (a:=55) (b:=55) sp1104 sp1159) (joinSmall (lo:=1214) (a:=55) (b:=56) sp1214 sp1269))) (joinSmall (lo:=1325) (a:=221) (b:=221) (joinSmall (lo:=1325) (a:=110) (b:=111) (joinSmall (lo:=1325) (a:=55) (b:=55) sp1325 sp1380) (joinSmall (lo:=1435) (a:=55) (b:=56) sp1435 sp1490)) (joinSmall (lo:=1546) (a:=110) (b:=111) (joinSmall (lo:=1546) (a:=55) (b:=55) sp1546 sp1601) (joinSmall (lo:=1656) (a:=55) (b:=56) sp1656 sp1711))))) (joinSmall (lo:=1767) (a:=884) (b:=884) (joinSmall (lo:=1767) (a:=442) (b:=442) (joinSmall (lo:=1767) (a:=221) (b:=221) (joinSmall (lo:=1767) (a:=110) (b:=111) (joinSmall (lo:=1767) (a:=55) (b:=55) sp1767 sp1822) (joinSmall (lo:=1877) (a:=55) (b:=56) sp1877 sp1932)) (joinSmall (lo:=1988) (a:=110) (b:=111) (joinSmall (lo:=1988) (a:=55) (b:=55) sp1988 sp2043) (joinSmall (lo:=2098) (a:=55) (b:=56) sp2098 sp2153))) (joinSmall (lo:=2209) (a:=221) (b:=221) (joinSmall (lo:=2209) (a:=110) (b:=111) (joinSmall (lo:=2209) (a:=55) (b:=55) sp2209 sp2264) (joinSmall (lo:=2319) (a:=55) (b:=56) sp2319 sp2374)) (joinSmall (lo:=2430) (a:=110) (b:=111) (joinSmall (lo:=2430) (a:=55) (b:=55) sp2430 sp2485) (joinSmall (lo:=2540) (a:=55) (b:=56) sp2540 sp2595)))) (joinSmall (lo:=2651) (a:=442) (b:=442) (joinSmall (lo:=2651) (a:=221) (b:=221) (joinSmall (lo:=2651) (a:=110) (b:=111) (joinSmall (lo:=2651) (a:=55) (b:=55) sp2651 sp2706) (joinSmall (lo:=2761) (a:=55) (b:=56) sp2761 sp2816)) (joinSmall (lo:=2872) (a:=110) (b:=111) (joinSmall (lo:=2872) (a:=55) (b:=55) sp2872 sp2927) (joinSmall (lo:=2982) (a:=55) (b:=56) sp2982 sp3037))) (joinSmall (lo:=3093) (a:=221) (b:=221) (joinSmall (lo:=3093) (a:=110) (b:=111) (joinSmall (lo:=3093) (a:=55) (b:=55) sp3093 sp3148) (joinSmall (lo:=3203) (a:=55) (b:=56) sp3203 sp3258)) (joinSmall (lo:=3314) (a:=110) (b:=111) (joinSmall (lo:=3314) (a:=55) (b:=55) sp3314 sp3369) (joinSmall (lo:=3424) (a:=55) (b:=56) sp3424 sp3479)))))) (joinSmall (lo:=3535) (a:=1768) (b:=1768) (joinSmall (lo:=3535) (a:=884) (b:=884) (joinSmall (lo:=3535) (a:=442) (b:=442) (joinSmall (lo:=3535) (a:=221) (b:=221) (joinSmall (lo:=3535) (a:=110) (b:=111) (joinSmall (lo:=3535) (a:=55) (b:=55) sp3535 sp3590) (joinSmall (lo:=3645) (a:=55) (b:=56) sp3645 sp3700)) (joinSmall (lo:=3756) (a:=110) (b:=111) (joinSmall (lo:=3756) (a:=55) (b:=55) sp3756 sp3811) (joinSmall (lo:=3866) (a:=55) (b:=56) sp3866 sp3921))) (joinSmall (lo:=3977) (a:=221) (b:=221) (joinSmall (lo:=3977) (a:=110) (b:=111) (joinSmall (lo:=3977) (a:=55) (b:=55) sp3977 sp4032) (joinSmall (lo:=4087) (a:=55) (b:=56) sp4087 sp4142)) (joinSmall (lo:=4198) (a:=110) (b:=111) (joinSmall (lo:=4198) (a:=55) (b:=55) sp4198 sp4253) (joinSmall (lo:=4308) (a:=55) (b:=56) sp4308 sp4363)))) (joinSmall (lo:=4419) (a:=442) (b:=442) (joinSmall (lo:=4419) (a:=221) (b:=221) (joinSmall (lo:=4419) (a:=110) (b:=111) (joinSmall (lo:=4419) (a:=55) (b:=55) sp4419 sp4474) (joinSmall (lo:=4529) (a:=55) (b:=56) sp4529 sp4584)) (joinSmall (lo:=4640) (a:=110) (b:=111) (joinSmall (lo:=4640) (a:=55) (b:=55) sp4640 sp4695) (joinSmall (lo:=4750) (a:=55) (b:=56) sp4750 sp4805))) (joinSmall (lo:=4861) (a:=221) (b:=221) (joinSmall (lo:=4861) (a:=110) (b:=111) (joinSmall (lo:=4861) (a:=55) (b:=55) sp4861 sp4916) (joinSmall (lo:=4971) (a:=55) (b:=56) sp4971 sp5026)) (joinSmall (lo:=5082) (a:=110) (b:=111) (joinSmall (lo:=5082) (a:=55) (b:=55) sp5082 sp5137) (joinSmall (lo:=5192) (a:=55) (b:=56) sp5192 sp5247))))) (joinSmall (lo:=5303) (a:=884) (b:=884) (joinSmall (lo:=5303) (a:=442) (b:=442) (joinSmall (lo:=5303) (a:=221) (b:=221) (joinSmall (lo:=5303) (a:=110) (b:=111) (joinSmall (lo:=5303) (a:=55) (b:=55) sp5303 sp5358) (joinSmall (lo:=5413) (a:=55) (b:=56) sp5413 sp5468)) (joinSmall (lo:=5524) (a:=110) (b:=111) (joinSmall (lo:=5524) (a:=55) (b:=55) sp5524 sp5579) (joinSmall (lo:=5634) (a:=55) (b:=56) sp5634 sp5689))) (joinSmall (lo:=5745) (a:=221) (b:=221) (joinSmall (lo:=5745) (a:=110) (b:=111) (joinSmall (lo:=5745) (a:=55) (b:=55) sp5745 sp5800) (joinSmall (lo:=5855) (a:=55) (b:=56) sp5855 sp5910)) (joinSmall (lo:=5966) (a:=110) (b:=111) (joinSmall (lo:=5966) (a:=55) (b:=55) sp5966 sp6021) (joinSmall (lo:=6076) (a:=55) (b:=56) sp6076 sp6131)))) (joinSmall (lo:=6187) (a:=442) (b:=442) (joinSmall (lo:=6187) (a:=221) (b:=221) (joinSmall (lo:=6187) (a:=110) (b:=111) (joinSmall (lo:=6187) (a:=55) (b:=55) sp6187 sp6242) (joinSmall (lo:=6297) (a:=55) (b:=56) sp6297 sp6352)) (joinSmall (lo:=6408) (a:=110) (b:=111) (joinSmall (lo:=6408) (a:=55) (b:=55) sp6408 sp6463) (joinSmall (lo:=6518) (a:=55) (b:=56) sp6518 sp6573))) (joinSmall (lo:=6629) (a:=221) (b:=221) (joinSmall (lo:=6629) (a:=110) (b:=111) (joinSmall (lo:=6629) (a:=55) (b:=55) sp6629 sp6684) (joinSmall (lo:=6739) (a:=55) (b:=56) sp6739 sp6794)) (joinSmall (lo:=6850) (a:=110) (b:=111) (joinSmall (lo:=6850) (a:=55) (b:=55) sp6850 sp6905) (joinSmall (lo:=6960) (a:=55) (b:=56) sp6960 sp7015))))))) (joinSmall (lo:=7071) (a:=3535) (b:=3536) (joinSmall (lo:=7071) (a:=1767) (b:=1768) (joinSmall (lo:=7071) (a:=883) (b:=884) (joinSmall (lo:=7071) (a:=441) (b:=442) (joinSmall (lo:=7071) (a:=220) (b:=221) (joinSmall (lo:=7071) (a:=110) (b:=110) (joinSmall (lo:=7071) (a:=55) (b:=55) sp7071 sp7126) (joinSmall (lo:=7181) (a:=55) (b:=55) sp7181 sp7236)) (joinSmall (lo:=7291) (a:=110) (b:=111) (joinSmall (lo:=7291) (a:=55) (b:=55) sp7291 sp7346) (joinSmall (lo:=7401) (a:=55) (b:=56) sp7401 sp7456))) (joinSmall (lo:=7512) (a:=221) (b:=221) (joinSmall (lo:=7512) (a:=110) (b:=111) (joinSmall (lo:=7512) (a:=55) (b:=55) sp7512 sp7567) (joinSmall (lo:=7622) (a:=55) (b:=56) sp7622 sp7677)) (joinSmall (lo:=7733) (a:=110) (b:=111) (joinSmall (lo:=7733) (a:=55) (b:=55) sp7733 sp7788) (joinSmall (lo:=7843) (a:=55) (b:=56) sp7843 sp7898)))) (joinSmall (lo:=7954) (a:=442) (b:=442) (joinSmall (lo:=7954) (a:=221) (b:=221) (joinSmall (lo:=7954) (a:=110) (b:=111) (joinSmall (lo:=7954) (a:=55) (b:=55) sp7954 sp8009) (joinSmall (lo:=8064) (a:=55) (b:=56) sp8064 sp8119)) (joinSmall (lo:=8175) (a:=110) (b:=111) (joinSmall (lo:=8175) (a:=55) (b:=55) sp8175 sp8230) (joinSmall (lo:=8285) (a:=55) (b:=56) sp8285 sp8340))) (joinSmall (lo:=8396) (a:=221) (b:=221) (joinSmall (lo:=8396) (a:=110) (b:=111) (joinSmall (lo:=8396) (a:=55) (b:=55) sp8396 sp8451) (joinSmall (lo:=8506) (a:=55) (b:=56) sp8506 sp8561)) (joinSmall (lo:=8617) (a:=110) (b:=111) (joinSmall (lo:=8617) (a:=55) (b:=55) sp8617 sp8672) (joinSmall (lo:=8727) (a:=55) (b:=56) sp8727 sp8782))))) (joinSmall (lo:=8838) (a:=884) (b:=884) (joinSmall (lo:=8838) (a:=442) (b:=442) (joinSmall (lo:=8838) (a:=221) (b:=221) (joinSmall (lo:=8838) (a:=110) (b:=111) (joinSmall (lo:=8838) (a:=55) (b:=55) sp8838 sp8893) (joinSmall (lo:=8948) (a:=55) (b:=56) sp8948 sp9003)) (joinSmall (lo:=9059) (a:=110) (b:=111) (joinSmall (lo:=9059) (a:=55) (b:=55) sp9059 sp9114) (joinSmall (lo:=9169) (a:=55) (b:=56) sp9169 sp9224))) (joinSmall (lo:=9280) (a:=221) (b:=221) (joinSmall (lo:=9280) (a:=110) (b:=111) (joinSmall (lo:=9280) (a:=55) (b:=55) sp9280 sp9335) (joinSmall (lo:=9390) (a:=55) (b:=56) sp9390 sp9445)) (joinSmall (lo:=9501) (a:=110) (b:=111) (joinSmall (lo:=9501) (a:=55) (b:=55) sp9501 sp9556) (joinSmall (lo:=9611) (a:=55) (b:=56) sp9611 sp9666)))) (joinSmall (lo:=9722) (a:=442) (b:=442) (joinSmall (lo:=9722) (a:=221) (b:=221) (joinSmall (lo:=9722) (a:=110) (b:=111) (joinSmall (lo:=9722) (a:=55) (b:=55) sp9722 sp9777) (joinSmall (lo:=9832) (a:=55) (b:=56) sp9832 sp9887)) (joinSmall (lo:=9943) (a:=110) (b:=111) (joinSmall (lo:=9943) (a:=55) (b:=55) sp9943 sp9998) (joinSmall (lo:=10053) (a:=55) (b:=56) sp10053 sp10108))) (joinSmall (lo:=10164) (a:=221) (b:=221) (joinSmall (lo:=10164) (a:=110) (b:=111) (joinSmall (lo:=10164) (a:=55) (b:=55) sp10164 sp10219) (joinSmall (lo:=10274) (a:=55) (b:=56) sp10274 sp10329)) (joinSmall (lo:=10385) (a:=110) (b:=111) (joinSmall (lo:=10385) (a:=55) (b:=55) sp10385 sp10440) (joinSmall (lo:=10495) (a:=55) (b:=56) sp10495 sp10550)))))) (joinSmall (lo:=10606) (a:=1768) (b:=1768) (joinSmall (lo:=10606) (a:=884) (b:=884) (joinSmall (lo:=10606) (a:=442) (b:=442) (joinSmall (lo:=10606) (a:=221) (b:=221) (joinSmall (lo:=10606) (a:=110) (b:=111) (joinSmall (lo:=10606) (a:=55) (b:=55) sp10606 sp10661) (joinSmall (lo:=10716) (a:=55) (b:=56) sp10716 sp10771)) (joinSmall (lo:=10827) (a:=110) (b:=111) (joinSmall (lo:=10827) (a:=55) (b:=55) sp10827 sp10882) (joinSmall (lo:=10937) (a:=55) (b:=56) sp10937 sp10992))) (joinSmall (lo:=11048) (a:=221) (b:=221) (joinSmall (lo:=11048) (a:=110) (b:=111) (joinSmall (lo:=11048) (a:=55) (b:=55) sp11048 sp11103) (joinSmall (lo:=11158) (a:=55) (b:=56) sp11158 sp11213)) (joinSmall (lo:=11269) (a:=110) (b:=111) (joinSmall (lo:=11269) (a:=55) (b:=55) sp11269 sp11324) (joinSmall (lo:=11379) (a:=55) (b:=56) sp11379 sp11434)))) (joinSmall (lo:=11490) (a:=442) (b:=442) (joinSmall (lo:=11490) (a:=221) (b:=221) (joinSmall (lo:=11490) (a:=110) (b:=111) (joinSmall (lo:=11490) (a:=55) (b:=55) sp11490 sp11545) (joinSmall (lo:=11600) (a:=55) (b:=56) sp11600 sp11655)) (joinSmall (lo:=11711) (a:=110) (b:=111) (joinSmall (lo:=11711) (a:=55) (b:=55) sp11711 sp11766) (joinSmall (lo:=11821) (a:=55) (b:=56) sp11821 sp11876))) (joinSmall (lo:=11932) (a:=221) (b:=221) (joinSmall (lo:=11932) (a:=110) (b:=111) (joinSmall (lo:=11932) (a:=55) (b:=55) sp11932 sp11987) (joinSmall (lo:=12042) (a:=55) (b:=56) sp12042 sp12097)) (joinSmall (lo:=12153) (a:=110) (b:=111) (joinSmall (lo:=12153) (a:=55) (b:=55) sp12153 sp12208) (joinSmall (lo:=12263) (a:=55) (b:=56) sp12263 sp12318))))) (joinSmall (lo:=12374) (a:=884) (b:=884) (joinSmall (lo:=12374) (a:=442) (b:=442) (joinSmall (lo:=12374) (a:=221) (b:=221) (joinSmall (lo:=12374) (a:=110) (b:=111) (joinSmall (lo:=12374) (a:=55) (b:=55) sp12374 sp12429) (joinSmall (lo:=12484) (a:=55) (b:=56) sp12484 sp12539)) (joinSmall (lo:=12595) (a:=110) (b:=111) (joinSmall (lo:=12595) (a:=55) (b:=55) sp12595 sp12650) (joinSmall (lo:=12705) (a:=55) (b:=56) sp12705 sp12760))) (joinSmall (lo:=12816) (a:=221) (b:=221) (joinSmall (lo:=12816) (a:=110) (b:=111) (joinSmall (lo:=12816) (a:=55) (b:=55) sp12816 sp12871) (joinSmall (lo:=12926) (a:=55) (b:=56) sp12926 sp12981)) (joinSmall (lo:=13037) (a:=110) (b:=111) (joinSmall (lo:=13037) (a:=55) (b:=55) sp13037 sp13092) (joinSmall (lo:=13147) (a:=55) (b:=56) sp13147 sp13202)))) (joinSmall (lo:=13258) (a:=442) (b:=442) (joinSmall (lo:=13258) (a:=221) (b:=221) (joinSmall (lo:=13258) (a:=110) (b:=111) (joinSmall (lo:=13258) (a:=55) (b:=55) sp13258 sp13313) (joinSmall (lo:=13368) (a:=55) (b:=56) sp13368 sp13423)) (joinSmall (lo:=13479) (a:=110) (b:=111) (joinSmall (lo:=13479) (a:=55) (b:=55) sp13479 sp13534) (joinSmall (lo:=13589) (a:=55) (b:=56) sp13589 sp13644))) (joinSmall (lo:=13700) (a:=221) (b:=221) (joinSmall (lo:=13700) (a:=110) (b:=111) (joinSmall (lo:=13700) (a:=55) (b:=55) sp13700 sp13755) (joinSmall (lo:=13810) (a:=55) (b:=56) sp13810 sp13865)) (joinSmall (lo:=13921) (a:=110) (b:=111) (joinSmall (lo:=13921) (a:=55) (b:=55) sp13921 sp13976) (joinSmall (lo:=14031) (a:=55) (b:=56) sp14031 sp14086)))))))) (joinSmall (lo:=14142) (a:=7071) (b:=7072) (joinSmall (lo:=14142) (a:=3535) (b:=3536) (joinSmall (lo:=14142) (a:=1767) (b:=1768) (joinSmall (lo:=14142) (a:=883) (b:=884) (joinSmall (lo:=14142) (a:=441) (b:=442) (joinSmall (lo:=14142) (a:=220) (b:=221) (joinSmall (lo:=14142) (a:=110) (b:=110) (joinSmall (lo:=14142) (a:=55) (b:=55) sp14142 sp14197) (joinSmall (lo:=14252) (a:=55) (b:=55) sp14252 sp14307)) (joinSmall (lo:=14362) (a:=110) (b:=111) (joinSmall (lo:=14362) (a:=55) (b:=55) sp14362 sp14417) (joinSmall (lo:=14472) (a:=55) (b:=56) sp14472 sp14527))) (joinSmall (lo:=14583) (a:=221) (b:=221) (joinSmall (lo:=14583) (a:=110) (b:=111) (joinSmall (lo:=14583) (a:=55) (b:=55) sp14583 sp14638) (joinSmall (lo:=14693) (a:=55) (b:=56) sp14693 sp14748)) (joinSmall (lo:=14804) (a:=110) (b:=111) (joinSmall (lo:=14804) (a:=55) (b:=55) sp14804 sp14859) (joinSmall (lo:=14914) (a:=55) (b:=56) sp14914 sp14969)))) (joinSmall (lo:=15025) (a:=442) (b:=442) (joinSmall (lo:=15025) (a:=221) (b:=221) (joinSmall (lo:=15025) (a:=110) (b:=111) (joinSmall (lo:=15025) (a:=55) (b:=55) sp15025 sp15080) (joinSmall (lo:=15135) (a:=55) (b:=56) sp15135 sp15190)) (joinSmall (lo:=15246) (a:=110) (b:=111) (joinSmall (lo:=15246) (a:=55) (b:=55) sp15246 sp15301) (joinSmall (lo:=15356) (a:=55) (b:=56) sp15356 sp15411))) (joinSmall (lo:=15467) (a:=221) (b:=221) (joinSmall (lo:=15467) (a:=110) (b:=111) (joinSmall (lo:=15467) (a:=55) (b:=55) sp15467 sp15522) (joinSmall (lo:=15577) (a:=55) (b:=56) sp15577 sp15632)) (joinSmall (lo:=15688) (a:=110) (b:=111) (joinSmall (lo:=15688) (a:=55) (b:=55) sp15688 sp15743) (joinSmall (lo:=15798) (a:=55) (b:=56) sp15798 sp15853))))) (joinSmall (lo:=15909) (a:=884) (b:=884) (joinSmall (lo:=15909) (a:=442) (b:=442) (joinSmall (lo:=15909) (a:=221) (b:=221) (joinSmall (lo:=15909) (a:=110) (b:=111) (joinSmall (lo:=15909) (a:=55) (b:=55) sp15909 sp15964) (joinSmall (lo:=16019) (a:=55) (b:=56) sp16019 sp16074)) (joinSmall (lo:=16130) (a:=110) (b:=111) (joinSmall (lo:=16130) (a:=55) (b:=55) sp16130 sp16185) (joinSmall (lo:=16240) (a:=55) (b:=56) sp16240 sp16295))) (joinSmall (lo:=16351) (a:=221) (b:=221) (joinSmall (lo:=16351) (a:=110) (b:=111) (joinSmall (lo:=16351) (a:=55) (b:=55) sp16351 sp16406) (joinSmall (lo:=16461) (a:=55) (b:=56) sp16461 sp16516)) (joinSmall (lo:=16572) (a:=110) (b:=111) (joinSmall (lo:=16572) (a:=55) (b:=55) sp16572 sp16627) (joinSmall (lo:=16682) (a:=55) (b:=56) sp16682 sp16737)))) (joinSmall (lo:=16793) (a:=442) (b:=442) (joinSmall (lo:=16793) (a:=221) (b:=221) (joinSmall (lo:=16793) (a:=110) (b:=111) (joinSmall (lo:=16793) (a:=55) (b:=55) sp16793 sp16848) (joinSmall (lo:=16903) (a:=55) (b:=56) sp16903 sp16958)) (joinSmall (lo:=17014) (a:=110) (b:=111) (joinSmall (lo:=17014) (a:=55) (b:=55) sp17014 sp17069) (joinSmall (lo:=17124) (a:=55) (b:=56) sp17124 sp17179))) (joinSmall (lo:=17235) (a:=221) (b:=221) (joinSmall (lo:=17235) (a:=110) (b:=111) (joinSmall (lo:=17235) (a:=55) (b:=55) sp17235 sp17290) (joinSmall (lo:=17345) (a:=55) (b:=56) sp17345 sp17400)) (joinSmall (lo:=17456) (a:=110) (b:=111) (joinSmall (lo:=17456) (a:=55) (b:=55) sp17456 sp17511) (joinSmall (lo:=17566) (a:=55) (b:=56) sp17566 sp17621)))))) (joinSmall (lo:=17677) (a:=1768) (b:=1768) (joinSmall (lo:=17677) (a:=884) (b:=884) (joinSmall (lo:=17677) (a:=442) (b:=442) (joinSmall (lo:=17677) (a:=221) (b:=221) (joinSmall (lo:=17677) (a:=110) (b:=111) (joinSmall (lo:=17677) (a:=55) (b:=55) sp17677 sp17732) (joinSmall (lo:=17787) (a:=55) (b:=56) sp17787 sp17842)) (joinSmall (lo:=17898) (a:=110) (b:=111) (joinSmall (lo:=17898) (a:=55) (b:=55) sp17898 sp17953) (joinSmall (lo:=18008) (a:=55) (b:=56) sp18008 sp18063))) (joinSmall (lo:=18119) (a:=221) (b:=221) (joinSmall (lo:=18119) (a:=110) (b:=111) (joinSmall (lo:=18119) (a:=55) (b:=55) sp18119 sp18174) (joinSmall (lo:=18229) (a:=55) (b:=56) sp18229 sp18284)) (joinSmall (lo:=18340) (a:=110) (b:=111) (joinSmall (lo:=18340) (a:=55) (b:=55) sp18340 sp18395) (joinSmall (lo:=18450) (a:=55) (b:=56) sp18450 sp18505)))) (joinSmall (lo:=18561) (a:=442) (b:=442) (joinSmall (lo:=18561) (a:=221) (b:=221) (joinSmall (lo:=18561) (a:=110) (b:=111) (joinSmall (lo:=18561) (a:=55) (b:=55) sp18561 sp18616) (joinSmall (lo:=18671) (a:=55) (b:=56) sp18671 sp18726)) (joinSmall (lo:=18782) (a:=110) (b:=111) (joinSmall (lo:=18782) (a:=55) (b:=55) sp18782 sp18837) (joinSmall (lo:=18892) (a:=55) (b:=56) sp18892 sp18947))) (joinSmall (lo:=19003) (a:=221) (b:=221) (joinSmall (lo:=19003) (a:=110) (b:=111) (joinSmall (lo:=19003) (a:=55) (b:=55) sp19003 sp19058) (joinSmall (lo:=19113) (a:=55) (b:=56) sp19113 sp19168)) (joinSmall (lo:=19224) (a:=110) (b:=111) (joinSmall (lo:=19224) (a:=55) (b:=55) sp19224 sp19279) (joinSmall (lo:=19334) (a:=55) (b:=56) sp19334 sp19389))))) (joinSmall (lo:=19445) (a:=884) (b:=884) (joinSmall (lo:=19445) (a:=442) (b:=442) (joinSmall (lo:=19445) (a:=221) (b:=221) (joinSmall (lo:=19445) (a:=110) (b:=111) (joinSmall (lo:=19445) (a:=55) (b:=55) sp19445 sp19500) (joinSmall (lo:=19555) (a:=55) (b:=56) sp19555 sp19610)) (joinSmall (lo:=19666) (a:=110) (b:=111) (joinSmall (lo:=19666) (a:=55) (b:=55) sp19666 sp19721) (joinSmall (lo:=19776) (a:=55) (b:=56) sp19776 sp19831))) (joinSmall (lo:=19887) (a:=221) (b:=221) (joinSmall (lo:=19887) (a:=110) (b:=111) (joinSmall (lo:=19887) (a:=55) (b:=55) sp19887 sp19942) (joinSmall (lo:=19997) (a:=55) (b:=56) sp19997 sp20052)) (joinSmall (lo:=20108) (a:=110) (b:=111) (joinSmall (lo:=20108) (a:=55) (b:=55) sp20108 sp20163) (joinSmall (lo:=20218) (a:=55) (b:=56) sp20218 sp20273)))) (joinSmall (lo:=20329) (a:=442) (b:=442) (joinSmall (lo:=20329) (a:=221) (b:=221) (joinSmall (lo:=20329) (a:=110) (b:=111) (joinSmall (lo:=20329) (a:=55) (b:=55) sp20329 sp20384) (joinSmall (lo:=20439) (a:=55) (b:=56) sp20439 sp20494)) (joinSmall (lo:=20550) (a:=110) (b:=111) (joinSmall (lo:=20550) (a:=55) (b:=55) sp20550 sp20605) (joinSmall (lo:=20660) (a:=55) (b:=56) sp20660 sp20715))) (joinSmall (lo:=20771) (a:=221) (b:=221) (joinSmall (lo:=20771) (a:=110) (b:=111) (joinSmall (lo:=20771) (a:=55) (b:=55) sp20771 sp20826) (joinSmall (lo:=20881) (a:=55) (b:=56) sp20881 sp20936)) (joinSmall (lo:=20992) (a:=110) (b:=111) (joinSmall (lo:=20992) (a:=55) (b:=55) sp20992 sp21047) (joinSmall (lo:=21102) (a:=55) (b:=56) sp21102 sp21157))))))) (joinSmall (lo:=21213) (a:=3536) (b:=3536) (joinSmall (lo:=21213) (a:=1768) (b:=1768) (joinSmall (lo:=21213) (a:=884) (b:=884) (joinSmall (lo:=21213) (a:=442) (b:=442) (joinSmall (lo:=21213) (a:=221) (b:=221) (joinSmall (lo:=21213) (a:=110) (b:=111) (joinSmall (lo:=21213) (a:=55) (b:=55) sp21213 sp21268) (joinSmall (lo:=21323) (a:=55) (b:=56) sp21323 sp21378)) (joinSmall (lo:=21434) (a:=110) (b:=111) (joinSmall (lo:=21434) (a:=55) (b:=55) sp21434 sp21489) (joinSmall (lo:=21544) (a:=55) (b:=56) sp21544 sp21599))) (joinSmall (lo:=21655) (a:=221) (b:=221) (joinSmall (lo:=21655) (a:=110) (b:=111) (joinSmall (lo:=21655) (a:=55) (b:=55) sp21655 sp21710) (joinSmall (lo:=21765) (a:=55) (b:=56) sp21765 sp21820)) (joinSmall (lo:=21876) (a:=110) (b:=111) (joinSmall (lo:=21876) (a:=55) (b:=55) sp21876 sp21931) (joinSmall (lo:=21986) (a:=55) (b:=56) sp21986 sp22041)))) (joinSmall (lo:=22097) (a:=442) (b:=442) (joinSmall (lo:=22097) (a:=221) (b:=221) (joinSmall (lo:=22097) (a:=110) (b:=111) (joinSmall (lo:=22097) (a:=55) (b:=55) sp22097 sp22152) (joinSmall (lo:=22207) (a:=55) (b:=56) sp22207 sp22262)) (joinSmall (lo:=22318) (a:=110) (b:=111) (joinSmall (lo:=22318) (a:=55) (b:=55) sp22318 sp22373) (joinSmall (lo:=22428) (a:=55) (b:=56) sp22428 sp22483))) (joinSmall (lo:=22539) (a:=221) (b:=221) (joinSmall (lo:=22539) (a:=110) (b:=111) (joinSmall (lo:=22539) (a:=55) (b:=55) sp22539 sp22594) (joinSmall (lo:=22649) (a:=55) (b:=56) sp22649 sp22704)) (joinSmall (lo:=22760) (a:=110) (b:=111) (joinSmall (lo:=22760) (a:=55) (b:=55) sp22760 sp22815) (joinSmall (lo:=22870) (a:=55) (b:=56) sp22870 sp22925))))) (joinSmall (lo:=22981) (a:=884) (b:=884) (joinSmall (lo:=22981) (a:=442) (b:=442) (joinSmall (lo:=22981) (a:=221) (b:=221) (joinSmall (lo:=22981) (a:=110) (b:=111) (joinSmall (lo:=22981) (a:=55) (b:=55) sp22981 sp23036) (joinSmall (lo:=23091) (a:=55) (b:=56) sp23091 sp23146)) (joinSmall (lo:=23202) (a:=110) (b:=111) (joinSmall (lo:=23202) (a:=55) (b:=55) sp23202 sp23257) (joinSmall (lo:=23312) (a:=55) (b:=56) sp23312 sp23367))) (joinSmall (lo:=23423) (a:=221) (b:=221) (joinSmall (lo:=23423) (a:=110) (b:=111) (joinSmall (lo:=23423) (a:=55) (b:=55) sp23423 sp23478) (joinSmall (lo:=23533) (a:=55) (b:=56) sp23533 sp23588)) (joinSmall (lo:=23644) (a:=110) (b:=111) (joinSmall (lo:=23644) (a:=55) (b:=55) sp23644 sp23699) (joinSmall (lo:=23754) (a:=55) (b:=56) sp23754 sp23809)))) (joinSmall (lo:=23865) (a:=442) (b:=442) (joinSmall (lo:=23865) (a:=221) (b:=221) (joinSmall (lo:=23865) (a:=110) (b:=111) (joinSmall (lo:=23865) (a:=55) (b:=55) sp23865 sp23920) (joinSmall (lo:=23975) (a:=55) (b:=56) sp23975 sp24030)) (joinSmall (lo:=24086) (a:=110) (b:=111) (joinSmall (lo:=24086) (a:=55) (b:=55) sp24086 sp24141) (joinSmall (lo:=24196) (a:=55) (b:=56) sp24196 sp24251))) (joinSmall (lo:=24307) (a:=221) (b:=221) (joinSmall (lo:=24307) (a:=110) (b:=111) (joinSmall (lo:=24307) (a:=55) (b:=55) sp24307 sp24362) (joinSmall (lo:=24417) (a:=55) (b:=56) sp24417 sp24472)) (joinSmall (lo:=24528) (a:=110) (b:=111) (joinSmall (lo:=24528) (a:=55) (b:=55) sp24528 sp24583) (joinSmall (lo:=24638) (a:=55) (b:=56) sp24638 sp24693)))))) (joinSmall (lo:=24749) (a:=1768) (b:=1768) (joinSmall (lo:=24749) (a:=884) (b:=884) (joinSmall (lo:=24749) (a:=442) (b:=442) (joinSmall (lo:=24749) (a:=221) (b:=221) (joinSmall (lo:=24749) (a:=110) (b:=111) (joinSmall (lo:=24749) (a:=55) (b:=55) sp24749 sp24804) (joinSmall (lo:=24859) (a:=55) (b:=56) sp24859 sp24914)) (joinSmall (lo:=24970) (a:=110) (b:=111) (joinSmall (lo:=24970) (a:=55) (b:=55) sp24970 sp25025) (joinSmall (lo:=25080) (a:=55) (b:=56) sp25080 sp25135))) (joinSmall (lo:=25191) (a:=221) (b:=221) (joinSmall (lo:=25191) (a:=110) (b:=111) (joinSmall (lo:=25191) (a:=55) (b:=55) sp25191 sp25246) (joinSmall (lo:=25301) (a:=55) (b:=56) sp25301 sp25356)) (joinSmall (lo:=25412) (a:=110) (b:=111) (joinSmall (lo:=25412) (a:=55) (b:=55) sp25412 sp25467) (joinSmall (lo:=25522) (a:=55) (b:=56) sp25522 sp25577)))) (joinSmall (lo:=25633) (a:=442) (b:=442) (joinSmall (lo:=25633) (a:=221) (b:=221) (joinSmall (lo:=25633) (a:=110) (b:=111) (joinSmall (lo:=25633) (a:=55) (b:=55) sp25633 sp25688) (joinSmall (lo:=25743) (a:=55) (b:=56) sp25743 sp25798)) (joinSmall (lo:=25854) (a:=110) (b:=111) (joinSmall (lo:=25854) (a:=55) (b:=55) sp25854 sp25909) (joinSmall (lo:=25964) (a:=55) (b:=56) sp25964 sp26019))) (joinSmall (lo:=26075) (a:=221) (b:=221) (joinSmall (lo:=26075) (a:=110) (b:=111) (joinSmall (lo:=26075) (a:=55) (b:=55) sp26075 sp26130) (joinSmall (lo:=26185) (a:=55) (b:=56) sp26185 sp26240)) (joinSmall (lo:=26296) (a:=110) (b:=111) (joinSmall (lo:=26296) (a:=55) (b:=55) sp26296 sp26351) (joinSmall (lo:=26406) (a:=55) (b:=56) sp26406 sp26461))))) (joinSmall (lo:=26517) (a:=884) (b:=884) (joinSmall (lo:=26517) (a:=442) (b:=442) (joinSmall (lo:=26517) (a:=221) (b:=221) (joinSmall (lo:=26517) (a:=110) (b:=111) (joinSmall (lo:=26517) (a:=55) (b:=55) sp26517 sp26572) (joinSmall (lo:=26627) (a:=55) (b:=56) sp26627 sp26682)) (joinSmall (lo:=26738) (a:=110) (b:=111) (joinSmall (lo:=26738) (a:=55) (b:=55) sp26738 sp26793) (joinSmall (lo:=26848) (a:=55) (b:=56) sp26848 sp26903))) (joinSmall (lo:=26959) (a:=221) (b:=221) (joinSmall (lo:=26959) (a:=110) (b:=111) (joinSmall (lo:=26959) (a:=55) (b:=55) sp26959 sp27014) (joinSmall (lo:=27069) (a:=55) (b:=56) sp27069 sp27124)) (joinSmall (lo:=27180) (a:=110) (b:=111) (joinSmall (lo:=27180) (a:=55) (b:=55) sp27180 sp27235) (joinSmall (lo:=27290) (a:=55) (b:=56) sp27290 sp27345)))) (joinSmall (lo:=27401) (a:=442) (b:=442) (joinSmall (lo:=27401) (a:=221) (b:=221) (joinSmall (lo:=27401) (a:=110) (b:=111) (joinSmall (lo:=27401) (a:=55) (b:=55) sp27401 sp27456) (joinSmall (lo:=27511) (a:=55) (b:=56) sp27511 sp27566)) (joinSmall (lo:=27622) (a:=110) (b:=111) (joinSmall (lo:=27622) (a:=55) (b:=55) sp27622 sp27677) (joinSmall (lo:=27732) (a:=55) (b:=56) sp27732 sp27787))) (joinSmall (lo:=27843) (a:=221) (b:=221) (joinSmall (lo:=27843) (a:=110) (b:=111) (joinSmall (lo:=27843) (a:=55) (b:=55) sp27843 sp27898) (joinSmall (lo:=27953) (a:=55) (b:=56) sp27953 sp28008)) (joinSmall (lo:=28064) (a:=110) (b:=111) (joinSmall (lo:=28064) (a:=55) (b:=55) sp28064 sp28119) (joinSmall (lo:=28174) (a:=55) (b:=56) sp28174 sp28229)))))))))
  have good : (List.range 28285).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 800000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 28284 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 28284 := by
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


private def packet (i : ℕ) : ℕ := (if i < 203 then (if i < 101 then (if i < 50 then (if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 4 then 0 else (if i < 5 then 0 else 0))) else (if i < 9 then (if i < 7 then 0 else (if i < 8 then 0 else 0)) else (if i < 10 then 0 else (if i < 11 then 0 else 0)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0 else (if i < 14 then 0 else 0)) else (if i < 16 then 0 else (if i < 17 then 0 else 0))) else (if i < 21 then (if i < 19 then 0 else (if i < 20 then 0 else 0)) else (if i < 23 then (if i < 22 then 0 else 0) else (if i < 24 then 0 else 0))))) else (if i < 37 then (if i < 31 then (if i < 28 then (if i < 26 then 0 else (if i < 27 then 0 else 0)) else (if i < 29 then 0 else (if i < 30 then 0 else 0))) else (if i < 34 then (if i < 32 then 0 else (if i < 33 then 0 else 0)) else (if i < 35 then 0 else (if i < 36 then 0 else 0)))) else (if i < 43 then (if i < 40 then (if i < 38 then 0 else (if i < 39 then 0 else 0)) else (if i < 41 then 0 else (if i < 42 then 0 else 0))) else (if i < 46 then (if i < 44 then 0 else (if i < 45 then 0 else 0)) else (if i < 48 then (if i < 47 then 0 else 0) else (if i < 49 then 0 else 0)))))) else (if i < 75 then (if i < 62 then (if i < 56 then (if i < 53 then (if i < 51 then 0 else (if i < 52 then 0 else 0)) else (if i < 54 then 0 else (if i < 55 then 0 else 0))) else (if i < 59 then (if i < 57 then 0 else (if i < 58 then 0 else 0)) else (if i < 60 then 0 else (if i < 61 then 0 else 0)))) else (if i < 68 then (if i < 65 then (if i < 63 then 0 else (if i < 64 then 0 else 0)) else (if i < 66 then 0 else (if i < 67 then 0 else 0))) else (if i < 71 then (if i < 69 then 0 else (if i < 70 then 0 else 0)) else (if i < 73 then (if i < 72 then 0 else 0) else (if i < 74 then 0 else 0))))) else (if i < 88 then (if i < 81 then (if i < 78 then (if i < 76 then 0 else (if i < 77 then 0 else 0)) else (if i < 79 then 0 else (if i < 80 then 0 else 0))) else (if i < 84 then (if i < 82 then 0 else (if i < 83 then 0 else 0)) else (if i < 86 then (if i < 85 then 0 else 0) else (if i < 87 then 0 else 0)))) else (if i < 94 then (if i < 91 then (if i < 89 then 0 else (if i < 90 then 0 else 0)) else (if i < 92 then 0 else (if i < 93 then 0 else 0))) else (if i < 97 then (if i < 95 then 0 else (if i < 96 then 0 else 0)) else (if i < 99 then (if i < 98 then 0 else 0) else (if i < 100 then 0 else 0))))))) else (if i < 152 then (if i < 126 then (if i < 113 then (if i < 107 then (if i < 104 then (if i < 102 then 0 else (if i < 103 then 0 else 0)) else (if i < 105 then 0 else (if i < 106 then 0 else 0))) else (if i < 110 then (if i < 108 then 0 else (if i < 109 then 0 else 0)) else (if i < 111 then 0 else (if i < 112 then 0 else 0)))) else (if i < 119 then (if i < 116 then (if i < 114 then 0 else (if i < 115 then 0 else 0)) else (if i < 117 then 0 else (if i < 118 then 0 else 0))) else (if i < 122 then (if i < 120 then 0 else (if i < 121 then 0 else 0)) else (if i < 124 then (if i < 123 then 0 else 0) else (if i < 125 then 0 else 0))))) else (if i < 139 then (if i < 132 then (if i < 129 then (if i < 127 then 0 else (if i < 128 then 0 else 0)) else (if i < 130 then 0 else (if i < 131 then 0 else 0))) else (if i < 135 then (if i < 133 then 0 else (if i < 134 then 0 else 0)) else (if i < 137 then (if i < 136 then 0 else 0) else (if i < 138 then 0 else 0)))) else (if i < 145 then (if i < 142 then (if i < 140 then 0 else (if i < 141 then 0 else 0)) else (if i < 143 then 0 else (if i < 144 then 0 else 0))) else (if i < 148 then (if i < 146 then 0 else (if i < 147 then 0 else 0)) else (if i < 150 then (if i < 149 then 0 else 0) else (if i < 151 then 0 else 0)))))) else (if i < 177 then (if i < 164 then (if i < 158 then (if i < 155 then (if i < 153 then 0 else (if i < 154 then 0 else 0)) else (if i < 156 then 0 else (if i < 157 then 0 else 0))) else (if i < 161 then (if i < 159 then 0 else (if i < 160 then 0 else 0)) else (if i < 162 then 0 else (if i < 163 then 0 else 0)))) else (if i < 170 then (if i < 167 then (if i < 165 then 0 else (if i < 166 then 0 else 0)) else (if i < 168 then 0 else (if i < 169 then 0 else 0))) else (if i < 173 then (if i < 171 then 0 else (if i < 172 then 0 else 0)) else (if i < 175 then (if i < 174 then 0 else 0) else (if i < 176 then 0 else 0))))) else (if i < 190 then (if i < 183 then (if i < 180 then (if i < 178 then 0 else (if i < 179 then 0 else 0)) else (if i < 181 then 0 else (if i < 182 then 0 else 0))) else (if i < 186 then (if i < 184 then 0 else (if i < 185 then 0 else 0)) else (if i < 188 then (if i < 187 then 0 else 0) else (if i < 189 then 0 else 0)))) else (if i < 196 then (if i < 193 then (if i < 191 then 0 else (if i < 192 then 0 else 0)) else (if i < 194 then 0 else (if i < 195 then 0 else 0))) else (if i < 199 then (if i < 197 then 0 else (if i < 198 then 0 else 0)) else (if i < 201 then (if i < 200 then 0 else 0) else (if i < 202 then 0 else 0)))))))) else (if i < 305 then (if i < 254 then (if i < 228 then (if i < 215 then (if i < 209 then (if i < 206 then (if i < 204 then 0 else (if i < 205 then 0 else 0)) else (if i < 207 then 0 else (if i < 208 then 0 else 0))) else (if i < 212 then (if i < 210 then 0 else (if i < 211 then 0 else 0)) else (if i < 213 then 0 else (if i < 214 then 0 else 0)))) else (if i < 221 then (if i < 218 then (if i < 216 then 0 else (if i < 217 then 0 else 0)) else (if i < 219 then 0 else (if i < 220 then 0 else 0))) else (if i < 224 then (if i < 222 then 0 else (if i < 223 then 0 else 0)) else (if i < 226 then (if i < 225 then 0 else 0) else (if i < 227 then 0 else 0))))) else (if i < 241 then (if i < 234 then (if i < 231 then (if i < 229 then 0 else (if i < 230 then 0 else 0)) else (if i < 232 then 0 else (if i < 233 then 0 else 0))) else (if i < 237 then (if i < 235 then 0 else (if i < 236 then 0 else 0)) else (if i < 239 then (if i < 238 then 0 else 0) else (if i < 240 then 0 else 0)))) else (if i < 247 then (if i < 244 then (if i < 242 then 0 else (if i < 243 then 0 else 0)) else (if i < 245 then 0 else (if i < 246 then 0 else 0))) else (if i < 250 then (if i < 248 then 0 else (if i < 249 then 0 else 0)) else (if i < 252 then (if i < 251 then 0 else 0) else (if i < 253 then 0 else 0)))))) else (if i < 279 then (if i < 266 then (if i < 260 then (if i < 257 then (if i < 255 then 0 else (if i < 256 then 0 else 0)) else (if i < 258 then 0 else (if i < 259 then 0 else 0))) else (if i < 263 then (if i < 261 then 0 else (if i < 262 then 0 else 0)) else (if i < 264 then 0 else (if i < 265 then 0 else 0)))) else (if i < 272 then (if i < 269 then (if i < 267 then 0 else (if i < 268 then 0 else 0)) else (if i < 270 then 0 else (if i < 271 then 0 else 0))) else (if i < 275 then (if i < 273 then 0 else (if i < 274 then 0 else 0)) else (if i < 277 then (if i < 276 then 0 else 0) else (if i < 278 then 0 else 0))))) else (if i < 292 then (if i < 285 then (if i < 282 then (if i < 280 then 0 else (if i < 281 then 0 else 0)) else (if i < 283 then 0 else (if i < 284 then 0 else 0))) else (if i < 288 then (if i < 286 then 0 else (if i < 287 then 0 else 0)) else (if i < 290 then (if i < 289 then 0 else 0) else (if i < 291 then 0 else 0)))) else (if i < 298 then (if i < 295 then (if i < 293 then 0 else (if i < 294 then 0 else 0)) else (if i < 296 then 0 else (if i < 297 then 0 else 0))) else (if i < 301 then (if i < 299 then 0 else (if i < 300 then 0 else 0)) else (if i < 303 then (if i < 302 then 0 else 0) else (if i < 304 then 0 else 0))))))) else (if i < 356 then (if i < 330 then (if i < 317 then (if i < 311 then (if i < 308 then (if i < 306 then 0 else (if i < 307 then 0 else 0)) else (if i < 309 then 0 else (if i < 310 then 0 else 0))) else (if i < 314 then (if i < 312 then 0 else (if i < 313 then 0 else 0)) else (if i < 315 then 0 else (if i < 316 then 0 else 0)))) else (if i < 323 then (if i < 320 then (if i < 318 then 0 else (if i < 319 then 0 else 0)) else (if i < 321 then 0 else (if i < 322 then 0 else 0))) else (if i < 326 then (if i < 324 then 0 else (if i < 325 then 0 else 0)) else (if i < 328 then (if i < 327 then 0 else 0) else (if i < 329 then 0 else 0))))) else (if i < 343 then (if i < 336 then (if i < 333 then (if i < 331 then 0 else (if i < 332 then 0 else 0)) else (if i < 334 then 0 else (if i < 335 then 0 else 0))) else (if i < 339 then (if i < 337 then 0 else (if i < 338 then 0 else 0)) else (if i < 341 then (if i < 340 then 0 else 0) else (if i < 342 then 0 else 0)))) else (if i < 349 then (if i < 346 then (if i < 344 then 0 else (if i < 345 then 0 else 0)) else (if i < 347 then 0 else (if i < 348 then 0 else 0))) else (if i < 352 then (if i < 350 then 0 else (if i < 351 then 0 else 0)) else (if i < 354 then (if i < 353 then 0 else 0) else (if i < 355 then 0 else 0)))))) else (if i < 381 then (if i < 368 then (if i < 362 then (if i < 359 then (if i < 357 then 0 else (if i < 358 then 0 else 0)) else (if i < 360 then 0 else (if i < 361 then 0 else 0))) else (if i < 365 then (if i < 363 then 0 else (if i < 364 then 0 else 0)) else (if i < 366 then 0 else (if i < 367 then 0 else 0)))) else (if i < 374 then (if i < 371 then (if i < 369 then 0 else (if i < 370 then 0 else 0)) else (if i < 372 then 0 else (if i < 373 then 0 else 0))) else (if i < 377 then (if i < 375 then 0 else (if i < 376 then 0 else 0)) else (if i < 379 then (if i < 378 then 0 else 0) else (if i < 380 then 0 else 0))))) else (if i < 394 then (if i < 387 then (if i < 384 then (if i < 382 then 0 else (if i < 383 then 0 else 0)) else (if i < 385 then 0 else (if i < 386 then 0 else 0))) else (if i < 390 then (if i < 388 then 0 else (if i < 389 then 0 else 0)) else (if i < 392 then (if i < 391 then 0 else 0) else (if i < 393 then 0 else 0)))) else (if i < 400 then (if i < 397 then (if i < 395 then 0x262616b2ca14b89aa46c20c0ecc6aa2ee14608b43a217108c83000ca00002625bab2b4145c9744642030e886902e414288ac39816508782e80b8000026255b62c994c498446d20d8ef46b230014a88ec3c418309483080dc00002624fef2b5942096245b1ff8eb069c2f514a88cc3aa17509082dc0ae00002624a122bb943c98045b2040ea86982ed14608c83ae17e09002dc0ac0000262440e2d5151499e47e20e0ed06aa2f914d89143b417f08b02f80ca00002623e6b2a313bc92842e1ee0dfc63c2d113a888839216d08182900aa000026238702cd14f89e04862148f386d431415989343ce18f09283400da000026232a82b514509724561fa0e5c65c2ce136887038816a08a02e00b800002622cef2af13ec9564551fb0e786882eb13e889c38c16c08982ec0bc0000262273a2ac93dc92c4391ef0e186502c1138084036015707c02a00a00000262217b2b7142495e4521f48e386642da13d086c36a15f08502b80ac00002621b8b2c694c09aa4652068ee86a02f214488b038c17108a02ec0c4000026215a62c0149c99447120c8eb86982e514188d43b017808c830c0bc00002620fac2cd95109b84772060ed86b630014d88ec3ac17208a03000ce000026209fc2a713a09284301eb0e1065e2d1139085038817308c02e00ba000026204432af13f49464521fb8e8068c2ed14388d839a17308e82fc0b80000261fe672c1947498c4602040ea46ac2fd15689103d218109103100b20000261f8552d415149c648f2170f1c6d230815908f83b017c08c02fc0c40000261f2782bb948499646a2018eb86b02fb14889003b617e09083040c20000261ec832ce14d09c047e20b0ef46a42f614f09103da18109003080b20000261e6932cb94f09c048520e8f186ce30415088cc3b017d08a02d40b80000261e0bd2bd146c98645a1ff8e706782e313e88a839618009303000bc0000261dafd2ae14249644541fd0e4c65e2d613a083838217108a02f80c60000261d5292bf94c09984672048ec46922e114308bc3ae17708c02dc0be0000261cf512bd94989844642080edc6ac2f314888bc3b818609183200c00000261c97b2c494b09ba4722068eb46962f214688b039016008402d00ac0000261c3b72b6144c9684581f98e106702d2135086437616308582cc0a20000261bded2b7144096e4591f58e586842e414388ac38416d08b03040be0000261b85429f93a09324401f18e4065c2d514308ac3b017b08e02cc0be0000261b2792c1949c9a646a2040ea46a82f414988d03b617a08c02f00b80000261aca12c114a49b047c20e0edc6a42ee14588d43a617a09383300c60000261a6cb2b9143c96244a1f78e406682d5140087437415408382b80b60000261a1032b694249504481f78e646722df14788b039417308e03180b800002619b302ba145497e4571fd8ea06a02ef14c89003ba17a08b82ec0c20000261956a2af941094843c1ef0e046522d113b889439816f08a02c80ac00002618fa52b3942c95e4571fc8e8467c2df13f887c38016508302c80aa000026189cd2b4944898245b1fe0e7468a2e814288c43b817508a82d80c6000026183fa2be946896c45d1ff0e9c68e2ef14208a039616708882d00c000002617e3b2b5141094443d1ef0e1064e2e013d088c37e16208582e80b2000026178592c814c09be48320b8ef06ac2fe14b88f83ce18b09583240d0000026172722c594bc9aa47720d0eb86a42ee146089c39216708802c40ac00002616c802cb94dc9bc4822128ef06aa2f314988fc3ac17508a82e40c20000261669d2c314c49b048020c0ec46b42f714808a438816608702bc0c0000026160ca2bb146497e4682038ea06882ec143089c3a817408c82dc0aa00002615ad42cd14909884591fd0e8868e2f314808b039e17708a82e80ba000026154f52c314a09904612000e746722dc14488b83a016808482c00b200002614f092c7949499c46c2098ec86c630014e09043ca17308702dc0c20000261490b2d095149ce47720d0ed06aa2f214c08f03be17a09182d80cc000026143072d1952c9c648620e0ef06c830d15809103be18b09403140bc00002613d1e2c494b499c47520c0ef46ca2fb14a08ec3c018409303040ca000026137382c7949098246f20a0ef06a22fc15109483e218c09303000bc000026131552bf949898245c2080ed06ae2ec14788cc3b016a08702bc0a200002612b662c494a896a4671ff0e6067e2e3146889839617608f02ec0c4000026125832bf948c9804642030ea86a62f314b89043bc17708d03100bc00002611fd32a993ec9424471f88e486682e014088a839016208282b00b4000026119e12cf94a49824672030e9c6942f715209243c418e09c03180b0000026113d12dc15489e649821f0f746de31315c898840a1a309a83440e000002610de62ca94e89a246920b8ec069a2ee14908d03bc17908482d80b20000261080d2ba147497e4692078eb86902e914208a039c17608a82e40b60000261023a2b3944097445e2000ec46a02e214909083aa17908882dc0b80000260fc582bf147c99646d2028e7c6722e313e88a439216208702e00c20000260f68f2b0943095a4581fe0e886762e014288943ae17608d82f40b00000260f0b32bf146c9944692060eb86a62ef143087438416307e826c08e000 else (if i < 396 then 0x263d8d32c494a898a45e2000ea86962f314908e43a417508d03180b20000263d3082bb14489604551fe8e706862e7140889037a17108b02dc0a80000263cd432b313fc94a4481f40e0063c2d113b888039016908202a40b00000263c79f2a313b892843a1f20e106462d413b887c37e15d08302a40aa0000263c1a92c914b099a4632020eac6922e914788d83b217c08e02e40b20000263bbcc2c514ac98a4652020ea86a02e6144088c39416608582b80c00000263b5d92c2149c98846a2090ec86b22f314608c03b417509683280bc0000263b0082c0149c9844662058ec46ba2fb15008f03be17b08982e00bc0000263aa0f2cc15109d64842148f386da31415d89884121a70a083300d00000263a4362c3148c9844562008e5c66c2e013d08b03a617408b02fc0b000002639e802ad144095a44d1f88e806942ed14608b439e17608e83080c6000026398a82b9944895445e1ff8e6467e2dc13b088037815b08382bc0ae000026392de2b7144096644f1fe8e786822ed14a08c839616e08902e80b200002638ce22d014e09da49521a8f606e8312156891c3e818f09603380d0000026387192b7141c94e4572000e746682db140885837216107f02840a80000263813a2c314c09a04752078eac6a62ff15109303e218f098031c0ca00002637b6d2ba147c97045a2018ea06862f013f086439617909403200bc000026375762cd14e49a447320d0ec06bc2f314908d03aa16f08782d00b600002636f8d2c114b099846e2068ec06a42f714a88d43ac16f08402b40b4000026369d22b0141494c44f1fd0e7067c2e513c886837417608d82fc0c4000026363e62cb94e09b247e2148ee46ae2f615009083bc17d08c82e409e00002635e362a994049544471f98e8868c2e113f085837817108a02f00ca0000263584a2c8149498846b20a8f0c6d630d154092c3e419009803580d6000026352632c1949098645b2020e9068e2e614808d43b218008a82cc0c200002634c982b5143894e4461f40e5867c2e4144089838c17308d02dc0b6000026346c52be148497e45c2028ea86922f214708d43bc18809683280c6000026340d92c714bc9a046820b8ef46ce30a15f09903f419309583340c600002633b0c2b7145897e4612048eb46a22fb15088f43d218a08e03080b6000026335432b013f09524401f40e1c6402c413a088438416b08a02dc0aa00002632f552d015109d24862160f486fc31d15789103e618909603300dc0000263293c2da95449e048d2168f1c6c230015189183d018408d02d80b4000026323842ae940c9464421f30e146642d013c085037815b082829c09c00002631d862d095209cc47120b8ed06ba2fc150092c3de18809503080ca000026317c02c014989884632060ed46a8302152892c3d218308d02f80c2000026311d62c894f09b047420c0efc6ce2fd14a88f83ba17909283300ca00002630bf12c0949099a47f20f8f346ce307155092c3ca18309183080c6000026306052c3949498046d2060ec069a2ec14788bc39617208a02ec0b0000026300372b9943896a4591fb8e9068c2f114788e839e17508b02d40b60000262fa452cb94c49a647420b0ef46b630115609243c618209003140d20000262f4482c814b89964722040ecc69a2ec14708d83a816d08d02e80b40000262ee862af940c93c4441f50e386622d0136087438216208302b00ac0000262e8852c994a89a24762060ec86942f014a08b039a16808702bc0b40000262e29c2bd14589884601ff0e706882e314788c43b617d08f82e40c00000262dcb82c894d09aa47a20a0ec86a230414d08e83b817b09402e00be0000262d6fa2b0940c95a44b1f68e2465a2d813f089039417208a82dc0b00000262d1242b9946496c45e1ff8e8867a2e914608ac3b017508782e00ca0000262cb352cf14d09b04722060ed46b42ef14708a439c17208902e40c80000262c53b2cb14e89c84832108ee46bc30014b88dc3ac17608d030c0c60000262bf522c294d099c47520b8ecc69c2f514808b439a17008982ec0da0000262b9822b6943c9744572000e8c67c2e414c88f03bc18909182f80bc0000262b39f2c4148c99247420c8ecc6aa2f615089103c217c08f02f80b00000262adce2b3945096845b1fd0e706922f015009203e218f09202f40c80000262a7d92c414a49ac47a2078ebc6a830014b88e43c218909203100d60000262a1f82c094809904662018e8469c2f114c88e03c2182095034c0ca00002629c112c414b89a04732098ea46a02f714d08e83ba17d09102b40b8000026295ff2da15389e049521f8f5c6e230114e88f83b017d09002f40ca000026290272c794ac98c4702070f086b22fa14d88f83ae17408902d00be00002628a352ca14ac99e46c20a8ec86902f214708c03b017c09002d40ba000026284772b2941c95844c1f38e246582cc138087437615e08282bc0ae00002627ea72b7142897845e2060ea46982e414b08e43c617e08e02fc0ca000026278fd2a8140495644d1f48e4c6622cb139886c37a16108202bc0ae000026273072c694e899646f2070ec86b02ed14a08e03c017608d82ec0b600002626d282c0147099246d2078ecc6bc2f914c08cc3ac17108a82d00c2000026267542b7943495c4541f80e6067a2d613b888438616908302b4094000 else 0x2654fce2c1148c98446a2080ec06b22fb14a88e43b618109083100c8000026549e92c914d499a46b2008e786842e814708e43a017e08e02f80c4000026544192b6143c95e4572020e9467a2e213f087c39c17208d02fc0d400002653e432bd947898445d2030e9c6a42f514b08d03aa16b08882cc0ac000026538902ad93fc93043d1f18e3c6702e614208cc39a16208482bc0be000026532ae2c614b098e4722038e9469c2e714688d03a218409302f40c200002652cff2ab94089464431f08e086502d813f88a83be17808d82f40ba000026527552a813f493c43a1f20e106502c6133885437616008582cc0ba0000265214b2d815349d24862120f0c6a22f314d88f43b417708b83100ba00002651b672c6948c97a46c2088e886a62ea14708c83be17708802c40ae000026515592d4952c9c647c20b8ef06b62fd15209103d018009182f00be00002650f562cc14e09b24722030ebc69c2ef14408b43a217308e03100cc0000265097b2bc148c9a04722028e986962f114d88f43b217c09483000c2000026503a62bb144c95e4551fa8e6468e2eb14988f03aa18109603140da0000264fde12b6945497a46e2070ee46842de14888b43aa17a08b02e00be0000264f80f2be94689844642050eb46aa2ef14e89103d418809483380d20000264f2212ca14d09be47e20c0ee86a82f915208ec3c4179086829c0b00000264ec712ab13c493c4481f30e4065a2dc14288a037c16308782e40c00000264e6a02bc148c9804642020e946822e314288c039616b08d02f80c40000264e0c12c514a497245e2050eb46a02ef14a08a83a417c08c02d40b60000264dac02d014ec9ca47f2110ee06ba2f314c89003c817f08c02fc0b60000264d4cc2cd14f49904651fc8e546702dc140888c38216108102c00bc0000264cec82d395189be4842150ef86ce30114e09043ca18109403240c20000264c8f32bc944c97845d2008e6868a2d113b084c37c16b08a82e00a00000264c3232b3145c97a45f2058eb069a2e2141888c37816208482bc0b40000264bd422c214a897e4672070ebc6942f014708b839a17409183000ca0000264b73c2cf95189c64822068eb06982f715189083b217b08e82e40ca0000264b16f2b9143095e44a1f68e6c6942ea14b08b43ac17708b82c80aa0000264ab962bd94809804612028ebc69c2f914688e03aa16f08902d40b80000264a5a62c594b89a84722070e8c6962f414889003b618209083080b200002649fc12c494b899646a2008e886802e613c08a039616f08982e80bc000026499f82b7142c96245b1fe0ea06882ec14808c83be18709302f40b6000026494182c794d89a046f2060eb46a82ff14f08f83b217b08f83040bc00002648e612ad140494a4551ff8e6867e2e314408c03a017b09283000c00000264887f2c014a497c4541fd8e9c6a82fd14888c43b217608c82d80b2000026482862cb95089c848f2168f086ca30114c08ec3b817808c02f80be00002647c902cf95149c247c20d8eec6c830215209143ce19109883180ca000026476b82c094a09ac47320b8f246dc30e15409203d018d09103100c8000026470e32b994689544401f20e4c67e2d7139086038216a08d02e00ca00002646b262af14089524551f60e4066e2d913f88b439c17108902fc0c2000026465662b494549864672038e846862db13b082c35015d07d026c0ae00002645fb92aa14009524471f78e5c6842df143887c3a417308a02e80b8000026459e72b9143c9704561fe0e4c6742d513f88b83a817508d83000ba000026453fd2c314d49b047320b0ed069a2ed14d89183bc17e09403400e200002644e0f2c794ec9c047e2118f206d831415e09643e218a09082e40ba000026448402bd14709804602058ed46822e314108d03a217c08b82e80b80000264423f2cf14f89c04842148f286c22fd15088f83b817808e02ec0c000002643c782bc147898245d1fe0e9c6982f114908b83a018308d82f80be0000264369c2bb94589744652058ebc6942ee14908c43a816d08b82bc0a2000026430b62c694d09b246f2048ea86922de14308c43ba17108902d40c800002642aa62d8156c9f849d21e8f786f230b15208f43b818909903240d4000026424b72c614b49aa47a20f8f0c6d230b15309483cc18608d02ec0c400002641f102a213d494844a1f48e3864e2cc14108b43a816e08b02f00cc0000264194f2af13e092e4381ef0e1064a2ce135884836815e08482e80c6000026413642c694bc9b247d2110f246d230115408f83c2186093831c0c800002640da02b4941095e44d1f80e5c6802e914708dc3a217008902c40a8000026407bf2c214b899c4611ff0e8466e2dd141889439416808802cc0ba000026401e22bb14709864642058eb068a2f014708b83b418409603140d20000263fbf02cc14d49b247e20b8ea86a82fa14e08c839815f08602d80b40000263f6172c094a899c4732080ed46b42eb14b890c3d018708f02f40ce0000263f00b2d114b499e4722118f186e430b15208fc3b217e09102fc0bc0000263ea2f2bc14b09aa46c20b8efc6c42fb14f88fc3a616f090832c0cc0000263e48d2a993c892043a1ef0e1464c2d413e089c39617608b02dc0c60000263deb82b9947897a45a2018e7867a2e014388b83aa17208982e4096000)) else (if i < 398 then 0x266c78c2b413f494444d1f88e346782e314708983a817908d02e80b60000266c1982cb14b099a4712080ea46962ed14388c039017908c02d00c20000266bbce2b914189564561fb8e706902ee14d08d43ae17808702ec0c40000266b5e62c3949899a4762118ed06982ec14488d039417a08c02e80a80000266aff92cb94d89b848120b8f046c62fc151092c3ce18309183080c00000266aa1b2c594ac97e4692080ea46922e614488c83a217908c82b00b20000266a4222cb14f09bc4802098ec46b02fe15109103d017f09083340e000002669e4d2bf14949704541fe8e806802e314308cc3ac16d08802d80b60000266985d2c8149498c4642038ea468c2e614208bc3b817808e83180c60000266929a2b7948497c4501fb0e886902e814808b43b617508c82cc0c000002668ce22af14089524561fe8e8068a2d713b887839c17408d02d00b4000026686f62c1947497a4602028ea46842df13e888438016108602dc0ac000026681242bd145097645e1f68e1c6562cc13a886437e15707b02980a800002667b2f2c614c49ac4722110efc6ba2ff15088dc3b418609383000b40000266752f2d2151c9de49621a8f586de31215a89603ec19409d83640e200002666f652b3143097e4652038eb06962e114188b43a017609082f00c20000266698e2bb94ac98a46720a0edc6b02fe15409143d418d09703480da000026663b72bc147498046c2050ec46962f314288ac3a216f08382c40ba00002665dc52c794c49be4772100f1c6d630315189143d419009803300d2000026657d62c894a09b64882170f186d030514e09003de18709683280be000026651ee2c494a49844642018e8c6902e714988f43c017808c02d00be00002664c222b393fc9424441ea0e186622da13a085c38816a08182c40b6000026646542b814409624571fa0e606702e714508d039e16f08d02e40c0000026640552cf14f89a646a2090ec86ac2fa14908d439e16f08b02f80c400002663a732c114989a047020a0ed46b22fb14f88f83b618409082f80b4000026634c72a793cc9384381f00dfc63e2c2130883037016208903000c200002662f122af941495a44e1f98e4867e2e814908d43be17c08d831c0bc000026629482b7143494a44e1fe0e306762da140885838c16e08702e00b00000266237b2b5142c94844c1fb8ea06782e4143889c39816c08102b40a800002661da92bb945c95c4582030ec06a82f314d88e03bc17a08c03080bc000026617c62c1149098245c2010ebc6a02f514908dc3b8184094032c0ce000026612022b7147496c4612028e7c6922e514488a039e17608f83080c400002660c262bb146c98c46c2060edc6ae2f014908a03a217508b82c40ba000026606402c714b09ac47120b0eec6c82f914c08e03a817108d03240c2000026600782b8948499445e2060ec86a42eb14b89083bc17a08802ec0d20000265fa402ec95b8a1a4ab2248f886f432015a093c3bc17c08e031c0c60000265f4542c494b89ac47f2120ec46982eb14708d43c018009283300c60000265ee7f2ba14a09824662048ea46a62fc14b08d03b017508e03100ca0000265e88d2ca14b09aa47d2158f2c6c830f15709143bc18308f02f80b60000265e29c2c614a09aa4782080ed86a42f814708b839217108c82d40be0000265dcb12c3148c97246a2048e8468c2ed14a09103be17c08d82e00ca0000265d6cb2c694ac99a4772090ec46a22f014208cc3b017808e83000b80000265d0f82bb148497c4621fd8e8c66e2dc14488b83a417b08b02c80aa0000265cb112c694b899a4742080ef46c230e15589383be18509003080ca0000265c5362ba94849884642058ec06982e914108b03ac17909302f80b40000265bf3d2ca95149ba48420f0f146ba30015108c838416908702e00ae0000265b95f2bd94889904672090eb06b62fd14f89243e218e09583400c60000265b3b02a613c49244331eb8dd86502d413a086035614e07e026809a0000265add52be147897245b2030e786782e814a88b43b017208c02ec0a20000265a80b2b5942c9644561fb0e786782e314488d839816d08982cc0b40000265a20e2ce14f49c64832108f186ca2fc14d88fc3d418009203180ba00002659c1b2c614cc9b247a2100ed86ac30114f09103d218509002f80c8000026596462ba944c95444a1f50e406802dc14108a039617608902c40ac0000265907c2b8144c9624581f98e7c6922f114588b439016e08e03140c600002658aa22c0949498a45e2018e946922eb14788d83b617808b02e80c2000026584c62c3947098246a2048eb46962f114908e03ac17b08f02fc0b400002657ec82cd14dc98c4662078eac6a42ef14d08d03be18209303400d6000026578fb2b7942c9724551fe8e9068c2de13f888039216608502d40a4000026573072cc94f89c24822100f206d630e157094c3e218f09503200c800002656d392bd146c9764562020eb068a2ec141089038416608902ec0c40000265674e2c914b09a04692050e946b42fe14e88ec3a016d08b82c40b60000265617e2af14009444421f98e5067c2e114308c038816d08482b80b600002655b792d094d49b44752060edc69a2f714988a83a017a08b82e80c2000026555a52be144c96e4612020ecc6ac2f914c88ec3b218008802fc0aa000 else (if i < 399 then 0x2683ed22bc949c9a446820b0ecc6a02ee14688d03a017508e03080d40000268390b2b6944096e45c1fe8e7867a2d713e08a83ae16a08c03040c0000026833212c594b09a646a2060eac6882ef14c08c839817108f033c0d200002682d342c614949a64692090ef06a82f1142889439017508b82f80c80000268275f2be94849804622050eb46982e814988e43c818409202f00bc000026821b42a2937c91642e1ec0e106582be133885837a16408502980ac00002681bd72ba147c9884632048e9868c2ed14908d83b217508d03180cc000026816192b0942096844a1f90e2c6662d613a085836415207e02b00b4000026810342c1948c9924612030ec46ac2fa14e08e03c618009103140d600002680a572ba147c98a4662048ea06922ee14988dc3bc188091830c0c2000026804a42a893d49324411f08e1064a2cb139887838a16808702d80c20000267fe8f2da15309e448c2148f106c030a15609103be17708a82c00b20000267f8c02b7941894e44a1f58e7067c2e3144089c38e16b08a02a80a00000267f2e82be948098a4651ff0e786702e4149089c38216508482d80ce0000267ed092c414889ba47920e8f0c6de30314f09083c618a09102ec0d00000267e72f2bd147c9984602060ec86a82f614688b83a417208902e00a20000267e1542bf94609724602000e8c6902e714588d83bc17e09403040b20000267db672c2148898c46820b8eec6ac2fe14a08d43b017f08e82f40c40000267d59c2b9145097c4581fd8e8467c2df140087c38416c08b83000ca0000267cfaf2cc14f89c648020f0f2c6d431215709103c4183096033c0dc0000267c9a32d094e89a847a20f0f086c02fe15589003c8184094031c0c40000267c3e52b194109484481f80e4865c2d8141889c3ac17608d83180be0000267be1f2b3944c95844a1f60e506802ec14a08ec3ba17308b02e80c20000267b8292cf95009cc4892118eec6ac2f514d08b439c17c08c82f00b80000267b2532be94809824652050ebc6a82f714688c03b017108c82e80b80000267ac7a2ba944098246d20c0ec86ac2f814688cc38e17108a02f00b80000267a68b2c994a899047720c0ef46ce2fc15009003b816f08a02ec0c20000267a0832d895689fc49b21c8f646c230615409143d217f08d82e40b400002679aad2bc148499c4702070ee06c22ff15689503cc18509282ec0be000026794d32be149499246c2050ea86a22ea14588cc3b017408e82f80b400002678ee92c394c09a047b20b0ee86c0306152892c3ca18909103200ca0000267892d2a693b89204331f08e1464e2d113b886c3a217008802c80b4000026783872a813a89284331eb0de06482d9142089838c16908b02dc0bc00002677d822d415349de47520b8edc6b030114f89203e0191098832c0ca000026777a12c094a899e4632010eb06b42f814b08e03c418c09003040d8000026771b62c814b89a246e20b0f006b42f614e09143e019109783240c800002676bc32cf15009ce4852140f446f8316159095c3e219009382f80ba000026765ff2b3941c9664592070eb06962f214688b039e17a08802ec0bc000026760242c4149498c4682058e9868e2ee14688dc3a217509082f40ce00002675a252d615309c64822120f046b030415209203d017708c02cc0b4000026754412c314b09944662028e846802ed14488b839017508a02f80be00002674e932a413e09404411f50e146662d5137885c38016908502a80ae000026748a12cc15109a84762118efc6ba2f714c89003bc18708f030c0b2000026742c52be948497c4511f80e346742e014909043da19009682e80c400002673ce92c194a898a46420b0ee06c030014c08e83c016f08902d80be0000267371b2b5944c96c4521fc0e586782d6140887038616a08c82d40ac000026731072d395489e24872110f206c82f814e08f83ca17808c82f80c600002672b272c094749844612008e9468e2e113f885437416508782dc0ca000026725602b8143c96e45b2008e906a22e914a88a839e17a08e830c0c400002671f622cf15049e848e2120f1c6c630415189243e218d09783380d8000026719922b5144895e4572000e806842eb13f888c39017308a03000ba000026713ba2bd947099246a2030e946902e814608bc39a17208d82f00c400002670dd82ba943c95e44d1fa0e5c65c2d3140086c38416408782ec0ce000026707fc2c1949098a4642008e986a62ee14e08e83b216c08a82e40b20000267020d2c614cc9b647e2088ee46c0308157894c3f219509d032c0cc0000266fc412b994509704602028e8c6a42e714708983ac17a09282d00b00000266f6662c014a49a247b20c8eec6ce30815509043c017e08e02f80c20000266f05c2d195089ca47d20f0ef06c430415a891c3d017b08a82d40ae0000266ea822bf148899046f2050ea468e2e614808d83ae17308b82f40c60000266e47d2d615349e24932170f306cc30e153093c3dc182093832c0c40000266deb82b2141095844d1f70e506682d313c888038216408582ac0980000266d8d62be945c9724631ff0eac6942f414d08e83c017908c03180da0000266d3272aa13c09244401f68e546662d4138886838816f08702dc0bc0000266cd452ca94d09a246b2050eb86982f614d88dc3c617708e82f40c2000 else 0x269b6ad2c694d89ac47e2098ef46bc2f514e89183b817d08b830c0bc0000269b0c22c814cc9c047720a8ed86aa2e914788bc3c017f08d82f40a00000269aadc2c414c89944742048ecc6b22f915308dc3a816a08582d00c00000269a4f22ca14ac9924692068ec06ba30014888c83a617f08d02d40aa00002699f2f2b3941496044c2008e7c6842e814488a83aa16708402cc0c00000269993f2c794989904742058ec06a02f314788c83a616c08382d00ae000026993792b4943896445b2030e906922fb14d88ec3ae17c09182ec0b800002698d7c2d295349d247a20a0ec06b62f114988dc3b617508f82f00b4000026987a52c514ac9824671ff0ea069a2ee14a88a03a017108982c40b6000026981ae2cc14e09b848620c8eec6be30715289103de18609003100c800002697bd02c0148c97e4612038e4c68e2ef15188fc3c017f08e83280c0000026975fa2b7141894444d1fc8e5067a2e014388a839416b08782ec0b4000026970322b293e893c4451f30e206482cc13a887c39416f08882cc0b200002696a562c1149c99446c2050edc6ae2f914f88f83c218108c82f40be000026964752bd145c9644511f80e4867c2dd14688f43b218109003180c800002695e8b2c294c497e4511f58e1865a2dd14b08b03a817908d03080d2000026958942ca14ec9ba47e20d8ed86b42fe14e09043c617f093832c0d4000026952d52b214109384421f20e3466a2da14188b03a217d08e02e80b400002694cd62ce15149b847720f8f1c6d230b15689303c018309003200bc000026947022b5943c97845e1fd8e646862e914608c039e17508682e40b0000026941262ba948c9904652020e986a82ff14c08cc3a617108982b409c00002693b2a2ca94e89ae47a20e0ee06ba2ea14908e43a617808b82fc0d8000026935432c5148899a4692040ed46cc30315089203d018508f83080c000002692f6f2bc94689764582028e7c67e2e314108983a616a08a02d00a0000026929772c9949c9a247c20b0f006b82fc14c08ec3d219509983200d20000269237f2cc14e09b246f20b0ef86cc30415989383d418809282ec0c200002691db92b113f895a4481fb0e7c6842ea14608c439a16508502cc0ae000026917bd2cf14f89bc47b20f0edc6aa2f414a89143be17d08e82fc0b6000026911c12d315109ba4802100f006b42f414708d439016c08e82f40be00002690c102aa13cc91c4381ef0e046542ce13a887438416308602ac0aa0000269061e2c894b09ae4752058ea069a2eb14a08e03b618408f02d00be000026900422bf14709864591fc8ea46922ee13e888439215f08202c40b60000268fa732b9146898646c2028ea86942f414388a03a817e08e02fc0ba0000268f4da2a193a492242b1e88de463e2ce139886438e16008582f40ca0000268ef052c0946c98e46c20a0eb86962ed14888d03c418509503140c80000268e9282c0149899a47a20d8f0c6ce2fc15188fc3bc17e08e83040cc0000268e3702af13f89404471f68e246622e213e887838c17308802f40b80000268dd6f2d095189d448c2188f406dc31015909683fe19b09c03180ce0000268d7712ce951c9d64852108f306ee31e15c099c40619709d03380dc0000268d18f2c314b49984672050eb06942f214988d039c16e08982f00ce0000268cbc12ba145097c4602058ec868a2e414808e03b617308c82f00ba0000268c5ff2b2141c96a45b2030eb069c2f114c08c83ae17a09683380c40000268c02e2b4944496e4622040eb469c2eb145889839a16708382d00bc0000268ba302ce95349cc4822160f0c6b62fb14a08b83a017208c82d80a20000268b4622b414409684502010ec46a82f314c88d439216f08702e80bc0000268ae6f2c294a099c46d20a8ebc6b62f514808dc3c617c08d82fc0be0000268a8942c0947c9824641ff8e846862d9142088837616f08882e40c20000268a2902d495249c848a2160f486e431615909303cc18209283040cc00002689cb82bd145096a4561f90e486642d213a087838e16f08d02dc0c0000026896d92bf948899647320a0ed46b630915389283d418a09483100ce000026890f62c0146c9784652000e9c6982f214988d83b618108c02e00c400002688b182be949098e46e2090ee86ac2fc15109183c817608c02c80a2000026885422bc14509764602040ee06b630215108bc3b217e091831c0b800002687f522ca14a899e4672048e986a42ed14808dc3aa17908c82d80ae0000268794c2d395009c447c20b0eec6ae2f615009083b618409203300d2000026873832b6944896c4571fe0e6c6802e614888b43a617a09003040b800002686d8c2c714c09b447820e0f0c6c630b15208ec3b618909783340de000026867c72b7945c97a4621ff0e706802e414208683a216808702d80ae000026861c52cc950c9ba47f2110f1c6de30b15509403de19809503280d600002685bea2bb14809864602048eb46a82e7143088c3a217408802c80b4000026855f52cc94f89c84872170f306c230114f08f83be17c08d02e40be0000268503a2ac93dc9324401f30e246642d914508bc3a617608c02f00c600002684a6a2b9143896e4571fb0e4c6582ce13a887837416808682ec0c4000026844a72b114149424491fb8e6068a2e313f088038416608882f40c2000))) else (if i < 403 then (if i < 401 then 0x26b2ccc2c0947498045f2028e986982e9145888438416908502c80a4000026b26eb2c714c49a64772088ecc6a02f6144888839417308b82d40ae000026b21212b5143096a45a2010eac6962e8144088838e16a08902e00c0000026b1b392c514a09a24601fc8e906842db140889c39017608c83000c6000026b156a2b9941495c44c1f68e546562ce13f089039816608902d00b0000026b0f982bc94649744621fd8e8068a2eb13e089038816b08b02c80ae000026b09d12b6141c94a4511f48e446722df13d886838a16608682cc0b2000026b04072bb145897444d1fc0e8868c2f214b88e83bc17f08e03140c0000026afe062d595349da4852160f246c230015309283d618f09b83480d8000026af8222bf947c97c4612060e8c6922e414288c83a417108902e40ca000026af24e2c2949898c4652010e986982ef14788d03aa17308b83000be000026aec5e2c794a89a24702060e9069e2f614908e03b817a08c82b8098000026ae6922b914509924672070e846782e614588e43a817709202fc0d4000026ae0c62b4145497a45a1fa0e6c66e2ce139887038c17008d82d00ca000026adb102aa13dc9364471f60e2c65e2d913e88883a616907e829c0ac000026ad51e2ca14f49ae47820a8ed06ba2f714408d03a016b08a82f80c0000026acf522bd947c97c4621ff8e9469a2f114908d43b017d08e82c00a8000026ac9632c614cc9c047d20c0ef86c82ff14a08d83a016e08982e40a2000026ac38f2b7146097c4672090ec469a2ee14988e83a817e08882f80c4000026abda32c814e49a04792070ecc6aa2fb151892c3d218b09282fc0c0000026ab7da2b9945895a45d1ff8e806842e414688fc3b817b08d83100d8000026ab1ef2c314b499c47b2128f0c6b02f414708b43a616d08b82dc0c4000026aac332ad140895c4581fe8ea46822e113e087038e165083029c0ae000026aa66a2b6943896245b1fd8e8067c2db13e88b43ac17b08c82dc0c8000026aa0822c5146898e4692068ec86c22f514608c03bc18209283180d6000026a9a9c2c514c09984712090f046b62fe14f08c83a017308782d00a6000026a94ae2c594b899447420c0ef46de30c15309083c017e08882a80a8000026a8eb92cd14ec9c046e2070ed86c02fc15108f83b016f08f83000c0000026a88ee2b0944095244a1f58e606822f0146889439416b08d03080c8000026a832f2b2141c96c4502008e8867c2dc13f88a438a16f08902d40c2000026a7d612b6144095e45f2018e9c6942e514a88d43b417f08e02f40ce000026a77952ba14449484461f78e7c6882ef14708d43aa17809003000c6000026a71b62bc944898445d2038e986922e714a88dc3ae17c08e82e80b8000026a6bef2ba94809684571fc8e6c6762e814688d039616c08982e40bc000026a66422ad93f49364331e88dec64c2cb13b085436e15a08182c80b6000026a603f2d295349d048420d0f046ca308154890c3c017c08d82ec0c2000026a5a712b694489664521fe0e686982e514808c43a617409003100c2000026a54992c2149899246d20c0ef86c62fc14f08fc3d818609183040ce000026a4ed22b394109524491f80e806842e714708e43b417908d82b00ac000026a48de2ca14d49ca4802100ef86b82fa15288f03b617e09183180c4000026a43262af94149564521f98e6066e2d213a083c36415a07e02880a4000026a3d4b2bd149899a4702038e9867e2e2142089439817708f02ec0bc000026a377b2b9945897a45f2028eac6b82f514988dc3be17209103500c8000026a31812d014e09b248820e8ef06ba30415409403dc18e09a03500c0000026a2bbc2b5941894c4491fa8e846a22f514d88fc3b617308682d00a8000026a25c22cc14f09be4852120f146c030515889083c017808b82f40aa000026a1ff72b1940894844d1fe0e586842df14008a438c16508182a80ae000026a1a142c094989a447520e8eec6ca30114c08ec3ba17408e83180ce000026a146d2a893b89264461f00e0866c2d213c886038417b08a82e40b0000026a0eae2b113f092a4401f20e246582cc139088839417508d82e80c0000026a08c32c614ac9ac4702088ed869c2f414408c03aa17308c83040ca000026a02d52c714a09ae46e2038ed869a2ec15008f43ae17f08e02ec0b80000269fce32c914d09a847b20f8ed06a02ee14b08ec3c417308d02e80b80000269f7092c594d49a64712008ea46842e414688b439617308702d80a60000269f1342c014b09984672040eb86a82eb14788e03a017708682c80c40000269eb452c5946497845b2018e806702e614408a03ae17d09302f80aa0000269e5582c194889a046d2048ef46c430314e88cc3bc17a08d83000be0000269dfae2aa13f493c4471f48e506542c8136886839c16508602b00ae0000269d9c72c714b49a44742098ec86882e714388a43a618208f82f00be0000269d4022b294309664592040e7868a2ea13f886838016a08982e40b00000269ce192c494709824642000e9468c2e214608a439c17908702fc0be0000269c84d2b413ec95a43b1f40e1066e2d513a087039617608c83040c40000269c2782b9945497044e1fc8e806822e514508bc39a17408c82d80b60000269bc9d2bd949c98a46a2028e7468c2e914908c03a816d08902d80be000 else (if i < 402 then 0x26ca4d62c0147097e4692080eb86a02f914b89003b217a08b02e00b0000026c9ec82d915609f249a2188f346e431015089203c417d09082fc0ac000026c98ff2b6143495244a1f98e6c6802e814788c439616808782f40d2000026c93332b614389624491f60e4c6762de14288a439017808982e00b8000026c8d692be146497845b1fe8e846a62f814b88d03b417108982e80b0000026c877f2c414849884611ff0e806982f314b88ec3b417f08e02f00b8000026c81b32bc947c97c4582040ee86ae2ef14e88ec3b017f08b82c80b2000026c7bdb2bf147c98646a2060ec46a22ee14708cc3b417a08f83040cc000026c761b2ae941c97045b2018ea46a62e914088a839417408c82d00ca000026c70492c0147098a45e2030eb069a2ea14688c43b217908a82f40c8000026c6a502c914d89c84872148f0c6c430214808cc3c218c09483000bc000026c646c2c094f09a047620d8ef06c22fe15008f83c017f09003000dc000026c5e6b2cf94f89ca48120f0ec869e2fa14c08c03ac17508e02e00c0000026c58a92b314489664571fa0e586862de141088c39616708002ac0be000026c52d52b994589704541ff0ea46982fd14e890c3b017d08e030c0c2000026c4cf42c394a49ba47f20c0eb06ba2fd15008e43ac17809083140cc000026c46f52cd14c89ba47b20a8ee86b22f414b08d03ac16e08b02f80cc000026c410e2c694d09ac48120b0ed86ac2e914208a03a017809203240c8000026c3b2f2c294749784591fb8e506822db14288ec3ae17a08b02f40c0000026c35492c894c49a84802160f086c22f914a89183c418108f82e80b6000026c2f6b2c314889884622028e8468c2e114088bc3ba17908b02dc0a0000026c296e2ce14e09b847d2120f1c6cc2fe15509043c618408e83040ba000026c238d2c394cc9ae47420d0f046902f114d88f03c618208d02dc0a6000026c1d9b2c914b49a04782078ef06c830615689283d818909302fc0b6000026c17aa2c894d49ca4812118f306d02fe14e09103d218408a02ec0b4000026c11dd2b8145497445f2000e8467e2f014508c03a417809003240d0000026c0c002bd94989a24652098e9c6a42ec14488d83b217e08e02dc0b8000026c06462af944496a4511fb8e986862e514088a038a16b08682dc0ca000026c00592c314a89a847b20f0f086b62fd14e88ec3c217c08c82d00b8000026bfaa92a893e893c4431ec8dec6362c913a885036415708002bc0aa000026bf4b92cd94dc9b247620a0eec6c42fc14e88e03ac17508e03000ca000026beecd2ca14d89b24892060ec86ba30515709343f019709582e40c6000026be9132b0141495c46520e0ec46a62f014808c43b617808d03080c8000026be3122d215309cc47f2160f086d6308152895c3f618e08f02f40c0000026bdd3c2b8947497e4611ff0e986b230014a88ec3b217d09683300ba000026bd7632c514b89b647720f0f046ba2fb15388f43b617c08c030c0ce000026bd17c2c514ac99c47820d8efc6aa2f314c09043b818609082f80b4000026bcbb82b7148c9764661fc0e6866e2d813e88b03a217e08b83000bc000026bc5c92c6147898e46d2090ed06862e714c09003ce18f09182f80ca000026bbfca2d294f49d049121a8f346e230715088f83da18608f82f00be000026bb9e62c614989ac47520d0ee46b22fe15489143c418809483040d2000026bb40a2bf946896e44c1fc0e7c6802ea14988bc38a17608d82c80b6000026bae2d2be947895e44c1f90e546702de14188a438e16f08782e40b8000026ba8482c514cc9ae47b20a8ef46ca2f814b88d43bc17d09103500cc000026ba2532c9948898646a20d8ed06b830415208fc3c618b09803340ba000026b9c7e2ba142c96244d1fb0e6068a2e1140085c39417108682e00ba000026b96af2bd147499646b2088ec86982f314b09103ca18e09503280cc000026b90c42c8149497e4662020e9c6802f614808c83b217b08902bc0aa000026b8ad02c914e499e4712050eb86982ec14088943a016b08d02d80b0000026b84db2d194e099e47020b8edc6b22f614809003ba18209303340d2000026b7f252aa13d491a4361eb8df06402cb138886436e15b082029808e000026b79522ba14409724531fb8e946882f114d88e83a217008b02d80ca000026b734d2d115309d648020e0f086c030715209403e419109403500e4000026b6d592ca94c499c4712080ee06ac2f815088f03bc17a09002e00bc000026b673f2de15689da48d2180f346d630a15509143bc18508d02ec0c0000026b614d2c714c49a646c2048e9c6a82e913f089c39a16808b83040be000026b5b7b2bb14749604512018ea06942eb14588c439416d08b02e80b0000026b55942c5947c9744551fa8e4465e2da141889c39c16e08a02ec0a2000026b4fad2c894c899e4692030eac6962ed14788e83b8171089030c0c4000026b49d22c1146c97c4571fa8e646822ee14308b83b217308802d80c0000026b44112b394309784591fa0e606762e4143088439a17408e82f40c6000026b3e402bd147c98a4682048ea86902ef15188f43bc17e08903000c8000026b386d2ba14589764632030ea46862dd142888438c16808602d40b8000026b32ae2b3145898a4692008e6467c2eb14288a43ba17908c82f80c6000 else 0x26e1ba42cd94f09ce47a2098ee46a22f114808ac3ac17608d82f80be000026e15b62c894b89b847820c0ee46b630115089043d819509603040b0000026e0ff92af94309664571ff8e806882e614508b037c16008182cc0aa000026e0a222bd949097c47020b0eb46ae2f614a08d43b217f091032c0c6000026e04552b6146897c45e2000eac6942dd14388a039c17208a02c40a8000026dfe6d2c614a898c4642050eac68c2e114588ac39c16e08502d00a8000026df88d2be147898c47220b8ec469c2fb150890c3c817d08d83080c2000026df2b52c794a499246d2068ec46ae2f314808a439216f08982d80b0000026ded082ad13f895444b2000e746762d313a085837c16a08582c40b0000026de73f2b8143896a45e1fc0e8c6782e014888e83ae17c08c82e80ba000026de1842ac13d494243e1f60e4c67c2e3146089039c17508d82ec0ce000026ddba02bd946897e4622090ef86d02f915209203c817d09303240cc000026dd58d2de95549fc49821d0f4c6d831015989483d618909083240be000026dcfbb2b914609604551fe0eb06962fb14e89043cc18408d02dc0be000026dc9d22c1947897a4642058edc6a42e814a08e83ce18709402f00b4000026dc3f02c5948498e45c1fb0e406682ce13c08ac39a17508b82f80c2000026dbe022c914c899e47820b0ee46c02fc15709183d418309082f00c0000026db8182c594949a846920e8efc6b62f714a88d43bc17609083000c6000026db2702aa142095043e1ef8e0c6562d313e889037a16508582e80d4000026dac912be948898c46f2068eb06b02fc1470890386170093832c0dc000026da6ba2bc14789824662040ebc69e2ef14488d03a0168081029c098000026da0da2bd948897c4652020e9c68c2ee14188a037a16908582d00ba000026d9b232aa13c091e4421f68e2c65c2d91410888380162081029c084000026d95352c714d899e46d2090ee86b02fc14e88e83d018309102e80b4000026d8f462ce94d89ac47620a0ec469c2f014e88b838e17408c02e40c0000026d89782ba943096a4521f58e686722e214108a039e17708b82dc0b2000026d83d42ae93c892a4451f80e206622dd14288b03a217808d83000ca000026d7dd12cc14e49b44822180f146cc30314d08c83aa17d09002fc0c6000026d78002bd145496644b1fb8e7c67a2df14008a43ac17508f02f40b8000026d722a2ba146498446a2050eac6a02f914808d03c618109583140d0000026d6c2f2cf15009b04712090ec86922f114288a438817409082f00c8000026d66532bd149499646e1fe0e646822e614c88c43b017c09202dc0a8000026d60952b2140c9564582050ec46a02f114908e43b617c09083080b0000026d5ade2b294189564571f90e6c68e2dd13d886838616a08882a80a4000026d55032bb94489604551fe8e4866a2d7143088037c17008d02f00b2000026d4f152c0947098a4601fd8e846a02ef14c08d439a17709003180be000026d49352c014849704601ff0e8c67a2eb14208a83aa18209102ec0b0000026d432d2d294c49b048c2108ee06b830215589303d618a09483200e0000026d3d512c1148099047020c0ee46ca30a15508fc3be18609603200cc000026d379e2aa14009484501fb8e306622d113f088439816f08882c00c8000026d31d12ba946c9864682020e7467a2e013e088037a15007e029c0a2000026d2bec2c994a497e4662048ebc6a82fa15389303c617c09003000ba000026d25eb2cd15049c44902160f386e430c15189043ba18009103040d0000026d20002c394c899c46e2078ecc6a22ee144089838816d08d83040d6000026d1a462b3944095444e1f90e306702e4140088838a16608882c80ba000026d14952a593b893a4451f68e7c67a2de140088438a16708602a40a4000026d0ec52b5943096844f1f38e4c6642d6141888c38016608582ac0a2000026d09002b9145897c45a1f90e4c6522cd137088038216408902d40b2000026d03232b414689604592010e886982f614a08e03aa18108f82f80ca000026cfd352ca14f49d248821b8f706ea304152090c3c618c09402f80bc000026cf7762b694589764602020eb869c2f414d88c83b217f09082d00ac000026cf1882c814c099a46d2078ea86a62ed14588a839617408882e80b4000026ceb902d215489e449321b0f3c6e631215b895c3ee194097832c0c8000026ce5832d195209c648720e8f206dc30715689143c218509303180d6000026cdfab2bf148c9844602070ee46ae2f914a08bc3b217208d02f40c0000026cd9e22b2941094a4511fb8e746882ec14708a839e16808882f40ca000026cd4132b514489644511f58e3066c2d0138886839216808982dc0ce000026cce192cb14f49cc4802118f046d230414f88e03ba18508f82e40c6000026cc83e2c314cc9b447a2080ebc69c2ee14c08fc3d418008e02ec0a4000026cc2272dc15689e649221c0f446e031015609503e219309203140c6000026cbc3e2bf147499046b20a0ecc69e2f3145087839c17008982ec0be000026cb6522c994bc99246b2090ee06b82fc14b88cc3be17a08b02e40be000026cb0842ba947098646d2088ebc6982ee142889438616a08182cc0b6000026caaac2bf145498a4611fd8e806822e314908cc3a817808d83040ba000)) else (if i < 405 then (if i < 404 then 0x26f92a62c494c89ae46f2070e9469e2eb14a89043b017308a03000ba000026f8cb12ca14c09a24682088ed46ae2f714f89043c2184099834c0da000026f86b72ce94f49c44882108ef06c02f714c88c039e17b09003140ce000026f80fd2b114149644531f70e786962e914208b03b018208f02e00b6000026f7b5e2a493d09364391f08e3064c2ce139887c38a16f08602e80b4000026f75612d315189ca4812128f1c6da30715408f43ca17f08d02f40c4000026f6f892c1148c98e4612028ebc6a82fb14508a43a817708c82f80b4000026f69ac2b9947098246a2090ed86b02ef14a08cc3b818008d82e00bc000026f63c92be146496645d2048ec868c2eb147089038816208682e80b2000026f5df02be14849784672068eb06a02ea14708e439616b08702b00c4000026f582b2b6142496a4541fd0e6066a2ed14b08c43c618308d82f40d0000026f525c2bb143c95e4461f58e406602d813f88d03b417609003080be000026f4c852bf14909944602070eb46902e714708cc3b017609002c00ae000026f469f2bf948898c4732048e9069a2e914388b439817308982ec0a6000026f40a92c1148c97645a2010e6c6842e9142089439e16e08682c00b2000026f3aa32d9152c9d44872128f086da30515088f03be17c09303200be000026f34e12ad940c93a44a1fb8e706762d9141888838c16f08c02d00c4000026f2f012bc14709704521f98e546762e314388ac39a16e08902c80c2000026f29202c294b89a247e20e8ed46aa2ef14908c83ac17c08882d40b4000026f23482c094a497c4622078eb469e2f014488e03c018309002e80b6000026f1d2e2df157ca0a49521a8f2c6d831215809203d418a09582fc0ca000026f171a2db95449e24932188f246da30515008e43b017708c02f00c2000026f112a2c794e09aa47520f8efc6a62f114888bc38416108602d40a6000026f0b3c2c994c09a647a2138f346c830b15489383d018a09603300d4000026f057d2b1943095c44b1f88e4c6662da13b887437a16108402cc0c8000026eff9f2bd148898846c2090efc6b42f614c89003a216508502c00b4000026ef9df2b614109424471f70e4c6722e413d086838016308a02dc0c2000026ef41a2ae94049324421f88e0c64e2c7139881c34815608202a40a2000026eee412bb948497a4602038e986ae2f614c090c3b818409203000c8000026ee87d2b4144095c4481f98e3c67a2ea13f887c38016608082b00a0000026ee2af2b194089504541f98e5868c2ec14808c43b617c09083080c0000026edcd62c014a89844702060ec06a22f114d09003c617d08b02f00ae000026ed7172b014049424591fa8e786942e214308bc3be18208f02fc0b6000026ed14d2ba94609784561ff8e5c6842e5142089838e16108602c00b8000026ecb7d2bb94689724542038eb869e30115108f83b217108d82cc0b6000026ec5db2a893c890e4331f30e3466a2df13d086437c16208782d00a6000026ebffa2c2944c97845c1fc0e686862ea14508ac39817208982e00c4000026eba2e2b9944c96645e2020ea46a82f714b08e83a017b08983040c6000026eb4242d115009ca4842108ef06b62fc14e08f03d217809203080cc000026eae552b7944c9644561fa0e546702d913e888839016b08a02f80c2000026ea8812b294649864692078ed46bc30714e88f03ba17708e82e80be000026ea2a32bc94749704562090ee46aa2ff14c88d03bc17b08e83040c8000026e9cc12c0146897245e1ff0e9c67a2d3139086037c15b08602b409e000026e96d72c494c49a44812130f106bc2fe15108f03b017008a02e40c2000026e90e92c694c899646b2040ea46aa30114f88f83bc18809683140ba000026e8adf2d215109c247e2140ef46b82ff15088fc3c817d08f82fc0b2000026e850c2be947497a45f2060ea868e2eb14608c839616d08982ec0be000026e7f5b2ae13f09584561fd0eb06bc2f814d890c3c017d09183240ca000026e79862bc947497445a1fc0e506722e714708d43b617108982d80bc000026e738b2d294e89c247a20c8eec6ce30a15689083c817c08e830c0cc000026e6da92c4948c98a46d2028ed06ca30914f09103b217c09102f40c2000026e67ea2af93ec93643f1f58e3c6702ea14888d43bc17a091030c0d0000026e621f2b5944095444b1f78e346582d514008ac3ac17c09082ec0b2000026e5c3a2c0949c97e47120d0ef06a42f214208bc39e16f08b82cc0c4000026e56662b794689784551fa8e5c6662d7138087437216108402cc0bc000026e50792c614b49964601fd0e6067e2d713e088439c16a08c82bc0ae000026e4a892c314b09a44772080ed46b430415309303d618608e82e80b0000026e44aa2be149899c4742108f306e031015989283c818109403140b8000026e3eae2d995449ce47820c8ed06b82f914b88ec3c218509383280c4000026e38dd2b9947098847320c0ebc68e2ef14488cc3ae17808c02ec0c0000026e332e2a593c09264371ef0dd861e2b412c082835e15007f02a8094000026e2d692ba14549724591f80e586642d813b088839617108082a80b4000026e27982bc145c98045f2030e9869e2f014788d43c618809402e00bc000026e219a2c814c499046c2088e9869e2eb13f886438216c08902c00ac000 else 0x27108d32c1946098045e1ff8e8c6842e414388a439816d08282bc0c60000271030e2b4140093443d1f08e0c6562ce139889438c16808782cc0c40000270fd412bd944496e4531fc8e646782dd13f086c37c16208f03140ba0000270f77f2b5142495844a1f28e706782da13a88843a416c08b030c0d00000270f17f2d515209d84902180f446dc31115b097c3fc19009003040be0000270ebac2ba94809764642018e906822d813d088437416608482bc0a60000270e5da2bc146095e4581ff0ea068c2ea14408ac39616f08b02f40ba0000270dffb2bb946497a4661fd8e7466e2db13e089038c16c08082a40a80000270da292b894449664551fd8e806962ec14508983a016f08602dc0c20000270d43a2c794f09a447820c0eec6ae2fa14c08ec3c218408f83080b20000270ce692b894449724652088eb86962f414c88e83ae17708b02b80b80000270c8a72b594189544511fd8e406662e414108b439217608e03180c20000270c2b92c814d09b447c2110f1c6e030815589383de18e094833c0c00000270bcde2be94889a84682090e9c6942df142886c38616608d02ec0c20000270b6e82cc95149cc47b2100f2c6cc30014c88d43c417808c83200d40000270b0f22c814c099a46c2058ea46862e013f889839616b08502dc0aa0000270ab3f2ab13f494a4551fa0e906922e014488b03b817d08d02e40b80000270a5432cd14b09a847620f8efc6c82fe14f89083c418909003140b800002709f892ac93fc9584451f88e586622db13e884836a15d08002940bc000027099ba2b9947499847620d8ee46aa2f214608b039417808c82ec0bc000027094082af13ec93c4381f20e1466c2d3143089839417208f82e40b600002708e3b2b9149898e4662048ec06bc2f914f08fc3a416a08a030c0b80000270884c2c494b09aa48120b8f1c6e430f15a89303ce17c08a02dc0aa0000270825d2c214a899246320a8ed06a82f914f09083ac17608902e80ba00002707c832ba14889904692080eac6902ea14608b43a417c08e82e80be000027076ae2b9945c96c4592000e7869e30014988c43ac18008d83080be000027070af2d015089b247920f0ee46aa2f414c09183ca19509f03780c800002706aee2b6945c9744672020eb06982eb14508bc39c16b08482c00b0000027064f52cf15089b447320d8ee86ae2f814a08e43b818809303200c400002705f082d094e49b447820b0ec46b42f714f88f83b817e09082e40b2000027059322b3143895c45b2028e906922f714e08f839a16a08282c40bc000027053452c794b49c647d20c0edc6982f714788b839e17908782c009a00002704d742b7945898846b2060e9468a2df14588a43a016a08782cc0a4000027047a82ba146897a4642030e986842e3141087439416d08902f80ce000027041cc2c1147496e4612010ea86a42f514508d43aa17908782e40b200002703bf62c094c49944672080ebc6ae30114a88e03b417a09082fc0c40000270364e2aa14009404421f58e586702e814588a439017108402b80b60000270305c2ca150c9c447c20c0ec469e2f214808a438015f07f82a80ae00002702a732c514a898e46c20a0ed46942f514d88bc3ba18009582f80cc0000270244c2e595709ec49221a0f206c830314c89043b8187092031c0c600002701e7a2bc949c9924692020eb069c2e914488a439e16e08802a4098000027018792cd95049c648d2168f546e030d15509203de19309a033c0d00000270129c2c0149c9a646b2060eb86962e313e88c83b817808b02c80c200002700cb72c694d89a64702040e906882e713f88a43a217008802bc0ae0000270070b2a393c491242e1eb8dc061a2c2138087839817008982e00bc000027001412b894549684511fa8e686702e114408b03a016e08902e80c0000026ffb7a2b714389484491fc0ea86982f614d88d43ac17808902b80a6000026ff5d02a113b492643e1f10e0064c2cf134084836c16008b02e40b0000026ff0052b9144898c4652038e646722de143089c39e16f08b030c0b8000026fea4e2b1140c96e4511f88e7068a2e914908c43aa17308902d80ac000026fe4782ba14409764591fa8e7c6762d9145089c38c16908802c80b2000026fde662d515209de48d2118f3c6da30d15409303de19809703500d0000026fd89f2b8142496045d2020e8c68e2eb14908e83d618c09402fc0b8000026fd2f62a713f09504491f78e3065a2cb138084c38016408382c40a4000026fcd0d2c314c89a446d2070ec46a42ef14188c03a217308d82e40b8000026fc74d2b314009664692060e946922e014288b438016a08202c0096000026fc17a2c114a099446f20a0ed86b22f114a88e83aa17808602e00b6000026fbbb42b6943c9664581f88e4c6762d6145086438816a08902c00a0000026fb5d82bb146c97e4682048ebc6ae2fe15208ec3b617d08d02f80cc000026fb0032b8147097e46f2058e886842e514308a83a417608f831c0c4000026faa212c514a89a246d20b0ecc6a22e713e88cc3a417e090833c0d0000026fa4442c0947098c46b2090ee86c230415488fc3ba18009002f40d4000026f9e582c594ac9a246b20c8ee86cc30614d89083de18a09183300b8000026f98872b9947c9904702020e9c6902ea147889c3a417308e82f00be000) else (if i < 406 then 0x27280a22cb94c499646a2088ef86ba2fd15008f03ae17808b82f40bc00002727abc2c1948c98646c2080ea869e2eb143089c39a16508902ec0c2000027275092b2941c9624491f48e486762e713b086c38416d08402a40aa00002726f312bc949498c4712060eac6902f414908ac3a617108882d40b40000272695a2b9144096e4672078edc6a02f6141889039e16f08902e80c6000027263662c814fc9b047f2128ee46b62f814d08f43a617508e83100d200002725da82ae13e892242d1ec8e3866a2d113a083c37015908082bc0b6000027257b32cb14b098646a2058e8c69a2ec14908b839e16b08d830c0a4000027251e82b7945497045d1fe0e746702d613f88a83a017f09002e80ba00002724c082bf947c9804561fe8e586722e5144889439817009002fc0c2000027246372b7944c9884632010e7c6822e414488bc3a016f08702c40a00000272405b2c214ac99e46b2098ef86c831115409083d818a09583040ba00002723a512d595049bc47620f8f146da30915509143c818e09303280ca000027234602cd94f49cc48b2140f206c230314d89243c017a08e02ec0b000002722e8c2ba944096c4632058e806982ea144889c3aa18809103080ba0000272289e2ca14c09924661ff8eb06922ea14608bc3ba18109182e80c2000027222b12cb94c89a647820e8eec6d430f15609303da18809b834c0e200002721cde2c114bc9964672080edc6a42f214b08dc3a017108c83180cc000027217252ac93e892c4331ef8e106722df140888c39416e08902ac09e000027211362c994d89b247c2078ef86a02eb144888c39017208902e00cc00002720b242d895449ee49b21c0f6c6d630814f89183cc18809103200c8000027205762a713c09324391f60e6468a2e0142889839416b08982dc0bc0000271ff912c5148899446f20e0f286b62fc15508e83c6179094031c0d00000271f9cf2b4141895c45e1ff8ec06962fa14a08dc3a216e08382d40ba0000271f3ea2c094809704682048eac69a2f615188fc39e17908f82f80b00000271ee022c614ac9904612050ebc6b82fc14e09043ba18a09a83680b60000271e8312b9944496a4571fd8e806922f214908ec3b817b08b82e40b20000271e2472c214bc9a04612028e9c68c2ea143089038e16d08602dc0c00000271dc782b8146096c4592000e7c6962de13a885437416808202ac0ae0000271d6692d815349e448f2178f546de31915d896c3fc19209403140dc0000271d08c2c1948897a4622028e8c68c2f314f89203bc17f09603480ca0000271caca2b5946897a45a1fe8e686702d9144089839416a08782b80be0000271c4e82c494849964642068ed46bc30514f08dc3a817c08f03140c60000271bf012c514ac99e46f2098ed86c02fe154893c3ea19709803280be0000271b9282be94a49984702078ecc6a02f014488d83ae17208682f40b20000271b33c2c214a49944671fc8e7868e2dd13e08a038416f08502c80960000271ad7b2b2946898e4602028eb46962e914608b83a217e08f82ec0ba0000271a75b2df1574a0449921d0f446d830e15809403f019209282e00c20000271a1592d114f49c848e2178f186dc2fe14b88e43a017908b02e80c400002719b882b714409804591fe8e886b02f814c08c439c17408c02f00b20000271959b2c614a499046e2068eb46b02fc15209283b818308a82d00be00002718fdb2b3942494c4501fd8e706842e614408ac39e16d08982d80c000002718a0f2ba944c9744612068e9068a2e314788c03a617b08f03240b8000027184112cc14f89a846f2040eac6942f114888d03bc18109383180ba00002717e312c894bc98c46c2030ea068c2ed14b08b83a817a08e83040c0000027178352cc95289b247920d8ecc6b02fb14608c439017108c82f40be000027172682b494349604612070ea06942e214088a03a417e09003200bc00002716c952b8941895c44c1f38e446722df13f08ac3ae17108882f40ba0000271668a2d495509e048b2120f1c6c830415108dc3ae17f08e82e80aa000027160922d514e099447d2150f106c02fb15509243da18b09002f40c000002715ac62b6143c9704541fe0e8c6882ea14588c03a616808302dc0b2000027155032b1944495644d1fa0e6069a2f514908d039016c08182c00b400002714f0f2cd14f499447120d8efc6b030214a08d43aa17408882cc09c000027149372bd946497a4662048eb46bc30315009083bc18809a03640de0000271436f2b7947498a4642020e906902e814b08c83b418309403000b800002713d942c3147c9844652020eb06a62f314408a439617408f82f00b8000027137c12b9147096e4612028e846962e513d886836c16c08882e80ca000027131d82bf147496444f1fd8e6867c2e014208d83b617808d82f40b200002712c162a993e09324311ed0df86582d613b884c36a15f08302a80ae000027126312c514789904652018eac68a2e414408ac3b617e08f82f80b40000271202d2d115009d249221f0f4c6e0307156094c3d418b094031c0ce00002711a392ca94c898e4642088ec86a82fd14c88f83c4182093031c0d8000027114542c614b898c4691fd8e786942e214488983a417d09202d00ba00002710eab2a713cc94c4471f78e5467a2e414308983a416d08c02f40b8000 else 0x273d35900000000000002078e9069a2ef14d09283c218809102ec0b80000273cd7d2c194b49ac4722090ef86ca30715189343c818d09883300c80000273c7bf2af93ec93a4481f10e006562cf13d886838616908582b40c60000273c2002b994a898e4602030ea067e2e914788cc3b018208e02d80c00000273bc472a913f495044c1f80e5c68c2f214808b03a617308a02f40b20000273b6512cd94dc9bc4802100f006c830014c88d43b217e09483200c60000273b08e2b1141894c4461ee8ddc64a2c5139885038816008582f00ae0000273aaaf2bf94809824581f78e506662d913f088039816e08582e40b00000273a49e2d215149c047520f8f006c22f714f08e43a817909083100d000002739ed82b2142897a4612070ecc6a02fc14788a838616f08882dc0c4000027398fc2c2149c9b047420d0ed06a22f114608d03ac17409003000c80000273930a2cf14fc9b847b2120f386d230615989543e618d09102fc0c000002738d3c2b314289824652060ed46b62f814808c43b817e09102f40bc0000273876e2b8144c9664592028e906a62ee14588b83ae17508c03080be000027381ac2b3145895e4511f60e3865e2d613a887c39617708a82f00b800002737bc52c194a097a4591fc8e6467c2de14408c03a616f08e83000a60000273760c2b3943897244b1f78e386722e314208c83ac17908902b00b40000273706d2a093749044271e28d886102ac128082036e16407f02d40ae00002736a672d094f899845b1fd8ea86882eb146089c3b218609483080c4000027364bc2a913dc94a44d1fc0e6c6862f414a08e83c217d09182f00d200002735f162aa13f09484491f48e386622db14088b439616e08702cc0cc000027359512b1943495644f1f80e5c6682e414788b43a017908902dc0b4000027353842b814709744581ff8e6066a2d614088a839a16c08982f40bc00002734dba2b294049404501fe0e686702dc13e087c38416608b82e00b6000027347f82b213d893a4431f80e4c6602da142889c39e17408c03040b80000273422d2b994449464471f38e406662d413a887037a16908502c80aa00002733c492c4147c98a46a2070eac69a2e814188bc3a817a08c02e40c00000273365e2c714d09b447320e0f2c6c630315289343dc18509583000d0000027330992b5144095e4551fd8e6066a2e0144088838e16608002940ae00002732aaf2c794c89ac47d20b8eec6c02f614e88f83d218f093032c0e4000027324c82bf94749704622010e846882ea14a88d43a417709083180d000002731f142a793c89344241e50db863c2bf137084c36815908602e009e000027319472bd149098246b2030e9469e2f614909003d0187095830c0ce000027313802b113fc94843f1f50e4065e2d814108bc3aa17408c82fc0bc00002730dc72aa94049324421f00df86402c0132083037c15b08182d80ba000027308042b2141895a4501f58e5067a2da148089438017308f82e40ca000027302252bf146098e46c2090ec86a22fb15088f43c818b09582fc0cc0000272fc6c2b5140895044c1fb8e2866a2d313f887438c16608802bc0b40000272f6b02b093ec94e4451f80e6866c2d0138085837216008082a80a00000272f0e82b3142095c44c1f60e6c67e2e614408b83ac17c08f030c0bc0000272eb172b5944096c4511ff8e8067a2e9141887838016b08a02f80bc0000272e5002da95689e24942190f6c6fc31a15b89603f019309403100b80000272df072ca94d499a46d20a8ef86be2fe15209203c418209283140c20000272d94d2b0142494c4401f50e7c68c2e915088f03b417c08c82e80c00000272d36e2c314b498a45f2020ea86862ec14488cc3a417708c03140ba0000272cd8d2c2947c98245d1fe0e786802f214e88f03be18308e83000b60000272c7ab2c294c09a64742070edc6c430a15689283e618d09682f40bc0000272c1c72bf146c99846e2098eb469c2f114f89003be17708982dc0b60000272bbde2ca94d49c048c2108f186d830714f090c3bc18208d82e40b40000272b5e72d1150c9ba47a2088edc6ac2f914a88ec3ae17508682bc0a40000272b0152ba14749764652068e986a42ef14a88cc3aa17708c82ec0b40000272aa612ac94089504571fa8e7866e2d013c883435c15d08382b40b40000272a4772c794bc9a647f2150f286d631215a09403d818b092031c0c800002729e822c814e09d247b2058ee86b82f215089203d018a09483180cc0000272989d2c1148c98c46e2070eb86ac2f314808d439616808982c00b8000027292a82ce95149bc47b2098ed86ac30615609403d018809302fc0ba00002728c9f2d195309d249721a8f806f831315488f43c818209103440ce0000272868c2dd15709fc49c21d8f586f630f15489203bc183098032c0c6000)))))))))

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



private theorem b403544 : covered 403544 403646 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b403646 : covered 403646 403747 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b403747 : covered 403747 403849 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b403849 : covered 403849 403950 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b403950 : covered 403950 404052 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b404052 : covered 404052 404153 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b404153 : covered 404153 404255 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b404255 : covered 404255 404357 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b404357 : covered 404357 404459 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b404459 : covered 404459 404560 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b404560 : covered 404560 404662 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b404662 : covered 404662 404764 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b404764 : covered 404764 404866 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b404866 : covered 404866 404967 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b404967 : covered 404967 405069 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b405069 : covered 405069 405171 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b405171 : covered 405171 405273 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b405273 : covered 405273 405374 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b405374 : covered 405374 405476 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b405476 : covered 405476 405578 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b405578 : covered 405578 405680 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b405680 : covered 405680 405781 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b405781 : covered 405781 405883 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b405883 : covered 405883 405985 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b405985 : covered 405985 406087 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b406087 : covered 406087 406188 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b406188 : covered 406188 406290 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b406290 : covered 406290 406392 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b406392 : covered 406392 406494 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b406494 : covered 406494 406595 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b406595 : covered 406595 406697 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b406697 : covered 406697 406799 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b406799 : covered 406799 406901 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b406901 : covered 406901 407002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b407002 : covered 407002 407104 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b407104 : covered 407104 407205 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b407205 : covered 407205 407307 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b407307 : covered 407307 407408 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b407408 : covered 407408 407510 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b407510 : covered 407510 407612 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b407612 : covered 407612 407714 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b407714 : covered 407714 407815 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b407815 : covered 407815 407917 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b407917 : covered 407917 408019 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b408019 : covered 408019 408121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b408121 : covered 408121 408222 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b408222 : covered 408222 408324 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b408324 : covered 408324 408426 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b408426 : covered 408426 408528 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b408528 : covered 408528 408629 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b408629 : covered 408629 408731 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b408731 : covered 408731 408833 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b408833 : covered 408833 408935 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b408935 : covered 408935 409036 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b409036 : covered 409036 409138 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b409138 : covered 409138 409240 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b409240 : covered 409240 409342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b409342 : covered 409342 409443 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b409443 : covered 409443 409545 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b409545 : covered 409545 409647 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b409647 : covered 409647 409749 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b409749 : covered 409749 409850 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b409850 : covered 409850 409952 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b409952 : covered 409952 410054 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b410054 : covered 410054 410156 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b410156 : covered 410156 410257 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b410257 : covered 410257 410359 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b410359 : covered 410359 410460 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b410460 : covered 410460 410562 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b410562 : covered 410562 410663 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b410663 : covered 410663 410765 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b410765 : covered 410765 410867 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b410867 : covered 410867 410969 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b410969 : covered 410969 411070 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b411070 : covered 411070 411172 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b411172 : covered 411172 411274 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b411274 : covered 411274 411376 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b411376 : covered 411376 411477 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b411477 : covered 411477 411579 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b411579 : covered 411579 411681 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b411681 : covered 411681 411783 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b411783 : covered 411783 411884 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b411884 : covered 411884 411986 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b411986 : covered 411986 412088 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b412088 : covered 412088 412190 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b412190 : covered 412190 412291 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b412291 : covered 412291 412393 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b412393 : covered 412393 412495 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b412495 : covered 412495 412597 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b412597 : covered 412597 412698 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b412698 : covered 412698 412800 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b412800 : covered 412800 412902 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b412902 : covered 412902 413004 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b413004 : covered 413004 413105 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b413105 : covered 413105 413207 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b413207 : covered 413207 413309 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b413309 : covered 413309 413411 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b413411 : covered 413411 413512 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b413512 : covered 413512 413614 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b413614 : covered 413614 413716 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b413716 : covered 413716 413818 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b413818 : covered 413818 413919 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b413919 : covered 413919 414021 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b414021 : covered 414021 414123 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b414123 : covered 414123 414225 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b414225 : covered 414225 414326 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b414326 : covered 414326 414428 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b414428 : covered 414428 414530 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b414530 : covered 414530 414632 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b414632 : covered 414632 414733 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b414733 : covered 414733 414835 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b414835 : covered 414835 414937 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b414937 : covered 414937 415039 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b415039 : covered 415039 415140 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b415140 : covered 415140 415242 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b415242 : covered 415242 415344 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b415344 : covered 415344 415446 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b415446 : covered 415446 415547 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b415547 : covered 415547 415649 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b415649 : covered 415649 415751 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b415751 : covered 415751 415853 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b415853 : covered 415853 415954 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b415954 : covered 415954 416056 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b416056 : covered 416056 416158 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b416158 : covered 416158 416260 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b416260 : covered 416260 416361 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b416361 : covered 416361 416463 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b416463 : covered 416463 416565 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b416565 : covered 416565 416667 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 403544 416667 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b403544 b403646) (joinCoverage b403747 b403849)) (joinCoverage (joinCoverage b403950 b404052) (joinCoverage b404153 b404255))) (joinCoverage (joinCoverage (joinCoverage b404357 b404459) (joinCoverage b404560 b404662)) (joinCoverage (joinCoverage b404764 b404866) (joinCoverage b404967 b405069)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b405171 b405273) (joinCoverage b405374 b405476)) (joinCoverage (joinCoverage b405578 b405680) (joinCoverage b405781 b405883))) (joinCoverage (joinCoverage (joinCoverage b405985 b406087) (joinCoverage b406188 b406290)) (joinCoverage (joinCoverage b406392 b406494) (joinCoverage b406595 b406697))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b406799 b406901) (joinCoverage b407002 b407104)) (joinCoverage (joinCoverage b407205 b407307) (joinCoverage b407408 b407510))) (joinCoverage (joinCoverage (joinCoverage b407612 b407714) (joinCoverage b407815 b407917)) (joinCoverage (joinCoverage b408019 b408121) (joinCoverage b408222 b408324)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b408426 b408528) (joinCoverage b408629 b408731)) (joinCoverage (joinCoverage b408833 b408935) (joinCoverage b409036 b409138))) (joinCoverage (joinCoverage (joinCoverage b409240 b409342) (joinCoverage b409443 b409545)) (joinCoverage (joinCoverage b409647 b409749) (joinCoverage b409850 b409952)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b410054 b410156) (joinCoverage b410257 b410359)) (joinCoverage (joinCoverage b410460 b410562) (joinCoverage b410663 b410765))) (joinCoverage (joinCoverage (joinCoverage b410867 b410969) (joinCoverage b411070 b411172)) (joinCoverage (joinCoverage b411274 b411376) (joinCoverage b411477 b411579)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b411681 b411783) (joinCoverage b411884 b411986)) (joinCoverage (joinCoverage b412088 b412190) (joinCoverage b412291 b412393))) (joinCoverage (joinCoverage (joinCoverage b412495 b412597) (joinCoverage b412698 b412800)) (joinCoverage (joinCoverage b412902 b413004) (joinCoverage b413105 b413207))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b413309 b413411) (joinCoverage b413512 b413614)) (joinCoverage (joinCoverage b413716 b413818) (joinCoverage b413919 b414021))) (joinCoverage (joinCoverage (joinCoverage b414123 b414225) (joinCoverage b414326 b414428)) (joinCoverage (joinCoverage b414530 b414632) (joinCoverage b414733 b414835)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b414937 b415039) (joinCoverage b415140 b415242)) (joinCoverage (joinCoverage b415344 b415446) (joinCoverage b415547 b415649))) (joinCoverage (joinCoverage (joinCoverage b415751 b415853) (joinCoverage b415954 b416056)) (joinCoverage (joinCoverage b416158 b416260) (joinCoverage b416361 (joinCoverage b416463 b416565))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 403544 ≤ index 775000000/512 := by decide +kernel
private theorem starting_value : fast 775000000=39925351 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 775000000=39925351) (n : ℕ) (low : 775000000≤n) (bound : n≤800000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=775000000
    · rw [first,anchor]
      exact starting_value
    · have past : 775000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤800000000 by omega)
        have within : index n / 512 < 416667 := by omega
        have lower : index 775000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤800000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ775000000To800000000
