import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ800000000To825000000

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




private def radical : ℕ := 0x145ec32fdd57968d7f6fdc3ba9a86ca3cef52d123ee8eae2b0a24d1f45abb89a11f5298d505c08c997f1bb48d5b415ee38c0371b2401c390a3a1f655ebb48b58db4797203299d1c4e9127c41dcbf21003f2a97578e7501a435e85150dec230b0468f820705892ed221d9e6f0a142a25e9e03efdd8a211c82aac20536a9cd6a4abbf727d53a52eb52502e65248515439220700ac808704e46551837ba5f502948aa94debbaf771dc2d9d906cfd535eb585e15bb3bc98e44b719e73a57aa7789da55c18bf213eaa717bf0a580dafc9885fdb00c0d7849d7610df72735f4e34303b3ff0e4cc21994c347baacb1a7edd3608698d9f34859fbc502440183ae75694d9f45c3a40f875262d270bd46625d5824a83dea9c47be53ef7d542ba44231c240f0aebe741cf1d6d5667213773c61f2a17438e6e21cfc16dd505195a7fe5ab578f93d84df12488cbb8c069a26c3fa49ad33682748f130fd84db04b66b383a85dfbc90b09efdc1628a53dbb14af24a8df7f362b2c9163d2c8db28c4c5f19c0aa613a944b04ef7aef92f7ec2accd28f1323ebd4e16834f59cd34276d5e4461ba9bc5e5aa6fa996f06bb4e8252a846ae33b6f66a5d6b80219cde635a1c19ab98c6aafca53138ce1340078124cc095253fc769b3b6d580e93c94eaba5317beac462b500d0dc652d617c32b94b382ab4fd23433dba7409de7f2616f54a24adf62008052f6f319fb86cdaa1ab3c8f1d0eaffa1772bd283594de0a165439bf8e7710856ebeff499d766b6132a3ffd6e0996a448b33eed641e8fc966d6128823dabc8e4236901ca57b7089937dfea73418b75ae04fcaf1033b72d6bf0e11b5d41210437bb3e00375bff6b2634212b70dd12f2d6ee72343159e305a3b2139792bdfd6bf5ec609ac3303dec0453eb199142d79a9208d632ddc806cc1bf220eaf64fc29b9fba44aa22f617f2fcc672da0ab0dbb3c73d35f3596d26aff35d520d31dd241ddda16bc0a657b61fdf0ca448c3d7cbf8e7824c1c99a05363c70e507a621484bc02fb2caf5af72d5aabbb5d54e468740623f49dd5c8b9d0f8d8e784cdd4809d6bd21621bb06c0d80c824ca307077d532d436da6f76edd9575841483eb40d898dc9dfaa6480458a7ee2c670854434734b177a035d9e70279c71ae1df1e495c8b54e23e0af33211b14fea9a5d7ee15934eca2559e683c1e46f611a2acc6cacdf3c8749aa1e0ae83975d5d39e404b5c690bcc6df944dbf7452857681843c83e09b4a4303ae5ad035fcb64fbb79559466a1bfbfb5a7e3012c65ef5e1a3296e18fca287a4123e9ef09e66a51018427ff197b184d24ae35a28f478dac4933d54f6167eea7f7fad1fd78bc3fe02f6e497e44e1d1760140393552923751867a93ec2d183b00e1b3c6761b708c42f6d03928f32bac6b065e63a2b398569202819071b2a15ccb43c611083e941b61398ecd747698fcba87d54d26eddb7b52a02980668cadc0431afb69e787cc6a745c369f4dc2e26c2b4d16d13f857013ac94e2b3c17a54a07917ab7ebb6703cccad75d60079b7747d17db00d668f95cb1bb961e25851ca3fc7da6863a4eb4d8259a6a0d911dd338694fb4b6e490349afd8db8b5e57287b308a5a8ba7b028f575be3d223f3987620430fffbb80f87a79d6f9333a52e3dfe56c94db43e07231dba8205bf5c0a90904cb89173af1b52e0e8d9388dbc8c24145c0ccbe0ce26a067985e8614d81b524569ccf3f8ee181c3bd851029801af0240cfd5b90a4a2dcb0aab51188a71e0c9f5df3f9748e006dd0ad20289cc13a5f6de8bee0619f538eea19ad0811351dcdf157d0c4d478bb56b1ef08ddf68a4b75f7c935e91ce7e42d68996c68c72e8719dc549057141cd317736d5ebd31b52dea2b30ae6c97f8f1f31bc6d3b2c9e4f25b047bb0f5d5e3fb2a8f82a879a7699418ba18ab73fe31066f967b18aeb8a959663b1bb9f504638e267e9c1de045357e4e3b93ebed73191b6112ef2cf8463ea48f5ebe84355902d19edab538a02efd67d3af22a567bf9048251842767ed810dba0f6d3f969cd484921bca7ff1e69917dafe7e2e11feddcb10ce88a69dd37ab0f872fc8697d8517475eb86da97dfa4c48e5ce2615a011128c04e30534a91578ff9da252305d8ae3d3956f0508064506eb90c04b52974c6f8a9a3a654b6d2aa1d0e4d49daf8ee6c17df87ed769a0bdfa623616aecb469321ae484d77e79c621687895ed81c9dbe546bf0a2c32fa3427b272fb1315e86cfb9b0997f7768e34f6b7dfe592fbd7a7238fb2c2efe83ab39039abb30731430531b16299cfd9ab46aa3d82d0838973ffe27a4ade6fc944a35fb7af986b6532911a002bf277947f2a0de6aa2f0eb572e7a25d3fc652b319bc1930cd9589c08a573d2f4efa9a5680937677772221548e5bfb87a9e8dde9eaec80820d61e53c60bf22b45ba91c72c7670de316a8cb082c290c0a3ab4bef93abc328870e5a79234d6cc753e9dde09b9e5dc234d23ddabfab0c1c1b1809c37e92a4ec9a19654f0f01cb4f6cb14f8ac76dc4e46b8be308650b7c57b5785ebe3ea87dc5bd945c6403932fc7e4c02e9bf21af90b9d41b22269612638378f1c38a512d29da7d6a6fc7e2ba85cd835248cf4b1911d5003f3193f0501e2bea79bd3415d396fc8bcfa0c9ab2e05d9f1a8d981b53c1fa4ee426f0c8f36d412fe641e1d49f95138a574bbb0eabd0c17099015e3098e4db468444f0362a44f2c63709192e5ec5b170c9157f6cf2e47cf8a0cae3d97657d6e63193d82581967fde856845da7486234ef3cdb0debc6edab873ef2c4359733cbb09491c8ae6e0a5f1aff29158a3792b77740b3e6b2b18a86930baff89157ee5d2aadaf15d157da5db16c140f5a9dd3d13055224cdd288cdf79ba16a3fba98ab30a11d365f1caa19d7155999ea22fa165be71b766a6c76b9a68fdfc9b3b3449574d18140fd5fed50bb8edd72a99953d9627f5e7dd8aeaedc3c33746309eff52bc16c8f1c3606074ff55b3b4b973ca2568256fb29f24a4aa4c9c93d0ed07bcf17311aa6695faebbad3a3afdf71946af8aebe47e71fb2f599a9c5c35965e602e33d282170132d77b2d8d1ae8363b9d5b04ca314b9287ae63caed005fdd840fe93ba16dc8068c3a24626fd4c2668646cb859eb57dbdfcdd675e2dcaa130d24970f87da83fe61e935a6df0cdf1d0fd30ee025d7de3c926b9b37759a42656049ec99b48c47e9bf5baf4f3408b0f3b898da2e86a42db509303274f74f60cbbed06f32d43eae34bd25ef11606705d43dcbdf3eca6ad87397f4b173126c88604f1a7452e96a8a584a82db89e4cc7a8817eae86d29538003381c14c910fe6343cc29b23147526f99e0c2173bc3da7015fb5e2f538cae2a951e0a0c433dba09ffee61a5843fdc32bc5d58d0aa25dbd70043b85eedfb8561d0fa0c47a78014d0532ed9845a7a7a3f4e2551e6b74ef4eb34bd8506ebd5fa04864fa6a3b18ad7aeea783c3888a9842a95248fca576d5500845ec4184068a9f2a29c05203ba0fd1fd8db354d82c3958c03ad48bb8f4bb80145f55f4fe40d8519cb2ffa8173cf6fdd67a4d4eeae61698322762fb31ae79a913496b6f89a37e840f8bb885ca10fc13f20da86bedd23ff2d80f0063bf37b6214f099eb534eadaf3d63602f68cc70bc708ae59e1e6b538632d411e2ab154db3a44a30905eacb1620edd76d985a87cf348c752d55440d0174a55f987cd409aa8d85d408c1a6772825fae18d39d062234905ba1533ac0b814a0e5249618dec3d618758d25dc2ce153c12afc6ce760d36061824bd271a26b5e4219edb5290e984012661d11e7045aa7ed7253abe21df5850e8ea7bb137a5cb1f8a8c175997b434afca2a2c7ee1948ec352980f4a3cc614901a9446941a696d2e3d2d72c5dc3a14f85a26d54c0bf97999053f04a9b8c984eaf01bd8dcd2171ed6107e1f2af5c115c1edd1f046543d9f187c2fb1d4e03cfe53a8d388464bee004b91de9f2d8903760e9bf6c88f31c4b1b302e214e50102ce84dc8c2ed6f1d8c6f74088da5b7e5b57ee554f50808af72cb0489e6ad3eab89e37b2c8b9308a7e3955828116f77366b3240d9d5c87e6629d43e356080fa19c8bb538e19a672dd405635d66e4e109ee220f5e097dd878a7403f1cc6cf637fed4ac591f20861fe86b12097d978e274514aa39e26a830895ee1d30f39d92a3fae28225bfef07707e462717510c03ba01484802411cbaba01a6f86e7e8b7d8176e72ed9075a05839881f4ebcea0d6f46d58a4b1e40b611ada037b2728fee6be7db7e014b2eab97fceed1276659a5c4c7436f7f20b9069d61a281cda4763cdeb04b7365d3f6ea1cf040fd87f3bb2951487eb321c706d1e2392c545cd79b445ffd4eba64de29e0810f4e79491f8564af5ebc811b9e326d97321fbcfcb5423a927909cac032f5ecab8a26a8c0536614767f456951b88b99c245132c16d7e4a1bf0543f623684aa8ddda48b6abcb6f051de94a0946eb36036549073e1422ece6ddbcdcc04c0d1735be98dce40eb8132bb6df4a40e410b290ef66540e510e6781c74fd2ca296e270c7687962623452474d083dbbd49191cb7c2e41ecd07dbc4cc70d0d8e3c64fb4a08a2a012015956d5a9299b341bf3727da70793de92b6ea6ce53b1a93d1eb53885c10b859c785e5228e75eee1b74499774297aa27568e8b2a8796706f9772e4b6d4a7a3e33fc0cf134ed8f125801b6417072ac663d82522532cfbceb1c1b7bad342f4387b54e13ecda7b18ae40af3e607299b2f905bb93b74ad0f3a710f7d5955da735fe33027aae3c2959c5d487cc05a2b208c0fe190015f94ada5d029d73c66dc6454e3435e3bd6b1a9641d1fe4059d9c1ef02fcd7187845361007d642866e96f51602c13284aa7c02d94f56066a7b338d671fdf2b718ef91c13ee130be2459c18e7fccd5f25c369704d44c81af41e8d01e40220afde8c9bb2091774cfd6fb5b6b814ead340696a96d2c3bfda5b1a8238ce070650ad933f71672e0f6c32a7d8e63d8f26882a050897f4432dfacc4915466e4935be351f61bae0b59eda47e39876658a228d4aedee2b63ef3dac6f4ca6abce79370b6efab0ca9ca7ad43c086f78c7b29edacfaaaab37ecea1eff4922e05402b82c63a8bd1fc55a5a79b05cf9315af352024fede188139c560ec7772037998afdf9422b23263e2abf94231f216345287f10ed0cf07b87e4269fa52f1430b3a62aee50af76cdc14c3e3d79c07a53ecc5463b3c26d96a83278f9f5908a2a75f27f708745a0388c0e659040f6ab542d8575b356189b46ceb35330e6c26b436e4d47b2ae69fa25f88b7aa5c4e44eab5663ac3f29a4d2286749ae3d49dafc5a39af199efc110e47556da5c807e10b0cf7075a459a5d58303bc20fb38556b41e5a97c49cddf95032154324eb7a7535c18ddadaac7ffc0acc0b7c8aaa207e404b136cc36b1962c68cc9efd07257676c6eab9875800c838c41fccca383bc976fa6a88e8f23b680089d9b45ccee1639dac186e71afbb680b05f0afc9b8510c48df690d86a9bf00a7d16318e6f0c917356f21eb6aeb6a29a41d2f60e25fb5ebe31b9b6327f2ce848973c83bd2173f4c46a98f2eafcc034e8a5c8412be96d00e9e84c3b79fc3740c3d31df00c2a747de5ad92f6444897f01e3e4e43d173cb989dcae1f8af01326b04f154667c289747fff7217cf03a6dc3a26a7f040d5b55e19c9521f39c55f1d409695c1ee7ac7e4da537c53a9254211f4f0bca4d316435bd4cd775aaa635d41612d991b50d54cc47779ed808f3b1c352e22753d5576c06d74f5d03e82f9c48830631354438c6542b9ade83ec14a93ae2014372cb0851a06ec91ad8b43bbd7b57abd307a14ee488326bd588b7b3ea567bddfa824c017d8ba163b96a944e6dcbf76d5847efd70d65b1968e35db18d4c90b17769c1ea5830512b425f2dc2f97263a89a7fb5dac49c0329a78f3aec51ea903d3d5cac962562ff21aac6e869f52c17463da089cbe32ef675f0c04cdaaf2dc0cf93115f27bbf28718254faeaab473fd55c6e1f962e22dce380a5e579313106e2c87991fd8e6b904cbc9cf73c2a0a857f4f70e745409a866c292571debb905711b490df850f8093909f4e3e414248a8fb01592e1caaa88ae477c869f3f18d02ddc9c93c5873149cf2c4013e1fddcd745c9645c57f1a8ffeea6891caa731566e7d62055e35c3fa522579b80e024968ac94a69724e8290f98f14e8ced82b83763640e330d035c2c1b0b7330cc90a77230294a8816e297ff38da03c498be6487b101fb7c8886848989e2d67a5ff642dd4673d0e54665d9c6d17c20964568548eadebb328e24bc7cc7f223bd2fee46b7136d9209d631536ea5bdcb2cbb4e1fc2f5bd1f450e80f80ce513cecad5fc2cb1c38667bbeaebf455f06d1171d2d942900b7265e9f3fa43dcdf11def7d3da0cd54fcf149bcb319b251acbc10327c35f052031c97d15bf0a2123648214fd14ec9262e57b28ce5adfb030c6cc92ae1bd5c6776d826396a5df8b04f490c503087a8a4f8c64fd6aee88711d9ef3211acce758725e6d4e13232a7b1499e2dc04b369b6fc840766dd96e7f7a80926fbf02289bb9b79f37dfa4436aa2ee046fc56642a383a3e46842ca878c80542978ea7219a86fecfcf54d85e20a56c1622e18d394b72ea845589a0fee2a2c0a4c3a0eb4e578b26ac191a1b7182b5fe0f59732e436f9232828e8cedf0674d1cc8ef46f436b99d29b5830bb9eaa091b6b380bac9e1bb07272a30e9d2c6344e749055c74f45f367789a2c1ab5a7553b18ce55c7fbe278933dd76562ce7a9a33b7650c40beb51aa889028706e66235dba632ae8072d91658c8f695e37817de6eca0bf2cb0e0edda17f2a68e62a800a578cf7027b3397bf96fe409c60691f41c304240dd8d8756d78487151a6fb05f02db38ba0d76cec2a91baa03d96d7650ad1a4de360495e0cd7892943a7e8a3004576424c612d339686ef4ba00b56da0053d04d13f22fd8c557d58d5532dfb1f572b7cb8e93d6aa4ace1a68128995e2f816447c10dbe6542e324894ee2b2efb59a319ab5fa65b0d4a6dc96b7050763b226ab5b378b1819f56cc4d09170a79291c0f3cc25f00717bf131ac6732ac182d042c1dc0639e93daa126d6fa99d6bb44821d3974000b4e6f233d3284e130a92964cf35f1f607eaf484bab0884f3b74ec51832d458f9fcf08ca9dab51468aaa7efcf323dfdd7470f757eff6acf2b543fe2dbc7d62429763e001f3728648c5b5a

private def light (n : ℕ) : Bool :=
  if n≤169 then decide n.Prime else n.gcd 42690680090047052749392518888995665380688186360567361038491634111179775549421800928543239701427161526538182301399050122215682485679075017796052357489455946484708413412107621199803603527401512378815048789750405684196703601544535852628274771797464002689372589486243840000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤28722) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 169 = 42690680090047052749392518888995665380688186360567361038491634111179775549421800928543239701427161526538182301399050122215682485679075017796052357489455946484708413412107621199803603527401512378815048789750405684196703601544535852628274771797464002689372589486243840000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 169 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤28722 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 56 := by unfold smallValid; decide +kernel

private theorem sp56 : smallValid 56 56 := by unfold smallValid; decide +kernel

private theorem sp112 : smallValid 112 56 := by unfold smallValid; decide +kernel

private theorem sp168 : smallValid 168 56 := by unfold smallValid; decide +kernel

private theorem sp224 : smallValid 224 56 := by unfold smallValid; decide +kernel

private theorem sp280 : smallValid 280 56 := by unfold smallValid; decide +kernel

private theorem sp336 : smallValid 336 56 := by unfold smallValid; decide +kernel

private theorem sp392 : smallValid 392 56 := by unfold smallValid; decide +kernel

private theorem sp448 : smallValid 448 56 := by unfold smallValid; decide +kernel

private theorem sp504 : smallValid 504 56 := by unfold smallValid; decide +kernel

private theorem sp560 : smallValid 560 56 := by unfold smallValid; decide +kernel

private theorem sp616 : smallValid 616 56 := by unfold smallValid; decide +kernel

private theorem sp672 : smallValid 672 56 := by unfold smallValid; decide +kernel

private theorem sp728 : smallValid 728 56 := by unfold smallValid; decide +kernel

private theorem sp784 : smallValid 784 56 := by unfold smallValid; decide +kernel

private theorem sp840 : smallValid 840 57 := by unfold smallValid; decide +kernel

private theorem sp897 : smallValid 897 56 := by unfold smallValid; decide +kernel

private theorem sp953 : smallValid 953 56 := by unfold smallValid; decide +kernel

private theorem sp1009 : smallValid 1009 56 := by unfold smallValid; decide +kernel

private theorem sp1065 : smallValid 1065 56 := by unfold smallValid; decide +kernel

private theorem sp1121 : smallValid 1121 56 := by unfold smallValid; decide +kernel

private theorem sp1177 : smallValid 1177 56 := by unfold smallValid; decide +kernel

private theorem sp1233 : smallValid 1233 56 := by unfold smallValid; decide +kernel

private theorem sp1289 : smallValid 1289 57 := by unfold smallValid; decide +kernel

private theorem sp1346 : smallValid 1346 56 := by unfold smallValid; decide +kernel

private theorem sp1402 : smallValid 1402 56 := by unfold smallValid; decide +kernel

private theorem sp1458 : smallValid 1458 56 := by unfold smallValid; decide +kernel

private theorem sp1514 : smallValid 1514 56 := by unfold smallValid; decide +kernel

private theorem sp1570 : smallValid 1570 56 := by unfold smallValid; decide +kernel

private theorem sp1626 : smallValid 1626 56 := by unfold smallValid; decide +kernel

private theorem sp1682 : smallValid 1682 56 := by unfold smallValid; decide +kernel

private theorem sp1738 : smallValid 1738 57 := by unfold smallValid; decide +kernel

private theorem sp1795 : smallValid 1795 56 := by unfold smallValid; decide +kernel

private theorem sp1851 : smallValid 1851 56 := by unfold smallValid; decide +kernel

private theorem sp1907 : smallValid 1907 56 := by unfold smallValid; decide +kernel

private theorem sp1963 : smallValid 1963 56 := by unfold smallValid; decide +kernel

private theorem sp2019 : smallValid 2019 56 := by unfold smallValid; decide +kernel

private theorem sp2075 : smallValid 2075 56 := by unfold smallValid; decide +kernel

private theorem sp2131 : smallValid 2131 56 := by unfold smallValid; decide +kernel

private theorem sp2187 : smallValid 2187 56 := by unfold smallValid; decide +kernel

private theorem sp2243 : smallValid 2243 56 := by unfold smallValid; decide +kernel

private theorem sp2299 : smallValid 2299 56 := by unfold smallValid; decide +kernel

private theorem sp2355 : smallValid 2355 56 := by unfold smallValid; decide +kernel

private theorem sp2411 : smallValid 2411 56 := by unfold smallValid; decide +kernel

private theorem sp2467 : smallValid 2467 56 := by unfold smallValid; decide +kernel

private theorem sp2523 : smallValid 2523 56 := by unfold smallValid; decide +kernel

private theorem sp2579 : smallValid 2579 56 := by unfold smallValid; decide +kernel

private theorem sp2635 : smallValid 2635 57 := by unfold smallValid; decide +kernel

private theorem sp2692 : smallValid 2692 56 := by unfold smallValid; decide +kernel

private theorem sp2748 : smallValid 2748 56 := by unfold smallValid; decide +kernel

private theorem sp2804 : smallValid 2804 56 := by unfold smallValid; decide +kernel

private theorem sp2860 : smallValid 2860 56 := by unfold smallValid; decide +kernel

private theorem sp2916 : smallValid 2916 56 := by unfold smallValid; decide +kernel

private theorem sp2972 : smallValid 2972 56 := by unfold smallValid; decide +kernel

private theorem sp3028 : smallValid 3028 56 := by unfold smallValid; decide +kernel

private theorem sp3084 : smallValid 3084 57 := by unfold smallValid; decide +kernel

private theorem sp3141 : smallValid 3141 56 := by unfold smallValid; decide +kernel

private theorem sp3197 : smallValid 3197 56 := by unfold smallValid; decide +kernel

private theorem sp3253 : smallValid 3253 56 := by unfold smallValid; decide +kernel

private theorem sp3309 : smallValid 3309 56 := by unfold smallValid; decide +kernel

private theorem sp3365 : smallValid 3365 56 := by unfold smallValid; decide +kernel

private theorem sp3421 : smallValid 3421 56 := by unfold smallValid; decide +kernel

private theorem sp3477 : smallValid 3477 56 := by unfold smallValid; decide +kernel

private theorem sp3533 : smallValid 3533 57 := by unfold smallValid; decide +kernel

private theorem sp3590 : smallValid 3590 56 := by unfold smallValid; decide +kernel

private theorem sp3646 : smallValid 3646 56 := by unfold smallValid; decide +kernel

private theorem sp3702 : smallValid 3702 56 := by unfold smallValid; decide +kernel

private theorem sp3758 : smallValid 3758 56 := by unfold smallValid; decide +kernel

private theorem sp3814 : smallValid 3814 56 := by unfold smallValid; decide +kernel

private theorem sp3870 : smallValid 3870 56 := by unfold smallValid; decide +kernel

private theorem sp3926 : smallValid 3926 56 := by unfold smallValid; decide +kernel

private theorem sp3982 : smallValid 3982 56 := by unfold smallValid; decide +kernel

private theorem sp4038 : smallValid 4038 56 := by unfold smallValid; decide +kernel

private theorem sp4094 : smallValid 4094 56 := by unfold smallValid; decide +kernel

private theorem sp4150 : smallValid 4150 56 := by unfold smallValid; decide +kernel

private theorem sp4206 : smallValid 4206 56 := by unfold smallValid; decide +kernel

private theorem sp4262 : smallValid 4262 56 := by unfold smallValid; decide +kernel

private theorem sp4318 : smallValid 4318 56 := by unfold smallValid; decide +kernel

private theorem sp4374 : smallValid 4374 56 := by unfold smallValid; decide +kernel

private theorem sp4430 : smallValid 4430 57 := by unfold smallValid; decide +kernel

private theorem sp4487 : smallValid 4487 56 := by unfold smallValid; decide +kernel

private theorem sp4543 : smallValid 4543 56 := by unfold smallValid; decide +kernel

private theorem sp4599 : smallValid 4599 56 := by unfold smallValid; decide +kernel

private theorem sp4655 : smallValid 4655 56 := by unfold smallValid; decide +kernel

private theorem sp4711 : smallValid 4711 56 := by unfold smallValid; decide +kernel

private theorem sp4767 : smallValid 4767 56 := by unfold smallValid; decide +kernel

private theorem sp4823 : smallValid 4823 56 := by unfold smallValid; decide +kernel

private theorem sp4879 : smallValid 4879 57 := by unfold smallValid; decide +kernel

private theorem sp4936 : smallValid 4936 56 := by unfold smallValid; decide +kernel

private theorem sp4992 : smallValid 4992 56 := by unfold smallValid; decide +kernel

private theorem sp5048 : smallValid 5048 56 := by unfold smallValid; decide +kernel

private theorem sp5104 : smallValid 5104 56 := by unfold smallValid; decide +kernel

private theorem sp5160 : smallValid 5160 56 := by unfold smallValid; decide +kernel

private theorem sp5216 : smallValid 5216 56 := by unfold smallValid; decide +kernel

private theorem sp5272 : smallValid 5272 56 := by unfold smallValid; decide +kernel

private theorem sp5328 : smallValid 5328 57 := by unfold smallValid; decide +kernel

private theorem sp5385 : smallValid 5385 56 := by unfold smallValid; decide +kernel

private theorem sp5441 : smallValid 5441 56 := by unfold smallValid; decide +kernel

private theorem sp5497 : smallValid 5497 56 := by unfold smallValid; decide +kernel

private theorem sp5553 : smallValid 5553 56 := by unfold smallValid; decide +kernel

private theorem sp5609 : smallValid 5609 56 := by unfold smallValid; decide +kernel

private theorem sp5665 : smallValid 5665 56 := by unfold smallValid; decide +kernel

private theorem sp5721 : smallValid 5721 56 := by unfold smallValid; decide +kernel

private theorem sp5777 : smallValid 5777 56 := by unfold smallValid; decide +kernel

private theorem sp5833 : smallValid 5833 56 := by unfold smallValid; decide +kernel

private theorem sp5889 : smallValid 5889 56 := by unfold smallValid; decide +kernel

private theorem sp5945 : smallValid 5945 56 := by unfold smallValid; decide +kernel

private theorem sp6001 : smallValid 6001 56 := by unfold smallValid; decide +kernel

private theorem sp6057 : smallValid 6057 56 := by unfold smallValid; decide +kernel

private theorem sp6113 : smallValid 6113 56 := by unfold smallValid; decide +kernel

private theorem sp6169 : smallValid 6169 56 := by unfold smallValid; decide +kernel

private theorem sp6225 : smallValid 6225 57 := by unfold smallValid; decide +kernel

private theorem sp6282 : smallValid 6282 56 := by unfold smallValid; decide +kernel

private theorem sp6338 : smallValid 6338 56 := by unfold smallValid; decide +kernel

private theorem sp6394 : smallValid 6394 56 := by unfold smallValid; decide +kernel

private theorem sp6450 : smallValid 6450 56 := by unfold smallValid; decide +kernel

private theorem sp6506 : smallValid 6506 56 := by unfold smallValid; decide +kernel

private theorem sp6562 : smallValid 6562 56 := by unfold smallValid; decide +kernel

private theorem sp6618 : smallValid 6618 56 := by unfold smallValid; decide +kernel

private theorem sp6674 : smallValid 6674 57 := by unfold smallValid; decide +kernel

private theorem sp6731 : smallValid 6731 56 := by unfold smallValid; decide +kernel

private theorem sp6787 : smallValid 6787 56 := by unfold smallValid; decide +kernel

private theorem sp6843 : smallValid 6843 56 := by unfold smallValid; decide +kernel

private theorem sp6899 : smallValid 6899 56 := by unfold smallValid; decide +kernel

private theorem sp6955 : smallValid 6955 56 := by unfold smallValid; decide +kernel

private theorem sp7011 : smallValid 7011 56 := by unfold smallValid; decide +kernel

private theorem sp7067 : smallValid 7067 56 := by unfold smallValid; decide +kernel

private theorem sp7123 : smallValid 7123 57 := by unfold smallValid; decide +kernel

private theorem sp7180 : smallValid 7180 56 := by unfold smallValid; decide +kernel

private theorem sp7236 : smallValid 7236 56 := by unfold smallValid; decide +kernel

private theorem sp7292 : smallValid 7292 56 := by unfold smallValid; decide +kernel

private theorem sp7348 : smallValid 7348 56 := by unfold smallValid; decide +kernel

private theorem sp7404 : smallValid 7404 56 := by unfold smallValid; decide +kernel

private theorem sp7460 : smallValid 7460 56 := by unfold smallValid; decide +kernel

private theorem sp7516 : smallValid 7516 56 := by unfold smallValid; decide +kernel

private theorem sp7572 : smallValid 7572 56 := by unfold smallValid; decide +kernel

private theorem sp7628 : smallValid 7628 56 := by unfold smallValid; decide +kernel

private theorem sp7684 : smallValid 7684 56 := by unfold smallValid; decide +kernel

private theorem sp7740 : smallValid 7740 56 := by unfold smallValid; decide +kernel

private theorem sp7796 : smallValid 7796 56 := by unfold smallValid; decide +kernel

private theorem sp7852 : smallValid 7852 56 := by unfold smallValid; decide +kernel

private theorem sp7908 : smallValid 7908 56 := by unfold smallValid; decide +kernel

private theorem sp7964 : smallValid 7964 56 := by unfold smallValid; decide +kernel

private theorem sp8020 : smallValid 8020 57 := by unfold smallValid; decide +kernel

private theorem sp8077 : smallValid 8077 56 := by unfold smallValid; decide +kernel

private theorem sp8133 : smallValid 8133 56 := by unfold smallValid; decide +kernel

private theorem sp8189 : smallValid 8189 56 := by unfold smallValid; decide +kernel

private theorem sp8245 : smallValid 8245 56 := by unfold smallValid; decide +kernel

private theorem sp8301 : smallValid 8301 56 := by unfold smallValid; decide +kernel

private theorem sp8357 : smallValid 8357 56 := by unfold smallValid; decide +kernel

private theorem sp8413 : smallValid 8413 56 := by unfold smallValid; decide +kernel

private theorem sp8469 : smallValid 8469 57 := by unfold smallValid; decide +kernel

private theorem sp8526 : smallValid 8526 56 := by unfold smallValid; decide +kernel

private theorem sp8582 : smallValid 8582 56 := by unfold smallValid; decide +kernel

private theorem sp8638 : smallValid 8638 56 := by unfold smallValid; decide +kernel

private theorem sp8694 : smallValid 8694 56 := by unfold smallValid; decide +kernel

private theorem sp8750 : smallValid 8750 56 := by unfold smallValid; decide +kernel

private theorem sp8806 : smallValid 8806 56 := by unfold smallValid; decide +kernel

private theorem sp8862 : smallValid 8862 56 := by unfold smallValid; decide +kernel

private theorem sp8918 : smallValid 8918 57 := by unfold smallValid; decide +kernel

private theorem sp8975 : smallValid 8975 56 := by unfold smallValid; decide +kernel

private theorem sp9031 : smallValid 9031 56 := by unfold smallValid; decide +kernel

private theorem sp9087 : smallValid 9087 56 := by unfold smallValid; decide +kernel

private theorem sp9143 : smallValid 9143 56 := by unfold smallValid; decide +kernel

private theorem sp9199 : smallValid 9199 56 := by unfold smallValid; decide +kernel

private theorem sp9255 : smallValid 9255 56 := by unfold smallValid; decide +kernel

private theorem sp9311 : smallValid 9311 56 := by unfold smallValid; decide +kernel

private theorem sp9367 : smallValid 9367 56 := by unfold smallValid; decide +kernel

private theorem sp9423 : smallValid 9423 56 := by unfold smallValid; decide +kernel

private theorem sp9479 : smallValid 9479 56 := by unfold smallValid; decide +kernel

private theorem sp9535 : smallValid 9535 56 := by unfold smallValid; decide +kernel

private theorem sp9591 : smallValid 9591 56 := by unfold smallValid; decide +kernel

private theorem sp9647 : smallValid 9647 56 := by unfold smallValid; decide +kernel

private theorem sp9703 : smallValid 9703 56 := by unfold smallValid; decide +kernel

private theorem sp9759 : smallValid 9759 56 := by unfold smallValid; decide +kernel

private theorem sp9815 : smallValid 9815 57 := by unfold smallValid; decide +kernel

private theorem sp9872 : smallValid 9872 56 := by unfold smallValid; decide +kernel

private theorem sp9928 : smallValid 9928 56 := by unfold smallValid; decide +kernel

private theorem sp9984 : smallValid 9984 56 := by unfold smallValid; decide +kernel

private theorem sp10040 : smallValid 10040 56 := by unfold smallValid; decide +kernel

private theorem sp10096 : smallValid 10096 56 := by unfold smallValid; decide +kernel

private theorem sp10152 : smallValid 10152 56 := by unfold smallValid; decide +kernel

private theorem sp10208 : smallValid 10208 56 := by unfold smallValid; decide +kernel

private theorem sp10264 : smallValid 10264 57 := by unfold smallValid; decide +kernel

private theorem sp10321 : smallValid 10321 56 := by unfold smallValid; decide +kernel

private theorem sp10377 : smallValid 10377 56 := by unfold smallValid; decide +kernel

private theorem sp10433 : smallValid 10433 56 := by unfold smallValid; decide +kernel

private theorem sp10489 : smallValid 10489 56 := by unfold smallValid; decide +kernel

private theorem sp10545 : smallValid 10545 56 := by unfold smallValid; decide +kernel

private theorem sp10601 : smallValid 10601 56 := by unfold smallValid; decide +kernel

private theorem sp10657 : smallValid 10657 56 := by unfold smallValid; decide +kernel

private theorem sp10713 : smallValid 10713 57 := by unfold smallValid; decide +kernel

private theorem sp10770 : smallValid 10770 56 := by unfold smallValid; decide +kernel

private theorem sp10826 : smallValid 10826 56 := by unfold smallValid; decide +kernel

private theorem sp10882 : smallValid 10882 56 := by unfold smallValid; decide +kernel

private theorem sp10938 : smallValid 10938 56 := by unfold smallValid; decide +kernel

private theorem sp10994 : smallValid 10994 56 := by unfold smallValid; decide +kernel

private theorem sp11050 : smallValid 11050 56 := by unfold smallValid; decide +kernel

private theorem sp11106 : smallValid 11106 56 := by unfold smallValid; decide +kernel

private theorem sp11162 : smallValid 11162 56 := by unfold smallValid; decide +kernel

private theorem sp11218 : smallValid 11218 56 := by unfold smallValid; decide +kernel

private theorem sp11274 : smallValid 11274 56 := by unfold smallValid; decide +kernel

private theorem sp11330 : smallValid 11330 56 := by unfold smallValid; decide +kernel

private theorem sp11386 : smallValid 11386 56 := by unfold smallValid; decide +kernel

private theorem sp11442 : smallValid 11442 56 := by unfold smallValid; decide +kernel

private theorem sp11498 : smallValid 11498 56 := by unfold smallValid; decide +kernel

private theorem sp11554 : smallValid 11554 56 := by unfold smallValid; decide +kernel

private theorem sp11610 : smallValid 11610 57 := by unfold smallValid; decide +kernel

private theorem sp11667 : smallValid 11667 56 := by unfold smallValid; decide +kernel

private theorem sp11723 : smallValid 11723 56 := by unfold smallValid; decide +kernel

private theorem sp11779 : smallValid 11779 56 := by unfold smallValid; decide +kernel

private theorem sp11835 : smallValid 11835 56 := by unfold smallValid; decide +kernel

private theorem sp11891 : smallValid 11891 56 := by unfold smallValid; decide +kernel

private theorem sp11947 : smallValid 11947 56 := by unfold smallValid; decide +kernel

private theorem sp12003 : smallValid 12003 56 := by unfold smallValid; decide +kernel

private theorem sp12059 : smallValid 12059 57 := by unfold smallValid; decide +kernel

private theorem sp12116 : smallValid 12116 56 := by unfold smallValid; decide +kernel

private theorem sp12172 : smallValid 12172 56 := by unfold smallValid; decide +kernel

private theorem sp12228 : smallValid 12228 56 := by unfold smallValid; decide +kernel

private theorem sp12284 : smallValid 12284 56 := by unfold smallValid; decide +kernel

private theorem sp12340 : smallValid 12340 56 := by unfold smallValid; decide +kernel

private theorem sp12396 : smallValid 12396 56 := by unfold smallValid; decide +kernel

private theorem sp12452 : smallValid 12452 56 := by unfold smallValid; decide +kernel

private theorem sp12508 : smallValid 12508 57 := by unfold smallValid; decide +kernel

private theorem sp12565 : smallValid 12565 56 := by unfold smallValid; decide +kernel

private theorem sp12621 : smallValid 12621 56 := by unfold smallValid; decide +kernel

private theorem sp12677 : smallValid 12677 56 := by unfold smallValid; decide +kernel

private theorem sp12733 : smallValid 12733 56 := by unfold smallValid; decide +kernel

private theorem sp12789 : smallValid 12789 56 := by unfold smallValid; decide +kernel

private theorem sp12845 : smallValid 12845 56 := by unfold smallValid; decide +kernel

private theorem sp12901 : smallValid 12901 56 := by unfold smallValid; decide +kernel

private theorem sp12957 : smallValid 12957 57 := by unfold smallValid; decide +kernel

private theorem sp13014 : smallValid 13014 56 := by unfold smallValid; decide +kernel

private theorem sp13070 : smallValid 13070 56 := by unfold smallValid; decide +kernel

private theorem sp13126 : smallValid 13126 56 := by unfold smallValid; decide +kernel

private theorem sp13182 : smallValid 13182 56 := by unfold smallValid; decide +kernel

private theorem sp13238 : smallValid 13238 56 := by unfold smallValid; decide +kernel

private theorem sp13294 : smallValid 13294 56 := by unfold smallValid; decide +kernel

private theorem sp13350 : smallValid 13350 56 := by unfold smallValid; decide +kernel

private theorem sp13406 : smallValid 13406 57 := by unfold smallValid; decide +kernel

private theorem sp13463 : smallValid 13463 56 := by unfold smallValid; decide +kernel

private theorem sp13519 : smallValid 13519 56 := by unfold smallValid; decide +kernel

private theorem sp13575 : smallValid 13575 56 := by unfold smallValid; decide +kernel

private theorem sp13631 : smallValid 13631 56 := by unfold smallValid; decide +kernel

private theorem sp13687 : smallValid 13687 56 := by unfold smallValid; decide +kernel

private theorem sp13743 : smallValid 13743 56 := by unfold smallValid; decide +kernel

private theorem sp13799 : smallValid 13799 56 := by unfold smallValid; decide +kernel

private theorem sp13855 : smallValid 13855 57 := by unfold smallValid; decide +kernel

private theorem sp13912 : smallValid 13912 56 := by unfold smallValid; decide +kernel

private theorem sp13968 : smallValid 13968 56 := by unfold smallValid; decide +kernel

private theorem sp14024 : smallValid 14024 56 := by unfold smallValid; decide +kernel

private theorem sp14080 : smallValid 14080 56 := by unfold smallValid; decide +kernel

private theorem sp14136 : smallValid 14136 56 := by unfold smallValid; decide +kernel

private theorem sp14192 : smallValid 14192 56 := by unfold smallValid; decide +kernel

private theorem sp14248 : smallValid 14248 56 := by unfold smallValid; decide +kernel

private theorem sp14304 : smallValid 14304 57 := by unfold smallValid; decide +kernel

private theorem sp14361 : smallValid 14361 56 := by unfold smallValid; decide +kernel

private theorem sp14417 : smallValid 14417 56 := by unfold smallValid; decide +kernel

private theorem sp14473 : smallValid 14473 56 := by unfold smallValid; decide +kernel

private theorem sp14529 : smallValid 14529 56 := by unfold smallValid; decide +kernel

private theorem sp14585 : smallValid 14585 56 := by unfold smallValid; decide +kernel

private theorem sp14641 : smallValid 14641 56 := by unfold smallValid; decide +kernel

private theorem sp14697 : smallValid 14697 56 := by unfold smallValid; decide +kernel

private theorem sp14753 : smallValid 14753 56 := by unfold smallValid; decide +kernel

private theorem sp14809 : smallValid 14809 56 := by unfold smallValid; decide +kernel

private theorem sp14865 : smallValid 14865 56 := by unfold smallValid; decide +kernel

private theorem sp14921 : smallValid 14921 56 := by unfold smallValid; decide +kernel

private theorem sp14977 : smallValid 14977 56 := by unfold smallValid; decide +kernel

private theorem sp15033 : smallValid 15033 56 := by unfold smallValid; decide +kernel

private theorem sp15089 : smallValid 15089 56 := by unfold smallValid; decide +kernel

private theorem sp15145 : smallValid 15145 56 := by unfold smallValid; decide +kernel

private theorem sp15201 : smallValid 15201 57 := by unfold smallValid; decide +kernel

private theorem sp15258 : smallValid 15258 56 := by unfold smallValid; decide +kernel

private theorem sp15314 : smallValid 15314 56 := by unfold smallValid; decide +kernel

private theorem sp15370 : smallValid 15370 56 := by unfold smallValid; decide +kernel

private theorem sp15426 : smallValid 15426 56 := by unfold smallValid; decide +kernel

private theorem sp15482 : smallValid 15482 56 := by unfold smallValid; decide +kernel

private theorem sp15538 : smallValid 15538 56 := by unfold smallValid; decide +kernel

private theorem sp15594 : smallValid 15594 56 := by unfold smallValid; decide +kernel

private theorem sp15650 : smallValid 15650 57 := by unfold smallValid; decide +kernel

private theorem sp15707 : smallValid 15707 56 := by unfold smallValid; decide +kernel

private theorem sp15763 : smallValid 15763 56 := by unfold smallValid; decide +kernel

private theorem sp15819 : smallValid 15819 56 := by unfold smallValid; decide +kernel

private theorem sp15875 : smallValid 15875 56 := by unfold smallValid; decide +kernel

private theorem sp15931 : smallValid 15931 56 := by unfold smallValid; decide +kernel

private theorem sp15987 : smallValid 15987 56 := by unfold smallValid; decide +kernel

private theorem sp16043 : smallValid 16043 56 := by unfold smallValid; decide +kernel

private theorem sp16099 : smallValid 16099 57 := by unfold smallValid; decide +kernel

private theorem sp16156 : smallValid 16156 56 := by unfold smallValid; decide +kernel

private theorem sp16212 : smallValid 16212 56 := by unfold smallValid; decide +kernel

private theorem sp16268 : smallValid 16268 56 := by unfold smallValid; decide +kernel

private theorem sp16324 : smallValid 16324 56 := by unfold smallValid; decide +kernel

private theorem sp16380 : smallValid 16380 56 := by unfold smallValid; decide +kernel

private theorem sp16436 : smallValid 16436 56 := by unfold smallValid; decide +kernel

private theorem sp16492 : smallValid 16492 56 := by unfold smallValid; decide +kernel

private theorem sp16548 : smallValid 16548 56 := by unfold smallValid; decide +kernel

private theorem sp16604 : smallValid 16604 56 := by unfold smallValid; decide +kernel

private theorem sp16660 : smallValid 16660 56 := by unfold smallValid; decide +kernel

private theorem sp16716 : smallValid 16716 56 := by unfold smallValid; decide +kernel

private theorem sp16772 : smallValid 16772 56 := by unfold smallValid; decide +kernel

private theorem sp16828 : smallValid 16828 56 := by unfold smallValid; decide +kernel

private theorem sp16884 : smallValid 16884 56 := by unfold smallValid; decide +kernel

private theorem sp16940 : smallValid 16940 56 := by unfold smallValid; decide +kernel

private theorem sp16996 : smallValid 16996 57 := by unfold smallValid; decide +kernel

private theorem sp17053 : smallValid 17053 56 := by unfold smallValid; decide +kernel

private theorem sp17109 : smallValid 17109 56 := by unfold smallValid; decide +kernel

private theorem sp17165 : smallValid 17165 56 := by unfold smallValid; decide +kernel

private theorem sp17221 : smallValid 17221 56 := by unfold smallValid; decide +kernel

private theorem sp17277 : smallValid 17277 56 := by unfold smallValid; decide +kernel

private theorem sp17333 : smallValid 17333 56 := by unfold smallValid; decide +kernel

private theorem sp17389 : smallValid 17389 56 := by unfold smallValid; decide +kernel

private theorem sp17445 : smallValid 17445 57 := by unfold smallValid; decide +kernel

private theorem sp17502 : smallValid 17502 56 := by unfold smallValid; decide +kernel

private theorem sp17558 : smallValid 17558 56 := by unfold smallValid; decide +kernel

private theorem sp17614 : smallValid 17614 56 := by unfold smallValid; decide +kernel

private theorem sp17670 : smallValid 17670 56 := by unfold smallValid; decide +kernel

private theorem sp17726 : smallValid 17726 56 := by unfold smallValid; decide +kernel

private theorem sp17782 : smallValid 17782 56 := by unfold smallValid; decide +kernel

private theorem sp17838 : smallValid 17838 56 := by unfold smallValid; decide +kernel

private theorem sp17894 : smallValid 17894 57 := by unfold smallValid; decide +kernel

private theorem sp17951 : smallValid 17951 56 := by unfold smallValid; decide +kernel

private theorem sp18007 : smallValid 18007 56 := by unfold smallValid; decide +kernel

private theorem sp18063 : smallValid 18063 56 := by unfold smallValid; decide +kernel

private theorem sp18119 : smallValid 18119 56 := by unfold smallValid; decide +kernel

private theorem sp18175 : smallValid 18175 56 := by unfold smallValid; decide +kernel

private theorem sp18231 : smallValid 18231 56 := by unfold smallValid; decide +kernel

private theorem sp18287 : smallValid 18287 56 := by unfold smallValid; decide +kernel

private theorem sp18343 : smallValid 18343 56 := by unfold smallValid; decide +kernel

private theorem sp18399 : smallValid 18399 56 := by unfold smallValid; decide +kernel

private theorem sp18455 : smallValid 18455 56 := by unfold smallValid; decide +kernel

private theorem sp18511 : smallValid 18511 56 := by unfold smallValid; decide +kernel

private theorem sp18567 : smallValid 18567 56 := by unfold smallValid; decide +kernel

private theorem sp18623 : smallValid 18623 56 := by unfold smallValid; decide +kernel

private theorem sp18679 : smallValid 18679 56 := by unfold smallValid; decide +kernel

private theorem sp18735 : smallValid 18735 56 := by unfold smallValid; decide +kernel

private theorem sp18791 : smallValid 18791 57 := by unfold smallValid; decide +kernel

private theorem sp18848 : smallValid 18848 56 := by unfold smallValid; decide +kernel

private theorem sp18904 : smallValid 18904 56 := by unfold smallValid; decide +kernel

private theorem sp18960 : smallValid 18960 56 := by unfold smallValid; decide +kernel

private theorem sp19016 : smallValid 19016 56 := by unfold smallValid; decide +kernel

private theorem sp19072 : smallValid 19072 56 := by unfold smallValid; decide +kernel

private theorem sp19128 : smallValid 19128 56 := by unfold smallValid; decide +kernel

private theorem sp19184 : smallValid 19184 56 := by unfold smallValid; decide +kernel

private theorem sp19240 : smallValid 19240 57 := by unfold smallValid; decide +kernel

private theorem sp19297 : smallValid 19297 56 := by unfold smallValid; decide +kernel

private theorem sp19353 : smallValid 19353 56 := by unfold smallValid; decide +kernel

private theorem sp19409 : smallValid 19409 56 := by unfold smallValid; decide +kernel

private theorem sp19465 : smallValid 19465 56 := by unfold smallValid; decide +kernel

private theorem sp19521 : smallValid 19521 56 := by unfold smallValid; decide +kernel

private theorem sp19577 : smallValid 19577 56 := by unfold smallValid; decide +kernel

private theorem sp19633 : smallValid 19633 56 := by unfold smallValid; decide +kernel

private theorem sp19689 : smallValid 19689 57 := by unfold smallValid; decide +kernel

private theorem sp19746 : smallValid 19746 56 := by unfold smallValid; decide +kernel

private theorem sp19802 : smallValid 19802 56 := by unfold smallValid; decide +kernel

private theorem sp19858 : smallValid 19858 56 := by unfold smallValid; decide +kernel

private theorem sp19914 : smallValid 19914 56 := by unfold smallValid; decide +kernel

private theorem sp19970 : smallValid 19970 56 := by unfold smallValid; decide +kernel

private theorem sp20026 : smallValid 20026 56 := by unfold smallValid; decide +kernel

private theorem sp20082 : smallValid 20082 56 := by unfold smallValid; decide +kernel

private theorem sp20138 : smallValid 20138 57 := by unfold smallValid; decide +kernel

private theorem sp20195 : smallValid 20195 56 := by unfold smallValid; decide +kernel

private theorem sp20251 : smallValid 20251 56 := by unfold smallValid; decide +kernel

private theorem sp20307 : smallValid 20307 56 := by unfold smallValid; decide +kernel

private theorem sp20363 : smallValid 20363 56 := by unfold smallValid; decide +kernel

private theorem sp20419 : smallValid 20419 56 := by unfold smallValid; decide +kernel

private theorem sp20475 : smallValid 20475 56 := by unfold smallValid; decide +kernel

private theorem sp20531 : smallValid 20531 56 := by unfold smallValid; decide +kernel

private theorem sp20587 : smallValid 20587 57 := by unfold smallValid; decide +kernel

private theorem sp20644 : smallValid 20644 56 := by unfold smallValid; decide +kernel

private theorem sp20700 : smallValid 20700 56 := by unfold smallValid; decide +kernel

private theorem sp20756 : smallValid 20756 56 := by unfold smallValid; decide +kernel

private theorem sp20812 : smallValid 20812 56 := by unfold smallValid; decide +kernel

private theorem sp20868 : smallValid 20868 56 := by unfold smallValid; decide +kernel

private theorem sp20924 : smallValid 20924 56 := by unfold smallValid; decide +kernel

private theorem sp20980 : smallValid 20980 56 := by unfold smallValid; decide +kernel

private theorem sp21036 : smallValid 21036 57 := by unfold smallValid; decide +kernel

private theorem sp21093 : smallValid 21093 56 := by unfold smallValid; decide +kernel

private theorem sp21149 : smallValid 21149 56 := by unfold smallValid; decide +kernel

private theorem sp21205 : smallValid 21205 56 := by unfold smallValid; decide +kernel

private theorem sp21261 : smallValid 21261 56 := by unfold smallValid; decide +kernel

private theorem sp21317 : smallValid 21317 56 := by unfold smallValid; decide +kernel

private theorem sp21373 : smallValid 21373 56 := by unfold smallValid; decide +kernel

private theorem sp21429 : smallValid 21429 56 := by unfold smallValid; decide +kernel

private theorem sp21485 : smallValid 21485 57 := by unfold smallValid; decide +kernel

private theorem sp21542 : smallValid 21542 56 := by unfold smallValid; decide +kernel

private theorem sp21598 : smallValid 21598 56 := by unfold smallValid; decide +kernel

private theorem sp21654 : smallValid 21654 56 := by unfold smallValid; decide +kernel

private theorem sp21710 : smallValid 21710 56 := by unfold smallValid; decide +kernel

private theorem sp21766 : smallValid 21766 56 := by unfold smallValid; decide +kernel

private theorem sp21822 : smallValid 21822 56 := by unfold smallValid; decide +kernel

private theorem sp21878 : smallValid 21878 56 := by unfold smallValid; decide +kernel

private theorem sp21934 : smallValid 21934 56 := by unfold smallValid; decide +kernel

private theorem sp21990 : smallValid 21990 56 := by unfold smallValid; decide +kernel

private theorem sp22046 : smallValid 22046 56 := by unfold smallValid; decide +kernel

private theorem sp22102 : smallValid 22102 56 := by unfold smallValid; decide +kernel

private theorem sp22158 : smallValid 22158 56 := by unfold smallValid; decide +kernel

private theorem sp22214 : smallValid 22214 56 := by unfold smallValid; decide +kernel

private theorem sp22270 : smallValid 22270 56 := by unfold smallValid; decide +kernel

private theorem sp22326 : smallValid 22326 56 := by unfold smallValid; decide +kernel

private theorem sp22382 : smallValid 22382 57 := by unfold smallValid; decide +kernel

private theorem sp22439 : smallValid 22439 56 := by unfold smallValid; decide +kernel

private theorem sp22495 : smallValid 22495 56 := by unfold smallValid; decide +kernel

private theorem sp22551 : smallValid 22551 56 := by unfold smallValid; decide +kernel

private theorem sp22607 : smallValid 22607 56 := by unfold smallValid; decide +kernel

private theorem sp22663 : smallValid 22663 56 := by unfold smallValid; decide +kernel

private theorem sp22719 : smallValid 22719 56 := by unfold smallValid; decide +kernel

private theorem sp22775 : smallValid 22775 56 := by unfold smallValid; decide +kernel

private theorem sp22831 : smallValid 22831 57 := by unfold smallValid; decide +kernel

private theorem sp22888 : smallValid 22888 56 := by unfold smallValid; decide +kernel

private theorem sp22944 : smallValid 22944 56 := by unfold smallValid; decide +kernel

private theorem sp23000 : smallValid 23000 56 := by unfold smallValid; decide +kernel

private theorem sp23056 : smallValid 23056 56 := by unfold smallValid; decide +kernel

private theorem sp23112 : smallValid 23112 56 := by unfold smallValid; decide +kernel

private theorem sp23168 : smallValid 23168 56 := by unfold smallValid; decide +kernel

private theorem sp23224 : smallValid 23224 56 := by unfold smallValid; decide +kernel

private theorem sp23280 : smallValid 23280 57 := by unfold smallValid; decide +kernel

private theorem sp23337 : smallValid 23337 56 := by unfold smallValid; decide +kernel

private theorem sp23393 : smallValid 23393 56 := by unfold smallValid; decide +kernel

private theorem sp23449 : smallValid 23449 56 := by unfold smallValid; decide +kernel

private theorem sp23505 : smallValid 23505 56 := by unfold smallValid; decide +kernel

private theorem sp23561 : smallValid 23561 56 := by unfold smallValid; decide +kernel

private theorem sp23617 : smallValid 23617 56 := by unfold smallValid; decide +kernel

private theorem sp23673 : smallValid 23673 56 := by unfold smallValid; decide +kernel

private theorem sp23729 : smallValid 23729 56 := by unfold smallValid; decide +kernel

private theorem sp23785 : smallValid 23785 56 := by unfold smallValid; decide +kernel

private theorem sp23841 : smallValid 23841 56 := by unfold smallValid; decide +kernel

private theorem sp23897 : smallValid 23897 56 := by unfold smallValid; decide +kernel

private theorem sp23953 : smallValid 23953 56 := by unfold smallValid; decide +kernel

private theorem sp24009 : smallValid 24009 56 := by unfold smallValid; decide +kernel

private theorem sp24065 : smallValid 24065 56 := by unfold smallValid; decide +kernel

private theorem sp24121 : smallValid 24121 56 := by unfold smallValid; decide +kernel

private theorem sp24177 : smallValid 24177 57 := by unfold smallValid; decide +kernel

private theorem sp24234 : smallValid 24234 56 := by unfold smallValid; decide +kernel

private theorem sp24290 : smallValid 24290 56 := by unfold smallValid; decide +kernel

private theorem sp24346 : smallValid 24346 56 := by unfold smallValid; decide +kernel

private theorem sp24402 : smallValid 24402 56 := by unfold smallValid; decide +kernel

private theorem sp24458 : smallValid 24458 56 := by unfold smallValid; decide +kernel

private theorem sp24514 : smallValid 24514 56 := by unfold smallValid; decide +kernel

private theorem sp24570 : smallValid 24570 56 := by unfold smallValid; decide +kernel

private theorem sp24626 : smallValid 24626 57 := by unfold smallValid; decide +kernel

private theorem sp24683 : smallValid 24683 56 := by unfold smallValid; decide +kernel

private theorem sp24739 : smallValid 24739 56 := by unfold smallValid; decide +kernel

private theorem sp24795 : smallValid 24795 56 := by unfold smallValid; decide +kernel

private theorem sp24851 : smallValid 24851 56 := by unfold smallValid; decide +kernel

private theorem sp24907 : smallValid 24907 56 := by unfold smallValid; decide +kernel

private theorem sp24963 : smallValid 24963 56 := by unfold smallValid; decide +kernel

private theorem sp25019 : smallValid 25019 56 := by unfold smallValid; decide +kernel

private theorem sp25075 : smallValid 25075 57 := by unfold smallValid; decide +kernel

private theorem sp25132 : smallValid 25132 56 := by unfold smallValid; decide +kernel

private theorem sp25188 : smallValid 25188 56 := by unfold smallValid; decide +kernel

private theorem sp25244 : smallValid 25244 56 := by unfold smallValid; decide +kernel

private theorem sp25300 : smallValid 25300 56 := by unfold smallValid; decide +kernel

private theorem sp25356 : smallValid 25356 56 := by unfold smallValid; decide +kernel

private theorem sp25412 : smallValid 25412 56 := by unfold smallValid; decide +kernel

private theorem sp25468 : smallValid 25468 56 := by unfold smallValid; decide +kernel

private theorem sp25524 : smallValid 25524 56 := by unfold smallValid; decide +kernel

private theorem sp25580 : smallValid 25580 56 := by unfold smallValid; decide +kernel

private theorem sp25636 : smallValid 25636 56 := by unfold smallValid; decide +kernel

private theorem sp25692 : smallValid 25692 56 := by unfold smallValid; decide +kernel

private theorem sp25748 : smallValid 25748 56 := by unfold smallValid; decide +kernel

private theorem sp25804 : smallValid 25804 56 := by unfold smallValid; decide +kernel

private theorem sp25860 : smallValid 25860 56 := by unfold smallValid; decide +kernel

private theorem sp25916 : smallValid 25916 56 := by unfold smallValid; decide +kernel

private theorem sp25972 : smallValid 25972 57 := by unfold smallValid; decide +kernel

private theorem sp26029 : smallValid 26029 56 := by unfold smallValid; decide +kernel

private theorem sp26085 : smallValid 26085 56 := by unfold smallValid; decide +kernel

private theorem sp26141 : smallValid 26141 56 := by unfold smallValid; decide +kernel

private theorem sp26197 : smallValid 26197 56 := by unfold smallValid; decide +kernel

private theorem sp26253 : smallValid 26253 56 := by unfold smallValid; decide +kernel

private theorem sp26309 : smallValid 26309 56 := by unfold smallValid; decide +kernel

private theorem sp26365 : smallValid 26365 56 := by unfold smallValid; decide +kernel

private theorem sp26421 : smallValid 26421 57 := by unfold smallValid; decide +kernel

private theorem sp26478 : smallValid 26478 56 := by unfold smallValid; decide +kernel

private theorem sp26534 : smallValid 26534 56 := by unfold smallValid; decide +kernel

private theorem sp26590 : smallValid 26590 56 := by unfold smallValid; decide +kernel

private theorem sp26646 : smallValid 26646 56 := by unfold smallValid; decide +kernel

private theorem sp26702 : smallValid 26702 56 := by unfold smallValid; decide +kernel

private theorem sp26758 : smallValid 26758 56 := by unfold smallValid; decide +kernel

private theorem sp26814 : smallValid 26814 56 := by unfold smallValid; decide +kernel

private theorem sp26870 : smallValid 26870 57 := by unfold smallValid; decide +kernel

private theorem sp26927 : smallValid 26927 56 := by unfold smallValid; decide +kernel

private theorem sp26983 : smallValid 26983 56 := by unfold smallValid; decide +kernel

private theorem sp27039 : smallValid 27039 56 := by unfold smallValid; decide +kernel

private theorem sp27095 : smallValid 27095 56 := by unfold smallValid; decide +kernel

private theorem sp27151 : smallValid 27151 56 := by unfold smallValid; decide +kernel

private theorem sp27207 : smallValid 27207 56 := by unfold smallValid; decide +kernel

private theorem sp27263 : smallValid 27263 56 := by unfold smallValid; decide +kernel

private theorem sp27319 : smallValid 27319 57 := by unfold smallValid; decide +kernel

private theorem sp27376 : smallValid 27376 56 := by unfold smallValid; decide +kernel

private theorem sp27432 : smallValid 27432 56 := by unfold smallValid; decide +kernel

private theorem sp27488 : smallValid 27488 56 := by unfold smallValid; decide +kernel

private theorem sp27544 : smallValid 27544 56 := by unfold smallValid; decide +kernel

private theorem sp27600 : smallValid 27600 56 := by unfold smallValid; decide +kernel

private theorem sp27656 : smallValid 27656 56 := by unfold smallValid; decide +kernel

private theorem sp27712 : smallValid 27712 56 := by unfold smallValid; decide +kernel

private theorem sp27768 : smallValid 27768 57 := by unfold smallValid; decide +kernel

private theorem sp27825 : smallValid 27825 56 := by unfold smallValid; decide +kernel

private theorem sp27881 : smallValid 27881 56 := by unfold smallValid; decide +kernel

private theorem sp27937 : smallValid 27937 56 := by unfold smallValid; decide +kernel

private theorem sp27993 : smallValid 27993 56 := by unfold smallValid; decide +kernel

private theorem sp28049 : smallValid 28049 56 := by unfold smallValid; decide +kernel

private theorem sp28105 : smallValid 28105 56 := by unfold smallValid; decide +kernel

private theorem sp28161 : smallValid 28161 56 := by unfold smallValid; decide +kernel

private theorem sp28217 : smallValid 28217 57 := by unfold smallValid; decide +kernel

private theorem sp28274 : smallValid 28274 56 := by unfold smallValid; decide +kernel

private theorem sp28330 : smallValid 28330 56 := by unfold smallValid; decide +kernel

private theorem sp28386 : smallValid 28386 56 := by unfold smallValid; decide +kernel

private theorem sp28442 : smallValid 28442 56 := by unfold smallValid; decide +kernel

private theorem sp28498 : smallValid 28498 56 := by unfold smallValid; decide +kernel

private theorem sp28554 : smallValid 28554 56 := by unfold smallValid; decide +kernel

private theorem sp28610 : smallValid 28610 56 := by unfold smallValid; decide +kernel

private theorem sp28666 : smallValid 28666 57 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤28722) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 28723 := (joinSmall (lo:=0) (a:=14361) (b:=14362) (joinSmall (lo:=0) (a:=7180) (b:=7181) (joinSmall (lo:=0) (a:=3590) (b:=3590) (joinSmall (lo:=0) (a:=1795) (b:=1795) (joinSmall (lo:=0) (a:=897) (b:=898) (joinSmall (lo:=0) (a:=448) (b:=449) (joinSmall (lo:=0) (a:=224) (b:=224) (joinSmall (lo:=0) (a:=112) (b:=112) (joinSmall (lo:=0) (a:=56) (b:=56) sp0 sp56) (joinSmall (lo:=112) (a:=56) (b:=56) sp112 sp168)) (joinSmall (lo:=224) (a:=112) (b:=112) (joinSmall (lo:=224) (a:=56) (b:=56) sp224 sp280) (joinSmall (lo:=336) (a:=56) (b:=56) sp336 sp392))) (joinSmall (lo:=448) (a:=224) (b:=225) (joinSmall (lo:=448) (a:=112) (b:=112) (joinSmall (lo:=448) (a:=56) (b:=56) sp448 sp504) (joinSmall (lo:=560) (a:=56) (b:=56) sp560 sp616)) (joinSmall (lo:=672) (a:=112) (b:=113) (joinSmall (lo:=672) (a:=56) (b:=56) sp672 sp728) (joinSmall (lo:=784) (a:=56) (b:=57) sp784 sp840)))) (joinSmall (lo:=897) (a:=449) (b:=449) (joinSmall (lo:=897) (a:=224) (b:=225) (joinSmall (lo:=897) (a:=112) (b:=112) (joinSmall (lo:=897) (a:=56) (b:=56) sp897 sp953) (joinSmall (lo:=1009) (a:=56) (b:=56) sp1009 sp1065)) (joinSmall (lo:=1121) (a:=112) (b:=113) (joinSmall (lo:=1121) (a:=56) (b:=56) sp1121 sp1177) (joinSmall (lo:=1233) (a:=56) (b:=57) sp1233 sp1289))) (joinSmall (lo:=1346) (a:=224) (b:=225) (joinSmall (lo:=1346) (a:=112) (b:=112) (joinSmall (lo:=1346) (a:=56) (b:=56) sp1346 sp1402) (joinSmall (lo:=1458) (a:=56) (b:=56) sp1458 sp1514)) (joinSmall (lo:=1570) (a:=112) (b:=113) (joinSmall (lo:=1570) (a:=56) (b:=56) sp1570 sp1626) (joinSmall (lo:=1682) (a:=56) (b:=57) sp1682 sp1738))))) (joinSmall (lo:=1795) (a:=897) (b:=898) (joinSmall (lo:=1795) (a:=448) (b:=449) (joinSmall (lo:=1795) (a:=224) (b:=224) (joinSmall (lo:=1795) (a:=112) (b:=112) (joinSmall (lo:=1795) (a:=56) (b:=56) sp1795 sp1851) (joinSmall (lo:=1907) (a:=56) (b:=56) sp1907 sp1963)) (joinSmall (lo:=2019) (a:=112) (b:=112) (joinSmall (lo:=2019) (a:=56) (b:=56) sp2019 sp2075) (joinSmall (lo:=2131) (a:=56) (b:=56) sp2131 sp2187))) (joinSmall (lo:=2243) (a:=224) (b:=225) (joinSmall (lo:=2243) (a:=112) (b:=112) (joinSmall (lo:=2243) (a:=56) (b:=56) sp2243 sp2299) (joinSmall (lo:=2355) (a:=56) (b:=56) sp2355 sp2411)) (joinSmall (lo:=2467) (a:=112) (b:=113) (joinSmall (lo:=2467) (a:=56) (b:=56) sp2467 sp2523) (joinSmall (lo:=2579) (a:=56) (b:=57) sp2579 sp2635)))) (joinSmall (lo:=2692) (a:=449) (b:=449) (joinSmall (lo:=2692) (a:=224) (b:=225) (joinSmall (lo:=2692) (a:=112) (b:=112) (joinSmall (lo:=2692) (a:=56) (b:=56) sp2692 sp2748) (joinSmall (lo:=2804) (a:=56) (b:=56) sp2804 sp2860)) (joinSmall (lo:=2916) (a:=112) (b:=113) (joinSmall (lo:=2916) (a:=56) (b:=56) sp2916 sp2972) (joinSmall (lo:=3028) (a:=56) (b:=57) sp3028 sp3084))) (joinSmall (lo:=3141) (a:=224) (b:=225) (joinSmall (lo:=3141) (a:=112) (b:=112) (joinSmall (lo:=3141) (a:=56) (b:=56) sp3141 sp3197) (joinSmall (lo:=3253) (a:=56) (b:=56) sp3253 sp3309)) (joinSmall (lo:=3365) (a:=112) (b:=113) (joinSmall (lo:=3365) (a:=56) (b:=56) sp3365 sp3421) (joinSmall (lo:=3477) (a:=56) (b:=57) sp3477 sp3533)))))) (joinSmall (lo:=3590) (a:=1795) (b:=1795) (joinSmall (lo:=3590) (a:=897) (b:=898) (joinSmall (lo:=3590) (a:=448) (b:=449) (joinSmall (lo:=3590) (a:=224) (b:=224) (joinSmall (lo:=3590) (a:=112) (b:=112) (joinSmall (lo:=3590) (a:=56) (b:=56) sp3590 sp3646) (joinSmall (lo:=3702) (a:=56) (b:=56) sp3702 sp3758)) (joinSmall (lo:=3814) (a:=112) (b:=112) (joinSmall (lo:=3814) (a:=56) (b:=56) sp3814 sp3870) (joinSmall (lo:=3926) (a:=56) (b:=56) sp3926 sp3982))) (joinSmall (lo:=4038) (a:=224) (b:=225) (joinSmall (lo:=4038) (a:=112) (b:=112) (joinSmall (lo:=4038) (a:=56) (b:=56) sp4038 sp4094) (joinSmall (lo:=4150) (a:=56) (b:=56) sp4150 sp4206)) (joinSmall (lo:=4262) (a:=112) (b:=113) (joinSmall (lo:=4262) (a:=56) (b:=56) sp4262 sp4318) (joinSmall (lo:=4374) (a:=56) (b:=57) sp4374 sp4430)))) (joinSmall (lo:=4487) (a:=449) (b:=449) (joinSmall (lo:=4487) (a:=224) (b:=225) (joinSmall (lo:=4487) (a:=112) (b:=112) (joinSmall (lo:=4487) (a:=56) (b:=56) sp4487 sp4543) (joinSmall (lo:=4599) (a:=56) (b:=56) sp4599 sp4655)) (joinSmall (lo:=4711) (a:=112) (b:=113) (joinSmall (lo:=4711) (a:=56) (b:=56) sp4711 sp4767) (joinSmall (lo:=4823) (a:=56) (b:=57) sp4823 sp4879))) (joinSmall (lo:=4936) (a:=224) (b:=225) (joinSmall (lo:=4936) (a:=112) (b:=112) (joinSmall (lo:=4936) (a:=56) (b:=56) sp4936 sp4992) (joinSmall (lo:=5048) (a:=56) (b:=56) sp5048 sp5104)) (joinSmall (lo:=5160) (a:=112) (b:=113) (joinSmall (lo:=5160) (a:=56) (b:=56) sp5160 sp5216) (joinSmall (lo:=5272) (a:=56) (b:=57) sp5272 sp5328))))) (joinSmall (lo:=5385) (a:=897) (b:=898) (joinSmall (lo:=5385) (a:=448) (b:=449) (joinSmall (lo:=5385) (a:=224) (b:=224) (joinSmall (lo:=5385) (a:=112) (b:=112) (joinSmall (lo:=5385) (a:=56) (b:=56) sp5385 sp5441) (joinSmall (lo:=5497) (a:=56) (b:=56) sp5497 sp5553)) (joinSmall (lo:=5609) (a:=112) (b:=112) (joinSmall (lo:=5609) (a:=56) (b:=56) sp5609 sp5665) (joinSmall (lo:=5721) (a:=56) (b:=56) sp5721 sp5777))) (joinSmall (lo:=5833) (a:=224) (b:=225) (joinSmall (lo:=5833) (a:=112) (b:=112) (joinSmall (lo:=5833) (a:=56) (b:=56) sp5833 sp5889) (joinSmall (lo:=5945) (a:=56) (b:=56) sp5945 sp6001)) (joinSmall (lo:=6057) (a:=112) (b:=113) (joinSmall (lo:=6057) (a:=56) (b:=56) sp6057 sp6113) (joinSmall (lo:=6169) (a:=56) (b:=57) sp6169 sp6225)))) (joinSmall (lo:=6282) (a:=449) (b:=449) (joinSmall (lo:=6282) (a:=224) (b:=225) (joinSmall (lo:=6282) (a:=112) (b:=112) (joinSmall (lo:=6282) (a:=56) (b:=56) sp6282 sp6338) (joinSmall (lo:=6394) (a:=56) (b:=56) sp6394 sp6450)) (joinSmall (lo:=6506) (a:=112) (b:=113) (joinSmall (lo:=6506) (a:=56) (b:=56) sp6506 sp6562) (joinSmall (lo:=6618) (a:=56) (b:=57) sp6618 sp6674))) (joinSmall (lo:=6731) (a:=224) (b:=225) (joinSmall (lo:=6731) (a:=112) (b:=112) (joinSmall (lo:=6731) (a:=56) (b:=56) sp6731 sp6787) (joinSmall (lo:=6843) (a:=56) (b:=56) sp6843 sp6899)) (joinSmall (lo:=6955) (a:=112) (b:=113) (joinSmall (lo:=6955) (a:=56) (b:=56) sp6955 sp7011) (joinSmall (lo:=7067) (a:=56) (b:=57) sp7067 sp7123))))))) (joinSmall (lo:=7180) (a:=3590) (b:=3591) (joinSmall (lo:=7180) (a:=1795) (b:=1795) (joinSmall (lo:=7180) (a:=897) (b:=898) (joinSmall (lo:=7180) (a:=448) (b:=449) (joinSmall (lo:=7180) (a:=224) (b:=224) (joinSmall (lo:=7180) (a:=112) (b:=112) (joinSmall (lo:=7180) (a:=56) (b:=56) sp7180 sp7236) (joinSmall (lo:=7292) (a:=56) (b:=56) sp7292 sp7348)) (joinSmall (lo:=7404) (a:=112) (b:=112) (joinSmall (lo:=7404) (a:=56) (b:=56) sp7404 sp7460) (joinSmall (lo:=7516) (a:=56) (b:=56) sp7516 sp7572))) (joinSmall (lo:=7628) (a:=224) (b:=225) (joinSmall (lo:=7628) (a:=112) (b:=112) (joinSmall (lo:=7628) (a:=56) (b:=56) sp7628 sp7684) (joinSmall (lo:=7740) (a:=56) (b:=56) sp7740 sp7796)) (joinSmall (lo:=7852) (a:=112) (b:=113) (joinSmall (lo:=7852) (a:=56) (b:=56) sp7852 sp7908) (joinSmall (lo:=7964) (a:=56) (b:=57) sp7964 sp8020)))) (joinSmall (lo:=8077) (a:=449) (b:=449) (joinSmall (lo:=8077) (a:=224) (b:=225) (joinSmall (lo:=8077) (a:=112) (b:=112) (joinSmall (lo:=8077) (a:=56) (b:=56) sp8077 sp8133) (joinSmall (lo:=8189) (a:=56) (b:=56) sp8189 sp8245)) (joinSmall (lo:=8301) (a:=112) (b:=113) (joinSmall (lo:=8301) (a:=56) (b:=56) sp8301 sp8357) (joinSmall (lo:=8413) (a:=56) (b:=57) sp8413 sp8469))) (joinSmall (lo:=8526) (a:=224) (b:=225) (joinSmall (lo:=8526) (a:=112) (b:=112) (joinSmall (lo:=8526) (a:=56) (b:=56) sp8526 sp8582) (joinSmall (lo:=8638) (a:=56) (b:=56) sp8638 sp8694)) (joinSmall (lo:=8750) (a:=112) (b:=113) (joinSmall (lo:=8750) (a:=56) (b:=56) sp8750 sp8806) (joinSmall (lo:=8862) (a:=56) (b:=57) sp8862 sp8918))))) (joinSmall (lo:=8975) (a:=897) (b:=898) (joinSmall (lo:=8975) (a:=448) (b:=449) (joinSmall (lo:=8975) (a:=224) (b:=224) (joinSmall (lo:=8975) (a:=112) (b:=112) (joinSmall (lo:=8975) (a:=56) (b:=56) sp8975 sp9031) (joinSmall (lo:=9087) (a:=56) (b:=56) sp9087 sp9143)) (joinSmall (lo:=9199) (a:=112) (b:=112) (joinSmall (lo:=9199) (a:=56) (b:=56) sp9199 sp9255) (joinSmall (lo:=9311) (a:=56) (b:=56) sp9311 sp9367))) (joinSmall (lo:=9423) (a:=224) (b:=225) (joinSmall (lo:=9423) (a:=112) (b:=112) (joinSmall (lo:=9423) (a:=56) (b:=56) sp9423 sp9479) (joinSmall (lo:=9535) (a:=56) (b:=56) sp9535 sp9591)) (joinSmall (lo:=9647) (a:=112) (b:=113) (joinSmall (lo:=9647) (a:=56) (b:=56) sp9647 sp9703) (joinSmall (lo:=9759) (a:=56) (b:=57) sp9759 sp9815)))) (joinSmall (lo:=9872) (a:=449) (b:=449) (joinSmall (lo:=9872) (a:=224) (b:=225) (joinSmall (lo:=9872) (a:=112) (b:=112) (joinSmall (lo:=9872) (a:=56) (b:=56) sp9872 sp9928) (joinSmall (lo:=9984) (a:=56) (b:=56) sp9984 sp10040)) (joinSmall (lo:=10096) (a:=112) (b:=113) (joinSmall (lo:=10096) (a:=56) (b:=56) sp10096 sp10152) (joinSmall (lo:=10208) (a:=56) (b:=57) sp10208 sp10264))) (joinSmall (lo:=10321) (a:=224) (b:=225) (joinSmall (lo:=10321) (a:=112) (b:=112) (joinSmall (lo:=10321) (a:=56) (b:=56) sp10321 sp10377) (joinSmall (lo:=10433) (a:=56) (b:=56) sp10433 sp10489)) (joinSmall (lo:=10545) (a:=112) (b:=113) (joinSmall (lo:=10545) (a:=56) (b:=56) sp10545 sp10601) (joinSmall (lo:=10657) (a:=56) (b:=57) sp10657 sp10713)))))) (joinSmall (lo:=10770) (a:=1795) (b:=1796) (joinSmall (lo:=10770) (a:=897) (b:=898) (joinSmall (lo:=10770) (a:=448) (b:=449) (joinSmall (lo:=10770) (a:=224) (b:=224) (joinSmall (lo:=10770) (a:=112) (b:=112) (joinSmall (lo:=10770) (a:=56) (b:=56) sp10770 sp10826) (joinSmall (lo:=10882) (a:=56) (b:=56) sp10882 sp10938)) (joinSmall (lo:=10994) (a:=112) (b:=112) (joinSmall (lo:=10994) (a:=56) (b:=56) sp10994 sp11050) (joinSmall (lo:=11106) (a:=56) (b:=56) sp11106 sp11162))) (joinSmall (lo:=11218) (a:=224) (b:=225) (joinSmall (lo:=11218) (a:=112) (b:=112) (joinSmall (lo:=11218) (a:=56) (b:=56) sp11218 sp11274) (joinSmall (lo:=11330) (a:=56) (b:=56) sp11330 sp11386)) (joinSmall (lo:=11442) (a:=112) (b:=113) (joinSmall (lo:=11442) (a:=56) (b:=56) sp11442 sp11498) (joinSmall (lo:=11554) (a:=56) (b:=57) sp11554 sp11610)))) (joinSmall (lo:=11667) (a:=449) (b:=449) (joinSmall (lo:=11667) (a:=224) (b:=225) (joinSmall (lo:=11667) (a:=112) (b:=112) (joinSmall (lo:=11667) (a:=56) (b:=56) sp11667 sp11723) (joinSmall (lo:=11779) (a:=56) (b:=56) sp11779 sp11835)) (joinSmall (lo:=11891) (a:=112) (b:=113) (joinSmall (lo:=11891) (a:=56) (b:=56) sp11891 sp11947) (joinSmall (lo:=12003) (a:=56) (b:=57) sp12003 sp12059))) (joinSmall (lo:=12116) (a:=224) (b:=225) (joinSmall (lo:=12116) (a:=112) (b:=112) (joinSmall (lo:=12116) (a:=56) (b:=56) sp12116 sp12172) (joinSmall (lo:=12228) (a:=56) (b:=56) sp12228 sp12284)) (joinSmall (lo:=12340) (a:=112) (b:=113) (joinSmall (lo:=12340) (a:=56) (b:=56) sp12340 sp12396) (joinSmall (lo:=12452) (a:=56) (b:=57) sp12452 sp12508))))) (joinSmall (lo:=12565) (a:=898) (b:=898) (joinSmall (lo:=12565) (a:=449) (b:=449) (joinSmall (lo:=12565) (a:=224) (b:=225) (joinSmall (lo:=12565) (a:=112) (b:=112) (joinSmall (lo:=12565) (a:=56) (b:=56) sp12565 sp12621) (joinSmall (lo:=12677) (a:=56) (b:=56) sp12677 sp12733)) (joinSmall (lo:=12789) (a:=112) (b:=113) (joinSmall (lo:=12789) (a:=56) (b:=56) sp12789 sp12845) (joinSmall (lo:=12901) (a:=56) (b:=57) sp12901 sp12957))) (joinSmall (lo:=13014) (a:=224) (b:=225) (joinSmall (lo:=13014) (a:=112) (b:=112) (joinSmall (lo:=13014) (a:=56) (b:=56) sp13014 sp13070) (joinSmall (lo:=13126) (a:=56) (b:=56) sp13126 sp13182)) (joinSmall (lo:=13238) (a:=112) (b:=113) (joinSmall (lo:=13238) (a:=56) (b:=56) sp13238 sp13294) (joinSmall (lo:=13350) (a:=56) (b:=57) sp13350 sp13406)))) (joinSmall (lo:=13463) (a:=449) (b:=449) (joinSmall (lo:=13463) (a:=224) (b:=225) (joinSmall (lo:=13463) (a:=112) (b:=112) (joinSmall (lo:=13463) (a:=56) (b:=56) sp13463 sp13519) (joinSmall (lo:=13575) (a:=56) (b:=56) sp13575 sp13631)) (joinSmall (lo:=13687) (a:=112) (b:=113) (joinSmall (lo:=13687) (a:=56) (b:=56) sp13687 sp13743) (joinSmall (lo:=13799) (a:=56) (b:=57) sp13799 sp13855))) (joinSmall (lo:=13912) (a:=224) (b:=225) (joinSmall (lo:=13912) (a:=112) (b:=112) (joinSmall (lo:=13912) (a:=56) (b:=56) sp13912 sp13968) (joinSmall (lo:=14024) (a:=56) (b:=56) sp14024 sp14080)) (joinSmall (lo:=14136) (a:=112) (b:=113) (joinSmall (lo:=14136) (a:=56) (b:=56) sp14136 sp14192) (joinSmall (lo:=14248) (a:=56) (b:=57) sp14248 sp14304)))))))) (joinSmall (lo:=14361) (a:=7181) (b:=7181) (joinSmall (lo:=14361) (a:=3590) (b:=3591) (joinSmall (lo:=14361) (a:=1795) (b:=1795) (joinSmall (lo:=14361) (a:=897) (b:=898) (joinSmall (lo:=14361) (a:=448) (b:=449) (joinSmall (lo:=14361) (a:=224) (b:=224) (joinSmall (lo:=14361) (a:=112) (b:=112) (joinSmall (lo:=14361) (a:=56) (b:=56) sp14361 sp14417) (joinSmall (lo:=14473) (a:=56) (b:=56) sp14473 sp14529)) (joinSmall (lo:=14585) (a:=112) (b:=112) (joinSmall (lo:=14585) (a:=56) (b:=56) sp14585 sp14641) (joinSmall (lo:=14697) (a:=56) (b:=56) sp14697 sp14753))) (joinSmall (lo:=14809) (a:=224) (b:=225) (joinSmall (lo:=14809) (a:=112) (b:=112) (joinSmall (lo:=14809) (a:=56) (b:=56) sp14809 sp14865) (joinSmall (lo:=14921) (a:=56) (b:=56) sp14921 sp14977)) (joinSmall (lo:=15033) (a:=112) (b:=113) (joinSmall (lo:=15033) (a:=56) (b:=56) sp15033 sp15089) (joinSmall (lo:=15145) (a:=56) (b:=57) sp15145 sp15201)))) (joinSmall (lo:=15258) (a:=449) (b:=449) (joinSmall (lo:=15258) (a:=224) (b:=225) (joinSmall (lo:=15258) (a:=112) (b:=112) (joinSmall (lo:=15258) (a:=56) (b:=56) sp15258 sp15314) (joinSmall (lo:=15370) (a:=56) (b:=56) sp15370 sp15426)) (joinSmall (lo:=15482) (a:=112) (b:=113) (joinSmall (lo:=15482) (a:=56) (b:=56) sp15482 sp15538) (joinSmall (lo:=15594) (a:=56) (b:=57) sp15594 sp15650))) (joinSmall (lo:=15707) (a:=224) (b:=225) (joinSmall (lo:=15707) (a:=112) (b:=112) (joinSmall (lo:=15707) (a:=56) (b:=56) sp15707 sp15763) (joinSmall (lo:=15819) (a:=56) (b:=56) sp15819 sp15875)) (joinSmall (lo:=15931) (a:=112) (b:=113) (joinSmall (lo:=15931) (a:=56) (b:=56) sp15931 sp15987) (joinSmall (lo:=16043) (a:=56) (b:=57) sp16043 sp16099))))) (joinSmall (lo:=16156) (a:=897) (b:=898) (joinSmall (lo:=16156) (a:=448) (b:=449) (joinSmall (lo:=16156) (a:=224) (b:=224) (joinSmall (lo:=16156) (a:=112) (b:=112) (joinSmall (lo:=16156) (a:=56) (b:=56) sp16156 sp16212) (joinSmall (lo:=16268) (a:=56) (b:=56) sp16268 sp16324)) (joinSmall (lo:=16380) (a:=112) (b:=112) (joinSmall (lo:=16380) (a:=56) (b:=56) sp16380 sp16436) (joinSmall (lo:=16492) (a:=56) (b:=56) sp16492 sp16548))) (joinSmall (lo:=16604) (a:=224) (b:=225) (joinSmall (lo:=16604) (a:=112) (b:=112) (joinSmall (lo:=16604) (a:=56) (b:=56) sp16604 sp16660) (joinSmall (lo:=16716) (a:=56) (b:=56) sp16716 sp16772)) (joinSmall (lo:=16828) (a:=112) (b:=113) (joinSmall (lo:=16828) (a:=56) (b:=56) sp16828 sp16884) (joinSmall (lo:=16940) (a:=56) (b:=57) sp16940 sp16996)))) (joinSmall (lo:=17053) (a:=449) (b:=449) (joinSmall (lo:=17053) (a:=224) (b:=225) (joinSmall (lo:=17053) (a:=112) (b:=112) (joinSmall (lo:=17053) (a:=56) (b:=56) sp17053 sp17109) (joinSmall (lo:=17165) (a:=56) (b:=56) sp17165 sp17221)) (joinSmall (lo:=17277) (a:=112) (b:=113) (joinSmall (lo:=17277) (a:=56) (b:=56) sp17277 sp17333) (joinSmall (lo:=17389) (a:=56) (b:=57) sp17389 sp17445))) (joinSmall (lo:=17502) (a:=224) (b:=225) (joinSmall (lo:=17502) (a:=112) (b:=112) (joinSmall (lo:=17502) (a:=56) (b:=56) sp17502 sp17558) (joinSmall (lo:=17614) (a:=56) (b:=56) sp17614 sp17670)) (joinSmall (lo:=17726) (a:=112) (b:=113) (joinSmall (lo:=17726) (a:=56) (b:=56) sp17726 sp17782) (joinSmall (lo:=17838) (a:=56) (b:=57) sp17838 sp17894)))))) (joinSmall (lo:=17951) (a:=1795) (b:=1796) (joinSmall (lo:=17951) (a:=897) (b:=898) (joinSmall (lo:=17951) (a:=448) (b:=449) (joinSmall (lo:=17951) (a:=224) (b:=224) (joinSmall (lo:=17951) (a:=112) (b:=112) (joinSmall (lo:=17951) (a:=56) (b:=56) sp17951 sp18007) (joinSmall (lo:=18063) (a:=56) (b:=56) sp18063 sp18119)) (joinSmall (lo:=18175) (a:=112) (b:=112) (joinSmall (lo:=18175) (a:=56) (b:=56) sp18175 sp18231) (joinSmall (lo:=18287) (a:=56) (b:=56) sp18287 sp18343))) (joinSmall (lo:=18399) (a:=224) (b:=225) (joinSmall (lo:=18399) (a:=112) (b:=112) (joinSmall (lo:=18399) (a:=56) (b:=56) sp18399 sp18455) (joinSmall (lo:=18511) (a:=56) (b:=56) sp18511 sp18567)) (joinSmall (lo:=18623) (a:=112) (b:=113) (joinSmall (lo:=18623) (a:=56) (b:=56) sp18623 sp18679) (joinSmall (lo:=18735) (a:=56) (b:=57) sp18735 sp18791)))) (joinSmall (lo:=18848) (a:=449) (b:=449) (joinSmall (lo:=18848) (a:=224) (b:=225) (joinSmall (lo:=18848) (a:=112) (b:=112) (joinSmall (lo:=18848) (a:=56) (b:=56) sp18848 sp18904) (joinSmall (lo:=18960) (a:=56) (b:=56) sp18960 sp19016)) (joinSmall (lo:=19072) (a:=112) (b:=113) (joinSmall (lo:=19072) (a:=56) (b:=56) sp19072 sp19128) (joinSmall (lo:=19184) (a:=56) (b:=57) sp19184 sp19240))) (joinSmall (lo:=19297) (a:=224) (b:=225) (joinSmall (lo:=19297) (a:=112) (b:=112) (joinSmall (lo:=19297) (a:=56) (b:=56) sp19297 sp19353) (joinSmall (lo:=19409) (a:=56) (b:=56) sp19409 sp19465)) (joinSmall (lo:=19521) (a:=112) (b:=113) (joinSmall (lo:=19521) (a:=56) (b:=56) sp19521 sp19577) (joinSmall (lo:=19633) (a:=56) (b:=57) sp19633 sp19689))))) (joinSmall (lo:=19746) (a:=898) (b:=898) (joinSmall (lo:=19746) (a:=449) (b:=449) (joinSmall (lo:=19746) (a:=224) (b:=225) (joinSmall (lo:=19746) (a:=112) (b:=112) (joinSmall (lo:=19746) (a:=56) (b:=56) sp19746 sp19802) (joinSmall (lo:=19858) (a:=56) (b:=56) sp19858 sp19914)) (joinSmall (lo:=19970) (a:=112) (b:=113) (joinSmall (lo:=19970) (a:=56) (b:=56) sp19970 sp20026) (joinSmall (lo:=20082) (a:=56) (b:=57) sp20082 sp20138))) (joinSmall (lo:=20195) (a:=224) (b:=225) (joinSmall (lo:=20195) (a:=112) (b:=112) (joinSmall (lo:=20195) (a:=56) (b:=56) sp20195 sp20251) (joinSmall (lo:=20307) (a:=56) (b:=56) sp20307 sp20363)) (joinSmall (lo:=20419) (a:=112) (b:=113) (joinSmall (lo:=20419) (a:=56) (b:=56) sp20419 sp20475) (joinSmall (lo:=20531) (a:=56) (b:=57) sp20531 sp20587)))) (joinSmall (lo:=20644) (a:=449) (b:=449) (joinSmall (lo:=20644) (a:=224) (b:=225) (joinSmall (lo:=20644) (a:=112) (b:=112) (joinSmall (lo:=20644) (a:=56) (b:=56) sp20644 sp20700) (joinSmall (lo:=20756) (a:=56) (b:=56) sp20756 sp20812)) (joinSmall (lo:=20868) (a:=112) (b:=113) (joinSmall (lo:=20868) (a:=56) (b:=56) sp20868 sp20924) (joinSmall (lo:=20980) (a:=56) (b:=57) sp20980 sp21036))) (joinSmall (lo:=21093) (a:=224) (b:=225) (joinSmall (lo:=21093) (a:=112) (b:=112) (joinSmall (lo:=21093) (a:=56) (b:=56) sp21093 sp21149) (joinSmall (lo:=21205) (a:=56) (b:=56) sp21205 sp21261)) (joinSmall (lo:=21317) (a:=112) (b:=113) (joinSmall (lo:=21317) (a:=56) (b:=56) sp21317 sp21373) (joinSmall (lo:=21429) (a:=56) (b:=57) sp21429 sp21485))))))) (joinSmall (lo:=21542) (a:=3590) (b:=3591) (joinSmall (lo:=21542) (a:=1795) (b:=1795) (joinSmall (lo:=21542) (a:=897) (b:=898) (joinSmall (lo:=21542) (a:=448) (b:=449) (joinSmall (lo:=21542) (a:=224) (b:=224) (joinSmall (lo:=21542) (a:=112) (b:=112) (joinSmall (lo:=21542) (a:=56) (b:=56) sp21542 sp21598) (joinSmall (lo:=21654) (a:=56) (b:=56) sp21654 sp21710)) (joinSmall (lo:=21766) (a:=112) (b:=112) (joinSmall (lo:=21766) (a:=56) (b:=56) sp21766 sp21822) (joinSmall (lo:=21878) (a:=56) (b:=56) sp21878 sp21934))) (joinSmall (lo:=21990) (a:=224) (b:=225) (joinSmall (lo:=21990) (a:=112) (b:=112) (joinSmall (lo:=21990) (a:=56) (b:=56) sp21990 sp22046) (joinSmall (lo:=22102) (a:=56) (b:=56) sp22102 sp22158)) (joinSmall (lo:=22214) (a:=112) (b:=113) (joinSmall (lo:=22214) (a:=56) (b:=56) sp22214 sp22270) (joinSmall (lo:=22326) (a:=56) (b:=57) sp22326 sp22382)))) (joinSmall (lo:=22439) (a:=449) (b:=449) (joinSmall (lo:=22439) (a:=224) (b:=225) (joinSmall (lo:=22439) (a:=112) (b:=112) (joinSmall (lo:=22439) (a:=56) (b:=56) sp22439 sp22495) (joinSmall (lo:=22551) (a:=56) (b:=56) sp22551 sp22607)) (joinSmall (lo:=22663) (a:=112) (b:=113) (joinSmall (lo:=22663) (a:=56) (b:=56) sp22663 sp22719) (joinSmall (lo:=22775) (a:=56) (b:=57) sp22775 sp22831))) (joinSmall (lo:=22888) (a:=224) (b:=225) (joinSmall (lo:=22888) (a:=112) (b:=112) (joinSmall (lo:=22888) (a:=56) (b:=56) sp22888 sp22944) (joinSmall (lo:=23000) (a:=56) (b:=56) sp23000 sp23056)) (joinSmall (lo:=23112) (a:=112) (b:=113) (joinSmall (lo:=23112) (a:=56) (b:=56) sp23112 sp23168) (joinSmall (lo:=23224) (a:=56) (b:=57) sp23224 sp23280))))) (joinSmall (lo:=23337) (a:=897) (b:=898) (joinSmall (lo:=23337) (a:=448) (b:=449) (joinSmall (lo:=23337) (a:=224) (b:=224) (joinSmall (lo:=23337) (a:=112) (b:=112) (joinSmall (lo:=23337) (a:=56) (b:=56) sp23337 sp23393) (joinSmall (lo:=23449) (a:=56) (b:=56) sp23449 sp23505)) (joinSmall (lo:=23561) (a:=112) (b:=112) (joinSmall (lo:=23561) (a:=56) (b:=56) sp23561 sp23617) (joinSmall (lo:=23673) (a:=56) (b:=56) sp23673 sp23729))) (joinSmall (lo:=23785) (a:=224) (b:=225) (joinSmall (lo:=23785) (a:=112) (b:=112) (joinSmall (lo:=23785) (a:=56) (b:=56) sp23785 sp23841) (joinSmall (lo:=23897) (a:=56) (b:=56) sp23897 sp23953)) (joinSmall (lo:=24009) (a:=112) (b:=113) (joinSmall (lo:=24009) (a:=56) (b:=56) sp24009 sp24065) (joinSmall (lo:=24121) (a:=56) (b:=57) sp24121 sp24177)))) (joinSmall (lo:=24234) (a:=449) (b:=449) (joinSmall (lo:=24234) (a:=224) (b:=225) (joinSmall (lo:=24234) (a:=112) (b:=112) (joinSmall (lo:=24234) (a:=56) (b:=56) sp24234 sp24290) (joinSmall (lo:=24346) (a:=56) (b:=56) sp24346 sp24402)) (joinSmall (lo:=24458) (a:=112) (b:=113) (joinSmall (lo:=24458) (a:=56) (b:=56) sp24458 sp24514) (joinSmall (lo:=24570) (a:=56) (b:=57) sp24570 sp24626))) (joinSmall (lo:=24683) (a:=224) (b:=225) (joinSmall (lo:=24683) (a:=112) (b:=112) (joinSmall (lo:=24683) (a:=56) (b:=56) sp24683 sp24739) (joinSmall (lo:=24795) (a:=56) (b:=56) sp24795 sp24851)) (joinSmall (lo:=24907) (a:=112) (b:=113) (joinSmall (lo:=24907) (a:=56) (b:=56) sp24907 sp24963) (joinSmall (lo:=25019) (a:=56) (b:=57) sp25019 sp25075)))))) (joinSmall (lo:=25132) (a:=1795) (b:=1796) (joinSmall (lo:=25132) (a:=897) (b:=898) (joinSmall (lo:=25132) (a:=448) (b:=449) (joinSmall (lo:=25132) (a:=224) (b:=224) (joinSmall (lo:=25132) (a:=112) (b:=112) (joinSmall (lo:=25132) (a:=56) (b:=56) sp25132 sp25188) (joinSmall (lo:=25244) (a:=56) (b:=56) sp25244 sp25300)) (joinSmall (lo:=25356) (a:=112) (b:=112) (joinSmall (lo:=25356) (a:=56) (b:=56) sp25356 sp25412) (joinSmall (lo:=25468) (a:=56) (b:=56) sp25468 sp25524))) (joinSmall (lo:=25580) (a:=224) (b:=225) (joinSmall (lo:=25580) (a:=112) (b:=112) (joinSmall (lo:=25580) (a:=56) (b:=56) sp25580 sp25636) (joinSmall (lo:=25692) (a:=56) (b:=56) sp25692 sp25748)) (joinSmall (lo:=25804) (a:=112) (b:=113) (joinSmall (lo:=25804) (a:=56) (b:=56) sp25804 sp25860) (joinSmall (lo:=25916) (a:=56) (b:=57) sp25916 sp25972)))) (joinSmall (lo:=26029) (a:=449) (b:=449) (joinSmall (lo:=26029) (a:=224) (b:=225) (joinSmall (lo:=26029) (a:=112) (b:=112) (joinSmall (lo:=26029) (a:=56) (b:=56) sp26029 sp26085) (joinSmall (lo:=26141) (a:=56) (b:=56) sp26141 sp26197)) (joinSmall (lo:=26253) (a:=112) (b:=113) (joinSmall (lo:=26253) (a:=56) (b:=56) sp26253 sp26309) (joinSmall (lo:=26365) (a:=56) (b:=57) sp26365 sp26421))) (joinSmall (lo:=26478) (a:=224) (b:=225) (joinSmall (lo:=26478) (a:=112) (b:=112) (joinSmall (lo:=26478) (a:=56) (b:=56) sp26478 sp26534) (joinSmall (lo:=26590) (a:=56) (b:=56) sp26590 sp26646)) (joinSmall (lo:=26702) (a:=112) (b:=113) (joinSmall (lo:=26702) (a:=56) (b:=56) sp26702 sp26758) (joinSmall (lo:=26814) (a:=56) (b:=57) sp26814 sp26870))))) (joinSmall (lo:=26927) (a:=898) (b:=898) (joinSmall (lo:=26927) (a:=449) (b:=449) (joinSmall (lo:=26927) (a:=224) (b:=225) (joinSmall (lo:=26927) (a:=112) (b:=112) (joinSmall (lo:=26927) (a:=56) (b:=56) sp26927 sp26983) (joinSmall (lo:=27039) (a:=56) (b:=56) sp27039 sp27095)) (joinSmall (lo:=27151) (a:=112) (b:=113) (joinSmall (lo:=27151) (a:=56) (b:=56) sp27151 sp27207) (joinSmall (lo:=27263) (a:=56) (b:=57) sp27263 sp27319))) (joinSmall (lo:=27376) (a:=224) (b:=225) (joinSmall (lo:=27376) (a:=112) (b:=112) (joinSmall (lo:=27376) (a:=56) (b:=56) sp27376 sp27432) (joinSmall (lo:=27488) (a:=56) (b:=56) sp27488 sp27544)) (joinSmall (lo:=27600) (a:=112) (b:=113) (joinSmall (lo:=27600) (a:=56) (b:=56) sp27600 sp27656) (joinSmall (lo:=27712) (a:=56) (b:=57) sp27712 sp27768)))) (joinSmall (lo:=27825) (a:=449) (b:=449) (joinSmall (lo:=27825) (a:=224) (b:=225) (joinSmall (lo:=27825) (a:=112) (b:=112) (joinSmall (lo:=27825) (a:=56) (b:=56) sp27825 sp27881) (joinSmall (lo:=27937) (a:=56) (b:=56) sp27937 sp27993)) (joinSmall (lo:=28049) (a:=112) (b:=113) (joinSmall (lo:=28049) (a:=56) (b:=56) sp28049 sp28105) (joinSmall (lo:=28161) (a:=56) (b:=57) sp28161 sp28217))) (joinSmall (lo:=28274) (a:=224) (b:=225) (joinSmall (lo:=28274) (a:=112) (b:=112) (joinSmall (lo:=28274) (a:=56) (b:=56) sp28274 sp28330) (joinSmall (lo:=28386) (a:=56) (b:=56) sp28386 sp28442)) (joinSmall (lo:=28498) (a:=112) (b:=113) (joinSmall (lo:=28498) (a:=56) (b:=56) sp28498 sp28554) (joinSmall (lo:=28610) (a:=56) (b:=57) sp28610 sp28666)))))))))
  have good : (List.range 28723).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 825000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 28722 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 28722 := by
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


private def packet (i : ℕ) : ℕ := (if i < 210 then (if i < 105 then (if i < 52 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 4 then 0 else (if i < 5 then 0 else 0))) else (if i < 9 then (if i < 7 then 0 else (if i < 8 then 0 else 0)) else (if i < 11 then (if i < 10 then 0 else 0) else (if i < 12 then 0 else 0)))) else (if i < 19 then (if i < 16 then (if i < 14 then 0 else (if i < 15 then 0 else 0)) else (if i < 17 then 0 else (if i < 18 then 0 else 0))) else (if i < 22 then (if i < 20 then 0 else (if i < 21 then 0 else 0)) else (if i < 24 then (if i < 23 then 0 else 0) else (if i < 25 then 0 else 0))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then 0 else (if i < 28 then 0 else 0)) else (if i < 30 then 0 else (if i < 31 then 0 else 0))) else (if i < 35 then (if i < 33 then 0 else (if i < 34 then 0 else 0)) else (if i < 37 then (if i < 36 then 0 else 0) else (if i < 38 then 0 else 0)))) else (if i < 45 then (if i < 42 then (if i < 40 then 0 else (if i < 41 then 0 else 0)) else (if i < 43 then 0 else (if i < 44 then 0 else 0))) else (if i < 48 then (if i < 46 then 0 else (if i < 47 then 0 else 0)) else (if i < 50 then (if i < 49 then 0 else 0) else (if i < 51 then 0 else 0)))))) else (if i < 78 then (if i < 65 then (if i < 58 then (if i < 55 then (if i < 53 then 0 else (if i < 54 then 0 else 0)) else (if i < 56 then 0 else (if i < 57 then 0 else 0))) else (if i < 61 then (if i < 59 then 0 else (if i < 60 then 0 else 0)) else (if i < 63 then (if i < 62 then 0 else 0) else (if i < 64 then 0 else 0)))) else (if i < 71 then (if i < 68 then (if i < 66 then 0 else (if i < 67 then 0 else 0)) else (if i < 69 then 0 else (if i < 70 then 0 else 0))) else (if i < 74 then (if i < 72 then 0 else (if i < 73 then 0 else 0)) else (if i < 76 then (if i < 75 then 0 else 0) else (if i < 77 then 0 else 0))))) else (if i < 91 then (if i < 84 then (if i < 81 then (if i < 79 then 0 else (if i < 80 then 0 else 0)) else (if i < 82 then 0 else (if i < 83 then 0 else 0))) else (if i < 87 then (if i < 85 then 0 else (if i < 86 then 0 else 0)) else (if i < 89 then (if i < 88 then 0 else 0) else (if i < 90 then 0 else 0)))) else (if i < 98 then (if i < 94 then (if i < 92 then 0 else (if i < 93 then 0 else 0)) else (if i < 96 then (if i < 95 then 0 else 0) else (if i < 97 then 0 else 0))) else (if i < 101 then (if i < 99 then 0 else (if i < 100 then 0 else 0)) else (if i < 103 then (if i < 102 then 0 else 0) else (if i < 104 then 0 else 0))))))) else (if i < 157 then (if i < 131 then (if i < 118 then (if i < 111 then (if i < 108 then (if i < 106 then 0 else (if i < 107 then 0 else 0)) else (if i < 109 then 0 else (if i < 110 then 0 else 0))) else (if i < 114 then (if i < 112 then 0 else (if i < 113 then 0 else 0)) else (if i < 116 then (if i < 115 then 0 else 0) else (if i < 117 then 0 else 0)))) else (if i < 124 then (if i < 121 then (if i < 119 then 0 else (if i < 120 then 0 else 0)) else (if i < 122 then 0 else (if i < 123 then 0 else 0))) else (if i < 127 then (if i < 125 then 0 else (if i < 126 then 0 else 0)) else (if i < 129 then (if i < 128 then 0 else 0) else (if i < 130 then 0 else 0))))) else (if i < 144 then (if i < 137 then (if i < 134 then (if i < 132 then 0 else (if i < 133 then 0 else 0)) else (if i < 135 then 0 else (if i < 136 then 0 else 0))) else (if i < 140 then (if i < 138 then 0 else (if i < 139 then 0 else 0)) else (if i < 142 then (if i < 141 then 0 else 0) else (if i < 143 then 0 else 0)))) else (if i < 150 then (if i < 147 then (if i < 145 then 0 else (if i < 146 then 0 else 0)) else (if i < 148 then 0 else (if i < 149 then 0 else 0))) else (if i < 153 then (if i < 151 then 0 else (if i < 152 then 0 else 0)) else (if i < 155 then (if i < 154 then 0 else 0) else (if i < 156 then 0 else 0)))))) else (if i < 183 then (if i < 170 then (if i < 163 then (if i < 160 then (if i < 158 then 0 else (if i < 159 then 0 else 0)) else (if i < 161 then 0 else (if i < 162 then 0 else 0))) else (if i < 166 then (if i < 164 then 0 else (if i < 165 then 0 else 0)) else (if i < 168 then (if i < 167 then 0 else 0) else (if i < 169 then 0 else 0)))) else (if i < 176 then (if i < 173 then (if i < 171 then 0 else (if i < 172 then 0 else 0)) else (if i < 174 then 0 else (if i < 175 then 0 else 0))) else (if i < 179 then (if i < 177 then 0 else (if i < 178 then 0 else 0)) else (if i < 181 then (if i < 180 then 0 else 0) else (if i < 182 then 0 else 0))))) else (if i < 196 then (if i < 189 then (if i < 186 then (if i < 184 then 0 else (if i < 185 then 0 else 0)) else (if i < 187 then 0 else (if i < 188 then 0 else 0))) else (if i < 192 then (if i < 190 then 0 else (if i < 191 then 0 else 0)) else (if i < 194 then (if i < 193 then 0 else 0) else (if i < 195 then 0 else 0)))) else (if i < 203 then (if i < 199 then (if i < 197 then 0 else (if i < 198 then 0 else 0)) else (if i < 201 then (if i < 200 then 0 else 0) else (if i < 202 then 0 else 0))) else (if i < 206 then (if i < 204 then 0 else (if i < 205 then 0 else 0)) else (if i < 208 then (if i < 207 then 0 else 0) else (if i < 209 then 0 else 0)))))))) else (if i < 315 then (if i < 262 then (if i < 236 then (if i < 223 then (if i < 216 then (if i < 213 then (if i < 211 then 0 else (if i < 212 then 0 else 0)) else (if i < 214 then 0 else (if i < 215 then 0 else 0))) else (if i < 219 then (if i < 217 then 0 else (if i < 218 then 0 else 0)) else (if i < 221 then (if i < 220 then 0 else 0) else (if i < 222 then 0 else 0)))) else (if i < 229 then (if i < 226 then (if i < 224 then 0 else (if i < 225 then 0 else 0)) else (if i < 227 then 0 else (if i < 228 then 0 else 0))) else (if i < 232 then (if i < 230 then 0 else (if i < 231 then 0 else 0)) else (if i < 234 then (if i < 233 then 0 else 0) else (if i < 235 then 0 else 0))))) else (if i < 249 then (if i < 242 then (if i < 239 then (if i < 237 then 0 else (if i < 238 then 0 else 0)) else (if i < 240 then 0 else (if i < 241 then 0 else 0))) else (if i < 245 then (if i < 243 then 0 else (if i < 244 then 0 else 0)) else (if i < 247 then (if i < 246 then 0 else 0) else (if i < 248 then 0 else 0)))) else (if i < 255 then (if i < 252 then (if i < 250 then 0 else (if i < 251 then 0 else 0)) else (if i < 253 then 0 else (if i < 254 then 0 else 0))) else (if i < 258 then (if i < 256 then 0 else (if i < 257 then 0 else 0)) else (if i < 260 then (if i < 259 then 0 else 0) else (if i < 261 then 0 else 0)))))) else (if i < 288 then (if i < 275 then (if i < 268 then (if i < 265 then (if i < 263 then 0 else (if i < 264 then 0 else 0)) else (if i < 266 then 0 else (if i < 267 then 0 else 0))) else (if i < 271 then (if i < 269 then 0 else (if i < 270 then 0 else 0)) else (if i < 273 then (if i < 272 then 0 else 0) else (if i < 274 then 0 else 0)))) else (if i < 281 then (if i < 278 then (if i < 276 then 0 else (if i < 277 then 0 else 0)) else (if i < 279 then 0 else (if i < 280 then 0 else 0))) else (if i < 284 then (if i < 282 then 0 else (if i < 283 then 0 else 0)) else (if i < 286 then (if i < 285 then 0 else 0) else (if i < 287 then 0 else 0))))) else (if i < 301 then (if i < 294 then (if i < 291 then (if i < 289 then 0 else (if i < 290 then 0 else 0)) else (if i < 292 then 0 else (if i < 293 then 0 else 0))) else (if i < 297 then (if i < 295 then 0 else (if i < 296 then 0 else 0)) else (if i < 299 then (if i < 298 then 0 else 0) else (if i < 300 then 0 else 0)))) else (if i < 308 then (if i < 304 then (if i < 302 then 0 else (if i < 303 then 0 else 0)) else (if i < 306 then (if i < 305 then 0 else 0) else (if i < 307 then 0 else 0))) else (if i < 311 then (if i < 309 then 0 else (if i < 310 then 0 else 0)) else (if i < 313 then (if i < 312 then 0 else 0) else (if i < 314 then 0 else 0))))))) else (if i < 367 then (if i < 341 then (if i < 328 then (if i < 321 then (if i < 318 then (if i < 316 then 0 else (if i < 317 then 0 else 0)) else (if i < 319 then 0 else (if i < 320 then 0 else 0))) else (if i < 324 then (if i < 322 then 0 else (if i < 323 then 0 else 0)) else (if i < 326 then (if i < 325 then 0 else 0) else (if i < 327 then 0 else 0)))) else (if i < 334 then (if i < 331 then (if i < 329 then 0 else (if i < 330 then 0 else 0)) else (if i < 332 then 0 else (if i < 333 then 0 else 0))) else (if i < 337 then (if i < 335 then 0 else (if i < 336 then 0 else 0)) else (if i < 339 then (if i < 338 then 0 else 0) else (if i < 340 then 0 else 0))))) else (if i < 354 then (if i < 347 then (if i < 344 then (if i < 342 then 0 else (if i < 343 then 0 else 0)) else (if i < 345 then 0 else (if i < 346 then 0 else 0))) else (if i < 350 then (if i < 348 then 0 else (if i < 349 then 0 else 0)) else (if i < 352 then (if i < 351 then 0 else 0) else (if i < 353 then 0 else 0)))) else (if i < 360 then (if i < 357 then (if i < 355 then 0 else (if i < 356 then 0 else 0)) else (if i < 358 then 0 else (if i < 359 then 0 else 0))) else (if i < 363 then (if i < 361 then 0 else (if i < 362 then 0 else 0)) else (if i < 365 then (if i < 364 then 0 else 0) else (if i < 366 then 0 else 0)))))) else (if i < 393 then (if i < 380 then (if i < 373 then (if i < 370 then (if i < 368 then 0 else (if i < 369 then 0 else 0)) else (if i < 371 then 0 else (if i < 372 then 0 else 0))) else (if i < 376 then (if i < 374 then 0 else (if i < 375 then 0 else 0)) else (if i < 378 then (if i < 377 then 0 else 0) else (if i < 379 then 0 else 0)))) else (if i < 386 then (if i < 383 then (if i < 381 then 0 else (if i < 382 then 0 else 0)) else (if i < 384 then 0 else (if i < 385 then 0 else 0))) else (if i < 389 then (if i < 387 then 0 else (if i < 388 then 0 else 0)) else (if i < 391 then (if i < 390 then 0 else 0) else (if i < 392 then 0 else 0))))) else (if i < 406 then (if i < 399 then (if i < 396 then (if i < 394 then 0 else (if i < 395 then 0 else 0)) else (if i < 397 then 0 else (if i < 398 then 0 else 0))) else (if i < 402 then (if i < 400 then 0 else (if i < 401 then 0 else 0)) else (if i < 404 then (if i < 403 then 0 else 0) else (if i < 405 then 0 else 0)))) else (if i < 413 then (if i < 409 then (if i < 407 then 0x273f6c22b8945c97445e1ff0e646782e7140889838e16e08d82f00c20000273f0d42c714ac99a4692020ea86922e213f089839e17108c83100d20000273eaec2c494b49a646d20a0ee86a62fe14d08e43bc180092032c0d80000273e4f02cd94d09be4842160f106d030815188f03a817408e030c0a40000273df2f2af13fc93c4471f38e2865e2d013a886837816608402bc0ae0000273d9492bf94789784652030ebc6b630715489143b818008f03100c20000273d3592c994ac9864632078e9069a2ef14d09283c218809102ec0b80000273cd7d2c194b49ac4722090ef86ca30715189343c818d09883300c80000273c7bf2af93ec93a4481f10e006562cf13d886838616908582b40c60000273c2002b994a898e4602030ea067e2e914788cc3b018208e02d80c00000273bc472a913f495044c1f80e5c68c2f214808b03a617308a02f40b20000273b6512cd94dc9bc4802100f006c830014c88d43b217e09483200c60000273b08e2b1141894c4461ee8ddc64a2c5139885038816008582f00ae0000273aaaf2bf94809824581f78e506662d913f088039816e08582e40b00000273a49e2d215149c047520f8f006c22f714f08e43a817909083100d000002739ed82b2142897a4612070ecc6a02fc14788a838616f08882dc0c4000027398fc2c2149c9b047420d0ed06a22f114608d03ac17409003000c80000273930a2cf14fc9b847b2120f386d230615989543e618d09102fc0c000002738d3c2b314289824652060ed46b62f814808c43b817e09102f40bc0000273876e2b8144c9664592028e906a62ee14588b83ae17508c03080be000027381ac2b3145895e4511f60e3865e2d613a887c39617708a82f00b800002737bc52c194a097a4591fc8e6467c2de14408c03a616f08e83000a60000273760c2b3943897244b1f78e386722e314208c83ac17908902b00b40000273706d2a093749044271e28d886102ac128082036e16407f02d40ae00002736a672d094f899845b1fd8ea86882eb146089c3b218609483080c4000027364bc2a913dc94a44d1fc0e6c6862f414a08e83c217d09182f00d200002735f162aa13f09484491f48e386622db14088b439616e08702cc0cc000027359512b1943495644f1f80e5c6682e414788b43a017908902dc0b4000027353842b814709744581ff8e6066a2d614088a839a16c08982f40bc00002734dba2b294049404501fe0e686702dc13e087c38416608b82e00b6000027347f82b213d893a4431f80e4c6602da142889c39e17408c03040b80000273422d2b994449464471f38e406662d413a887037a16908502c80aa00002733c492c4147c98a46a2070eac69a2e814188bc3a817a08c02e40c00000273365e2c714d09b447320e0f2c6c630315289343dc18509583000d0000027330992b5144095e4551fd8e6066a2e0144088838e16608002940ae00002732aaf2c794c89ac47d20b8eec6c02f614e88f83d218f093032c0e4000027324c82bf94749704622010e846882ea14a88d43a417709083180d000002731f142a793c89344241e50db863c2bf137084c36815908602e009e000027319472bd149098246b2030e9469e2f614909003d0187095830c0ce000027313802b113fc94843f1f50e4065e2d814108bc3aa17408c82fc0bc00002730dc72aa94049324421f00df86402c0132083037c15b08182d80ba000027308042b2141895a4501f58e5067a2da148089438017308f82e40ca000027302252bf146098e46c2090ec86a22fb15088f43c818b09582fc0cc0000272fc6c2b5140895044c1fb8e2866a2d313f887438c16608802bc0b40000272f6b02b093ec94e4451f80e6866c2d0138085837216008082a80a00000272f0e82b3142095c44c1f60e6c67e2e614408b83ac17c08f030c0bc0000272eb172b5944096c4511ff8e8067a2e9141887838016b08a02f80bc0000272e5002da95689e24942190f6c6fc31a15b89603f019309403100b80000272df072ca94d499a46d20a8ef86be2fe15209203c418209283140c20000272d94d2b0142494c4401f50e7c68c2e915088f03b417c08c82e80c00000272d36e2c314b498a45f2020ea86862ec14488cc3a417708c03140ba0000272cd8d2c2947c98245d1fe0e786802f214e88f03be18308e83000b60000272c7ab2c294c09a64742070edc6c430a15689283e618d09682f40bc0000272c1c72bf146c99846e2098eb469c2f114f89003be17708982dc0b60000272bbde2ca94d49c048c2108f186d830714f090c3bc18208d82e40b40000272b5e72d1150c9ba47a2088edc6ac2f914a88ec3ae17508682bc0a40000272b0152ba14749764652068e986a42ef14a88cc3aa17708c82ec0b40000272aa612ac94089504571fa8e7866e2d013c883435c15d08382b40b40000272a4772c794bc9a647f2150f286d631215a09403d818b092031c0c800002729e822c814e09d247b2058ee86b82f215089203d018a09483180cc0000272989d2c1148c98c46e2070eb86ac2f314808d439616808982c00b8000027292a82ce95149bc47b2098ed86ac30615609403d018809302fc0ba00002728c9f2d195309d249721a8f806f831315488f43c818209103440ce0000272868c2dd15709fc49c21d8f586f630f15489203bc183098032c0c6000 else (if i < 408 then 0x2756da22b694149504541fd0e6c6782dc13b887038216d08502e40b0000027567c02bb94589804612048ea86a02f514c08f03c017908d82fc0c6000027561fc2b514789804611fc0e6067c2e014108b03a217808f82f00c000002755bee2d194fc9c24852158f146ce30a15789203da18d09703140d20000275562b2b514249584471f20e186522c4135883835e15c08882a80a8000027550432c314a49a647720c8ed86be30115389243da18f09803140b600002754a7c2b514249784571fc8e6c67e2df140889039a16807e82a809e000027544ab2bb145895c44d1fd8e646862db13d887037216108382e00c200002753eea2b3145c9784591fb8e7c67a2ef14908d43b617d08e03080bc000027539132bc946c9944692028eb46a630214d88d83bc17f09182ec0c2000027533112d415009c448c2178f106ba30a154893c3dc19509883380d200002752d642ac13f094244b1f90e446682d513d887c3a616f08782f80b2000027527862c0148c9864651fc0e6c65e2e0145089c39c16d08802d40aa000027521ac2c1148c98646b2070eb06962e614408b03aa17a08d02ec0cc00002751bdf2b594189524531f40e486722dc14308c03a617309102f00ca0000275161f2b314209744591fe0e606762d814388a038c17208982e80b4000027510742a993ec92e4331f00e1465c2d713b888c38e16f08c82fc0c400002750a7c2ce95049bc47e20e0eb86a62ec14a08e83c818508f82f40b0000027504982c594d499c46f2040ebc6ac2f714a88cc3aa17c08c82e40be0000274fedc2b4943095044c1fc8e586622d713d888c39616d08902e00be0000274f8f62c594b09aa46e20b0edc6aa2ee14b88d03a617f08a02f00c20000274f2f32d295309d04852110f0c6c230315009143d218409983640de0000274ecf02d615289dc49721a8f546fa32715e894c3d618409282fc0ac0000274e7272bc145c97a45e2000ea46a02f215009083cc18609102dc0aa0000274e1562b6941c94a4341eb0df86382c313a084437415d08782d00be0000274db7b2bd147498045d1ff8e706882f614b88e83bc18609603200ca0000274d5c92b3144c96844b1f58e4066a2d913e087037e16708582fc0bc0000274cfda2c794cc9964712058e986862e814388cc3d218108f02e40b40000274c9ef2ca94f49ba4822150f046b030715409183e018c094831c0ba0000274c40d2c394a49964642028ea06982ed14608e43ae17608c83100c00000274be132cb94c89ac48020c8f186d230414f88e83d419309383100c40000274b7e12e995b09fe48f2170f246d430b15a096c3f219309403180cc0000274b1e42ce14ec9b246d2040eac67a2e014808bc39016a08402cc0b00000274abfb2c594d899446e2088ee06b62f514908c83b418208f83080c00000274a6462a893d493843f1f30e246642df14088bc39216a08882c40bc0000274a0892af94049584521f98e2c65c2c913b086c38216b08b82e809a00002749a932cf14fc9c04822120efc6d430c15409303d4189096030c0d8000027494cf2b4945097a4632058ec46922e514c08d439817308c031c0da00002748eee2bd147899646f20e8f046b82fd154091c3c817e08a02f00bc000027489292b514249604531f90e606702d514088943aa16f08502a40ae000027483532bc949097e4632050ec06a830515009103c4182093031c0c200002747d5d2ce15109c447720a0eac6a62e914888b83ba17708e02dc0b80000274778e2be14b09984692030e8868c2ec14808fc3ac17208482dc0b2000027471952cc951c9d648b2168f386c830215589303e219509903240cc00002746bc92b7945496a45d1fe0e8c67c2e014108b038816a08782e00b6000027465f32bc149c99c4672090e9869a2f915088d83ac17008882c40ba0000274600c2c694c49bc4832128f346d831015809383d419009d83540d0000027459f92dc1584a064a62218f686e830f15789183d818a09703200c0000027454092cd15149d44822110f146ac2fc14d08c039816d08082a00a400002744e6e2a693e094a4421f50e486642d0139885c38416208702d40a6000027448a22b2940c9384461f18e1c6642da13c885c39416807e82d40b0000027442c32c594ac9a24692068ec06a02f214b88f03c217b09202f40c200002743ce82bf947098045c2030e886842e9142889839c16508782a40a0000027437292b1940894844f1fb0e646622d613f088c39c17508a02b40b6000027431692b6944c9744561fc0ea068a2ea141887839217108902e80d000002742b9a2b9144c9624551fd8e486662d613f888437816708402f00ba0000274259e2cf95009cc48620c8ee06b42f514b88c43b617b08a02d80a000002741fcd2b514609744601fc8e5466c2df13e085c37616608502c80a6000027419df2c514b499847020a8ecc6ac2fe15488e439c17108e82d00b2000027413e02ca14d89bc4702098ee86a62f914888c439c16a08882f40ba00002740e242ae13f092e43a1ef0e0466c2df143889039016c08983080c2000027408562bf14a498c4662038eb06b630015088e03a817108902e00c2000027402952b2941895644f1f68e586782ef14988e83a817608902f40bc0000273fc952cf151c9e24952160f5c6e231b15709143d618c09202e40c4000 else 0x276e3212c894ac9ae4712038edc6ba30114b88b439017208a82d00b00000276dd562b9946095844d1f48e2c6662d3137085c37815d07b027409a0000276d7822be144c97c4602048ea46b02f914f89143da18a09203080c40000276d1b32ba946496a4572048ed06b22f514f88dc3b217f08f03080c60000276cbbe2cf94d49c046d20c0ea46802de14408ac39617008e02e80b00000276c6132ac940094443c1f78e6c68a2e214108a43a817608682c009c0000276c0182ca14e099e47e20b8ee06d030214a08a83a617508682e40b60000276ba422b614509584501fc0e9868e2f414d88f43be18008f83200d20000276b49b2ad14049464401f08e3c6662e014508c839e16d08c02fc0bc0000276aeba2c394989a647d20d8ef06bc2fe14f09303cc18d09202f80bc0000276a8e02c0149099c4732068ecc6ae2f914e88e03ae17708802fc0b00000276a3332ad93ec95644c1ff0e686742da141087037e16108782d40b200002769d482ca14e89b647e20d0ee06a82f314908b83a417808f82e80bc000027697662c794d89ba4702090ed067c2dc142089c3a618009103000d00000276917b2c514dc9a64652068e906942ef14c08b43ae17b09002e00c600002768ba22b8946897a45a2040e9869a2df13e089c39c17408c02c80a8000027685eb2b1141c96c45b1ff8e7c6842ec14808fc3ca17b09382dc0c4000027680212bc947898a4601ff0e5c6702da13a086036e16308682d40b400002767a1e2d194e09ac46a2058eec6c22fb14c08c439616f08d82fc0b4000027674612ac140093443d1ed0df46462d0139088037c16308482d00ba00002766e922b8145c97e4652038eb06982e014308983a817108982f40be000027668992d1150c9b44682008e8068a2f814b88b438816508582dc0c0000027662b22c7148c9964732088ec46b82fa14d88f83ae17d090031c0c800002765cf02b494249584531fe8e9069a2f414688c43aa17508c82ec0ba0000276570e2b9945496e4521fc0e6867e2e614888ec3b217e09182d40bc000027651322bd94609784611ff8e7867a2da14108b03a818209303180ce00002764b702b6943496444f1f98e706762dd13a889c39417608e82dc0bc000027645692d6953c9e84962188f4871432416309883f6191099834c0cc00002763f8e2be149099246a2060eac6862e314608b83a817408d02dc0a8000027639b72c214b89a647c20c0ee46a82e814708b439816d08e82f40d2000027633e62b994309744621fe0ed46942f014388a83a817508b82c80ae00002762ddb2cc14e49a44672028e986802e5144089839616c08802e009c000027628172b0140895445d1fc0e706842e514188a03a817608c83140cc0000276222b2c914a49984682028e946842e714688b839c17508b02e80ae00002761c7a2a693b891242b1eb8e186522c4133085036415b07e02b409e000027616c32b093fc94244a1fb0e3466a2d0139088038416c08502a00ac000027610ed2be94549684652068e9c68a2e7143089c3a017008f82f40b800002760b182b7946496a4571fe0e906862eb144889839e17908c831c0b80000276053e2bf147c98e46c2078ea868a2ea14388d43bc17908c02d80a80000275ff822ae142894c4451f88e6c6822db13e08a438c16e08d83000ba0000275f9902c494a498e46e2070eac6942e714888b438a16808582c00a00000275f3ba2bb149899847020b8ecc6aa2fa14988c03aa17c08f82e40be0000275edda2b894609744671ff8e786782d813a087837816608702cc0c60000275e80d2b6943096a4561fd0e746842f314608d83b417709083000b80000275e2652a993d492e4351f28e3c6422ce13d084c37216a08582f80bc0000275dc842c794dc9b247b2110ef86c630014c091c3c418108e82d40bc0000275d6a92bd949897e4662000e746762d913e085c37215e08602c80ac0000275d0c42c4148c9a04772090ef46c630314d08e43b217908c83080bc0000275cadb2c914dc99c46f2078ef06d030515488fc3ca18509483200b60000275c51b2ad93cc9424481f80e5c67c2e1142888c39416a08a83000a80000275bf3f2be147097246a1ff8e586922e9144887437a17008a82e00ac0000275b9682bb947897c45b1fe0e6c6902f214d88fc3b617508e02e80be0000275b39e2bf148c9884632070eb06a630315489183be18108d02f00ba0000275add92b5141093843d1ef0e1c6602d213d087438016808882bc0a80000275a80d2b7945099647a20f0ef06b030015009043c217d09103100c60000275a2482b5942496845d1ff0e9868a2e1146089c39c17c09182e40b200002759c7c2b6945497044f1f90e446622e714208a439c17008683040b20000275968b2c7149097e4672020ea46b22f714988c43a217608882ac0b0000027590be2b694709804682020e9467c2dd14108ac3c017e09282f00a600002758b2829b13789184391ec0e006422c8138885438e16a08c02f00c20000275854f2c4948897044b1f78e346542ca135887838416808502d40ae00002757f532cd95049be47d20e0ef06be2fb14f88f43b617508d83000ac000027579642ca15049b246e2060eac6a22f114808c439617608d02c40be000027573712c994d49b847e2108f086b62f714f09303b017408d02fc0ca000)) else (if i < 411 then (if i < 410 then 0x2785ae02dc15549ea48b2190f6470a32415989383de18909102f80c2000027854f52c914d89b64872140ef06ae2ee14688e43b817108d82e00be00002784f022c394a099446e2040ea06b22f915109043d417e09003280d6000027849362b9148097a4602010e8c6862e213b087438616d08a02d40a6000027843752b2942094a44f1ff0e786942ef14708d03b416b08982ec0ca00002783da02bf94a49a44752098ec86ca30415289243c018708e830c0cc000027837b62c614d49944692048ea06762e614488d83c017c08d83100c4000027831d82c394b89ac4752068edc6ba30a14d89043d618109603140d800002782c2f2a913fc9404511f78e5467a2df142087439216008782cc0b0000027826682b694409684612020e806802df140889839016f08702c40b6000027820a52b1143096644d1f88e2c6542d813c887c38216408d02e80c000002781ab72c494c49a247420c8ed06962f814688b039c16c08602ac0a4000027814b72cd94f89b847420b8f086c630314c09203d218b08e82d80a600002780ed92c594a499046b20e0f086c830a154892c3c417b08e02e80c6000027809002be147c98c47520b0ef86ce30e15789583d618309102f80be000027803162c814dc99e4672060edc69a2e514608b439816908582c80c00000277fd362bf147896e44e1fe0e746a22ea14c08dc3b017108c02e40b80000277f76d2bb94549804622058ea86902ed14c09183c218109202f40bc0000277f17f2cb94a498846e2098ec06b02f714c88b438816e08782a00a00000277ebac2bf148c98c4521fb8e6067e2e614508a43a217108e02dc0ae0000277e5e32b0946098a4702098ec46b02f114388b03a816e08982e00c40000277dfdf2d495289ca47c20f0f0c6e230415109083e0195097032c0d60000277da122b8144c97a45c2000eac6922ed14a08cc3ac17309303080be0000277d4152d094ec9c648d2188f546ee31215309003e0188093831c0bc0000277ce562ae943c95e4551fb0e746822dc13f887c38617308d83040c00000277c8772c4149097c45f2020eac6a62eb14888b83b618109002e00ba0000277c2802cf15009b447d2140f006c430715589203bc18408e83200c00000277bcc02b0941094e4471f70e346662e514788ac3a216f08c82d40b40000277b7082af941094a44a1fc8e6866a2d513a887c37816508402b40a60000277b13f2ba145495e4531fb0e706842e714988b83b817d08a82f80b20000277ab7b2b8944c9624571fb0e4466c2d613b886438616408102980a40000277a56a2dc957c9d448220d0ed468e2ee14408c43b617b08982d40ba00002779f822c614b098e4612030e906902db13b08983a217709203080bc000027799b62b7145096c4581fc8ea468c2f014e88ec3da18609083200c0000027793d02c714cc9a247d20a8ea06922e314488ac38e16b08682bc0b800002778e0b2b9142c94e43f1f08e206442cc139084836c16708382b40a0000027787f82db958c9f849921c8f5c6d631015b895c3f4196099831c0c0000027782102c0949898445f1fd8e5866c2d513d089038416b08a83200c800002777c2c2c494b89844682050ec46b42fd15309143e2192099832c0e0000027776572bd94709764621fb0e7c6722e514888ec3c218108e030c0c4000027770702c0148c9a847c2098ed86c62fd15209083c418209002e00a400002776a6d2d495089c24852150f346ce2fa14889043ca181094832c0c00000277649c2be148498047820a8ef86ce2f614c08e83bc17d08f03140bc00002775eb92c294bc98445e1fc8e786902e1141089039217308d82e80b8000027758e72ba147097446a2028eac69e2f714a08d03a218308f02f00c6000027753112ba945c9584572000ea068e2eb14308d03a217108702b80b600002774d132d415309d84802150f086bc2fc14d08d43b817108b83200d00000277474d2b394589764572010e986a62e013c885c37616f08882d40a80000277416d2bf947498646c2008e8c6822eb14388b439016408702c00ba00002773b6f2d094f89ca48020e0eec6c62ff15088d43a217308802d00b2000027735822c614b099a4682068eb469a2ed14688d83ba17c092030c0c800002772f9c2c494b098e4672050eb869e2ef14708e03be17308a82c80aa000027729c42bc94549804612050e9c69a30215689343c818009183380d0000027724022b414149504511fc8e446722db13f889039817208c82f80bc00002771e032ce95049c048921a0f846f832715f89543d219809783240d00000277182d2ba14389604551fa0e5468a2eb14488cc3aa16408d02e80b00000277122c2cc94f09c04802150f286dc30515788f83ac17108a03080ca00002770c702ab93d89344411f48e446762de141889839a16b08682a40a8000027706952bf148898a47420f8f286c831115409203da18a092830c0ce0000277009f2c994e09c047f2110ee46ae2fd14888c039a17008f82f00c00000276fab32c8949c99e4662098ecc6a22f414608b83b618208b82c00b80000276f4ca2c694a09964652090ee86ba30615488e03ba17f09102f40a80000276eed92ca14d89b047a20b8ed86b42fe15488f83ba17408f82f00be0000276e90e2af14149604531fe8e9868e2ea14688dc3ae17708e83100bc000 else 0x279d1eb2c494a89a047120b8f006cc30d15489203ba17b08a02ec0b60000279cbf42ca150c9de48c2110ee46a42f614c08fc3ba17909102fc0c40000279c5f02d415309e448f21a0f5c6dc2fa15109203c617e08c02f80bc0000279c0072c794bc99e47220b8ecc6b02fa14908b83b017908a82d80a40000279ba3c2bd148c9944602000e9c6822dd13f889838416c09102f80c80000279b4472c714b89a047b2108ee46b8307151891c3ba18109303140b80000279ae712b9943c97445e1fe8e8c6862ec14708b83b218308d03140c40000279a8982b914689724612058ea86962f014b88e83c218c090830c0c20000279a2be2c1148c99846c2060ec469a2f314a08ec3b417508e82f80b800002799ce72b994689824631ff8e906a02ef14788b43a216608602b00b0000027997102b7143097444e1fb8e8068c2e814888b83a617c08b82c00c0000027991402b714489504401f60e6c6682d813d089c37c15907e82940a000002798b762b8945097045a1fb8e786842f314a08f03c618108d82d00a2000027985a62bd946496845f1fe8e886602dc13e88a439c17708d82fc0da00002797fda2ba94609724582060ea46902ed14288a438c16b088828409800002797a202ae93e49424461f10e1865a2c6137887839016908a02e40d40000279746e2aa93d893844c1f88e5067e2e3142887037a15908d82e40ac00002796e752cc14d89ba47d20e8f086ca30c14b08dc3ce17f09202f00bc000027968cb2a893dc94044f2038ebc6bc2fa14f08fc3be17d08782e80c8000027962f72b9145895a4561f58e3066c2df14508bc39e17708c82d40aa00002795d202bd14889824622070ec469c2e5147087037c16708782c40aa000027957452be14689724612008e9c68e2e313e88b43a417608a02fc0c2000027951782b9146096c4531fc8e846882eb14708e83a217508a02ec0be00002794b982bc94849964722098ecc6942f914e08e03b217c09103100ba0000279459f2cf14f09c646e20f8ef86c2300153090c3be17d09183040ba00002793fe12b4143494e4541fb0e886862ed14b88cc3b217708f03000c0000027939fd2c694c09a446c2048e9469e2e914a08a038816f08902d40aa000027933fd2cd95309d649021f8f9470232515e09583f0194097030c0b000002792dfb2d515349d44822118f186ce30514e88e03a617f08c82dc0b80000279284d2a593949224371f08e1c6422cb137884c37a16708282b00a6000027922752ba142c95244d1f20e206562d013d884c38816508483000d400002791ca22b7146498646c2090eb869c2f614e08ec3a817c09203100c2000027916b12cc94ec99647220d0ec06a62eb14908c43a417f08d02ec0b0000027910b62d395289dc4952188f406e231014e88ec3b818109083040c000002790ac92cb14dc99e46b2060ed46982ec14988c439a16b08782d00b6000027905142aa93d494044e1f60e506862df14388d83ba18008d83100c40000278ff432c0147496c44e2000e3c6682e714488c03a818809202f40bc0000278f9872b0940c95c4491f70e206622cc13c886837c163082029c0b20000278f3952cf14cc9b648320f8f146ba2f914708b43a2176090032c0d00000278edb62c314d49a64752068e8c69c2ff14e08f43c418009083180bc0000278e7cd2bd149099846e20d0edc6ac2e914208a439e16e08782dc0be0000278e1ed2c514bc98c46a2068ec86ae2fe14d09103ae17e08a82fc0ba0000278dc2b2b2141895a45a2000e806862e814288a439816e08982e00b40000278d6642b3943c9724622018e8c6a42fc14c88c43b218408d02ec0be0000278d08c2bd948497e45e2040e7c6822ed14a88f43b817d09302ec0ba0000278cab32bb948499846a2060ed86ba30114b09103be182095830c0c40000278c4da2bc149496e45b2000e686a02ef14908e839017608e02ec0ba0000278bf0e2bb94809824742080ed86b230114b88cc3ae18008e83080ce0000278b90c2d195489e44902108f006b42f915408d83b018109102ec0bc0000278b3112d1151c9e049b2170f386da31615709443de18b09403100c20000278ad452b9945c9724642010e746822f014188ac37816408482bc0c20000278a7712bc148098047620d0ee46bc2f414988e83b017e08e02f40ce0000278a1b62ac940894e44c1f30e646662d314008a039017c08d82d00b800002789be62b3142496a4551fe0e606742cf13d08803a817908d830c0ca000027895eb2ce150c9cc48020b8ed46c430314e88a039016d08982cc0b000002788ffc2c894ac99847720a0ee86c430314a08c439a17208682c80ae00002788a012d215149be47f20d8ef86d030c15d89643f419309303000c4000027884122c914a498646b1fd8e6c6942ec143089039416d08502c00b600002787e742a293989064291e50db86262c212f882c34615508082b00c00000278788a2c5949c98e46b20c0ec86ce30415008f43de18b08d82dc0a40000278729a2c594b89a64712080eac69c2f815108ec3b616e08683140c000002786cc32b9145496a45c1fd8eb86a22ec14908d43b017b09603340d2000027866f12bd146c9744521f60e406682db14288c83ba18109003280d2000027861012cb94c49aa4812088ea069e2f014388ac3a216d08402c00b0000) else (if i < 412 then 0x27b48592b4141094445a2010e986962f314a88e83be18809783240cc000027b42922b2943896a4561fc8e806742dd13e088838e16708b03040bc000027b3cab2c994d89a64692020ec869c2f514a08b43a616f08482c40bc000027b36f62b114489664521fa0e606822df13f088c38216a08802d809c000027b30f52d195209ca47d2118ef46d630b15488ec3ae17508a82bc0a6000027b2b172c314c89b647b20c0f006bc30c15108ec3aa17c090032c0d2000027b254b2b714689744591ff0e8c6942ea14788c83a816808102cc0b4000027b1f7f2b994409624531fd0ea869c2f014808d03be18508e82d40b4000027b19a32be14889a24722070ef46c030314f09083bc17e08b82e80be000027b13be2c314b89ac47c20b0ecc6c22fa14c08f039817708b03000c4000027b0ddb2c294b89b447820c0f046c62f614e890c3d418209102f40b8000027b08322a613a493a4481f70e3c6782e614a08dc3b216a08482cc0c2000027b02762b4141c9584551fc8e786842f114e890c3bc18008f83080c0000027afcbb2ae941494e44e1f90e506682d613e88d83c017a08f83140ca000027af6dd2c114849864621ff0e6c66e2dd142889039a17308803000b8000027af0f72c794e49ac47220c8ee06b22ee14888f83d218d09a830c0c6000027aeb1d2b9144097245d1fc0e486802eb141887838e16a08602e80b2000027ae51d2d395309d04852160f246e830815189243d018509503240ce000027adf752ac13bc93c4421f30e486622e214488a03a017008902a40ae000027ad9642d214ec9cc4842120f186c4301153090c3cc18e09503480d2000027ad3632d495409de4932180f446da31215d89483e618108d82f00b0000027acd652ce14d89b447820c8ecc6a22e814788dc3c417b09182f40ba000027ac7902bf947498646720b8ee46be30014f08ec3bc17b09483200c4000027ac1c62bb144496244e1fa0e4c6722d013a086c38c16108402a80b0000027abbdf2c614a898a4642078ecc6a62ea14288b03a216e08d82ec0c2000027ab5ef2cb14c499c46e20a8ed068c2f1149089c39a16d08b83080ba000027aaffb2c994c09ae46e2048ec46b42f415109103b818e09002ec0c0000027aaa522a813e494e44e1f88e8c68a2dc14208a439e16708902f00b8000027aa4712c3148098e46b2068ea86a02ea14508b83b017008782dc0c0000027a9e922c594c49b847920c8f086bc2f514e08e03c8186095831c0d2000027a98ae2c614bc9c44822168f046d02fe14d891c3c817d08882e40c0000027a92b02ce14cc9a24732088edc6c230b14d08cc3ae17108b02c409c000027a8cf02b8945096a4551f70e506782e4142887c39e16d082029c0ac000027a87352b1940c9504431ee8e106582d5137080c35215608102c40a4000027a81462c1947c9744572000e7c68a2e614a09143c417e09202f40be000027a7b662be149c9a246b20b8eec6b02f214888e83c617c08d02f80b2000027a75672d2950c9d848e2138f086c02fc14908ec3be18008f02f00bc000027a6f9f2b3941094844a1f18e4c66a2d613d085437a16b07f82b409a000027a69b32c714cc9b047720e0efc6e230d157094c3e219409203080c2000027a63d82c014ac99447320b8f246be2fe15109143d217c08f82d40aa000027a5e032b8945c97c4692088ee06ca30315309503d418709003200bc000027a585c2a993bc92042b1e78dd86202be132083837e16308382a80b0000027a52742c494a09a246e20b0eb468a2f214a88dc3b417608c82d00b4000027a4ca32b4143095e4561fa8e646602d813c087c37816608282980a8000027a46b92c614d89ac47c2118f1c6c6304153894c3d618809583000b8000027a40b92d315149d447520e0eec6b22f714f09143a217108c82e40be000027a3ada2c714bc9ac46f2078ef06be308157891c3c218108c02f00b6000027a34fe2bf94849744511f98e8c6802d613c088839e16d08d03100c2000027a2f1d2c094749764561f30e2c65e2dc141887c37c16808582e40ae000027a29542b3942495644f1f70e406762e1149091c3bc17c08c03040c6000027a238e2b394149484501f90e4465c2db14208983a417a09003040b0000027a1db92c0149099446e2068ea068e2ec14588c838c17509102fc0b6000027a17ee2b6144496a45a2018e686962e414588a839a16e08982e40b4000027a11f72cd15109ce47a2130f4c6e430915308e439a16b08902e00b2000027a0c262b2143496645e2018ecc69e2da13d889438615707a82940a0000027a06422c2945c9764511f70e5c6942e514788c83ac17808e02ec0d0000027a00552c614ec9ba47c2108ed068e2ee14688cc3a017609183300ca0000279fa962ae944495a45a1fd8ebc6962ee14c08ec3c017f08f02fc0c20000279f4b72c4148c9844672050eb468c2e714508b039417a08983040be0000279eec52c994c899a47520a8ee86b42fe14d88dc3b017608e82d80b40000279e8f32bd946c97c4652030ea868c2e3140889838416c08b02ec0a80000279e3412ad93e09464401ee8df464c2d413c885c38015808002c80ae0000279dd6d2be94989b647220c0efc6c0313159891c3dc18208f831c0d00000279d7cd2a313b492c4361ea8dfc64a2c6130880836a16108482b00b4000 else 0x27cbe752b614389684551f88e3c6642c7137882c35815408082b40ae000027cb8d62a2139490e4321f60e606742df13d88883a617008882b00aa000027cb2f52c714ac9a64732080ee46ac2e3143088438c17108782c80b4000027cad3f2aa14149364431ee0e3465c2d513c086038c16b08b02d00b6000027ca74e2c914cc99847720c8ef46ac2f814d08d83ac16a08702ec0c4000027ca1822ba94309504441f70e206682e113f888c39c17308c030c0d4000027c9bbf2ae141894a43a1ed0df064e2ce137883438216308982cc0a2000027c95e42bd14749a847820e0f006a82f414e88c83ac17c08f83280c8000027c8ff52c494c098e46a2020e7c67c2e114588b83a417608f02e80b8000027c8a202b8145c95c44b1f68e346682e314208ac39c16f08582f00cc000027c84472b994749844622070ec86ae2ed14b88dc3bc17d08c03000b6000027c7e642c194709704672008e7c6882e114088b03aa17208e02f00c0000027c78962bb14989864632058ea46882e0138887438e16808982fc0b0000027c72ee2a493e893844c1f38e086482cd133884c36415307f82880a2000027c6d1a2b6946898045a1fe8e706782e514308b83ae17508d02d40a2000027c67562b3140c95244e1fe8e8467e2e0141889839017208982d00b6000027c617c2bd14889864672048e986a62fd150091c3c018609082e40ac000027c5bae2bb947498445f2008ea067a2dd14688b43ac17c08d02e40c2000027c55b02c714c09ca48a2168f406d030f156892c3e619009683180e4000027c4fbd2c514c89b04692078f046b830715a09403d018308f83240ae000027c49ec2b8145096a4561fc0e586922e7145889439c17108a02f40a8000027c444d2a513d49324411f20e0865a2d813f88c83a617308d02e00bc000027c3e892b393f49544501f90e4465c2d013988743ac17308302c00b6000027c38ab2be946c9944672038ed46ac2f714b08bc3a617408a02a80a0000027c32e32bb14849824551ff8e906882e014288ac38c17108b82ec0b8000027c2d102c3148c98245d2020eb469e2f314b08fc3c618409382fc0c6000027c271c2ca94b098e4682058ec469a2ef14a88ec3ac17608582f00aa000027c213d2c214b09a24782098eac69c2ea14c88f83b818308d82fc0c2000027c1b532c514b097446b20c8ef46a02f814988f43b817e08a82e40b8000027c15692c294b09a64762078ea869a2f414c090c3d217f08d02dc0b4000027c0fb22ac93ec93a4491f68e1c6502cb140889039c17809203140ca000027c09cb2c1949499446b2090ec46b22f514a08f03a417508f02ec0b8000027c04212a513ec94c43f1f00de463a2bf135086036415908002b40a6000027bfe252d015089be48020c8edc6b42ff15008f03be18208e83000c8000027bf8522b394209604561f88e2c6642d613f887838616a089029c09a000027bf2582c494b89b44892180f506e631115789083ba17c08e82f80b8000027bec8d2b7144c96845a2020e7c6782d5137083835815808282b00a4000027be6942c694b49a646e2090edc6ac30315088dc3aa17b08f83100c4000027be09b2d2950c9b646d2040eac6b02ff14e89083be17c08e82d00c4000027bdab32c694d09a84842100f1c6c4301150090c3c418f09403100d2000027bd4cf2c214f89ba4802138f386ee31815309443d017e08e830c0be000027bceec2bf94ac98846e2090ed06aa2ef14c88f83c218b09303080ac000027bc9272b2142494c44b1f60e306582c913a884836615e07f02ac0a8000027bc3592b7145097445b2020e946842db13c08983ac16d08682980b0000027bbd9b2b3141c96c44f1f68e3c66c2dd13f088039a16f08882b80a2000027bb7b22bc147097445d1fe8e906842d0137881c36816208302b80b2000027bb1cf2c214c49c64812080ed06b8301155090c3ba17c08c02fc0c2000027bac072b594109384381ed8e0464c2bf134885c37c15807f02cc0b0000027ba63f2b3143c95644d1f50e186682de14508bc39616f08882e00c0000027ba0832b2941895444e1fa0e8066a2de142086037815c07e829c0b0000027b9a962c714ac9a44662080eb869c2f014c08e83bc17e08f82e00b0000027b94bf2b7942c97645d2028eb068c2ea14c08d83ac17808c82fc0ba000027b8ef52b714109444471f90e646802db14088a03a617108482c40ac000027b89012c894e89a04682060ed869c2f914688a43ae17108902f00ae000027b83362b8944894e4451f38e2866c2e014308c43b217b08d82c40b4000027b7d5d2bb144897845e2020e786802e2144089c3ae16d08602dc0ae000027b77452dc955c9ea49a21b8f586dc31c15e098440419709d036c0da000027b71622c294c49ae47c20f8ef06da30c15209203d018f09283180c2000027b6b872c814ac9ac47820a8ef06b42ff14a08cc3b417708c82ec0a6000027b65922c914d49a647b2138ef46b22f815108d83a417b08e82cc0b2000027b5f932ce94ec9b248020a8ecc69c2f114888cc3a818108d83240d6000027b599b2d195049b847920b8f006ba30015009103cc18e09002f00b0000027b53c92b7147899046a2090edc6a82eb14a08c03a617308a02d80ac000027b4e222a713949124231e50dc464a2cd136885037416008182bc0aa000))) else (if i < 416 then (if i < 414 then 0x27e34522ae13f893e4471ed8e206562c813a888038c16808902cc0a6000027e2e7f2b9946498e47520d0ecc6b02f714d08cc3a217208d82bc0a4000027e28bb2b6944496445f1fd8e786802dd13d087838216c08802d80c6000027e22eb2b6143497246e2080ea06862e214488a839e17808f031c0c4000027e1d3d2a993e493843a1ec8e246542d113c887439416007c028c0ac000027e17572be14649744642040eac6be30615009003b617d09083000ca000027e11892ba945c97c4611ff0e9869a2f114a08c83ae17608e02e00be000027e0bbe2b714549764592030e9868a2e514608c03a017108c82bc0a6000027e05b92cd94d89b247d20d0f0c6d030c15809643ee18408e02ec0ba000027dff932e09584a184a12258fa06fe32515789443ec19509603180c8000027df9a32cd14fc9b647620a8ebc6a22f715009203ca183094033c0cc000027df3b92ca14d89b648320c0ee46bc30115289303ca17108f02d00b0000027dedfb2b514189644581fe0e686682e113e088038815d08102c40a6000027de8202bc147098c46a20b0e9c68a2f214688ac3a617308802cc0b6000027de2802a193849184331ed0df064a2ce137085436615d08302fc0c6000027ddcb12b814649744592000e9c67c2da13f88a839c16d08e02f40ca000027dd6e62b7145898c46e2050ec06a42ee14608b03a616f08a02f40b8000027dd12a2b2141094e4411f38e046462c1139886c36e15708002dc0b2000027dcb4c2c3148096c45c1fc8e8869c2fb14f88e83b217508b02dc0c2000027dc5912ab93f092e43d1f10e306602d9141889c39217508902ec0c4000027dbfdf2ae13f893a4401f78e606922e913f888c39a16f08c02e80b2000027db9eb2ca14cc9a648420d0ec86a62f414d08e83bc17808f02f00c8000027db4272b8942895a4481f88e406642de13d887437c16908902e40a8000027dae2f2d5950c9c649821b8f546ee30e15389243de197093831c0b2000027da8562bb948098046f2068ec86bc30214c08e43d0186091032c0c6000027da2762c414bc99c46c2050e9069e2f914b08ec3ac17c08e03140ce000027d9cab2ba947c9784571fc0e706702dc14288c43a017008902e80aa000027d96cd2bc945897846b2020e8868e2ed14488a439c17208d83080ba000027d90d72c614dc9b44762088ebc6982ea14489003be18108d02c40ba000027d8ae42cb14e09b04792098ec06c430015589083d418409a83680d8000027d85182b9146c97e4642090ed86a62f314988e83b418209203080bc000027d7f3b2ba946097a46a2028e9c6ae30114b08b03a017c08a82cc0a4000027d79552c314949884612068ea46a62f614688c43b217e09583200b2000027d736c2bf148499a4722078eb46942e714508e43ae17308c03180ca000027d6d742cd14d098a46d2068f1c6c430015089043b0177092031c0d0000027d67ae2b4945096a45d1fe0e646722e413f088039a16f08c02cc0b0000027d61c32c914d89984752038eb46962fa14f88f83c817f09083100c2000027d5be22c4149c9a84712050e906882e214688d03c417808c02f40b6000027d56062c3948499c46f2058e9c6802ee14608ac39816608602e40b6000027d504e2ac14009224341ef0e246602da13d88a439217008c03180ce000027d4a5f2c814b49a247920e8f306d4304155891c3bc18509402fc0b4000027d44762c314a09b247720c0f1c6d2312156094c3ce18a096031c0cc000027d3ed429f137890c42b1ee0df863c2c3131881c36015508102c00bc000027d39102ba945496c44f1f90e7c6802e314688f43d017c08e82f40b4000027d33582b1944098e46a2088ed06b02ff14d09143c618009202fc0ba000027d2d872bb147c97c4632040ed06962f614788dc3a817708d83180ce000027d27c12b4142095444b1fc8e9469a2e713d087438c16b08682f00bc000027d21f72b714389664591f68e5466c2e614088a039616a08a02e00c4000027d1c2e2af940c9644501f70e446482cc133886838c17608902e80bc000027d16592b9944097e46b2060ed46c02f714908f43b818008b82bc0a4000027d10732c314b498c45b2020ea869c2eb14c08b038e17208702d80c2000027d0a9f2ba147899846f20c8ef86ca2f414a88a039c17608c82e00b4000027d049e2ce94e49ae47a2078ebc6942f815088e43b817d08f02fc0b8000027cfebf2bd945498a4681ff0e946962f715109103c217308b82ec0c8000027cf8e62bb14749784642040ea06902f814e08f43b018308c82d80b2000027cf2fa2c514c09a24652028eb06922ee14488c83a218009283200c6000027ced252b9943095a4481fa0e786902e914a08e43b217b09303240ca000027ce73d2c714c49a04752058ea06842eb14e88d83ae17308a02e80b6000027ce1722b814689724562018ea46a22f714b08b43b017a08f03040ca000027cdb8d2c214bc9a647220b0ee06982fb15089003d618e09583180b6000027cd5a42c6148c99446f2040e6c6902e914288c03a617608b03140c2000027ccfe02b6142c9744631fd0e7869c2f214e89243d818c09182f40b2000027cca222b4142897845f2058edc6b62f714b090c3ce187098033c0c0000027cc43c2c114b89964652020ea46a62ea14708e03a816608982f80be000 else (if i < 415 then 0x27fab642ae941094a4461f38e0c64a2c1139886438617008c02ac0a2000027fa5822c4149098045e2008e886962eb14688d43be18c094833c0c8000027f9fa62bc943896c45f1f88e5867a2d8141889839c17108682c40ae000027f99ad2cb94a499c46e20b0f0c6c430015009103ca18609583040bc000027f93cc2c714a49984722080ec06b82f614f08dc3ba18508c831c0c4000027f8ddb2c594c09924622048e8c6a22f214c88e43a417d08e82e40d0000027f88152b514489684592040e9c6882ed14688dc3be17b09483480c6000027f82202c614d09a84762090ed86ba2ef14988e83ce19609a03380c0000027f7c552b8946097c4672058ed86a62f514c08c03ba18909403280c2000027f76562d3153c9da4872148ef46b430014808c83a817a08f03000ce000027f70572d394e89b647b2080eb46982eb14588983a017508f02e00be000027f6a962ae942894c4491fa8e5465e2d513a885037416408302ac0a8000027f64972d315089c447720f8ef069e2e914408dc39217108f83300c6000027f5eb72c1949099e4732080ee46b22fa14e88d43a017c08e83100ba000027f58e12b8144c96844c1f48e4464e2d314208a839617708d02e80a8000027f52ee2cf14e49bc4892118efc6b830115309403da188092032c0c8000027f4cec2ce14dc9b847c2118f1c6d230415909483ec19a09a03400c8000027f47192be946c97e4632010eb86a22f614a88e43ac17508a02ac0a2000027f413c2c5948897445f2068ea468c2e513d888037a15e08a82f80ce000027f3b672bc945c9764632040eb069c2f314d09083c018908d02f80c2000027f358b2bf14909904732070ecc69a2e4146090c3b818009303440be000027f2fa62c314989a44712080ed46a42ed14908b43a616f08a02cc0bc000027f29d82b4941894c44c1f60e3c66e2e113c085c38015e08002c40b8000027f23dc2cb94d89c64812148f386e030315009043cc17f08f830c0c0000027f1e2b2ab13c494c4471f60e4068c2e414508bc39a17208482e80ba000027f188b2a1139c92c44b1fa0e706802fb14988bc39617708982c00cc000027f12ca2b6942c96c4541fc8e946962ea14508b03c017d08f03100ca000027f0ce92bc947498645f2040eb86982ef14a08f43b817709182fc0b2000027f071d2ba14549784622010e886762eb14788c43ac17108e82c40b2000027f01512bc942095644f1fa0e6468e2ee14808e03c018008c02d80c4000027efb872bb14549624501f68e5c66e2dc14708e83b017508982e40b0000027ef5932d5151c9ca48e21d0f406e230b15609443c818208b82e80c2000027eefb12c1946497445d2068e986902ec14708bc3ae17608a82f40c6000027ee9e12bb143c97c45f2018ecc6962f314c08c039e16d08702c80b8000027ee3e42cd94e49a64762100f046c8300150090c3c817d08e02e00c2000027ede2a2ac93cc94c44d1f98e286482c6137885c36a16108782e40a6000027ed85c2bd14749724571fe0eb469a2eb14788cc3b218209002f40b4000027ed2a82ab93e092443b1f18e186562d413d889037e169080828409e000027ecc9b2d495309e248721e0f646f231c15c092c3e419a095833c0e0000027ec6b92c5149898645b1fe0eb069e2f214b08b838817008902bc0ac000027ec0d82ca14c89ac46f2060ecc6a82fe14e091c3d218509303200d6000027ebaef2c914bc99e4792068eb469a2f314c08f03c418a096032c0cc000027eb5192ba142c9644511f90e4c6522d4139884837016208782c40a6000027eaf592b794649704541fa8e8868a2e6140887038c16909002cc0bc000027ea9872ba945097a4632010e786902ef14e08e83c218108d02b40a4000027ea3b42bc947497e45a1ff0e8c6782db14688f43a017008802c00aa000027e9dc82c494a498045a1fa0e786842e014888cc3a417008402bc0b4000027e97be2d2951c9de48c2158f006b82f7154090c3c217f08b82e80b8000027e91d22c714ac9aa4802100ee86b02f714908c03b617c08e82f00a8000027e8bd12d1950c9c647b20e0f046c02ff15489083b617a09002fc0c2000027e85ec2c614b49a646a2070ed06a82f714b08d83b617509083080ca000027e80362b214049524411ef8e046402d0137084438c16a08582940a8000027e7a762ab94409744642018e8c6962e314688a438016e08882e40b4000027e747d2cd950c9ca48a2108f086ce30f158894c3d617b090030c0c8000027e6ea92b6944c96c44c1fa0e586782e414508c439c16c08c82ec0aa000027e68d32bf948c98046c2060ebc6b22f514908d03a417108702b00a6000027e62f72be143896844d1fa0e8c68c2f014a88dc3a216808802d40b4000027e5d122c2947c9844682048e7c6762de144089038616d08682a80ae000027e575a2b294389724622058efc6be30515489183b417b08702dc098000027e51882b8144495c4471f40e386702e913c887839016908382bc0b8000027e4ba52bb946897a45d1fd8e606842e8148888438a17108882f00b6000027e45d02bf14a099246c2058eb86a42ef14688b43b417708c02f80ba000027e3ff12c0148c9a247f2108f1c6ba2f314c08f03b217908702d80c4000027e3a062c894fc9cc4862138eec6ba2fc15109243c017908a82b80b4000 else 0x28122042be147c9844682008e806722da14108a039e16608a02cc0b000002811c392bc145097646720c8ed06a02f514e08f03bc17108b02d80c6000028116622bb146c97a45a2078ea86922eb14708b839617008b02f00c2000028110b42b014309664521fb0e5c6862db13e88a03aa16a08302c80b400002810abf2c994bc9984662038eb86ba2fd14e88ec3b617f09302ec0c0000028104e52c4148c99247120b0f106e831315709483ec192097031c0d20000280feda2d595049d24842140f006d430a15308e83bc18209282fc0c20000280f9012be94889864642028eac69e2ea14908c839016308382b80ae0000280f3382b8146896645e2008ec46aa2ec14709003b818509103000c60000280ed612bc147c9704571f80e746842eb14b08d83a017e08f030c0ba0000280e78c2bc947497e46a2068e846922e514188b038e16f08e03140b40000280e1a62c2146898645e2050e9c67c2e114588c83b617d08e02e40bc0000280dbcb2c514b49964621ff0e9868a2e914408bc39a17108682c009e0000280d6072b2941c9464411f20e346562d413a885836615b08102c00ac0000280d0502ae142495e4581fb8e246602ce13c08a438417108d031c0c20000280ca722c114889a047b2070ea06962f614888f43d017f09282d80b80000280c4c42a593d092e43f1ee8e006502cb137886437216408102a809e0000280bee42c3148897c4682068ea06862dd13f88b43a416508602b80a40000280b90d2bf949c9a047320a8ed06aa2fc14a08d83aa17f08f02f00b00000280b3302b7142c9764581fa0e4066e2e014788943a217708982a80940000280ad6c2b3145897c45e2028e8c6982ed14308ac39016708c03040c00000280a7732c694d89aa47420e0ed86b82f214608a439c16908982d40c60000280a1662d695609f849c21f0f746fe31e15b89283da18609103040ba00002809b682cb14dc99e4712098ec06922f914f09283cc177093832c0d4000028095902be14949804692038ebc6ba30014f08ec3ca18108c03000ca00002808fd82ae93ec95a4551fe0e5c66a2dc14508d43bc191094831c0e400002808a122b2143494644b1f80e6c68a2e814608c03aa17908d02c00a6000028084212c514c49b64712098ef86b630114e88dc3bc17f08e83080b400002807e212d014e49d44892190f506e031115289143b617f08e82d40a20000280785d2b114189664531f98e586602da14388bc39a17208982e00a2000028072602ca94e09b247b20b0ee86b02fc15108d439c17a08c82f40c400002806c952b9946c9764612040eac6922e814c09003ba18208e82e80ca000028066922ce950c9bc47f2098ed86a22f214a08c43a217708a02e00b4000028060ce2b494249544481f58e3067c2da13c088437615f081829c0ac00002805af22b9943494e4522030eb06b22f814c88d43a217508e02f80d4000028054f72ce94dc9b047a20f0f0c6c4300151090c3c017f08c02dc0b200002804ee42d695389e448b2138f086d230f15689583d018a09182ec0c0000028049232b7947097446a2010e9068e2eb14688d43c218508f02f00b2000028043642b1942495a45e2068ebc6a42e914788cc3b617d090831c0d600002803d802c2148097a46520a0f246ca30615008e03b617f08e03040ba000028037b32b6145497a4581f88e646702d714288a03a217108e02f00c0000028031e72b7944c97845e1fa0e3c67e2ce137883c36415808282c80ae00002802c152b8947496e4541fe8e546702e014388a439c17208903000c0000028026482bb14789924631ff8e9469e2f314988dc3ba17909283200c8000028020672bd947496c4591f88e2c66c2da140889c39616808882d80ba00002801a782c694b899c46e20b0edc6ae2f214608d43b217809103180c8000028014922c394b89aa4742088e9869a2f514488c439c17508d02ec0ca00002800ebc2ba944c95244f1f98e606902e814508983a017208482d40b4000028008d12c614cc9964692040e9068c2ea14508b03b017408982e40ae000028003022bc146496e45a1fc8e506762de13e88b83a817208f83000ae000027ffd3d2b714389664551fe8e8c6922e8140087839a17408d82f40ba000027ff76b2b8943897644e1fc0e4c6622d514108983a216908c031c0ca000027ff19a2bb144c98445d1ff8e786762dd13f88a039016c08702c80aa000027febb52c594dc9be47720f0ed469c2fa14c88d43a817d08e83000b8000027fe5de2bd946c97a4651ff8e706842e214808e43b818509382fc0c0000027fdff02c494e89b64822110f346de30b15708fc3b417a08f83180ce000027fda1f2bb145c9844702018e9469e2f014a08f43b218308f02d80b0000027fd41d2cd14f09ac47d20d0ecc6ba2fd14c08d839016f09082d00aa000027fce512b7943c9784652058e7868c2e414488a83a217b08a02f809e000027fc88c2b394089684611fc8e606822f114988d83b217808702c00ac000027fc2ac2c394b89a447c2070ef06ba30e154890c3d418509302f00c8000027fbcda2b994709744571fc0e446602d113e889839216f08c02fc0b8000027fb6fa2c814b09b047e20e0ebc6a62f514d08d43a817a09283300da000027fb1292bb146c97c4672090ec468c2ea13f888c39217608782e40c2000)) else (if i < 418 then (if i < 417 then 0x28297c52b6141895c4491f68e5c67a2dc13e087c37a15c07f02a4096000028292012b093f893e4461f68e206682d113b886037e16608402a80a000002828c312b9943894c44a1f70e5067e2e514608d03b016f08b02f80c6000028286642b7949098046b2080ecc69a2fa14b88b839817208c02d40a4000028280962b8942c95c4501fe0e4866c2d613c887437e15f08802c40a600002827a8e2d395089c04842178f1c6be30514a88ec39a17608c82e00b4000028274a52ca15149ca4832138f086d830b14f88f03b417e09002dc0bc00002826ed72b6943c94e4511f90e6066e2e6143089c3a617d09003100d2000028269112b7946895c4531f70e506762e414388843a617d08f82e80ba0000282630e2d195309c64762100f546da30d15309083be17d08902ec0c600002825d422bf147c99447020f0f186b431015509243c018008c02ec0b8000028257452d395309da4902178f386e630c14f08e03c217f08d02e40b40000282517c2bb144c94c4561fe0e906922f414f88f43b418009183100ca00002824b752d915349e649521a8f546e230714d88dc3b818b08d82cc0ba0000282459b2c1949498a4642030e886742dd14108a039217308902e80ba00002823fdf2b1943896e4581fa0e7c6802d913c88783a016c08502b40a200002823a0e2b994609784662040eb46aa2f214a09003b017f09082f00ac0000282346f29c13ac9344361f00e346542d013a086c38c16a081829c0ae00002822e8e2c414bc99e4682078ea86822ed14408a43a017008882e80b2000028228a02c1946c98e4662048ebc6a42e0140889038c17408a82d00bc000028222c72b9944c97a4622070ea469c2e414108b83a817a08882f00c200002821ce72be145096045e1ff8e886a42ef144088039017308c02d00ae0000282174e2a293c49424441f00e186422bc131886c39a16308282d80b6000028211612cb14d89ac47120d0ee06b630014e88f03b017a08e02e40a800002820b8e2b714589844682060edc6aa2f714c08f03a817208a83040c2000028205da2aa940895645d1fe0e9866a2d1133883c38416308802f40b20000281fff12cd14f49a647420f0ec869c2ec14888ac3a216f08102a80b20000281fa352b014209624531f88e846862f314b88dc3ba17909082e00b60000281f44f2be948c9824591fd8e6c6802db13f089038c17108a82f80b80000281ee662c3947c97c4682068ed06b8304152090c3ca18708a82f40b80000281e8b92a793c493a4451f50e286582ce135887039216c08982bc0b20000281e2d62be948498a4612028ebc6b22f914f093c3e218008f02f00be0000281dccd2da95409d248a2120f1c6bc30415509203d618e09002fc0b80000281d7052b9942896044e1fa8e7066e2d713b087438e16f09183000ca0000281d1022cf14fc9ba47a2100f2c6e031115208f03b218809483340c20000281cb172cb94d099e47920f8f1c6e431a15d895c3ec19509583180c00000281c54c2b814849984692068ee06bc30315489243d218f09403200d00000281bf622c994c099846e2058e9068e2f214e09043be18309082e80c80000281b98c2c094989904682068ebc6942eb145088838217508782d80a80000281b3c22b914289684602048e8467a2d614108a039617008702fc0c60000281adf72b6144c9624541f60e3c6602d213b886838816f08882d40aa0000281a7f82ce95009ce47c2138f3c6d830b151891c3cc18609783300d00000281a2442b0141494e44a1f58e1064e2d7141087c38015f08582cc0b000002819c7a2b814249584501fa8e746882e914688d03b617b08c02f00c2000028196752cf14e89ba4802110ee86ca30e15209203cc18d09883400e4000028190902c294949a646b2070ec46a82fe14888d03a817d08f832c0d000002818ac72b414109604541fa0e846822f0141088038816408182bc0a6000028184ea2c0148098c4691fd0e7c6982f014688a039617308902e80ae00002817f1b2bb14409584521ff8e6c6782de141889039616a08882e80c0000028179282cc14e499a46d2090ed46b62f815009283d018e09582f00b80000281736a2b2140493c42f1ef8e146602d813c885838816808882d00a800002816d962b9145497245e2018e906822e214108bc39a17208982e00be000028167e12b3142c9664551f90e806922e914f09083b617e09002cc0b20000281623c2a913bc9324421f68e6c68a2e414488c43a817208e02f00b600002815c782b0141094844b1f88e6866c2d514208a03a617108e02c40c6000028156c02b314289544491f38e146522d8140088c39016308882dc0be000028150d72c594989824652040ea469a2f615189243b217e08782cc0c400002814aec2c394889984672070eac6b22fc15409103b217008782dc0b6000028144fb2c794cc9b847d20d8f046d030514d88e83ba18208f02f80c800002813f272c0145c9644501fe0e7067e2d9141886c37816208502a80b80000281393d2c394689764612060eac6942e814888cc3b216608582d80b8000028133832af93f09484431f20e346682e514c08d439a17208982f80bc00002812da12c4148c9984682070e9468e2e714808e83c416f08a02e00c2000028127e12af13ec94a43f1f38e706842e414588a83ae17908d03100dc000 else 0x2840dd22c1148499a47120d0ee86b22f414f091c3b617b08d82ec0d4000028407c52d414f89ba47d20f8efc6b82ff14d88c03a616a08882d40ba000028401ed2bf148899047020c0ee86ac2f314c08c439416808982d00c40000283fc552a113748f241c1e78df06482d213e887838c16d08502ac0b40000283f6912b6142097045d1fc8e786802e714608cc3ac17a08a02ec0c60000283f0ac2bd947c9884682008ea86a62f714588c83b618108e83180c80000283eac82c594b099245f1fe0e646762d113d888438c16208382b409e0000283e5082ae93f495644b1f10e386502d213a087c38816708582a40a80000283df2b2c394a498045d2030e7067a2de13c085c37816108402b00ce0000283d94f2c2148898646e20b0ed46a42ee14a08f03ec19209683300e40000283d3772bf147098e4592030e7c6722dd14588f83b818309402fc0c00000283cd912c3949898447120c8ea469a2fb14d09243ca17d08d03000c60000283c7dd2ad93f89584511fd0e886a82fb14f08f83b417708982d80b80000283c20e2b5945095043c1ed0e246442d013d087c38a16208002980a00000283bc072d695589dc4902190f586d230c15609183c4182094831c0c40000283b6522af941095043c1ec8e146542cf133884c36e15408282bc0be0000283b08d2af943095e45e2020ea06962f214888d43ae18708f030c0d00000283aaad2c0948899847620d8ed06b830115189043d4188093030c0da0000283a4f22b8942896e4601ff0e686882e714288c03a417108e82ec0b600002839f082c5149c9b04712098ec869e301151891c3c218c092831c0b40000283993d2b794689704521fd0e946a82eb145889839416d08402a4090000028393af29f139891a42b1e80de463c2c0132883c36c15f08502d40b400002838dcf2c4947898846a20b8ed86c02fe14e091c3c617c094031c0c0000028387f32bd143c95c4531ff8eb06b02ee14a88b43a417608c02f80bc0000283821f2bb147c98e46c2080ee06c430c15789103ce18508e82dc0b400002837c4c2b994389524541f78e3c6722e114988d03a216a08a02d40aa000028376642c594b098e4702040e9c6742e214208a039816608b82fc0da000028370562d995689d84862120ec06b030515588f43ae17208c02d40ba00002836a822bd146096c4621fb0e386902e714288b439c17509403200ce0000283648b2ca94c099446a1ff8ea468e2f4147889839617208e83100d000002835e992cc14c49b647f2090ec46bc2f815188d43ac16e08982cc0b6000028358bc2c694e499446a2080ebc6ac2fb15088e039416d08982d00ae000028352c32ce14f09ca4832140f286d630614888b43b618509103100c000002834d0f2a813ec9444441f48e206582db13d887038616f09283240bc000028347572b094209464451f40e446762e213b885438815f08582ac0ae000028341512cf95149be48d2190f4c6d430515209143be17e08f83540cc00002833b8b2b5943096a4511f90e446722df142089837615708102c00b2000028335c02b5143096845b2010e706862e314688d43a017708b02dc0ca00002832fe22bd148897645c2018ebc6ac2f414988ac3ae16d08802dc0be000028329e12cd94cc99e4732080ecc6b22f914708bc39a17f09183040c00000283243e2a893a892243b1f10e446802e914588bc39616c08b82dc0c200002831e272da15109ca47d20d8ee86c230615088f03a617c08c82f00ce0000283183b2d015109d64872148f046ca30a15388fc3ca18208e82e40be000028312642bc144497e45e1fc8e886902f314608c43a617808782dc0b000002830c562d495149e449a21b8f2c6e230715489283c417909003080c20000283067b2c014ac98a4602018eb06a42f914c89003e2192099836c0e0000028300de29e13a891843c1ea8e106622da13a889039616a08802dc0ca0000282fb092bc947097445c2010ea06b42e914b08c03b018108f83140bc0000282f5642a493d492442f1ef0dd06382cd136084c36c15e08182b80a60000282ef732cf15089ea48b21c0f706f030c15389143c417c09102ec0ae0000282e9832ca14b099a47320e8ed86a62f014c08d83b217609002e00c00000282e39c2c194b098c46e2058e986a22f814a88ec3a817e09103240dc0000282ddc12bb949099246f2080ee86a02ee14d88f43b617c09103040d60000282d7ea2b9945c9744551fd8e946622d913e88a839416c08902d40ae0000282d1f72cc94f09b246f2080ed46ac2f814f88f03be17d09483080c80000282cc4d2ac94209764591fd8e6867c2d7138085438415e08582d80b20000282c6672c714d09a64712070e9868c2e514008b439816908782d80c60000282c0842c594a09904642020e7867a2e0142089c39617008b82e40ba0000282bab52b2941c9724602018e706842e1144088438816e08782d40c80000282b5002ad94109784571fe8e686762e6141889038216208702c40c20000282af302b794589764591fe8e846862dc13f089c3b618108c82f40ba0000282a9442c4948898c46e2070e906842e014408d839617c08b030c0dc0000282a3532ca94e89a64722078ec46b42ff14e08f03bc18209083200c000002829d872b5142496645e1fb0e4c67e2e013f087039216508502b00aa000) else (if i < 419 then 0x28584062c794c098e4662038e9c6942e814988ac39817a08a030c0ce00002857e2e2b994509664612010ea06842e214408ac3b2178090831c0d60000285786d2b3942c95243d1f20df86482c613988a03a2179092830c0b0000028572a02b794789824652068eb06902f214708ac39e17a08d03200c600002856caa2ce15249ce4812140f086d630f15509403da19209803300ca000028566d72be948099646e2058ed46b02fa14a08c43b0175094032c0cc000028560d52d695409e248b21a0f346e831215389203ca18909403000c800002855aef2c614a89864681ff8e886a02f414b88e43ba17908a82fc0b60000285551c2b9144895a45c2020eb06a62e714488c439616d08803040ce00002854f5a2b514609684511f48e5c66a2dd14108c83b217308982ec0ba0000285497f2bb14549644582020e946822e114408b43b818008f831c0d20000285437b2d615449d848f2150f346da31b15a893c3d618d09683440c000002853dc62ac93f89444441ef0e0c65c2d414008a03a016d08a02d80bc000028537c42d114d89aa4802130f046ca2fd14f090c3c817a08b02ec0b6000028531c62cf15089c44852128f186c02ec142889c38016708b02d40b800002852bf42c1148c9924752078e7c6962f414588d839e17208b02d80ac000028526412ab13d893243c1f18e4867c2db13b08a43a417308802f40b6000028520742b1140c9644581fd0e7c67c2eb14388b039c179091030c0c600002851a8d2bf14749784551f70e506722e014288a03a818208682b00bc000028514b62be149c99046a2010e7468a2e914788b839616608802dc0b000002850edf2b914349684551fd0e806782e814208a83a417808a02fc0c0000028508fb2c714e89aa4732090ec46b42f614f09143c218409703240c8000028503292ba946897045e1ff8e906862e914388b839c17708e83000d20000284fd642b5144896a4591fa0e546642db13b08a03a416f08702dc0c40000284f78a2c194949904662090ee86b02f514a09083d018308d82d40ae0000284f1d02b1943497a4621fa8e686602db14208a439616508082c00c40000284ebf42c094a09884652010e946822e5146887c37c16008502a40a60000284e6122c0148c9944652030eb06942f014708fc3c418c09182fc0c20000284e0262c314c09a24692060ea86aa2fb14c88dc3bc17b09002f00b40000284da722ac93e894243a1ef8e206602e0138886c38416c08c82fc0cc0000284d48e2c3147898e4622030eb06982f1142887c38016608502b80a60000284ce9f2c394989924682030eb068e2e5148089c39a17a08e02f80ca0000284c8b52c514a89844742078eac6922de14708cc3aa17f08c83180c20000284c3162a0137490642e1e60dcc6302b512e881c34c15007a829c0c00000284bd712a113a491a42b1e98de06382cb13b085839216008282b40ac0000284b78d2c514c49ac47b2078ec86a02f314b08ec3a417709002f80c00000284b1d72aa13d89504461f40e306562d913c085437c16908582fc0ac0000284abfa2bf14389724692040eac6922e9142087c38617009083080cc0000284a62b2b614489624501f68e3065e2d2138884036415808002c00ae0000284a0342cc94ec9c847420d8ee46ca30215209203d0184091031c0bc00002849a6e2b314409504411f40e3466c2e314288a03a6172092030c0bc0000284949e2b714289564562000e8c68e2ea14588d03b417a09283080c400002848eab2c794a49904622018e986902e4141089c39e17408882f00b20000284885d2f19634a3c4b92238f6c6fe32115809443dc19109583200ba0000284828a2bd14789584531f20df864c2d513e888839216308a03000d400002847caf2c1949498a47220b0eac6a82fd14b08bc39217508c02f80cc000028476c82c314749884632020e9c69c2f0143888c37e16b08302d00b4000028470a02e31594a0e4a22228f9871c32f166896c3fc19208f82fc0aa00002846ad22b4944496e4632060eac6942eb14a08bc3b417408c03040b8000028465002b7147c96c4571fd0e7c6922ed14788a439617508882d00ac00002845f162ca14ec9ba4832158f3c6d830f15309083b817808a82f80d8000028459622b414189504431f78e5c68c2e914408a438616308602e00ba0000284539b2b9946098a46c2088ebc6a02f514c88dc3aa17e09082f40c000002844dbf2c1146c9704611ff0e8467a2e013f087838816208482c80ba000028447e42c2148899246c20a8ec46c42fc14c88e03a617808f82f40c6000028442502a313808f64191e00d986302be12b881435615608002700a000002843c822b9144897a45d2070ea86902fe15189203e018a097032c0d8000028436c82b2142094643a1f30e286682cc13b886038c16708502f00ae000028430fd2ba14649844682040e7467c2e2140889837e16808b02c00a600002842b112cc94ec9b646f2088e9868a2ea145086035415607d027409c000028425432b494349524471f78e5c66c2d613d087c37e16208682a80b000002841f5b2c194c09b44782100f306e430a15209383ea19409d03440c60000284198f2bc94649744541fa8e586722d714308c839e17408d82d40bc000028413ac2c814b899446d2090ee06c430215589303dc18a09182e00a4000 else 0x2866d2e000000000000000000000002dd13b886837e16508002a80a00000286670a2de15949e649821c0f546de30714d88f03b817808e03040be000028661362b4940c9664602070ec469c2f314c88e83c218209103100d200002865b722b6946897646d2028e9067e2dc13b886838416808502d409e0000286559d2c114889a24732050ea06942e714688cc3c218508f02e40c600002864fcd2b9945c98a45c2000eac69e2f314988cc3be18309182ec09a000028649e42c514c898e4712098ed86b02f214808e03ac17908d02ec0ae000028644232ad943096844a1f98e346602da13d887837a16308302a40b400002863e712ad93f09424431ee8e3c6682da140887038017008d83180c2000028638b02b313f895044e1f68e446582bc13a088c3a017108b82e40b40000286331029e938091642e1ec8dcc6302c4132884836a14e07c02a40a200002862d362b914349604451f50e2c65e2d5144888837816408402b00a8000028627662bb949499a4722070edc6a430014d08f83b217e08c82e00a4000028621802c514b499246d20a8edc69a2f014d88f43d017c08e83100da00002861ba42c394a898845d2090eb46aa2fb15408f83aa17408a82c80a4000028615d82b013bc94c4471f28e386622da140089c39616d08882d00ba00002860fe72c914a09ae47720f8eec6b82fc14908ec3a417408c02dc0b400002860a172bd94a09904661fe8e7c6962e9140089439016b08a82e00ba000028604442bd94b099c46a1fc0e846982f814e89303ce18709202e40aa0000285fe612bc94509744601fc0e6c6722e114608bc3b017a08b02f80d20000285f8772c894bc9b84862170f446f431b15b09603dc18909503280ce0000285f2bd2ab13f09444401f58e6c6802db142888c3b418308e83000c00000285ecfa2af94149404401f28e606702df145089c3a017208c82fc0b60000285e7332b3942c94c44d1f38e5866c2dc13f08ac38e16408702bc0aa0000285e15d2b8141c96e4501fb0e786922f414a88f43b817f08b82fc0bc0000285db9d2ae140c93c43d1e90df46422cd135886838816908b02c00aa0000285d5e22af94089504451f40e506622e014588b43a617509003280d20000285cffd2c494b899e4742098efc6c430715088fc3c218809703000ba0000285ca382b094049544481fe8e6c6902e114308b83b418609103140bc0000285c4732ad13ec94c44a1f80e486602e013e088c39816c08502d80ac0000285bec42a913e09384421f80e1465c2d713a08ac3b617008b82ec0ce0000285b8c82cb94e49b047120a0f206d630415109003ca192094830c0ca0000285b2fc2b3947498a46b2068eb86a62fd14d08b83a417708b830c0ca0000285acee2ce94fc9ba4822138f186d230214f88f83b617c09002dc0b60000285a7292b6941c9564511fc8e6c6642e214808bc39e17d08c82f40b60000285a1512c4147898c46c1ff0ec06a02e014308a039c17708b82dc0aa00002859b9c2a9940893643f1f38e306682d5142888c38816408882f40c0000028595912d115189c248b20d8edc6b82f714c09183d218509683140c400002858fee2a593b893844a1f58e3c66e2e614788cc39e16408902ec0ba000028589f12ce95009c647920f0f006b82fe14f88f03c417708982ec0b8000)))))))))

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



private theorem b416574 : covered 416574 416679 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b416679 : covered 416679 416784 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b416784 : covered 416784 416889 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b416889 : covered 416889 416994 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b416994 : covered 416994 417099 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b417099 : covered 417099 417203 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b417203 : covered 417203 417308 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b417308 : covered 417308 417413 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b417413 : covered 417413 417518 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b417518 : covered 417518 417623 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b417623 : covered 417623 417728 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b417728 : covered 417728 417833 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b417833 : covered 417833 417938 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b417938 : covered 417938 418042 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b418042 : covered 418042 418147 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b418147 : covered 418147 418252 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b418252 : covered 418252 418357 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b418357 : covered 418357 418462 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b418462 : covered 418462 418567 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b418567 : covered 418567 418672 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b418672 : covered 418672 418777 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b418777 : covered 418777 418882 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b418882 : covered 418882 418987 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b418987 : covered 418987 419092 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b419092 : covered 419092 419197 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b419197 : covered 419197 419302 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b419302 : covered 419302 419407 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b419407 : covered 419407 419512 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b419512 : covered 419512 419617 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b419617 : covered 419617 419721 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b419721 : covered 419721 419826 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b419826 : covered 419826 419931 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b419931 : covered 419931 420036 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b420036 : covered 420036 420141 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b420141 : covered 420141 420246 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b420246 : covered 420246 420351 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b420351 : covered 420351 420456 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b420456 : covered 420456 420560 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b420560 : covered 420560 420665 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b420665 : covered 420665 420770 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b420770 : covered 420770 420875 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b420875 : covered 420875 420980 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b420980 : covered 420980 421085 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b421085 : covered 421085 421190 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b421190 : covered 421190 421295 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b421295 : covered 421295 421399 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b421399 : covered 421399 421504 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b421504 : covered 421504 421609 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b421609 : covered 421609 421714 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b421714 : covered 421714 421819 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b421819 : covered 421819 421924 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b421924 : covered 421924 422029 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b422029 : covered 422029 422134 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b422134 : covered 422134 422239 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b422239 : covered 422239 422344 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b422344 : covered 422344 422449 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b422449 : covered 422449 422554 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b422554 : covered 422554 422659 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b422659 : covered 422659 422764 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b422764 : covered 422764 422869 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b422869 : covered 422869 422974 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b422974 : covered 422974 423078 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b423078 : covered 423078 423183 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b423183 : covered 423183 423288 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b423288 : covered 423288 423393 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b423393 : covered 423393 423498 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b423498 : covered 423498 423603 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b423603 : covered 423603 423708 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b423708 : covered 423708 423813 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b423813 : covered 423813 423917 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b423917 : covered 423917 424022 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b424022 : covered 424022 424127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b424127 : covered 424127 424232 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b424232 : covered 424232 424337 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b424337 : covered 424337 424442 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b424442 : covered 424442 424547 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b424547 : covered 424547 424652 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b424652 : covered 424652 424756 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b424756 : covered 424756 424861 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b424861 : covered 424861 424966 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b424966 : covered 424966 425071 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b425071 : covered 425071 425176 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b425176 : covered 425176 425281 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b425281 : covered 425281 425386 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b425386 : covered 425386 425491 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b425491 : covered 425491 425596 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b425596 : covered 425596 425701 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b425701 : covered 425701 425806 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b425806 : covered 425806 425911 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b425911 : covered 425911 426016 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b426016 : covered 426016 426121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b426121 : covered 426121 426226 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b426226 : covered 426226 426331 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b426331 : covered 426331 426435 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b426435 : covered 426435 426540 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b426540 : covered 426540 426645 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b426645 : covered 426645 426750 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b426750 : covered 426750 426855 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b426855 : covered 426855 426960 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b426960 : covered 426960 427065 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b427065 : covered 427065 427170 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b427170 : covered 427170 427274 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b427274 : covered 427274 427379 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b427379 : covered 427379 427484 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b427484 : covered 427484 427589 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b427589 : covered 427589 427694 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b427694 : covered 427694 427799 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b427799 : covered 427799 427904 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b427904 : covered 427904 428009 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b428009 : covered 428009 428113 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b428113 : covered 428113 428218 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b428218 : covered 428218 428323 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b428323 : covered 428323 428428 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b428428 : covered 428428 428533 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b428533 : covered 428533 428638 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b428638 : covered 428638 428743 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b428743 : covered 428743 428848 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b428848 : covered 428848 428953 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b428953 : covered 428953 429058 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b429058 : covered 429058 429163 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b429163 : covered 429163 429268 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b429268 : covered 429268 429373 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b429373 : covered 429373 429478 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b429478 : covered 429478 429583 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b429583 : covered 429583 429688 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 416574 429688 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b416574 (joinCoverage b416679 b416784)) (joinCoverage (joinCoverage b416889 b416994) (joinCoverage b417099 b417203))) (joinCoverage (joinCoverage (joinCoverage b417308 b417413) (joinCoverage b417518 b417623)) (joinCoverage (joinCoverage b417728 b417833) (joinCoverage b417938 b418042)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b418147 b418252) (joinCoverage b418357 b418462)) (joinCoverage (joinCoverage b418567 b418672) (joinCoverage b418777 b418882))) (joinCoverage (joinCoverage (joinCoverage b418987 b419092) (joinCoverage b419197 b419302)) (joinCoverage (joinCoverage b419407 b419512) (joinCoverage b419617 b419721))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b419826 (joinCoverage b419931 b420036)) (joinCoverage (joinCoverage b420141 b420246) (joinCoverage b420351 b420456))) (joinCoverage (joinCoverage (joinCoverage b420560 b420665) (joinCoverage b420770 b420875)) (joinCoverage (joinCoverage b420980 b421085) (joinCoverage b421190 b421295)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b421399 b421504) (joinCoverage b421609 b421714)) (joinCoverage (joinCoverage b421819 b421924) (joinCoverage b422029 b422134))) (joinCoverage (joinCoverage (joinCoverage b422239 b422344) (joinCoverage b422449 b422554)) (joinCoverage (joinCoverage b422659 b422764) (joinCoverage b422869 b422974)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b423078 (joinCoverage b423183 b423288)) (joinCoverage (joinCoverage b423393 b423498) (joinCoverage b423603 b423708))) (joinCoverage (joinCoverage (joinCoverage b423813 b423917) (joinCoverage b424022 b424127)) (joinCoverage (joinCoverage b424232 b424337) (joinCoverage b424442 b424547)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b424652 b424756) (joinCoverage b424861 b424966)) (joinCoverage (joinCoverage b425071 b425176) (joinCoverage b425281 b425386))) (joinCoverage (joinCoverage (joinCoverage b425491 b425596) (joinCoverage b425701 b425806)) (joinCoverage (joinCoverage b425911 b426016) (joinCoverage b426121 b426226))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b426331 b426435) (joinCoverage b426540 b426645)) (joinCoverage (joinCoverage b426750 b426855) (joinCoverage b426960 b427065))) (joinCoverage (joinCoverage (joinCoverage b427170 b427274) (joinCoverage b427379 b427484)) (joinCoverage (joinCoverage b427589 b427694) (joinCoverage b427799 b427904)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b428009 b428113) (joinCoverage b428218 b428323)) (joinCoverage (joinCoverage b428428 b428533) (joinCoverage b428638 b428743))) (joinCoverage (joinCoverage (joinCoverage b428848 b428953) (joinCoverage b429058 b429163)) (joinCoverage (joinCoverage b429268 b429373) (joinCoverage b429478 b429583)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 416574 ≤ index 800000000/512 := by decide +kernel
private theorem starting_value : fast 800000000=41146179 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 800000000=41146179) (n : ℕ) (low : 800000000≤n) (bound : n≤825000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=800000000
    · rw [first,anchor]
      exact starting_value
    · have past : 800000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤825000000 by omega)
        have within : index n / 512 < 429688 := by omega
        have lower : index 800000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤825000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ800000000To825000000
