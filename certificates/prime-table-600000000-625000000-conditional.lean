import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ600000000To625000000

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




private def radical : ℕ := 0xa79852d9ea21ded5e0fa16885c46f9c91929df59f32b0ef0b19086e1fc1acc67f5fa996addda01711d3316b79b5f4421e4dd6de23e104e2cabd6d648dcc3b62bed8e9a20935a19781f5eaaff16c50ba54be329de79d3c09470acd159b0a10594583f72b4b00d2ceaf8e14ca523e2ab95e6d14b17c1a1011f2dc439b92cb0ff56836eb2879470bd88e04ccee9394e5db56ba8f1ef6ee11143dbf8a9649140b7b71025c4415b9a2a95081d95eb4c9e973fd9c90a43c736626edb72d82d4211924eb9aae485ca5bfd8d7df5819666d0038d9b145e5298eb910a58a7fdc32a3e25d7e0aae6be5ff0820aaf986e62f5a2e9452080799e9c4ae4ec7837fdf865393ae0e43308572c48b877e212885c58fe629b4ae8b4ab3b13034bd5d8267168fc9e5fc48d2f3c2d618298301a9429438e2a74ec8808b88da93e1c8ab8d9c75d1b38e414ad6f21480c233e2ac4d61d543ef42807b36f6d36087a8d6f0adf49bfe7da022fd688f6a248d9f2784da92f1e451000bf521d8a7f4b314617a4bb94ecac017dffbf189071bbfd399a8d8cf47c29950f4143bdbc5283b390133b24e4f08ecb457be007f78c890a620acec7e378915ad26429170634d5e813c62b44f429da1765f9565fee55086950c6c60b983f49567462e48c8ee57febc6e0e3a5f975ccc186919d2734ac057c23386bfc53528ae432d55b9bb2608c2e2e0d6ce9d9e28cf0eb706e2a69bf924a1d5615f7828e39aa6a7b2365185964ca07143ac96e8308bfd4b505c5f2e6c0aadaaf3ef3afea18812f9ee796a4edc5fc88e6cbe29f705710f0168aa4dc7975618fd2e26f52fcb2f0abd92a19f0e5c2461fd2b93df1949e857b137a0bc581dc38518e77d3ce99cc0e661c7b7e59754d547a5010db37929fc36569eeb63e1687755fd712aea376116f6260b41ee1718de71bba6853d7ea226e4b71099e14f19d48e7d9345190f0cfaf5d23e6afd76de724f1d740ecafd0172243128cc1dfa5e94f7d746d889c57077760b66652ef45166d99be51b8043a6b9803f6f95a23840154e5348fcb8c2956735ccd37558ca1af48074c1997ab7abca56e5cff40a2ba8a5eb2773b60692d4f1aedc78a30384dd0989750287014455b3223b2bfca45e296889ac26ad9d62a62489ff318e9911bedada76ed18c4206ed228b93823c35dd1ed659da8662a9598b0b4897e272c83136bfd2cb6cc4ba21da0a1599fa75d5a5c01a13f69926f5665ace8550572abda7b80909a19bd7c6219ca100600fc817eee4ea387c24eb2b0e4f603b49d85ef70163398239e06842c286b9c927bec685de4f5f02b3e7dae6968a0072ae198851fc923bd2238b19f1a3a6c24a7851eda495818d8364c09f421dbb3c4081e3faa75c1cc50ff1913b5c418b320fb350db50b8d67bc0f583b997921a224f7162798092eb5287140d34f93f9f67ce643f1fdbfa20884c8eb9d030f6fbb0a0d092d83e0513837fef3cb177509fb62cc28c2326d36b35f2590cd839867e945fc44d8675211038557c754aa1bbcb559b67b831b60be9090abcfdde375b9680925f522c5ef7b2b9a2cd880905242add5865100fdec07aa4734a12404164a62ec10dc8f7d16c7f8fd32ffad64ad21dc1120659893f44dfd583a012544ef30716a2a806bdafd63c46a2330d545a4540f6617a180d78eb73eb2747628fa1d0bcfa8fd169e1aec2eef89ab757d745561b84b07d474d22f03a0cd6ff2aac6e0e055ad6ed3b44d75c34fb7ed7acb2b2d8b51b1fb4c98ff24cf4d9bb13e30885830125286287309a9281abd32eb05d92955b027476d01c922a1e04615c9c349908fa187ec97c3215dbb902472b7e73b0e1fea70b431800f085b613b45b2317594af0ff3e25d5984a30042febb1be5f7939aa6f9d7546732f396708f550c6f561251d8dc2d2f92cf9e692891f49437335e93564728fa6128cf2b8c4c8b7c4814b3389301c7d63b4db30bcad510ba4c9f5f1101440ca2b7ddd077e6a0379114275d84bec84db3ffdeb697e9375d10a0107f394a9d72a80c7549a1031ead67edb46e6834737e93032b9f5c7201d8fb1e7c772dba6f354877994a1f1e8850efa01f6b53ee61eefd39c49d40df878eac8cf8fdf26b9d1286a873f91a510b048d2131ffd545da7f403ceb0586e89f3c06220b3576805fb76a5968abc295d53729a4cd56896f0ebf0938d6167632e45705de8289130c6b50c6587eea684e86fa5a7f28ad466aeaf4f30f4c4672a8a39ad3ec911602cbf9906f91bea490abe7ed9a557ddfc66e69806e8a54cf95481f491381b9c176fa9b0cb8492524601b14ab62b0929dd7e00bb3c695209b0e0f94fcd0e7ea4dabba9410fffdf1e0418395be651e56b91b2608f1f297ce3a8f9e7f697da4a1c8dabaf53139d748093f2e65a8c7d5d1461aafeb43cd117777b410974c36d6d742d31751bc9d44da67725aa7edc6dc7377b0d24002121c0948bc57b20d665047d295686c54902574c7e776573d78da5b2d2258cf70fa17baacc2761a70026eb92ad65aea900448b52a3dec9ea85688eda7c5444fa0aa9b8a4495a81dda6075d41e26bf9206df61f9ede1de40f5b6c6fb26da1fce2015d9a2d9e09fe981bdf6433e78449836e481d609a6167a71d69c66c14328f7cae7bce54bfcc84822b6e754a5a99a7ee8c5c04dd63215b88f1f8fb071475b12df6f06d0dc41cf4ab55842d5ba0ab66baa5d4ecd6f33d13157f4ddad0cedcf8e83e4f0f0442def43bbccb2a6c169bb239ec3b455a95c09a9f1c5880e6d11a7dca2c04ea492e252fa5509eca54711be8af45119ab9157f2cfd4c16c5305f8724234a0acbae147b42614817edd0355a58909d2071ba2eb048cf2ce8448639d4a40e26e77babd3978de596a9d06fd9b3bd5691f81803792e4170521e3a8a33283fdcf70ff9fcfd423bb47a7d3c745a674679ffe73faa5599276fb14b431c667b0e7964b808f94340315a6122baeff7c4c50873fa2c8defa7dcd261d8bd84530b39ead86d9a29d24f68a05f84178072e610a2750417384019aacefffe5255d3980531694d16d604a5eea277d0cb3f5f088d2606981de96a400e1f9486b47768099b38fb1c1112cfae15904ac982720ed1ab069ae6a2cd7fd9620971d0e691747552b43ad66cc784aff550795385a8b96414c8a8644b1de331ecae99aff5bffe5508287292b70bc8568b465a545e86095df3674ae67a628c627d79ac14f21757a90d083362978bc12f363e445fbf4d2bce63b624d505d8513d6e9b849b3492b26a2e23c4e2a7b394e0152cb6680e8035fafab4816d248b3775c94beee6801b3980bc72ce24379bbd7a504868953c27a85dbe63b0f2ab02df431f9e7f8123ee12727eb4489e28af78c989380c4859822b986816ea2b2a90b1ba79ce1e47885c520bd0e7c109a91347aed8dbedd1074aeeaebd100ce84667e7e237c7765c8b582537c9079ca0c4dbc992abf86387b289c7c062f2e00190003ab97cbd04b4c9b4d9d1906d02b92d868ee93526f3408417077e7edd8210a84460f209a8cee8478310d656520853124dd01d77395818068ca8ca56ec42f22a8ad08e95c4c706424c430dcb814afdd342766350458e1615ed9de31f594d87daac785a7ef9a040bfa92dbbf4fe70546d966d1078de0f236d0047651b3675968862629d7e1c8722f2effe668a5c095453e916a68ea9306723f4bc16579637a5d15894bcbf957fb59c96786c42f30f91fd0badd798bcb53c188962e4b9aa9ac844b28b556a2d5d70dea81e1eb53d2b91abe4337c2569c1bef16b50a9961c62b788104842b12350e3ecd047965df60ee9031e44ea5d8de5d4a3e0806d547622c248ca2ffefc63a29243b76cb54d64d59896d8c2ec4eaf3e8ce80316c27e8bb1da9dba02f6e85d5c297c56ab9bb987963c6fff4b7896dc44c40e36c7feb1a3fd8471f91d39c6fccc91e523d545b3f05e184e10327ab3830ed1d9826de921ca48a98a53cdc9bc8767a3fd3047d21edd73234fa40090aa8c8fcc15681afa3d36f4a30a7e058e10a2eba0027a3a9af756b144e93c793d25c85c5cca175441ca6b43893b4e9943332e666a880756ce40b4e5ee6297a3fbd017611c158420125eb3ce1678d281797ef2e4dee60938c6ec3c07575ba851cbbf6fe35c85cc9cf0f68dd99e725afefbb21fee0047dd28936ec9ab75c93727e3d1cc402c8045103bed190f0eaa7e53b8c69a81f2f633ce989ddc56e8492e064278cb054c49c9cf404c0d9d5dd3691484a29b27a81a0625eff85cca3deb16fc9107dece2b31c193b58b2d9e3a8c128edb0ceb73b846c1ee7ae2f2dd134c941e2fa566b52856b95db93240775c2f31047f8936e9bdca4b63c4105b498a94542b660e4ea3fe1b7b4e129270e5c657b1a0cbfc33ed0f6aeec3a99d6cf593a56f8703cd78f973cd87bbb37d5364339509801508dd63146431aac071c3c268afa4fb66dc177f852e32ff5187756e3e49d8af3768e643a2dc1f3ea0161b4dd1497c98bbcd69cfc5aa372a44960facd6e36b922864ee9c718ef146195a2a0f8357390cbc8a24968ce4c5f95704f98e1e7ef36949cc15746100aa89f3b971dadacfc3bfe7389cd383c0efd38e69f4f0292950f93aa31b87021cfdaaa82c80f9cbc2d1c622611f3088616ae57c371c4ec1b007dfa62cca212abc2877911368b63dee34fb093fc6dd45300cbbacb50f0399f55430a53962a6643e41ed289e588ab366c54e128cb8dbd19a700570dc2845f2b64338342bf3942f1d1bb987160012e673a9c8bf2f427f5d5d513a0ed5a118d71f510dabeec3f8b05735735a80434e0bc70dc77fbdd34921ead9cb7a70b6aacaa7985de940e12b687c15b194e5074fec82946d7b9d080b45e6220c96b9a7a4ac51b6423a50c364323e72f3ae8484886dc8fa247043d234fab0b3b92d58b601cfe32e94ee469f279ee5b32df50ff5e37e3d9c7fbdcac2f6649feaff4be9907ddf5861926abbbadaafddca485634d7224f0a48278f1e7e93da17a738bf3852acbdbec84b5f8f179d8680f18265d9da93b2c271ef98ae5b589dfbf97316d6905af607d1c7c321d703a1c7a9d06c122f34609ee67f72b6c9f247d3825055322795df60dcf71e70a93f1f4c2e5fe104332198046067727f8333f8873ff66594ce591fc78cb912ea56b11889fc448cd046623d2b64dc000a8c32d798443f079f4bfafdb6277af10eaaf97bae3c90cf461e5bb0a02d81d688b5df5d0c7652f61002993fb1e24870eda415400ffddfd79747361257418fe4817346b5639501eafad572be490297c425791d1b74cbf349064eee44528bb32ec175e5e18756379be68f7eb6f5d2c9bfbe2f1f9a8b7ecdc6604de50252e592293efab2e91f1002b250bd6e729e294c35e6b9ea10518d4608008b31427df01a93d0f3e0e84791bbdc722e78e58d8f59c4afc45a23c1186b24ebe4bbd304c0d595caa24b39a6ce13f7ae8bc29c033aeb106336d1b0e482236daca05abf9f1a90c85954fc0ffc86e35488bb1d0efb16e265606ffdc86d90986f029572a2f85f72ccb37924f54e4600aec35fb0c62f74e807e95bf315f2403227adba66fcc49631fba3c80ecdcdb7ba6af4fa6026228393551998497daa369c56ef3b3470ab07eae3f06bb40c7a0f7c4d5ad8db083ab5e873dc59669c7eea8a569d7de2585ddd02e58d120e746c5aa3665558cb5a7269dac55ec7ab3aed08d441e7993fa6fbac84a4c82cad3fb8d9ae768e671c1cf96f379d04fb66208d2349cc34524fdd8145c5a682eaaa308bbf984dcf68717e64421b7a536314fb54e70f017ee70f407e22ff17f894568d00198e65d318fcfa1df41e306cabaf34ad0cb0a4011d3a6c81e6678491455ff539c1fdbe71290058d27770343ea28996c484fa964b13639288ad0002889e333fa9ee248c375b46067597914c75e946d07a82d9b7c0aa17c703a6041d84477f1d4e077e1dac51d8f582751214c029974c0c022e74137ccfd841cef5ff1b8d2c83826be0e34f74c0375f295498508b0d7d631ca04f497fc8adeca9f4dd8e09a5f136b2c401a0f80a8483d90ec68b756b528fd4b6c59262ed1971d36caafe0379025c4a393686b9e190c65a22d3433e82003ccf8a86423ff20fd728411a5841fe915be2f8fd84d2896f359aa0f4d3465b9ce47711c5e2bb1f6f458866987819b564ce06e4e85897c75a21603d45b9344f463bd2c1f5e942a50a394db74db9322289870008d01ea297e577d0da32808fba3141e18f41ef6a9719e633d7c6991b73c2cd09934019a06bc152dce5d6881f869f6fa06ec43e2107ef8e261997c504b350d6

private def light (n : ℕ) : Bool :=
  if n≤158 then decide n.Prime else n.gcd 18532718694937347965436097530510785296823609396441045793117318330092082290386068409865488609988797000768975161352971551183449189831128213401843942132763743125584936372389347993692214687901085347282697877066265401639080576328353511479745865318400000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤25000) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 158 = 18532718694937347965436097530510785296823609396441045793117318330092082290386068409865488609988797000768975161352971551183449189831128213401843942132763743125584936372389347993692214687901085347282697877066265401639080576328353511479745865318400000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 158 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤25000 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 48 := by unfold smallValid; decide +kernel

private theorem sp48 : smallValid 48 49 := by unfold smallValid; decide +kernel

private theorem sp97 : smallValid 97 49 := by unfold smallValid; decide +kernel

private theorem sp146 : smallValid 146 49 := by unfold smallValid; decide +kernel

private theorem sp195 : smallValid 195 48 := by unfold smallValid; decide +kernel

private theorem sp243 : smallValid 243 49 := by unfold smallValid; decide +kernel

private theorem sp292 : smallValid 292 49 := by unfold smallValid; decide +kernel

private theorem sp341 : smallValid 341 49 := by unfold smallValid; decide +kernel

private theorem sp390 : smallValid 390 48 := by unfold smallValid; decide +kernel

private theorem sp438 : smallValid 438 49 := by unfold smallValid; decide +kernel

private theorem sp487 : smallValid 487 49 := by unfold smallValid; decide +kernel

private theorem sp536 : smallValid 536 49 := by unfold smallValid; decide +kernel

private theorem sp585 : smallValid 585 49 := by unfold smallValid; decide +kernel

private theorem sp634 : smallValid 634 49 := by unfold smallValid; decide +kernel

private theorem sp683 : smallValid 683 49 := by unfold smallValid; decide +kernel

private theorem sp732 : smallValid 732 49 := by unfold smallValid; decide +kernel

private theorem sp781 : smallValid 781 48 := by unfold smallValid; decide +kernel

private theorem sp829 : smallValid 829 49 := by unfold smallValid; decide +kernel

private theorem sp878 : smallValid 878 49 := by unfold smallValid; decide +kernel

private theorem sp927 : smallValid 927 49 := by unfold smallValid; decide +kernel

private theorem sp976 : smallValid 976 48 := by unfold smallValid; decide +kernel

private theorem sp1024 : smallValid 1024 49 := by unfold smallValid; decide +kernel

private theorem sp1073 : smallValid 1073 49 := by unfold smallValid; decide +kernel

private theorem sp1122 : smallValid 1122 49 := by unfold smallValid; decide +kernel

private theorem sp1171 : smallValid 1171 48 := by unfold smallValid; decide +kernel

private theorem sp1219 : smallValid 1219 49 := by unfold smallValid; decide +kernel

private theorem sp1268 : smallValid 1268 49 := by unfold smallValid; decide +kernel

private theorem sp1317 : smallValid 1317 49 := by unfold smallValid; decide +kernel

private theorem sp1366 : smallValid 1366 49 := by unfold smallValid; decide +kernel

private theorem sp1415 : smallValid 1415 49 := by unfold smallValid; decide +kernel

private theorem sp1464 : smallValid 1464 49 := by unfold smallValid; decide +kernel

private theorem sp1513 : smallValid 1513 49 := by unfold smallValid; decide +kernel

private theorem sp1562 : smallValid 1562 48 := by unfold smallValid; decide +kernel

private theorem sp1610 : smallValid 1610 49 := by unfold smallValid; decide +kernel

private theorem sp1659 : smallValid 1659 49 := by unfold smallValid; decide +kernel

private theorem sp1708 : smallValid 1708 49 := by unfold smallValid; decide +kernel

private theorem sp1757 : smallValid 1757 48 := by unfold smallValid; decide +kernel

private theorem sp1805 : smallValid 1805 49 := by unfold smallValid; decide +kernel

private theorem sp1854 : smallValid 1854 49 := by unfold smallValid; decide +kernel

private theorem sp1903 : smallValid 1903 49 := by unfold smallValid; decide +kernel

private theorem sp1952 : smallValid 1952 48 := by unfold smallValid; decide +kernel

private theorem sp2000 : smallValid 2000 49 := by unfold smallValid; decide +kernel

private theorem sp2049 : smallValid 2049 49 := by unfold smallValid; decide +kernel

private theorem sp2098 : smallValid 2098 49 := by unfold smallValid; decide +kernel

private theorem sp2147 : smallValid 2147 49 := by unfold smallValid; decide +kernel

private theorem sp2196 : smallValid 2196 49 := by unfold smallValid; decide +kernel

private theorem sp2245 : smallValid 2245 49 := by unfold smallValid; decide +kernel

private theorem sp2294 : smallValid 2294 49 := by unfold smallValid; decide +kernel

private theorem sp2343 : smallValid 2343 48 := by unfold smallValid; decide +kernel

private theorem sp2391 : smallValid 2391 49 := by unfold smallValid; decide +kernel

private theorem sp2440 : smallValid 2440 49 := by unfold smallValid; decide +kernel

private theorem sp2489 : smallValid 2489 49 := by unfold smallValid; decide +kernel

private theorem sp2538 : smallValid 2538 49 := by unfold smallValid; decide +kernel

private theorem sp2587 : smallValid 2587 49 := by unfold smallValid; decide +kernel

private theorem sp2636 : smallValid 2636 49 := by unfold smallValid; decide +kernel

private theorem sp2685 : smallValid 2685 49 := by unfold smallValid; decide +kernel

private theorem sp2734 : smallValid 2734 48 := by unfold smallValid; decide +kernel

private theorem sp2782 : smallValid 2782 49 := by unfold smallValid; decide +kernel

private theorem sp2831 : smallValid 2831 49 := by unfold smallValid; decide +kernel

private theorem sp2880 : smallValid 2880 49 := by unfold smallValid; decide +kernel

private theorem sp2929 : smallValid 2929 49 := by unfold smallValid; decide +kernel

private theorem sp2978 : smallValid 2978 49 := by unfold smallValid; decide +kernel

private theorem sp3027 : smallValid 3027 49 := by unfold smallValid; decide +kernel

private theorem sp3076 : smallValid 3076 49 := by unfold smallValid; decide +kernel

private theorem sp3125 : smallValid 3125 48 := by unfold smallValid; decide +kernel

private theorem sp3173 : smallValid 3173 49 := by unfold smallValid; decide +kernel

private theorem sp3222 : smallValid 3222 49 := by unfold smallValid; decide +kernel

private theorem sp3271 : smallValid 3271 49 := by unfold smallValid; decide +kernel

private theorem sp3320 : smallValid 3320 48 := by unfold smallValid; decide +kernel

private theorem sp3368 : smallValid 3368 49 := by unfold smallValid; decide +kernel

private theorem sp3417 : smallValid 3417 49 := by unfold smallValid; decide +kernel

private theorem sp3466 : smallValid 3466 49 := by unfold smallValid; decide +kernel

private theorem sp3515 : smallValid 3515 48 := by unfold smallValid; decide +kernel

private theorem sp3563 : smallValid 3563 49 := by unfold smallValid; decide +kernel

private theorem sp3612 : smallValid 3612 49 := by unfold smallValid; decide +kernel

private theorem sp3661 : smallValid 3661 49 := by unfold smallValid; decide +kernel

private theorem sp3710 : smallValid 3710 49 := by unfold smallValid; decide +kernel

private theorem sp3759 : smallValid 3759 49 := by unfold smallValid; decide +kernel

private theorem sp3808 : smallValid 3808 49 := by unfold smallValid; decide +kernel

private theorem sp3857 : smallValid 3857 49 := by unfold smallValid; decide +kernel

private theorem sp3906 : smallValid 3906 48 := by unfold smallValid; decide +kernel

private theorem sp3954 : smallValid 3954 49 := by unfold smallValid; decide +kernel

private theorem sp4003 : smallValid 4003 49 := by unfold smallValid; decide +kernel

private theorem sp4052 : smallValid 4052 49 := by unfold smallValid; decide +kernel

private theorem sp4101 : smallValid 4101 48 := by unfold smallValid; decide +kernel

private theorem sp4149 : smallValid 4149 49 := by unfold smallValid; decide +kernel

private theorem sp4198 : smallValid 4198 49 := by unfold smallValid; decide +kernel

private theorem sp4247 : smallValid 4247 49 := by unfold smallValid; decide +kernel

private theorem sp4296 : smallValid 4296 48 := by unfold smallValid; decide +kernel

private theorem sp4344 : smallValid 4344 49 := by unfold smallValid; decide +kernel

private theorem sp4393 : smallValid 4393 49 := by unfold smallValid; decide +kernel

private theorem sp4442 : smallValid 4442 49 := by unfold smallValid; decide +kernel

private theorem sp4491 : smallValid 4491 49 := by unfold smallValid; decide +kernel

private theorem sp4540 : smallValid 4540 49 := by unfold smallValid; decide +kernel

private theorem sp4589 : smallValid 4589 49 := by unfold smallValid; decide +kernel

private theorem sp4638 : smallValid 4638 49 := by unfold smallValid; decide +kernel

private theorem sp4687 : smallValid 4687 48 := by unfold smallValid; decide +kernel

private theorem sp4735 : smallValid 4735 49 := by unfold smallValid; decide +kernel

private theorem sp4784 : smallValid 4784 49 := by unfold smallValid; decide +kernel

private theorem sp4833 : smallValid 4833 49 := by unfold smallValid; decide +kernel

private theorem sp4882 : smallValid 4882 48 := by unfold smallValid; decide +kernel

private theorem sp4930 : smallValid 4930 49 := by unfold smallValid; decide +kernel

private theorem sp4979 : smallValid 4979 49 := by unfold smallValid; decide +kernel

private theorem sp5028 : smallValid 5028 49 := by unfold smallValid; decide +kernel

private theorem sp5077 : smallValid 5077 48 := by unfold smallValid; decide +kernel

private theorem sp5125 : smallValid 5125 49 := by unfold smallValid; decide +kernel

private theorem sp5174 : smallValid 5174 49 := by unfold smallValid; decide +kernel

private theorem sp5223 : smallValid 5223 49 := by unfold smallValid; decide +kernel

private theorem sp5272 : smallValid 5272 49 := by unfold smallValid; decide +kernel

private theorem sp5321 : smallValid 5321 49 := by unfold smallValid; decide +kernel

private theorem sp5370 : smallValid 5370 49 := by unfold smallValid; decide +kernel

private theorem sp5419 : smallValid 5419 49 := by unfold smallValid; decide +kernel

private theorem sp5468 : smallValid 5468 48 := by unfold smallValid; decide +kernel

private theorem sp5516 : smallValid 5516 49 := by unfold smallValid; decide +kernel

private theorem sp5565 : smallValid 5565 49 := by unfold smallValid; decide +kernel

private theorem sp5614 : smallValid 5614 49 := by unfold smallValid; decide +kernel

private theorem sp5663 : smallValid 5663 49 := by unfold smallValid; decide +kernel

private theorem sp5712 : smallValid 5712 49 := by unfold smallValid; decide +kernel

private theorem sp5761 : smallValid 5761 49 := by unfold smallValid; decide +kernel

private theorem sp5810 : smallValid 5810 49 := by unfold smallValid; decide +kernel

private theorem sp5859 : smallValid 5859 48 := by unfold smallValid; decide +kernel

private theorem sp5907 : smallValid 5907 49 := by unfold smallValid; decide +kernel

private theorem sp5956 : smallValid 5956 49 := by unfold smallValid; decide +kernel

private theorem sp6005 : smallValid 6005 49 := by unfold smallValid; decide +kernel

private theorem sp6054 : smallValid 6054 49 := by unfold smallValid; decide +kernel

private theorem sp6103 : smallValid 6103 49 := by unfold smallValid; decide +kernel

private theorem sp6152 : smallValid 6152 49 := by unfold smallValid; decide +kernel

private theorem sp6201 : smallValid 6201 49 := by unfold smallValid; decide +kernel

private theorem sp6250 : smallValid 6250 48 := by unfold smallValid; decide +kernel

private theorem sp6298 : smallValid 6298 49 := by unfold smallValid; decide +kernel

private theorem sp6347 : smallValid 6347 49 := by unfold smallValid; decide +kernel

private theorem sp6396 : smallValid 6396 49 := by unfold smallValid; decide +kernel

private theorem sp6445 : smallValid 6445 48 := by unfold smallValid; decide +kernel

private theorem sp6493 : smallValid 6493 49 := by unfold smallValid; decide +kernel

private theorem sp6542 : smallValid 6542 49 := by unfold smallValid; decide +kernel

private theorem sp6591 : smallValid 6591 49 := by unfold smallValid; decide +kernel

private theorem sp6640 : smallValid 6640 48 := by unfold smallValid; decide +kernel

private theorem sp6688 : smallValid 6688 49 := by unfold smallValid; decide +kernel

private theorem sp6737 : smallValid 6737 49 := by unfold smallValid; decide +kernel

private theorem sp6786 : smallValid 6786 49 := by unfold smallValid; decide +kernel

private theorem sp6835 : smallValid 6835 49 := by unfold smallValid; decide +kernel

private theorem sp6884 : smallValid 6884 49 := by unfold smallValid; decide +kernel

private theorem sp6933 : smallValid 6933 49 := by unfold smallValid; decide +kernel

private theorem sp6982 : smallValid 6982 49 := by unfold smallValid; decide +kernel

private theorem sp7031 : smallValid 7031 48 := by unfold smallValid; decide +kernel

private theorem sp7079 : smallValid 7079 49 := by unfold smallValid; decide +kernel

private theorem sp7128 : smallValid 7128 49 := by unfold smallValid; decide +kernel

private theorem sp7177 : smallValid 7177 49 := by unfold smallValid; decide +kernel

private theorem sp7226 : smallValid 7226 48 := by unfold smallValid; decide +kernel

private theorem sp7274 : smallValid 7274 49 := by unfold smallValid; decide +kernel

private theorem sp7323 : smallValid 7323 49 := by unfold smallValid; decide +kernel

private theorem sp7372 : smallValid 7372 49 := by unfold smallValid; decide +kernel

private theorem sp7421 : smallValid 7421 48 := by unfold smallValid; decide +kernel

private theorem sp7469 : smallValid 7469 49 := by unfold smallValid; decide +kernel

private theorem sp7518 : smallValid 7518 49 := by unfold smallValid; decide +kernel

private theorem sp7567 : smallValid 7567 49 := by unfold smallValid; decide +kernel

private theorem sp7616 : smallValid 7616 49 := by unfold smallValid; decide +kernel

private theorem sp7665 : smallValid 7665 49 := by unfold smallValid; decide +kernel

private theorem sp7714 : smallValid 7714 49 := by unfold smallValid; decide +kernel

private theorem sp7763 : smallValid 7763 49 := by unfold smallValid; decide +kernel

private theorem sp7812 : smallValid 7812 48 := by unfold smallValid; decide +kernel

private theorem sp7860 : smallValid 7860 49 := by unfold smallValid; decide +kernel

private theorem sp7909 : smallValid 7909 49 := by unfold smallValid; decide +kernel

private theorem sp7958 : smallValid 7958 49 := by unfold smallValid; decide +kernel

private theorem sp8007 : smallValid 8007 48 := by unfold smallValid; decide +kernel

private theorem sp8055 : smallValid 8055 49 := by unfold smallValid; decide +kernel

private theorem sp8104 : smallValid 8104 49 := by unfold smallValid; decide +kernel

private theorem sp8153 : smallValid 8153 49 := by unfold smallValid; decide +kernel

private theorem sp8202 : smallValid 8202 48 := by unfold smallValid; decide +kernel

private theorem sp8250 : smallValid 8250 49 := by unfold smallValid; decide +kernel

private theorem sp8299 : smallValid 8299 49 := by unfold smallValid; decide +kernel

private theorem sp8348 : smallValid 8348 49 := by unfold smallValid; decide +kernel

private theorem sp8397 : smallValid 8397 49 := by unfold smallValid; decide +kernel

private theorem sp8446 : smallValid 8446 49 := by unfold smallValid; decide +kernel

private theorem sp8495 : smallValid 8495 49 := by unfold smallValid; decide +kernel

private theorem sp8544 : smallValid 8544 49 := by unfold smallValid; decide +kernel

private theorem sp8593 : smallValid 8593 48 := by unfold smallValid; decide +kernel

private theorem sp8641 : smallValid 8641 49 := by unfold smallValid; decide +kernel

private theorem sp8690 : smallValid 8690 49 := by unfold smallValid; decide +kernel

private theorem sp8739 : smallValid 8739 49 := by unfold smallValid; decide +kernel

private theorem sp8788 : smallValid 8788 49 := by unfold smallValid; decide +kernel

private theorem sp8837 : smallValid 8837 49 := by unfold smallValid; decide +kernel

private theorem sp8886 : smallValid 8886 49 := by unfold smallValid; decide +kernel

private theorem sp8935 : smallValid 8935 49 := by unfold smallValid; decide +kernel

private theorem sp8984 : smallValid 8984 48 := by unfold smallValid; decide +kernel

private theorem sp9032 : smallValid 9032 49 := by unfold smallValid; decide +kernel

private theorem sp9081 : smallValid 9081 49 := by unfold smallValid; decide +kernel

private theorem sp9130 : smallValid 9130 49 := by unfold smallValid; decide +kernel

private theorem sp9179 : smallValid 9179 49 := by unfold smallValid; decide +kernel

private theorem sp9228 : smallValid 9228 49 := by unfold smallValid; decide +kernel

private theorem sp9277 : smallValid 9277 49 := by unfold smallValid; decide +kernel

private theorem sp9326 : smallValid 9326 49 := by unfold smallValid; decide +kernel

private theorem sp9375 : smallValid 9375 48 := by unfold smallValid; decide +kernel

private theorem sp9423 : smallValid 9423 49 := by unfold smallValid; decide +kernel

private theorem sp9472 : smallValid 9472 49 := by unfold smallValid; decide +kernel

private theorem sp9521 : smallValid 9521 49 := by unfold smallValid; decide +kernel

private theorem sp9570 : smallValid 9570 48 := by unfold smallValid; decide +kernel

private theorem sp9618 : smallValid 9618 49 := by unfold smallValid; decide +kernel

private theorem sp9667 : smallValid 9667 49 := by unfold smallValid; decide +kernel

private theorem sp9716 : smallValid 9716 49 := by unfold smallValid; decide +kernel

private theorem sp9765 : smallValid 9765 48 := by unfold smallValid; decide +kernel

private theorem sp9813 : smallValid 9813 49 := by unfold smallValid; decide +kernel

private theorem sp9862 : smallValid 9862 49 := by unfold smallValid; decide +kernel

private theorem sp9911 : smallValid 9911 49 := by unfold smallValid; decide +kernel

private theorem sp9960 : smallValid 9960 49 := by unfold smallValid; decide +kernel

private theorem sp10009 : smallValid 10009 49 := by unfold smallValid; decide +kernel

private theorem sp10058 : smallValid 10058 49 := by unfold smallValid; decide +kernel

private theorem sp10107 : smallValid 10107 49 := by unfold smallValid; decide +kernel

private theorem sp10156 : smallValid 10156 48 := by unfold smallValid; decide +kernel

private theorem sp10204 : smallValid 10204 49 := by unfold smallValid; decide +kernel

private theorem sp10253 : smallValid 10253 49 := by unfold smallValid; decide +kernel

private theorem sp10302 : smallValid 10302 49 := by unfold smallValid; decide +kernel

private theorem sp10351 : smallValid 10351 48 := by unfold smallValid; decide +kernel

private theorem sp10399 : smallValid 10399 49 := by unfold smallValid; decide +kernel

private theorem sp10448 : smallValid 10448 49 := by unfold smallValid; decide +kernel

private theorem sp10497 : smallValid 10497 49 := by unfold smallValid; decide +kernel

private theorem sp10546 : smallValid 10546 48 := by unfold smallValid; decide +kernel

private theorem sp10594 : smallValid 10594 49 := by unfold smallValid; decide +kernel

private theorem sp10643 : smallValid 10643 49 := by unfold smallValid; decide +kernel

private theorem sp10692 : smallValid 10692 49 := by unfold smallValid; decide +kernel

private theorem sp10741 : smallValid 10741 49 := by unfold smallValid; decide +kernel

private theorem sp10790 : smallValid 10790 49 := by unfold smallValid; decide +kernel

private theorem sp10839 : smallValid 10839 49 := by unfold smallValid; decide +kernel

private theorem sp10888 : smallValid 10888 49 := by unfold smallValid; decide +kernel

private theorem sp10937 : smallValid 10937 48 := by unfold smallValid; decide +kernel

private theorem sp10985 : smallValid 10985 49 := by unfold smallValid; decide +kernel

private theorem sp11034 : smallValid 11034 49 := by unfold smallValid; decide +kernel

private theorem sp11083 : smallValid 11083 49 := by unfold smallValid; decide +kernel

private theorem sp11132 : smallValid 11132 48 := by unfold smallValid; decide +kernel

private theorem sp11180 : smallValid 11180 49 := by unfold smallValid; decide +kernel

private theorem sp11229 : smallValid 11229 49 := by unfold smallValid; decide +kernel

private theorem sp11278 : smallValid 11278 49 := by unfold smallValid; decide +kernel

private theorem sp11327 : smallValid 11327 48 := by unfold smallValid; decide +kernel

private theorem sp11375 : smallValid 11375 49 := by unfold smallValid; decide +kernel

private theorem sp11424 : smallValid 11424 49 := by unfold smallValid; decide +kernel

private theorem sp11473 : smallValid 11473 49 := by unfold smallValid; decide +kernel

private theorem sp11522 : smallValid 11522 49 := by unfold smallValid; decide +kernel

private theorem sp11571 : smallValid 11571 49 := by unfold smallValid; decide +kernel

private theorem sp11620 : smallValid 11620 49 := by unfold smallValid; decide +kernel

private theorem sp11669 : smallValid 11669 49 := by unfold smallValid; decide +kernel

private theorem sp11718 : smallValid 11718 48 := by unfold smallValid; decide +kernel

private theorem sp11766 : smallValid 11766 49 := by unfold smallValid; decide +kernel

private theorem sp11815 : smallValid 11815 49 := by unfold smallValid; decide +kernel

private theorem sp11864 : smallValid 11864 49 := by unfold smallValid; decide +kernel

private theorem sp11913 : smallValid 11913 49 := by unfold smallValid; decide +kernel

private theorem sp11962 : smallValid 11962 49 := by unfold smallValid; decide +kernel

private theorem sp12011 : smallValid 12011 49 := by unfold smallValid; decide +kernel

private theorem sp12060 : smallValid 12060 49 := by unfold smallValid; decide +kernel

private theorem sp12109 : smallValid 12109 48 := by unfold smallValid; decide +kernel

private theorem sp12157 : smallValid 12157 49 := by unfold smallValid; decide +kernel

private theorem sp12206 : smallValid 12206 49 := by unfold smallValid; decide +kernel

private theorem sp12255 : smallValid 12255 49 := by unfold smallValid; decide +kernel

private theorem sp12304 : smallValid 12304 49 := by unfold smallValid; decide +kernel

private theorem sp12353 : smallValid 12353 49 := by unfold smallValid; decide +kernel

private theorem sp12402 : smallValid 12402 49 := by unfold smallValid; decide +kernel

private theorem sp12451 : smallValid 12451 49 := by unfold smallValid; decide +kernel

private theorem sp12500 : smallValid 12500 48 := by unfold smallValid; decide +kernel

private theorem sp12548 : smallValid 12548 49 := by unfold smallValid; decide +kernel

private theorem sp12597 : smallValid 12597 49 := by unfold smallValid; decide +kernel

private theorem sp12646 : smallValid 12646 49 := by unfold smallValid; decide +kernel

private theorem sp12695 : smallValid 12695 48 := by unfold smallValid; decide +kernel

private theorem sp12743 : smallValid 12743 49 := by unfold smallValid; decide +kernel

private theorem sp12792 : smallValid 12792 49 := by unfold smallValid; decide +kernel

private theorem sp12841 : smallValid 12841 49 := by unfold smallValid; decide +kernel

private theorem sp12890 : smallValid 12890 48 := by unfold smallValid; decide +kernel

private theorem sp12938 : smallValid 12938 49 := by unfold smallValid; decide +kernel

private theorem sp12987 : smallValid 12987 49 := by unfold smallValid; decide +kernel

private theorem sp13036 : smallValid 13036 49 := by unfold smallValid; decide +kernel

private theorem sp13085 : smallValid 13085 49 := by unfold smallValid; decide +kernel

private theorem sp13134 : smallValid 13134 49 := by unfold smallValid; decide +kernel

private theorem sp13183 : smallValid 13183 49 := by unfold smallValid; decide +kernel

private theorem sp13232 : smallValid 13232 49 := by unfold smallValid; decide +kernel

private theorem sp13281 : smallValid 13281 48 := by unfold smallValid; decide +kernel

private theorem sp13329 : smallValid 13329 49 := by unfold smallValid; decide +kernel

private theorem sp13378 : smallValid 13378 49 := by unfold smallValid; decide +kernel

private theorem sp13427 : smallValid 13427 49 := by unfold smallValid; decide +kernel

private theorem sp13476 : smallValid 13476 48 := by unfold smallValid; decide +kernel

private theorem sp13524 : smallValid 13524 49 := by unfold smallValid; decide +kernel

private theorem sp13573 : smallValid 13573 49 := by unfold smallValid; decide +kernel

private theorem sp13622 : smallValid 13622 49 := by unfold smallValid; decide +kernel

private theorem sp13671 : smallValid 13671 48 := by unfold smallValid; decide +kernel

private theorem sp13719 : smallValid 13719 49 := by unfold smallValid; decide +kernel

private theorem sp13768 : smallValid 13768 49 := by unfold smallValid; decide +kernel

private theorem sp13817 : smallValid 13817 49 := by unfold smallValid; decide +kernel

private theorem sp13866 : smallValid 13866 49 := by unfold smallValid; decide +kernel

private theorem sp13915 : smallValid 13915 49 := by unfold smallValid; decide +kernel

private theorem sp13964 : smallValid 13964 49 := by unfold smallValid; decide +kernel

private theorem sp14013 : smallValid 14013 49 := by unfold smallValid; decide +kernel

private theorem sp14062 : smallValid 14062 48 := by unfold smallValid; decide +kernel

private theorem sp14110 : smallValid 14110 49 := by unfold smallValid; decide +kernel

private theorem sp14159 : smallValid 14159 49 := by unfold smallValid; decide +kernel

private theorem sp14208 : smallValid 14208 49 := by unfold smallValid; decide +kernel

private theorem sp14257 : smallValid 14257 48 := by unfold smallValid; decide +kernel

private theorem sp14305 : smallValid 14305 49 := by unfold smallValid; decide +kernel

private theorem sp14354 : smallValid 14354 49 := by unfold smallValid; decide +kernel

private theorem sp14403 : smallValid 14403 49 := by unfold smallValid; decide +kernel

private theorem sp14452 : smallValid 14452 48 := by unfold smallValid; decide +kernel

private theorem sp14500 : smallValid 14500 49 := by unfold smallValid; decide +kernel

private theorem sp14549 : smallValid 14549 49 := by unfold smallValid; decide +kernel

private theorem sp14598 : smallValid 14598 49 := by unfold smallValid; decide +kernel

private theorem sp14647 : smallValid 14647 49 := by unfold smallValid; decide +kernel

private theorem sp14696 : smallValid 14696 49 := by unfold smallValid; decide +kernel

private theorem sp14745 : smallValid 14745 49 := by unfold smallValid; decide +kernel

private theorem sp14794 : smallValid 14794 49 := by unfold smallValid; decide +kernel

private theorem sp14843 : smallValid 14843 48 := by unfold smallValid; decide +kernel

private theorem sp14891 : smallValid 14891 49 := by unfold smallValid; decide +kernel

private theorem sp14940 : smallValid 14940 49 := by unfold smallValid; decide +kernel

private theorem sp14989 : smallValid 14989 49 := by unfold smallValid; decide +kernel

private theorem sp15038 : smallValid 15038 49 := by unfold smallValid; decide +kernel

private theorem sp15087 : smallValid 15087 49 := by unfold smallValid; decide +kernel

private theorem sp15136 : smallValid 15136 49 := by unfold smallValid; decide +kernel

private theorem sp15185 : smallValid 15185 49 := by unfold smallValid; decide +kernel

private theorem sp15234 : smallValid 15234 48 := by unfold smallValid; decide +kernel

private theorem sp15282 : smallValid 15282 49 := by unfold smallValid; decide +kernel

private theorem sp15331 : smallValid 15331 49 := by unfold smallValid; decide +kernel

private theorem sp15380 : smallValid 15380 49 := by unfold smallValid; decide +kernel

private theorem sp15429 : smallValid 15429 49 := by unfold smallValid; decide +kernel

private theorem sp15478 : smallValid 15478 49 := by unfold smallValid; decide +kernel

private theorem sp15527 : smallValid 15527 49 := by unfold smallValid; decide +kernel

private theorem sp15576 : smallValid 15576 49 := by unfold smallValid; decide +kernel

private theorem sp15625 : smallValid 15625 48 := by unfold smallValid; decide +kernel

private theorem sp15673 : smallValid 15673 49 := by unfold smallValid; decide +kernel

private theorem sp15722 : smallValid 15722 49 := by unfold smallValid; decide +kernel

private theorem sp15771 : smallValid 15771 49 := by unfold smallValid; decide +kernel

private theorem sp15820 : smallValid 15820 48 := by unfold smallValid; decide +kernel

private theorem sp15868 : smallValid 15868 49 := by unfold smallValid; decide +kernel

private theorem sp15917 : smallValid 15917 49 := by unfold smallValid; decide +kernel

private theorem sp15966 : smallValid 15966 49 := by unfold smallValid; decide +kernel

private theorem sp16015 : smallValid 16015 48 := by unfold smallValid; decide +kernel

private theorem sp16063 : smallValid 16063 49 := by unfold smallValid; decide +kernel

private theorem sp16112 : smallValid 16112 49 := by unfold smallValid; decide +kernel

private theorem sp16161 : smallValid 16161 49 := by unfold smallValid; decide +kernel

private theorem sp16210 : smallValid 16210 49 := by unfold smallValid; decide +kernel

private theorem sp16259 : smallValid 16259 49 := by unfold smallValid; decide +kernel

private theorem sp16308 : smallValid 16308 49 := by unfold smallValid; decide +kernel

private theorem sp16357 : smallValid 16357 49 := by unfold smallValid; decide +kernel

private theorem sp16406 : smallValid 16406 48 := by unfold smallValid; decide +kernel

private theorem sp16454 : smallValid 16454 49 := by unfold smallValid; decide +kernel

private theorem sp16503 : smallValid 16503 49 := by unfold smallValid; decide +kernel

private theorem sp16552 : smallValid 16552 49 := by unfold smallValid; decide +kernel

private theorem sp16601 : smallValid 16601 48 := by unfold smallValid; decide +kernel

private theorem sp16649 : smallValid 16649 49 := by unfold smallValid; decide +kernel

private theorem sp16698 : smallValid 16698 49 := by unfold smallValid; decide +kernel

private theorem sp16747 : smallValid 16747 49 := by unfold smallValid; decide +kernel

private theorem sp16796 : smallValid 16796 48 := by unfold smallValid; decide +kernel

private theorem sp16844 : smallValid 16844 49 := by unfold smallValid; decide +kernel

private theorem sp16893 : smallValid 16893 49 := by unfold smallValid; decide +kernel

private theorem sp16942 : smallValid 16942 49 := by unfold smallValid; decide +kernel

private theorem sp16991 : smallValid 16991 49 := by unfold smallValid; decide +kernel

private theorem sp17040 : smallValid 17040 49 := by unfold smallValid; decide +kernel

private theorem sp17089 : smallValid 17089 49 := by unfold smallValid; decide +kernel

private theorem sp17138 : smallValid 17138 49 := by unfold smallValid; decide +kernel

private theorem sp17187 : smallValid 17187 48 := by unfold smallValid; decide +kernel

private theorem sp17235 : smallValid 17235 49 := by unfold smallValid; decide +kernel

private theorem sp17284 : smallValid 17284 49 := by unfold smallValid; decide +kernel

private theorem sp17333 : smallValid 17333 49 := by unfold smallValid; decide +kernel

private theorem sp17382 : smallValid 17382 48 := by unfold smallValid; decide +kernel

private theorem sp17430 : smallValid 17430 49 := by unfold smallValid; decide +kernel

private theorem sp17479 : smallValid 17479 49 := by unfold smallValid; decide +kernel

private theorem sp17528 : smallValid 17528 49 := by unfold smallValid; decide +kernel

private theorem sp17577 : smallValid 17577 48 := by unfold smallValid; decide +kernel

private theorem sp17625 : smallValid 17625 49 := by unfold smallValid; decide +kernel

private theorem sp17674 : smallValid 17674 49 := by unfold smallValid; decide +kernel

private theorem sp17723 : smallValid 17723 49 := by unfold smallValid; decide +kernel

private theorem sp17772 : smallValid 17772 49 := by unfold smallValid; decide +kernel

private theorem sp17821 : smallValid 17821 49 := by unfold smallValid; decide +kernel

private theorem sp17870 : smallValid 17870 49 := by unfold smallValid; decide +kernel

private theorem sp17919 : smallValid 17919 49 := by unfold smallValid; decide +kernel

private theorem sp17968 : smallValid 17968 48 := by unfold smallValid; decide +kernel

private theorem sp18016 : smallValid 18016 49 := by unfold smallValid; decide +kernel

private theorem sp18065 : smallValid 18065 49 := by unfold smallValid; decide +kernel

private theorem sp18114 : smallValid 18114 49 := by unfold smallValid; decide +kernel

private theorem sp18163 : smallValid 18163 49 := by unfold smallValid; decide +kernel

private theorem sp18212 : smallValid 18212 49 := by unfold smallValid; decide +kernel

private theorem sp18261 : smallValid 18261 49 := by unfold smallValid; decide +kernel

private theorem sp18310 : smallValid 18310 49 := by unfold smallValid; decide +kernel

private theorem sp18359 : smallValid 18359 48 := by unfold smallValid; decide +kernel

private theorem sp18407 : smallValid 18407 49 := by unfold smallValid; decide +kernel

private theorem sp18456 : smallValid 18456 49 := by unfold smallValid; decide +kernel

private theorem sp18505 : smallValid 18505 49 := by unfold smallValid; decide +kernel

private theorem sp18554 : smallValid 18554 49 := by unfold smallValid; decide +kernel

private theorem sp18603 : smallValid 18603 49 := by unfold smallValid; decide +kernel

private theorem sp18652 : smallValid 18652 49 := by unfold smallValid; decide +kernel

private theorem sp18701 : smallValid 18701 49 := by unfold smallValid; decide +kernel

private theorem sp18750 : smallValid 18750 48 := by unfold smallValid; decide +kernel

private theorem sp18798 : smallValid 18798 49 := by unfold smallValid; decide +kernel

private theorem sp18847 : smallValid 18847 49 := by unfold smallValid; decide +kernel

private theorem sp18896 : smallValid 18896 49 := by unfold smallValid; decide +kernel

private theorem sp18945 : smallValid 18945 48 := by unfold smallValid; decide +kernel

private theorem sp18993 : smallValid 18993 49 := by unfold smallValid; decide +kernel

private theorem sp19042 : smallValid 19042 49 := by unfold smallValid; decide +kernel

private theorem sp19091 : smallValid 19091 49 := by unfold smallValid; decide +kernel

private theorem sp19140 : smallValid 19140 48 := by unfold smallValid; decide +kernel

private theorem sp19188 : smallValid 19188 49 := by unfold smallValid; decide +kernel

private theorem sp19237 : smallValid 19237 49 := by unfold smallValid; decide +kernel

private theorem sp19286 : smallValid 19286 49 := by unfold smallValid; decide +kernel

private theorem sp19335 : smallValid 19335 49 := by unfold smallValid; decide +kernel

private theorem sp19384 : smallValid 19384 49 := by unfold smallValid; decide +kernel

private theorem sp19433 : smallValid 19433 49 := by unfold smallValid; decide +kernel

private theorem sp19482 : smallValid 19482 49 := by unfold smallValid; decide +kernel

private theorem sp19531 : smallValid 19531 48 := by unfold smallValid; decide +kernel

private theorem sp19579 : smallValid 19579 49 := by unfold smallValid; decide +kernel

private theorem sp19628 : smallValid 19628 49 := by unfold smallValid; decide +kernel

private theorem sp19677 : smallValid 19677 49 := by unfold smallValid; decide +kernel

private theorem sp19726 : smallValid 19726 48 := by unfold smallValid; decide +kernel

private theorem sp19774 : smallValid 19774 49 := by unfold smallValid; decide +kernel

private theorem sp19823 : smallValid 19823 49 := by unfold smallValid; decide +kernel

private theorem sp19872 : smallValid 19872 49 := by unfold smallValid; decide +kernel

private theorem sp19921 : smallValid 19921 48 := by unfold smallValid; decide +kernel

private theorem sp19969 : smallValid 19969 49 := by unfold smallValid; decide +kernel

private theorem sp20018 : smallValid 20018 49 := by unfold smallValid; decide +kernel

private theorem sp20067 : smallValid 20067 49 := by unfold smallValid; decide +kernel

private theorem sp20116 : smallValid 20116 49 := by unfold smallValid; decide +kernel

private theorem sp20165 : smallValid 20165 49 := by unfold smallValid; decide +kernel

private theorem sp20214 : smallValid 20214 49 := by unfold smallValid; decide +kernel

private theorem sp20263 : smallValid 20263 49 := by unfold smallValid; decide +kernel

private theorem sp20312 : smallValid 20312 48 := by unfold smallValid; decide +kernel

private theorem sp20360 : smallValid 20360 49 := by unfold smallValid; decide +kernel

private theorem sp20409 : smallValid 20409 49 := by unfold smallValid; decide +kernel

private theorem sp20458 : smallValid 20458 49 := by unfold smallValid; decide +kernel

private theorem sp20507 : smallValid 20507 48 := by unfold smallValid; decide +kernel

private theorem sp20555 : smallValid 20555 49 := by unfold smallValid; decide +kernel

private theorem sp20604 : smallValid 20604 49 := by unfold smallValid; decide +kernel

private theorem sp20653 : smallValid 20653 49 := by unfold smallValid; decide +kernel

private theorem sp20702 : smallValid 20702 48 := by unfold smallValid; decide +kernel

private theorem sp20750 : smallValid 20750 49 := by unfold smallValid; decide +kernel

private theorem sp20799 : smallValid 20799 49 := by unfold smallValid; decide +kernel

private theorem sp20848 : smallValid 20848 49 := by unfold smallValid; decide +kernel

private theorem sp20897 : smallValid 20897 49 := by unfold smallValid; decide +kernel

private theorem sp20946 : smallValid 20946 49 := by unfold smallValid; decide +kernel

private theorem sp20995 : smallValid 20995 49 := by unfold smallValid; decide +kernel

private theorem sp21044 : smallValid 21044 49 := by unfold smallValid; decide +kernel

private theorem sp21093 : smallValid 21093 48 := by unfold smallValid; decide +kernel

private theorem sp21141 : smallValid 21141 49 := by unfold smallValid; decide +kernel

private theorem sp21190 : smallValid 21190 49 := by unfold smallValid; decide +kernel

private theorem sp21239 : smallValid 21239 49 := by unfold smallValid; decide +kernel

private theorem sp21288 : smallValid 21288 49 := by unfold smallValid; decide +kernel

private theorem sp21337 : smallValid 21337 49 := by unfold smallValid; decide +kernel

private theorem sp21386 : smallValid 21386 49 := by unfold smallValid; decide +kernel

private theorem sp21435 : smallValid 21435 49 := by unfold smallValid; decide +kernel

private theorem sp21484 : smallValid 21484 48 := by unfold smallValid; decide +kernel

private theorem sp21532 : smallValid 21532 49 := by unfold smallValid; decide +kernel

private theorem sp21581 : smallValid 21581 49 := by unfold smallValid; decide +kernel

private theorem sp21630 : smallValid 21630 49 := by unfold smallValid; decide +kernel

private theorem sp21679 : smallValid 21679 49 := by unfold smallValid; decide +kernel

private theorem sp21728 : smallValid 21728 49 := by unfold smallValid; decide +kernel

private theorem sp21777 : smallValid 21777 49 := by unfold smallValid; decide +kernel

private theorem sp21826 : smallValid 21826 49 := by unfold smallValid; decide +kernel

private theorem sp21875 : smallValid 21875 48 := by unfold smallValid; decide +kernel

private theorem sp21923 : smallValid 21923 49 := by unfold smallValid; decide +kernel

private theorem sp21972 : smallValid 21972 49 := by unfold smallValid; decide +kernel

private theorem sp22021 : smallValid 22021 49 := by unfold smallValid; decide +kernel

private theorem sp22070 : smallValid 22070 48 := by unfold smallValid; decide +kernel

private theorem sp22118 : smallValid 22118 49 := by unfold smallValid; decide +kernel

private theorem sp22167 : smallValid 22167 49 := by unfold smallValid; decide +kernel

private theorem sp22216 : smallValid 22216 49 := by unfold smallValid; decide +kernel

private theorem sp22265 : smallValid 22265 48 := by unfold smallValid; decide +kernel

private theorem sp22313 : smallValid 22313 49 := by unfold smallValid; decide +kernel

private theorem sp22362 : smallValid 22362 49 := by unfold smallValid; decide +kernel

private theorem sp22411 : smallValid 22411 49 := by unfold smallValid; decide +kernel

private theorem sp22460 : smallValid 22460 49 := by unfold smallValid; decide +kernel

private theorem sp22509 : smallValid 22509 49 := by unfold smallValid; decide +kernel

private theorem sp22558 : smallValid 22558 49 := by unfold smallValid; decide +kernel

private theorem sp22607 : smallValid 22607 49 := by unfold smallValid; decide +kernel

private theorem sp22656 : smallValid 22656 48 := by unfold smallValid; decide +kernel

private theorem sp22704 : smallValid 22704 49 := by unfold smallValid; decide +kernel

private theorem sp22753 : smallValid 22753 49 := by unfold smallValid; decide +kernel

private theorem sp22802 : smallValid 22802 49 := by unfold smallValid; decide +kernel

private theorem sp22851 : smallValid 22851 49 := by unfold smallValid; decide +kernel

private theorem sp22900 : smallValid 22900 49 := by unfold smallValid; decide +kernel

private theorem sp22949 : smallValid 22949 49 := by unfold smallValid; decide +kernel

private theorem sp22998 : smallValid 22998 49 := by unfold smallValid; decide +kernel

private theorem sp23047 : smallValid 23047 48 := by unfold smallValid; decide +kernel

private theorem sp23095 : smallValid 23095 49 := by unfold smallValid; decide +kernel

private theorem sp23144 : smallValid 23144 49 := by unfold smallValid; decide +kernel

private theorem sp23193 : smallValid 23193 49 := by unfold smallValid; decide +kernel

private theorem sp23242 : smallValid 23242 49 := by unfold smallValid; decide +kernel

private theorem sp23291 : smallValid 23291 49 := by unfold smallValid; decide +kernel

private theorem sp23340 : smallValid 23340 49 := by unfold smallValid; decide +kernel

private theorem sp23389 : smallValid 23389 49 := by unfold smallValid; decide +kernel

private theorem sp23438 : smallValid 23438 48 := by unfold smallValid; decide +kernel

private theorem sp23486 : smallValid 23486 49 := by unfold smallValid; decide +kernel

private theorem sp23535 : smallValid 23535 49 := by unfold smallValid; decide +kernel

private theorem sp23584 : smallValid 23584 49 := by unfold smallValid; decide +kernel

private theorem sp23633 : smallValid 23633 48 := by unfold smallValid; decide +kernel

private theorem sp23681 : smallValid 23681 49 := by unfold smallValid; decide +kernel

private theorem sp23730 : smallValid 23730 49 := by unfold smallValid; decide +kernel

private theorem sp23779 : smallValid 23779 49 := by unfold smallValid; decide +kernel

private theorem sp23828 : smallValid 23828 48 := by unfold smallValid; decide +kernel

private theorem sp23876 : smallValid 23876 49 := by unfold smallValid; decide +kernel

private theorem sp23925 : smallValid 23925 49 := by unfold smallValid; decide +kernel

private theorem sp23974 : smallValid 23974 49 := by unfold smallValid; decide +kernel

private theorem sp24023 : smallValid 24023 49 := by unfold smallValid; decide +kernel

private theorem sp24072 : smallValid 24072 49 := by unfold smallValid; decide +kernel

private theorem sp24121 : smallValid 24121 49 := by unfold smallValid; decide +kernel

private theorem sp24170 : smallValid 24170 49 := by unfold smallValid; decide +kernel

private theorem sp24219 : smallValid 24219 48 := by unfold smallValid; decide +kernel

private theorem sp24267 : smallValid 24267 49 := by unfold smallValid; decide +kernel

private theorem sp24316 : smallValid 24316 49 := by unfold smallValid; decide +kernel

private theorem sp24365 : smallValid 24365 49 := by unfold smallValid; decide +kernel

private theorem sp24414 : smallValid 24414 49 := by unfold smallValid; decide +kernel

private theorem sp24463 : smallValid 24463 49 := by unfold smallValid; decide +kernel

private theorem sp24512 : smallValid 24512 49 := by unfold smallValid; decide +kernel

private theorem sp24561 : smallValid 24561 49 := by unfold smallValid; decide +kernel

private theorem sp24610 : smallValid 24610 48 := by unfold smallValid; decide +kernel

private theorem sp24658 : smallValid 24658 49 := by unfold smallValid; decide +kernel

private theorem sp24707 : smallValid 24707 49 := by unfold smallValid; decide +kernel

private theorem sp24756 : smallValid 24756 49 := by unfold smallValid; decide +kernel

private theorem sp24805 : smallValid 24805 49 := by unfold smallValid; decide +kernel

private theorem sp24854 : smallValid 24854 49 := by unfold smallValid; decide +kernel

private theorem sp24903 : smallValid 24903 49 := by unfold smallValid; decide +kernel

private theorem sp24952 : smallValid 24952 49 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤25000) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 25001 := (joinSmall (lo:=0) (a:=12500) (b:=12501) (joinSmall (lo:=0) (a:=6250) (b:=6250) (joinSmall (lo:=0) (a:=3125) (b:=3125) (joinSmall (lo:=0) (a:=1562) (b:=1563) (joinSmall (lo:=0) (a:=781) (b:=781) (joinSmall (lo:=0) (a:=390) (b:=391) (joinSmall (lo:=0) (a:=195) (b:=195) (joinSmall (lo:=0) (a:=97) (b:=98) (joinSmall (lo:=0) (a:=48) (b:=49) sp0 sp48) (joinSmall (lo:=97) (a:=49) (b:=49) sp97 sp146)) (joinSmall (lo:=195) (a:=97) (b:=98) (joinSmall (lo:=195) (a:=48) (b:=49) sp195 sp243) (joinSmall (lo:=292) (a:=49) (b:=49) sp292 sp341))) (joinSmall (lo:=390) (a:=195) (b:=196) (joinSmall (lo:=390) (a:=97) (b:=98) (joinSmall (lo:=390) (a:=48) (b:=49) sp390 sp438) (joinSmall (lo:=487) (a:=49) (b:=49) sp487 sp536)) (joinSmall (lo:=585) (a:=98) (b:=98) (joinSmall (lo:=585) (a:=49) (b:=49) sp585 sp634) (joinSmall (lo:=683) (a:=49) (b:=49) sp683 sp732)))) (joinSmall (lo:=781) (a:=390) (b:=391) (joinSmall (lo:=781) (a:=195) (b:=195) (joinSmall (lo:=781) (a:=97) (b:=98) (joinSmall (lo:=781) (a:=48) (b:=49) sp781 sp829) (joinSmall (lo:=878) (a:=49) (b:=49) sp878 sp927)) (joinSmall (lo:=976) (a:=97) (b:=98) (joinSmall (lo:=976) (a:=48) (b:=49) sp976 sp1024) (joinSmall (lo:=1073) (a:=49) (b:=49) sp1073 sp1122))) (joinSmall (lo:=1171) (a:=195) (b:=196) (joinSmall (lo:=1171) (a:=97) (b:=98) (joinSmall (lo:=1171) (a:=48) (b:=49) sp1171 sp1219) (joinSmall (lo:=1268) (a:=49) (b:=49) sp1268 sp1317)) (joinSmall (lo:=1366) (a:=98) (b:=98) (joinSmall (lo:=1366) (a:=49) (b:=49) sp1366 sp1415) (joinSmall (lo:=1464) (a:=49) (b:=49) sp1464 sp1513))))) (joinSmall (lo:=1562) (a:=781) (b:=782) (joinSmall (lo:=1562) (a:=390) (b:=391) (joinSmall (lo:=1562) (a:=195) (b:=195) (joinSmall (lo:=1562) (a:=97) (b:=98) (joinSmall (lo:=1562) (a:=48) (b:=49) sp1562 sp1610) (joinSmall (lo:=1659) (a:=49) (b:=49) sp1659 sp1708)) (joinSmall (lo:=1757) (a:=97) (b:=98) (joinSmall (lo:=1757) (a:=48) (b:=49) sp1757 sp1805) (joinSmall (lo:=1854) (a:=49) (b:=49) sp1854 sp1903))) (joinSmall (lo:=1952) (a:=195) (b:=196) (joinSmall (lo:=1952) (a:=97) (b:=98) (joinSmall (lo:=1952) (a:=48) (b:=49) sp1952 sp2000) (joinSmall (lo:=2049) (a:=49) (b:=49) sp2049 sp2098)) (joinSmall (lo:=2147) (a:=98) (b:=98) (joinSmall (lo:=2147) (a:=49) (b:=49) sp2147 sp2196) (joinSmall (lo:=2245) (a:=49) (b:=49) sp2245 sp2294)))) (joinSmall (lo:=2343) (a:=391) (b:=391) (joinSmall (lo:=2343) (a:=195) (b:=196) (joinSmall (lo:=2343) (a:=97) (b:=98) (joinSmall (lo:=2343) (a:=48) (b:=49) sp2343 sp2391) (joinSmall (lo:=2440) (a:=49) (b:=49) sp2440 sp2489)) (joinSmall (lo:=2538) (a:=98) (b:=98) (joinSmall (lo:=2538) (a:=49) (b:=49) sp2538 sp2587) (joinSmall (lo:=2636) (a:=49) (b:=49) sp2636 sp2685))) (joinSmall (lo:=2734) (a:=195) (b:=196) (joinSmall (lo:=2734) (a:=97) (b:=98) (joinSmall (lo:=2734) (a:=48) (b:=49) sp2734 sp2782) (joinSmall (lo:=2831) (a:=49) (b:=49) sp2831 sp2880)) (joinSmall (lo:=2929) (a:=98) (b:=98) (joinSmall (lo:=2929) (a:=49) (b:=49) sp2929 sp2978) (joinSmall (lo:=3027) (a:=49) (b:=49) sp3027 sp3076)))))) (joinSmall (lo:=3125) (a:=1562) (b:=1563) (joinSmall (lo:=3125) (a:=781) (b:=781) (joinSmall (lo:=3125) (a:=390) (b:=391) (joinSmall (lo:=3125) (a:=195) (b:=195) (joinSmall (lo:=3125) (a:=97) (b:=98) (joinSmall (lo:=3125) (a:=48) (b:=49) sp3125 sp3173) (joinSmall (lo:=3222) (a:=49) (b:=49) sp3222 sp3271)) (joinSmall (lo:=3320) (a:=97) (b:=98) (joinSmall (lo:=3320) (a:=48) (b:=49) sp3320 sp3368) (joinSmall (lo:=3417) (a:=49) (b:=49) sp3417 sp3466))) (joinSmall (lo:=3515) (a:=195) (b:=196) (joinSmall (lo:=3515) (a:=97) (b:=98) (joinSmall (lo:=3515) (a:=48) (b:=49) sp3515 sp3563) (joinSmall (lo:=3612) (a:=49) (b:=49) sp3612 sp3661)) (joinSmall (lo:=3710) (a:=98) (b:=98) (joinSmall (lo:=3710) (a:=49) (b:=49) sp3710 sp3759) (joinSmall (lo:=3808) (a:=49) (b:=49) sp3808 sp3857)))) (joinSmall (lo:=3906) (a:=390) (b:=391) (joinSmall (lo:=3906) (a:=195) (b:=195) (joinSmall (lo:=3906) (a:=97) (b:=98) (joinSmall (lo:=3906) (a:=48) (b:=49) sp3906 sp3954) (joinSmall (lo:=4003) (a:=49) (b:=49) sp4003 sp4052)) (joinSmall (lo:=4101) (a:=97) (b:=98) (joinSmall (lo:=4101) (a:=48) (b:=49) sp4101 sp4149) (joinSmall (lo:=4198) (a:=49) (b:=49) sp4198 sp4247))) (joinSmall (lo:=4296) (a:=195) (b:=196) (joinSmall (lo:=4296) (a:=97) (b:=98) (joinSmall (lo:=4296) (a:=48) (b:=49) sp4296 sp4344) (joinSmall (lo:=4393) (a:=49) (b:=49) sp4393 sp4442)) (joinSmall (lo:=4491) (a:=98) (b:=98) (joinSmall (lo:=4491) (a:=49) (b:=49) sp4491 sp4540) (joinSmall (lo:=4589) (a:=49) (b:=49) sp4589 sp4638))))) (joinSmall (lo:=4687) (a:=781) (b:=782) (joinSmall (lo:=4687) (a:=390) (b:=391) (joinSmall (lo:=4687) (a:=195) (b:=195) (joinSmall (lo:=4687) (a:=97) (b:=98) (joinSmall (lo:=4687) (a:=48) (b:=49) sp4687 sp4735) (joinSmall (lo:=4784) (a:=49) (b:=49) sp4784 sp4833)) (joinSmall (lo:=4882) (a:=97) (b:=98) (joinSmall (lo:=4882) (a:=48) (b:=49) sp4882 sp4930) (joinSmall (lo:=4979) (a:=49) (b:=49) sp4979 sp5028))) (joinSmall (lo:=5077) (a:=195) (b:=196) (joinSmall (lo:=5077) (a:=97) (b:=98) (joinSmall (lo:=5077) (a:=48) (b:=49) sp5077 sp5125) (joinSmall (lo:=5174) (a:=49) (b:=49) sp5174 sp5223)) (joinSmall (lo:=5272) (a:=98) (b:=98) (joinSmall (lo:=5272) (a:=49) (b:=49) sp5272 sp5321) (joinSmall (lo:=5370) (a:=49) (b:=49) sp5370 sp5419)))) (joinSmall (lo:=5468) (a:=391) (b:=391) (joinSmall (lo:=5468) (a:=195) (b:=196) (joinSmall (lo:=5468) (a:=97) (b:=98) (joinSmall (lo:=5468) (a:=48) (b:=49) sp5468 sp5516) (joinSmall (lo:=5565) (a:=49) (b:=49) sp5565 sp5614)) (joinSmall (lo:=5663) (a:=98) (b:=98) (joinSmall (lo:=5663) (a:=49) (b:=49) sp5663 sp5712) (joinSmall (lo:=5761) (a:=49) (b:=49) sp5761 sp5810))) (joinSmall (lo:=5859) (a:=195) (b:=196) (joinSmall (lo:=5859) (a:=97) (b:=98) (joinSmall (lo:=5859) (a:=48) (b:=49) sp5859 sp5907) (joinSmall (lo:=5956) (a:=49) (b:=49) sp5956 sp6005)) (joinSmall (lo:=6054) (a:=98) (b:=98) (joinSmall (lo:=6054) (a:=49) (b:=49) sp6054 sp6103) (joinSmall (lo:=6152) (a:=49) (b:=49) sp6152 sp6201))))))) (joinSmall (lo:=6250) (a:=3125) (b:=3125) (joinSmall (lo:=6250) (a:=1562) (b:=1563) (joinSmall (lo:=6250) (a:=781) (b:=781) (joinSmall (lo:=6250) (a:=390) (b:=391) (joinSmall (lo:=6250) (a:=195) (b:=195) (joinSmall (lo:=6250) (a:=97) (b:=98) (joinSmall (lo:=6250) (a:=48) (b:=49) sp6250 sp6298) (joinSmall (lo:=6347) (a:=49) (b:=49) sp6347 sp6396)) (joinSmall (lo:=6445) (a:=97) (b:=98) (joinSmall (lo:=6445) (a:=48) (b:=49) sp6445 sp6493) (joinSmall (lo:=6542) (a:=49) (b:=49) sp6542 sp6591))) (joinSmall (lo:=6640) (a:=195) (b:=196) (joinSmall (lo:=6640) (a:=97) (b:=98) (joinSmall (lo:=6640) (a:=48) (b:=49) sp6640 sp6688) (joinSmall (lo:=6737) (a:=49) (b:=49) sp6737 sp6786)) (joinSmall (lo:=6835) (a:=98) (b:=98) (joinSmall (lo:=6835) (a:=49) (b:=49) sp6835 sp6884) (joinSmall (lo:=6933) (a:=49) (b:=49) sp6933 sp6982)))) (joinSmall (lo:=7031) (a:=390) (b:=391) (joinSmall (lo:=7031) (a:=195) (b:=195) (joinSmall (lo:=7031) (a:=97) (b:=98) (joinSmall (lo:=7031) (a:=48) (b:=49) sp7031 sp7079) (joinSmall (lo:=7128) (a:=49) (b:=49) sp7128 sp7177)) (joinSmall (lo:=7226) (a:=97) (b:=98) (joinSmall (lo:=7226) (a:=48) (b:=49) sp7226 sp7274) (joinSmall (lo:=7323) (a:=49) (b:=49) sp7323 sp7372))) (joinSmall (lo:=7421) (a:=195) (b:=196) (joinSmall (lo:=7421) (a:=97) (b:=98) (joinSmall (lo:=7421) (a:=48) (b:=49) sp7421 sp7469) (joinSmall (lo:=7518) (a:=49) (b:=49) sp7518 sp7567)) (joinSmall (lo:=7616) (a:=98) (b:=98) (joinSmall (lo:=7616) (a:=49) (b:=49) sp7616 sp7665) (joinSmall (lo:=7714) (a:=49) (b:=49) sp7714 sp7763))))) (joinSmall (lo:=7812) (a:=781) (b:=782) (joinSmall (lo:=7812) (a:=390) (b:=391) (joinSmall (lo:=7812) (a:=195) (b:=195) (joinSmall (lo:=7812) (a:=97) (b:=98) (joinSmall (lo:=7812) (a:=48) (b:=49) sp7812 sp7860) (joinSmall (lo:=7909) (a:=49) (b:=49) sp7909 sp7958)) (joinSmall (lo:=8007) (a:=97) (b:=98) (joinSmall (lo:=8007) (a:=48) (b:=49) sp8007 sp8055) (joinSmall (lo:=8104) (a:=49) (b:=49) sp8104 sp8153))) (joinSmall (lo:=8202) (a:=195) (b:=196) (joinSmall (lo:=8202) (a:=97) (b:=98) (joinSmall (lo:=8202) (a:=48) (b:=49) sp8202 sp8250) (joinSmall (lo:=8299) (a:=49) (b:=49) sp8299 sp8348)) (joinSmall (lo:=8397) (a:=98) (b:=98) (joinSmall (lo:=8397) (a:=49) (b:=49) sp8397 sp8446) (joinSmall (lo:=8495) (a:=49) (b:=49) sp8495 sp8544)))) (joinSmall (lo:=8593) (a:=391) (b:=391) (joinSmall (lo:=8593) (a:=195) (b:=196) (joinSmall (lo:=8593) (a:=97) (b:=98) (joinSmall (lo:=8593) (a:=48) (b:=49) sp8593 sp8641) (joinSmall (lo:=8690) (a:=49) (b:=49) sp8690 sp8739)) (joinSmall (lo:=8788) (a:=98) (b:=98) (joinSmall (lo:=8788) (a:=49) (b:=49) sp8788 sp8837) (joinSmall (lo:=8886) (a:=49) (b:=49) sp8886 sp8935))) (joinSmall (lo:=8984) (a:=195) (b:=196) (joinSmall (lo:=8984) (a:=97) (b:=98) (joinSmall (lo:=8984) (a:=48) (b:=49) sp8984 sp9032) (joinSmall (lo:=9081) (a:=49) (b:=49) sp9081 sp9130)) (joinSmall (lo:=9179) (a:=98) (b:=98) (joinSmall (lo:=9179) (a:=49) (b:=49) sp9179 sp9228) (joinSmall (lo:=9277) (a:=49) (b:=49) sp9277 sp9326)))))) (joinSmall (lo:=9375) (a:=1562) (b:=1563) (joinSmall (lo:=9375) (a:=781) (b:=781) (joinSmall (lo:=9375) (a:=390) (b:=391) (joinSmall (lo:=9375) (a:=195) (b:=195) (joinSmall (lo:=9375) (a:=97) (b:=98) (joinSmall (lo:=9375) (a:=48) (b:=49) sp9375 sp9423) (joinSmall (lo:=9472) (a:=49) (b:=49) sp9472 sp9521)) (joinSmall (lo:=9570) (a:=97) (b:=98) (joinSmall (lo:=9570) (a:=48) (b:=49) sp9570 sp9618) (joinSmall (lo:=9667) (a:=49) (b:=49) sp9667 sp9716))) (joinSmall (lo:=9765) (a:=195) (b:=196) (joinSmall (lo:=9765) (a:=97) (b:=98) (joinSmall (lo:=9765) (a:=48) (b:=49) sp9765 sp9813) (joinSmall (lo:=9862) (a:=49) (b:=49) sp9862 sp9911)) (joinSmall (lo:=9960) (a:=98) (b:=98) (joinSmall (lo:=9960) (a:=49) (b:=49) sp9960 sp10009) (joinSmall (lo:=10058) (a:=49) (b:=49) sp10058 sp10107)))) (joinSmall (lo:=10156) (a:=390) (b:=391) (joinSmall (lo:=10156) (a:=195) (b:=195) (joinSmall (lo:=10156) (a:=97) (b:=98) (joinSmall (lo:=10156) (a:=48) (b:=49) sp10156 sp10204) (joinSmall (lo:=10253) (a:=49) (b:=49) sp10253 sp10302)) (joinSmall (lo:=10351) (a:=97) (b:=98) (joinSmall (lo:=10351) (a:=48) (b:=49) sp10351 sp10399) (joinSmall (lo:=10448) (a:=49) (b:=49) sp10448 sp10497))) (joinSmall (lo:=10546) (a:=195) (b:=196) (joinSmall (lo:=10546) (a:=97) (b:=98) (joinSmall (lo:=10546) (a:=48) (b:=49) sp10546 sp10594) (joinSmall (lo:=10643) (a:=49) (b:=49) sp10643 sp10692)) (joinSmall (lo:=10741) (a:=98) (b:=98) (joinSmall (lo:=10741) (a:=49) (b:=49) sp10741 sp10790) (joinSmall (lo:=10839) (a:=49) (b:=49) sp10839 sp10888))))) (joinSmall (lo:=10937) (a:=781) (b:=782) (joinSmall (lo:=10937) (a:=390) (b:=391) (joinSmall (lo:=10937) (a:=195) (b:=195) (joinSmall (lo:=10937) (a:=97) (b:=98) (joinSmall (lo:=10937) (a:=48) (b:=49) sp10937 sp10985) (joinSmall (lo:=11034) (a:=49) (b:=49) sp11034 sp11083)) (joinSmall (lo:=11132) (a:=97) (b:=98) (joinSmall (lo:=11132) (a:=48) (b:=49) sp11132 sp11180) (joinSmall (lo:=11229) (a:=49) (b:=49) sp11229 sp11278))) (joinSmall (lo:=11327) (a:=195) (b:=196) (joinSmall (lo:=11327) (a:=97) (b:=98) (joinSmall (lo:=11327) (a:=48) (b:=49) sp11327 sp11375) (joinSmall (lo:=11424) (a:=49) (b:=49) sp11424 sp11473)) (joinSmall (lo:=11522) (a:=98) (b:=98) (joinSmall (lo:=11522) (a:=49) (b:=49) sp11522 sp11571) (joinSmall (lo:=11620) (a:=49) (b:=49) sp11620 sp11669)))) (joinSmall (lo:=11718) (a:=391) (b:=391) (joinSmall (lo:=11718) (a:=195) (b:=196) (joinSmall (lo:=11718) (a:=97) (b:=98) (joinSmall (lo:=11718) (a:=48) (b:=49) sp11718 sp11766) (joinSmall (lo:=11815) (a:=49) (b:=49) sp11815 sp11864)) (joinSmall (lo:=11913) (a:=98) (b:=98) (joinSmall (lo:=11913) (a:=49) (b:=49) sp11913 sp11962) (joinSmall (lo:=12011) (a:=49) (b:=49) sp12011 sp12060))) (joinSmall (lo:=12109) (a:=195) (b:=196) (joinSmall (lo:=12109) (a:=97) (b:=98) (joinSmall (lo:=12109) (a:=48) (b:=49) sp12109 sp12157) (joinSmall (lo:=12206) (a:=49) (b:=49) sp12206 sp12255)) (joinSmall (lo:=12304) (a:=98) (b:=98) (joinSmall (lo:=12304) (a:=49) (b:=49) sp12304 sp12353) (joinSmall (lo:=12402) (a:=49) (b:=49) sp12402 sp12451)))))))) (joinSmall (lo:=12500) (a:=6250) (b:=6251) (joinSmall (lo:=12500) (a:=3125) (b:=3125) (joinSmall (lo:=12500) (a:=1562) (b:=1563) (joinSmall (lo:=12500) (a:=781) (b:=781) (joinSmall (lo:=12500) (a:=390) (b:=391) (joinSmall (lo:=12500) (a:=195) (b:=195) (joinSmall (lo:=12500) (a:=97) (b:=98) (joinSmall (lo:=12500) (a:=48) (b:=49) sp12500 sp12548) (joinSmall (lo:=12597) (a:=49) (b:=49) sp12597 sp12646)) (joinSmall (lo:=12695) (a:=97) (b:=98) (joinSmall (lo:=12695) (a:=48) (b:=49) sp12695 sp12743) (joinSmall (lo:=12792) (a:=49) (b:=49) sp12792 sp12841))) (joinSmall (lo:=12890) (a:=195) (b:=196) (joinSmall (lo:=12890) (a:=97) (b:=98) (joinSmall (lo:=12890) (a:=48) (b:=49) sp12890 sp12938) (joinSmall (lo:=12987) (a:=49) (b:=49) sp12987 sp13036)) (joinSmall (lo:=13085) (a:=98) (b:=98) (joinSmall (lo:=13085) (a:=49) (b:=49) sp13085 sp13134) (joinSmall (lo:=13183) (a:=49) (b:=49) sp13183 sp13232)))) (joinSmall (lo:=13281) (a:=390) (b:=391) (joinSmall (lo:=13281) (a:=195) (b:=195) (joinSmall (lo:=13281) (a:=97) (b:=98) (joinSmall (lo:=13281) (a:=48) (b:=49) sp13281 sp13329) (joinSmall (lo:=13378) (a:=49) (b:=49) sp13378 sp13427)) (joinSmall (lo:=13476) (a:=97) (b:=98) (joinSmall (lo:=13476) (a:=48) (b:=49) sp13476 sp13524) (joinSmall (lo:=13573) (a:=49) (b:=49) sp13573 sp13622))) (joinSmall (lo:=13671) (a:=195) (b:=196) (joinSmall (lo:=13671) (a:=97) (b:=98) (joinSmall (lo:=13671) (a:=48) (b:=49) sp13671 sp13719) (joinSmall (lo:=13768) (a:=49) (b:=49) sp13768 sp13817)) (joinSmall (lo:=13866) (a:=98) (b:=98) (joinSmall (lo:=13866) (a:=49) (b:=49) sp13866 sp13915) (joinSmall (lo:=13964) (a:=49) (b:=49) sp13964 sp14013))))) (joinSmall (lo:=14062) (a:=781) (b:=782) (joinSmall (lo:=14062) (a:=390) (b:=391) (joinSmall (lo:=14062) (a:=195) (b:=195) (joinSmall (lo:=14062) (a:=97) (b:=98) (joinSmall (lo:=14062) (a:=48) (b:=49) sp14062 sp14110) (joinSmall (lo:=14159) (a:=49) (b:=49) sp14159 sp14208)) (joinSmall (lo:=14257) (a:=97) (b:=98) (joinSmall (lo:=14257) (a:=48) (b:=49) sp14257 sp14305) (joinSmall (lo:=14354) (a:=49) (b:=49) sp14354 sp14403))) (joinSmall (lo:=14452) (a:=195) (b:=196) (joinSmall (lo:=14452) (a:=97) (b:=98) (joinSmall (lo:=14452) (a:=48) (b:=49) sp14452 sp14500) (joinSmall (lo:=14549) (a:=49) (b:=49) sp14549 sp14598)) (joinSmall (lo:=14647) (a:=98) (b:=98) (joinSmall (lo:=14647) (a:=49) (b:=49) sp14647 sp14696) (joinSmall (lo:=14745) (a:=49) (b:=49) sp14745 sp14794)))) (joinSmall (lo:=14843) (a:=391) (b:=391) (joinSmall (lo:=14843) (a:=195) (b:=196) (joinSmall (lo:=14843) (a:=97) (b:=98) (joinSmall (lo:=14843) (a:=48) (b:=49) sp14843 sp14891) (joinSmall (lo:=14940) (a:=49) (b:=49) sp14940 sp14989)) (joinSmall (lo:=15038) (a:=98) (b:=98) (joinSmall (lo:=15038) (a:=49) (b:=49) sp15038 sp15087) (joinSmall (lo:=15136) (a:=49) (b:=49) sp15136 sp15185))) (joinSmall (lo:=15234) (a:=195) (b:=196) (joinSmall (lo:=15234) (a:=97) (b:=98) (joinSmall (lo:=15234) (a:=48) (b:=49) sp15234 sp15282) (joinSmall (lo:=15331) (a:=49) (b:=49) sp15331 sp15380)) (joinSmall (lo:=15429) (a:=98) (b:=98) (joinSmall (lo:=15429) (a:=49) (b:=49) sp15429 sp15478) (joinSmall (lo:=15527) (a:=49) (b:=49) sp15527 sp15576)))))) (joinSmall (lo:=15625) (a:=1562) (b:=1563) (joinSmall (lo:=15625) (a:=781) (b:=781) (joinSmall (lo:=15625) (a:=390) (b:=391) (joinSmall (lo:=15625) (a:=195) (b:=195) (joinSmall (lo:=15625) (a:=97) (b:=98) (joinSmall (lo:=15625) (a:=48) (b:=49) sp15625 sp15673) (joinSmall (lo:=15722) (a:=49) (b:=49) sp15722 sp15771)) (joinSmall (lo:=15820) (a:=97) (b:=98) (joinSmall (lo:=15820) (a:=48) (b:=49) sp15820 sp15868) (joinSmall (lo:=15917) (a:=49) (b:=49) sp15917 sp15966))) (joinSmall (lo:=16015) (a:=195) (b:=196) (joinSmall (lo:=16015) (a:=97) (b:=98) (joinSmall (lo:=16015) (a:=48) (b:=49) sp16015 sp16063) (joinSmall (lo:=16112) (a:=49) (b:=49) sp16112 sp16161)) (joinSmall (lo:=16210) (a:=98) (b:=98) (joinSmall (lo:=16210) (a:=49) (b:=49) sp16210 sp16259) (joinSmall (lo:=16308) (a:=49) (b:=49) sp16308 sp16357)))) (joinSmall (lo:=16406) (a:=390) (b:=391) (joinSmall (lo:=16406) (a:=195) (b:=195) (joinSmall (lo:=16406) (a:=97) (b:=98) (joinSmall (lo:=16406) (a:=48) (b:=49) sp16406 sp16454) (joinSmall (lo:=16503) (a:=49) (b:=49) sp16503 sp16552)) (joinSmall (lo:=16601) (a:=97) (b:=98) (joinSmall (lo:=16601) (a:=48) (b:=49) sp16601 sp16649) (joinSmall (lo:=16698) (a:=49) (b:=49) sp16698 sp16747))) (joinSmall (lo:=16796) (a:=195) (b:=196) (joinSmall (lo:=16796) (a:=97) (b:=98) (joinSmall (lo:=16796) (a:=48) (b:=49) sp16796 sp16844) (joinSmall (lo:=16893) (a:=49) (b:=49) sp16893 sp16942)) (joinSmall (lo:=16991) (a:=98) (b:=98) (joinSmall (lo:=16991) (a:=49) (b:=49) sp16991 sp17040) (joinSmall (lo:=17089) (a:=49) (b:=49) sp17089 sp17138))))) (joinSmall (lo:=17187) (a:=781) (b:=782) (joinSmall (lo:=17187) (a:=390) (b:=391) (joinSmall (lo:=17187) (a:=195) (b:=195) (joinSmall (lo:=17187) (a:=97) (b:=98) (joinSmall (lo:=17187) (a:=48) (b:=49) sp17187 sp17235) (joinSmall (lo:=17284) (a:=49) (b:=49) sp17284 sp17333)) (joinSmall (lo:=17382) (a:=97) (b:=98) (joinSmall (lo:=17382) (a:=48) (b:=49) sp17382 sp17430) (joinSmall (lo:=17479) (a:=49) (b:=49) sp17479 sp17528))) (joinSmall (lo:=17577) (a:=195) (b:=196) (joinSmall (lo:=17577) (a:=97) (b:=98) (joinSmall (lo:=17577) (a:=48) (b:=49) sp17577 sp17625) (joinSmall (lo:=17674) (a:=49) (b:=49) sp17674 sp17723)) (joinSmall (lo:=17772) (a:=98) (b:=98) (joinSmall (lo:=17772) (a:=49) (b:=49) sp17772 sp17821) (joinSmall (lo:=17870) (a:=49) (b:=49) sp17870 sp17919)))) (joinSmall (lo:=17968) (a:=391) (b:=391) (joinSmall (lo:=17968) (a:=195) (b:=196) (joinSmall (lo:=17968) (a:=97) (b:=98) (joinSmall (lo:=17968) (a:=48) (b:=49) sp17968 sp18016) (joinSmall (lo:=18065) (a:=49) (b:=49) sp18065 sp18114)) (joinSmall (lo:=18163) (a:=98) (b:=98) (joinSmall (lo:=18163) (a:=49) (b:=49) sp18163 sp18212) (joinSmall (lo:=18261) (a:=49) (b:=49) sp18261 sp18310))) (joinSmall (lo:=18359) (a:=195) (b:=196) (joinSmall (lo:=18359) (a:=97) (b:=98) (joinSmall (lo:=18359) (a:=48) (b:=49) sp18359 sp18407) (joinSmall (lo:=18456) (a:=49) (b:=49) sp18456 sp18505)) (joinSmall (lo:=18554) (a:=98) (b:=98) (joinSmall (lo:=18554) (a:=49) (b:=49) sp18554 sp18603) (joinSmall (lo:=18652) (a:=49) (b:=49) sp18652 sp18701))))))) (joinSmall (lo:=18750) (a:=3125) (b:=3126) (joinSmall (lo:=18750) (a:=1562) (b:=1563) (joinSmall (lo:=18750) (a:=781) (b:=781) (joinSmall (lo:=18750) (a:=390) (b:=391) (joinSmall (lo:=18750) (a:=195) (b:=195) (joinSmall (lo:=18750) (a:=97) (b:=98) (joinSmall (lo:=18750) (a:=48) (b:=49) sp18750 sp18798) (joinSmall (lo:=18847) (a:=49) (b:=49) sp18847 sp18896)) (joinSmall (lo:=18945) (a:=97) (b:=98) (joinSmall (lo:=18945) (a:=48) (b:=49) sp18945 sp18993) (joinSmall (lo:=19042) (a:=49) (b:=49) sp19042 sp19091))) (joinSmall (lo:=19140) (a:=195) (b:=196) (joinSmall (lo:=19140) (a:=97) (b:=98) (joinSmall (lo:=19140) (a:=48) (b:=49) sp19140 sp19188) (joinSmall (lo:=19237) (a:=49) (b:=49) sp19237 sp19286)) (joinSmall (lo:=19335) (a:=98) (b:=98) (joinSmall (lo:=19335) (a:=49) (b:=49) sp19335 sp19384) (joinSmall (lo:=19433) (a:=49) (b:=49) sp19433 sp19482)))) (joinSmall (lo:=19531) (a:=390) (b:=391) (joinSmall (lo:=19531) (a:=195) (b:=195) (joinSmall (lo:=19531) (a:=97) (b:=98) (joinSmall (lo:=19531) (a:=48) (b:=49) sp19531 sp19579) (joinSmall (lo:=19628) (a:=49) (b:=49) sp19628 sp19677)) (joinSmall (lo:=19726) (a:=97) (b:=98) (joinSmall (lo:=19726) (a:=48) (b:=49) sp19726 sp19774) (joinSmall (lo:=19823) (a:=49) (b:=49) sp19823 sp19872))) (joinSmall (lo:=19921) (a:=195) (b:=196) (joinSmall (lo:=19921) (a:=97) (b:=98) (joinSmall (lo:=19921) (a:=48) (b:=49) sp19921 sp19969) (joinSmall (lo:=20018) (a:=49) (b:=49) sp20018 sp20067)) (joinSmall (lo:=20116) (a:=98) (b:=98) (joinSmall (lo:=20116) (a:=49) (b:=49) sp20116 sp20165) (joinSmall (lo:=20214) (a:=49) (b:=49) sp20214 sp20263))))) (joinSmall (lo:=20312) (a:=781) (b:=782) (joinSmall (lo:=20312) (a:=390) (b:=391) (joinSmall (lo:=20312) (a:=195) (b:=195) (joinSmall (lo:=20312) (a:=97) (b:=98) (joinSmall (lo:=20312) (a:=48) (b:=49) sp20312 sp20360) (joinSmall (lo:=20409) (a:=49) (b:=49) sp20409 sp20458)) (joinSmall (lo:=20507) (a:=97) (b:=98) (joinSmall (lo:=20507) (a:=48) (b:=49) sp20507 sp20555) (joinSmall (lo:=20604) (a:=49) (b:=49) sp20604 sp20653))) (joinSmall (lo:=20702) (a:=195) (b:=196) (joinSmall (lo:=20702) (a:=97) (b:=98) (joinSmall (lo:=20702) (a:=48) (b:=49) sp20702 sp20750) (joinSmall (lo:=20799) (a:=49) (b:=49) sp20799 sp20848)) (joinSmall (lo:=20897) (a:=98) (b:=98) (joinSmall (lo:=20897) (a:=49) (b:=49) sp20897 sp20946) (joinSmall (lo:=20995) (a:=49) (b:=49) sp20995 sp21044)))) (joinSmall (lo:=21093) (a:=391) (b:=391) (joinSmall (lo:=21093) (a:=195) (b:=196) (joinSmall (lo:=21093) (a:=97) (b:=98) (joinSmall (lo:=21093) (a:=48) (b:=49) sp21093 sp21141) (joinSmall (lo:=21190) (a:=49) (b:=49) sp21190 sp21239)) (joinSmall (lo:=21288) (a:=98) (b:=98) (joinSmall (lo:=21288) (a:=49) (b:=49) sp21288 sp21337) (joinSmall (lo:=21386) (a:=49) (b:=49) sp21386 sp21435))) (joinSmall (lo:=21484) (a:=195) (b:=196) (joinSmall (lo:=21484) (a:=97) (b:=98) (joinSmall (lo:=21484) (a:=48) (b:=49) sp21484 sp21532) (joinSmall (lo:=21581) (a:=49) (b:=49) sp21581 sp21630)) (joinSmall (lo:=21679) (a:=98) (b:=98) (joinSmall (lo:=21679) (a:=49) (b:=49) sp21679 sp21728) (joinSmall (lo:=21777) (a:=49) (b:=49) sp21777 sp21826)))))) (joinSmall (lo:=21875) (a:=1563) (b:=1563) (joinSmall (lo:=21875) (a:=781) (b:=782) (joinSmall (lo:=21875) (a:=390) (b:=391) (joinSmall (lo:=21875) (a:=195) (b:=195) (joinSmall (lo:=21875) (a:=97) (b:=98) (joinSmall (lo:=21875) (a:=48) (b:=49) sp21875 sp21923) (joinSmall (lo:=21972) (a:=49) (b:=49) sp21972 sp22021)) (joinSmall (lo:=22070) (a:=97) (b:=98) (joinSmall (lo:=22070) (a:=48) (b:=49) sp22070 sp22118) (joinSmall (lo:=22167) (a:=49) (b:=49) sp22167 sp22216))) (joinSmall (lo:=22265) (a:=195) (b:=196) (joinSmall (lo:=22265) (a:=97) (b:=98) (joinSmall (lo:=22265) (a:=48) (b:=49) sp22265 sp22313) (joinSmall (lo:=22362) (a:=49) (b:=49) sp22362 sp22411)) (joinSmall (lo:=22460) (a:=98) (b:=98) (joinSmall (lo:=22460) (a:=49) (b:=49) sp22460 sp22509) (joinSmall (lo:=22558) (a:=49) (b:=49) sp22558 sp22607)))) (joinSmall (lo:=22656) (a:=391) (b:=391) (joinSmall (lo:=22656) (a:=195) (b:=196) (joinSmall (lo:=22656) (a:=97) (b:=98) (joinSmall (lo:=22656) (a:=48) (b:=49) sp22656 sp22704) (joinSmall (lo:=22753) (a:=49) (b:=49) sp22753 sp22802)) (joinSmall (lo:=22851) (a:=98) (b:=98) (joinSmall (lo:=22851) (a:=49) (b:=49) sp22851 sp22900) (joinSmall (lo:=22949) (a:=49) (b:=49) sp22949 sp22998))) (joinSmall (lo:=23047) (a:=195) (b:=196) (joinSmall (lo:=23047) (a:=97) (b:=98) (joinSmall (lo:=23047) (a:=48) (b:=49) sp23047 sp23095) (joinSmall (lo:=23144) (a:=49) (b:=49) sp23144 sp23193)) (joinSmall (lo:=23242) (a:=98) (b:=98) (joinSmall (lo:=23242) (a:=49) (b:=49) sp23242 sp23291) (joinSmall (lo:=23340) (a:=49) (b:=49) sp23340 sp23389))))) (joinSmall (lo:=23438) (a:=781) (b:=782) (joinSmall (lo:=23438) (a:=390) (b:=391) (joinSmall (lo:=23438) (a:=195) (b:=195) (joinSmall (lo:=23438) (a:=97) (b:=98) (joinSmall (lo:=23438) (a:=48) (b:=49) sp23438 sp23486) (joinSmall (lo:=23535) (a:=49) (b:=49) sp23535 sp23584)) (joinSmall (lo:=23633) (a:=97) (b:=98) (joinSmall (lo:=23633) (a:=48) (b:=49) sp23633 sp23681) (joinSmall (lo:=23730) (a:=49) (b:=49) sp23730 sp23779))) (joinSmall (lo:=23828) (a:=195) (b:=196) (joinSmall (lo:=23828) (a:=97) (b:=98) (joinSmall (lo:=23828) (a:=48) (b:=49) sp23828 sp23876) (joinSmall (lo:=23925) (a:=49) (b:=49) sp23925 sp23974)) (joinSmall (lo:=24023) (a:=98) (b:=98) (joinSmall (lo:=24023) (a:=49) (b:=49) sp24023 sp24072) (joinSmall (lo:=24121) (a:=49) (b:=49) sp24121 sp24170)))) (joinSmall (lo:=24219) (a:=391) (b:=391) (joinSmall (lo:=24219) (a:=195) (b:=196) (joinSmall (lo:=24219) (a:=97) (b:=98) (joinSmall (lo:=24219) (a:=48) (b:=49) sp24219 sp24267) (joinSmall (lo:=24316) (a:=49) (b:=49) sp24316 sp24365)) (joinSmall (lo:=24414) (a:=98) (b:=98) (joinSmall (lo:=24414) (a:=49) (b:=49) sp24414 sp24463) (joinSmall (lo:=24512) (a:=49) (b:=49) sp24512 sp24561))) (joinSmall (lo:=24610) (a:=195) (b:=196) (joinSmall (lo:=24610) (a:=97) (b:=98) (joinSmall (lo:=24610) (a:=48) (b:=49) sp24610 sp24658) (joinSmall (lo:=24707) (a:=49) (b:=49) sp24707 sp24756)) (joinSmall (lo:=24805) (a:=98) (b:=98) (joinSmall (lo:=24805) (a:=49) (b:=49) sp24805 sp24854) (joinSmall (lo:=24903) (a:=49) (b:=49) sp24903 sp24952)))))))))
  have good : (List.range 25001).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 625000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 25000 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 25000 := by
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


private def packet (i : ℕ) : ℕ := (if i < 159 then (if i < 79 then (if i < 39 then (if i < 19 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else (if i < 8 then 0 else 0)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0 else 0) else (if i < 12 then 0 else (if i < 13 then 0 else 0))) else (if i < 16 then (if i < 15 then 0 else 0) else (if i < 17 then 0 else (if i < 18 then 0 else 0))))) else (if i < 29 then (if i < 24 then (if i < 21 then (if i < 20 then 0 else 0) else (if i < 22 then 0 else (if i < 23 then 0 else 0))) else (if i < 26 then (if i < 25 then 0 else 0) else (if i < 27 then 0 else (if i < 28 then 0 else 0)))) else (if i < 34 then (if i < 31 then (if i < 30 then 0 else 0) else (if i < 32 then 0 else (if i < 33 then 0 else 0))) else (if i < 36 then (if i < 35 then 0 else 0) else (if i < 37 then 0 else (if i < 38 then 0 else 0)))))) else (if i < 59 then (if i < 49 then (if i < 44 then (if i < 41 then (if i < 40 then 0 else 0) else (if i < 42 then 0 else (if i < 43 then 0 else 0))) else (if i < 46 then (if i < 45 then 0 else 0) else (if i < 47 then 0 else (if i < 48 then 0 else 0)))) else (if i < 54 then (if i < 51 then (if i < 50 then 0 else 0) else (if i < 52 then 0 else (if i < 53 then 0 else 0))) else (if i < 56 then (if i < 55 then 0 else 0) else (if i < 57 then 0 else (if i < 58 then 0 else 0))))) else (if i < 69 then (if i < 64 then (if i < 61 then (if i < 60 then 0 else 0) else (if i < 62 then 0 else (if i < 63 then 0 else 0))) else (if i < 66 then (if i < 65 then 0 else 0) else (if i < 67 then 0 else (if i < 68 then 0 else 0)))) else (if i < 74 then (if i < 71 then (if i < 70 then 0 else 0) else (if i < 72 then 0 else (if i < 73 then 0 else 0))) else (if i < 76 then (if i < 75 then 0 else 0) else (if i < 77 then 0 else (if i < 78 then 0 else 0))))))) else (if i < 119 then (if i < 99 then (if i < 89 then (if i < 84 then (if i < 81 then (if i < 80 then 0 else 0) else (if i < 82 then 0 else (if i < 83 then 0 else 0))) else (if i < 86 then (if i < 85 then 0 else 0) else (if i < 87 then 0 else (if i < 88 then 0 else 0)))) else (if i < 94 then (if i < 91 then (if i < 90 then 0 else 0) else (if i < 92 then 0 else (if i < 93 then 0 else 0))) else (if i < 96 then (if i < 95 then 0 else 0) else (if i < 97 then 0 else (if i < 98 then 0 else 0))))) else (if i < 109 then (if i < 104 then (if i < 101 then (if i < 100 then 0 else 0) else (if i < 102 then 0 else (if i < 103 then 0 else 0))) else (if i < 106 then (if i < 105 then 0 else 0) else (if i < 107 then 0 else (if i < 108 then 0 else 0)))) else (if i < 114 then (if i < 111 then (if i < 110 then 0 else 0) else (if i < 112 then 0 else (if i < 113 then 0 else 0))) else (if i < 116 then (if i < 115 then 0 else 0) else (if i < 117 then 0 else (if i < 118 then 0 else 0)))))) else (if i < 139 then (if i < 129 then (if i < 124 then (if i < 121 then (if i < 120 then 0 else 0) else (if i < 122 then 0 else (if i < 123 then 0 else 0))) else (if i < 126 then (if i < 125 then 0 else 0) else (if i < 127 then 0 else (if i < 128 then 0 else 0)))) else (if i < 134 then (if i < 131 then (if i < 130 then 0 else 0) else (if i < 132 then 0 else (if i < 133 then 0 else 0))) else (if i < 136 then (if i < 135 then 0 else 0) else (if i < 137 then 0 else (if i < 138 then 0 else 0))))) else (if i < 149 then (if i < 144 then (if i < 141 then (if i < 140 then 0 else 0) else (if i < 142 then 0 else (if i < 143 then 0 else 0))) else (if i < 146 then (if i < 145 then 0 else 0) else (if i < 147 then 0 else (if i < 148 then 0 else 0)))) else (if i < 154 then (if i < 151 then (if i < 150 then 0 else 0) else (if i < 152 then 0 else (if i < 153 then 0 else 0))) else (if i < 156 then (if i < 155 then 0 else 0) else (if i < 157 then 0 else (if i < 158 then 0 else 0)))))))) else (if i < 238 then (if i < 198 then (if i < 178 then (if i < 168 then (if i < 163 then (if i < 161 then (if i < 160 then 0 else 0) else (if i < 162 then 0 else 0)) else (if i < 165 then (if i < 164 then 0 else 0) else (if i < 166 then 0 else (if i < 167 then 0 else 0)))) else (if i < 173 then (if i < 170 then (if i < 169 then 0 else 0) else (if i < 171 then 0 else (if i < 172 then 0 else 0))) else (if i < 175 then (if i < 174 then 0 else 0) else (if i < 176 then 0 else (if i < 177 then 0 else 0))))) else (if i < 188 then (if i < 183 then (if i < 180 then (if i < 179 then 0 else 0) else (if i < 181 then 0 else (if i < 182 then 0 else 0))) else (if i < 185 then (if i < 184 then 0 else 0) else (if i < 186 then 0 else (if i < 187 then 0 else 0)))) else (if i < 193 then (if i < 190 then (if i < 189 then 0 else 0) else (if i < 191 then 0 else (if i < 192 then 0 else 0))) else (if i < 195 then (if i < 194 then 0 else 0) else (if i < 196 then 0 else (if i < 197 then 0 else 0)))))) else (if i < 218 then (if i < 208 then (if i < 203 then (if i < 200 then (if i < 199 then 0 else 0) else (if i < 201 then 0 else (if i < 202 then 0 else 0))) else (if i < 205 then (if i < 204 then 0 else 0) else (if i < 206 then 0 else (if i < 207 then 0 else 0)))) else (if i < 213 then (if i < 210 then (if i < 209 then 0 else 0) else (if i < 211 then 0 else (if i < 212 then 0 else 0))) else (if i < 215 then (if i < 214 then 0 else 0) else (if i < 216 then 0 else (if i < 217 then 0 else 0))))) else (if i < 228 then (if i < 223 then (if i < 220 then (if i < 219 then 0 else 0) else (if i < 221 then 0 else (if i < 222 then 0 else 0))) else (if i < 225 then (if i < 224 then 0 else 0) else (if i < 226 then 0 else (if i < 227 then 0 else 0)))) else (if i < 233 then (if i < 230 then (if i < 229 then 0 else 0) else (if i < 231 then 0 else (if i < 232 then 0 else 0))) else (if i < 235 then (if i < 234 then 0 else 0) else (if i < 236 then 0 else (if i < 237 then 0 else 0))))))) else (if i < 278 then (if i < 258 then (if i < 248 then (if i < 243 then (if i < 240 then (if i < 239 then 0 else 0) else (if i < 241 then 0 else (if i < 242 then 0 else 0))) else (if i < 245 then (if i < 244 then 0 else 0) else (if i < 246 then 0 else (if i < 247 then 0 else 0)))) else (if i < 253 then (if i < 250 then (if i < 249 then 0 else 0) else (if i < 251 then 0 else (if i < 252 then 0 else 0))) else (if i < 255 then (if i < 254 then 0 else 0) else (if i < 256 then 0 else (if i < 257 then 0 else 0))))) else (if i < 268 then (if i < 263 then (if i < 260 then (if i < 259 then 0 else 0) else (if i < 261 then 0 else (if i < 262 then 0 else 0))) else (if i < 265 then (if i < 264 then 0 else 0) else (if i < 266 then 0 else (if i < 267 then 0 else 0)))) else (if i < 273 then (if i < 270 then (if i < 269 then 0 else 0) else (if i < 271 then 0 else (if i < 272 then 0 else 0))) else (if i < 275 then (if i < 274 then 0 else 0) else (if i < 276 then 0 else (if i < 277 then 0 else 0)))))) else (if i < 298 then (if i < 288 then (if i < 283 then (if i < 280 then (if i < 279 then 0 else 0) else (if i < 281 then 0 else (if i < 282 then 0 else 0))) else (if i < 285 then (if i < 284 then 0 else 0) else (if i < 286 then 0 else (if i < 287 then 0 else 0)))) else (if i < 293 then (if i < 290 then (if i < 289 then 0 else 0) else (if i < 291 then 0 else (if i < 292 then 0 else 0))) else (if i < 295 then (if i < 294 then 0 else 0) else (if i < 296 then 0 else (if i < 297 then 0 else 0))))) else (if i < 308 then (if i < 303 then (if i < 300 then (if i < 299 then 0 else 0) else (if i < 301 then 0 else (if i < 302 then 0 else 0))) else (if i < 305 then (if i < 304 then 0 else 0) else (if i < 306 then 0x1df2dea2d014fc9b047820d0ee46b62fa14d88f83a017208983000d600001df28012c514c099447220e0eec6b830c15709343d818909203240c200001df22272c314a898a4652068ecc6a62fe14d08cc3a017208a82e40ae00001df1c052dd95589e84862190f5c6f831815e895c3e218a09083040bc00001df161f2c6948c99246d20c0ed46a82fe15109003cc17f09702fc0bc00001df101d2cd94d09a04692088ef06be2fa14b08c03b416f08802fc0be00001df0a282d015109d448e2140ee46a22ed144088c38216708882d40b800001df04122d415389e84902168f546dc31315789543e618e08e02fc0bc00001defe062d5951c9d648e2120efc6a22ec14688d83b217b08482c40be00001def8332b914709724561fa0e6868c2ea144088c38616a08b82f80be00001def24e2c4946c9704622038e906782e614388c83a217608f02dc0b000001deec672c0948497045d2050ea069c2ed14808e43b017409103380c800001dee6a62b214009644561fd8e886902ec14888e439a17609282fc0c600001dee0bf2c294cc9a447820d0efc6b62f814e89343d019009503100b400001dedaa22dc15349ce47920e0f046be2f615089043b417008a83080dc00001ded4aa2c714cc9a64661ff0e906762ee14608c83b017c09002dc0b400001decec92c114949824682048e986a42f814f89003c017b08a83000c600001dec8e02c514b09a846a2018eb46922f414a08cc3b417108a82e40b800001dec30f2ba943c96c4531f50e346682d413d088c38c17508a82d00b200001debd1a2ca15089c246d20e0f006b22ef14a88bc39816e09102fc0c400001deb7122d215309de48e20f8eec6ba2fb15009303d218709482ec0cc00001deb12c2c714dc9a64772080f006d230615409003ca19509d83480e000001deab472c694d09ae47720e0f146cc30a151891c3ca18009303200ea00001dea5702bc945895a4491f90e546702df14588a439816d08582c80a800001de9f662da95649d448b2190f546e230f15889403e819009082ec0ca00001de99422df15489dc4802148f206da2fc15008ec3ac17b08a02f00b000001de935f2c194749904651ff8e8469e2eb14808bc39816f08682b40b000001de8d6b2d014ec9d848d2138ed06b02f914c08e83b017a08f03000c400001de87812c0947498446b2058e846902eb14508d03c017908c02d00bc00001de818b2ca14fc9ba47f2110f086d42fa14d08f03bc18109002fc0da00001de7bb52bc944897e46b2070ed469e2f314988d03b417508f02e00b400001de75b22d215349d24942108f506dc30014b88ec3b217c08d82e80a600001de6fd02c694a09944672020eb069a2f214c09183d618c09782fc0cc00001de69d82ce94ec9c247b20d0ee46a22f514f092c3b817b08e03000c400001de63e72cc94ec9ae4872168f206d030a15088e439816f08c82dc0b400001de5e042be94b49a047020a0ed06ae2ff15189243d4182094030c0b400001de57f82da15689d84882168f086b02ff15088f03b417e08f02e40b600001de522a2bb14349684592008ea86902df14308b839817908f82f80d600001de4c282d194f89ba47f2090eb86a22ff15309043a617c08c830c0c600001de462f2cf94fc9c64882188f306d830115689043ce18809282f80c600001de40402c794a898e4642040eb86a02fb14a88a438c160082829c0b000001de3a752b4144c9624572020e8c6862e914508e43bc17608983040ba00001de349b2bd94849704622040e9c6882e1146089438816408502f40b000001de2e8e2d394e499c4732080ea869a2e6140087839616a08902ec0ba00001de288b2d1150c9c447d20f8f0c6c630714e88ec3b417f08f02d80b000001de22782d7952c9d047f2160f386c02f614908f43bc18208f82e80b600001de1c882c914f49ae47a2120f146ca30014e89103ce18709383180c600001de16772db95609e04852110eec6b230014e090c3e618709183100cc00001de10602d715309ca4872120eec6d430d15509103cc18c09783680d600001de0a492e095689e048d2188f4c6d030115509083e018d09a83500d200001de04662bd14c499e46f2078e986a02fa14b88f43c017908f03000ba00001ddfe842c494c49a446b2058ebc6ae2f414708c839c16f08782ec0b800001ddf89f2cb94e89be4822110ef46b030114f88f03ac17d08e03200c800001ddf2c92bc942c9624551fa8e386622e214608dc3a217808882d00b200001ddecb52db15549f249921b8f6c6fa31815c09443e419409c83380d000001dde6ba2c994e89ac4782100ef46be2f814f09103c818308e83040c400001dde0b22d91584a0649b2198f386e630b15409083b418509603040be00001dddad32c414a499246d2088eec6d02fd14d88fc3c617c08e02ec0b800001ddd5062b5142494e44c1f68e6c6882e7143889438a17e08f02e00b000001ddcf152ca14d09a447920e0ec86ac2f114608b839417308982e80be00001ddc9252cb94e49b647320d8ebc6902ea14988e43c417d08f83040ca00001ddc3522be948098a45f1fd0e8868e2e214708d43ae17c09283080ce00001ddbd812ba145497a4662020eac6a62fd15189103d218908a82e80b200001ddb77a2d195049e44872170f246d231115189043b418609403180ba000 else (if i < 307 then 0x1e0aa312d8955c9f049821d0f3c6e231215209183d818609603680e000001e0a43a2d095049be48c2150f086ba2fe15289283c417808b82f40c400001e09e4f2c5948c99e4802108ef46a22ee14588d83a416f08602d80a400001e0989d2ac14049404401f20e286602dc13e888c39c16f08c029009000001e092952d194f89b248b21c8f5c6f231615989383f219709703280d600001e08c852db15209d648a2188f5c6ea310155090c3d018d09483240da00001e086a52c094d09c047b20a0ebc6942ef145888039617c08e82f40c200001e080a62d495489ec4872140f086d230715009003d418408b82d40ba00001e07aa12d694f89ae46f2040e906882e814208bc3ac16f08c02e80c600001e074ca2be14949984712038e906862e014608e039617308d83000c600001e06ec72cc14e09b846f20c8efc6be2f714688c839816808602c80b000001e068c62d115449da4852110f0c6c230615409243bc180093030c0be00001e062d32c994dc9a647720f0f0c6b42f614988d03be17709003040ba00001e05ce12c994c09a646c2070ecc6902f314a89083c617c08e82d40b400001e057282b4944095044c1f40e1c6582c913d887438e16d08c02d00b800001e051342d014f49d24832150f506d631315a09503e018409583380b600001e04b1e2db157ca064a821d0f586c630d15909583e618c09683300da00001e0451e2cd94f89ba4842140ee46c02fd14b08e43aa17008702e00b800001e03ef52e615749f249521c8f206cc30215089043cc17e08e83000ac00001e039062c414ac9944632018ed86aa2fe15109203bc185091031c0be00001e0331f2c794ac99c47b20a8ee46b62fc15509443d618e09383040b600001e02d352c3948097e4662030ea46942f114708cc3b818109283080ba00001e027672b9141c9484451f20e506802e313e88c43b817708c02f00cc00001e0216d2cb94e09b44712070eb869e2f014508b838816708182d00b200001e01b792cc14f49b647720a8ee46ca2ff15088d83ba17a08d82d80b200001e015772d1152c9e24902118f1c6c030915409203ce18e09a031c0c200001e00fbe2b3942c95c4531f80e5866e2df13d88943a016b08282c80b400001e009c32cf14bc9884681ff0e7c67a2dd13d089839617208c82f40ca00001e003cb2cd14f89bc48a21e0f6c6fc320161099040e1a109b03380ce00001dffdda2ca14ac99c46e2080ee86b830814c08d83a817708d03000c600001dff7e12ca94ac99847f2128ef46c82fd14c08e43bc18108e83200c600001dff1ed2c915049c648b2158f546da30a15389143be17c08d82d40b600001dfec052c614c49884611ff0eb06982e314808b03aa17408c82d00b600001dfe6232c514b099246d2078ec86a42f414d08ec3b816f08c82e00cc00001dfe04a2c2147498c45b1fb0e686562d813f08a839416c08902c00ac00001dfda442d115149ca4862118efc6bc304150090c3c217d08b82f00c200001dfd44b2cf95109cc4872108f2c6de30115589443ee18b09a03280c000001dfce3f2d495049b84752080ec46b02fc143888438a16308182c00b200001dfc8392d514f89c647b20a8ef46c230014e88e83be18208d82f40c200001dfc24f2c114b899247d2118f106a82eb14408cc38a16c08a82c80b400001dfbc4b2d3152c9bc47820c0f0c6c6301152893440018f098833c0c600001dfb6632bd948c97a4511fe8e8869a2ea13c089839e17b08b02ec0bc00001dfb0442e395bca284b12240fac71a32d16709743fe19a09703380e000001dfaa6e2b7143895e44a1f88e706802df13e889439016108582d80c000001dfa4a52ba143c95e45c1ff8e7466e2d714088843a017e09203280ae00001df9eab2ce94d89c047d2108ef46c82fe15309043c018308f83040be00001df98b02c994909a247220b8ed46a22f114408c439a16c08c82e80b600001df92ac2cf94f89d448c2128f0c6be30515209283ca17f09082fc0e000001df8cea2b9147497a4632000ebc6982ee14708c43a217d08902d00a800001df86df2d7154c9d448020b0f1c6ca30a15389303d218809102ec0c200001df80c12dd95549de49221f0f2c6d230b15988fc3ba18a08c02e00be00001df7af42bc946c98245e2018ea869e2f215009143bc17308a82fc0c400001df75222be948498045e1fe8e9c68e2f714b88cc3a416f08982f40be00001df6f382cb14c89a046f2098ecc6962e914d08f43c618108c02e80bc00001df695e2b8145097c4622050ea068a2ed14588e43a817309003080c200001df636b2c814c49a046e2068ebc6ac2ed14a08cc3ac17f08b82ec0b400001df5d842c714f099c47920a0ebc6b02fe14e88f03a417609102f00b600001df57cb2ad13fc94e4461f68e3464c2c9135885c37c17008c82c40b000001df51bc2db15649ee4882188f3c6c830a15809283f2192097032c0d400001df4bd22c794c89b64792090ee06a62ef14b08b83c618208f02f40c400001df45d22d094f89b647b2180f3c6ce30815309083c818b09303000b800001df3fba2da95509e849621a0f186f231615909443e218b094832c0c800001df39df2bc944096e4581f90e706982f214288cc3ac16f08802b00ac00001df33e82c914cc99e46d2098ecc69e2f514b08f83a217a08d02c80b6000 else 0x1e226702c2949498846a1fe8e346622d613f088c39416008682b40a600001e220b02b213f49364421f90e6867e2e714708f03ae17908c030c0d200001e21a9d2db15549f449e2200f586ee31616409983e819309a03480e000001e214d32b4944497445c2020eb869c2f214a88f03c818809103000c000001e20ede2d615209be4802140f146b230215309343bc17708982d00b200001e208d82d615509f24992228f9470e31415a09283aa18008f030c0bc00001e202e22ca14e49ac4772108f106ce30015088d03b618009103000ce00001e1fcf62c594a49904712068e9069a2e714808d83a617d09183200b600001e1f7022ca14b898a4571ff8ea86902e714308cc39617b08d02ec0c600001e1f1152c4949c9a447120b8ee46b42ff14e89083ce18408e83100c800001e1eb5e2af942895844f1fb0e8c6942e9144088437e16a08a02ec0c000001e1e58f2b6143c95a4592008e7066c2de13d088836a15708102c00bc00001e1df922c794c09784672080ee46a22f514888d03a818309182fc0b800001e1d98e2d0951c9d24842130f106bc2ff14708b439017108b82ec0b800001e1d38d2d014fc9b24892138f186ce303154091c3be18109183040be00001e1cd7f2da9578a084a521e0f486f0315159894c3e818809483040d200001e1c7ba2af94289504591fd8e6c6802d7135886837e15e07f82a80b000001e1c1e92c0149899846d2078ed46b630515409203c618808d82f00bc00001e1bbe42d495509c247c20b0ecc6ae30614e88e43c018108f02dc0b400001e1b6262b014089404411f78e486862de14808dc3b417508e03000c400001e1b03e2c614a89824632038ea069a2ee14588ac3a817409082e00aa00001e1aa7c2b414289604561fb0e806742e013d885439616c08b83040c400001e1a48d2c1948898a4722080e9068a2e0140088438416208002980b800001e19e982cd94d49a64691fe0e706882eb147889439817109203100d800001e198b02c3948899647120a8ecc6b62fa14e89083cc18b09502ec0c000001e192e42b7144096e4591fd0e906802f214d88d43a417308c82fc0bc00001e18ccb2d9154c9e44902198f206e230f159093c3cc18109083180bc00001e186d52cd94e89a84732098ed86b82fd155091c3b618409002d00ac00001e181052b494409704591fe0e686802ce13a085c38616a08482b40aa00001e17b0e2c994d49aa46b2070ed06a42f515009143ba18109583280c000001e1752f2bd94949a447020b0ec86b22fc14d09003ae17a08d82f80c200001e16f4d2bf945c97e4642080ea06982e914788b83a617b08d83200d800001e169702bd14589724622020e706702da13b887839017008682d00b200001e163682ce15189dc4872140f106d230f15a89483be17d08f83040ba00001e15d702d014e49bc47a2080e8c68e2e714788a038816e08b02e80b000001e157772d1950c9d84892188f5c6e030415109183c817f09103240da00001e1518c2c494c099646c1fd0e5c6802e214388b03a217c08a82d80ae00001e14b8a2d094f49d847f20d0ef46ae2fa15308f43ba18109003200ca00001e145972ce94f49a647320b0ecc6b22f714b88c03aa17808a82f40a400001e13f952d395309ce4832118f2c6d831415689643e618f09a03540d400001e139732e315789f44962198f506f630f158092c3c418009183100ba00001e133a12b5946897245a1fe8e906942f614e08f03cc18008a02ec0b800001e12dbc2c314c899e4682060eb46842ed14808d03aa16c08c02cc0b800001e127cb2ca14dc9a647620d8ee46b230415409243d018f09903440d400001e121eb2c694b09a046f2048e7867a2e314808cc3a217309302f80ae00001e11bf52cb95209c648e20f8eec6c22fb15009083ba17e08f83300d000001e115f02cf14f49ca4872168f3c6c62f6151891c3c417908f03140cc00001e10fd32db15489ee4962188f286ca30e15709203de18c09782fc0cc00001e109e12c614849884662060ef06be30215409183b217f08d02e00bc00001e103f82c594c49a647120a8f006b2300152092c3c417c08f02e00c600001e0fdf92d495149d047f2120f1c6c2302154894c3e019109583440be00001e0f7f12d095389e64942188f386cc30b15089083ce18409683200cc00001e0f1e42d615209ce4872150f206e030815189243d418c090831c0d000001e0ebd32e015509c247d2098ee46a42f814e88f83b817e09203140b000001e0e5f42c314a89a447b20c0ecc6a42f615089103b817c08f83200c400001e0e0192be148c9884632050eb06aa2ff14888dc3aa18109082e80b600001e0da242c894e09ac47c20d0f246c22f914d08f43b018709183180b800001e0d4222cc94e89b847e20c0ec069a2ea143089839216c08682e40c600001e0ce012e295709e649c2228f9070a31c15a89783ea18b09903440d000001e0c82d2b9948098845b2040ec46a22f114788a039816f08a02c40ba00001e0c2252d515209be4852140ef06b82f7153890c3d218008f831c0c200001e0bc092d595309d84872108f306d630f159891c3d018309083140b200001e0b62e2bf946c99646b2088ee86ba30815289343e218208b82c80a400001e0b03f2cd94e09ba4832190f086ba30114f09043b417708a82d80b4000)))) else (if i < 313 then (if i < 310 then (if i < 309 then 0x1e3a1e92b8141495c44e1f98e5c67c2d413c886039e17308e831c0bc00001e39bfa2c914cc9a247b2088ef86ba30114e89143ca18809182e00bc00001e396102c614ac9b44762120f146c030615609083b617408902bc0b600001e390202c894f49b647320c8ee06d030414808c839818009283140d400001e38a2c2c914b899246c2080ef06be2fc14d08f03be17909003200d800001e3843d2c7949c98a4681ff8e7c6a630214f88d83aa17408702b80b200001e37e562c214909ac47e20e0f106ba2fb14a88ac3b217a08982c80ae00001e378382dd95449d848b2160f2c6e830c15309003ae18309102f40b600001e372652bb94b09824622068ed46a82f814d89003bc17c08d02e00c600001e36c962bb944c9584551fa8e8468a2e6143888839a17808902e80be00001e3669d2cc94e09aa4722088ee46c430015509183c017909102e00bc00001e360762e195aca2c4a92200f6c70631915f096c3d818609303200c600001e35ab02bb147497e4552000e7c6842ed14408a038616a08702c80b200001e354b02ce15089cc47f20e8f106d030e15889283d818609583100bc00001e34eed2b4141c95444b1f68e0864c2cf138886837215708402d80b800001e348d82dc957c9f64992130edc6b82fd14e890c3ba17c08882e80b600001e342ea2cb14e49c04892160f106c230315389083c618409082f40c600001e33d062c594a89ac47c20e8ed469e2f714a08ec3be18308e03140b600001e337342b4944096845d2030ea46862e814608e43b618008f02e40ba00001e331612bb148497c45d2060ec069c2df14588d03ba18109383380de00001e32b4e2d595409e848c2198f586e030a156091c3c218e09683180ce00001e325612c814809724601fc8e4c66e2df141088439417308f02ec0c400001e31f742c694a89824652038eec6ac2f014909083cc18209683200c600001e319962ba146896e4551fc0e8068a2f014c08e83c817f08f83040c000001e313a42c794cc99c4832120f086c430a15189143ba185090832c0d000001e30da02d6150c9ba4832140f306da31d15b89443ce18209203100b800001e307b62c1148897c46a2098ecc6ba30015189443e419409803240b800001e301af2d295089bc4832108f046c42ff15289103c418209282f80b600001e2fbcf2c1148097645a2038eac6862f514c88fc3c217708f02dc0b000001e2f5d02d495049b847520c8f086e230c15709343d618f09202ec0c400001e2efd92d0151c9d448f2188f3c6d22ff15009003bc17e08e02f80c600001e2e9ce2d4152c9a44752060ea469a2ef14808cc3ae17b08f03000d600001e2e3e22c714ac98a4632028e746782e214308a038c16a08883200bc00001e2dde12cc94c09aa47e20a8ee06b62f014f89083b618409403580cc00001e2d7fd2c0149c99e47120a8ee86ba2fd14d88e43c817b09083140bc00001e2d2112cf14d09c047f2110f1c6cc2fd152891c3c817108c02a80a200001e2cbfd2db15509da4982200f246da30d15089103dc18c09683000b000001e2c6042cd14f89d648d2130f286e0312154892c3f219309883200c200001e2c0372c214cc99e47020f0ef869a2fe14b08bc3b017608b02e80be00001e2ba622bf946897c4602038eb46982ee14988f03b018208c82ec0bc00001e2b4b72ac13d492c4361ef0dd062c2c012f081837416708402b40b200001e2aebe2cf951c9cc4852198f686f431e15909403e618b098033c0d200001e2a8ce2cb94f89b047a20a8ee46c230414e08f83d418409103140d200001e2a2e42c814c49b24752060eb86b42fc15009043b218108e830c0ca00001e29cde2d295249d648620e8ef86bc30a15509103dc18a08c02e80b800001e296c22de9570a0e4a12218f986fc31a15f899040c19009403080c600001e290d92cb95009ce4832110ef06b62ef14708f83aa17808c82ec0b000001e28adc2c394e89ca47d20f0f2c6d830615809403d418709183300d000001e284cc2d315389de49a2208f7c6f432515a89283f219109a832c0d200001e27f0d2af93e89384421f30e2464c2c613b88a43a216e08a02c00c600001e2790b2d294f49b04782078ea46822ef14708b83a017008c02e40c000001e273292c1147898245e2028e9068c2e614488b83a0178090030c0be00001e26d1c2d415149d84872118f206c830115389283b217808f03040be00001e2672d2c714809864602028e946822df14588e839017209102f00b000001e261452c814ac9a247320a0e8467c2df14388b039416f08a02d00c000001e25b702be94789804541f38e346702d5143888837a16708b03140b400001e255902bf14789884662018e8c6922ef14a88fc3b017809002e80ac00001e24fc02b9944895e4602060eb06a22ee14888c83bc18b09783080ca00001e24a042ad942094c44f1fa0e246622e314088a03ac18009503100c000001e243ea2db15689fc49d2200f946f4324163097c40019809a83300c600001e23e202b0140496c4531fc8e7868a2e4140087837c168086829c0a000001e238272cc14d899a4722058ed86ae2f214788c839417408b030c0cc00001e232462bb145896645b1fc0e8467e2e014588c43b417108d02a40b000001e22c4b2d5155c9da49221c0f5c6d831015489003b818109403400d2000 else 0x1e51d492bc14349684521fd0e906822e5142889839616a08883080c800001e517392da9578a104a921f8f7070032616109a441a19909d83580de00001e5113e2ce14d89b648220e8ecc6b22f614d08ec3c618308f030c0c000001e50b492d094fc9bc4872130f086be2fc14909043c418709083140b600001e505552d014fc9a847a20c0ec069a2fd15089143bc17f09303240c400001e4ff8a2ba944097a45f2038eb86802d813f88a438616a08402c80b600001e4f9932ca14d49b247b2110f206d030215289383d4184092830c0b800001e4f3af2bf14609a84711ff8ea468c2df14488a838e16d08782b80a800001e4edc02c214909924722078eb469e2e814908b43b618009082f00c400001e4e7d32c494a898446b2060eac67e2e014608cc3b217208602c40b000001e4e1cd2cf151c9d047f2110ef46d231415b89483c618008882fc0a600001e4dbf62b7144c9584622040e7c67e2eb14608c03c618809003100ba00001e4d6272b614649764511fa8e886a62f814808dc39e17008602dc0a200001e4d0382c5145496645e1ff8ea06a42f214a08cc3b417608d830c0bc00001e4ca632be94509704612008e986982ee14988b038e16608582bc0b000001e4c4662cf15149c24882150f386dc311159092c3da18309283440da00001e4be892c094a09884642060edc6ac30515009003c417b09483400c800001e4b8b72bd14609604581fc8e806882e213c886438215b084029c0ac00001e4b2a92d9154c9c247920b8ee86c230615589203dc192095031c0ca00001e4ace82b214209364341ea0db06462ca137086839617608e03000ca00001e4a6ed2d2150c9be4812128f1c6de30e15609303e818c09003000c800001e4a0fe2c814c89944772120f186d230414d09103d619009102ec0bc00001e49b2f2b4141493e43b1f00e546782e514a88cc3b817908e82d80b200001e4954b2c614a89924631ff8e646942eb144089439616508882c409a00001e48f3c2d715289cc4862160f506e831915989583ce18708b02e80c200001e489532c994f09ca48a2168f446dc30c15689383dc18e09403040b400001e4835e2cb94bc98846b2018e946882ee14e89003ba17808d82c00a400001e47d8e2bd949499846c20a0ed06a02ed14908a838c16808902ec0c000001e477ba2b814589704521fc8e5c6842ec14308a838a16508402a809800001e471c82cc15049c048420d8ef069c2f514888d03b017a08e02fc0be00001e46bdb2cf95149b447e2088ed86be2f614988b03a617a08d82ec0ac00001e465f72c114a098245f2058ea86aa30215008f43d018608b82dc0ae00001e460262c2945c97a4561f88e6c66e2d613d087c38216208482e00c600001e45a2d2ce94f49ac47620c0ee06d430515288d83b617d08c02ec0bc00001e454362cd950c9c647d20f8ef86b82fc150892c3d019209902f40a800001e44e342ce14e89ba4772110f0c6ca2fc14c08e03c018009102e00ba00001e4483b2d215009c44882130f086cc2ff14e08fc3cc18509083080c400001e442422ca950c9b847e20d0ef06a82f914808a439617108782d80bc00001e43c712ba948c97a4611fe8e946742e413d887838e17408e83040bc00001e4366f2ca94d49aa47720b0efc6bc2fc15309243cc18909483140bc00001e430832c314e09b448820d8ef86cc2fa15289183d618509182ec0aa00001e42a702d895289d64812110edc6a02f214988dc39617908a82dc0bc00001e424ab2ba14749644551fc0e5466e2d6143889c39016b08a02e00ac00001e41eb32c814d09a248020f8f186e430c15209243aa17108902f80c600001e418b42d315349dc49721c8f5c6e231615709543d818708d82e40c200001e412d52b7143895e4431f38e0464c2d213c089c3a617b08f03200d800001e40cd02cb94f89c447d20d0ef46bc2fb15288e43b618a08a82cc0a800001e406bf2d715009b648920e0ef46ba2fe153093c3d618809182f80c000001e400ec2b514389604441f50e286542c3132083436a16008302bc0a000001e3fadc2d395109c847f2138ef86bc30914e08f03b617e08e02e40b200001e3f4f12c494c89a246c2060eb86982f014a88e03b017708c03040ca00001e3eec82dd95889f249c21b0f6c6e831816589a04141a209783380d200001e3e8da2c814d49b04852108efc6c42fb15208f43be18509382e40ca00001e3e3162bc148c99c4672078ec868c2f214b08f03bc17e09783400c200001e3dd4c2bb147897e4622040ed06a62fc14e09103d218908e83280ce00001e3d7462d495249d648a2150eec6c22f614a88b839a17308f031c0d200001e3d1492c694b89a04732068ea867c2e514288a43a617008d031c0cc00001e3cb702bd148c9ac47c20b0eb06a02f2145088438616308382c00b000001e3c57d2c794dc9be4772080ea86942f1143889439017408c02ec0cc00001e3bf812cc14dc9aa4732090ee86b42fd15208f83d017b08d82e40b000001e3b9a22c4146497645a1ff0e606782ed14508ac3b217708e82f80dc00001e3b3952d8153c9d048120d0ec86ba2f714a88c43b617908a02e80b200001e3adba2bc94649944662020e8868c2eb14b88e43b417708d82fc0b400001e3a7b82d4951c9ba47f2160f386e42ff14f88dc3c418009283000ce000) else (if i < 311 then 0x1e698802d895349e24832130f1c6d0303157895c3ee197097033c0dc00001e692942be94609844571f98e786822e614388a43ac16a08a82f40c800001e68c9c2ca14e099645e2060ed46b030014f88ec39417108a02d40b000001e686bd2c294909944672008e886962e714608ac39e16d08a02f00c400001e680c72cf95249cc4922148f046be30115488fc3d217e08f02dc0ca00001e67af02bb14789724641ff0e7068e2e814508b43b017f09283240b600001e6750b2c294a09a847320b8e806982f014908d039a17208b030c0bc00001e66f512ad13f094844d1f98e606822e813d086438e16708982ec0d000001e669892b9145095c4501f68e806922f114908a839a16f08d82e40b800001e6639e2c7149c9a247720b8edc6ac2fc14b890c3b217c08602bc0b400001e65d9d2ce150c9c248020e0edc69c2f114f88e43aa17d090832c0d600001e657952d195249da48420d8efc6c62ff15309083ac17708e82f40be00001e651b22c594f49b047220a8ed06a630715209203d818f094030c0c600001e64bb72cc14ec9c448820f8f006b02f814488b43a017408882dc0c000001e645ea2b814589644652008e7467e2e414808e43a017108b02f00c600001e640152ba145897245b2028eb867e2df14388ac38616108402c40a600001e63a2c2cb94c49aa47920d8ef86b22f414a09003c017e08a02d40b600001e634052e415809f24912158f146ce2ff15189103ca18809102cc09800001e62e1e2c614cc99e4692098ed46aa30915389443d218609403100c600001e6285c2b414249584501f98e586722e614388a439e16c08902e00b400001e6227d2c314a89a84782068eac68e2ec14708c83b217508a82d00a800001e61c812c814b899a46920c0ee86b2304151090c3cc18409083100c600001e616942c1147895e4461f80e006442c6139883c36015e08302940a200001e610b22bd94789984612040e9c68a2eb14508c039c16708982d80c200001e60adf2be14889924722090ebc6922e814708cc3a217808d82b80c000001e604eb2cc94f89a246920a8ef06b02f414d88cc3c417308802e00c800001e5ff262b6942894e4451f48e406642d713f88ac38c16808902ec0b800001e5f9342c5148499246e2098ee46ba2f9152891c3c417e08d02f80d800001e5f3402d215009a846b2068ea06962e814588b03a416e08a82ec0be00001e5ed492cc15009b247b2108f346d230a15409103ca18609083040be00001e5e7552ca94e89a64802118f1c6e2311155891c3c6182092031c0bc00001e5e15f2cf14e89bc47b2120f146ca30215209243d618c09282e40ae00001e5db5f2d895289c448b2140f2c6d830b15789243de18608f83040dc00001e5d56e2ce94dc9a846c2090ee06c230b15609603ea19609683180d800001e5cf682d414e49c048d21a0f446ec31615f89483b817d09102d40c200001e5c96f2cc94ec9c447a2090eb46942f915009183c418909683180ca00001e5c3772cf95149ce47e2090ec06a62f514e08f83bc17108882f00b600001e5bd782cb14e89c648220b0eb06b22f414a08cc3b017d08b82d80c000001e5b7832c8951c9c248820b8ee86b4305152092c3c6190096831c0be00001e5b1852ce14d49b64862080eb86a02eb14508a039016d09003080c400001e5ab882d094ec99e4722118ee46b62fe14f08c43a817b08a83080bc00001e5a5aa2c194889804671fd8ebc6922ee14488b43a216f08582dc0be00001e59fbc2c714d899a47620a0ed469a2ef14508e03c218b09203180c400001e59a032a913e092e4421f80e2867a2e614288a039217408902f00be00001e593f42da15589e448c2148f046ca2fa15209183c4184097834c0c000001e58df12d415309d448921b0f486d830e15d893c3e218c08d83180ca00001e588122be14a49884632040eac69a2e814388a439417208c83100d400001e582182c814a09a24762120ec46ba30514c88dc39e17208b02dc0b600001e57c432b8946496a45a2040ebc6982f314788b43bc18509002f40be00001e5764e2cb94ec9d048820f0ee06c42f914d08b83a017208b82f40c200001e570592cf95109d447f20d8ef46ae2fd15309383fa19809a03200c000001e56a6f2c214a099c4662070ed069c2ef14588b83b417d09182f80c600001e5645d2dd152c9c047520d0eec6c830215009083b217808a82b809a00001e55e8a2bb147097c4562028e8c6ae2fa15189043be17e08d02f80cc00001e558ad2bc14809824622018ea86a62ef14888ac39c16908402a80ac00001e552732e915c09fe4a221e8f486ce30615809303c617e08e02d80b800001e54c882c514ac9a24692050ec469c2f614908b03a017708682d40b400001e546be2ba144495a4602030ea46a62e914188a038816808982ec0d600001e540c62ce95049d248e2150f286b22f314808f43c218009002fc0c600001e53afc2b5944095e4531fe8e7c6902e314708bc3aa17f09102fc0c400001e535142c394a89984622038ebc6ac2f314c08f03a418608d830c0b800001e52f132ca94c89b44872140f106d630f15709303b818208e82f40a800001e529182d315109cc47d20c8e9469a2f414b08dc39216808282b00aa00001e523262c594bc9ae4822128f2c6f231515509103ac17a08c82ec0c2000 else (if i < 312 then 0x1e8152c2c2949099a47520d0ef86c62fa14d08c83ba17708d82fc0c000001e80f402c4148899247620a0ee06a2301155893c3d818809583240da00001e8095a2c3147897c4692018e786822e4141886c37a16708602f80c000001e8035b2d114f89c447920c0ebc6aa2f814b08d038e16c08d83000c000001e7fd972b693f894a44e1fd0ec06b830214988ac3b817909182f00c200001e7f7852db155c9e849321a8f3c6d631215789243da18809482fc0d200001e7f1752d615609dc48720f8f046ca2ff15209183c418e09583040c400001e7eb862ca14e49b847b2078ed46a82f615288ec3b617d08f02fc0a800001e7e5a32c314b09884662050ec86ac2f714f89043b217308c03000b400001e7df9d2cf95049ca48a2150f186da30b154092c3d018609283100c600001e7d9862d895149d04832128f0c6d431315489083ce181092031c0c600001e7d3922cb94d09a646e2018eb46aa2f714a88ec3bc17008982e00c000001e7cda02ce14f89b047b2120efc6c8315158094c3ce18609703380d200001e7c7e02b214149564521fa8e306542d814288983a217308682d80a600001e7c1ba2e015449d248c2160f2c6ce2fd15489303de182090030c0bc00001e7bbac2d915289ce4842138f086c430a15409483d818709382e00c200001e7b5ae2d215189c447420f0ec86a42fa15208fc3cc186092830c0d000001e7afa62d9154c9f64a221f0f586e230314e88f43be18108a82d40b200001e7a9b62c714c498e4692050eac6a22ec14908f03c218e09783680e800001e7a3cc2c994cc99e46e2080eec6b02fa14888ec3aa17808f83000c400001e79dbd2d415149c047f20e0ef86b22f314b08b03ae17008c83000be00001e797f92b3146c97a4612050eb46a42f914d891c3c418309603180d600001e792392b2143895a44f1fc8e4c66e2ed14a88d43b618109203180c800001e78c5c2bf14b899647420c0eec6962ea14888ac3aa17308602c40be00001e7864d2d695449e649021e0f606e430b15a89303d619309703300cc00001e7806c2bc946c9ae47d2138f146ae2ea14a88c83a4180092831c0cc00001e77a992b8145496e4682048e9466e2e014688d83c0183097030c0b600001e774b32c494cc9b44722098ec06862f214708f03cc18309382f80d000001e76ec52cd14e89b047b2128f0c6c82f414a08e03aa17c08d02b809a00001e768c32d194f89c448420b8f046b02fa14f89303c217908f02e80d000001e762c72d395249be4752110ef46b62fe153891c3c617c08902b40aa00001e75cca2c994d89a046b2050e9869a2f314b889c39616608102dc0b200001e756cd2d115109c848020d0ee46b02ef14908dc3b817e08e82fc0d000001e750e72c414b89ac47520e0ed86bc2f814b88e83ae17a08d02ec0a800001e74af32d095049ca47820d0efc6d030215489303e618909683280ce00001e744e92d115009c047e2118ef06b430615689603f019209303240da00001e73ece2da95509e048b2198f306d030715089283c818909182d80bc00001e738d82ce95009c44842118f1c6d830815409043c217408602e00b800001e732d22d895189c047c2080ed86982f014888b438616808a02e40be00001e72cd52cd952c9e048c2130f1c6ce30a15709083c418808f830c0c600001e726cd2d115349d04792098ed06ba30b154891c3d018709103140c200001e720c42d815309e248b2158f106e8315159892c3ee19609a83340ce00001e71aed2b6943c9664561f90e646742d714308ac39817b09002fc0d200001e714f82d114d49c048320c0eec6ae2f514c88ec3c017909182f00bc00001e70f252be148897e4662030ea06982f214788e03be17908c02c80b800001e7093f2c714bc9b247f20c0efc6b42f014808c438a17208982e40b800001e7033d2d015189c248d20d0ee46c030715609303ec19309782ec0a800001e6fd5b2c1149c97845c1f90e446782e8144888438217608d82dc0b800001e6f7852b9945898446b2068eb86b830415409403d218b09402fc0d000001e6f16e2db157c9fa49f21d0f4c6fa31315589403e6189095030c0be00001e6eb882c914d49924722070eb468c2e4141889c39e17008802e00c200001e6e5a52c594b09a446b2020edc6a42ea14908c43b017e08a82e00b000001e6dfd02ba94589784511f90e5c66a2d113b887439617408c82e40bc00001e6d9bc2d995209d448f2148f1c6bc30015088e83b817d08f03140e200001e6d3fb2b394049564441f48e6066e2ee14908c439e15c08302a40a600001e6ce112c194909944612030ec86b02f914608b83a017608983000b600001e6c8212c594989804612000ea069a2ee14908c43ac16b08c82e00be00001e6c2472bc146c98e4662068ec46c62fe14c89003b017608902d80ba00001e6bc762c094b497e4581fe8e8c6802df143886839016108982c80b800001e6b67d2cf94f89ae4732070e946962e714908c03b617609103040c600001e6b0922be149c99c46a2060e946a22f914f88f03b016f08e02f00ba00001e6aa6c2e31594a0249e21f8f506e430e15689403ea18a09283000b800001e6a4822c214849884602038ebc69a2e614688ac3b617d09202e40bc00001e69e912c9949c97e4692098ee06c62fc14e88f43c418508f03100ce000 else 0x1e9907e2b7942095a4451f28e2866c2db139886839016f08702d00ac00001e98a8c2c694e099a4732088eac6862dd13f084c37815808302c809800001e984a02c514949744602020e906802e814708a03a417608b82e40b600001e97ede2b5141095a44c1f28e0064c2d0138882c37015d08282ac0b600001e9790d2ba946897c4611fb0e3c6742e214408a438a16c08d82cc0b400001e973222c2949c99a47a2080eb86a630215289303d818a08d82fc0b000001e96d1d2d4151c9e449321b0f286ca30c15689303de19209a83540d000001e967352c494bc9a24762080ef46c02fd14e08f43b618509383340c200001e9612f2ce15289d84862130f306ce31115489583d218008a82d40b200001e95b1f2d315249d84922120ef46a02f814a88f43b217808c82f00b400001e955252d295349ca48d2158f286ca30615289203d218808f02ec0b000001e94f3f2c494d49ac4742090ed86b42f614a88fc3ae16d08c02f00be00001e9493e2cc94cc9ae47920e0ecc6b82ff14d88d43ce18909002f40bc00001e9436b2b9143c9744531f80e806922eb144888838a16a08882c409e00001e93d492e0154c9da4922180f2c6c02f515089183ae16d08802e80b800001e9376d2bc94a09884642018ea86942f614a88d43be17e08f02ec0ce00001e9318a2c0149098c4652030e906742d713d089c3a017108b82d00bc00001e92b6b2e4958ca104ad2220f906fc32715e89683f018d09403200c000001e925762c894ac9844612058ea86b02fd14d88e03c018709083080ba00001e91f7a2cf14d89b847a2140f446dc30915089203ba18109002fc0b800001e9193d2ec1604a364be22c0fdc71e32916489803da18d09183180c800001e913392ce94ec9bc48220f8f246c62fe15109183bc18409103080b200001e90d602c314989a447f2110f186de30d15388f83ca18709783140c000001e9075e2cb14d89aa4872150f0c6c631015989303ca191094032c0ce00001e9017f2c5149898a46e20b8eec6b630515109243dc18f097034c0da00001e8fb8b2cc94f49c648c2150f0c6e430b15689083c6184091031c0d800001e8f5ae2c114a09964742090ed46b430415289303d218d09583280ca00001e8eff22b414289624561fc0e7068a2db13d087838e16f08482d80ac00001e8ea0e2c0148c97a4622078e986802e0142088438a16f08782f00be00001e8e41d2ca94cc99a47a2130f246ce2f814c08d83a817908f82fc0be00001e8de262cb94f89a646f2090ec46a42f114988d43ac17509083000b200001e8d8542bd146497246d2070ec469c2ed14308b839417108a02e80b000001e8d2772b994489664581fd0e9869c2f314b88e03aa17508b82dc0d000001e8cca22b8946496e4561f68e4466c2dd14108a039817208d02ec0bc00001e8c6ad2cc14fc9c44832168ee069a2ed150090c3ce18409182e00c000001e8c0af2cd14c09ac47b2108ee46b02f914d08ec3b817f08902ec0c400001e8bac52c794dc9ac4742080e946902f414d08c43b618408f03080b800001e8b4c92ca14e89c448c2140f086c830614f09103ba17808d82e80be00001e8aee42ca15289dc48020e0ed46982ee14e08d83b417f09203000c600001e8a8f92c2948498c47420a8ec86942f414808c03a217208a03000b800001e8a2ee2d294f89ac47320d8edc6a02ed14b08f03c818709503080cc00001e89d0a2ca14f49aa47420c8eac6a22f614a08d03c818709182fc0b800001e897172c594cc9a847420b0ebc6842ea14588d83b418209083100d600001e891462b7147097645d2008e9069c2e014688e43c218608f02fc0bc00001e88b4a2d194e499c47a2108f086ce311157890c3d219009d033c0d200001e8855e2c294b89aa47920b0ea868c2e814908e43b417908e82f40c600001e87f8c2b914309644571f90e846982e913d088839216608982d40b800001e879c52b6940494c4491f58e346642de14388c03aa17b08e02c80c200001e873f22b8944c97844f1f80e406582d213d886839017308a02e00c400001e86dc32e895949f049221c8f546f631f16389583ec19809503240c400001e867d82c414a09b24892150f506e231315789383e218108b82fc0c800001e8620b2b9942495a45a1fe0e9068a2ef14788ac3a817708c02f00bc00001e85c1d2c494ac98846c2048eac6962ef14988e83aa17508e02cc0b200001e856302c6147c9764642048ec06b22f614a08f83b217c08e02ec0c400001e850432c5149c98045e2008e6467a2ee14508c039c16d08d83100d000001e84a352d7152c9cc4892128f146ae2fd15289203c217408e02f40bc00001e844282d8952c9ce4852110f386d831015509203d618308d82d809c00001e83e6f2ac14009364471ef8e3468e2e613e088839417c09102e00ba00001e838c12ac94189684571f90e5066c2ea14908d83b418109403000d000001e832b42d795489ec4a321d0f7470a32716c09943ec18b09082f80c600001e82ce52b2942495444f1fe8e986862e414888d43b818408f83100ca00001e826f52cb14d49b047d2110f106c030215509103d018e09503280ba00001e821232bc147896045a1fe8e946822dd140888039216a08702c00ae00001e81b142d294f49984682070e9c6842e714708c83a017408b82cc0ac000))) else (if i < 315 then (if i < 314 then 0x1eb0b1c2cc94f49bc4872130f406dc31b15809243ce18209103440c400001eb052b2cc94d89ac4742070ec06a62ee14c89043ae18b09202f40ba00001eaff3d2c514b899a46e20c0f006b82f614988e43b417608702d00be00001eaf9612bf147c97645a2080edc6a22f114e08f039617f08e82d80b600001eaf3682cc94e89a04682020e7c6802e113d087c39616d08783040c600001eaed842bc94749604571f60e886982f314a08c439e17108802b00b400001eae7982c2149c99c4692050ec468e2ea14988dc3a817808c02f40b400001eae1ca2bd945898245a1ff8e646562d413b08a439016a08b82f40be00001eadbfa2ba14149664511fa0e706762de13c887c37416608b02e80a200001ead6252be147897c45d2028e8868c2f214a08d83b017a09003000bc00001ead03b2c914dc9b44862140f246d430f15009203b618309883280b800001eaca3f2d115189be47f20d8efc6b02f914b88fc3d418c08f02fc0c400001eac4542c814c09944672068ef46c4304152090c3c818608e82ec0aa00001eabe992b094009364501f90e7467c2d313b086038c16608702b80b200001eab8a92c694bc9a24732068ed06ac2f114d08e03b017508f03080bc00001eab2a72d2950c9a447520d0ed86a42f514f88e43a6173089830c0b600001eaacd62be14549824622028e986942ea14988c43c017b08b02ec0b800001eaa6df2cf15009b848020e0ef46d830515409043d218809602f40d000001eaa0ed2c514bc97a4531fe0e8468c2e614088ac39816d089029c09e00001ea9b072c014b098845f2040eb46aa2f314a08c43a817708e02f00c200001ea954e2af94149524592040eb86a22f114888e83c8182094030c0d400001ea8f632c814c499647920c0ec86b02f614c09303e018109803680d600001ea897f2c0147c96a4602028e9c6862e3144888839c17909102fc0be00001ea83832cf151c9d44942158f586e230f15289003c218209002dc0b400001ea7d612dd15509de4992208f246de31815809203dc18e09403140c200001ea77852be947c97a45d2008e746962f414508b03a817908a02e80c800001ea71862d1150c9d047c20e8ef86d030a15188fc3ac17308a82f40b000001ea6b9b2c814e09b648120e0f186c8304151890c3e619109203200c000001ea65aa2ca14d49ac46f20f0ef06b42fd15489303d018509303300c400001ea5fb92ca14d89be47a2120ef46c431015809403e819109403380ce00001ea59af2d6954c9c24832140f406e030d15a094c3c817c08a82e40ae00001ea53c02cb14c498c4732050ed86ac2f714a08e83d018509603200c600001ea4e062ad93f893c4441ee8e306702d613f0890398167083829c09600001ea48102c714dc9ba47120f8ee86a62ec14508c83b017708c82e00a600001ea42252cb14e09c047f2118ee86c22fa15108fc3cc17e08f82fc0c200001ea3c232d7954c9ec4882138f0c6ce2fe14a88e03a416a08382a00a200001ea36182db953c9de4952158f406de30c15389383ec18c09103140d600001ea30422ba144095044c1fa0e3867c2e614008b039617508782d80ac00001ea2a262dd15509e64882170f1c6dc30815889383f019609383200c800001ea244b2c714bc99646f20a8ef46cc30d15489103e6195098031c0c400001ea1e972aa93f495a4511fa8e8c6982f414f88ec3b818108b82ec0ac00001ea18982cd14d09b447820c8ee86a62f514688b439217108b83100d200001ea12f12a093a091a43a1ee8e086442bb136086437c15a08302cc0ae00001ea0d0c2c314a099c47320b0ee069e2eb14488b83a816e08e02f00be00001ea073b2b9144c96445b2020e8468a2e3142889438816808482e40c200001ea01322d4153c9ec4a12238f846f831115589303cc18309483180ce00001e9fb3e2c814b098e4612038ebc6a830015188fc3b016f08602e00c000001e9f5482ca14b89aa47f2148f1c6e631315989343da18509483180c200001e9ef662c4949c9924662048eb06a02ea14789103a817308b02d80ac00001e9e9852bc145c9744551fa0e746902ed147089439217508c030c0c000001e9e39b2c514b49b447f20d8f2c6de30d15c09383ca18409803340ce00001e9ddcb2bf148497a4652048ea06982ee14b88cc3b417708d82c80a800001e9d7b62d6953c9da4882140ee86b82eb145089039616f08902f00ba00001e9d1d02c814c49c047a20c0f046a82ef14388b839816b08b02b40a400001e9cc022b514209304311ed0e106562d9141889438816808903000b600001e9c61e2c214789a047220a8ecc6b02fa14808c839617608d02d80ba00001e9c02d2c214ac9a047620c0f006d630b15409203d418b09703140ca00001e9ba132de1570a0849d21e0f546e230314e08fc3b618509483140cc00001e9b4132d095089a647520b0ea86902e4147089c38c16608882f00b200001e9ae1d2d095189e049421d0f386de31715609243d818a09503400c400001e9a82a2cb15109d447f2130f346cc30615209203bc18108d83140d600001e9a22f2ce151c9cc4862138f0c6b22f614988b839e17c09703040d200001e99c4d2c214e49ca47f2110ef86b82f314a08bc3a017208e02d80c400001e9964b2ce15089cc48520f0f146b030314c890c3c417d09203100be000 else 0x1ec85932cc94f49cc4842128f046cc30715389083c818809583000ca00001ec7fa82c614b49aa47e20a8ec468e2f614b88e03b017809303040ca00001ec79c42cb94b89944652048eb86a82f614e88ec3b817808b82c00be00001ec73c12ce15049ac46f20d8f006c22ff14f89083c618709483240ca00001ec6de62bd148c99046f2080eb86a62e813f089439e16d08b82bc0b800001ec67e52ce14bc9ac4822120f006ac2f915388e038e16d08102d40c000001ec62212ae141094a43b1ef8e2064a2d1142889039c16b08902ec0b000001ec5c182db95589f64a921e0f7870231315d095c3d818f09483340ca00001ec56462c094909aa47420a0ed46a02ec14688d03b416f08882ec0bc00001ec50542c594a49bc47620a0f086be2f815009103cc18408f03080c600001ec4a992b193e093644e1f50e7466e2dd14308903a016d08a82c80ba00001ec44932d115009c047c2120ebc69c2fb14e08e83b017d08d830c0b800001ec3ea42c794dc9ae47120a8ea86922e5141085c37816008602980b600001ec38be2c0947c98245a2000e8c6942f014a88e03bc17f08d03100ce00001ec32d92c4148c98a4611ff0ea06962fc14d09143cc18309402f40cc00001ec2d092ba146c97445f2038e946922eb14a08c43a016d08502b00a600001ec27312b7946896644c1fc0e586482c5136082836015207e82c40c200001ec21552bf94a098a4642008e946982f314808d03a817408882ec0b000001ec1b6e2c5148c98c46d2058eb46982ed148089c3a216a08402e00be00001ec15832c394a09aa4762090ea069e2ea14508b439816b08482b40a200001ec0fa52c2949899e46b2068edc6ba2fb14f89003c618509283180c000001ec09ad2cc14d89be48120e0ef86c630414a08f43b417a08d03140c400001ec03c02c794b498c46a20c0ef86aa2f014c88c839416a08702fc0ba00001ebfda92d595509f849c21e8f6470231f15e09543e618d099830c0b800001ebf7ae2cc94f499e4832128eec6bc308152091c3ca18609083000d000001ebf1e42bc945095c4612048ed06962f314d09043be17d08d82f80cc00001ebebdd2d214e899447520e8ee06962ed14708c83b418209403040bc00001ebe5c32da15449dc4902188f306e231b15889543d618909182dc0be00001ebdfcc2ce95009d849121a0f486cc30d15309083c8186093031c0d600001ebd9d82ca94c09aa48720d0eec6b02f614688883a017808e02cc0ca00001ebd3f02c594a89a04752128f246cc2fb14708c83a617d08682d00c800001ebcdec2ca14e49c447c20c0edc6a22f214608cc37c16a08682d00ae00001ebc7f72d094e09d04852108f346c230215108e43b818b09583340d000001ebc2022c594d499a46e20d8ec46a22ea14188b43a216e08982c40b200001ebbc192bf94a09ac47320c0ed06c22fd14b89183c618709a032c0ce00001ebb6112d515149c64832168f246ca307151090c3c018a09203180ce00001ebb02a2cb14f89c44832128ee06ba30515109083b617c08e83040c800001ebaa342cc14e49a647a2108f246d831415e09883fc19609a83400cc00001eba4292d8953c9b44722088eec6d630215289183ba17b08c02dc0b800001eb9e7a2a593e493e4401f28e186642da13d086837615e08682c80b200001eb98632d715109be47d20f0eec6c82f514688cc3aa17a08983180ca00001eb92902b014249644501fb0e346482d113e086436e16908982c40ac00001eb8caa2be94949884612000e846a62f614908f83ba186092030c0c600001eb86c92c314c09ac46d2078eb06a22ef14708e83ac17f09683040c200001eb80bf2d695249e249721b8f746fa32015b89183ce19409282fc0c200001eb7ae32c1147898646d2050e9c69a2e514508b839216808802dc0be00001eb74f22cc14e89c648d2130f106c4306154093c3ec18e09583040c200001eb6f092cd94e09aa47b20e8f0c6c830a154890c3c417a08a02cc0ae00001eb69092ce14cc9b04842120f286d830f15788e03d6189090030c0b800001eb62f12e2155c9fc49b21d0f686e830615a09483e019d09883140ce00001eb5d2a2b9943c97045b2010e746962f814d88cc39a17908902d40ba00001eb57302cc94dc9b846d2068ed06b830115589183d418709303180c200001eb514d2bf948899646920a8ee469e2ec14888cc3c018108a02f00b800001eb4b6c2c494e09c44832188f286e231615b89643ea18e098032c0bc00001eb45692d4953c9da48e2150f2c6e031415889543ca18509202f80d000001eb3f802c494b499846c2050ea068e2ee14988ac3a216108402cc0b000001eb39a82c094849884652028eb068c2e114388b03a617308902e40aa00001eb33d02b9949899246f20b0eac69e2ee14988d039616908902b80a800001eb2e032b4941894a44f1ff8ea46822ec14208d43a217b08c031c0d200001eb283a2b8945497a4581fe8eac6ae30514f88e43be17a08a82d40ae00001eb22762b0941095a4511f80e446762e314608a839017308602b00ac00001eb1ca02bc146c98a4622048ea46962f414e88d43a217208802cc09e00001eb16ea2b414049504591fb0e6467e2e4144888c39c17608c03280ba00001eb11222b7146897a4652050ea069e2fc145888c39216708a02e40be000) else (if i < 316 then 0x1ee014f2db15549e449521f8f806f832116009683f618609483380d200001edfb702cb950c9c847920a8ed46b02fd15289283c817d092831c0bc00001edf5762d114f89b847620a8ee068e2dd14388bc39a16f08c83100d000001edef6d2d795189c647a20b8eb469c2ed14988dc3bc17e08c02e80d400001ede9852c514b899e46c2048eac6922f0148889038816e08b83040ae00001ede3cd2b294349524511fa0e5467e2da14008a039a16b08682a40a400001edde0b2b394649804642048eb46b42ed14108a039a16d08a82cc0b600001edd7f72d895209ca48b2158f286bc30c157090c3bc18e09702f40b600001edd20a2c4149c9a44642018e746762db13e087439a17508b82dc0ba00001edcc1d2c214a898e46e20a8ed869e30015388e43b218508e03100cc00001edc66d2b2142c96445c1fe0ea46902ec14488a03a617d091830c0b400001edc0652d6953c9d24852170f306cc30a15008e03aa17d094833c0e000001edbab52a713cc92a43c1ee8e146622db142889c39a16f09382f40a800001edb4af2ce94f49c648820b8ee06b62fb14f08f03b217e08882e00be00001edaec82c214a49904672048eb06902ee14a89003c017908d030c0c000001eda8a92e215749f84a221e8f806de309151090839e17e09483180ca00001eda2a22d595189ce48c2188f686fc317159893c3d218308e82e40c200001ed9cc22c2946497045c1fd8e946b22f3147889439a17408c82e00aa00001ed96cf2cb14ec9ca4832118efc6ae2f814a88c43a016b08802e40c400001ed90af2e015489e449121a0f286d830c15208fc3ba17b08c830c0b000001ed8acc2c0947c9844612028ea06862e914a08a839e17308b82e40b400001ed85192ab941c94c4421f50e606842e9144887838216e08182a80aa00001ed7f2f2c194c49be4802158ee46ba2ff15489383de18a09483400c600001ed793a2c394d898446a2090ee06c030515509183d418b096034c0c000001ed73422ce95049b248320f0ef86cc2fe15188fc3be18108f02e40c800001ed6d4b2cd950c9c64812100f306e2316157090c3ca18008b02f00b800001ed673c2d59554a024902200f806f631715d096c3e219909c83480c000001ed614d2c914e49b84712070ebc6982e414508b438817908c03000c000001ed5b4b2d615089d848b2130f206ca30015409203c018b09783300d200001ed55532d315249dc48c2150f3c6da31515509483c017308982e80b200001ed4f502cd94fc9b04782098ed06a62f414c08d43a016f08782d80aa00001ed49842b3944895e4551fa0e6468a2f514a88c83b218209603200c200001ed438c2cd94e899246c2048e9c69a2ef147889c3a017f08a82e80bc00001ed3d8a2cd14e09b04832118ee86b42fb15289443ee19b09a832c0cc00001ed37d12a793cc9344331ef8df86542d313c886038815c08202c80be00001ed31eb2bf94409704551fd0e646622dc13a888838816b08a82e00c800001ed2beb2d194fc9ce49021a8f786f831015609283d618608f02d40c000001ed26292b1943096845b1fb0e6c6842f214c88dc3ae17208b02bc0b400001ed20452c9149497c4652000eb069a2f314788a43a216e08702f00b800001ed1a362d915049d04842120f186bc2fe14a08c03c017d08882d00ba00001ed144a2c1148097e45f1fd8e806942ee14588e038e16308982f40c000001ed0e7c2b9144c9604481f48e346682d5140089839a17c08d02f00ae00001ed08882c2947c97c45c1fe8e406742e614388b43aa17f08e02f80b800001ed02ab2bf146096c4632078e906962eb14208b037015f08302bc0a000001ecfd022a913f093a4401f08e3c66c2d513e889839417308d02f40b800001ecf7272b8143896c45e2000e7c6a02f214c88ec3b217608e02ec0b400001ecf1202d815649e248d2138f186da30715409283cc17808e83100bc00001eceb072da95289e24912168f446dc30b15208cc3b417e08e82ec0c200001ece5342bd144895e4632070e9c68e2f9154894c3e018a09803400c800001ecdf0e2e995dca284a62248f4c6e431515909183c018109302ec0a800001ecd93a2c1948897e4562018e7468c2e013e888c39617b08902d80c200001ecd33f2cc94f49bc47e20c8ef46bc30314608b83aa17c08a83040c200001eccd462cb14d09b24732058ec46ac30014c88cc39617608a02ec0ac00001ecc7582cd94c098a4652048e906742e314508a838e16708102c40c400001ecc13e2de95509e44892180f306ea31415989443ea19109c03480c200001ecbb3b2d315609dc4872168f106bc2fc14f89283d618609103100c000001ecb5482c894f09ae47620c8f0c6d22f714608c83c418708f82e80ba00001ecaf672c294c89ae47920f8f086d230815409203c217909182f40c000001eca9812c714bc9a047320d0ed46aa2e8145888839e17f08602dc0a400001eca3872cf94dc98c47320c8ee06ce30014c09103c017e09102ec0c200001ec9d912d415249de4902188f446ce308153892c3b817c08e02e00b000001ec97842d815009ca47e20d8ed06c02fd15009283e018609a83400e200001ec91a12bf946c97e46a2058ea86902fc14588a439617308c02e40c000001ec8b952d094fc9b446f20b0ea467c2e6143089838c16a08c83180de000 else (if i < 317 then 0x1ef7c482c194b499247120d8eb86a62ef14908c839e17308682d80be00001ef765b2c694b09b24812188f546e031015709343c2186090831c0ce00001ef70752c294b098c4632008e886822ea14288b83a418209483100b200001ef6a8b2c714bc9964712070ec46ae2fd14e08ec3ba18309582f00c200001ef64a32c694c89b44782060ec86a82eb14388a83a817308982d00b200001ef5ec92c3949c9a048020b8eb46a62f714c08ec3ba18409082dc0ac00001ef58a22db953c9de48c2178f146c430415589383e419309a83500ce00001ef52a82cd15109cc48e2110f306c02f914b88f43d018508c02cc0a800001ef4cb12c914e09a04672068ea86a02e3141889438016708682c00b000001ef46ea2b4143c9644581fe0e6065e2d313e088c39016b08c82f00c000001ef41042c394b099446b2088ea86922f214d89043ba18309183280be00001ef3b272c514849764681ff8e986762e5148888c39a17908d03000a200001ef35292cd94ec9bc48120b0ef46be2f414e89183be18909783240d400001ef2f2f2c894ec9c247a20c0ec06ba2fe15108f43a417608e83140c600001ef29492c4149c9924672028e906882eb14788a439a16508382c80a800001ef239a2a8138c9144401eb8e1864e2c3138089038616008502d40b400001ef1da02c694bc98c4712090ed46a22ed14688c43ae17508d02f80c400001ef17c22c0147899046f20a8ee86c030715509383cc17908d03280c000001ef11b02d515109c248520d0ee46b02fc15188ec3ae16f08202a40a400001ef0bdd2b7145c9744541fa0e786822e014a08c83aa17a08b03100da00001ef05e62ca14c89a246c2048ed86b830014908d83a416e08f02f80c000001eefff42ce14c499445f1fb0e6c68c2ee14588a03a417308a82ec0be00001eefa062c194949944722050eac6962fd14d88e03c618309182fc0bc00001eef42e2bc145c96a4511fb0e746922e214989003c218109103280be00001eeee632b8143496a44f1f60e406822e514108a43ac17d08d02e80b800001eee8602d595289de49021a0f686e230b15789483d818f095032c0d600001eee2752cd94f89b647b20b0f006b22f714d08d83a617908f03100ae00001eedc7e2cc94f89c04832148f286ba2fc14d89103e618e09503440cc00001eed69a2c194c09b448020a8ed46b830a154893040619509a83440e600001eed0972d515209da48a20f0ee06c430f15509443e218b09302e00ba00001eecab82c514c49a447520c0f086aa30715509243da18a09082f80c000001eec4c22cd150c9bc4772120ef06ca2fb14808c839e17208802f80b800001eebf052ad94389764732088ea869c2e013e88b039416d08782e00cc00001eeb94e2b2942497045a2018ea46982ea14488c83ac17709002f80b800001eeb3442d595089ce4752110f1c6c830915289143ca18109203400bc00001eead392d294f49c248320e0ef06ba2fe15108ec3c417d09083040be00001eea7622bc948c9824652078ea46ae2e514008bc3ba17f08f02e80a000001eea17c2ca14b89aa47720c8eec6bc2f614b08b039817908f83080b800001ee9b5e2e29598a1a4aa2268f98718320160093c3e819a098831c0c400001ee95662cb94f499c46820a0eec6c62fc14c89103c418b09302f00ba00001ee8f752c894bc99846f2030ea46a42e1145889838a17008902c80c000001ee895a2dd1570a0249421d0f0c6c02f514e09043b217c09002ec0ac00001ee839a2af142094c44c1fb0e4c6802e714b08ec3bc17909103040c000001ee7dd82b314389544451f58e4c6562d513c88b039816e08902e80b600001ee78082b814489684582018e7068a2e314888fc39617208b82d80a800001ee71f72d795589e84982190f506f030a15408f43c618b096031c0cc00001ee6c162c494ac98a46d2040e746702dd14388bc3b217008d82ec0c000001ee66562b5140c9484411ef0e0c64a2ca135883837415e08582c80a200001ee602d2e415b09f449f21d0f5c6da30b15689343c217a09103080c000001ee5a242d095049ac47920a8f006b22f914a08c83a017608a82c00ac00001ee54552bf14ac98e47520e0ed46b62ff15009303ea19209703500d000001ee4e8e2bc946096645c1ff8e686782dc13e088c3a817008d83140be00001ee48892cb14f89b84852180f646f231a15a893c3f619509883300c600001ee42b92ba14449744672058eb06942e914588a83ae17608c02e40c400001ee3cc82ca14e49b247d20b0f006a02f4146088838c16c08782c80ac00001ee36ad2e19584a1c4a92260f846e830d155094c3d218b09483300a800001ee30be2c914dc9aa47620e8f106e630215409183c217c090033c0be00001ee2ace2cb14cc99e4652038ea46842e414388d83b217e09103140c800001ee24ea2ca94c49a847a20b8ef86aa2fc14c88f83ce192094032c0ce00001ee1f1a2b7944497444c1fb8e7c6702dd140088439616608c02e80ae00001ee19192ce14dc9a84702038e906802e814408b439c17308c02e40a600001ee13132d315009ce4982198f7070632316109783fe19409383280c800001ee0d462b5142096a4541f90e6c67a2dc141889039817708f030c0c400001ee07602c414a89984792090ee06a830114f88ec3be17308982c40b8000 else 0x1f0d47200000000000000000000000000000000000000000000000da00001f0ceb62b5940c9564532020e846922ee14608ac3b017108b83040c000001f0c8ae2d415389d84942190f5c6ee31a15a09683f619509903340cc00001f0c2c62c914c499a4772078eb06a42fb14e88e03b617708c02e80ac00001f0bcbe2d6153c9d248d2168f3c6dc30b15789343e818f09102fc0b600001f0b6c72cd950c9d44832128f006b82f714488b039416a085029809800001f0b0ed2ba14409624521fe8e806982e414488a83a216c08602d00c000001f0aafa2ca14d49a646f2068ef06b02f814f08b839217d08902d80a800001f0a4df2de155c9e24892128f246cc30315409343d618b096833c0d200001f09ef42c414a49904692080ed86a82f814988c438817208d82e40c400001f098fd2cc94cc9984732018ec868e2f114a08cc3a817208902e80be00001f093172c314949884601fe0e7c6802ee14608b839817b08c82d80ba00001f08d352c0145c97a45c2068edc6c02f414b08e83b217d09083040e600001f087582be94909784612060e846902e614188c038e16c08b82dc0c600001f081682d395109de4902188f686ec30815709303d618609383140c200001f07b7b2c514cc9ac4832110f006c830315109203cc18a09203200c000001f075832cc95149da49121b8f406de30215108d839a16e08d02bc0b000001f06f962cb14c49be47c2108ef46a02f714a08883a016608382d80c200001f069a72c814d49b847920f0f286bc30015409083b417308b02c40ca00001f063bb2cd95049c647e20f0f1c6c630714f890c3ba184097832c0b800001f05deb2bb148097a4621ff0e5c65e2d9140885836616208402a80a200001f057ef2cc94d49be4832148ef46b02f314b08c43a818008f82f80d800001f051f82cd94ec9aa4732050ecc6c02fe14d090c3ba17408582b40b600001f04c142c4148c9a44702088ecc6b630414e89303de19009383440d800001f0461f2cf14e89a84752090e986b62fc14408c83a017308882d40b000001f0401f2ca94c09904652068e8068e2f314408bc3a017608e82e40b000001f03a232d1952c9b84782080eac6a42ed14588d43aa17c08d03240c400001f034482bb147498a4752058ea06782d614288b43b217e09083200c400001f02e4e2cc14cc98a46b2040e8468e2e414a88d83ba18009483140be00001f0283f2d615049b247620b8ed46c02fe14a08e03d018608c82e00c000001f022592c1148c98a4571fb8e886862e614508bc39e17608d02f40be00001f01c562d695409e648d21e8f646fc31f15f094c3de19b09903380c000001f016752c3947496a44d1fa0e7467a2df138086c38016e08983200ca00001f010662d3950c9cc4892188f286e431915689503e418e09c83240c400001f00a6d2c794b89ac46d2070ec46be30815209243da19009203300ca00001f0046d2d1954c9f64a92198f2c6b630515509403de18309083000d000001effe752d315209b24732088eac6842e314808cc3a417008902dc0a200001eff8a22b894a09a446b2098ed46a42f314d88e43c818308c02f00bc00001eff2ea2a713c89344411f30e3463c2bb132880434c154082029c0a200001efecd22d595189d848c2158f046c230115488f03b417f08e03000c400001efe6e02c894d49bc47820d8ee46aa2f214688e43ae17a08f032c0d800001efe0e22cb94e49ba47a20b8ec069e2e014088a039617008d02f80b800001efdb332a713e89304381f10df464c2cf136887839217e09282f40b000001efd5282d495009d64882128f0c6d430714e89003c618c095833c0d800001efcf5c2b594549824591fb0e686622d0135086037e15f08682d40ca00001efc99b2b094289544521fd0e6c67a2ea14188a839816c08b82e80b400001efc3ce2b7944896a4591f80e5c66c2dc14608a439215f08382c40be00001efbdd42c894c89a44692058ec86a22dd13e88743a817d09303000bc00001efb7c82d494e49ae47a2098e9c6802df140088838e16408202d40b200001efb1cd2cf951c9bc47d20c8eb46942de143089439216e08d82e00ca00001efabe02c594e49a44732070eb86ba2f714b88d83b218109103180c600001efa5f22ca14cc9ae47c20d0ed06a02e814588a438e17808982e00ba00001efa01e2b2942c95a44b1f68e386462d413d086c38015c08082c40cc00001ef9a052dc95449d44902198f7071032916189a840019309682f80ba00001ef93ec2dd15609f049621d8f886fc32a16009603dc18509603400ce00001ef8dfd2cc14fc9bc47b2098ec06aa2fa15008f43b818109003180ca00001ef87ee2d895389ea4962180f306e031215d89283d018b09883300c400001ef822a2b214089444411f20e1465e2d914308b439a16f08182d80ba000)))))))))

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



private theorem b312486 : covered 312486 312565 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b312565 : covered 312565 312645 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b312645 : covered 312645 312724 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b312724 : covered 312724 312804 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b312804 : covered 312804 312883 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b312883 : covered 312883 312963 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b312963 : covered 312963 313042 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313042 : covered 313042 313122 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313122 : covered 313122 313201 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313201 : covered 313201 313281 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313281 : covered 313281 313360 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313360 : covered 313360 313440 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313440 : covered 313440 313519 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313519 : covered 313519 313599 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313599 : covered 313599 313678 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313678 : covered 313678 313758 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313758 : covered 313758 313837 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313837 : covered 313837 313917 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313917 : covered 313917 313996 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b313996 : covered 313996 314076 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b314076 : covered 314076 314155 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b314155 : covered 314155 314235 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b314235 : covered 314235 314314 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b314314 : covered 314314 314394 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b314394 : covered 314394 314473 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b314473 : covered 314473 314553 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b314553 : covered 314553 314632 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b314632 : covered 314632 314712 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b314712 : covered 314712 314791 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b314791 : covered 314791 314871 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b314871 : covered 314871 314950 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b314950 : covered 314950 315030 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315030 : covered 315030 315109 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315109 : covered 315109 315189 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315189 : covered 315189 315268 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315268 : covered 315268 315348 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315348 : covered 315348 315427 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315427 : covered 315427 315506 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315506 : covered 315506 315585 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315585 : covered 315585 315665 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315665 : covered 315665 315744 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315744 : covered 315744 315824 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315824 : covered 315824 315903 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315903 : covered 315903 315983 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b315983 : covered 315983 316062 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b316062 : covered 316062 316142 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b316142 : covered 316142 316221 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b316221 : covered 316221 316301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b316301 : covered 316301 316380 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b316380 : covered 316380 316460 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b316460 : covered 316460 316539 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b316539 : covered 316539 316619 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b316619 : covered 316619 316698 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b316698 : covered 316698 316778 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b316778 : covered 316778 316857 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b316857 : covered 316857 316937 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b316937 : covered 316937 317016 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317016 : covered 317016 317096 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317096 : covered 317096 317175 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317175 : covered 317175 317255 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317255 : covered 317255 317334 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317334 : covered 317334 317414 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317414 : covered 317414 317493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317493 : covered 317493 317573 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317573 : covered 317573 317652 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317652 : covered 317652 317732 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317732 : covered 317732 317811 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317811 : covered 317811 317891 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317891 : covered 317891 317970 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b317970 : covered 317970 318049 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b318049 : covered 318049 318128 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b318128 : covered 318128 318208 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b318208 : covered 318208 318287 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b318287 : covered 318287 318367 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b318367 : covered 318367 318446 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b318446 : covered 318446 318526 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b318526 : covered 318526 318605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b318605 : covered 318605 318685 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b318685 : covered 318685 318764 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b318764 : covered 318764 318844 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b318844 : covered 318844 318923 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b318923 : covered 318923 319003 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319003 : covered 319003 319082 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319082 : covered 319082 319162 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319162 : covered 319162 319241 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319241 : covered 319241 319321 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319321 : covered 319321 319400 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319400 : covered 319400 319480 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319480 : covered 319480 319559 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319559 : covered 319559 319639 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319639 : covered 319639 319718 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319718 : covered 319718 319798 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319798 : covered 319798 319877 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319877 : covered 319877 319957 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b319957 : covered 319957 320036 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320036 : covered 320036 320116 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320116 : covered 320116 320195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320195 : covered 320195 320275 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320275 : covered 320275 320354 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320354 : covered 320354 320434 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320434 : covered 320434 320513 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320513 : covered 320513 320592 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320592 : covered 320592 320671 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320671 : covered 320671 320751 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320751 : covered 320751 320830 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320830 : covered 320830 320910 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320910 : covered 320910 320989 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b320989 : covered 320989 321069 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b321069 : covered 321069 321148 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b321148 : covered 321148 321228 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b321228 : covered 321228 321307 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b321307 : covered 321307 321387 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b321387 : covered 321387 321466 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b321466 : covered 321466 321546 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b321546 : covered 321546 321625 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b321625 : covered 321625 321705 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b321705 : covered 321705 321784 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b321784 : covered 321784 321864 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b321864 : covered 321864 321943 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b321943 : covered 321943 322023 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322023 : covered 322023 322102 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322102 : covered 322102 322182 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322182 : covered 322182 322261 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322261 : covered 322261 322341 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322341 : covered 322341 322420 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322420 : covered 322420 322500 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322500 : covered 322500 322579 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322579 : covered 322579 322659 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322659 : covered 322659 322738 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322738 : covered 322738 322818 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322818 : covered 322818 322897 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322897 : covered 322897 322977 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b322977 : covered 322977 323056 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b323056 : covered 323056 323136 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b323136 : covered 323136 323215 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b323215 : covered 323215 323295 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b323295 : covered 323295 323374 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b323374 : covered 323374 323454 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b323454 : covered 323454 323533 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b323533 : covered 323533 323613 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b323613 : covered 323613 323692 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b323692 : covered 323692 323772 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b323772 : covered 323772 323851 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b323851 : covered 323851 323931 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b323931 : covered 323931 324010 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324010 : covered 324010 324090 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324090 : covered 324090 324169 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324169 : covered 324169 324249 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324249 : covered 324249 324328 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324328 : covered 324328 324408 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324408 : covered 324408 324487 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324487 : covered 324487 324567 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324567 : covered 324567 324646 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324646 : covered 324646 324726 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324726 : covered 324726 324805 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324805 : covered 324805 324885 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324885 : covered 324885 324964 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b324964 : covered 324964 325044 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b325044 : covered 325044 325123 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b325123 : covered 325123 325203 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b325203 : covered 325203 325282 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b325282 : covered 325282 325362 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b325362 : covered 325362 325441 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b325441 : covered 325441 325521 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 312486 325521 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b312486 b312565) (joinCoverage b312645 (joinCoverage b312724 b312804))) (joinCoverage (joinCoverage b312883 b312963) (joinCoverage b313042 (joinCoverage b313122 b313201)))) (joinCoverage (joinCoverage (joinCoverage b313281 b313360) (joinCoverage b313440 (joinCoverage b313519 b313599))) (joinCoverage (joinCoverage b313678 b313758) (joinCoverage b313837 (joinCoverage b313917 b313996))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b314076 b314155) (joinCoverage b314235 (joinCoverage b314314 b314394))) (joinCoverage (joinCoverage b314473 b314553) (joinCoverage b314632 (joinCoverage b314712 b314791)))) (joinCoverage (joinCoverage (joinCoverage b314871 b314950) (joinCoverage b315030 (joinCoverage b315109 b315189))) (joinCoverage (joinCoverage b315268 (joinCoverage b315348 b315427)) (joinCoverage b315506 (joinCoverage b315585 b315665)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b315744 b315824) (joinCoverage b315903 (joinCoverage b315983 b316062))) (joinCoverage (joinCoverage b316142 b316221) (joinCoverage b316301 (joinCoverage b316380 b316460)))) (joinCoverage (joinCoverage (joinCoverage b316539 b316619) (joinCoverage b316698 (joinCoverage b316778 b316857))) (joinCoverage (joinCoverage b316937 b317016) (joinCoverage b317096 (joinCoverage b317175 b317255))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b317334 b317414) (joinCoverage b317493 (joinCoverage b317573 b317652))) (joinCoverage (joinCoverage b317732 b317811) (joinCoverage b317891 (joinCoverage b317970 b318049)))) (joinCoverage (joinCoverage (joinCoverage b318128 b318208) (joinCoverage b318287 (joinCoverage b318367 b318446))) (joinCoverage (joinCoverage b318526 (joinCoverage b318605 b318685)) (joinCoverage b318764 (joinCoverage b318844 b318923))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b319003 b319082) (joinCoverage b319162 (joinCoverage b319241 b319321))) (joinCoverage (joinCoverage b319400 b319480) (joinCoverage b319559 (joinCoverage b319639 b319718)))) (joinCoverage (joinCoverage (joinCoverage b319798 b319877) (joinCoverage b319957 (joinCoverage b320036 b320116))) (joinCoverage (joinCoverage b320195 b320275) (joinCoverage b320354 (joinCoverage b320434 b320513))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b320592 b320671) (joinCoverage b320751 (joinCoverage b320830 b320910))) (joinCoverage (joinCoverage b320989 b321069) (joinCoverage b321148 (joinCoverage b321228 b321307)))) (joinCoverage (joinCoverage (joinCoverage b321387 b321466) (joinCoverage b321546 (joinCoverage b321625 b321705))) (joinCoverage (joinCoverage b321784 (joinCoverage b321864 b321943)) (joinCoverage b322023 (joinCoverage b322102 b322182)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b322261 b322341) (joinCoverage b322420 (joinCoverage b322500 b322579))) (joinCoverage (joinCoverage b322659 b322738) (joinCoverage b322818 (joinCoverage b322897 b322977)))) (joinCoverage (joinCoverage (joinCoverage b323056 b323136) (joinCoverage b323215 (joinCoverage b323295 b323374))) (joinCoverage (joinCoverage b323454 b323533) (joinCoverage b323613 (joinCoverage b323692 b323772))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b323851 b323931) (joinCoverage b324010 (joinCoverage b324090 b324169))) (joinCoverage (joinCoverage b324249 b324328) (joinCoverage b324408 (joinCoverage b324487 b324567)))) (joinCoverage (joinCoverage (joinCoverage b324646 b324726) (joinCoverage b324805 (joinCoverage b324885 b324964))) (joinCoverage (joinCoverage b325044 (joinCoverage b325123 b325203)) (joinCoverage b325282 (joinCoverage b325362 b325441))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 312486 ≤ index 600000000/512 := by decide +kernel
private theorem starting_value : fast 600000000=31324703 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 600000000=31324703) (n : ℕ) (low : 600000000≤n) (bound : n≤625000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=600000000
    · rw [first,anchor]
      exact starting_value
    · have past : 600000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤625000000 by omega)
        have within : index n / 512 < 325521 := by omega
        have lower : index 600000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤625000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ600000000To625000000
