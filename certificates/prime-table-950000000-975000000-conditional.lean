import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ950000000To975000000

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




private def radical : ℕ := 0x415acffd4b3c6ea20e7cb8255ecb2f688d1610e94386cacf7f5fccffcf27dcc99ee6b4f95863dce60ca556397c2f7cd28c70686488ab1954bcaa9a4949a3092556b59b831149c61407e004c5a4330a1ba95bc6522dd6877c736007799c6a674ca691a8be8d026e8916d662cd5fa8cd0cfb382ee1608778d97fe0b61aa19c66e4b3dbf3fe73e53f6652214f7910dcd3e3cef29a6ee95b0538b0be2fb8c42e21142341957ca663d2ffa413fef5af1029755609c77d66b64bed816b9c8a95db76dd9bf5fb4c61a531f6d627d6661ead5d7a99690a503eca859c90d8a29a570f9c20c1ea6a029677b194079ba97ff0da4a44044c53b8f5757f7df84cbf4623630b45ac2459a5fbf56e13b14d9c056b03a44a3c2c87ff3bc7b7aa0c752f21dea0e7c1a457324d4d08949c181bad006c1b01bdc2e9125b03cdef6b0042bc3dff1e7f7d50d9f9ca148de36fcc15ea1ad56197f08dd39b03b8d1c99fd14da17e02cc595e2f07cfd1bea45363f24fb2f18468b36e8e9f57fe348c21e3427aee2e22c9e4e920092467b87c337119d171dd0f9cbdadbab4065fceb6ab2718e53da47d0d0712cb340f45d78896fde4a4c8ed5ce9ce997bda8f67ff3d8a9b6aa72473733a7932b9ac5837be365f16c6ba6ea130d617bda413882a40b3db137c58441719ea349f813b241b1b15f8e2a617123ff4ff25ef2bba05aa0ddf3ed0c2af682000f3ef4cf4d4415e9a0626126624affff76744a4cbd07db2621504a76406cebba2c67edc0f433415e3a8f7310cbde18eec628248e6ef8c62ee87ba32ed82e499cf05048650b71bbe7543e0427c42d93079382b1c8cf93a3638c3020e1d1670167dfb3cd6d56e8222ebb8ce804b6d656a25153a5b53c8ba68999a7763912371e111a3a93f3fa45e79016c979b453850384167cb8fd026c3f6eb8a28acacb1438550ffbdbc95243309940141e7098a5973d389640a51cee770ea265ae9460d0e5d6407debfa9b56f2c50fbe18696cf30335256d3b49b633805b90c9e9a13eb2e345fb51fa4327135bf109284b5424e21566f3d0e5bfa5b82f1914e4c2bdab467af86cc78cdb57b28a4ad23d8f02927159b9b451776f7436bf73f90f6d0f50ce5070fda0828e8ad021e5c938a209444edbcbb12a0fd12e0046d5b44e6b7554a640138b24e73752e71d0b388937b2f0191109f2fe29adde969bb204aea3e1f4e8e9ca17830caa540137925c319f021019895117154693a02c7e3c9301d7ee38302a8a45d88a1472f75b251ad66378a21515996eb3df2091529890b268e1789e9accd13f29c3a698966e3691048993e7311603a95978d2c1f38aceae4bf8604f5d9e4bcc184e3be556570f76e6068f330b9e30da457d5809c69289b01f688638a4e1a9707b8d95ce04a4b956315fbb137d14f63bb3acd57546cffdc51fb217fb57f9f30f1845cb5422e8bf9c6fa26106251b83c94ae5ce03a35b86c7444a2531f2d28b1f8d1fdc37e0836c64c3dd90f1c21452ef4e46934e8d8677728340ec0134743d9dafb6056ac19c6e9848300e3bc65c419abfbadb41f00edb6db992126299bb6457ba507ddfaaf35953387ac3c8e2cf8c686915464fe3ab71589c2280325dd173c7c5b97f03ce572e005dc277e99249fcdbffdb653a6405e1baf1078fb913fe4d640681cd1b6c326f37b0a16fc16a25c830feb64c093b25a43e44142c001e9f231715c7ebe64a7aba31532563d12ac0a3cd5e439d591b0f37e06d624ebd6dcf7fc30ab3ea85cb3c6df1acacb0d424f7dbafebb4271e6f030b3e8b220013bb37e3e4b17dfda492764413bf07684425c0a21a99b330dacfc033924a710de1522aead410ce414a4bbb495173778d3cd2930d9797edb2b36a68305884658bc12e3c76211d921db9083a67f2acba306516603b4d779c5e7156c5dc15e7236122a81aca16d10634053ee747745aa6ed3c590bac87f03ec555cdc16fe7408c68732339fe2f05f629f519879c8df971d066f26bb881c41c51dd7315edc44a43383539c92254664a5f652c773491106af379eeee5bb9058faa25dc8573e79b2c949a3cad910ad0310ac645966efb0d18b93236fcda9ab855efa7e4b259d67ffed2dbc29af68df89ad1875d2e6d9d3955d3686891917417913d6c423d636d6a2ad3aa449b8b97b7d219c4355fad5cabe1a33c735dd8cd30274e872b55524d8c22123317040526684a5a257386d9970061d3903e613df6fbab5d0dca9b148a10f8c2135edcf85304e9b6770339d2b8e025dc16b7372096c13ef003f78dd5969c1dda958070510e2973210476e9dc71937435fb3d15bf63bc9c753eed762668b1cb1e1c0599aa7c93af19eed0223d804adc9d06a55d30e9eba05d1336a5115d57438ec9d5c52fec79c2a62fb168c130184d45c3f70f9ce72ac8cb319cd4f121d00ef93365cc3de5a20eef157122481dd1b3458106a527c0028c5f3cf38a3e42a80f55a6f054ad11dd8fe5f8479ada0ed3055d62cf7fc8cbcdc5fb9625a07577e08e77358ac12c9216a6b1b7fcf90b9e9075ebdb177fb2f702a8abaf5d82a74b36f594a41a0d259cfe99faa4f85f70427e0d84559f53005fccfd6d12a26c62e1f6ac573469c768c74f35987ac9829cb4e3686fb817c2be82c6d92d4b8f7fb000b44fe25dfc27881ce409e174296eb1ede16afb13fe93d3471b0c4d5ce26ac9cc84827d4d926834a77558e995e40b88396739b075e705652567936f6a91fde96e102b8fea7b09ec52fc893aff588e4013ae657848fd31c875a1e5d64e30edb85a1cd2fb7642d554b6e60366de8ef98846032f8e40f2dee6595b9dcdc775b8cd1a331e17bbf570d20ae189da53da5a596c6e4ac68c7cb64f3081ef0987385babd10080049ae1e5c09a7163eec9145176a4b3d59838149854f54d334369bb16514848b0c3c7ca627de352a92022063147da2d11d252d5258a1e027761001e729ad64855cc91f47baf4e4479f23bae160b580b6fd15b08bec94b954b7bbca6c2842a9221f27dea331d4b013bb5b936609ee9a8220d962f55f893123bdd661d778d75ea7c4599f35abd94f9ff67ff3697ee1fdca5b72489e1fd74d2383ac02bea50eb71fe94887719889423c8a6f74d0d2a25115ba8218c73161ea6d4b772e025f6591f47f3b814e9248ac04565f357fe219ebc6c426b4380e36109184955c8124a8934a56052f35df37cbc1bb559f63c9a3de2529b042716382d068cc69cbf4b0a296426a2fa346e04849281b63e3ea73520df0803dce8000ddfafaeb96fcb5efb59d996294dcb027e71b6df191083313463d3b9f690b0719369e7a020bcb0f18d675bf72415b0bb786a5030fbd971edc855ed168ae8b20e11fe8f5853abd651c5b7cb0e910007d736d355ab0dc5ae312b6c39a7c30fef1094ef7220b7024f2bfcaae0eae99697491d89a3d85b8f30ab09c1cc632de4b5be98429a455f6af601625a100d7f699107b796594c9f872ec5bc1f41a3baa13b399f6b6eb96671feebc0b4fcc5d7db38e9dabbf4f2a649d0baefd0f0c7b71f3b94ca9659cc86ea1da87336d8283f08ec4a908faa15005c3537822f1b9db1124f192d5b46bf1b49858826794bd170de8bb4adeb2b7d1bc5fd055135951662ed04d4de195c7eb5f0036806dc7919927a0a9bad89a5a45281b566b2ea8a5898ae3a2d21cf574c473335e240cb38d684b29c5e475b6867deade8296645905b92ea3109cdee8d70868c99bbfbf2625ca7a2056f80ed67046b95785030402c79d739970a77be6cdebf94d573398e7a64618f797ac80554084c3b9d2c59e553a4707e597f0240589b7ed7b8c0ec64756f0238b5d6fe8ac88c631092deaa8b09c908614082fb2ee4c5aec4e7d81c8216afc03ffeef276fc1799e0a9dffc40d8986233c1f4ea180cf81febb1fc9340267c9a820df1cd06ddbfff8b7b416dd93ea1dc6b0cbb116ba183ba80147ffa2ce02e0a9fd2d977652a2fcc3f55fa2f25e359b980bd6e09e81e7146f3017925c037be03e987d7e8a1e9bad4b374ee9d5e9c11004d3cd41f0fc92d678b1ba79d1a3081f84357ad59e6af2b2ebf69ab6f531daee860f738db361e13f337577c42b3f6347cef7ea68f8ae08b1fcc640f393ea4217cb8660091044cf3b744ffd815e82cdcdca9858b0bb541e00a97cea7f4db93b36c5f01b79b24f28325e94b4691a17cc53e3e0e29876d53b47a098e7bd39f6bde42a7e370ebe4b831e6d01fe6586a990747af8e92b4e1b8df555e2898f8b51f77f55a0cbd98807ba5bca237d2f496355d18aee80c7246e8bf3f5b58c6a0572ce46087e32b0bdee1d1c5289d1637c83f3ebbd08f886cc61bce2d19948db1f6303550e8376aab66c09c0a3ecb98d6d72c0ce9df3d55ba4df7cb5fd4e82d40767ac769e59a72131167f4ee74e291218a85a18661dcf3bf2790e5c114b0c9a029d04dcac38ec9cf979e8e5aa96620680df332ed274891f8943a186d53371a771c63ca19adc179e0f131097c7d7da863aeb600402f43c56c6b4464f398ae482a2517903f57fe758d9ec76ad2b6949ac6c9b58ce9bf13c1b1cbb500b8fffb3378f6fc1b375af7e0a7e0775dcf0458edc9851988415261af1cdef819e6ab44a20d0bf2bc57811060dc6552c3ac1fc15f7698c80b6304af1b63097ff81109435c8ba2757b1bcd9b589d85005f82c75b88645d1ef16e058d16ff1a08872c1bbb85d6dcd225f9bee5e0c69ff862c1286df9a48f5e22cae18aa06795dca56b706538665580b322ef3e6f404a461ac7e3da51174e8a199d3e819d419c374fd976e845490e0db4c129ef956d6ac4fa4efb2e95500c7d3ca768cd784eda37b0db0e2ddd2ed4b8b66914b1accbcca154766fb136a8978d787558a05d26b66e7450fcac24e8efae3a3ec4f4405d18a1b46ebece43e26adb039715d1083be4de0719800d70d1d636ea70308358895a81d4487c38d2aae09dbb7ba85888ca91ae67a8428d731749326b72f71e0f0354854099570fe9ed9de6d738d3366f951d22795cb2d6d791bbfdd00fcbe20209a79057c512c257cf8cc7728c2875b3370a28d934828db8c117d471ce69043eb633bdfb22eccc5569124f485da770d15f6319ff9fa2fa44d69d1e2f3eaa51cfeeec24c9f22168f7bb76319dee32e023dbdb345b06ee7fbdd7d777cd77b4b7e5b70efeaef26909f02cad146b8f3cb5319a7f92155c45c854cd97153bafca531eb6a318b2dc1608833fe5ea737a9cf89776d89a2ed62302f70649c0bc0ee162c43bbe50bc3a7c28f76be54702d39ede3154b9bbaccac03ca0dc36ee922a29457b7b0f55067c9294e622a41dda4813c7c0ea75b13a5734d6b8543f2a38533b631c7ee8e1eb7ae95297621651fafdd6c45374ce7c105e910d429548bf1c254d88b40704a6bddd538d14d352a93ef97b3f803b801d743217dda1be3536cad1c89fd0791707eed8486fde7f95b77b57dd146ec096bbbb94116fe31ae2c378c418e9a4f23ed70459a59514bee2b92eaa442db577de1f4790f3aff2cb8f623cd8a13f70e9cecb5fabd47bd2a45ccfd781ec301092d996b445c2157a312ecd39b13ba5d27684ca91b09a138985467b1bf9a24805cad6bbd2df801ba236eaae8818cdea52d6f788344ed3fb8ea992b252e3f7f1c577d77f4ee3ad6fc077077e8cc362953073294fccc14a7ebe45bdb7b47c18a9ba0269b84080569fd34de8d5bb40bf7c85e5fb6e29e14c06f0685a1d1fe1fc0b5f4326ab3e5f948d65355b33ed5f3a1cd1d4ae1e292f74ceff6ef341cb92e7952a86b55b849fe05a7ce9826189f87cfbd2923c545c02b83906bbe2d579018909ee6c3b2bf0652f115a7bec58723c7fc5f2c84507ca543dcca62bbf289dd4fe98e973e7eb93c95da18a2e00beb9848e87be1f71bf22b1b439e1380c9a3bfb788e9adf30e5c21fd6cabd7424933ad4e600a0d91b57227e2343b67511d05bd94129c2314701b62185b92f11ab2fc26fe5e489b3d68793a5e60c6b6739a5a598f6c242c5fc378fca6842bc802d4fc9d5c4436df2844264f8943a21a1c94b1e49198186bf3b4eacbcf8a7e6cd08dbd83b8afb57920f41b6e1163065faa52f4f1c2f1f6b2d403f3bb2ac57dcf5abbc216fcd373f581ca1e3f9a539e831288ee6ca81d5145f903532d18af10b7c7259488508ade5ca56c67bf2a6f01b57d10baee8c22c9fba95bd68f95ee66cc4d1b167d68948d2705b22bf79ff889938af76d7d8950d15cbab51775a6fcd7b5ba170a7311803b6b3e58b1d0a51674d3c821a84d488e115d2697a6384a5f06c89e27d304eb384bb4d967580ef6a64d551ff4a3da452db42992de803e812f4e16ce38b895600bfabeb923853e2875bceb60a97c9a3e6fc1df6022a9605160b4b143086e4cd3bb7789cb0b40aa527ef3f980f84187e5a3c770b3a7726381843632e1d4a37e3c5ab2cf243d3638099e59ec1171ff65ec48eacda48ddb1e87db6566034d9a78a50390a8f717e6796e4f912c8745ab34c6de91f57cd69a85a7fa683ac4e8e2a8f2422735479b2bb395c7683345f5a21538616772ef9ee07d9f9ed2b5f759becdc4150d54c4302265a5a890280249f209a535eb6aa9dc85de54ba34867f4e431b1baf33f5eea39404a4b60309389fbee45f2b0a13b1b4311012f8c8f157d2c6536d2094e55ef01a39616e3f424a4b838ed8b565a6c7585d55f3fb51703a360a1b6f3c91c1a2292ffad745a11d9d4309689aa66b187c4130fedbef6119863cba64a6c18315f6099c9fe035ecfec706bf654a6d56f2e1f68e53bb65441a4417017114354cb959d7beccc20ac9fd90cef31008f83cd8db3c3037c6f766db99260463df71a91547e0a07db2225ec8ec1bfec79d202d2175052560fa702e36f90b403115c927b7c699d021cd2e96c343ab57b77d2f15d21c8f5bb2a74011b52487b38c907263bfcee80eab0bda99fcef3423aef2dffb673efab9b4c5b400e0766c1ae6b9e994a4934f9c42f52c9fa726c2747911bc321c9aa51d0a7839820e4927daef43b787170ea8b5ccf402d4e712ed9a05a85802c2e00d75b66a5fed8f867d19b0d8a5ff9b16630880ebbdf65040239fc62303f8f7ffe114efb3386c78ac01609c619b09f3e523654f3a26ae67fc9c5bb337fc82215861e59c2f5ce23bc6a822eafcab42fb03ebe0243c212233c5143d1a195ca8cbd5b4c0f16035c77d0f18031ee937e207a4ddb0e53d4568666898469d10b1f23747a9011b6a5c5678e88fc348cd3c2c65b56581e68257b2196a536ba6e5eafb60392f57f069e47631439fb38cf2ebdc3040f2955a860fadcb4e0e66ec821476a058b4f8a7a01d590bec74ca42219f5b2a1c741808dd8febb36f35b1791621c144565b836946587b74fb2682a301b329ca5a5f9a5b9655d414633411ff75c05a35b6f94f4be9e3a6c56b09e12c04325cad55a073b632f7bdefd62c58d37ee7a455e2a85ae0a5cf75cdbe6e53026940f70e5f79a5f6624db239fadd54dabe070b0702eef0f3226d0485761c95f544c51c0ab82472b2ec0ef2afeaa064540a4ca4d97f340dd0155c3c73ef0110ea70d446eb64f2745bb589de4fcc3a1890a7683523c10e1a85211c68bb8d80bc59f574d8104fe419bde21f6c3f4339abead0ed210b7b9c199d710bd535c4a564967bdf64291e3e826607f0225376efe9028f6b807287d12e979648ea9d1a7f747d87367242363ab1192925cafd6b2d8dfdc1ee9092ce9b27c6a398c54667cf8b93aaa61fa8e4921d08cd664628fee0d55546b16eaaea51239cc3639ca9fbab64b1b1885f2aa3bb3fe06a4cbd87280ffd56b26e6e4aac6bae71cd0f6d5aeb1d61f73b5a5eb872227bbf33b1fe069679d6f859444b259b6bcb46ca8d525f903c814bf0bdb3815bea16dea479532

private def light (n : ℕ) : Bool :=
  if n≤176 then decide n.Prime else n.gcd 197903110431089593781523349201027948917123035651341137489024816374078433104458659211158835472420542693898110922165988275858968674058568071585243060450987108613508803599172370973670818494109816573853124770653833923665200268368491678853380911534764814405201861230320955810392309760000000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤31224) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 176 = 197903110431089593781523349201027948917123035651341137489024816374078433104458659211158835472420542693898110922165988275858968674058568071585243060450987108613508803599172370973670818494109816573853124770653833923665200268368491678853380911534764814405201861230320955810392309760000000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 176 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤31224 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 60 := by unfold smallValid; decide +kernel

private theorem sp60 : smallValid 60 61 := by unfold smallValid; decide +kernel

private theorem sp121 : smallValid 121 61 := by unfold smallValid; decide +kernel

private theorem sp182 : smallValid 182 61 := by unfold smallValid; decide +kernel

private theorem sp243 : smallValid 243 61 := by unfold smallValid; decide +kernel

private theorem sp304 : smallValid 304 61 := by unfold smallValid; decide +kernel

private theorem sp365 : smallValid 365 61 := by unfold smallValid; decide +kernel

private theorem sp426 : smallValid 426 61 := by unfold smallValid; decide +kernel

private theorem sp487 : smallValid 487 61 := by unfold smallValid; decide +kernel

private theorem sp548 : smallValid 548 61 := by unfold smallValid; decide +kernel

private theorem sp609 : smallValid 609 61 := by unfold smallValid; decide +kernel

private theorem sp670 : smallValid 670 61 := by unfold smallValid; decide +kernel

private theorem sp731 : smallValid 731 61 := by unfold smallValid; decide +kernel

private theorem sp792 : smallValid 792 61 := by unfold smallValid; decide +kernel

private theorem sp853 : smallValid 853 61 := by unfold smallValid; decide +kernel

private theorem sp914 : smallValid 914 61 := by unfold smallValid; decide +kernel

private theorem sp975 : smallValid 975 61 := by unfold smallValid; decide +kernel

private theorem sp1036 : smallValid 1036 61 := by unfold smallValid; decide +kernel

private theorem sp1097 : smallValid 1097 61 := by unfold smallValid; decide +kernel

private theorem sp1158 : smallValid 1158 61 := by unfold smallValid; decide +kernel

private theorem sp1219 : smallValid 1219 61 := by unfold smallValid; decide +kernel

private theorem sp1280 : smallValid 1280 61 := by unfold smallValid; decide +kernel

private theorem sp1341 : smallValid 1341 61 := by unfold smallValid; decide +kernel

private theorem sp1402 : smallValid 1402 61 := by unfold smallValid; decide +kernel

private theorem sp1463 : smallValid 1463 61 := by unfold smallValid; decide +kernel

private theorem sp1524 : smallValid 1524 61 := by unfold smallValid; decide +kernel

private theorem sp1585 : smallValid 1585 61 := by unfold smallValid; decide +kernel

private theorem sp1646 : smallValid 1646 61 := by unfold smallValid; decide +kernel

private theorem sp1707 : smallValid 1707 61 := by unfold smallValid; decide +kernel

private theorem sp1768 : smallValid 1768 61 := by unfold smallValid; decide +kernel

private theorem sp1829 : smallValid 1829 61 := by unfold smallValid; decide +kernel

private theorem sp1890 : smallValid 1890 61 := by unfold smallValid; decide +kernel

private theorem sp1951 : smallValid 1951 61 := by unfold smallValid; decide +kernel

private theorem sp2012 : smallValid 2012 61 := by unfold smallValid; decide +kernel

private theorem sp2073 : smallValid 2073 61 := by unfold smallValid; decide +kernel

private theorem sp2134 : smallValid 2134 61 := by unfold smallValid; decide +kernel

private theorem sp2195 : smallValid 2195 61 := by unfold smallValid; decide +kernel

private theorem sp2256 : smallValid 2256 61 := by unfold smallValid; decide +kernel

private theorem sp2317 : smallValid 2317 61 := by unfold smallValid; decide +kernel

private theorem sp2378 : smallValid 2378 61 := by unfold smallValid; decide +kernel

private theorem sp2439 : smallValid 2439 61 := by unfold smallValid; decide +kernel

private theorem sp2500 : smallValid 2500 61 := by unfold smallValid; decide +kernel

private theorem sp2561 : smallValid 2561 61 := by unfold smallValid; decide +kernel

private theorem sp2622 : smallValid 2622 61 := by unfold smallValid; decide +kernel

private theorem sp2683 : smallValid 2683 61 := by unfold smallValid; decide +kernel

private theorem sp2744 : smallValid 2744 61 := by unfold smallValid; decide +kernel

private theorem sp2805 : smallValid 2805 61 := by unfold smallValid; decide +kernel

private theorem sp2866 : smallValid 2866 61 := by unfold smallValid; decide +kernel

private theorem sp2927 : smallValid 2927 61 := by unfold smallValid; decide +kernel

private theorem sp2988 : smallValid 2988 61 := by unfold smallValid; decide +kernel

private theorem sp3049 : smallValid 3049 61 := by unfold smallValid; decide +kernel

private theorem sp3110 : smallValid 3110 61 := by unfold smallValid; decide +kernel

private theorem sp3171 : smallValid 3171 61 := by unfold smallValid; decide +kernel

private theorem sp3232 : smallValid 3232 61 := by unfold smallValid; decide +kernel

private theorem sp3293 : smallValid 3293 61 := by unfold smallValid; decide +kernel

private theorem sp3354 : smallValid 3354 61 := by unfold smallValid; decide +kernel

private theorem sp3415 : smallValid 3415 61 := by unfold smallValid; decide +kernel

private theorem sp3476 : smallValid 3476 61 := by unfold smallValid; decide +kernel

private theorem sp3537 : smallValid 3537 61 := by unfold smallValid; decide +kernel

private theorem sp3598 : smallValid 3598 61 := by unfold smallValid; decide +kernel

private theorem sp3659 : smallValid 3659 61 := by unfold smallValid; decide +kernel

private theorem sp3720 : smallValid 3720 61 := by unfold smallValid; decide +kernel

private theorem sp3781 : smallValid 3781 61 := by unfold smallValid; decide +kernel

private theorem sp3842 : smallValid 3842 61 := by unfold smallValid; decide +kernel

private theorem sp3903 : smallValid 3903 60 := by unfold smallValid; decide +kernel

private theorem sp3963 : smallValid 3963 61 := by unfold smallValid; decide +kernel

private theorem sp4024 : smallValid 4024 61 := by unfold smallValid; decide +kernel

private theorem sp4085 : smallValid 4085 61 := by unfold smallValid; decide +kernel

private theorem sp4146 : smallValid 4146 61 := by unfold smallValid; decide +kernel

private theorem sp4207 : smallValid 4207 61 := by unfold smallValid; decide +kernel

private theorem sp4268 : smallValid 4268 61 := by unfold smallValid; decide +kernel

private theorem sp4329 : smallValid 4329 61 := by unfold smallValid; decide +kernel

private theorem sp4390 : smallValid 4390 61 := by unfold smallValid; decide +kernel

private theorem sp4451 : smallValid 4451 61 := by unfold smallValid; decide +kernel

private theorem sp4512 : smallValid 4512 61 := by unfold smallValid; decide +kernel

private theorem sp4573 : smallValid 4573 61 := by unfold smallValid; decide +kernel

private theorem sp4634 : smallValid 4634 61 := by unfold smallValid; decide +kernel

private theorem sp4695 : smallValid 4695 61 := by unfold smallValid; decide +kernel

private theorem sp4756 : smallValid 4756 61 := by unfold smallValid; decide +kernel

private theorem sp4817 : smallValid 4817 61 := by unfold smallValid; decide +kernel

private theorem sp4878 : smallValid 4878 61 := by unfold smallValid; decide +kernel

private theorem sp4939 : smallValid 4939 61 := by unfold smallValid; decide +kernel

private theorem sp5000 : smallValid 5000 61 := by unfold smallValid; decide +kernel

private theorem sp5061 : smallValid 5061 61 := by unfold smallValid; decide +kernel

private theorem sp5122 : smallValid 5122 61 := by unfold smallValid; decide +kernel

private theorem sp5183 : smallValid 5183 61 := by unfold smallValid; decide +kernel

private theorem sp5244 : smallValid 5244 61 := by unfold smallValid; decide +kernel

private theorem sp5305 : smallValid 5305 61 := by unfold smallValid; decide +kernel

private theorem sp5366 : smallValid 5366 61 := by unfold smallValid; decide +kernel

private theorem sp5427 : smallValid 5427 61 := by unfold smallValid; decide +kernel

private theorem sp5488 : smallValid 5488 61 := by unfold smallValid; decide +kernel

private theorem sp5549 : smallValid 5549 61 := by unfold smallValid; decide +kernel

private theorem sp5610 : smallValid 5610 61 := by unfold smallValid; decide +kernel

private theorem sp5671 : smallValid 5671 61 := by unfold smallValid; decide +kernel

private theorem sp5732 : smallValid 5732 61 := by unfold smallValid; decide +kernel

private theorem sp5793 : smallValid 5793 61 := by unfold smallValid; decide +kernel

private theorem sp5854 : smallValid 5854 61 := by unfold smallValid; decide +kernel

private theorem sp5915 : smallValid 5915 61 := by unfold smallValid; decide +kernel

private theorem sp5976 : smallValid 5976 61 := by unfold smallValid; decide +kernel

private theorem sp6037 : smallValid 6037 61 := by unfold smallValid; decide +kernel

private theorem sp6098 : smallValid 6098 61 := by unfold smallValid; decide +kernel

private theorem sp6159 : smallValid 6159 61 := by unfold smallValid; decide +kernel

private theorem sp6220 : smallValid 6220 61 := by unfold smallValid; decide +kernel

private theorem sp6281 : smallValid 6281 61 := by unfold smallValid; decide +kernel

private theorem sp6342 : smallValid 6342 61 := by unfold smallValid; decide +kernel

private theorem sp6403 : smallValid 6403 61 := by unfold smallValid; decide +kernel

private theorem sp6464 : smallValid 6464 61 := by unfold smallValid; decide +kernel

private theorem sp6525 : smallValid 6525 61 := by unfold smallValid; decide +kernel

private theorem sp6586 : smallValid 6586 61 := by unfold smallValid; decide +kernel

private theorem sp6647 : smallValid 6647 61 := by unfold smallValid; decide +kernel

private theorem sp6708 : smallValid 6708 61 := by unfold smallValid; decide +kernel

private theorem sp6769 : smallValid 6769 61 := by unfold smallValid; decide +kernel

private theorem sp6830 : smallValid 6830 61 := by unfold smallValid; decide +kernel

private theorem sp6891 : smallValid 6891 61 := by unfold smallValid; decide +kernel

private theorem sp6952 : smallValid 6952 61 := by unfold smallValid; decide +kernel

private theorem sp7013 : smallValid 7013 61 := by unfold smallValid; decide +kernel

private theorem sp7074 : smallValid 7074 61 := by unfold smallValid; decide +kernel

private theorem sp7135 : smallValid 7135 61 := by unfold smallValid; decide +kernel

private theorem sp7196 : smallValid 7196 61 := by unfold smallValid; decide +kernel

private theorem sp7257 : smallValid 7257 61 := by unfold smallValid; decide +kernel

private theorem sp7318 : smallValid 7318 61 := by unfold smallValid; decide +kernel

private theorem sp7379 : smallValid 7379 61 := by unfold smallValid; decide +kernel

private theorem sp7440 : smallValid 7440 61 := by unfold smallValid; decide +kernel

private theorem sp7501 : smallValid 7501 61 := by unfold smallValid; decide +kernel

private theorem sp7562 : smallValid 7562 61 := by unfold smallValid; decide +kernel

private theorem sp7623 : smallValid 7623 61 := by unfold smallValid; decide +kernel

private theorem sp7684 : smallValid 7684 61 := by unfold smallValid; decide +kernel

private theorem sp7745 : smallValid 7745 61 := by unfold smallValid; decide +kernel

private theorem sp7806 : smallValid 7806 60 := by unfold smallValid; decide +kernel

private theorem sp7866 : smallValid 7866 61 := by unfold smallValid; decide +kernel

private theorem sp7927 : smallValid 7927 61 := by unfold smallValid; decide +kernel

private theorem sp7988 : smallValid 7988 61 := by unfold smallValid; decide +kernel

private theorem sp8049 : smallValid 8049 61 := by unfold smallValid; decide +kernel

private theorem sp8110 : smallValid 8110 61 := by unfold smallValid; decide +kernel

private theorem sp8171 : smallValid 8171 61 := by unfold smallValid; decide +kernel

private theorem sp8232 : smallValid 8232 61 := by unfold smallValid; decide +kernel

private theorem sp8293 : smallValid 8293 61 := by unfold smallValid; decide +kernel

private theorem sp8354 : smallValid 8354 61 := by unfold smallValid; decide +kernel

private theorem sp8415 : smallValid 8415 61 := by unfold smallValid; decide +kernel

private theorem sp8476 : smallValid 8476 61 := by unfold smallValid; decide +kernel

private theorem sp8537 : smallValid 8537 61 := by unfold smallValid; decide +kernel

private theorem sp8598 : smallValid 8598 61 := by unfold smallValid; decide +kernel

private theorem sp8659 : smallValid 8659 61 := by unfold smallValid; decide +kernel

private theorem sp8720 : smallValid 8720 61 := by unfold smallValid; decide +kernel

private theorem sp8781 : smallValid 8781 61 := by unfold smallValid; decide +kernel

private theorem sp8842 : smallValid 8842 61 := by unfold smallValid; decide +kernel

private theorem sp8903 : smallValid 8903 61 := by unfold smallValid; decide +kernel

private theorem sp8964 : smallValid 8964 61 := by unfold smallValid; decide +kernel

private theorem sp9025 : smallValid 9025 61 := by unfold smallValid; decide +kernel

private theorem sp9086 : smallValid 9086 61 := by unfold smallValid; decide +kernel

private theorem sp9147 : smallValid 9147 61 := by unfold smallValid; decide +kernel

private theorem sp9208 : smallValid 9208 61 := by unfold smallValid; decide +kernel

private theorem sp9269 : smallValid 9269 61 := by unfold smallValid; decide +kernel

private theorem sp9330 : smallValid 9330 61 := by unfold smallValid; decide +kernel

private theorem sp9391 : smallValid 9391 61 := by unfold smallValid; decide +kernel

private theorem sp9452 : smallValid 9452 61 := by unfold smallValid; decide +kernel

private theorem sp9513 : smallValid 9513 61 := by unfold smallValid; decide +kernel

private theorem sp9574 : smallValid 9574 61 := by unfold smallValid; decide +kernel

private theorem sp9635 : smallValid 9635 61 := by unfold smallValid; decide +kernel

private theorem sp9696 : smallValid 9696 61 := by unfold smallValid; decide +kernel

private theorem sp9757 : smallValid 9757 61 := by unfold smallValid; decide +kernel

private theorem sp9818 : smallValid 9818 61 := by unfold smallValid; decide +kernel

private theorem sp9879 : smallValid 9879 61 := by unfold smallValid; decide +kernel

private theorem sp9940 : smallValid 9940 61 := by unfold smallValid; decide +kernel

private theorem sp10001 : smallValid 10001 61 := by unfold smallValid; decide +kernel

private theorem sp10062 : smallValid 10062 61 := by unfold smallValid; decide +kernel

private theorem sp10123 : smallValid 10123 61 := by unfold smallValid; decide +kernel

private theorem sp10184 : smallValid 10184 61 := by unfold smallValid; decide +kernel

private theorem sp10245 : smallValid 10245 61 := by unfold smallValid; decide +kernel

private theorem sp10306 : smallValid 10306 61 := by unfold smallValid; decide +kernel

private theorem sp10367 : smallValid 10367 61 := by unfold smallValid; decide +kernel

private theorem sp10428 : smallValid 10428 61 := by unfold smallValid; decide +kernel

private theorem sp10489 : smallValid 10489 61 := by unfold smallValid; decide +kernel

private theorem sp10550 : smallValid 10550 61 := by unfold smallValid; decide +kernel

private theorem sp10611 : smallValid 10611 61 := by unfold smallValid; decide +kernel

private theorem sp10672 : smallValid 10672 61 := by unfold smallValid; decide +kernel

private theorem sp10733 : smallValid 10733 61 := by unfold smallValid; decide +kernel

private theorem sp10794 : smallValid 10794 61 := by unfold smallValid; decide +kernel

private theorem sp10855 : smallValid 10855 61 := by unfold smallValid; decide +kernel

private theorem sp10916 : smallValid 10916 61 := by unfold smallValid; decide +kernel

private theorem sp10977 : smallValid 10977 61 := by unfold smallValid; decide +kernel

private theorem sp11038 : smallValid 11038 61 := by unfold smallValid; decide +kernel

private theorem sp11099 : smallValid 11099 61 := by unfold smallValid; decide +kernel

private theorem sp11160 : smallValid 11160 61 := by unfold smallValid; decide +kernel

private theorem sp11221 : smallValid 11221 61 := by unfold smallValid; decide +kernel

private theorem sp11282 : smallValid 11282 61 := by unfold smallValid; decide +kernel

private theorem sp11343 : smallValid 11343 61 := by unfold smallValid; decide +kernel

private theorem sp11404 : smallValid 11404 61 := by unfold smallValid; decide +kernel

private theorem sp11465 : smallValid 11465 61 := by unfold smallValid; decide +kernel

private theorem sp11526 : smallValid 11526 61 := by unfold smallValid; decide +kernel

private theorem sp11587 : smallValid 11587 61 := by unfold smallValid; decide +kernel

private theorem sp11648 : smallValid 11648 61 := by unfold smallValid; decide +kernel

private theorem sp11709 : smallValid 11709 60 := by unfold smallValid; decide +kernel

private theorem sp11769 : smallValid 11769 61 := by unfold smallValid; decide +kernel

private theorem sp11830 : smallValid 11830 61 := by unfold smallValid; decide +kernel

private theorem sp11891 : smallValid 11891 61 := by unfold smallValid; decide +kernel

private theorem sp11952 : smallValid 11952 61 := by unfold smallValid; decide +kernel

private theorem sp12013 : smallValid 12013 61 := by unfold smallValid; decide +kernel

private theorem sp12074 : smallValid 12074 61 := by unfold smallValid; decide +kernel

private theorem sp12135 : smallValid 12135 61 := by unfold smallValid; decide +kernel

private theorem sp12196 : smallValid 12196 61 := by unfold smallValid; decide +kernel

private theorem sp12257 : smallValid 12257 61 := by unfold smallValid; decide +kernel

private theorem sp12318 : smallValid 12318 61 := by unfold smallValid; decide +kernel

private theorem sp12379 : smallValid 12379 61 := by unfold smallValid; decide +kernel

private theorem sp12440 : smallValid 12440 61 := by unfold smallValid; decide +kernel

private theorem sp12501 : smallValid 12501 61 := by unfold smallValid; decide +kernel

private theorem sp12562 : smallValid 12562 61 := by unfold smallValid; decide +kernel

private theorem sp12623 : smallValid 12623 61 := by unfold smallValid; decide +kernel

private theorem sp12684 : smallValid 12684 61 := by unfold smallValid; decide +kernel

private theorem sp12745 : smallValid 12745 61 := by unfold smallValid; decide +kernel

private theorem sp12806 : smallValid 12806 61 := by unfold smallValid; decide +kernel

private theorem sp12867 : smallValid 12867 61 := by unfold smallValid; decide +kernel

private theorem sp12928 : smallValid 12928 61 := by unfold smallValid; decide +kernel

private theorem sp12989 : smallValid 12989 61 := by unfold smallValid; decide +kernel

private theorem sp13050 : smallValid 13050 61 := by unfold smallValid; decide +kernel

private theorem sp13111 : smallValid 13111 61 := by unfold smallValid; decide +kernel

private theorem sp13172 : smallValid 13172 61 := by unfold smallValid; decide +kernel

private theorem sp13233 : smallValid 13233 61 := by unfold smallValid; decide +kernel

private theorem sp13294 : smallValid 13294 61 := by unfold smallValid; decide +kernel

private theorem sp13355 : smallValid 13355 61 := by unfold smallValid; decide +kernel

private theorem sp13416 : smallValid 13416 61 := by unfold smallValid; decide +kernel

private theorem sp13477 : smallValid 13477 61 := by unfold smallValid; decide +kernel

private theorem sp13538 : smallValid 13538 61 := by unfold smallValid; decide +kernel

private theorem sp13599 : smallValid 13599 61 := by unfold smallValid; decide +kernel

private theorem sp13660 : smallValid 13660 61 := by unfold smallValid; decide +kernel

private theorem sp13721 : smallValid 13721 61 := by unfold smallValid; decide +kernel

private theorem sp13782 : smallValid 13782 61 := by unfold smallValid; decide +kernel

private theorem sp13843 : smallValid 13843 61 := by unfold smallValid; decide +kernel

private theorem sp13904 : smallValid 13904 61 := by unfold smallValid; decide +kernel

private theorem sp13965 : smallValid 13965 61 := by unfold smallValid; decide +kernel

private theorem sp14026 : smallValid 14026 61 := by unfold smallValid; decide +kernel

private theorem sp14087 : smallValid 14087 61 := by unfold smallValid; decide +kernel

private theorem sp14148 : smallValid 14148 61 := by unfold smallValid; decide +kernel

private theorem sp14209 : smallValid 14209 61 := by unfold smallValid; decide +kernel

private theorem sp14270 : smallValid 14270 61 := by unfold smallValid; decide +kernel

private theorem sp14331 : smallValid 14331 61 := by unfold smallValid; decide +kernel

private theorem sp14392 : smallValid 14392 61 := by unfold smallValid; decide +kernel

private theorem sp14453 : smallValid 14453 61 := by unfold smallValid; decide +kernel

private theorem sp14514 : smallValid 14514 61 := by unfold smallValid; decide +kernel

private theorem sp14575 : smallValid 14575 61 := by unfold smallValid; decide +kernel

private theorem sp14636 : smallValid 14636 61 := by unfold smallValid; decide +kernel

private theorem sp14697 : smallValid 14697 61 := by unfold smallValid; decide +kernel

private theorem sp14758 : smallValid 14758 61 := by unfold smallValid; decide +kernel

private theorem sp14819 : smallValid 14819 61 := by unfold smallValid; decide +kernel

private theorem sp14880 : smallValid 14880 61 := by unfold smallValid; decide +kernel

private theorem sp14941 : smallValid 14941 61 := by unfold smallValid; decide +kernel

private theorem sp15002 : smallValid 15002 61 := by unfold smallValid; decide +kernel

private theorem sp15063 : smallValid 15063 61 := by unfold smallValid; decide +kernel

private theorem sp15124 : smallValid 15124 61 := by unfold smallValid; decide +kernel

private theorem sp15185 : smallValid 15185 61 := by unfold smallValid; decide +kernel

private theorem sp15246 : smallValid 15246 61 := by unfold smallValid; decide +kernel

private theorem sp15307 : smallValid 15307 61 := by unfold smallValid; decide +kernel

private theorem sp15368 : smallValid 15368 61 := by unfold smallValid; decide +kernel

private theorem sp15429 : smallValid 15429 61 := by unfold smallValid; decide +kernel

private theorem sp15490 : smallValid 15490 61 := by unfold smallValid; decide +kernel

private theorem sp15551 : smallValid 15551 61 := by unfold smallValid; decide +kernel

private theorem sp15612 : smallValid 15612 60 := by unfold smallValid; decide +kernel

private theorem sp15672 : smallValid 15672 61 := by unfold smallValid; decide +kernel

private theorem sp15733 : smallValid 15733 61 := by unfold smallValid; decide +kernel

private theorem sp15794 : smallValid 15794 61 := by unfold smallValid; decide +kernel

private theorem sp15855 : smallValid 15855 61 := by unfold smallValid; decide +kernel

private theorem sp15916 : smallValid 15916 61 := by unfold smallValid; decide +kernel

private theorem sp15977 : smallValid 15977 61 := by unfold smallValid; decide +kernel

private theorem sp16038 : smallValid 16038 61 := by unfold smallValid; decide +kernel

private theorem sp16099 : smallValid 16099 61 := by unfold smallValid; decide +kernel

private theorem sp16160 : smallValid 16160 61 := by unfold smallValid; decide +kernel

private theorem sp16221 : smallValid 16221 61 := by unfold smallValid; decide +kernel

private theorem sp16282 : smallValid 16282 61 := by unfold smallValid; decide +kernel

private theorem sp16343 : smallValid 16343 61 := by unfold smallValid; decide +kernel

private theorem sp16404 : smallValid 16404 61 := by unfold smallValid; decide +kernel

private theorem sp16465 : smallValid 16465 61 := by unfold smallValid; decide +kernel

private theorem sp16526 : smallValid 16526 61 := by unfold smallValid; decide +kernel

private theorem sp16587 : smallValid 16587 61 := by unfold smallValid; decide +kernel

private theorem sp16648 : smallValid 16648 61 := by unfold smallValid; decide +kernel

private theorem sp16709 : smallValid 16709 61 := by unfold smallValid; decide +kernel

private theorem sp16770 : smallValid 16770 61 := by unfold smallValid; decide +kernel

private theorem sp16831 : smallValid 16831 61 := by unfold smallValid; decide +kernel

private theorem sp16892 : smallValid 16892 61 := by unfold smallValid; decide +kernel

private theorem sp16953 : smallValid 16953 61 := by unfold smallValid; decide +kernel

private theorem sp17014 : smallValid 17014 61 := by unfold smallValid; decide +kernel

private theorem sp17075 : smallValid 17075 61 := by unfold smallValid; decide +kernel

private theorem sp17136 : smallValid 17136 61 := by unfold smallValid; decide +kernel

private theorem sp17197 : smallValid 17197 61 := by unfold smallValid; decide +kernel

private theorem sp17258 : smallValid 17258 61 := by unfold smallValid; decide +kernel

private theorem sp17319 : smallValid 17319 61 := by unfold smallValid; decide +kernel

private theorem sp17380 : smallValid 17380 61 := by unfold smallValid; decide +kernel

private theorem sp17441 : smallValid 17441 61 := by unfold smallValid; decide +kernel

private theorem sp17502 : smallValid 17502 61 := by unfold smallValid; decide +kernel

private theorem sp17563 : smallValid 17563 61 := by unfold smallValid; decide +kernel

private theorem sp17624 : smallValid 17624 61 := by unfold smallValid; decide +kernel

private theorem sp17685 : smallValid 17685 61 := by unfold smallValid; decide +kernel

private theorem sp17746 : smallValid 17746 61 := by unfold smallValid; decide +kernel

private theorem sp17807 : smallValid 17807 61 := by unfold smallValid; decide +kernel

private theorem sp17868 : smallValid 17868 61 := by unfold smallValid; decide +kernel

private theorem sp17929 : smallValid 17929 61 := by unfold smallValid; decide +kernel

private theorem sp17990 : smallValid 17990 61 := by unfold smallValid; decide +kernel

private theorem sp18051 : smallValid 18051 61 := by unfold smallValid; decide +kernel

private theorem sp18112 : smallValid 18112 61 := by unfold smallValid; decide +kernel

private theorem sp18173 : smallValid 18173 61 := by unfold smallValid; decide +kernel

private theorem sp18234 : smallValid 18234 61 := by unfold smallValid; decide +kernel

private theorem sp18295 : smallValid 18295 61 := by unfold smallValid; decide +kernel

private theorem sp18356 : smallValid 18356 61 := by unfold smallValid; decide +kernel

private theorem sp18417 : smallValid 18417 61 := by unfold smallValid; decide +kernel

private theorem sp18478 : smallValid 18478 61 := by unfold smallValid; decide +kernel

private theorem sp18539 : smallValid 18539 61 := by unfold smallValid; decide +kernel

private theorem sp18600 : smallValid 18600 61 := by unfold smallValid; decide +kernel

private theorem sp18661 : smallValid 18661 61 := by unfold smallValid; decide +kernel

private theorem sp18722 : smallValid 18722 61 := by unfold smallValid; decide +kernel

private theorem sp18783 : smallValid 18783 61 := by unfold smallValid; decide +kernel

private theorem sp18844 : smallValid 18844 61 := by unfold smallValid; decide +kernel

private theorem sp18905 : smallValid 18905 61 := by unfold smallValid; decide +kernel

private theorem sp18966 : smallValid 18966 61 := by unfold smallValid; decide +kernel

private theorem sp19027 : smallValid 19027 61 := by unfold smallValid; decide +kernel

private theorem sp19088 : smallValid 19088 61 := by unfold smallValid; decide +kernel

private theorem sp19149 : smallValid 19149 61 := by unfold smallValid; decide +kernel

private theorem sp19210 : smallValid 19210 61 := by unfold smallValid; decide +kernel

private theorem sp19271 : smallValid 19271 61 := by unfold smallValid; decide +kernel

private theorem sp19332 : smallValid 19332 61 := by unfold smallValid; decide +kernel

private theorem sp19393 : smallValid 19393 61 := by unfold smallValid; decide +kernel

private theorem sp19454 : smallValid 19454 61 := by unfold smallValid; decide +kernel

private theorem sp19515 : smallValid 19515 60 := by unfold smallValid; decide +kernel

private theorem sp19575 : smallValid 19575 61 := by unfold smallValid; decide +kernel

private theorem sp19636 : smallValid 19636 61 := by unfold smallValid; decide +kernel

private theorem sp19697 : smallValid 19697 61 := by unfold smallValid; decide +kernel

private theorem sp19758 : smallValid 19758 61 := by unfold smallValid; decide +kernel

private theorem sp19819 : smallValid 19819 61 := by unfold smallValid; decide +kernel

private theorem sp19880 : smallValid 19880 61 := by unfold smallValid; decide +kernel

private theorem sp19941 : smallValid 19941 61 := by unfold smallValid; decide +kernel

private theorem sp20002 : smallValid 20002 61 := by unfold smallValid; decide +kernel

private theorem sp20063 : smallValid 20063 61 := by unfold smallValid; decide +kernel

private theorem sp20124 : smallValid 20124 61 := by unfold smallValid; decide +kernel

private theorem sp20185 : smallValid 20185 61 := by unfold smallValid; decide +kernel

private theorem sp20246 : smallValid 20246 61 := by unfold smallValid; decide +kernel

private theorem sp20307 : smallValid 20307 61 := by unfold smallValid; decide +kernel

private theorem sp20368 : smallValid 20368 61 := by unfold smallValid; decide +kernel

private theorem sp20429 : smallValid 20429 61 := by unfold smallValid; decide +kernel

private theorem sp20490 : smallValid 20490 61 := by unfold smallValid; decide +kernel

private theorem sp20551 : smallValid 20551 61 := by unfold smallValid; decide +kernel

private theorem sp20612 : smallValid 20612 61 := by unfold smallValid; decide +kernel

private theorem sp20673 : smallValid 20673 61 := by unfold smallValid; decide +kernel

private theorem sp20734 : smallValid 20734 61 := by unfold smallValid; decide +kernel

private theorem sp20795 : smallValid 20795 61 := by unfold smallValid; decide +kernel

private theorem sp20856 : smallValid 20856 61 := by unfold smallValid; decide +kernel

private theorem sp20917 : smallValid 20917 61 := by unfold smallValid; decide +kernel

private theorem sp20978 : smallValid 20978 61 := by unfold smallValid; decide +kernel

private theorem sp21039 : smallValid 21039 61 := by unfold smallValid; decide +kernel

private theorem sp21100 : smallValid 21100 61 := by unfold smallValid; decide +kernel

private theorem sp21161 : smallValid 21161 61 := by unfold smallValid; decide +kernel

private theorem sp21222 : smallValid 21222 61 := by unfold smallValid; decide +kernel

private theorem sp21283 : smallValid 21283 61 := by unfold smallValid; decide +kernel

private theorem sp21344 : smallValid 21344 61 := by unfold smallValid; decide +kernel

private theorem sp21405 : smallValid 21405 61 := by unfold smallValid; decide +kernel

private theorem sp21466 : smallValid 21466 61 := by unfold smallValid; decide +kernel

private theorem sp21527 : smallValid 21527 61 := by unfold smallValid; decide +kernel

private theorem sp21588 : smallValid 21588 61 := by unfold smallValid; decide +kernel

private theorem sp21649 : smallValid 21649 61 := by unfold smallValid; decide +kernel

private theorem sp21710 : smallValid 21710 61 := by unfold smallValid; decide +kernel

private theorem sp21771 : smallValid 21771 61 := by unfold smallValid; decide +kernel

private theorem sp21832 : smallValid 21832 61 := by unfold smallValid; decide +kernel

private theorem sp21893 : smallValid 21893 61 := by unfold smallValid; decide +kernel

private theorem sp21954 : smallValid 21954 61 := by unfold smallValid; decide +kernel

private theorem sp22015 : smallValid 22015 61 := by unfold smallValid; decide +kernel

private theorem sp22076 : smallValid 22076 61 := by unfold smallValid; decide +kernel

private theorem sp22137 : smallValid 22137 61 := by unfold smallValid; decide +kernel

private theorem sp22198 : smallValid 22198 61 := by unfold smallValid; decide +kernel

private theorem sp22259 : smallValid 22259 61 := by unfold smallValid; decide +kernel

private theorem sp22320 : smallValid 22320 61 := by unfold smallValid; decide +kernel

private theorem sp22381 : smallValid 22381 61 := by unfold smallValid; decide +kernel

private theorem sp22442 : smallValid 22442 61 := by unfold smallValid; decide +kernel

private theorem sp22503 : smallValid 22503 61 := by unfold smallValid; decide +kernel

private theorem sp22564 : smallValid 22564 61 := by unfold smallValid; decide +kernel

private theorem sp22625 : smallValid 22625 61 := by unfold smallValid; decide +kernel

private theorem sp22686 : smallValid 22686 61 := by unfold smallValid; decide +kernel

private theorem sp22747 : smallValid 22747 61 := by unfold smallValid; decide +kernel

private theorem sp22808 : smallValid 22808 61 := by unfold smallValid; decide +kernel

private theorem sp22869 : smallValid 22869 61 := by unfold smallValid; decide +kernel

private theorem sp22930 : smallValid 22930 61 := by unfold smallValid; decide +kernel

private theorem sp22991 : smallValid 22991 61 := by unfold smallValid; decide +kernel

private theorem sp23052 : smallValid 23052 61 := by unfold smallValid; decide +kernel

private theorem sp23113 : smallValid 23113 61 := by unfold smallValid; decide +kernel

private theorem sp23174 : smallValid 23174 61 := by unfold smallValid; decide +kernel

private theorem sp23235 : smallValid 23235 61 := by unfold smallValid; decide +kernel

private theorem sp23296 : smallValid 23296 61 := by unfold smallValid; decide +kernel

private theorem sp23357 : smallValid 23357 61 := by unfold smallValid; decide +kernel

private theorem sp23418 : smallValid 23418 60 := by unfold smallValid; decide +kernel

private theorem sp23478 : smallValid 23478 61 := by unfold smallValid; decide +kernel

private theorem sp23539 : smallValid 23539 61 := by unfold smallValid; decide +kernel

private theorem sp23600 : smallValid 23600 61 := by unfold smallValid; decide +kernel

private theorem sp23661 : smallValid 23661 61 := by unfold smallValid; decide +kernel

private theorem sp23722 : smallValid 23722 61 := by unfold smallValid; decide +kernel

private theorem sp23783 : smallValid 23783 61 := by unfold smallValid; decide +kernel

private theorem sp23844 : smallValid 23844 61 := by unfold smallValid; decide +kernel

private theorem sp23905 : smallValid 23905 61 := by unfold smallValid; decide +kernel

private theorem sp23966 : smallValid 23966 61 := by unfold smallValid; decide +kernel

private theorem sp24027 : smallValid 24027 61 := by unfold smallValid; decide +kernel

private theorem sp24088 : smallValid 24088 61 := by unfold smallValid; decide +kernel

private theorem sp24149 : smallValid 24149 61 := by unfold smallValid; decide +kernel

private theorem sp24210 : smallValid 24210 61 := by unfold smallValid; decide +kernel

private theorem sp24271 : smallValid 24271 61 := by unfold smallValid; decide +kernel

private theorem sp24332 : smallValid 24332 61 := by unfold smallValid; decide +kernel

private theorem sp24393 : smallValid 24393 61 := by unfold smallValid; decide +kernel

private theorem sp24454 : smallValid 24454 61 := by unfold smallValid; decide +kernel

private theorem sp24515 : smallValid 24515 61 := by unfold smallValid; decide +kernel

private theorem sp24576 : smallValid 24576 61 := by unfold smallValid; decide +kernel

private theorem sp24637 : smallValid 24637 61 := by unfold smallValid; decide +kernel

private theorem sp24698 : smallValid 24698 61 := by unfold smallValid; decide +kernel

private theorem sp24759 : smallValid 24759 61 := by unfold smallValid; decide +kernel

private theorem sp24820 : smallValid 24820 61 := by unfold smallValid; decide +kernel

private theorem sp24881 : smallValid 24881 61 := by unfold smallValid; decide +kernel

private theorem sp24942 : smallValid 24942 61 := by unfold smallValid; decide +kernel

private theorem sp25003 : smallValid 25003 61 := by unfold smallValid; decide +kernel

private theorem sp25064 : smallValid 25064 61 := by unfold smallValid; decide +kernel

private theorem sp25125 : smallValid 25125 61 := by unfold smallValid; decide +kernel

private theorem sp25186 : smallValid 25186 61 := by unfold smallValid; decide +kernel

private theorem sp25247 : smallValid 25247 61 := by unfold smallValid; decide +kernel

private theorem sp25308 : smallValid 25308 61 := by unfold smallValid; decide +kernel

private theorem sp25369 : smallValid 25369 61 := by unfold smallValid; decide +kernel

private theorem sp25430 : smallValid 25430 61 := by unfold smallValid; decide +kernel

private theorem sp25491 : smallValid 25491 61 := by unfold smallValid; decide +kernel

private theorem sp25552 : smallValid 25552 61 := by unfold smallValid; decide +kernel

private theorem sp25613 : smallValid 25613 61 := by unfold smallValid; decide +kernel

private theorem sp25674 : smallValid 25674 61 := by unfold smallValid; decide +kernel

private theorem sp25735 : smallValid 25735 61 := by unfold smallValid; decide +kernel

private theorem sp25796 : smallValid 25796 61 := by unfold smallValid; decide +kernel

private theorem sp25857 : smallValid 25857 61 := by unfold smallValid; decide +kernel

private theorem sp25918 : smallValid 25918 61 := by unfold smallValid; decide +kernel

private theorem sp25979 : smallValid 25979 61 := by unfold smallValid; decide +kernel

private theorem sp26040 : smallValid 26040 61 := by unfold smallValid; decide +kernel

private theorem sp26101 : smallValid 26101 61 := by unfold smallValid; decide +kernel

private theorem sp26162 : smallValid 26162 61 := by unfold smallValid; decide +kernel

private theorem sp26223 : smallValid 26223 61 := by unfold smallValid; decide +kernel

private theorem sp26284 : smallValid 26284 61 := by unfold smallValid; decide +kernel

private theorem sp26345 : smallValid 26345 61 := by unfold smallValid; decide +kernel

private theorem sp26406 : smallValid 26406 61 := by unfold smallValid; decide +kernel

private theorem sp26467 : smallValid 26467 61 := by unfold smallValid; decide +kernel

private theorem sp26528 : smallValid 26528 61 := by unfold smallValid; decide +kernel

private theorem sp26589 : smallValid 26589 61 := by unfold smallValid; decide +kernel

private theorem sp26650 : smallValid 26650 61 := by unfold smallValid; decide +kernel

private theorem sp26711 : smallValid 26711 61 := by unfold smallValid; decide +kernel

private theorem sp26772 : smallValid 26772 61 := by unfold smallValid; decide +kernel

private theorem sp26833 : smallValid 26833 61 := by unfold smallValid; decide +kernel

private theorem sp26894 : smallValid 26894 61 := by unfold smallValid; decide +kernel

private theorem sp26955 : smallValid 26955 61 := by unfold smallValid; decide +kernel

private theorem sp27016 : smallValid 27016 61 := by unfold smallValid; decide +kernel

private theorem sp27077 : smallValid 27077 61 := by unfold smallValid; decide +kernel

private theorem sp27138 : smallValid 27138 61 := by unfold smallValid; decide +kernel

private theorem sp27199 : smallValid 27199 61 := by unfold smallValid; decide +kernel

private theorem sp27260 : smallValid 27260 61 := by unfold smallValid; decide +kernel

private theorem sp27321 : smallValid 27321 61 := by unfold smallValid; decide +kernel

private theorem sp27382 : smallValid 27382 61 := by unfold smallValid; decide +kernel

private theorem sp27443 : smallValid 27443 61 := by unfold smallValid; decide +kernel

private theorem sp27504 : smallValid 27504 61 := by unfold smallValid; decide +kernel

private theorem sp27565 : smallValid 27565 61 := by unfold smallValid; decide +kernel

private theorem sp27626 : smallValid 27626 61 := by unfold smallValid; decide +kernel

private theorem sp27687 : smallValid 27687 61 := by unfold smallValid; decide +kernel

private theorem sp27748 : smallValid 27748 61 := by unfold smallValid; decide +kernel

private theorem sp27809 : smallValid 27809 61 := by unfold smallValid; decide +kernel

private theorem sp27870 : smallValid 27870 61 := by unfold smallValid; decide +kernel

private theorem sp27931 : smallValid 27931 61 := by unfold smallValid; decide +kernel

private theorem sp27992 : smallValid 27992 61 := by unfold smallValid; decide +kernel

private theorem sp28053 : smallValid 28053 61 := by unfold smallValid; decide +kernel

private theorem sp28114 : smallValid 28114 61 := by unfold smallValid; decide +kernel

private theorem sp28175 : smallValid 28175 61 := by unfold smallValid; decide +kernel

private theorem sp28236 : smallValid 28236 61 := by unfold smallValid; decide +kernel

private theorem sp28297 : smallValid 28297 61 := by unfold smallValid; decide +kernel

private theorem sp28358 : smallValid 28358 61 := by unfold smallValid; decide +kernel

private theorem sp28419 : smallValid 28419 61 := by unfold smallValid; decide +kernel

private theorem sp28480 : smallValid 28480 61 := by unfold smallValid; decide +kernel

private theorem sp28541 : smallValid 28541 61 := by unfold smallValid; decide +kernel

private theorem sp28602 : smallValid 28602 61 := by unfold smallValid; decide +kernel

private theorem sp28663 : smallValid 28663 61 := by unfold smallValid; decide +kernel

private theorem sp28724 : smallValid 28724 61 := by unfold smallValid; decide +kernel

private theorem sp28785 : smallValid 28785 61 := by unfold smallValid; decide +kernel

private theorem sp28846 : smallValid 28846 61 := by unfold smallValid; decide +kernel

private theorem sp28907 : smallValid 28907 61 := by unfold smallValid; decide +kernel

private theorem sp28968 : smallValid 28968 61 := by unfold smallValid; decide +kernel

private theorem sp29029 : smallValid 29029 61 := by unfold smallValid; decide +kernel

private theorem sp29090 : smallValid 29090 61 := by unfold smallValid; decide +kernel

private theorem sp29151 : smallValid 29151 61 := by unfold smallValid; decide +kernel

private theorem sp29212 : smallValid 29212 61 := by unfold smallValid; decide +kernel

private theorem sp29273 : smallValid 29273 61 := by unfold smallValid; decide +kernel

private theorem sp29334 : smallValid 29334 61 := by unfold smallValid; decide +kernel

private theorem sp29395 : smallValid 29395 61 := by unfold smallValid; decide +kernel

private theorem sp29456 : smallValid 29456 61 := by unfold smallValid; decide +kernel

private theorem sp29517 : smallValid 29517 61 := by unfold smallValid; decide +kernel

private theorem sp29578 : smallValid 29578 61 := by unfold smallValid; decide +kernel

private theorem sp29639 : smallValid 29639 61 := by unfold smallValid; decide +kernel

private theorem sp29700 : smallValid 29700 61 := by unfold smallValid; decide +kernel

private theorem sp29761 : smallValid 29761 61 := by unfold smallValid; decide +kernel

private theorem sp29822 : smallValid 29822 61 := by unfold smallValid; decide +kernel

private theorem sp29883 : smallValid 29883 61 := by unfold smallValid; decide +kernel

private theorem sp29944 : smallValid 29944 61 := by unfold smallValid; decide +kernel

private theorem sp30005 : smallValid 30005 61 := by unfold smallValid; decide +kernel

private theorem sp30066 : smallValid 30066 61 := by unfold smallValid; decide +kernel

private theorem sp30127 : smallValid 30127 61 := by unfold smallValid; decide +kernel

private theorem sp30188 : smallValid 30188 61 := by unfold smallValid; decide +kernel

private theorem sp30249 : smallValid 30249 61 := by unfold smallValid; decide +kernel

private theorem sp30310 : smallValid 30310 61 := by unfold smallValid; decide +kernel

private theorem sp30371 : smallValid 30371 61 := by unfold smallValid; decide +kernel

private theorem sp30432 : smallValid 30432 61 := by unfold smallValid; decide +kernel

private theorem sp30493 : smallValid 30493 61 := by unfold smallValid; decide +kernel

private theorem sp30554 : smallValid 30554 61 := by unfold smallValid; decide +kernel

private theorem sp30615 : smallValid 30615 61 := by unfold smallValid; decide +kernel

private theorem sp30676 : smallValid 30676 61 := by unfold smallValid; decide +kernel

private theorem sp30737 : smallValid 30737 61 := by unfold smallValid; decide +kernel

private theorem sp30798 : smallValid 30798 61 := by unfold smallValid; decide +kernel

private theorem sp30859 : smallValid 30859 61 := by unfold smallValid; decide +kernel

private theorem sp30920 : smallValid 30920 61 := by unfold smallValid; decide +kernel

private theorem sp30981 : smallValid 30981 61 := by unfold smallValid; decide +kernel

private theorem sp31042 : smallValid 31042 61 := by unfold smallValid; decide +kernel

private theorem sp31103 : smallValid 31103 61 := by unfold smallValid; decide +kernel

private theorem sp31164 : smallValid 31164 61 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤31224) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 31225 := (joinSmall (lo:=0) (a:=15612) (b:=15613) (joinSmall (lo:=0) (a:=7806) (b:=7806) (joinSmall (lo:=0) (a:=3903) (b:=3903) (joinSmall (lo:=0) (a:=1951) (b:=1952) (joinSmall (lo:=0) (a:=975) (b:=976) (joinSmall (lo:=0) (a:=487) (b:=488) (joinSmall (lo:=0) (a:=243) (b:=244) (joinSmall (lo:=0) (a:=121) (b:=122) (joinSmall (lo:=0) (a:=60) (b:=61) sp0 sp60) (joinSmall (lo:=121) (a:=61) (b:=61) sp121 sp182)) (joinSmall (lo:=243) (a:=122) (b:=122) (joinSmall (lo:=243) (a:=61) (b:=61) sp243 sp304) (joinSmall (lo:=365) (a:=61) (b:=61) sp365 sp426))) (joinSmall (lo:=487) (a:=244) (b:=244) (joinSmall (lo:=487) (a:=122) (b:=122) (joinSmall (lo:=487) (a:=61) (b:=61) sp487 sp548) (joinSmall (lo:=609) (a:=61) (b:=61) sp609 sp670)) (joinSmall (lo:=731) (a:=122) (b:=122) (joinSmall (lo:=731) (a:=61) (b:=61) sp731 sp792) (joinSmall (lo:=853) (a:=61) (b:=61) sp853 sp914)))) (joinSmall (lo:=975) (a:=488) (b:=488) (joinSmall (lo:=975) (a:=244) (b:=244) (joinSmall (lo:=975) (a:=122) (b:=122) (joinSmall (lo:=975) (a:=61) (b:=61) sp975 sp1036) (joinSmall (lo:=1097) (a:=61) (b:=61) sp1097 sp1158)) (joinSmall (lo:=1219) (a:=122) (b:=122) (joinSmall (lo:=1219) (a:=61) (b:=61) sp1219 sp1280) (joinSmall (lo:=1341) (a:=61) (b:=61) sp1341 sp1402))) (joinSmall (lo:=1463) (a:=244) (b:=244) (joinSmall (lo:=1463) (a:=122) (b:=122) (joinSmall (lo:=1463) (a:=61) (b:=61) sp1463 sp1524) (joinSmall (lo:=1585) (a:=61) (b:=61) sp1585 sp1646)) (joinSmall (lo:=1707) (a:=122) (b:=122) (joinSmall (lo:=1707) (a:=61) (b:=61) sp1707 sp1768) (joinSmall (lo:=1829) (a:=61) (b:=61) sp1829 sp1890))))) (joinSmall (lo:=1951) (a:=976) (b:=976) (joinSmall (lo:=1951) (a:=488) (b:=488) (joinSmall (lo:=1951) (a:=244) (b:=244) (joinSmall (lo:=1951) (a:=122) (b:=122) (joinSmall (lo:=1951) (a:=61) (b:=61) sp1951 sp2012) (joinSmall (lo:=2073) (a:=61) (b:=61) sp2073 sp2134)) (joinSmall (lo:=2195) (a:=122) (b:=122) (joinSmall (lo:=2195) (a:=61) (b:=61) sp2195 sp2256) (joinSmall (lo:=2317) (a:=61) (b:=61) sp2317 sp2378))) (joinSmall (lo:=2439) (a:=244) (b:=244) (joinSmall (lo:=2439) (a:=122) (b:=122) (joinSmall (lo:=2439) (a:=61) (b:=61) sp2439 sp2500) (joinSmall (lo:=2561) (a:=61) (b:=61) sp2561 sp2622)) (joinSmall (lo:=2683) (a:=122) (b:=122) (joinSmall (lo:=2683) (a:=61) (b:=61) sp2683 sp2744) (joinSmall (lo:=2805) (a:=61) (b:=61) sp2805 sp2866)))) (joinSmall (lo:=2927) (a:=488) (b:=488) (joinSmall (lo:=2927) (a:=244) (b:=244) (joinSmall (lo:=2927) (a:=122) (b:=122) (joinSmall (lo:=2927) (a:=61) (b:=61) sp2927 sp2988) (joinSmall (lo:=3049) (a:=61) (b:=61) sp3049 sp3110)) (joinSmall (lo:=3171) (a:=122) (b:=122) (joinSmall (lo:=3171) (a:=61) (b:=61) sp3171 sp3232) (joinSmall (lo:=3293) (a:=61) (b:=61) sp3293 sp3354))) (joinSmall (lo:=3415) (a:=244) (b:=244) (joinSmall (lo:=3415) (a:=122) (b:=122) (joinSmall (lo:=3415) (a:=61) (b:=61) sp3415 sp3476) (joinSmall (lo:=3537) (a:=61) (b:=61) sp3537 sp3598)) (joinSmall (lo:=3659) (a:=122) (b:=122) (joinSmall (lo:=3659) (a:=61) (b:=61) sp3659 sp3720) (joinSmall (lo:=3781) (a:=61) (b:=61) sp3781 sp3842)))))) (joinSmall (lo:=3903) (a:=1951) (b:=1952) (joinSmall (lo:=3903) (a:=975) (b:=976) (joinSmall (lo:=3903) (a:=487) (b:=488) (joinSmall (lo:=3903) (a:=243) (b:=244) (joinSmall (lo:=3903) (a:=121) (b:=122) (joinSmall (lo:=3903) (a:=60) (b:=61) sp3903 sp3963) (joinSmall (lo:=4024) (a:=61) (b:=61) sp4024 sp4085)) (joinSmall (lo:=4146) (a:=122) (b:=122) (joinSmall (lo:=4146) (a:=61) (b:=61) sp4146 sp4207) (joinSmall (lo:=4268) (a:=61) (b:=61) sp4268 sp4329))) (joinSmall (lo:=4390) (a:=244) (b:=244) (joinSmall (lo:=4390) (a:=122) (b:=122) (joinSmall (lo:=4390) (a:=61) (b:=61) sp4390 sp4451) (joinSmall (lo:=4512) (a:=61) (b:=61) sp4512 sp4573)) (joinSmall (lo:=4634) (a:=122) (b:=122) (joinSmall (lo:=4634) (a:=61) (b:=61) sp4634 sp4695) (joinSmall (lo:=4756) (a:=61) (b:=61) sp4756 sp4817)))) (joinSmall (lo:=4878) (a:=488) (b:=488) (joinSmall (lo:=4878) (a:=244) (b:=244) (joinSmall (lo:=4878) (a:=122) (b:=122) (joinSmall (lo:=4878) (a:=61) (b:=61) sp4878 sp4939) (joinSmall (lo:=5000) (a:=61) (b:=61) sp5000 sp5061)) (joinSmall (lo:=5122) (a:=122) (b:=122) (joinSmall (lo:=5122) (a:=61) (b:=61) sp5122 sp5183) (joinSmall (lo:=5244) (a:=61) (b:=61) sp5244 sp5305))) (joinSmall (lo:=5366) (a:=244) (b:=244) (joinSmall (lo:=5366) (a:=122) (b:=122) (joinSmall (lo:=5366) (a:=61) (b:=61) sp5366 sp5427) (joinSmall (lo:=5488) (a:=61) (b:=61) sp5488 sp5549)) (joinSmall (lo:=5610) (a:=122) (b:=122) (joinSmall (lo:=5610) (a:=61) (b:=61) sp5610 sp5671) (joinSmall (lo:=5732) (a:=61) (b:=61) sp5732 sp5793))))) (joinSmall (lo:=5854) (a:=976) (b:=976) (joinSmall (lo:=5854) (a:=488) (b:=488) (joinSmall (lo:=5854) (a:=244) (b:=244) (joinSmall (lo:=5854) (a:=122) (b:=122) (joinSmall (lo:=5854) (a:=61) (b:=61) sp5854 sp5915) (joinSmall (lo:=5976) (a:=61) (b:=61) sp5976 sp6037)) (joinSmall (lo:=6098) (a:=122) (b:=122) (joinSmall (lo:=6098) (a:=61) (b:=61) sp6098 sp6159) (joinSmall (lo:=6220) (a:=61) (b:=61) sp6220 sp6281))) (joinSmall (lo:=6342) (a:=244) (b:=244) (joinSmall (lo:=6342) (a:=122) (b:=122) (joinSmall (lo:=6342) (a:=61) (b:=61) sp6342 sp6403) (joinSmall (lo:=6464) (a:=61) (b:=61) sp6464 sp6525)) (joinSmall (lo:=6586) (a:=122) (b:=122) (joinSmall (lo:=6586) (a:=61) (b:=61) sp6586 sp6647) (joinSmall (lo:=6708) (a:=61) (b:=61) sp6708 sp6769)))) (joinSmall (lo:=6830) (a:=488) (b:=488) (joinSmall (lo:=6830) (a:=244) (b:=244) (joinSmall (lo:=6830) (a:=122) (b:=122) (joinSmall (lo:=6830) (a:=61) (b:=61) sp6830 sp6891) (joinSmall (lo:=6952) (a:=61) (b:=61) sp6952 sp7013)) (joinSmall (lo:=7074) (a:=122) (b:=122) (joinSmall (lo:=7074) (a:=61) (b:=61) sp7074 sp7135) (joinSmall (lo:=7196) (a:=61) (b:=61) sp7196 sp7257))) (joinSmall (lo:=7318) (a:=244) (b:=244) (joinSmall (lo:=7318) (a:=122) (b:=122) (joinSmall (lo:=7318) (a:=61) (b:=61) sp7318 sp7379) (joinSmall (lo:=7440) (a:=61) (b:=61) sp7440 sp7501)) (joinSmall (lo:=7562) (a:=122) (b:=122) (joinSmall (lo:=7562) (a:=61) (b:=61) sp7562 sp7623) (joinSmall (lo:=7684) (a:=61) (b:=61) sp7684 sp7745))))))) (joinSmall (lo:=7806) (a:=3903) (b:=3903) (joinSmall (lo:=7806) (a:=1951) (b:=1952) (joinSmall (lo:=7806) (a:=975) (b:=976) (joinSmall (lo:=7806) (a:=487) (b:=488) (joinSmall (lo:=7806) (a:=243) (b:=244) (joinSmall (lo:=7806) (a:=121) (b:=122) (joinSmall (lo:=7806) (a:=60) (b:=61) sp7806 sp7866) (joinSmall (lo:=7927) (a:=61) (b:=61) sp7927 sp7988)) (joinSmall (lo:=8049) (a:=122) (b:=122) (joinSmall (lo:=8049) (a:=61) (b:=61) sp8049 sp8110) (joinSmall (lo:=8171) (a:=61) (b:=61) sp8171 sp8232))) (joinSmall (lo:=8293) (a:=244) (b:=244) (joinSmall (lo:=8293) (a:=122) (b:=122) (joinSmall (lo:=8293) (a:=61) (b:=61) sp8293 sp8354) (joinSmall (lo:=8415) (a:=61) (b:=61) sp8415 sp8476)) (joinSmall (lo:=8537) (a:=122) (b:=122) (joinSmall (lo:=8537) (a:=61) (b:=61) sp8537 sp8598) (joinSmall (lo:=8659) (a:=61) (b:=61) sp8659 sp8720)))) (joinSmall (lo:=8781) (a:=488) (b:=488) (joinSmall (lo:=8781) (a:=244) (b:=244) (joinSmall (lo:=8781) (a:=122) (b:=122) (joinSmall (lo:=8781) (a:=61) (b:=61) sp8781 sp8842) (joinSmall (lo:=8903) (a:=61) (b:=61) sp8903 sp8964)) (joinSmall (lo:=9025) (a:=122) (b:=122) (joinSmall (lo:=9025) (a:=61) (b:=61) sp9025 sp9086) (joinSmall (lo:=9147) (a:=61) (b:=61) sp9147 sp9208))) (joinSmall (lo:=9269) (a:=244) (b:=244) (joinSmall (lo:=9269) (a:=122) (b:=122) (joinSmall (lo:=9269) (a:=61) (b:=61) sp9269 sp9330) (joinSmall (lo:=9391) (a:=61) (b:=61) sp9391 sp9452)) (joinSmall (lo:=9513) (a:=122) (b:=122) (joinSmall (lo:=9513) (a:=61) (b:=61) sp9513 sp9574) (joinSmall (lo:=9635) (a:=61) (b:=61) sp9635 sp9696))))) (joinSmall (lo:=9757) (a:=976) (b:=976) (joinSmall (lo:=9757) (a:=488) (b:=488) (joinSmall (lo:=9757) (a:=244) (b:=244) (joinSmall (lo:=9757) (a:=122) (b:=122) (joinSmall (lo:=9757) (a:=61) (b:=61) sp9757 sp9818) (joinSmall (lo:=9879) (a:=61) (b:=61) sp9879 sp9940)) (joinSmall (lo:=10001) (a:=122) (b:=122) (joinSmall (lo:=10001) (a:=61) (b:=61) sp10001 sp10062) (joinSmall (lo:=10123) (a:=61) (b:=61) sp10123 sp10184))) (joinSmall (lo:=10245) (a:=244) (b:=244) (joinSmall (lo:=10245) (a:=122) (b:=122) (joinSmall (lo:=10245) (a:=61) (b:=61) sp10245 sp10306) (joinSmall (lo:=10367) (a:=61) (b:=61) sp10367 sp10428)) (joinSmall (lo:=10489) (a:=122) (b:=122) (joinSmall (lo:=10489) (a:=61) (b:=61) sp10489 sp10550) (joinSmall (lo:=10611) (a:=61) (b:=61) sp10611 sp10672)))) (joinSmall (lo:=10733) (a:=488) (b:=488) (joinSmall (lo:=10733) (a:=244) (b:=244) (joinSmall (lo:=10733) (a:=122) (b:=122) (joinSmall (lo:=10733) (a:=61) (b:=61) sp10733 sp10794) (joinSmall (lo:=10855) (a:=61) (b:=61) sp10855 sp10916)) (joinSmall (lo:=10977) (a:=122) (b:=122) (joinSmall (lo:=10977) (a:=61) (b:=61) sp10977 sp11038) (joinSmall (lo:=11099) (a:=61) (b:=61) sp11099 sp11160))) (joinSmall (lo:=11221) (a:=244) (b:=244) (joinSmall (lo:=11221) (a:=122) (b:=122) (joinSmall (lo:=11221) (a:=61) (b:=61) sp11221 sp11282) (joinSmall (lo:=11343) (a:=61) (b:=61) sp11343 sp11404)) (joinSmall (lo:=11465) (a:=122) (b:=122) (joinSmall (lo:=11465) (a:=61) (b:=61) sp11465 sp11526) (joinSmall (lo:=11587) (a:=61) (b:=61) sp11587 sp11648)))))) (joinSmall (lo:=11709) (a:=1951) (b:=1952) (joinSmall (lo:=11709) (a:=975) (b:=976) (joinSmall (lo:=11709) (a:=487) (b:=488) (joinSmall (lo:=11709) (a:=243) (b:=244) (joinSmall (lo:=11709) (a:=121) (b:=122) (joinSmall (lo:=11709) (a:=60) (b:=61) sp11709 sp11769) (joinSmall (lo:=11830) (a:=61) (b:=61) sp11830 sp11891)) (joinSmall (lo:=11952) (a:=122) (b:=122) (joinSmall (lo:=11952) (a:=61) (b:=61) sp11952 sp12013) (joinSmall (lo:=12074) (a:=61) (b:=61) sp12074 sp12135))) (joinSmall (lo:=12196) (a:=244) (b:=244) (joinSmall (lo:=12196) (a:=122) (b:=122) (joinSmall (lo:=12196) (a:=61) (b:=61) sp12196 sp12257) (joinSmall (lo:=12318) (a:=61) (b:=61) sp12318 sp12379)) (joinSmall (lo:=12440) (a:=122) (b:=122) (joinSmall (lo:=12440) (a:=61) (b:=61) sp12440 sp12501) (joinSmall (lo:=12562) (a:=61) (b:=61) sp12562 sp12623)))) (joinSmall (lo:=12684) (a:=488) (b:=488) (joinSmall (lo:=12684) (a:=244) (b:=244) (joinSmall (lo:=12684) (a:=122) (b:=122) (joinSmall (lo:=12684) (a:=61) (b:=61) sp12684 sp12745) (joinSmall (lo:=12806) (a:=61) (b:=61) sp12806 sp12867)) (joinSmall (lo:=12928) (a:=122) (b:=122) (joinSmall (lo:=12928) (a:=61) (b:=61) sp12928 sp12989) (joinSmall (lo:=13050) (a:=61) (b:=61) sp13050 sp13111))) (joinSmall (lo:=13172) (a:=244) (b:=244) (joinSmall (lo:=13172) (a:=122) (b:=122) (joinSmall (lo:=13172) (a:=61) (b:=61) sp13172 sp13233) (joinSmall (lo:=13294) (a:=61) (b:=61) sp13294 sp13355)) (joinSmall (lo:=13416) (a:=122) (b:=122) (joinSmall (lo:=13416) (a:=61) (b:=61) sp13416 sp13477) (joinSmall (lo:=13538) (a:=61) (b:=61) sp13538 sp13599))))) (joinSmall (lo:=13660) (a:=976) (b:=976) (joinSmall (lo:=13660) (a:=488) (b:=488) (joinSmall (lo:=13660) (a:=244) (b:=244) (joinSmall (lo:=13660) (a:=122) (b:=122) (joinSmall (lo:=13660) (a:=61) (b:=61) sp13660 sp13721) (joinSmall (lo:=13782) (a:=61) (b:=61) sp13782 sp13843)) (joinSmall (lo:=13904) (a:=122) (b:=122) (joinSmall (lo:=13904) (a:=61) (b:=61) sp13904 sp13965) (joinSmall (lo:=14026) (a:=61) (b:=61) sp14026 sp14087))) (joinSmall (lo:=14148) (a:=244) (b:=244) (joinSmall (lo:=14148) (a:=122) (b:=122) (joinSmall (lo:=14148) (a:=61) (b:=61) sp14148 sp14209) (joinSmall (lo:=14270) (a:=61) (b:=61) sp14270 sp14331)) (joinSmall (lo:=14392) (a:=122) (b:=122) (joinSmall (lo:=14392) (a:=61) (b:=61) sp14392 sp14453) (joinSmall (lo:=14514) (a:=61) (b:=61) sp14514 sp14575)))) (joinSmall (lo:=14636) (a:=488) (b:=488) (joinSmall (lo:=14636) (a:=244) (b:=244) (joinSmall (lo:=14636) (a:=122) (b:=122) (joinSmall (lo:=14636) (a:=61) (b:=61) sp14636 sp14697) (joinSmall (lo:=14758) (a:=61) (b:=61) sp14758 sp14819)) (joinSmall (lo:=14880) (a:=122) (b:=122) (joinSmall (lo:=14880) (a:=61) (b:=61) sp14880 sp14941) (joinSmall (lo:=15002) (a:=61) (b:=61) sp15002 sp15063))) (joinSmall (lo:=15124) (a:=244) (b:=244) (joinSmall (lo:=15124) (a:=122) (b:=122) (joinSmall (lo:=15124) (a:=61) (b:=61) sp15124 sp15185) (joinSmall (lo:=15246) (a:=61) (b:=61) sp15246 sp15307)) (joinSmall (lo:=15368) (a:=122) (b:=122) (joinSmall (lo:=15368) (a:=61) (b:=61) sp15368 sp15429) (joinSmall (lo:=15490) (a:=61) (b:=61) sp15490 sp15551)))))))) (joinSmall (lo:=15612) (a:=7806) (b:=7807) (joinSmall (lo:=15612) (a:=3903) (b:=3903) (joinSmall (lo:=15612) (a:=1951) (b:=1952) (joinSmall (lo:=15612) (a:=975) (b:=976) (joinSmall (lo:=15612) (a:=487) (b:=488) (joinSmall (lo:=15612) (a:=243) (b:=244) (joinSmall (lo:=15612) (a:=121) (b:=122) (joinSmall (lo:=15612) (a:=60) (b:=61) sp15612 sp15672) (joinSmall (lo:=15733) (a:=61) (b:=61) sp15733 sp15794)) (joinSmall (lo:=15855) (a:=122) (b:=122) (joinSmall (lo:=15855) (a:=61) (b:=61) sp15855 sp15916) (joinSmall (lo:=15977) (a:=61) (b:=61) sp15977 sp16038))) (joinSmall (lo:=16099) (a:=244) (b:=244) (joinSmall (lo:=16099) (a:=122) (b:=122) (joinSmall (lo:=16099) (a:=61) (b:=61) sp16099 sp16160) (joinSmall (lo:=16221) (a:=61) (b:=61) sp16221 sp16282)) (joinSmall (lo:=16343) (a:=122) (b:=122) (joinSmall (lo:=16343) (a:=61) (b:=61) sp16343 sp16404) (joinSmall (lo:=16465) (a:=61) (b:=61) sp16465 sp16526)))) (joinSmall (lo:=16587) (a:=488) (b:=488) (joinSmall (lo:=16587) (a:=244) (b:=244) (joinSmall (lo:=16587) (a:=122) (b:=122) (joinSmall (lo:=16587) (a:=61) (b:=61) sp16587 sp16648) (joinSmall (lo:=16709) (a:=61) (b:=61) sp16709 sp16770)) (joinSmall (lo:=16831) (a:=122) (b:=122) (joinSmall (lo:=16831) (a:=61) (b:=61) sp16831 sp16892) (joinSmall (lo:=16953) (a:=61) (b:=61) sp16953 sp17014))) (joinSmall (lo:=17075) (a:=244) (b:=244) (joinSmall (lo:=17075) (a:=122) (b:=122) (joinSmall (lo:=17075) (a:=61) (b:=61) sp17075 sp17136) (joinSmall (lo:=17197) (a:=61) (b:=61) sp17197 sp17258)) (joinSmall (lo:=17319) (a:=122) (b:=122) (joinSmall (lo:=17319) (a:=61) (b:=61) sp17319 sp17380) (joinSmall (lo:=17441) (a:=61) (b:=61) sp17441 sp17502))))) (joinSmall (lo:=17563) (a:=976) (b:=976) (joinSmall (lo:=17563) (a:=488) (b:=488) (joinSmall (lo:=17563) (a:=244) (b:=244) (joinSmall (lo:=17563) (a:=122) (b:=122) (joinSmall (lo:=17563) (a:=61) (b:=61) sp17563 sp17624) (joinSmall (lo:=17685) (a:=61) (b:=61) sp17685 sp17746)) (joinSmall (lo:=17807) (a:=122) (b:=122) (joinSmall (lo:=17807) (a:=61) (b:=61) sp17807 sp17868) (joinSmall (lo:=17929) (a:=61) (b:=61) sp17929 sp17990))) (joinSmall (lo:=18051) (a:=244) (b:=244) (joinSmall (lo:=18051) (a:=122) (b:=122) (joinSmall (lo:=18051) (a:=61) (b:=61) sp18051 sp18112) (joinSmall (lo:=18173) (a:=61) (b:=61) sp18173 sp18234)) (joinSmall (lo:=18295) (a:=122) (b:=122) (joinSmall (lo:=18295) (a:=61) (b:=61) sp18295 sp18356) (joinSmall (lo:=18417) (a:=61) (b:=61) sp18417 sp18478)))) (joinSmall (lo:=18539) (a:=488) (b:=488) (joinSmall (lo:=18539) (a:=244) (b:=244) (joinSmall (lo:=18539) (a:=122) (b:=122) (joinSmall (lo:=18539) (a:=61) (b:=61) sp18539 sp18600) (joinSmall (lo:=18661) (a:=61) (b:=61) sp18661 sp18722)) (joinSmall (lo:=18783) (a:=122) (b:=122) (joinSmall (lo:=18783) (a:=61) (b:=61) sp18783 sp18844) (joinSmall (lo:=18905) (a:=61) (b:=61) sp18905 sp18966))) (joinSmall (lo:=19027) (a:=244) (b:=244) (joinSmall (lo:=19027) (a:=122) (b:=122) (joinSmall (lo:=19027) (a:=61) (b:=61) sp19027 sp19088) (joinSmall (lo:=19149) (a:=61) (b:=61) sp19149 sp19210)) (joinSmall (lo:=19271) (a:=122) (b:=122) (joinSmall (lo:=19271) (a:=61) (b:=61) sp19271 sp19332) (joinSmall (lo:=19393) (a:=61) (b:=61) sp19393 sp19454)))))) (joinSmall (lo:=19515) (a:=1951) (b:=1952) (joinSmall (lo:=19515) (a:=975) (b:=976) (joinSmall (lo:=19515) (a:=487) (b:=488) (joinSmall (lo:=19515) (a:=243) (b:=244) (joinSmall (lo:=19515) (a:=121) (b:=122) (joinSmall (lo:=19515) (a:=60) (b:=61) sp19515 sp19575) (joinSmall (lo:=19636) (a:=61) (b:=61) sp19636 sp19697)) (joinSmall (lo:=19758) (a:=122) (b:=122) (joinSmall (lo:=19758) (a:=61) (b:=61) sp19758 sp19819) (joinSmall (lo:=19880) (a:=61) (b:=61) sp19880 sp19941))) (joinSmall (lo:=20002) (a:=244) (b:=244) (joinSmall (lo:=20002) (a:=122) (b:=122) (joinSmall (lo:=20002) (a:=61) (b:=61) sp20002 sp20063) (joinSmall (lo:=20124) (a:=61) (b:=61) sp20124 sp20185)) (joinSmall (lo:=20246) (a:=122) (b:=122) (joinSmall (lo:=20246) (a:=61) (b:=61) sp20246 sp20307) (joinSmall (lo:=20368) (a:=61) (b:=61) sp20368 sp20429)))) (joinSmall (lo:=20490) (a:=488) (b:=488) (joinSmall (lo:=20490) (a:=244) (b:=244) (joinSmall (lo:=20490) (a:=122) (b:=122) (joinSmall (lo:=20490) (a:=61) (b:=61) sp20490 sp20551) (joinSmall (lo:=20612) (a:=61) (b:=61) sp20612 sp20673)) (joinSmall (lo:=20734) (a:=122) (b:=122) (joinSmall (lo:=20734) (a:=61) (b:=61) sp20734 sp20795) (joinSmall (lo:=20856) (a:=61) (b:=61) sp20856 sp20917))) (joinSmall (lo:=20978) (a:=244) (b:=244) (joinSmall (lo:=20978) (a:=122) (b:=122) (joinSmall (lo:=20978) (a:=61) (b:=61) sp20978 sp21039) (joinSmall (lo:=21100) (a:=61) (b:=61) sp21100 sp21161)) (joinSmall (lo:=21222) (a:=122) (b:=122) (joinSmall (lo:=21222) (a:=61) (b:=61) sp21222 sp21283) (joinSmall (lo:=21344) (a:=61) (b:=61) sp21344 sp21405))))) (joinSmall (lo:=21466) (a:=976) (b:=976) (joinSmall (lo:=21466) (a:=488) (b:=488) (joinSmall (lo:=21466) (a:=244) (b:=244) (joinSmall (lo:=21466) (a:=122) (b:=122) (joinSmall (lo:=21466) (a:=61) (b:=61) sp21466 sp21527) (joinSmall (lo:=21588) (a:=61) (b:=61) sp21588 sp21649)) (joinSmall (lo:=21710) (a:=122) (b:=122) (joinSmall (lo:=21710) (a:=61) (b:=61) sp21710 sp21771) (joinSmall (lo:=21832) (a:=61) (b:=61) sp21832 sp21893))) (joinSmall (lo:=21954) (a:=244) (b:=244) (joinSmall (lo:=21954) (a:=122) (b:=122) (joinSmall (lo:=21954) (a:=61) (b:=61) sp21954 sp22015) (joinSmall (lo:=22076) (a:=61) (b:=61) sp22076 sp22137)) (joinSmall (lo:=22198) (a:=122) (b:=122) (joinSmall (lo:=22198) (a:=61) (b:=61) sp22198 sp22259) (joinSmall (lo:=22320) (a:=61) (b:=61) sp22320 sp22381)))) (joinSmall (lo:=22442) (a:=488) (b:=488) (joinSmall (lo:=22442) (a:=244) (b:=244) (joinSmall (lo:=22442) (a:=122) (b:=122) (joinSmall (lo:=22442) (a:=61) (b:=61) sp22442 sp22503) (joinSmall (lo:=22564) (a:=61) (b:=61) sp22564 sp22625)) (joinSmall (lo:=22686) (a:=122) (b:=122) (joinSmall (lo:=22686) (a:=61) (b:=61) sp22686 sp22747) (joinSmall (lo:=22808) (a:=61) (b:=61) sp22808 sp22869))) (joinSmall (lo:=22930) (a:=244) (b:=244) (joinSmall (lo:=22930) (a:=122) (b:=122) (joinSmall (lo:=22930) (a:=61) (b:=61) sp22930 sp22991) (joinSmall (lo:=23052) (a:=61) (b:=61) sp23052 sp23113)) (joinSmall (lo:=23174) (a:=122) (b:=122) (joinSmall (lo:=23174) (a:=61) (b:=61) sp23174 sp23235) (joinSmall (lo:=23296) (a:=61) (b:=61) sp23296 sp23357))))))) (joinSmall (lo:=23418) (a:=3903) (b:=3904) (joinSmall (lo:=23418) (a:=1951) (b:=1952) (joinSmall (lo:=23418) (a:=975) (b:=976) (joinSmall (lo:=23418) (a:=487) (b:=488) (joinSmall (lo:=23418) (a:=243) (b:=244) (joinSmall (lo:=23418) (a:=121) (b:=122) (joinSmall (lo:=23418) (a:=60) (b:=61) sp23418 sp23478) (joinSmall (lo:=23539) (a:=61) (b:=61) sp23539 sp23600)) (joinSmall (lo:=23661) (a:=122) (b:=122) (joinSmall (lo:=23661) (a:=61) (b:=61) sp23661 sp23722) (joinSmall (lo:=23783) (a:=61) (b:=61) sp23783 sp23844))) (joinSmall (lo:=23905) (a:=244) (b:=244) (joinSmall (lo:=23905) (a:=122) (b:=122) (joinSmall (lo:=23905) (a:=61) (b:=61) sp23905 sp23966) (joinSmall (lo:=24027) (a:=61) (b:=61) sp24027 sp24088)) (joinSmall (lo:=24149) (a:=122) (b:=122) (joinSmall (lo:=24149) (a:=61) (b:=61) sp24149 sp24210) (joinSmall (lo:=24271) (a:=61) (b:=61) sp24271 sp24332)))) (joinSmall (lo:=24393) (a:=488) (b:=488) (joinSmall (lo:=24393) (a:=244) (b:=244) (joinSmall (lo:=24393) (a:=122) (b:=122) (joinSmall (lo:=24393) (a:=61) (b:=61) sp24393 sp24454) (joinSmall (lo:=24515) (a:=61) (b:=61) sp24515 sp24576)) (joinSmall (lo:=24637) (a:=122) (b:=122) (joinSmall (lo:=24637) (a:=61) (b:=61) sp24637 sp24698) (joinSmall (lo:=24759) (a:=61) (b:=61) sp24759 sp24820))) (joinSmall (lo:=24881) (a:=244) (b:=244) (joinSmall (lo:=24881) (a:=122) (b:=122) (joinSmall (lo:=24881) (a:=61) (b:=61) sp24881 sp24942) (joinSmall (lo:=25003) (a:=61) (b:=61) sp25003 sp25064)) (joinSmall (lo:=25125) (a:=122) (b:=122) (joinSmall (lo:=25125) (a:=61) (b:=61) sp25125 sp25186) (joinSmall (lo:=25247) (a:=61) (b:=61) sp25247 sp25308))))) (joinSmall (lo:=25369) (a:=976) (b:=976) (joinSmall (lo:=25369) (a:=488) (b:=488) (joinSmall (lo:=25369) (a:=244) (b:=244) (joinSmall (lo:=25369) (a:=122) (b:=122) (joinSmall (lo:=25369) (a:=61) (b:=61) sp25369 sp25430) (joinSmall (lo:=25491) (a:=61) (b:=61) sp25491 sp25552)) (joinSmall (lo:=25613) (a:=122) (b:=122) (joinSmall (lo:=25613) (a:=61) (b:=61) sp25613 sp25674) (joinSmall (lo:=25735) (a:=61) (b:=61) sp25735 sp25796))) (joinSmall (lo:=25857) (a:=244) (b:=244) (joinSmall (lo:=25857) (a:=122) (b:=122) (joinSmall (lo:=25857) (a:=61) (b:=61) sp25857 sp25918) (joinSmall (lo:=25979) (a:=61) (b:=61) sp25979 sp26040)) (joinSmall (lo:=26101) (a:=122) (b:=122) (joinSmall (lo:=26101) (a:=61) (b:=61) sp26101 sp26162) (joinSmall (lo:=26223) (a:=61) (b:=61) sp26223 sp26284)))) (joinSmall (lo:=26345) (a:=488) (b:=488) (joinSmall (lo:=26345) (a:=244) (b:=244) (joinSmall (lo:=26345) (a:=122) (b:=122) (joinSmall (lo:=26345) (a:=61) (b:=61) sp26345 sp26406) (joinSmall (lo:=26467) (a:=61) (b:=61) sp26467 sp26528)) (joinSmall (lo:=26589) (a:=122) (b:=122) (joinSmall (lo:=26589) (a:=61) (b:=61) sp26589 sp26650) (joinSmall (lo:=26711) (a:=61) (b:=61) sp26711 sp26772))) (joinSmall (lo:=26833) (a:=244) (b:=244) (joinSmall (lo:=26833) (a:=122) (b:=122) (joinSmall (lo:=26833) (a:=61) (b:=61) sp26833 sp26894) (joinSmall (lo:=26955) (a:=61) (b:=61) sp26955 sp27016)) (joinSmall (lo:=27077) (a:=122) (b:=122) (joinSmall (lo:=27077) (a:=61) (b:=61) sp27077 sp27138) (joinSmall (lo:=27199) (a:=61) (b:=61) sp27199 sp27260)))))) (joinSmall (lo:=27321) (a:=1952) (b:=1952) (joinSmall (lo:=27321) (a:=976) (b:=976) (joinSmall (lo:=27321) (a:=488) (b:=488) (joinSmall (lo:=27321) (a:=244) (b:=244) (joinSmall (lo:=27321) (a:=122) (b:=122) (joinSmall (lo:=27321) (a:=61) (b:=61) sp27321 sp27382) (joinSmall (lo:=27443) (a:=61) (b:=61) sp27443 sp27504)) (joinSmall (lo:=27565) (a:=122) (b:=122) (joinSmall (lo:=27565) (a:=61) (b:=61) sp27565 sp27626) (joinSmall (lo:=27687) (a:=61) (b:=61) sp27687 sp27748))) (joinSmall (lo:=27809) (a:=244) (b:=244) (joinSmall (lo:=27809) (a:=122) (b:=122) (joinSmall (lo:=27809) (a:=61) (b:=61) sp27809 sp27870) (joinSmall (lo:=27931) (a:=61) (b:=61) sp27931 sp27992)) (joinSmall (lo:=28053) (a:=122) (b:=122) (joinSmall (lo:=28053) (a:=61) (b:=61) sp28053 sp28114) (joinSmall (lo:=28175) (a:=61) (b:=61) sp28175 sp28236)))) (joinSmall (lo:=28297) (a:=488) (b:=488) (joinSmall (lo:=28297) (a:=244) (b:=244) (joinSmall (lo:=28297) (a:=122) (b:=122) (joinSmall (lo:=28297) (a:=61) (b:=61) sp28297 sp28358) (joinSmall (lo:=28419) (a:=61) (b:=61) sp28419 sp28480)) (joinSmall (lo:=28541) (a:=122) (b:=122) (joinSmall (lo:=28541) (a:=61) (b:=61) sp28541 sp28602) (joinSmall (lo:=28663) (a:=61) (b:=61) sp28663 sp28724))) (joinSmall (lo:=28785) (a:=244) (b:=244) (joinSmall (lo:=28785) (a:=122) (b:=122) (joinSmall (lo:=28785) (a:=61) (b:=61) sp28785 sp28846) (joinSmall (lo:=28907) (a:=61) (b:=61) sp28907 sp28968)) (joinSmall (lo:=29029) (a:=122) (b:=122) (joinSmall (lo:=29029) (a:=61) (b:=61) sp29029 sp29090) (joinSmall (lo:=29151) (a:=61) (b:=61) sp29151 sp29212))))) (joinSmall (lo:=29273) (a:=976) (b:=976) (joinSmall (lo:=29273) (a:=488) (b:=488) (joinSmall (lo:=29273) (a:=244) (b:=244) (joinSmall (lo:=29273) (a:=122) (b:=122) (joinSmall (lo:=29273) (a:=61) (b:=61) sp29273 sp29334) (joinSmall (lo:=29395) (a:=61) (b:=61) sp29395 sp29456)) (joinSmall (lo:=29517) (a:=122) (b:=122) (joinSmall (lo:=29517) (a:=61) (b:=61) sp29517 sp29578) (joinSmall (lo:=29639) (a:=61) (b:=61) sp29639 sp29700))) (joinSmall (lo:=29761) (a:=244) (b:=244) (joinSmall (lo:=29761) (a:=122) (b:=122) (joinSmall (lo:=29761) (a:=61) (b:=61) sp29761 sp29822) (joinSmall (lo:=29883) (a:=61) (b:=61) sp29883 sp29944)) (joinSmall (lo:=30005) (a:=122) (b:=122) (joinSmall (lo:=30005) (a:=61) (b:=61) sp30005 sp30066) (joinSmall (lo:=30127) (a:=61) (b:=61) sp30127 sp30188)))) (joinSmall (lo:=30249) (a:=488) (b:=488) (joinSmall (lo:=30249) (a:=244) (b:=244) (joinSmall (lo:=30249) (a:=122) (b:=122) (joinSmall (lo:=30249) (a:=61) (b:=61) sp30249 sp30310) (joinSmall (lo:=30371) (a:=61) (b:=61) sp30371 sp30432)) (joinSmall (lo:=30493) (a:=122) (b:=122) (joinSmall (lo:=30493) (a:=61) (b:=61) sp30493 sp30554) (joinSmall (lo:=30615) (a:=61) (b:=61) sp30615 sp30676))) (joinSmall (lo:=30737) (a:=244) (b:=244) (joinSmall (lo:=30737) (a:=122) (b:=122) (joinSmall (lo:=30737) (a:=61) (b:=61) sp30737 sp30798) (joinSmall (lo:=30859) (a:=61) (b:=61) sp30859 sp30920)) (joinSmall (lo:=30981) (a:=122) (b:=122) (joinSmall (lo:=30981) (a:=61) (b:=61) sp30981 sp31042) (joinSmall (lo:=31103) (a:=61) (b:=61) sp31103 sp31164)))))))))
  have good : (List.range 31225).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 975000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 31224 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 31224 := by
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


private def packet (i : ℕ) : ℕ := (if i < 248 then (if i < 124 then (if i < 62 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 5 then (if i < 4 then 0 else 0) else (if i < 6 then 0 else 0))) else (if i < 11 then (if i < 9 then (if i < 8 then 0 else 0) else (if i < 10 then 0 else 0)) else (if i < 13 then (if i < 12 then 0 else 0) else (if i < 14 then 0 else 0)))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then 0 else 0) else (if i < 18 then 0 else 0)) else (if i < 21 then (if i < 20 then 0 else 0) else (if i < 22 then 0 else 0))) else (if i < 27 then (if i < 25 then (if i < 24 then 0 else 0) else (if i < 26 then 0 else 0)) else (if i < 29 then (if i < 28 then 0 else 0) else (if i < 30 then 0 else 0))))) else (if i < 46 then (if i < 38 then (if i < 34 then (if i < 32 then 0 else (if i < 33 then 0 else 0)) else (if i < 36 then (if i < 35 then 0 else 0) else (if i < 37 then 0 else 0))) else (if i < 42 then (if i < 40 then (if i < 39 then 0 else 0) else (if i < 41 then 0 else 0)) else (if i < 44 then (if i < 43 then 0 else 0) else (if i < 45 then 0 else 0)))) else (if i < 54 then (if i < 50 then (if i < 48 then (if i < 47 then 0 else 0) else (if i < 49 then 0 else 0)) else (if i < 52 then (if i < 51 then 0 else 0) else (if i < 53 then 0 else 0))) else (if i < 58 then (if i < 56 then (if i < 55 then 0 else 0) else (if i < 57 then 0 else 0)) else (if i < 60 then (if i < 59 then 0 else 0) else (if i < 61 then 0 else 0)))))) else (if i < 93 then (if i < 77 then (if i < 69 then (if i < 65 then (if i < 63 then 0 else (if i < 64 then 0 else 0)) else (if i < 67 then (if i < 66 then 0 else 0) else (if i < 68 then 0 else 0))) else (if i < 73 then (if i < 71 then (if i < 70 then 0 else 0) else (if i < 72 then 0 else 0)) else (if i < 75 then (if i < 74 then 0 else 0) else (if i < 76 then 0 else 0)))) else (if i < 85 then (if i < 81 then (if i < 79 then (if i < 78 then 0 else 0) else (if i < 80 then 0 else 0)) else (if i < 83 then (if i < 82 then 0 else 0) else (if i < 84 then 0 else 0))) else (if i < 89 then (if i < 87 then (if i < 86 then 0 else 0) else (if i < 88 then 0 else 0)) else (if i < 91 then (if i < 90 then 0 else 0) else (if i < 92 then 0 else 0))))) else (if i < 108 then (if i < 100 then (if i < 96 then (if i < 94 then 0 else (if i < 95 then 0 else 0)) else (if i < 98 then (if i < 97 then 0 else 0) else (if i < 99 then 0 else 0))) else (if i < 104 then (if i < 102 then (if i < 101 then 0 else 0) else (if i < 103 then 0 else 0)) else (if i < 106 then (if i < 105 then 0 else 0) else (if i < 107 then 0 else 0)))) else (if i < 116 then (if i < 112 then (if i < 110 then (if i < 109 then 0 else 0) else (if i < 111 then 0 else 0)) else (if i < 114 then (if i < 113 then 0 else 0) else (if i < 115 then 0 else 0))) else (if i < 120 then (if i < 118 then (if i < 117 then 0 else 0) else (if i < 119 then 0 else 0)) else (if i < 122 then (if i < 121 then 0 else 0) else (if i < 123 then 0 else 0))))))) else (if i < 186 then (if i < 155 then (if i < 139 then (if i < 131 then (if i < 127 then (if i < 125 then 0 else (if i < 126 then 0 else 0)) else (if i < 129 then (if i < 128 then 0 else 0) else (if i < 130 then 0 else 0))) else (if i < 135 then (if i < 133 then (if i < 132 then 0 else 0) else (if i < 134 then 0 else 0)) else (if i < 137 then (if i < 136 then 0 else 0) else (if i < 138 then 0 else 0)))) else (if i < 147 then (if i < 143 then (if i < 141 then (if i < 140 then 0 else 0) else (if i < 142 then 0 else 0)) else (if i < 145 then (if i < 144 then 0 else 0) else (if i < 146 then 0 else 0))) else (if i < 151 then (if i < 149 then (if i < 148 then 0 else 0) else (if i < 150 then 0 else 0)) else (if i < 153 then (if i < 152 then 0 else 0) else (if i < 154 then 0 else 0))))) else (if i < 170 then (if i < 162 then (if i < 158 then (if i < 156 then 0 else (if i < 157 then 0 else 0)) else (if i < 160 then (if i < 159 then 0 else 0) else (if i < 161 then 0 else 0))) else (if i < 166 then (if i < 164 then (if i < 163 then 0 else 0) else (if i < 165 then 0 else 0)) else (if i < 168 then (if i < 167 then 0 else 0) else (if i < 169 then 0 else 0)))) else (if i < 178 then (if i < 174 then (if i < 172 then (if i < 171 then 0 else 0) else (if i < 173 then 0 else 0)) else (if i < 176 then (if i < 175 then 0 else 0) else (if i < 177 then 0 else 0))) else (if i < 182 then (if i < 180 then (if i < 179 then 0 else 0) else (if i < 181 then 0 else 0)) else (if i < 184 then (if i < 183 then 0 else 0) else (if i < 185 then 0 else 0)))))) else (if i < 217 then (if i < 201 then (if i < 193 then (if i < 189 then (if i < 187 then 0 else (if i < 188 then 0 else 0)) else (if i < 191 then (if i < 190 then 0 else 0) else (if i < 192 then 0 else 0))) else (if i < 197 then (if i < 195 then (if i < 194 then 0 else 0) else (if i < 196 then 0 else 0)) else (if i < 199 then (if i < 198 then 0 else 0) else (if i < 200 then 0 else 0)))) else (if i < 209 then (if i < 205 then (if i < 203 then (if i < 202 then 0 else 0) else (if i < 204 then 0 else 0)) else (if i < 207 then (if i < 206 then 0 else 0) else (if i < 208 then 0 else 0))) else (if i < 213 then (if i < 211 then (if i < 210 then 0 else 0) else (if i < 212 then 0 else 0)) else (if i < 215 then (if i < 214 then 0 else 0) else (if i < 216 then 0 else 0))))) else (if i < 232 then (if i < 224 then (if i < 220 then (if i < 218 then 0 else (if i < 219 then 0 else 0)) else (if i < 222 then (if i < 221 then 0 else 0) else (if i < 223 then 0 else 0))) else (if i < 228 then (if i < 226 then (if i < 225 then 0 else 0) else (if i < 227 then 0 else 0)) else (if i < 230 then (if i < 229 then 0 else 0) else (if i < 231 then 0 else 0)))) else (if i < 240 then (if i < 236 then (if i < 234 then (if i < 233 then 0 else 0) else (if i < 235 then 0 else 0)) else (if i < 238 then (if i < 237 then 0 else 0) else (if i < 239 then 0 else 0))) else (if i < 244 then (if i < 242 then (if i < 241 then 0 else 0) else (if i < 243 then 0 else 0)) else (if i < 246 then (if i < 245 then 0 else 0) else (if i < 247 then 0 else 0)))))))) else (if i < 372 then (if i < 310 then (if i < 279 then (if i < 263 then (if i < 255 then (if i < 251 then (if i < 249 then 0 else (if i < 250 then 0 else 0)) else (if i < 253 then (if i < 252 then 0 else 0) else (if i < 254 then 0 else 0))) else (if i < 259 then (if i < 257 then (if i < 256 then 0 else 0) else (if i < 258 then 0 else 0)) else (if i < 261 then (if i < 260 then 0 else 0) else (if i < 262 then 0 else 0)))) else (if i < 271 then (if i < 267 then (if i < 265 then (if i < 264 then 0 else 0) else (if i < 266 then 0 else 0)) else (if i < 269 then (if i < 268 then 0 else 0) else (if i < 270 then 0 else 0))) else (if i < 275 then (if i < 273 then (if i < 272 then 0 else 0) else (if i < 274 then 0 else 0)) else (if i < 277 then (if i < 276 then 0 else 0) else (if i < 278 then 0 else 0))))) else (if i < 294 then (if i < 286 then (if i < 282 then (if i < 280 then 0 else (if i < 281 then 0 else 0)) else (if i < 284 then (if i < 283 then 0 else 0) else (if i < 285 then 0 else 0))) else (if i < 290 then (if i < 288 then (if i < 287 then 0 else 0) else (if i < 289 then 0 else 0)) else (if i < 292 then (if i < 291 then 0 else 0) else (if i < 293 then 0 else 0)))) else (if i < 302 then (if i < 298 then (if i < 296 then (if i < 295 then 0 else 0) else (if i < 297 then 0 else 0)) else (if i < 300 then (if i < 299 then 0 else 0) else (if i < 301 then 0 else 0))) else (if i < 306 then (if i < 304 then (if i < 303 then 0 else 0) else (if i < 305 then 0 else 0)) else (if i < 308 then (if i < 307 then 0 else 0) else (if i < 309 then 0 else 0)))))) else (if i < 341 then (if i < 325 then (if i < 317 then (if i < 313 then (if i < 311 then 0 else (if i < 312 then 0 else 0)) else (if i < 315 then (if i < 314 then 0 else 0) else (if i < 316 then 0 else 0))) else (if i < 321 then (if i < 319 then (if i < 318 then 0 else 0) else (if i < 320 then 0 else 0)) else (if i < 323 then (if i < 322 then 0 else 0) else (if i < 324 then 0 else 0)))) else (if i < 333 then (if i < 329 then (if i < 327 then (if i < 326 then 0 else 0) else (if i < 328 then 0 else 0)) else (if i < 331 then (if i < 330 then 0 else 0) else (if i < 332 then 0 else 0))) else (if i < 337 then (if i < 335 then (if i < 334 then 0 else 0) else (if i < 336 then 0 else 0)) else (if i < 339 then (if i < 338 then 0 else 0) else (if i < 340 then 0 else 0))))) else (if i < 356 then (if i < 348 then (if i < 344 then (if i < 342 then 0 else (if i < 343 then 0 else 0)) else (if i < 346 then (if i < 345 then 0 else 0) else (if i < 347 then 0 else 0))) else (if i < 352 then (if i < 350 then (if i < 349 then 0 else 0) else (if i < 351 then 0 else 0)) else (if i < 354 then (if i < 353 then 0 else 0) else (if i < 355 then 0 else 0)))) else (if i < 364 then (if i < 360 then (if i < 358 then (if i < 357 then 0 else 0) else (if i < 359 then 0 else 0)) else (if i < 362 then (if i < 361 then 0 else 0) else (if i < 363 then 0 else 0))) else (if i < 368 then (if i < 366 then (if i < 365 then 0 else 0) else (if i < 367 then 0 else 0)) else (if i < 370 then (if i < 369 then 0 else 0) else (if i < 371 then 0 else 0))))))) else (if i < 434 then (if i < 403 then (if i < 387 then (if i < 379 then (if i < 375 then (if i < 373 then 0 else (if i < 374 then 0 else 0)) else (if i < 377 then (if i < 376 then 0 else 0) else (if i < 378 then 0 else 0))) else (if i < 383 then (if i < 381 then (if i < 380 then 0 else 0) else (if i < 382 then 0 else 0)) else (if i < 385 then (if i < 384 then 0 else 0) else (if i < 386 then 0 else 0)))) else (if i < 395 then (if i < 391 then (if i < 389 then (if i < 388 then 0 else 0) else (if i < 390 then 0 else 0)) else (if i < 393 then (if i < 392 then 0 else 0) else (if i < 394 then 0 else 0))) else (if i < 399 then (if i < 397 then (if i < 396 then 0 else 0) else (if i < 398 then 0 else 0)) else (if i < 401 then (if i < 400 then 0 else 0) else (if i < 402 then 0 else 0))))) else (if i < 418 then (if i < 410 then (if i < 406 then (if i < 404 then 0 else (if i < 405 then 0 else 0)) else (if i < 408 then (if i < 407 then 0 else 0) else (if i < 409 then 0 else 0))) else (if i < 414 then (if i < 412 then (if i < 411 then 0 else 0) else (if i < 413 then 0 else 0)) else (if i < 416 then (if i < 415 then 0 else 0) else (if i < 417 then 0 else 0)))) else (if i < 426 then (if i < 422 then (if i < 420 then (if i < 419 then 0 else 0) else (if i < 421 then 0 else 0)) else (if i < 424 then (if i < 423 then 0 else 0) else (if i < 425 then 0 else 0))) else (if i < 430 then (if i < 428 then (if i < 427 then 0 else 0) else (if i < 429 then 0 else 0)) else (if i < 432 then (if i < 431 then 0 else 0) else (if i < 433 then 0 else 0)))))) else (if i < 465 then (if i < 449 then (if i < 441 then (if i < 437 then (if i < 435 then 0 else (if i < 436 then 0 else 0)) else (if i < 439 then (if i < 438 then 0 else 0) else (if i < 440 then 0 else 0))) else (if i < 445 then (if i < 443 then (if i < 442 then 0 else 0) else (if i < 444 then 0 else 0)) else (if i < 447 then (if i < 446 then 0 else 0) else (if i < 448 then 0 else 0)))) else (if i < 457 then (if i < 453 then (if i < 451 then (if i < 450 then 0 else 0) else (if i < 452 then 0 else 0)) else (if i < 455 then (if i < 454 then 0 else 0) else (if i < 456 then 0 else 0))) else (if i < 461 then (if i < 459 then (if i < 458 then 0 else 0) else (if i < 460 then 0 else 0)) else (if i < 463 then (if i < 462 then 0 else 0) else (if i < 464 then 0 else 0))))) else (if i < 480 then (if i < 472 then (if i < 468 then (if i < 466 then 0 else (if i < 467 then 0 else 0)) else (if i < 470 then (if i < 469 then 0 else 0) else (if i < 471 then 0 else 0))) else (if i < 476 then (if i < 474 then (if i < 473 then 0 else 0) else (if i < 475 then 0 else 0)) else (if i < 478 then (if i < 477 then 0 else 0) else (if i < 479 then 0 else 0)))) else (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 0 else 0) else (if i < 483 then 0 else 0x2e426192b7944896244b1f80e3066e2e214688c839415e085029c0a800002e420482c1946899846e2038e946922de13f886438216708a82e00ca00002e41a882b6946098446a2050e886862e414388a438616a08c03180bc00002e414a62c894c499c46c2048ecc6aa2f114708b038e16808802e00a600002e40eb02cd15049ae47c20b8ec86b42f714988d039c17108902ac09000002e408d22c594a09704552010ea86a02e814688a839e17508b82ec0c400002e403022bd94b499846c2068eac68a2fa15089083e8193099033c0e800002e3fd432b0943894e44e1f80e846982e414488c039216308482dc0be00002e3f7a42aa93ec9544582008e686762d613e08a03a217e08c830c0c600002e3f1fb2a813d095244a1f58e586782e3142088839416d08782c80ac00002e3ec342b4941893c4451f20e2c65a2c813b886036815e08402b40a600002e3e6762b3945c98847420a8f046bc30915609403e818608d82fc0ca00002e3e0982bb945897645f1fd8e5867e2e814588cc3b017008b82d40ae00002e3dad62b4141c9544551f88e2065a2cd138885436614e07c82900aa00002e3d53b2a493b49244371f20e0465c2cb13c086438c16c08582cc0b400002e3cf812ad13d493043a1ed0dcc6322c0135084438216808982cc0a800002e3c9ad2b3142c95c4491f68e646762e214308b43a417508c82d00ac00002e3c3c02c594c89a647820a0ef46a02f715188f83c418209683440de00002e3bdf62ba943895c4522038e946962f1148889039216708302b009e00002e3b7f32ce94f09b047c20d8ef86ce30615008fc3c818009583340ca00002e3b2222bd14749844642030e906a02ef147088c38416c08602c80c400002e3ac6f2af14089484461f68e5868a2ef14708dc38c16708382c00ac00002e3a67c2cb14cc9aa47f2100ef46b430315489043c018809182fc0d800002e3a0942c1149098a4672088ec469a2f314e890c3e018c095831c0ba00002e39ae92ab93e093644d1f78e3465c2cb134885837215f08582c80c200002e3950b2bb943c9544491f80e6067a2e714608e83a817e08e83000b200002e38f1b2c814c899c47e2128f246e630814d88fc3d018408d82f80b000002e389742a293ac93e43a1f38e0c65e2db13b886436615c08182a00aa00002e383bb2ae94189684582008e9869e2f614a88d03ae17508d82e009a00002e37e112a793cc9464411f00e186542cc135883836c16207c02880b400002e378212c2948098c46a2040e9468e2e614188a838c16e083828c0ae00002e372432ba945c98045a1fc0e6c6962e7140887838016508482b00a000002e36c5f2c514789844632028e586862e613f88bc38e18509283100c800002e3669c2b1943497045d1fb0e746622d313e887c38816208282bc0a200002e360cc2b7945c97444d1f88e7c6842e814808c83a817408a82dc0c200002e35b082b6145896045d2010e8467e2eb14988b03ae17708b82f00c800002e355522ae14409564521ff8e9c68c2f014b88dc3ba18008e03180b200002e34f952b194209544501ff0e6866e2e213e08b03ac17309002f40ca00002e349eb2a993e49304461f60e586502d213d887c37815d08382c80c400002e3440c2bd14589664501fb0e5c6722d8140888c38816308302b809e00002e33e212c694cc9944712098eb068e2e0142089c3a217c08882f40b400002e338732aa140094c4441ef0df46582db13c887038c16808482ac0ae00002e332a92b7943096244c1f70e306482d113c08a03a217108782c80ba00002e32ce22b113f095e4581ff0e606822f214b08e03b618209082d40ae00002e327182bb94309564591ff8e6c6922f615009083cc18209102c80aa00002e321422bc947897645a2050ea86962eb14308c03a217c09383100d200002e31b812b3145896e4581fb0e606722dc14188a839617309102f00b600002e315b52b6944c97e45c1fb8e9469c2eb14688c83b216f08882c40d000002e310092a693f494a4441f90e646742db14488d83b217b08e82cc0b600002e30a272c094949944722080ed86b82ee14d88e83ca17a09103080c400002e304532bc147c98a45b2008ea06822ed14c88e03a216f08802b40a000002e2fe9f2b014209644571fb8e7867e2ec14888b839416e09103180be00002e2f8b22c194a09ae4802100f086ae2fd14f08d03a617e09403200d200002e2f2e52ba148097846b2070ef06a42f514b08c03aa16f08d82f40ce00002e2ed1a2b694109604491f58e486682e514288dc39a16a08702b40a000002e2e7522b614309684571f90e2863c2cc13a088437816908982bc0a600002e2e1912b7143095844e1f80e606882df14108cc3aa17308c02e80cc00002e2dbbb2c294b099e4722068ecc6ac2f814d08f83ae17608e82fc0b200002e2d5f72b9144c9624501fa0e7c6862e314688c03ac16e08e02e40b600002e2d0512a713d492a4401ed0df86402ce135884435614a07d029809e00002e2ca932ae13e095c4551f58e506722d913f089c3ae17708d02d80a400002e2c4ca2b8146897a45d2020e9c68c2ef14688a439817208682c00a400002e2bee92c414d09b847e20b8ef06c430915088fc3b418108d83000c600002e2b9342ab940494e44a1f30e446742d613d086436c15908402c00aa000)) else (if i < 486 then (if i < 485 then 0x2e599db2c1946896a4642020ebc6b82ff14d892c3d618809203280d000002e594172b394309584531fa8e7467c2e314508ac3a816f08582cc0ac00002e58e2e2c594a89904622040ebc6a02f314f89443e619509303200c400002e588752b1943497045a2040eb46a62ec14988f03be17909003180b000002e5829a2ba148499246e20a0ec869a2f414e08fc3ac17809102f80ba00002e57cd32b4944c98046b1fe0e686822ee14588e83c018009482f00b600002e576f92bd947898445f1fb8e846982f514708a839616e08a82e40ae00002e571292bf94989a247220e8edc6922ea14588c43aa18308f82f40ba00002e56b722ad942095645c1ff8e6c6822e214188b03b217708d83200d200002e565912be147097e4662010e9c68e2ed147089c3a017508c82cc0a800002e55fa12c514a099a4732098ed46c2301150891c3d218408d030c0b800002e559ea2b0142094a43d1f28e486662d914288a038816008302e80b400002e554102bb945c96c45b1fe0e886742e114408a438c17308d02f40c000002e54e302c194a499846e2098ee06b22f814a88b43a817808e83100cc00002e548612b9945c98c46a20c0ed46a22ee14788c43ac17c08f02e80b000002e542882c0149c99246d2050ed86a42eb14408c03a817508982e00ba00002e53cc22b4943495c45e1f88e5465a2ce13a884437015d081028809400002e536cf2ce95049ba48220f0eec6b4301156892c3c218d09383540d800002e530fb2bd94609624581fe8eac6802e414008b039216a08482a40b000002e52b1c2c0146c98846f2080ed06a02ec14b08cc3a017208f03280c600002e5255d2b213f094443e1f50e546702e414488cc3c418009503240ce00002e51f9a2af942093e44e1fa8e686862d914408c03a216408482c00a800002e519d72b2942495244a1fa0e6c67e2e214288b839a16f08b82f00b400002e514152b1143495e45e1fd8e686822f114a08d039c17008882c40b600002e50e452b814449724591fb0e786802e6141886837615f08302b80ae00002e5086e2ba14489704511fd8e706922e8144886c37e16408482980a800002e5027b2c394b89a647c20f8f106da30815389143c017e08e03340d000002e4fc8a2cb94d49b24782090ee86c230a15009343e419d09803280c800002e4f6df2a613f894643b1e90e1465c2dc14288f43be17f08d02c80b800002e4f10c2c094749864642050eb06942ef14b89003b217e09302f40ca00002e4eb4b2b5141096245a1fc0e5867c2df14188c83a416d08502e40b800002e4e5702bf146496e45f2008e8c6822e513b885837c16408682c40a600002e4dfd52a413b493643e1f10e246522d614788d83b817608a83140ca00002e4d9ef2c094b099e46920a0ec86aa2f614d08e03a618709683240c600002e4d4362a813f09464441f70e406722db13d08903a417008a03100aa00002e4ce8f2a993dc92a43b1f10e4866a2e414b08f83a417708682d80be00002e4c8c72b5944496a45b1fd8e3866c2d314708a438216208702b80a200002e4c2ee2c094909704672030e946822e114208b03a417b08f03000b200002e4bd322af94149664551fa8e786822e714308b83ba18809303000c400002e4b76d2b7145496a4561fc8e8867c2e114688bc3a0178090030c0be00002e4b19a2bb14849964662088eb06a02e714608c83a817c08c02f80c400002e4abcf2ba948096e4552038eac6902f414a88f83c218009103240ba00002e4a62a29c13749084301ed0dc464c2d413e888838416b08482cc0b000002e4a0462c214a89a44762098eb869c2f514b08cc3b017808b82dc0b400002e49a742bd949098a4782098ef46b02f314888d83ac17d08882d80b600002e494832c594b098a4592000e6066e2e414608b43aa17b08e82d80b000002e48e9d2c0949497e45f2028ea068a2e5144089439a16708902c80b000002e488d12b3144896045c2078ee06c02fe15209243c218508f83040c800002e4831d2b194249544461f78e706802e114488ac39616508682a80aa00002e47d302c914e49b24822108f2c6ea31c15909183e418d09603040c800002e477552be946497245e2020ea86a230015009103cc18a09483240d200002e4717c2bd94809604572040ea86a02f614a88e03a017708d02f00b400002e46ba82bd94249664551fc0e986822ec147089c38816908c832c0be00002e465e02b8944c9704652000ea068e2f014b08c03a417208902c00a600002e460122be148497645e2008e8c6a22f414788a83a417208b82d00ae00002e45a342ba146097a4601fe8e946a42e9142088038e16a08f030c0d400002e454532c094e09a446f20a8ee46b42fa14b89003c218208d82fc0c000002e44e8b2b3942c96a4581fc0e746762d9139884837817208c02d80b400002e448d72aa941c95c4461f90e6868c2e414888e03a616d08902a40b600002e4431e2b2940c9584441f78e3c6642d913c889039617508b03180b800002e43d462bc949099c46b2070e706642e314488cc3aa17808c82f00c200002e4379d2aa13d894044d1fa8e546682d6139886c39617908c02ec0b400002e431bc2cb14b898c4662078ee06b02f614b89003b417208e83100b400002e42bf12b694709804662080ea86902f314488ac3aa17f09283040b2000 else 0x2e70ddf2b8145896e45b2010e8c6a02fa14c09003bc18408d02f00be00002e707fe2c014649664521f78e586622dc14388f83b417a08c03000c800002e702452b0141095c4541ff8e746862ec14708b03a017808a82d40b800002e6fc7e2bb144c9864651ff0ea06902e714308b03a016908882d40ba00002e6f6c22b0943c9764541fd8e6c6762da13d085835c16908c82e00b800002e6f0d22c294d89aa47c20b0ef06ce2fb14708c83b818309002dc0ae00002e6eae32cd15189d84892158f0c6cc2fb15088e03b217e08e83040b200002e6e5132b6946096244c1f50e586722d913b088c3a417e08b03080ba00002e6df4a2bb94709724541fc8e746742da141087c38c16c08802d00c000002e6d97e2b714489644411f38e386702da13c08a039216e08682b80b600002e6d3a12c014949924682060eb86922ec14b08f43c417708f82f80bc00002e6cdff2a994089564511f98e486702da13c886438016308102c80a200002e6c82b2b4141093e4481f78e3c6562c6139087038815c08202e40c800002e6c2392d014e09b248220e0f0c6c630614808f03be18008f030c0d800002e6bc692bc947498c4692020e9c6942eb14888ec3d218b09283140cc00002e6b6882c114ac9a04722058ed46b02f414d88f43be18809382f00b800002e6b0aa2c5147c97c4591fb0e606722de14308cc3a818409082e80bc00002e6aafb2a893ac92442f1ec0e2865c2d814188bc3a617208b02d40b800002e6a50f2c794c899247620f8f046b630415309443d418809483500d800002e69f4e2b494489724631ff8ea469c2f114c08ec3ba17c09282ec0c200002e699912ae14389644531f10e406622ee14988c839e17308782c40b800002e693d72ae93e494443f1ef8e206582d413d886438216908702d00b800002e68e192ad94109404471f30e486742da138084438816808602e80b600002e688382c594a897e4571fe0e4c6602d713d88b43b618109482fc0ba00002e682442cb14e89b247320a0eec6b22ff14d88c03b417408f83000b000002e67c6e2bb14709764581ff0e8c6942fa14588b43a017508d03140d000002e676a42b594049544491fb0e586702d6140086837817109002e00b800002e6709f2de15409e24822160f646e030e15509083c6181094030c0c200002e66ae62b294089464491f78e7067e2e714788e43b217308e02f00b600002e665332ac93f89444461f60e4466c2db140088838816a08882b40ba00002e65f4a2bf146c98045c1fc8e7467e2e214908cc3a816c08802b80b000002e659732bf949c98446e2088ed86aa2fa14f88e439817708682d00c000002e653a72b8944496c4541f90e906842de14408c43a817c08d02fc0c400002e64e0229e934c8f84201e78df06502c1133082437c16108182b80b000002e648462b2940c95044d1f88e706682dc13d886838616208002b009e00002e6426b2c0145c96445f2008e8c68a2e4143889839817508c03040ba00002e63cb32b0142094043f1f10e146482c6135083436c16008002c40ae00002e636df2bf945497e45e2038eb068e2f314888c03b217a08f83040c000002e631302ac140c94643f1f18e106642d913b886039a16d08502bc0ac00002e62b422cb14cc9bc4872128f186b02fa14c08d43ae17408802fc0bc00002e6255f2c514c09a046b2080ebc6a42fb15089443ba18009302fc0ce00002e61fa02b6944096445f2008e646622e513f087838a169080829c0a400002e619db2b3946096044e1f60e3c6622c9135882c37816a08602b00b200002e614022bc14709824621ff0ea86a22e614608b039a16a08502ec0bc00002e60dff2d215089d449a21c8f846fc316153090c3ba18108e83140be00002e6084e2ab141896444d1f98e4066e2eb143886836815f08582bc0b000002e602642c814f499646f20c8ee06b02fb14888e43b417a08b82e80c800002e5fc9e2b3142895844c1fd8e646862ed14288b838816308502b40ba00002e5f6d42ab940c9524541fe0e6c66a2e214408c03a6175085830c0ce00002e5f10a2b5941c95644f1f58e3066c2ce13e087038416a08582dc0aa00002e5eb4a2b613f493c44b1f18e0864a2c513b886839816308783080d000002e5e5692bf944c97c45b1fb8e486762d013a888039016b08b02f00bc00002e5df5f2d695109d24832188f586f031115a895c3ec19809a03480e200002e5d9852c114ac9904682000e6c6762df13e088837416308482b40a000002e5d3ca2ad13e492a43a1f38e4c6762e614408a838e17308702f40b600002e5cdce2cd951c9d247f2140f146c230114f89183dc18a09283080a800002e5c83d29f93a892442e1ee0dc46382cd13d088439016808802c40a400002e5c2892ab93fc9664531fe8e8067c2e3141088c38016008802c80b600002e5bc9f2c394d099e4782048ea86902ee14688d039217108502e40ac00002e5b6ed2a913c494044d1f68df06502d013c086438a16108a02ec0ba00002e5b0fc2c514a49884682070ed86b22f814d88f43a817908d03240c400002e5ab322b994649864591f78e6866a2de14988b83ae17c08e03080ce00002e5a55d2b6944c98846d2060e9c6942ed14888b839816e08982e00bc00002e59fa82ac13e89524461f68e506682de13b88ac39416c08582dc0ac000) else (if i < 487 then 0x2e8814b2bc147c96e4532000e846842f814c88dc3b818008e03040b800002e87b732bd947898e4692070ed06b62fe15109043b817e08e02fc0b800002e8759a2bd147c99246f2098ebc69e2e714c08f03bc18309003140bc00002e86fc12c394b89884632008e806882de14308e03b217e09203380c400002e869e82bc946c9864692030e7469a2ed14288bc3a617d08882d80b800002e863e02d815489ec4912170f3c6ce30515388f83c018108d02d80c600002e85e3f2a0138c9144331ee0df06522c413a086c39216408582a80b200002e858772b1141c96845a1fe0e9869c2ea145887437e15c08582ec0c200002e852722d315049b64792068ed46ac2ee144888c38c16f08782b80a800002e84cb02af941095a4491f50e286442c0133080835e15e08482d80c600002e846ca2c2149099245b1fd8e806802f114808b43a617308c83040d000002e840de2c894ac9a246a2008e6c68c2e814688ac38216a08b82e80b000002e83b0a2be14b499a4642048eb869a2f514908d43bc17508a82d80c000002e8354b2ab93dc93e43c1ed0de463e2c3139087c38e17908f831c0d600002e82f9f2a693f49304451f60e286722e6142888438816408482b009e00002e829d02b8946898c4622088ec46a82f615108e43c817b08b02f80be00002e823ff2b8947497a46b2020eac69e2ef14808d439016808282c80a800002e81e572a393a09244391ed0e0464a2c8137084037a15d08402d40ae00002e8185a2d095149d248b2170f2c6e430c15609403dc19109d03640da00002e812542d795189ce4802130f186ce30f15509243e218309383180cc00002e80c9f2ab13f093a4491f70e3c6702d113a887c37c16308702c80b400002e806cc2b5141496045d1ff8e8c69e2f314708e039016a08902dc0c000002e801092b494149504551fd8e5867c2e5144088437a16708682b80a400002e7fb1e2c394a899646b2070ed06b02fe14f09083b618209302f80c400002e7f53b2c514b49a646f2090ec06aa2f714b88ec3bc17c08d82e00ca00002e7ef9b29f93b09204341ef0e1c66c2e214508f03c817a08d82f80ce00002e7e9af2c594ac9a24722030e8067a2e914688d43bc17908e02f00bc00002e7e3b52ce14e09b44772138f2c6c830414f09283c618b090030c0ae00002e7dde52b9947c9864672048ea46a02f914f89103cc17d09283180d600002e7d84929f939892643e1f08df46502d314108b43a817308982f80bc00002e7d24e2ca14b49ac46f2098ecc6bc2f715088fc3c017b08e02ec0b200002e7cc842b4141494a44c1f48e106602d814308ac38e16008682f80c400002e7c6ac2c0148898c4662048e9468c2ed14a08c03a016608702e00b800002e7c1112a213d09304441ef8e186442cc137085437416008002940a800002e7bb5b2af13f094844b1fc0e6467c2e214408a838e16008102b40b200002e7b5822b5144496445a1fb8e706782e714408bc39e17308a02dc0ac00002e7afab2bc146897a45c1fc0e7468c2eb14488d83b217808c82d40c000002e7a9e02b814689624612008e886982e914508b439617008f82e40c400002e7a4312aa93e893e4421f38e386562d2139887037e16908a82b00a600002e79e5b2b5143c97845d2008eb46aa2f314808c03a817608d02f00b200002e7986c2cb14cc9ae4702048ea06862ed14988f03c218108f02f80ba00002e7927e2cc94dc9a046e20a8ef46da31515c09583dc18908f82fc0d600002e78cc22b6144c96245e1fc0e6465c2d2138086037016108702e00c000002e786df2c1948c9744541fd0e946902ea14a09183be17308c83140ba00002e7813b2a713cc91e4421ed0e106422c6135883436a16908602c80b400002e77b5b2bf949097c4632078ed06a62f914d08c03a617e09102e40bc00002e775a62a813e493a4431f70e306602d913c082436015507e82a80b200002e76ff52af140493e4381f08e1066a2d713d089c38c15d08e03100d200002e76a212b794209464461f40e4c67e2e5142889439a17b09083140c600002e764362c214a09a64662010e886842ed14608e83a416808602d80ac00002e75ea429f93a891a43a1f08e0c64c2c3135086038a16008682c00c200002e758e92b0940494843f1f30e2065e2dd13d088439416708982f40be00002e7531f2b4941496a4571fc8e646662d613b088438e16808682dc0be00002e74d4c2c2149098446b2050eec6b82fb14b88f83b818409003300ca00002e7477a2b8948098245e2088efc6be30d15789283cc18c09402f40d000002e741ab2b514349524501fb8e8c68e2ef14988c038c16c08382d80b600002e73c0a2a0938c8f042b1e50dc46362c6135884837416007f02a00b800002e736312ba144496245e2020e986782dd14188a039017408502d80b600002e7307b2ad93f895a4561fc0e686782e514608c439816c08602e00ae00002e72ac72ab93e49484401f00e006462ce13a882436215d08402e00be00002e725182a713d89304391ee8de46322d013c08a43a216b08182a00b400002e71f4a2c2945897645a1f60e586742d9141089439016e08782b80aa00002e719582d094f49c24802140efc6d031815c09683f419909c83700e400002e713b02a893d49524431f70e486782e414888a438a16b08602dc0bc000 else 0x2e9f5542ad940895044b1f38e586862dd14b88e03ac179093830c0c400002e9ef8d2b8946c9824652048ec46a82e8144888c39417608802d40b400002e9e9cc2b1142094644e1fc0e7466a2e4144889036c16908402ec0c000002e9e3d62cb15009b247b20f0ef46aa2f414a08c038616708c02d40b600002e9ddff2ba947497445e1fb8e586682d413c084037e16c08c830c0e200002e9d8132cb14dc9c848a2130f246be2fb15188e83b817e08c82cc0ca00002e9d22e2bc147895844f1fd0e4c6682dd13f087c39617608b82e40a600002e9cc712b013ec94c4441f58e5067c2e514508dc3ba17a091830c0c400002e9c6aa2b314309564521fd0e7867e2d7138086438216008482bc0ac00002e9c1082a3939491a42f1e80df86522cd133084c37816508c02cc0b200002e9baff2d394e49ac46a2058ea068c2e614108b03a217608d02fc0ca00002e9b50a2cb14f89a446f2080ed46982ea14488c039c17f08e03000c800002e9af362bc146498a4642060f006a42ed14788cc3ac17508c03040b600002e9a98d2a193a091c4251e88de86402c3137086038e16b08b82e40b600002e9a38b2ce14c099a46a2008e746602cb135086c36816108702fc0cc00002e99d942c894d89a047620a0eb86922ec14808e03b0178094033c0be00002e997bf2b7946c9724622058edc6a22eb14408bc3ac17508e83080c200002e992152aa13fc94444e1fd8e906882eb14408b83b817e08b82d80ac00002e98c582b4941894e4541fe8e6c6862e3142889c37a15e08782e80b000002e986702c314c49aa46c2030eac69a2f214a08f83c818409083300c400002e980da29f13a89344471f60e806702df13e888837415a08502a80a600002e97b222af940094a4521f58e0864e2cc14388bc3ac16b08602a409800002e9752d2cd94d49b848020f8f086e831115d89683e018909103040d000002e96f5f2bc145c9764591fb8e8c68e2e7143889c3ac17809002fc0b600002e969912b814889684531f70e9c6a62ed14c88cc3b817208c02bc0b800002e963e52aa93e894c4491f40e4c6662de14288b439817008a02c809a00002e95de22d014f49b447b20f8ef06ac2f814a08ec3aa17f08d02f00c200002e9580f2bb145498045e2010e9c6a02f414a890c3d0185093030c0b800002e952662a993e893a43e1ea8dfc64c2d413c886c39617408d82f40c000002e94c8b2b594449704662080edc6c42f914e08f83ca18609203180ba00002e946912d1950c9c847f20d8f046cc31115e09803fa19d09e033c0c600002e940c72bb94809884692060ea067e2e5142888838e17508802f00bc00002e93ad62cc94f49b04762068ee06aa2ed14608a838616508202bc0a000002e934f02c514ac9a24732048eb069e2f314688ec3b6181094833c0be00002e92f3d2b2942896a44c1f70e2c66e2df14208a438e16908c02d40b400002e929662be946097c4602018e986a62f214908bc3a417308582c00be00002e923902ba94509644531f58e4866e2da139087c39a17108e82ec0aa00002e91dca2b8142c96845f1fd8e986ac2e714608dc3b018109302fc0c600002e917f92b914849864561f70e206482c7134086438e17308a82cc0b800002e912412ae940c96444c1f60e2c6642e914388a43a417008c82e80c600002e90c6e2b4143094c44b1f60e146522d0138086037e16708802c00ae00002e906b42b0942496444c1fb8e4866c2dd14008b83a016908582c40ac00002e900fc2af93f494a4511fa0ea467c2e614b08c43b218109103140d000002e8fb2d2b9946098a46d2088ec46942ef14889083d418509303040c600002e8f56d2af93dc9564571f98e646942ea14288a83ae17b08a02fc0be00002e8ef942c1946497045f1fe8e8468c2e514088ac39417408e03200ca00002e8e9d22b3143c9584531fb0e786822e514988cc3b017908b82e80ba00002e8e40c2b5143496a44d1f68e2c66e2da14008a039a17108a82f00c000002e8de4f2ae140c9524521f68e5c6802e714588c83ae17609083180da00002e8d89a2b6945c98e4651fe0e9c6922e314288dc3c817f08c02e80b200002e8d2d52b694349544471f68e5465a2cf13b888838215c07d02d40b000002e8ccce2db15349d64872150f5c6da30315209283d619709282f00b800002e8c6fb2bd948097c46720c0ee46a62f314d08c03aa17208502dc0b200002e8c1232be94c099a4622080ea86802e6141088039617008902e80ae00002e8bb5c2b9942495a4471fb8e7c6702dd13f08c039817308702c40a600002e8b5842c2147097e4642090ec46a830215089043be18509402f80ca00002e8afd02b2143c9524441f00e386682df14588a839816f08802d40a400002e8aa0f2ae140c96e45a1fd0e7c6762d513e088839617108b02e80ba00002e8a4322be947096a4551fa0e606a22fb14b88e43b617b08982d80aa00002e89e542c314989944732058eb06962ee141886838e17408782c40b000002e898782bf949898e4732068efc6a62f614b88bc3a617308702fc0ca00002e892bd2b3942896045d2008e806a82f014508a83a617b08a030c0d600002e88cd62c3947c97a44f1fb0e7867c2d513f88983a016b08b02a80a000002e887152b114249544491f38e7c6942f014808e43ac17d09083200e6000))) else (if i < 492 then (if i < 490 then (if i < 489 then 0x2eb69492b194449704501fc8e5c66a2d0139886c39a17708982b40b400002eb637d2bb946897c4692008e986922e5142089437415e082829c0a800002eb5db32b594449584622018e846882ee14a88c83a216f08682b80c200002eb57bd2cc94c09a047820f8ee86a62eb147889038e16a08482bc09e00002eb52182a613dc92c4391f08e106422c713c886036616408082ac0b000002eb4c472be948899c4692090ed86b230415109143ea18a094030c0b600002eb46712b9945c9724612040eb869a2ea14608c439c16b08682bc0c600002eb40762c8949898645f2048ed06942eb14a88dc3c218809603080cc00002eb3aa32b994549a247120c0efc6c62fe14888b038217608f03040c200002eb34e42b214249584481f50e4c68a2e714c08e83b418209303340de00002eb2f122bd948498e46c20a0ec869c2f514d88f83b218008c02f40c400002eb294f2b914409864682040e6467a2e114608e03b018108c83100ca00002eb23862b113dc92e4391ed8e0c6582d813d088839817108a82d40ba00002eb1dae2bf944c96245d1ff0e646782dd13d888c39e17508b83000c000002eb17d22bc947097e4601ff0e9c6922f6150892c3dc18c09303200ca00002eb120a2b414509704662020e4466e2df140087838616908982e00aa00002eb0c272c714b49a247b20d0edc6be30415309403cc17f091031c0ba00002eb067e2a1139c9084321ec8dfc6422c3135881c36a15007f82ac0aa00002eb00a32b9945c97a4591f98e6466c2dd13f889c39616b08c02d00b000002eafada2ba144496645e1fe8e5866e2da13f8884398170091830c0d000002eaf4fb2ba944095e4521f78e586762e014388b83a617408782e80b200002eaef492ac13d093a4431f48e2866a2e114388b43b217a08d03040b400002eae98e2ae140c9524471f88e0465e2da142088438616d09082f40c200002eae3ad2c394d49b047920a8ec06a62f715189183c418b09603140c200002eaddfc2a413b09284331ed0e106542d6138886437215d08202ac0a600002ead81a2c1947096e4581fd8e786862e914508dc3b417508902d00b800002ead27829f93889144291e68dfc6462c7139088c39416708a02f00c400002eaccc12b213f89444441ef0e1c6422cf145087838c16608903040d200002eac6a02e01594a224a32250fbc712324163099040c19d0a203580d200002eac0ff2a793c894c4491fb0e5868a2ea14388d83b617309002ec0c000002eabb132c894b499246b2090ed06b82f914b08c43ac17f093032c0c200002eab5322c1948c9a847b20a8f106a62f814d88ec3aa16c08982cc0b600002eaaf412c6148c9804612038e806842e714989083ca17e096030c0ba00002eaa98a2af141c95e4562030e6c6882e714008803a017208502e40d000002eaa3b42bc147c9864632078eb86922f314608c03b417808c02d80a200002ea9de42b7144c95e4531f98e6c67a2da13c085c37416a08402ac0a800002ea97f92c994ec9a84752090ed46ac2f614b89003d619009083180ba00002ea92302b2942c95c4491fc0e686802e014588d43ae17408782c809e00002ea8c642b5145095844f1fb0e686782e213b885037215107c02b00ac00002ea866a2d294ec9a646a2038e986802e514288ac39e17008b02ec0ae00002ea80a52b4142095645a1fa8e646782e314288c03ae17708d82e80c200002ea7ac42c994ec9b04882170f3c6e430e15689143be18109282e00c000002ea74f92b9946497e4722010ea869c2f6144889437e15d08182a00b800002ea6f1b2c2148498a45d1f98e2c65a2d713f08a038c16708a82d80b200002ea69512bd14949864692040e7c6822e514308c039016508402a40aa00002ea63712bf14889884632070ea06902ed14288a039016b08902e00b400002ea5dbe2ab93dc9424491fc8e706762e6140088438416708102880b200002ea58032aa93c49324391ef8dd064a2d113d887039016408782c40aa00002ea52322bc94249604441ef0df06442c3136086c36a15c08282ac0a200002ea4c432cb94f09ae48220f0ea46a02ea14b88e83ba18709002e40ac00002ea467e2b5142095a44b1f88e906a82f514488d43aa17308982e00d200002ea408c2cb95049ce4882100ec46a62ef14888dc3b617808d82f00c200002ea3ad82ac941093e43c1f10e3466c2df14208bc39a17b08e03040c800002ea35162b394509784572018e7c6902e914588b439217208782d40c600002ea2f4a2bb143c96845f1fc0e686782e314208b43b017708a02f80da00002ea296e2bd948099447020a0ee06902e7141088436015e08782d40b400002ea23a22b2143c96845c2000e5867e2df140088439217608882b40aa00002ea1dc92c1148098845e1fd0e906942f314c08f43d618b08f02f00be00002ea17ef2be146c96a4561fd8e906942e914a08a83aa18008e030c0bc00002ea121f2ba946896a4581fe0e7067c2d2142089039016d08882dc0ba00002ea0c5b2af942895a4491fc0eb46b030014e89083b218108d82d80be00002ea06b42a593d893243d1ed8e106542d513f886038416208502dc0b400002ea00cd2c714cc9d248b2160f546f031315a093c3ee18c09b03640f200002e9fb112ae14009544471f68e3064c2cf137887438617009282ec0c2000 else 0x2ecdc542ac940c93243f1f10e706942ef14688c439e17008a02e40ba00002ecd6b22a513e094a44f1fb0e3c65c2d5137088038215e07e82900aa00002ecd0e92b4142c9424551f90e5467c2d813a887838616c08f82cc0b800002eccb1d2b414289524531f50e006502de14708e83bc17808c82d40b800002ecc54e2bb947899246a2018ec86ae2fc15189103d018809403200c600002ecbf8d2b5941895a44a1f00e646742e314808bc39617a08802e40bc00002ecb9b22bf94549724602040e886902ea14688cc3ae17c09403080ba00002ecb3e32b8945898046e20b0ef46bc2fd15089183ce18108682c80b000002ecae162b994609884622020ecc6ba2f514b88e03ae17c08b82b809e00002eca8472b9145097646a2070e786782dd142889439a17108d82cc0c400002eca25f2c414dc9b447f20f8ef86be30114b08e03b817c08e02f00c800002ec9cb02a9940493243e1f78e6c6862e414408ac3a017708602c40c000002ec96c02c814b098c45f1fc8e9468e2e6141087838816d08782d00ba00002ec90f82b3143c96045b1ff0e946962f314c88ec3ae17b08a02b40a600002ec8b302b4941c94e44c1f60e586602e313b088837a16408502fc0d200002ec855d2bb146c9724531fc0e686862e8141889438a16508d03100b800002ec7f852c0149098c46b2088e706922f314708f03cc18a09103200ba00002ec79b82b9146c97e4612008eb069c2ee14c88f03a017308602e80b800002ec73d82c294bc9a847d2100f006ce2f814d88fc3d417e094832c0d200002ec6dfc2bd146c96a4622090ed46a82ff14f88d039817f09102ec0b000002ec686d29b937c8f24241e90db062e2be133883c36c15507f02900a600002ec62862bd94709964631fd0e746802ff14d88e43b817a091830c0e000002ec5caf2c2949499447520f8f2c6cc30f15889443e618909402d40ca00002ec57012a993f095244c1fd8e5067e2e713f088038e16b08602f00b600002ec51262bd946c9844702080ea06942f1142087439016e08602f80c400002ec4b292ce95049bc48520f0ee46a02f614588d03aa17709202d00a400002ec456c2b594609844692028e886b42fd14d08d83c417d08982f00b800002ec3f942be147497e45f2010ea868e2ee14a090c3c818609083040c800002ec39ab2bd144c96244d1f58e446822f214c08e03c818008e02d40b800002ec33df2b414409684602020e946922e113a887037816f08982dc0a800002ec2e032ba94449864642060e946822de14108c03a817d09603280d200002ec28072cb94e89c24842140f186ce30b150093c3cc18709083180c400002ec21ff2d3152c9c047d2110ee86ba30014e08d839617708a82c00c200002ec1c6129e936c90a43b1ed8e1864c2c5137085437a16d08b02f40ba00002ec16972b514449724501fd0e7467c2e414208a03a817408d03040d000002ec10cb2b7145898a4661ff8e886882e613f08b038a15908082900a000002ec0ae92c514b49884702028e886762ea14508ac3a017909102e00ba00002ec05372a893e89344451f78e586822df13d887837e16108282c40b800002ebff7e2ad13f093644d1f60e886802e0143088c39c17208a82cc0b800002ebf9be2ab13ec9284391f18e306802d913a088839c17e08c02e80a400002ebf3f52b594249544451f50e386602e0141089838c16b08482c40c000002ebee1f2bb14409604531f90e5866c2df145889839617008a82dc0b400002ebe84a2ba14849984712070ea86842dc142089438c17108b82e00ba00002ebe28c2af94389624521fa0e5c67c2de142089838c16508902b40b200002ebdcc22b514489764692038e946882e114688bc3a617508982bc0ac00002ebd6e12c714b899646c20c8ee06c030415509283da18909783400ca00002ebd1392a513b490c42a1e90dd063e2c8134883036816208882e80b200002ebcb6a2ba943094e4401eb0ddc62e2bb136087038816808b02cc0ae00002ebc5b22ab141895a4461f28e1c6742e514788c83ac17b08982c80b000002ebbfd12bf149099e47220e8ed46b02f814f890c3d218608903000d000002ebba082b114409724612048ed469e2fc14f89083be18209282d40a000002ebb4462b5942095e45e2058eb86aa2f414688ac3a617508983040be00002ebae9c2a093d09364441f40e3865e2d3139885c36e15c07d02ac0a600002eba8bf2c6148c98a4652018e8c6802d813c087c38a16908b82f40c800002eba2fc2b7944895e4531fa0e3c6682d813a88943a217108d03040c600002eb9d3b2b5144497e45f2050ebc6962f015108dc39617809182fc0cc00002eb978d2b2143c95e4541ff8e946a22f714d08f43bc17908d02e00be00002eb91d62a894109644531fa0e886842e014188c43a817308c02f00b600002eb8c162ad94109424481f60e5067e2e714488903a217308b83080ac00002eb866f2a993f09424421f10e5066e2d513c88a839c17008503140cc00002eb80982bc947897a46e2078ee06bc30314e092c3d818009202fc0ae00002eb7ac32ba943c9444481f50e4c65c2c7137087038616808a82b00a800002eb75152a593a09204311ed0de864a2c3135084437215d08402d80b000002eb6f002da15549ea4a12120f2c6c830915509243d418c093831c0ce000) else (if i < 491 then 0x2ee4fbb2bb94609844541fa0e486722d613c889c3a217008c82e80b800002ee49cc2cc94c49ba4892148f006b6303155892c3d418408e02dc0bc00002ee43f72ba14809964742088ea069a2f614e08fc3be17508882b00b800002ee3e022ca14f49b44792100ef06ae2f514f091c3b417f09103140bc00002ee383a2b4941495c4471f78e246802e414908b43a617508502d00b800002ee327d2b394589604521fd8e686842eb14d88f83b617f090031c0ca00002ee2cb52b213f494844e1fb8e486762dd143088838816108682f80b600002ee26cf2c394ac9944692070ed069e2f314d08f83ae17b08a82cc09e00002ee21072b7941c9584471f40e3c6502c413a887038817108982d80b000002ee1b4c2b2143098045a2038eac68e2e2140888439816608982d80be00002ee158b2b2142c9604551fc0e646702d413c88c03b217709102ec0b800002ee0fb92c0147097e45f2028e986842e914a89043c018509603380b600002ee09fd2b594189544531f48e6c6882e414388a03b617108702cc0b200002ee04302ba947897e45e2000e786882df14a08dc3ac17908782b00b400002edfe552b8944c9864581fc0e9868e2ea143086c38a17208e831c0b200002edf88c2b314609684571fd8e906922e2146888838617008b82ec0be00002edf2c42ba143c96a45b1ff8eb068a2e314488a43a617308e82f40c600002eded3329d93bc9344401ea8de06402c212f87f834e14e07f02a809e00002ede7582bd14709744642080ee069e2ef14a88b83a216b08982b80c000002ede1722c694d49a647020c0ee86ac2fa14888e83ca18508b82fc0c800002eddbba2ae14009444401f50e4c6802e814288c43aa16f08c02f40b800002edd6082a413c093a4441f60e406622d513f088839617309283000d000002edd0222c214b49924712090eb069e2f015208e43b818c091831c0d200002edca602b5941494844a1f98e506782e6143087c38e16908602d80b800002edc4912ba944495a44e1f58e2865e2c6136882c36815a08482ec0ba00002edbeac2c714e49ae47d20c0ecc6a82f814908e03b417b08c82b00a400002edb8f32ae142495c4561fb8e746982f214c08c83c018709103240bc00002edb31c2bc14409624561fd8eb46962f814b89003b818909503180b600002edad552b814949944662048e9466e2e414288a03b617f08a02f00b200002eda7a42a893d49324421f40e3c6682d3141888438816808682ec09e00002eda1af2cb94ac99e47920e0ee06bc31015609383ca17f09003180c600002ed9c0a2a893a89044301ea0e1064a2ce143889838c17208b02f80c400002ed966d29f937c9224341e98dd062c2b412d07ec34815908082a80b000002ed90922c694b89a847820d0ee469c2f214808e83b217108a02e40a400002ed8ac62ba94609644501f98e5868c2e4145889c38216708582d80aa00002ed84ea2bd14989904642010e6466e2d4139886437216c08982c40b400002ed7f152ba14449624501fb8e546682e0143888039817208e82d00b600002ed791b2ce951c9dc4852110f1c6bc30014f09143c617e08e82dc0b400002ed73672af13fc94043f1ef8df064a2dd14208cc38e17008902dc0ba00002ed6d9f2b6942096445f2030ec06922ef14d08d83de18e097032c0bc00002ed68002a093989024291e80df064c2ca138085438816708b02dc0c000002ed62452af943895c44a1f78e3467c2de13b088037816308602ac09400002ed5c782b514209684581fe8e6c6882e614a08b43a217208b82e40c200002ed56a22bd944496e4571f90e486762e214508cc3b418608d830c0c400002ed50a02d1950c9c44832118f0c6dc31015909343de18a08d82c80b800002ed4aca2ba944c96e4602030ec068e2ee14488d43a817508e82ec0c000002ed45082b314349624511ff0e6c6702e514a88d03ac17b09402e80ae00002ed3f302be945495a4562028eac6902ed14788c03b017609202fc0d800002ed39762a913d49224391f00de46462cd14008cc3b016e08782d40bc00002ed33892c894b499e46d2050e886a22f314908d03ac17808b82dc0b600002ed2d932c814c89a046920a0ee06d630c15209043b417d08882ac0a800002ed27ce2b6140c94e4511fa8e7c67c2ee14688b83b617d08e83000bc00002ed21ff2ba94309584521fe8e8867e2d613d886c38416808982bc0b600002ed1c072cf94fc9c04872110eec6b42f414908d43a017408782e00b600002ed16492b3142495444e1f88e3866a2df14108843aa17308a82e40c000002ed10902b514709784622048ec46982f814c08e03b217608e831c0cc00002ed0ab92b6142c95844f1f60e606762dc140089838817108c82dc0ae00002ed04e12bc14a498c4611fe8ea069e2ef152090c3ce185093833c0c800002ecff132be94a098c4682090ee86c230514f88e83b417f09183200c000002ecf9572b0141495644c1f98e646722e514208a03a417f08d82f40c000002ecf36f2c514b499c45c1fe0ea069c2f514d08f03be18709183300d000002ecedb92aa93e894844a1f38e046542cc139085839417509283080ce00002ece7c92c414ac99047120a0ed46b82f914b08d43c018209883300c200002ece2072ae13d49484401f20dfc65a2d314008a03b618209082f00ca000 else 0x2efc27229f13848fc4271e48d9860c2b312987e835014a07d82a00aa00002efbcbc2af93f09584571f80e2c6622dd14488a037416408302d40b200002efb6dc2c394b09c04792140f486e631215a893c3e018409102f40c400002efb1092bb94689864602028ea86882f214d08f43b817708b82f40c000002efab3e2b8145497a45b2008e9c6802e8148089c38616b08902d80be00002efa5792b1942494e45a1fc0e686682d313e086c38e16408682c80a800002ef9fbe2ad14149564461f20e1865c2db13e088039217208682e00b400002ef99e82bc94849844661ff8e706922eb14a08d03b617608e831c0b000002ef94262af140c9604561fe8e806802e2140887437a161084829c0a600002ef8e552b794749764522008eb068c2ed14608bc39a17d08982e40c000002ef88a82ad14009484431f50e2864e2c4133881035014908002a40b400002ef82ba2c914b49a44712070ec069c2ed14b08e03ae17508c83040c000002ef7cea2b4942c95a4481f70e486702e3141088839e17408e03040c200002ef77162c314789984712090ea46842ea143888439416408502dc0ae00002ef71552b4142896444d1fc0e446782e013d887838616108382d00ae00002ef6b942af94009324411f10de86442d3138885c37e17308a02c80a400002ef65d52b5947097845e2010e806802e514108a03b017a08d02d80aa00002ef5fe42c814d09ae47720b0eb86bc307157890c3c818b09703340ce00002ef5a302a893c893c43e1ef8e386622db13d88943a016908782dc0ae00002ef543b2cb94ec9b246f2068eb86862e114108a839416f08882d00b400002ef4e872ae94209604491f40e3867a2da14208a03a817408d82f00b600002ef48a92bf949498a4681fb0e786742e0142089838016108502d80ac00002ef42d32ba148c9904722080ea86962ef14c88d03b017d09103040ba00002ef3d092b6145897e45f1fd8e7467e2db13f88a839a16d08a02c00a600002ef371a2c4948c97c4621fe8ea06962ed14708dc3c417e08b02c80c000002ef31692ac140495a4581fe0e6c67a2da14488983ae17e09083040bc00002ef2b962b914209564501f48e2c65e2dc14388e03a616c08902c40be00002ef25d42b294289484501ff0e9468a2e7141086437417008682cc0b600002ef20142b894689844702058ed46aa2e214388a03a017008582bc0b000002ef1a522b194109584541fc0e7867a2e914388dc3b217a08902e40ae00002ef148e2b9142897445a1fb8eb06a22f514f08e43bc18209783200d600002ef0ea02ca94c09ac47d20d8ef86be2f914b88e83b817f08e82f80cc00002ef08d92b093f494c44c1f48e406642d914008b03a617708c02ec0bc00002ef02f92c3947c99046f2070ed46962ee14688b439817208f03200de00002eefd492af140494e44c1f90e7066c2e814288b03a416d088031c0be00002eef7532d114ec9a247720a0ed06a82fa15109103c818b09583140c200002eef1502d395449ee49721a8f206ee30b15689443d018909282fc0c200002eeeb8f2b6943096a4642030ec06a22f114a88e43a817008782ac0b600002eee5e72ac93fc9464481f30e2464e2d5138887838a16b08a02cc0ae00002eee04f2a213ac9024301e70de06502bd132085438616308282800b000002eeda752c294a899e4732048eac6a02f114c08f03c617f09383300ca00002eed4b42b213fc94444b1fa0e486622d213c887038c16d08a02c00bc00002eeceeb2b7945897846a20a0ea46882df14688b83b418009283180ba00002eec9152bc14849aa47620b0ee06ac2ff15309343d619509003140b400002eec3722a393c09324311eb0e246702e314908d83a416e08903080be00002eebd9f2bd148898c4622040ea46ac2f914d88cc39816b08282bc0ae00002eeb7ca2c1947899247020b0ed86a62fb15088f43ce17f08903080d600002eeb22c29b938c92c4361ee8e046302b71348850394171083829409600002eeac652b7941095c4521fd8e806982e914608a439c17608d82ec0b800002eea6b22ac13f09384451fb8e606a22f514988f03ae16f08882e00c800002eea0f32ae93fc9384461f38e3c65c2ce13e889439616908a82e80c600002ee9b242b8943097445e2028eb067e2e813d886c37816208582b40aa00002ee955d2b794209464441f70e386562ce134883434e15608202d40b000002ee8f9e2b7147099e4661fd8e846822ed14c88d83b217e08e83000b800002ee89ed2ac13e094a44e1f88e4c66e2de141086c38217108702f40be00002ee84162be147897846b1fc0e606742dd14408a439a17008c82ec0b800002ee7e432ba94489724601f98e846822e613f088c39817108a02e40b800002ee78482cd14d89be48a2180f3c6cc30514f88dc3a617309103100cc00002ee727b2b6145097045c2058ed86b82f314808f43c818209102ec0aa00002ee6cd42aa942c95845e2050e8c6882e514888e83ac17308e030c0ce00002ee66fa2bb944c9664491fc8e606662d413d889c38a16d08982d40b000002ee61332b5941c9584561fc8e446622d613f888839617808a82e40be00002ee5b662b7147896a4571fa0e546702de13d886838016c08782d40aa00002ee55902c314a499846a20e0ee46c630915308fc3d018009203040d8000)) else (if i < 494 then (if i < 493 then 0x2f135ef2c794d89d24832168f4c6ee30e156092c3cc18909483480d800002f130072c2149097e4631ff8ea469c2e614988a839e16c08b82dc0c200002f12a142c614bc98e4742100f306d031015809043cc18709583340c400002f124352c3147c9704551fe8e8c6962e814888c83a017008b82d00b200002f11e702b3940894a4481fd0ea06ae2f814988b03a817008782e40bc00002f118a92b8944c94c44b1f80e486762d813a086c39417308982dc0bc00002f112e22bc147897a45f2020ea869c2f314a88d03b217708c02c00aa00002f10d252b1142896c4531fa0e5c6702e1147088c38c16908402d80b800002f107512bb147c98245c2028ed06a02ee14788dc39416f08b82cc0b600002f101602c994f49aa47220a0ed06b42fb14e08e03b217b08a02c40c000002f0fb9f2ad93e093e4421f40e5c6802de13b086438216c08802d80ae00002f0f5aa2c6149498845c2050eb46a82fc14a08f83c218709082fc0c200002f0f0032a493d89384481f80e4c6862ec14788ac39417a08902b40b200002f0ea5f2a493b091043d1f10e1065e2d714288a839817608e02e80bc00002f0e4812be948098646720c0ea069a2ef14688d83b617c08a82ec0be00002f0debd2a913e09264351ed8e1065a2cd139886c38216708982d00a600002f0d8f22ba944895a44b1f98e746942ec14908d438e16808b02cc0ae00002f0d3072c894cc9b247720e0ee06b62fa14d09003c017a08e82ec0a600002f0cd292bc14549724591fd8e706822df14088b43a216b08902cc0b800002f0c7822a593b89324371ea0db46282c3132884c37816307e828809e00002f0c1de2a413a490e4341ed0e086662d6135884838417508a82d00b200002f0bc2e2a913f09464481f58e3065a2c913e889438a16a08882c40ba00002f0b6432c994b09964662008e886962ea14808cc3ac18208f83040c800002f0b06f2b3143897045f2020e906862e6142886035e15607a827009800002f0aa952c0149c98c4621fd8e506882e613f08a039c17608b82b40ae00002f0a4d82ae943095844f2040edc6902dd13a885c37816307f02ac0aa00002f09f092bb146097e4561ff8e906982e914708c43a417308302c00b800002f099352b894449684571fd0e846722dd143089c38a17208b82f00a000002f093812aa93bc9204311ef0e4466c2d713c089438e16e08c02fc0d000002f08dbf2af14089484461f70e6c6842ef14588983a2179090030c0c600002f087b62d114f899447d2108f2c6e031115108ec3be18709583180b200002f081f42b8145c95a4551f30e186462d113f887838a16a08b82f00b600002f07c382b5140894c4421f38e286602cc13a085838416708682a00b200002f0764f2c814d09ac47720c0ed06a22fb14e88fc3ce18509a03440c200002f070892b7145c9604501fe8e6866a2e214388a839417208882c80a200002f06ad82a793d893844a1f90e3c6562d813f887c38216208602ac09c00002f064ec2c5149499646a2048e8468c2e1143889838e16d08382e40a800002f05f192ba94709824601fb8e8067c2e714a88f83c418c09703540da00002f059632ac93f09384451f58e1c65c2d713c087c39617308c82e40c400002f053b02b1942895e4601ff8e4c66a2d3136886837214b07c028009800002f04dd02c494cc9c047f20e0f0c6d230d15709443da19209683300d400002f047f12be949c98e4581ff8e6c6762d313f08a038a16a08b82fc0ba00002f0420c2c594a898c4632060e9c68a2ec14909003c817e08b82e80c400002f03c302bb14849724622010e9467a2e414988e43ac17909003000c000002f036742b3142c95044d1fb0e7067a2e914888ac3a216f08b82f00a600002f030a32bd147898846e20d0ebc6aa2e314a88e039c17208d03080c000002f02af02a713d09404391ee8e306622e214188b839a16808702d00c000002f0252a2b7944c98e4721fe8ea06ba30a15389283ba17909302f80d800002f01f332cb94c09a247720e8f306be2fd14b08e43bc18609282f80ce00002f019482c514bc9b447b20f0f1c6dc30f15109283da18f094830c0b600002f0138c2b0141493643b1f60e486742e1143888838417308582b00b000002f00d892d715249d048220d8f0c6ba2f814908c43ac18209583300c600002f007be2b5144c97c45c2018e9067e2e714808d438a16508482bc0b600002f001f52b5143c96e45a1fe8ea46b02f815008d43aa17f09002f80a200002effc2c2b994249584531f78e2c65e2d013b886439416508182940ae00002eff6732b1942495a44c1f60e486602cd13c886438a16d08902bc0b600002eff0ad2b013e09484521f78e6067c2d7144088c38416108402d00c200002efeadc2b614389524491f98e4c6682e614788c839817609283100be00002efe50e2b4945896a4652010e7c67e2ec14208b439416b08702cc0ae00002efdf352c214789824602040ed06a02eb14688a43a416b08a02e80ba00002efd9582bf949c9aa46e2078ecc6a82f514908ec3bc18209083300d600002efd3b32a4139c9124321ee0e086582c3137084c37616008702e80b000002efcde22b8147098045d1fe0e8c6822e6140887836a16208602e80be00002efc8082bb94a89844612020ecc6b62f314b88b43b217808c03180d0000 else 0x2f2a93c2af141c93c4441f30e1864a2d013d086037e15a08582c80be00002f2a3b029493408d84111e20da06282b5131884837816908482f00b600002f29ddc2be14749764662020ec46a82ea14808e03bc17f08c03000c200002f297e52d014fc9c84812168f186ca305152093c3d418b09383140ca00002f292362af14309544501f58e346782de14008a039816f09083140ba00002f28c812a913f495444c1fb8e606822e614688d83a217a08b030c0ca00002f286d42a713dc9344431f90e546762dc143889038816408382cc0a600002f280f22be146097845c2000ecc6b6301152893c3e619509883000c200002f27b292bb945c95c4491f38e4868c2ea14388c43b817508f83040ca00002f275562b994449664581fa0e4066c2d913d888438e16608682c00b600002f26f932b4141095e4591fb8e8067a2ec14a08f03ac18008f83000cc00002f269a72c714cc99a4702100ef46a82fe15009043c218209283240cc00002f263e62ae940c9584531fa8e786762da14608c43a217b08e83140b400002f25e302ac93e893443c1f18e6467c2da139883c36014c07c027009800002f258582bc145c9884641ff0e946882f014888dc3b417008902fc0b200002f2526c2c594a49a04772100ee86b82fa14888b039a17108b82f80c000002f24c8a2c714cc9ba47620c8ea46a62f814a08b439816d08482a80a200002f246ae2c0145896e4602058e9467a2ea14608bc3a817e08f032c0c200002f240fe2ab940c94a44f1fd8e5466a2db140089c39217808702ac0b200002f23b2e2ba944c9644551fe8e946882e414508dc3be17b092833c0d200002f235972a313ac91c4331ec0e1066c2d913e087038416908982f80c200002f22fc92bc948098e46c20b0eb06a02ef14c89143c418008e02fc0c000002f22a0a2ad140493c4481f90e646882ed14388c03ac18809103100bc00002f224132cd15089ce48a2198f5c70831915c09443e418f09383240d200002f21e522b714289744582000ea46982f314e08dc3cc18009082e40c600002f218502ce94dc99c4722060ed869e2f015009183c818909583180b000002f212852b494689744622040e9468e2e514108d03b617908a82f00b000002f20cbf2b5942897645b2050eb06842e914908c439817408902f80bc00002f206e62be94809884702028e8c68a2d413b889039a17008b82ec0bc00002f201132be14749824662050ea06a02f814f89143c416f08b03080ca00002f1fb442b414449504541fe0e9c6842ec14808c03a817d08a82c80ba00002f1f56b2be14749824652028e986a22f014d08f43bc17b09183280d000002f1ef912c114a899c46c2060ec46922e114688903a416e08c82d80a000002f1e9ef2a213ac9364451f48e546762e0144889038c16108682c80a800002f1e3f22d014d89b846c2050edc6bc30715309143ce18409283240dc00002f1de0b2c4148497444c1fb8e4c67c2e2142889439c17508b03100ae00002f1d84d2ad93e093e4471fa0e546702e314408a83aa17b08e83040ce00002f1d2872b5142895244a1fc8e5c66e2e714588bc3be18208782dc0a600002f1cca82c0947c97c4672050eb469e2f214988d83c617e09083240d600002f1c6c92bd948899047220d0ee46a42f414b891c3be18b09a83480ca00002f1c12a2a193b49144321ee8df46462c513c086438016a08082c80aa00002f1bb672b8143c9744602010e806882e514989083b217208c02f40ba00002f1b5b62af13e493e4471fa0e386502d2138885839416f08602b80b400002f1afc02cb14c499a4632040ee06a62e914908b439617108e82f40ba00002f1a9f42b7944496e45f2020e9c6922e2141889c39e17108d82fc0c600002f1a4192ba14489724612018e906942ea140888438c16808582bc0b200002f19e542b4941495245e2070eac6982ee14c88dc39617508f83180c800002f198942b1942c9544562038eec6ca30515789103ca18d09002ec0ba00002f192d02ad93e09424461f08e706802db13e886438017008a02dc0ca00002f18ce52c814c09aa47c2060e9869630614f08e03b618a08f82f40b400002f187492a293d493444b1fb8e4866c2df14a08ec3c418309002f80b200002f1816f2ba14649864672038e946942e914788bc3b818808e02ec0b400002f17b9c2bb94449604481fb8e546762e614208ac3a617808f03080ca00002f175e42b0941493e4401f40e286442c9139886037816c08802d40ae00002f170142b1142c9684541ff0e6c6982ec14a88d83b017b08c82f00ba00002f16a0e2d2952c9ea4942190f2c6e230215209243d418f09282dc0ba00002f164412b3141c94844b1fa8e3c66a2d813d888839616c08582c00aa00002f15e7f2b7146898a4752120ef46a62f314b88ec3c817c09103000c400002f158d92a013d892c4331ed0e0c6482c3134084c37a16808182940a200002f153092b714589864621ff0e746702d9140087438e16d08b02ec0c000002f14d4a2b213fc9364451f48e446602d1139085c37c17008882f40be00002f147592c994c09a847c20c0ec06aa2f714d08e83b617b08e030c0d200002f141b62a393b093242c1e28de46462cc13a889439616a08782dc0c200002f13bdf2c094a899046b2048eac69c2f314888e03b817708c82e40ae000) else (if i < 495 then 0x2f41b8d2ae93f494644b1f58e4867e2e213b887c38a16908902d00a600002f415bd2b3142c9664551fd8e886922e514388cc3a216f08582bc0c200002f4102e299937090442b1e38ddc63c2ce138086838016308702bc0b000002f40a7a2b393f89544531f98e586742d513d08943ac17308782c00ae00002f404ac2c1948c9844621fe0e806902ed14f08f83ae16a08682d80be00002f3fedd2b694749804642058ea86b02fc14c88f03c417e093030c0c800002f3f9142b2143c9684541f60e4c66e2da14188883aa17e08d03040ce00002f3f3542b3943095443f1f40e286562d313f088839a17008b02f80be00002f3ed892b7144c98447220c8ef46ca2fd14a88ec3b417908682d00c200002f3e7bb2b5143c98645c1fc0e546822e013e887038815c08282c00aa00002f3e2082ab940894244d1f68e2c6522ca13a886c38416808402c80b200002f3dc572a993c89244361f48e4466c2d713a885436a16508a02dc0b400002f3d68a2b7947499445a1fa0e8468c2e013c08a039416f08502c40c400002f3d0c32b5942c9624592028ec46982e914788ac39016908582c809800002f3cadc2c514b099447820e0ec46a62f614c890c3cc180091831c0c000002f3c5262b014249444562010e846962eb14588bc3a017708e82fc0bc00002f3bf5d2b4943895a45e1f90e346482cf135881c34a15808382e80ba00002f3b9952b794709884722050ec06a22fd14c08ec3a617908e83140c600002f3b3d82af13dc93a44b1f20e246562da14388a03ae17308a02dc0ac00002f3ae292aa93d093843c1ef8e0462c2ba12e883838616808582a40b000002f3a8772ad140895644f1f80e2c6602de1408898382169085029c0a000002f3a2a02bb145c9804581ff0e646742d313a084838616d08902e00c000002f39cef2ab13dc93c43d1f38df06422c3135883836415c08082b00a800002f396e72d1952c9d848a2120edc6a82ef14b08c039c16f08903000ba00002f3911f2b7144496245b1ff0e6c6882e714908a037c16c08702b809c00002f38b492b8941095043a1ee8e1c6562cc135883437216b08602a00a000002f385572cf94cc9ba4752068ea46a02ed14508a83a817708d03000ae00002f37f5f2cb14b49a247a2088efc6be2f814a88c83ae17a08f03080b400002f379862be94889764521fd0e986942ed14688d83b817b09283100cc00002f373eb2a7941495c4531f80e7868c2e814b08d03ae18709282f40c600002f36e0b2c4149498e46b20b0ee86ba2f014f89083c418308b82e00b800002f3687a29d939c91843a1ef0e006422cb13887f835c15508482e00ca00002f362b92b994609724551fa8e6867c2e714608c43b017f08f02f80b600002f35cf22b5144496845e2008e9069a2ea14a08f03b017c08f82dc0aa00002f3573d2b2945495e45f2008e8869a2ef14b88ec3b218808f83040cc00002f351612c1949c9a447a2088ec46a22f314c88d039e16c08f82f80bc00002f34b832c994e49da4852158f346da31115608f839a16b08602ac0aa00002f345b42b9945496c4571fe0e7867e2e4144087439c17308c82f80bc00002f340002b313f093e4451f58e486742e214988f439e16b08802d00b600002f339fb2cf14d499846e2078ed86b42fe14e09283ce19009983300c200002f334522a293c89304401f80e2867e2e614708c43ae17308902d80be00002f32e722c0948498846b2088eb46a42fb15009083ca18008d82f40be00002f3289e2bb146498645e1fd8e8068c2e314888fc3be18609203200d400002f322e52b614449724622018ea86822e714888b039016408582ac0c000002f31d242b6142894c44b1f78e7869a2eb142889038e16c08a02f80be00002f317432c394789784562020eac69a2f614c09083cc184090830c0c400002f311a22a793c092c4461f70e5066c2dc13f087038e16708702e00be00002f30be02b894589864632008e9869c2ea14708b839e17309202dc0bc00002f306052bb14909944622020e9c68c2e214688a039016908a82e80c200002f3004c2b0941895c44b1fb0e3c6602dd14108a43a616908502c80a600002f2fa552c914c89b84722078e9c6aa2fb14c89043ae17f09383180c600002f2f4642c894a898e4702060efc6cc30315309243d818808c82cc0b400002f2eeb22ac93bc9284471f68e286782e3143889439417408f02fc0b400002f2e8db2c1147c9864631f98e8c69c2ee14888bc3bc18409182e80b600002f2e3102b2943c94c44e1f20e2c65a2e114008983b217108c02ec0ba00002f2dd472bc146c9724541fd0ea46902e914908e43a417608b02d40a800002f2d7682c414c099e47220c8ed46a22f415088e83ba18008c02e80b200002f2d1a02b4142096c45f2048ea86822ea14308c83ac17408e82d00c800002f2cbe22b5142c9644531f80e6c6862f314a08f03ac17b08c82f80b600002f2c62b2ab93f89564401f70e4066e2d7140089c37c16608382b00a800002f2c05a2b614049564571fa8e446662da14288a439c17408982e00a600002f2ba962b2141094644a1fa8e5c66a2d513f88c038416408902dc0be00002f2b4c32b794609664531fd8e746862ea14388a039816c08802d00a800002f2aef82ba147898a46a20a0ed46b62fd14e09003bc17108602c40ae000 else 0x2f571e40000000000000000000000000000000003cc17e09282e40c000002f56c112b6944c96e4572020eb869a2dd13b089039017908f83040ca00002f566462be148498e46a2058e8c6942f414b88d83c018209082e00ba00002f560782c394a098845f2028ea868a2e814a08d03c018309403300c800002f55a8d2cc14e09ae4702088eb86ac2f014808b839e17708c03180c800002f554c12b7143094e44e1f98e486482cd135082436615708282b40ae00002f54eeb2be149099245f2038e9c6942e414408c039c17108a02fc0ae00002f549302b293fc91e4351f48e3c6722db14008a039a17808902dc0c200002f543572c1948498046a2038e906902df14408bc3ac18209103080c000002f53d6b2c594bc9ae47b20b8ed46ae2fc14f08f03d018309403080c200002f537a32b8943494e4511f78e4c6782d713f08a037216308682cc0a200002f531c22c414889a64752078e9c67e2db14408b43b417908e030c0b400002f52c162a4139c9204371f20e5c6742de14588cc3ae17508b02d00b800002f526532b5942094c4511f70e346622d713f888c39216a08482ac0a600002f5207b2bc147498246920a0f006be30514c88dc3b218309583200b800002f51aa32b7943096444e1f78e486802e314808d83a617808d03040c800002f514db2b5947497c4571fb8e7c6902eb14608b43ac17908d03100ac00002f50f0d2bc947098846c2078eb06a62ed14b88fc3b217b08d83040c400002f5095e2ae13f09424401f78e5c6702e714308b038c16b08d82f40c400002f503b02a913cc9264341f10df465a2cd134085038616408282d80b200002f4fdd22c4949098c45a1fa0e2c6582d413d889038416908d02e40b000002f4f8092b794649844511fe8e846922e513f889838816408302bc0ac00002f4f23b2b6944895e45a1fe0e606742da143088c39217b08c82f40c400002f4ec6d2c494d89b04872168f306dc31615f09703f219509d03000b400002f4e6872c314d09a847520f0ee86b630515209303d818f09683140ce00002f4e0b82be94689884682080ebc6b42f214a88e43b217208882e40b600002f4db2329e93a890c4391f28e2065c2cd138889c3a217008b02d00bc00002f4d5312d215309d44892188f286d430315a09743e818f09203000c800002f4cf7f2b1941c95a4491f78e546802eb14588a839616b08802c80c400002f4c9bd2b694289664521fd8e7c6922ed145888437c17608a82e00b400002f4c3dc2c694a49864652080ed06bc2f814988bc39217708802b40a600002f4be122b5143096e45b1fe8ea46842ea144887039617208882e00bc00002f4b84a2b7144096445d2008e986882db13d888436a16308182a009a00002f4b27d2ba944495644e1fa8e706922f114f08e83c618309183040ca00002f4acbf2ad942095644b1f68e2865c2d8140889037215e08602e00b200002f4a6f52b9147c9864631fa0e7868e2fd14b89003ca19509302f40c400002f4a1302af143896c4551fe0eac69c2ea14a88d83b618409003140d200002f49b762ac93ec91c4331ef8e1864a2c3132084838016808682d80ac00002f495972c194a099e46c2080ec06a62ee14708cc3ac17308d02e80be00002f48fe02aa13f894c4461f58e3866c2e114588b43a8177090831c0c400002f48a0d2ba947c97e4602030ebc69e2ef14608cc3a616a08782dc0b600002f484382c1147c97a4682078e9868e2e714008603a416e08a82dc0be00002f47e6e2bc146c96444f1f80e106642d113c086037e16d08482e00ae00002f478b32aa942094e4551fd0e7068e2ed14908c039416308482b40a600002f472de2b5945095c4581f90e7c67e2dc140889038415c08582ec0b000002f46cfe2be946497645e2028ec86b22f514608f03b618c09503000cc00002f4672e2b8943096a4591ff8e886822e514708b838616908282c00a600002f461572bb947499446e2078eb069a2f615088fc3ba182095032c0ce00002f45b772c1949099a46e2090ec869c2f814d091c3d618008c82d80be00002f455ae2b9941c95c4571f98e7066e2dc13e888439416e08d02d40b400002f44f962da95649f04912140f286d430a154891c3d218209302fc0b200002f449f82a2939c92642e1e80dec62e2c1130881434e15c08082a409400002f444182bf948899446c20d8eb86ac2f515109143c817e08e82ec0c200002f43e1f2d215189c44892110ef86aa2fd14e09283de185090830c0ba00002f4385b2b514389564572010e646662e013f888038c17808e83080c600002f4329b2af142096645f2040eb06a02ed147886839a17208982e40be00002f42ceb2a613d49284441f80e206482c2138882c36016f08c82f40c000002f4270b2c294bc9a24742058eb069a2e314808c039e17708682b40a800002f4213b2bb14789924681ff0e786842e1146888038216508582b80b2000)))))))))

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



private theorem b494670 : covered 494670 494794 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b494794 : covered 494794 494918 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b494918 : covered 494918 495042 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b495042 : covered 495042 495166 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b495166 : covered 495166 495290 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b495290 : covered 495290 495414 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b495414 : covered 495414 495538 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b495538 : covered 495538 495662 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b495662 : covered 495662 495786 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b495786 : covered 495786 495910 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b495910 : covered 495910 496034 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b496034 : covered 496034 496158 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b496158 : covered 496158 496282 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b496282 : covered 496282 496406 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b496406 : covered 496406 496530 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b496530 : covered 496530 496654 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b496654 : covered 496654 496778 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b496778 : covered 496778 496902 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b496902 : covered 496902 497026 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b497026 : covered 497026 497150 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b497150 : covered 497150 497274 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b497274 : covered 497274 497398 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b497398 : covered 497398 497522 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b497522 : covered 497522 497646 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b497646 : covered 497646 497770 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b497770 : covered 497770 497894 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b497894 : covered 497894 498018 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b498018 : covered 498018 498142 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b498142 : covered 498142 498266 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b498266 : covered 498266 498390 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b498390 : covered 498390 498514 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b498514 : covered 498514 498638 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b498638 : covered 498638 498762 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b498762 : covered 498762 498886 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b498886 : covered 498886 499010 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b499010 : covered 499010 499134 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b499134 : covered 499134 499258 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b499258 : covered 499258 499382 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b499382 : covered 499382 499506 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b499506 : covered 499506 499630 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b499630 : covered 499630 499754 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b499754 : covered 499754 499878 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b499878 : covered 499878 500001 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b500001 : covered 500001 500125 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b500125 : covered 500125 500249 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b500249 : covered 500249 500373 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b500373 : covered 500373 500497 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b500497 : covered 500497 500621 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b500621 : covered 500621 500745 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b500745 : covered 500745 500869 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b500869 : covered 500869 500993 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b500993 : covered 500993 501117 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b501117 : covered 501117 501241 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b501241 : covered 501241 501365 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b501365 : covered 501365 501489 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b501489 : covered 501489 501613 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b501613 : covered 501613 501737 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b501737 : covered 501737 501861 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b501861 : covered 501861 501985 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b501985 : covered 501985 502109 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b502109 : covered 502109 502233 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b502233 : covered 502233 502357 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b502357 : covered 502357 502481 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b502481 : covered 502481 502605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b502605 : covered 502605 502729 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b502729 : covered 502729 502853 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b502853 : covered 502853 502977 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b502977 : covered 502977 503101 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b503101 : covered 503101 503225 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b503225 : covered 503225 503349 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b503349 : covered 503349 503473 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b503473 : covered 503473 503597 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b503597 : covered 503597 503721 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b503721 : covered 503721 503845 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b503845 : covered 503845 503969 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b503969 : covered 503969 504093 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b504093 : covered 504093 504217 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b504217 : covered 504217 504341 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b504341 : covered 504341 504465 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b504465 : covered 504465 504589 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b504589 : covered 504589 504713 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b504713 : covered 504713 504837 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b504837 : covered 504837 504961 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b504961 : covered 504961 505085 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b505085 : covered 505085 505209 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b505209 : covered 505209 505333 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b505333 : covered 505333 505457 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b505457 : covered 505457 505581 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b505581 : covered 505581 505705 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b505705 : covered 505705 505829 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b505829 : covered 505829 505953 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b505953 : covered 505953 506077 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b506077 : covered 506077 506201 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b506201 : covered 506201 506325 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b506325 : covered 506325 506449 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b506449 : covered 506449 506573 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b506573 : covered 506573 506697 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b506697 : covered 506697 506821 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b506821 : covered 506821 506945 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b506945 : covered 506945 507069 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b507069 : covered 507069 507193 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b507193 : covered 507193 507317 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b507317 : covered 507317 507441 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b507441 : covered 507441 507565 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b507565 : covered 507565 507689 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b507689 : covered 507689 507813 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 494670 507813 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b494670 (joinCoverage b494794 b494918)) (joinCoverage b495042 (joinCoverage b495166 b495290))) (joinCoverage (joinCoverage b495414 (joinCoverage b495538 b495662)) (joinCoverage (joinCoverage b495786 b495910) (joinCoverage b496034 b496158)))) (joinCoverage (joinCoverage (joinCoverage b496282 (joinCoverage b496406 b496530)) (joinCoverage b496654 (joinCoverage b496778 b496902))) (joinCoverage (joinCoverage b497026 (joinCoverage b497150 b497274)) (joinCoverage (joinCoverage b497398 b497522) (joinCoverage b497646 b497770))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b497894 (joinCoverage b498018 b498142)) (joinCoverage b498266 (joinCoverage b498390 b498514))) (joinCoverage (joinCoverage b498638 (joinCoverage b498762 b498886)) (joinCoverage (joinCoverage b499010 b499134) (joinCoverage b499258 b499382)))) (joinCoverage (joinCoverage (joinCoverage b499506 (joinCoverage b499630 b499754)) (joinCoverage (joinCoverage b499878 b500001) (joinCoverage b500125 b500249))) (joinCoverage (joinCoverage b500373 (joinCoverage b500497 b500621)) (joinCoverage (joinCoverage b500745 b500869) (joinCoverage b500993 b501117)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b501241 (joinCoverage b501365 b501489)) (joinCoverage b501613 (joinCoverage b501737 b501861))) (joinCoverage (joinCoverage b501985 (joinCoverage b502109 b502233)) (joinCoverage (joinCoverage b502357 b502481) (joinCoverage b502605 b502729)))) (joinCoverage (joinCoverage (joinCoverage b502853 (joinCoverage b502977 b503101)) (joinCoverage b503225 (joinCoverage b503349 b503473))) (joinCoverage (joinCoverage b503597 (joinCoverage b503721 b503845)) (joinCoverage (joinCoverage b503969 b504093) (joinCoverage b504217 b504341))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b504465 (joinCoverage b504589 b504713)) (joinCoverage b504837 (joinCoverage b504961 b505085))) (joinCoverage (joinCoverage b505209 (joinCoverage b505333 b505457)) (joinCoverage (joinCoverage b505581 b505705) (joinCoverage b505829 b505953)))) (joinCoverage (joinCoverage (joinCoverage b506077 (joinCoverage b506201 b506325)) (joinCoverage (joinCoverage b506449 b506573) (joinCoverage b506697 b506821))) (joinCoverage (joinCoverage b506945 (joinCoverage b507069 b507193)) (joinCoverage (joinCoverage b507317 b507441) (joinCoverage b507565 b507689)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 494670 ≤ index 950000000/512 := by decide +kernel
private theorem starting_value : fast 950000000=48431471 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 950000000=48431471) (n : ℕ) (low : 950000000≤n) (bound : n≤975000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=950000000
    · rw [first,anchor]
      exact starting_value
    · have past : 950000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤975000000 by omega)
        have within : index n / 512 < 507813 := by omega
        have lower : index 950000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤975000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ950000000To975000000
