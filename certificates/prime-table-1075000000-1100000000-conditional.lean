import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ1075000000To1100000000

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




private def radical : ℕ := 0xa2083b0f24af792142df42b0261e414142e7ac9e325aa3547e7ef6e4150288fc9486cca44100f818cb71b85a70bc949a2146fef78f4fc3a7cc25c8c8b0742e610bbacce8fba4db37abf67bec5155ab8bcf6afaa9ca32ffed342f332b2e5b74046e7cf9548dc870c0d982856069e85e0ad3c9423f882ffbe5617e5ac3e640224a8a6f6c0b35cf30c8e5c47fc9c56ef62b67f2b9c66510c277a3068329d12c6a17133bbab84766d716cba93675258c64a6fee43efbb5a5317af51b7f1a7a24eca4886e512a15044937e980b1b9e992c9e8e987ab6baeedd55a50d386bd6b2a17aacf6a6a2ef7a858f41c8222be52cbd953efedfd0aebde51c785052289dfdc404c271015aef09861b2c7fe5dedaa3118188c0581fc0ea4bc7abbdb55f80b8f6f0ca3633897bc74f64d5ad0eed8dcf463cf5f181f167a6e27e43b93e1ea1031e05233ff2c7a1fd7feeeac623e7b33138015544c0e8a5ec75a7ebf103a3e1067091dc003d0bbeafc8081561cf4246f0e4c151d41e1308d15739a9766aa9c67c7853c816bdf23a5624b03f88a5adeb75e34271e1f0befb22f6d5a1ea8f7bfebfe9643deee99c4cf8058efae73b0dfeb9704d36ec89d956260cb5c1bb9267d05c0a05a1910b973838903e40c0f604520709ce1783cb72d1bd6c0bf14a4d1a6eabe32404167bc5078a4f6112744125d9d460fab0056269a6caf6fa383768a613de2e4e1b8233b2bb4ea2c403106fb8f921123625fbdd9a37983c1e2b36a7082c0358aa76f56f838ef7e7a3ca0e334ce7a2a66629a4a9b7ef9226fdb6838e0f48e8902bd6ab0c91a17074f798ffe190fc5cdfc16b0fa38a545e0a2f4cb70feb179b1db7c7d4b21434f809ad85be2f23e85279012df7ea995e7bc649362c2a930139ef2b29de34bebddb4f90862463bc62e37cf75848a9fc46b643a4e4ad3df20f7f029a262c773732839cc2db535b0c186d9cfa7814c6de4732a2376546ab11a55f7604c2e95fc9fd06bc47c757278e50dcebb92c6acbac73f079cb12d1210b643229c5bd57c2a7b2401b9f6615840470c81b75eca90886418c659f4351989fa920b50e80763be5c8632d7cf1f9afc933c27c175b8384992a5c9bf4b4a6b4e4aed8da97f9843e6f384ee9a8077c81f22e71a47464c4ee20cb1e76c68baf643e3898d9ef4f13a58eef51c240f653a5c3c4b1460fb9ee3a0bfc1f4f3a403ad5eb557f1820195af8e427f01fa9946add9d2bd3ba3eb5064f73d51d2f0dca9dc534e40e352681d105ee97c744bb580acdce4cc718d2656abb77ec31b5fc4ef04e1e5e68de4e189697eee6971bef647898acf53b1840dde9500e1d00655c8b3875914527cc103ce4c5ecf68d388d94d70b238e20e72da4f0492f293b7f4ea85e1e5e4a7fe6998ca562c6b5c0f276b9ac090152b428ff1d24b5a6853940b994a826d4f49148e54a2c5271692b0bde05126a3402ed558809805a793a2ba7887bc3baea749d6362c14f5ea5ba2d379047ca458dc0f2c3319612157a341fc4ccc2be2e28c4d6f9130d90f9478e4dfc31da2afa8f55c8ecb17a6beb96b3e799c20f9d22017c25bbde47157737e15c42f7ecdabf81b210eae496eff1db63fb2ad094b47c6bce6fa52855e9d0d04f3d7314bc5e05cf7115a316e1499ba28cf694c499f72c9c263a1b634713484eda324452ce1a3ab49e5271da01ce7e1bb0547b330e390802da12cf90361337f039c112b1ad9e91bd260aecea61638f252412b3cfcc8d23511264952b23efea4fe59b47940591b24aedf6cb4403c70f4809a31d1ca2e42e78fb887810ea977006a5fecc934e68e6172c0b51af6f6ee7787aa600e23a24219f60c75ccefe8919173a48591e72ef374809b952e38f3cfec251e0a227b63d11751240a0f2b22ee71ee49abca1c3aa91af2aa30fd5fa2e9228738d3c43de2695828e748320976d1a494272f64b5dc66ae68a69417a9e933ace969e8f432eae62baac9afbf37ad392e5384e3b86f44b03c933535e47aaabd0d43166fad0679d502621a18f8ffde43b39eba056c00388ba1b349ed9dcba3fed397084961917013b9d3aef28bc1b01e88f1539bb19798bc1292b1cc1e97df8faea1339f93f28f2c30b0e7033d04fba98bac6f127c583b00fcd3decec8edb621023bc962336f90cb17b938933b430a6bd905214caeca0112eab2d2c2a930eee298ba3495ffd38730585b4b5d93224da4f853705fc04afb72d35da167a544bbb7bc32a3b934081a3861314b9029fd48442c1acd973449bf77683220883ee83de5ed99e7f69dd30905d030cc6fe4c07498cc16e613e3f6e5d266d4a3ee4d2f424a8a4ea3fbc3de07813ac2570692cbaeb6a349ba15c4ed01d327d58469f98ed0a795f9d9b27725f6d532ece0068cb6c1211fcfdb4a7eae04c52abe28cf54301137e09259fa88b55e2d305df0173f69f151359242f501dc6448e0b30f681a21e0273a09673e7efc11ec69a5a08b29aeeaddd5ec24817ed1334ec84efe8c744d92015643c5b7464f73411f92f2a53d3af930a98afa97f46e3bb5156c402d13f9f58192b56b175cc11aea9637b84d14936abd1151e4b77841d0901a2e439449be35af67e1a3bc144894dfaf644ab6c27a2a3cc60ef5fc1a4268a6509aa0a11f49a34e9fe8825790df196007e00aa9b80654547add92bb3bce37f1f7753c990b7c490959c54bb47d386ffcf674cfe339452edcf8ce37a6506d46c58a78811448e3cfacf4a258dbbeb10a0971f33d6b9206d40e6936a816b77174b39f014d24dd1040a5723b8dd5b543cdcb4619d15e4f635456b91d5050eced85727b3b26f7b808ea6c6d35c6bd05c4a473ef9d921eb0b1fbfb62de881b06d771c8e7f2c6bec4d7cae520694cd75cad8144b0be648b1c1e41a39c66fa90983af10966e8f80ec76a9ff7981fed42f9932b2739342fdfb9a7d0bb8c453e0b381d2d4e61dc7f4941e1b2f4aada27247346f37415c4053b0976ca1ad1d2d77d8f982b111a69004ba396f3859c05e44b70bf193ec550547cf2c5f6c14d28b92d91a291ff6ff3f135d0ebbdd7dccc77a03b103166fb398c7b622f091accc68240f2d987c855ceb7b0994bebf7d8efe29397d4d6db3ab0b356a82fd1bf284c93598e6d5f62cc5df64d7abe6b8f647508e2296d8663507badf8bf5f69702fc6e2f8c9305ac697929b339e038a850248319b8640f0670c7d1dcd5e884e1ae9cb89a5d1aaf14b9f87685a1780760f21f55737f9374cca3bbabd8f94262991b67c38c5d76ba8332d0d4b2b23a74f397a5edc435bb52e277c843fe056b2b813198cbe9518321ad4feeaed728ec87316f336ba1b971c2779fb4468eca04ba07c0aa2766100140f91f5bb692ff2f3be26a5f669fd0caf28d007c19341fff41dec9fe0e681ca4078b923c0be54f53e8996fdde44210e4aa45df5365a8ef6ad74036405fe60db714734ff2699f10a17201765e55037cba02fb2470e08e5e1fa93d87ec5c6140cfdc7d523705586c987a2156352f5fd529285d2dbfca1748f26807352fcd3cb0606a40a4ebb865f656b4c33e9c3d5681f7301daef2ef0dd3833f1a1b4d332e60f07725d34103febb60a0101a47f8a63301e3b3c0ae6c62046810b2a269d4645c68f8e65008ce7f9d88e65893f1291397415742ce4dc6ef7c1ee3dfd2f6cdeb485c2b1af3722c7297dd285437af49e1ac0fcde7cb6d9c22e8cd200e1ab67cf2fbcd00def15124aac3f94310cabe664df9cfc12e7519abe4a62048cca6310132878b4acb3e7c38d5788b339b4d5381cf557dae72b08fdaccd883aa345b3c305b42273ab864ea336dadd0d900e714905f79bf5fe77a9df39d8c6840d1a36f791e82f8b3dc43f97ec679f7d8cb8a16b9590e3377dca5b3078e5898a8c1a94a9398cbe0deb563bec8c018a2d9b256853a9c0cc9335ce19926165be70e5f1cb0ed5924a113b4eb296f1a9cd7390af49402aec929cf57a6cac7f76fb028876b6b3f17bf7ef0ccc29521eba00db9abd111add28bd2effee35514800ef258099dc3b0f52fa19e8da5e1810988dd56b914017d70d495ef83bb255750b54e69a7b078ab2fb94f2f790e017343a6240fcb0e0d1343bcfedc6e4c3e2c9ed37fe221eee6767994c971353ba83c29d9195ca0d2ba4990715aed373f49a7e71c6b631753cf6de747a626becf09ee69f2f3436049263cafd0bffc8fc0c80d725138dd16fe1f07c307e1633828d052095c86e88330181f03f1609563763403de727de75741f470fdff270fc879dbe375caf906df03031a1630a783ac4bed5b4ab0c5586ce7603e886e30534045ff286faf00263d2eb424c8d5f37cdcf2a04fb46b63df8f74670d5ff4412497fa0b0f411a35c9dec67d8e64490c0ee5e9d0fc9141ec19264b8c6c0b38696cb7db8e49319e9ec4b7eb3b82bb75f23b072f2d62282449ceae17e6bcc9a41902b06731b6cb4192d1226a78726f14c52060814c47fadc6b5cfa767d736802ead6a96461ab4a6d2ae1c4a3733801fef8adeb81e42a2bac80418756d23cd2b2990eabb068e62e8bb2174ba6b2988cec370e50ef405d11c10341e00aeffecffc8d45698766c702b44fe8eb9baef0b048a27eb5b78e66c71706c8eacbb47770109760abf353660d4a9e95fb9393b4872fa39203048fa5db874fd306d1700ae5a0c5e3fd2001605c41099cfe94582baf4b21f8c475dc674c212e5672be4b16fa792ff6ee838dad701bec03af3544ae1076a5a352224321db0a19a47da8a46cdcfb4a3db33ad81925493b218021b808ee6b1fc7af0450d8a99840c05c1917c2b41338271dfd55b35bb60b813857401f90ea90a63baec978eb329481bc72d57c82979002d92411ac68ed403f07950d3a762ed6f5cf6ba72bbde71f1ffba9d0b95c0e0d4fe654ba9ed5af9c23b2d5663bbb1f0e80848140606fe14ca90f0d7e6d86d2f4c02b46473731cf199ac38a5705bdb86b1d587a74993c5c591066635ae151a52715cb17ad73a4a85556284cd6617bfddc7b24c53c2d73c689b0888da3b911f472166b02e21e1d600b64224b4d6dd23b2c1ed169e80382f3958eeb31498924bc57fe22038b70649af93bc24536826761b8ae458359cbd5ada28aee207ca64faac55e8452b3ba969e1d783f85ed38598de008acece6096c1522149fd56053116a1e080f4ead9efb2a0714253589605aff6184dfde94c39e7c908345b46a671e6d16576e5bd70487a31be898d9fc96cb5be61d066697deb2d08f1aec201fcc017a438c47a24241eafdcd0dcee642c13226ddf258ec46d3ce78e0834320d9ba172282982c81f9ad9712b630e7902f45917a2f10e084f2a7adc64672bf2bc657c554db0f3c7c7854376913e520394f1f0371a15e8ed5d9730e63e77ae2960b67dec8f26464bc0037a390fe33c5f556e1e200261d8759e5245f4ce63b5b8141e1e56ea4693e74515ada2eeb311f8f451e879c0d92e810e4f0562f9abffbb713307919301d1fa042cc2c7380c5afae7ed97aaf040f6492e1df06f8fd37afd18d7629c2eb491d8856b94d88b4790646aeda44517de40c023ff7d6c56fd09ca38db4997f20cd1cf53c214337920e2f1fe10a5e357a2db5c3b168bf2e2f8ea7462508ef2882d330689e61a5ca9beb4700385e8c00ce9cb50ac87ce2796f379d39e503c5a0ca2c8c8094689f47e979a9a0f1cf0f2a211f38211542c0b9ab3df342efdab481b71b73156a44a78a7d470107ebace8956461406d6b9d6810416198785d4b9881e4f2bc70747b1e676fe8ffd095c1974d5c359a92a8693c17285ed96218f3be80370899dfbd3f68dc0663a9ddc09b5de76e904ebecf3edd79cfe7fb26c30e6341f0c37ec02cad68dab0b1ff1d0bd8563cb76e40ac345e8810829fc4999f325da8426cfe7ae85b0dec995d065b7b45eca1da96a0c942b3f454903aeb47dbbadc8f515d8c78d0999e22fe25ed72e28ddf89f026b71503378e90f1dd453f62f4e9e1d5f47e9466c32ec8186b362a4ad1e357480a4f8ff05c1ab33f2323ad0338bef4002c27301e19441137eeb31b1cc7aba51591aed84fd1ff4436d7c5c87c37b987c26abe838a7bdb238ac183281031540ad7d29a8668e494a632df799a233791a4f208869864f1aa5c7bc15b8ec704ab81665bcdde50af20e551af3a381fae2cec5689e81b34cb1f3b8f001d517fd92e23b12b98be0c38a89ab7cba80875fe79d7f07adf4660e388c485c5fd1facef132474fe85c278947d1c89a9cba09c6ca66d4ca2d71f2fa965161be5c5b66f01aa620db5ced5a2cca728d630395f9bad8626785b29fb864befddd9afbdf061409fea0885a10c61920392b4a3f1b1886ecb48da72891dd7a2ed822f8853af41b93ed94b080192d718e9cca83e3ad83953c5a9115b8070aeaec8de64a7e3eae7551d8dfded21acb589199d0069e8c71b802970f15ea1df4b8be61c79ea8852a2b763e18f77e6270e20ac7478a56f76a8e3a79225bd3239c6e3f3e379b6673a779f8b211858c61c656afa6785cb0f3774670fd4ac9b302f91bed948fb8e929e6c0c6f891aa7d527964bf8a28c1f775b8d4d3b4d7114c45fd82d713cf8f0f2267d75475cc3030703400834466b16504528a4ce09b951df23c1263afd7950b10c58b2ca0f34a2b3bda2e47aae98be1c4c8d451b26d42333f86d35104593fecfce7d24c2af8a380e5743c52599d22310b8bba77748d04056eb442a402c1664683143da8de305bb8a67c4cb0b56a0b5a6f46d930b67b507b7ab6353fabd5d44b792d19a0eb63d7aaaade1ac51f35f21eb6ccc1ee56719ed88b201697826d2d07b0bec466ac938696265d142b5ce75e6c4cb8a1dd5d6bf00f879c9a1ed379c61b4d1752e85d36445c6e361897a3fda3bb32cbf11f9235f9cb9d5423406635e6c8775f7bedb38224c0f866a2c08119517e394ca07d6f3375bb7ac36b24153f4c1708ff69dc3317c396603bb5f012471ec4006fd657d1b60331ba0f7793bc7447a598123dbe7185e3a5559b6d33c231c02b6124a66147e2e83143b7f25ed63ca4f5514c2a595a8222a2332232935ecf3643502b8a2f33f99fc58af07418f26ece77a8343fc4dadc0e053cd4596534cf06ac7431f580c575adaba615ec42ee034d5a94d9dc3dfb8a0a054357a115604dad7a674d40da847bff064beb597f4e063b44d829e68b243e4e405da07fdcbede438f5de86e9029c70c91f6c532e63b0482566e453822d292160d7c14339119510897f1e4929fbf363d9bbab22dcf5e1d4db134a2d23aeeef24fc51b8a02bddcfad8ad2ff74fdea03031ca3dcdc4f6b22dd1d974535a84542cbd39bda130643867f826f20895b9cfd1f6cd1610e433c1637b29b26f6e88f719bf7ac4200155c7ba1d98e62645e98fc60883252f19c9754a60ffccf2fc51d62a371d2c65ae42f8e10f7ece77666a5a3f6995315b8ec210d04274aacb89707f9628acd95a3ab0201ac53c9250c866333c294a227eac3fe0b8ca335c9ba3dac7d0801c40defd37acb53855e5b75f0cdda999ab71b76e070b3ad5e2a3def4c6d96c3d8e02586845fee1997dc57dd603b1741d74bf2d8160c6cdeba004834fdaac4dcfbe0dc15ca75f1ed4a4ce623f06f496e95ba82b99cc668eeccf8cdbd67f120ca2c8223ca5dd0c2033f71bc239a8a881aaab9fa271dc34acf12ae22ef1f7180801c91067386d3f908cb89bacb2470f80a83ba1ad734516873c0568c3b20d3080763c5cab843c06bef6bc05e0b64ffbae4bc6e0135eaeefb929d53799e1143f9586ff64d6aba665d829f9b1f37a106e97a65cba0c56c4a34a5e26ea18cae1074f3af872d09fc795dc3be0b071cdb847b298ecb0a3d8e49d9c9990ee59616944efcf45c0bb639bea4c29605ee1060756f04dbc0c42b82acf4c3075ab729b16fb52368e9d15c6a2d3ed002c3105de981b9d2ecadc0d75907db77d32996047cd6afc8f471a360276636b3a446be376c50972f35da00181aa4dab58424a9513973973631df484a3ce5ea867a487d4f3a6fab0923f6442ac346f11cd2888f7efc63ceb8748a7045920494d14e744918486b783f83c0e4648e0b3f217eba88364bd48ebad0ab0299229e342fe38294bde3e089df04288e0471235c48c6e64260b1f575271673392786a1d4e7947c9ae583131183abb625ea513fb4c87337b42326eee74df64d3cacfbc9c014855bda56986663954f138c6d3599ec9c970a495b5c97f9cfd6ae52672d6de2db3a60388e300acb8ca57755061636fb4ed7be8f239e28ad820f95cc23413f38437da5ba239979a1c1c7cd5c30f1a4e86d52f0f05cac216b92e270b0212382e7d52934e2e192038802f056c0b721d4ce93843ebceeaf4082be8161cff56ec20a4bb6a03d2affdf20b30c79894ca27e316777fac4e542b72

private def light (n : ℕ) : Bool :=
  if n≤182 then decide n.Prime else n.gcd 6617918090846482099299290940109294607621613906596302340913820810842197809526770404164356109688709577311175972876374017941783140498482132117303247394840048051710775719534642064901569944752621422554534336981337328498675734550843085835317647162879068664278892019554735323605004669084116608614400000000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤33166) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 182 = 6617918090846482099299290940109294607621613906596302340913820810842197809526770404164356109688709577311175972876374017941783140498482132117303247394840048051710775719534642064901569944752621422554534336981337328498675734550843085835317647162879068664278892019554735323605004669084116608614400000000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 182 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤33166 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 64 := by unfold smallValid; decide +kernel

private theorem sp64 : smallValid 64 32 := by unfold smallValid; decide +kernel

private theorem sp96 : smallValid 96 33 := by unfold smallValid; decide +kernel

private theorem sp129 : smallValid 129 32 := by unfold smallValid; decide +kernel

private theorem sp161 : smallValid 161 33 := by unfold smallValid; decide +kernel

private theorem sp194 : smallValid 194 32 := by unfold smallValid; decide +kernel

private theorem sp226 : smallValid 226 33 := by unfold smallValid; decide +kernel

private theorem sp259 : smallValid 259 64 := by unfold smallValid; decide +kernel

private theorem sp323 : smallValid 323 32 := by unfold smallValid; decide +kernel

private theorem sp355 : smallValid 355 33 := by unfold smallValid; decide +kernel

private theorem sp388 : smallValid 388 32 := by unfold smallValid; decide +kernel

private theorem sp420 : smallValid 420 33 := by unfold smallValid; decide +kernel

private theorem sp453 : smallValid 453 32 := by unfold smallValid; decide +kernel

private theorem sp485 : smallValid 485 33 := by unfold smallValid; decide +kernel

private theorem sp518 : smallValid 518 64 := by unfold smallValid; decide +kernel

private theorem sp582 : smallValid 582 32 := by unfold smallValid; decide +kernel

private theorem sp614 : smallValid 614 33 := by unfold smallValid; decide +kernel

private theorem sp647 : smallValid 647 32 := by unfold smallValid; decide +kernel

private theorem sp679 : smallValid 679 33 := by unfold smallValid; decide +kernel

private theorem sp712 : smallValid 712 32 := by unfold smallValid; decide +kernel

private theorem sp744 : smallValid 744 33 := by unfold smallValid; decide +kernel

private theorem sp777 : smallValid 777 64 := by unfold smallValid; decide +kernel

private theorem sp841 : smallValid 841 32 := by unfold smallValid; decide +kernel

private theorem sp873 : smallValid 873 33 := by unfold smallValid; decide +kernel

private theorem sp906 : smallValid 906 32 := by unfold smallValid; decide +kernel

private theorem sp938 : smallValid 938 33 := by unfold smallValid; decide +kernel

private theorem sp971 : smallValid 971 32 := by unfold smallValid; decide +kernel

private theorem sp1003 : smallValid 1003 33 := by unfold smallValid; decide +kernel

private theorem sp1036 : smallValid 1036 64 := by unfold smallValid; decide +kernel

private theorem sp1100 : smallValid 1100 32 := by unfold smallValid; decide +kernel

private theorem sp1132 : smallValid 1132 33 := by unfold smallValid; decide +kernel

private theorem sp1165 : smallValid 1165 32 := by unfold smallValid; decide +kernel

private theorem sp1197 : smallValid 1197 33 := by unfold smallValid; decide +kernel

private theorem sp1230 : smallValid 1230 32 := by unfold smallValid; decide +kernel

private theorem sp1262 : smallValid 1262 33 := by unfold smallValid; decide +kernel

private theorem sp1295 : smallValid 1295 64 := by unfold smallValid; decide +kernel

private theorem sp1359 : smallValid 1359 32 := by unfold smallValid; decide +kernel

private theorem sp1391 : smallValid 1391 33 := by unfold smallValid; decide +kernel

private theorem sp1424 : smallValid 1424 32 := by unfold smallValid; decide +kernel

private theorem sp1456 : smallValid 1456 33 := by unfold smallValid; decide +kernel

private theorem sp1489 : smallValid 1489 32 := by unfold smallValid; decide +kernel

private theorem sp1521 : smallValid 1521 33 := by unfold smallValid; decide +kernel

private theorem sp1554 : smallValid 1554 64 := by unfold smallValid; decide +kernel

private theorem sp1618 : smallValid 1618 32 := by unfold smallValid; decide +kernel

private theorem sp1650 : smallValid 1650 33 := by unfold smallValid; decide +kernel

private theorem sp1683 : smallValid 1683 32 := by unfold smallValid; decide +kernel

private theorem sp1715 : smallValid 1715 33 := by unfold smallValid; decide +kernel

private theorem sp1748 : smallValid 1748 32 := by unfold smallValid; decide +kernel

private theorem sp1780 : smallValid 1780 33 := by unfold smallValid; decide +kernel

private theorem sp1813 : smallValid 1813 64 := by unfold smallValid; decide +kernel

private theorem sp1877 : smallValid 1877 32 := by unfold smallValid; decide +kernel

private theorem sp1909 : smallValid 1909 33 := by unfold smallValid; decide +kernel

private theorem sp1942 : smallValid 1942 32 := by unfold smallValid; decide +kernel

private theorem sp1974 : smallValid 1974 33 := by unfold smallValid; decide +kernel

private theorem sp2007 : smallValid 2007 32 := by unfold smallValid; decide +kernel

private theorem sp2039 : smallValid 2039 33 := by unfold smallValid; decide +kernel

private theorem sp2072 : smallValid 2072 64 := by unfold smallValid; decide +kernel

private theorem sp2136 : smallValid 2136 32 := by unfold smallValid; decide +kernel

private theorem sp2168 : smallValid 2168 33 := by unfold smallValid; decide +kernel

private theorem sp2201 : smallValid 2201 32 := by unfold smallValid; decide +kernel

private theorem sp2233 : smallValid 2233 33 := by unfold smallValid; decide +kernel

private theorem sp2266 : smallValid 2266 32 := by unfold smallValid; decide +kernel

private theorem sp2298 : smallValid 2298 33 := by unfold smallValid; decide +kernel

private theorem sp2331 : smallValid 2331 64 := by unfold smallValid; decide +kernel

private theorem sp2395 : smallValid 2395 32 := by unfold smallValid; decide +kernel

private theorem sp2427 : smallValid 2427 33 := by unfold smallValid; decide +kernel

private theorem sp2460 : smallValid 2460 32 := by unfold smallValid; decide +kernel

private theorem sp2492 : smallValid 2492 33 := by unfold smallValid; decide +kernel

private theorem sp2525 : smallValid 2525 32 := by unfold smallValid; decide +kernel

private theorem sp2557 : smallValid 2557 33 := by unfold smallValid; decide +kernel

private theorem sp2590 : smallValid 2590 64 := by unfold smallValid; decide +kernel

private theorem sp2654 : smallValid 2654 32 := by unfold smallValid; decide +kernel

private theorem sp2686 : smallValid 2686 33 := by unfold smallValid; decide +kernel

private theorem sp2719 : smallValid 2719 32 := by unfold smallValid; decide +kernel

private theorem sp2751 : smallValid 2751 33 := by unfold smallValid; decide +kernel

private theorem sp2784 : smallValid 2784 32 := by unfold smallValid; decide +kernel

private theorem sp2816 : smallValid 2816 33 := by unfold smallValid; decide +kernel

private theorem sp2849 : smallValid 2849 64 := by unfold smallValid; decide +kernel

private theorem sp2913 : smallValid 2913 32 := by unfold smallValid; decide +kernel

private theorem sp2945 : smallValid 2945 33 := by unfold smallValid; decide +kernel

private theorem sp2978 : smallValid 2978 32 := by unfold smallValid; decide +kernel

private theorem sp3010 : smallValid 3010 33 := by unfold smallValid; decide +kernel

private theorem sp3043 : smallValid 3043 32 := by unfold smallValid; decide +kernel

private theorem sp3075 : smallValid 3075 33 := by unfold smallValid; decide +kernel

private theorem sp3108 : smallValid 3108 64 := by unfold smallValid; decide +kernel

private theorem sp3172 : smallValid 3172 32 := by unfold smallValid; decide +kernel

private theorem sp3204 : smallValid 3204 33 := by unfold smallValid; decide +kernel

private theorem sp3237 : smallValid 3237 32 := by unfold smallValid; decide +kernel

private theorem sp3269 : smallValid 3269 33 := by unfold smallValid; decide +kernel

private theorem sp3302 : smallValid 3302 32 := by unfold smallValid; decide +kernel

private theorem sp3334 : smallValid 3334 33 := by unfold smallValid; decide +kernel

private theorem sp3367 : smallValid 3367 64 := by unfold smallValid; decide +kernel

private theorem sp3431 : smallValid 3431 32 := by unfold smallValid; decide +kernel

private theorem sp3463 : smallValid 3463 33 := by unfold smallValid; decide +kernel

private theorem sp3496 : smallValid 3496 32 := by unfold smallValid; decide +kernel

private theorem sp3528 : smallValid 3528 33 := by unfold smallValid; decide +kernel

private theorem sp3561 : smallValid 3561 32 := by unfold smallValid; decide +kernel

private theorem sp3593 : smallValid 3593 33 := by unfold smallValid; decide +kernel

private theorem sp3626 : smallValid 3626 64 := by unfold smallValid; decide +kernel

private theorem sp3690 : smallValid 3690 32 := by unfold smallValid; decide +kernel

private theorem sp3722 : smallValid 3722 33 := by unfold smallValid; decide +kernel

private theorem sp3755 : smallValid 3755 32 := by unfold smallValid; decide +kernel

private theorem sp3787 : smallValid 3787 33 := by unfold smallValid; decide +kernel

private theorem sp3820 : smallValid 3820 32 := by unfold smallValid; decide +kernel

private theorem sp3852 : smallValid 3852 33 := by unfold smallValid; decide +kernel

private theorem sp3885 : smallValid 3885 32 := by unfold smallValid; decide +kernel

private theorem sp3917 : smallValid 3917 33 := by unfold smallValid; decide +kernel

private theorem sp3950 : smallValid 3950 32 := by unfold smallValid; decide +kernel

private theorem sp3982 : smallValid 3982 33 := by unfold smallValid; decide +kernel

private theorem sp4015 : smallValid 4015 32 := by unfold smallValid; decide +kernel

private theorem sp4047 : smallValid 4047 33 := by unfold smallValid; decide +kernel

private theorem sp4080 : smallValid 4080 32 := by unfold smallValid; decide +kernel

private theorem sp4112 : smallValid 4112 33 := by unfold smallValid; decide +kernel

private theorem sp4145 : smallValid 4145 64 := by unfold smallValid; decide +kernel

private theorem sp4209 : smallValid 4209 32 := by unfold smallValid; decide +kernel

private theorem sp4241 : smallValid 4241 33 := by unfold smallValid; decide +kernel

private theorem sp4274 : smallValid 4274 32 := by unfold smallValid; decide +kernel

private theorem sp4306 : smallValid 4306 33 := by unfold smallValid; decide +kernel

private theorem sp4339 : smallValid 4339 32 := by unfold smallValid; decide +kernel

private theorem sp4371 : smallValid 4371 33 := by unfold smallValid; decide +kernel

private theorem sp4404 : smallValid 4404 64 := by unfold smallValid; decide +kernel

private theorem sp4468 : smallValid 4468 32 := by unfold smallValid; decide +kernel

private theorem sp4500 : smallValid 4500 33 := by unfold smallValid; decide +kernel

private theorem sp4533 : smallValid 4533 32 := by unfold smallValid; decide +kernel

private theorem sp4565 : smallValid 4565 33 := by unfold smallValid; decide +kernel

private theorem sp4598 : smallValid 4598 32 := by unfold smallValid; decide +kernel

private theorem sp4630 : smallValid 4630 33 := by unfold smallValid; decide +kernel

private theorem sp4663 : smallValid 4663 64 := by unfold smallValid; decide +kernel

private theorem sp4727 : smallValid 4727 32 := by unfold smallValid; decide +kernel

private theorem sp4759 : smallValid 4759 33 := by unfold smallValid; decide +kernel

private theorem sp4792 : smallValid 4792 32 := by unfold smallValid; decide +kernel

private theorem sp4824 : smallValid 4824 33 := by unfold smallValid; decide +kernel

private theorem sp4857 : smallValid 4857 32 := by unfold smallValid; decide +kernel

private theorem sp4889 : smallValid 4889 33 := by unfold smallValid; decide +kernel

private theorem sp4922 : smallValid 4922 64 := by unfold smallValid; decide +kernel

private theorem sp4986 : smallValid 4986 32 := by unfold smallValid; decide +kernel

private theorem sp5018 : smallValid 5018 33 := by unfold smallValid; decide +kernel

private theorem sp5051 : smallValid 5051 32 := by unfold smallValid; decide +kernel

private theorem sp5083 : smallValid 5083 33 := by unfold smallValid; decide +kernel

private theorem sp5116 : smallValid 5116 32 := by unfold smallValid; decide +kernel

private theorem sp5148 : smallValid 5148 33 := by unfold smallValid; decide +kernel

private theorem sp5181 : smallValid 5181 64 := by unfold smallValid; decide +kernel

private theorem sp5245 : smallValid 5245 32 := by unfold smallValid; decide +kernel

private theorem sp5277 : smallValid 5277 33 := by unfold smallValid; decide +kernel

private theorem sp5310 : smallValid 5310 32 := by unfold smallValid; decide +kernel

private theorem sp5342 : smallValid 5342 33 := by unfold smallValid; decide +kernel

private theorem sp5375 : smallValid 5375 32 := by unfold smallValid; decide +kernel

private theorem sp5407 : smallValid 5407 33 := by unfold smallValid; decide +kernel

private theorem sp5440 : smallValid 5440 64 := by unfold smallValid; decide +kernel

private theorem sp5504 : smallValid 5504 32 := by unfold smallValid; decide +kernel

private theorem sp5536 : smallValid 5536 33 := by unfold smallValid; decide +kernel

private theorem sp5569 : smallValid 5569 32 := by unfold smallValid; decide +kernel

private theorem sp5601 : smallValid 5601 33 := by unfold smallValid; decide +kernel

private theorem sp5634 : smallValid 5634 32 := by unfold smallValid; decide +kernel

private theorem sp5666 : smallValid 5666 33 := by unfold smallValid; decide +kernel

private theorem sp5699 : smallValid 5699 64 := by unfold smallValid; decide +kernel

private theorem sp5763 : smallValid 5763 32 := by unfold smallValid; decide +kernel

private theorem sp5795 : smallValid 5795 33 := by unfold smallValid; decide +kernel

private theorem sp5828 : smallValid 5828 32 := by unfold smallValid; decide +kernel

private theorem sp5860 : smallValid 5860 33 := by unfold smallValid; decide +kernel

private theorem sp5893 : smallValid 5893 32 := by unfold smallValid; decide +kernel

private theorem sp5925 : smallValid 5925 33 := by unfold smallValid; decide +kernel

private theorem sp5958 : smallValid 5958 32 := by unfold smallValid; decide +kernel

private theorem sp5990 : smallValid 5990 33 := by unfold smallValid; decide +kernel

private theorem sp6023 : smallValid 6023 32 := by unfold smallValid; decide +kernel

private theorem sp6055 : smallValid 6055 33 := by unfold smallValid; decide +kernel

private theorem sp6088 : smallValid 6088 32 := by unfold smallValid; decide +kernel

private theorem sp6120 : smallValid 6120 33 := by unfold smallValid; decide +kernel

private theorem sp6153 : smallValid 6153 32 := by unfold smallValid; decide +kernel

private theorem sp6185 : smallValid 6185 33 := by unfold smallValid; decide +kernel

private theorem sp6218 : smallValid 6218 64 := by unfold smallValid; decide +kernel

private theorem sp6282 : smallValid 6282 32 := by unfold smallValid; decide +kernel

private theorem sp6314 : smallValid 6314 33 := by unfold smallValid; decide +kernel

private theorem sp6347 : smallValid 6347 32 := by unfold smallValid; decide +kernel

private theorem sp6379 : smallValid 6379 33 := by unfold smallValid; decide +kernel

private theorem sp6412 : smallValid 6412 32 := by unfold smallValid; decide +kernel

private theorem sp6444 : smallValid 6444 33 := by unfold smallValid; decide +kernel

private theorem sp6477 : smallValid 6477 64 := by unfold smallValid; decide +kernel

private theorem sp6541 : smallValid 6541 32 := by unfold smallValid; decide +kernel

private theorem sp6573 : smallValid 6573 33 := by unfold smallValid; decide +kernel

private theorem sp6606 : smallValid 6606 32 := by unfold smallValid; decide +kernel

private theorem sp6638 : smallValid 6638 33 := by unfold smallValid; decide +kernel

private theorem sp6671 : smallValid 6671 32 := by unfold smallValid; decide +kernel

private theorem sp6703 : smallValid 6703 33 := by unfold smallValid; decide +kernel

private theorem sp6736 : smallValid 6736 64 := by unfold smallValid; decide +kernel

private theorem sp6800 : smallValid 6800 32 := by unfold smallValid; decide +kernel

private theorem sp6832 : smallValid 6832 33 := by unfold smallValid; decide +kernel

private theorem sp6865 : smallValid 6865 32 := by unfold smallValid; decide +kernel

private theorem sp6897 : smallValid 6897 33 := by unfold smallValid; decide +kernel

private theorem sp6930 : smallValid 6930 32 := by unfold smallValid; decide +kernel

private theorem sp6962 : smallValid 6962 33 := by unfold smallValid; decide +kernel

private theorem sp6995 : smallValid 6995 64 := by unfold smallValid; decide +kernel

private theorem sp7059 : smallValid 7059 32 := by unfold smallValid; decide +kernel

private theorem sp7091 : smallValid 7091 33 := by unfold smallValid; decide +kernel

private theorem sp7124 : smallValid 7124 32 := by unfold smallValid; decide +kernel

private theorem sp7156 : smallValid 7156 33 := by unfold smallValid; decide +kernel

private theorem sp7189 : smallValid 7189 32 := by unfold smallValid; decide +kernel

private theorem sp7221 : smallValid 7221 33 := by unfold smallValid; decide +kernel

private theorem sp7254 : smallValid 7254 64 := by unfold smallValid; decide +kernel

private theorem sp7318 : smallValid 7318 32 := by unfold smallValid; decide +kernel

private theorem sp7350 : smallValid 7350 33 := by unfold smallValid; decide +kernel

private theorem sp7383 : smallValid 7383 32 := by unfold smallValid; decide +kernel

private theorem sp7415 : smallValid 7415 33 := by unfold smallValid; decide +kernel

private theorem sp7448 : smallValid 7448 32 := by unfold smallValid; decide +kernel

private theorem sp7480 : smallValid 7480 33 := by unfold smallValid; decide +kernel

private theorem sp7513 : smallValid 7513 64 := by unfold smallValid; decide +kernel

private theorem sp7577 : smallValid 7577 32 := by unfold smallValid; decide +kernel

private theorem sp7609 : smallValid 7609 33 := by unfold smallValid; decide +kernel

private theorem sp7642 : smallValid 7642 32 := by unfold smallValid; decide +kernel

private theorem sp7674 : smallValid 7674 33 := by unfold smallValid; decide +kernel

private theorem sp7707 : smallValid 7707 32 := by unfold smallValid; decide +kernel

private theorem sp7739 : smallValid 7739 33 := by unfold smallValid; decide +kernel

private theorem sp7772 : smallValid 7772 64 := by unfold smallValid; decide +kernel

private theorem sp7836 : smallValid 7836 32 := by unfold smallValid; decide +kernel

private theorem sp7868 : smallValid 7868 33 := by unfold smallValid; decide +kernel

private theorem sp7901 : smallValid 7901 32 := by unfold smallValid; decide +kernel

private theorem sp7933 : smallValid 7933 33 := by unfold smallValid; decide +kernel

private theorem sp7966 : smallValid 7966 32 := by unfold smallValid; decide +kernel

private theorem sp7998 : smallValid 7998 33 := by unfold smallValid; decide +kernel

private theorem sp8031 : smallValid 8031 32 := by unfold smallValid; decide +kernel

private theorem sp8063 : smallValid 8063 33 := by unfold smallValid; decide +kernel

private theorem sp8096 : smallValid 8096 32 := by unfold smallValid; decide +kernel

private theorem sp8128 : smallValid 8128 33 := by unfold smallValid; decide +kernel

private theorem sp8161 : smallValid 8161 32 := by unfold smallValid; decide +kernel

private theorem sp8193 : smallValid 8193 33 := by unfold smallValid; decide +kernel

private theorem sp8226 : smallValid 8226 32 := by unfold smallValid; decide +kernel

private theorem sp8258 : smallValid 8258 33 := by unfold smallValid; decide +kernel

private theorem sp8291 : smallValid 8291 64 := by unfold smallValid; decide +kernel

private theorem sp8355 : smallValid 8355 32 := by unfold smallValid; decide +kernel

private theorem sp8387 : smallValid 8387 33 := by unfold smallValid; decide +kernel

private theorem sp8420 : smallValid 8420 32 := by unfold smallValid; decide +kernel

private theorem sp8452 : smallValid 8452 33 := by unfold smallValid; decide +kernel

private theorem sp8485 : smallValid 8485 32 := by unfold smallValid; decide +kernel

private theorem sp8517 : smallValid 8517 33 := by unfold smallValid; decide +kernel

private theorem sp8550 : smallValid 8550 64 := by unfold smallValid; decide +kernel

private theorem sp8614 : smallValid 8614 32 := by unfold smallValid; decide +kernel

private theorem sp8646 : smallValid 8646 33 := by unfold smallValid; decide +kernel

private theorem sp8679 : smallValid 8679 32 := by unfold smallValid; decide +kernel

private theorem sp8711 : smallValid 8711 33 := by unfold smallValid; decide +kernel

private theorem sp8744 : smallValid 8744 32 := by unfold smallValid; decide +kernel

private theorem sp8776 : smallValid 8776 33 := by unfold smallValid; decide +kernel

private theorem sp8809 : smallValid 8809 64 := by unfold smallValid; decide +kernel

private theorem sp8873 : smallValid 8873 32 := by unfold smallValid; decide +kernel

private theorem sp8905 : smallValid 8905 33 := by unfold smallValid; decide +kernel

private theorem sp8938 : smallValid 8938 32 := by unfold smallValid; decide +kernel

private theorem sp8970 : smallValid 8970 33 := by unfold smallValid; decide +kernel

private theorem sp9003 : smallValid 9003 32 := by unfold smallValid; decide +kernel

private theorem sp9035 : smallValid 9035 33 := by unfold smallValid; decide +kernel

private theorem sp9068 : smallValid 9068 64 := by unfold smallValid; decide +kernel

private theorem sp9132 : smallValid 9132 32 := by unfold smallValid; decide +kernel

private theorem sp9164 : smallValid 9164 33 := by unfold smallValid; decide +kernel

private theorem sp9197 : smallValid 9197 32 := by unfold smallValid; decide +kernel

private theorem sp9229 : smallValid 9229 33 := by unfold smallValid; decide +kernel

private theorem sp9262 : smallValid 9262 32 := by unfold smallValid; decide +kernel

private theorem sp9294 : smallValid 9294 33 := by unfold smallValid; decide +kernel

private theorem sp9327 : smallValid 9327 64 := by unfold smallValid; decide +kernel

private theorem sp9391 : smallValid 9391 32 := by unfold smallValid; decide +kernel

private theorem sp9423 : smallValid 9423 33 := by unfold smallValid; decide +kernel

private theorem sp9456 : smallValid 9456 32 := by unfold smallValid; decide +kernel

private theorem sp9488 : smallValid 9488 33 := by unfold smallValid; decide +kernel

private theorem sp9521 : smallValid 9521 32 := by unfold smallValid; decide +kernel

private theorem sp9553 : smallValid 9553 33 := by unfold smallValid; decide +kernel

private theorem sp9586 : smallValid 9586 64 := by unfold smallValid; decide +kernel

private theorem sp9650 : smallValid 9650 32 := by unfold smallValid; decide +kernel

private theorem sp9682 : smallValid 9682 33 := by unfold smallValid; decide +kernel

private theorem sp9715 : smallValid 9715 32 := by unfold smallValid; decide +kernel

private theorem sp9747 : smallValid 9747 33 := by unfold smallValid; decide +kernel

private theorem sp9780 : smallValid 9780 32 := by unfold smallValid; decide +kernel

private theorem sp9812 : smallValid 9812 33 := by unfold smallValid; decide +kernel

private theorem sp9845 : smallValid 9845 64 := by unfold smallValid; decide +kernel

private theorem sp9909 : smallValid 9909 32 := by unfold smallValid; decide +kernel

private theorem sp9941 : smallValid 9941 33 := by unfold smallValid; decide +kernel

private theorem sp9974 : smallValid 9974 32 := by unfold smallValid; decide +kernel

private theorem sp10006 : smallValid 10006 33 := by unfold smallValid; decide +kernel

private theorem sp10039 : smallValid 10039 32 := by unfold smallValid; decide +kernel

private theorem sp10071 : smallValid 10071 33 := by unfold smallValid; decide +kernel

private theorem sp10104 : smallValid 10104 32 := by unfold smallValid; decide +kernel

private theorem sp10136 : smallValid 10136 33 := by unfold smallValid; decide +kernel

private theorem sp10169 : smallValid 10169 32 := by unfold smallValid; decide +kernel

private theorem sp10201 : smallValid 10201 33 := by unfold smallValid; decide +kernel

private theorem sp10234 : smallValid 10234 32 := by unfold smallValid; decide +kernel

private theorem sp10266 : smallValid 10266 33 := by unfold smallValid; decide +kernel

private theorem sp10299 : smallValid 10299 32 := by unfold smallValid; decide +kernel

private theorem sp10331 : smallValid 10331 33 := by unfold smallValid; decide +kernel

private theorem sp10364 : smallValid 10364 64 := by unfold smallValid; decide +kernel

private theorem sp10428 : smallValid 10428 32 := by unfold smallValid; decide +kernel

private theorem sp10460 : smallValid 10460 33 := by unfold smallValid; decide +kernel

private theorem sp10493 : smallValid 10493 32 := by unfold smallValid; decide +kernel

private theorem sp10525 : smallValid 10525 33 := by unfold smallValid; decide +kernel

private theorem sp10558 : smallValid 10558 32 := by unfold smallValid; decide +kernel

private theorem sp10590 : smallValid 10590 33 := by unfold smallValid; decide +kernel

private theorem sp10623 : smallValid 10623 64 := by unfold smallValid; decide +kernel

private theorem sp10687 : smallValid 10687 32 := by unfold smallValid; decide +kernel

private theorem sp10719 : smallValid 10719 33 := by unfold smallValid; decide +kernel

private theorem sp10752 : smallValid 10752 32 := by unfold smallValid; decide +kernel

private theorem sp10784 : smallValid 10784 33 := by unfold smallValid; decide +kernel

private theorem sp10817 : smallValid 10817 32 := by unfold smallValid; decide +kernel

private theorem sp10849 : smallValid 10849 33 := by unfold smallValid; decide +kernel

private theorem sp10882 : smallValid 10882 64 := by unfold smallValid; decide +kernel

private theorem sp10946 : smallValid 10946 32 := by unfold smallValid; decide +kernel

private theorem sp10978 : smallValid 10978 33 := by unfold smallValid; decide +kernel

private theorem sp11011 : smallValid 11011 32 := by unfold smallValid; decide +kernel

private theorem sp11043 : smallValid 11043 33 := by unfold smallValid; decide +kernel

private theorem sp11076 : smallValid 11076 32 := by unfold smallValid; decide +kernel

private theorem sp11108 : smallValid 11108 33 := by unfold smallValid; decide +kernel

private theorem sp11141 : smallValid 11141 64 := by unfold smallValid; decide +kernel

private theorem sp11205 : smallValid 11205 32 := by unfold smallValid; decide +kernel

private theorem sp11237 : smallValid 11237 33 := by unfold smallValid; decide +kernel

private theorem sp11270 : smallValid 11270 32 := by unfold smallValid; decide +kernel

private theorem sp11302 : smallValid 11302 33 := by unfold smallValid; decide +kernel

private theorem sp11335 : smallValid 11335 32 := by unfold smallValid; decide +kernel

private theorem sp11367 : smallValid 11367 33 := by unfold smallValid; decide +kernel

private theorem sp11400 : smallValid 11400 64 := by unfold smallValid; decide +kernel

private theorem sp11464 : smallValid 11464 32 := by unfold smallValid; decide +kernel

private theorem sp11496 : smallValid 11496 33 := by unfold smallValid; decide +kernel

private theorem sp11529 : smallValid 11529 32 := by unfold smallValid; decide +kernel

private theorem sp11561 : smallValid 11561 33 := by unfold smallValid; decide +kernel

private theorem sp11594 : smallValid 11594 32 := by unfold smallValid; decide +kernel

private theorem sp11626 : smallValid 11626 33 := by unfold smallValid; decide +kernel

private theorem sp11659 : smallValid 11659 64 := by unfold smallValid; decide +kernel

private theorem sp11723 : smallValid 11723 32 := by unfold smallValid; decide +kernel

private theorem sp11755 : smallValid 11755 33 := by unfold smallValid; decide +kernel

private theorem sp11788 : smallValid 11788 32 := by unfold smallValid; decide +kernel

private theorem sp11820 : smallValid 11820 33 := by unfold smallValid; decide +kernel

private theorem sp11853 : smallValid 11853 32 := by unfold smallValid; decide +kernel

private theorem sp11885 : smallValid 11885 33 := by unfold smallValid; decide +kernel

private theorem sp11918 : smallValid 11918 64 := by unfold smallValid; decide +kernel

private theorem sp11982 : smallValid 11982 32 := by unfold smallValid; decide +kernel

private theorem sp12014 : smallValid 12014 33 := by unfold smallValid; decide +kernel

private theorem sp12047 : smallValid 12047 32 := by unfold smallValid; decide +kernel

private theorem sp12079 : smallValid 12079 33 := by unfold smallValid; decide +kernel

private theorem sp12112 : smallValid 12112 32 := by unfold smallValid; decide +kernel

private theorem sp12144 : smallValid 12144 33 := by unfold smallValid; decide +kernel

private theorem sp12177 : smallValid 12177 32 := by unfold smallValid; decide +kernel

private theorem sp12209 : smallValid 12209 33 := by unfold smallValid; decide +kernel

private theorem sp12242 : smallValid 12242 32 := by unfold smallValid; decide +kernel

private theorem sp12274 : smallValid 12274 33 := by unfold smallValid; decide +kernel

private theorem sp12307 : smallValid 12307 32 := by unfold smallValid; decide +kernel

private theorem sp12339 : smallValid 12339 33 := by unfold smallValid; decide +kernel

private theorem sp12372 : smallValid 12372 32 := by unfold smallValid; decide +kernel

private theorem sp12404 : smallValid 12404 33 := by unfold smallValid; decide +kernel

private theorem sp12437 : smallValid 12437 64 := by unfold smallValid; decide +kernel

private theorem sp12501 : smallValid 12501 32 := by unfold smallValid; decide +kernel

private theorem sp12533 : smallValid 12533 33 := by unfold smallValid; decide +kernel

private theorem sp12566 : smallValid 12566 32 := by unfold smallValid; decide +kernel

private theorem sp12598 : smallValid 12598 33 := by unfold smallValid; decide +kernel

private theorem sp12631 : smallValid 12631 32 := by unfold smallValid; decide +kernel

private theorem sp12663 : smallValid 12663 33 := by unfold smallValid; decide +kernel

private theorem sp12696 : smallValid 12696 64 := by unfold smallValid; decide +kernel

private theorem sp12760 : smallValid 12760 32 := by unfold smallValid; decide +kernel

private theorem sp12792 : smallValid 12792 33 := by unfold smallValid; decide +kernel

private theorem sp12825 : smallValid 12825 32 := by unfold smallValid; decide +kernel

private theorem sp12857 : smallValid 12857 33 := by unfold smallValid; decide +kernel

private theorem sp12890 : smallValid 12890 32 := by unfold smallValid; decide +kernel

private theorem sp12922 : smallValid 12922 33 := by unfold smallValid; decide +kernel

private theorem sp12955 : smallValid 12955 64 := by unfold smallValid; decide +kernel

private theorem sp13019 : smallValid 13019 32 := by unfold smallValid; decide +kernel

private theorem sp13051 : smallValid 13051 33 := by unfold smallValid; decide +kernel

private theorem sp13084 : smallValid 13084 32 := by unfold smallValid; decide +kernel

private theorem sp13116 : smallValid 13116 33 := by unfold smallValid; decide +kernel

private theorem sp13149 : smallValid 13149 32 := by unfold smallValid; decide +kernel

private theorem sp13181 : smallValid 13181 33 := by unfold smallValid; decide +kernel

private theorem sp13214 : smallValid 13214 64 := by unfold smallValid; decide +kernel

private theorem sp13278 : smallValid 13278 32 := by unfold smallValid; decide +kernel

private theorem sp13310 : smallValid 13310 33 := by unfold smallValid; decide +kernel

private theorem sp13343 : smallValid 13343 32 := by unfold smallValid; decide +kernel

private theorem sp13375 : smallValid 13375 33 := by unfold smallValid; decide +kernel

private theorem sp13408 : smallValid 13408 32 := by unfold smallValid; decide +kernel

private theorem sp13440 : smallValid 13440 33 := by unfold smallValid; decide +kernel

private theorem sp13473 : smallValid 13473 64 := by unfold smallValid; decide +kernel

private theorem sp13537 : smallValid 13537 32 := by unfold smallValid; decide +kernel

private theorem sp13569 : smallValid 13569 33 := by unfold smallValid; decide +kernel

private theorem sp13602 : smallValid 13602 32 := by unfold smallValid; decide +kernel

private theorem sp13634 : smallValid 13634 33 := by unfold smallValid; decide +kernel

private theorem sp13667 : smallValid 13667 32 := by unfold smallValid; decide +kernel

private theorem sp13699 : smallValid 13699 33 := by unfold smallValid; decide +kernel

private theorem sp13732 : smallValid 13732 64 := by unfold smallValid; decide +kernel

private theorem sp13796 : smallValid 13796 32 := by unfold smallValid; decide +kernel

private theorem sp13828 : smallValid 13828 33 := by unfold smallValid; decide +kernel

private theorem sp13861 : smallValid 13861 32 := by unfold smallValid; decide +kernel

private theorem sp13893 : smallValid 13893 33 := by unfold smallValid; decide +kernel

private theorem sp13926 : smallValid 13926 32 := by unfold smallValid; decide +kernel

private theorem sp13958 : smallValid 13958 33 := by unfold smallValid; decide +kernel

private theorem sp13991 : smallValid 13991 64 := by unfold smallValid; decide +kernel

private theorem sp14055 : smallValid 14055 32 := by unfold smallValid; decide +kernel

private theorem sp14087 : smallValid 14087 33 := by unfold smallValid; decide +kernel

private theorem sp14120 : smallValid 14120 32 := by unfold smallValid; decide +kernel

private theorem sp14152 : smallValid 14152 33 := by unfold smallValid; decide +kernel

private theorem sp14185 : smallValid 14185 32 := by unfold smallValid; decide +kernel

private theorem sp14217 : smallValid 14217 33 := by unfold smallValid; decide +kernel

private theorem sp14250 : smallValid 14250 32 := by unfold smallValid; decide +kernel

private theorem sp14282 : smallValid 14282 33 := by unfold smallValid; decide +kernel

private theorem sp14315 : smallValid 14315 32 := by unfold smallValid; decide +kernel

private theorem sp14347 : smallValid 14347 33 := by unfold smallValid; decide +kernel

private theorem sp14380 : smallValid 14380 32 := by unfold smallValid; decide +kernel

private theorem sp14412 : smallValid 14412 33 := by unfold smallValid; decide +kernel

private theorem sp14445 : smallValid 14445 32 := by unfold smallValid; decide +kernel

private theorem sp14477 : smallValid 14477 33 := by unfold smallValid; decide +kernel

private theorem sp14510 : smallValid 14510 64 := by unfold smallValid; decide +kernel

private theorem sp14574 : smallValid 14574 32 := by unfold smallValid; decide +kernel

private theorem sp14606 : smallValid 14606 33 := by unfold smallValid; decide +kernel

private theorem sp14639 : smallValid 14639 32 := by unfold smallValid; decide +kernel

private theorem sp14671 : smallValid 14671 33 := by unfold smallValid; decide +kernel

private theorem sp14704 : smallValid 14704 32 := by unfold smallValid; decide +kernel

private theorem sp14736 : smallValid 14736 33 := by unfold smallValid; decide +kernel

private theorem sp14769 : smallValid 14769 64 := by unfold smallValid; decide +kernel

private theorem sp14833 : smallValid 14833 32 := by unfold smallValid; decide +kernel

private theorem sp14865 : smallValid 14865 33 := by unfold smallValid; decide +kernel

private theorem sp14898 : smallValid 14898 32 := by unfold smallValid; decide +kernel

private theorem sp14930 : smallValid 14930 33 := by unfold smallValid; decide +kernel

private theorem sp14963 : smallValid 14963 32 := by unfold smallValid; decide +kernel

private theorem sp14995 : smallValid 14995 33 := by unfold smallValid; decide +kernel

private theorem sp15028 : smallValid 15028 64 := by unfold smallValid; decide +kernel

private theorem sp15092 : smallValid 15092 32 := by unfold smallValid; decide +kernel

private theorem sp15124 : smallValid 15124 33 := by unfold smallValid; decide +kernel

private theorem sp15157 : smallValid 15157 32 := by unfold smallValid; decide +kernel

private theorem sp15189 : smallValid 15189 33 := by unfold smallValid; decide +kernel

private theorem sp15222 : smallValid 15222 32 := by unfold smallValid; decide +kernel

private theorem sp15254 : smallValid 15254 33 := by unfold smallValid; decide +kernel

private theorem sp15287 : smallValid 15287 64 := by unfold smallValid; decide +kernel

private theorem sp15351 : smallValid 15351 32 := by unfold smallValid; decide +kernel

private theorem sp15383 : smallValid 15383 33 := by unfold smallValid; decide +kernel

private theorem sp15416 : smallValid 15416 32 := by unfold smallValid; decide +kernel

private theorem sp15448 : smallValid 15448 33 := by unfold smallValid; decide +kernel

private theorem sp15481 : smallValid 15481 32 := by unfold smallValid; decide +kernel

private theorem sp15513 : smallValid 15513 33 := by unfold smallValid; decide +kernel

private theorem sp15546 : smallValid 15546 64 := by unfold smallValid; decide +kernel

private theorem sp15610 : smallValid 15610 32 := by unfold smallValid; decide +kernel

private theorem sp15642 : smallValid 15642 33 := by unfold smallValid; decide +kernel

private theorem sp15675 : smallValid 15675 32 := by unfold smallValid; decide +kernel

private theorem sp15707 : smallValid 15707 33 := by unfold smallValid; decide +kernel

private theorem sp15740 : smallValid 15740 32 := by unfold smallValid; decide +kernel

private theorem sp15772 : smallValid 15772 33 := by unfold smallValid; decide +kernel

private theorem sp15805 : smallValid 15805 64 := by unfold smallValid; decide +kernel

private theorem sp15869 : smallValid 15869 32 := by unfold smallValid; decide +kernel

private theorem sp15901 : smallValid 15901 33 := by unfold smallValid; decide +kernel

private theorem sp15934 : smallValid 15934 32 := by unfold smallValid; decide +kernel

private theorem sp15966 : smallValid 15966 33 := by unfold smallValid; decide +kernel

private theorem sp15999 : smallValid 15999 32 := by unfold smallValid; decide +kernel

private theorem sp16031 : smallValid 16031 33 := by unfold smallValid; decide +kernel

private theorem sp16064 : smallValid 16064 64 := by unfold smallValid; decide +kernel

private theorem sp16128 : smallValid 16128 32 := by unfold smallValid; decide +kernel

private theorem sp16160 : smallValid 16160 33 := by unfold smallValid; decide +kernel

private theorem sp16193 : smallValid 16193 32 := by unfold smallValid; decide +kernel

private theorem sp16225 : smallValid 16225 33 := by unfold smallValid; decide +kernel

private theorem sp16258 : smallValid 16258 32 := by unfold smallValid; decide +kernel

private theorem sp16290 : smallValid 16290 33 := by unfold smallValid; decide +kernel

private theorem sp16323 : smallValid 16323 32 := by unfold smallValid; decide +kernel

private theorem sp16355 : smallValid 16355 33 := by unfold smallValid; decide +kernel

private theorem sp16388 : smallValid 16388 32 := by unfold smallValid; decide +kernel

private theorem sp16420 : smallValid 16420 33 := by unfold smallValid; decide +kernel

private theorem sp16453 : smallValid 16453 32 := by unfold smallValid; decide +kernel

private theorem sp16485 : smallValid 16485 33 := by unfold smallValid; decide +kernel

private theorem sp16518 : smallValid 16518 32 := by unfold smallValid; decide +kernel

private theorem sp16550 : smallValid 16550 33 := by unfold smallValid; decide +kernel

private theorem sp16583 : smallValid 16583 64 := by unfold smallValid; decide +kernel

private theorem sp16647 : smallValid 16647 32 := by unfold smallValid; decide +kernel

private theorem sp16679 : smallValid 16679 33 := by unfold smallValid; decide +kernel

private theorem sp16712 : smallValid 16712 32 := by unfold smallValid; decide +kernel

private theorem sp16744 : smallValid 16744 33 := by unfold smallValid; decide +kernel

private theorem sp16777 : smallValid 16777 32 := by unfold smallValid; decide +kernel

private theorem sp16809 : smallValid 16809 33 := by unfold smallValid; decide +kernel

private theorem sp16842 : smallValid 16842 64 := by unfold smallValid; decide +kernel

private theorem sp16906 : smallValid 16906 32 := by unfold smallValid; decide +kernel

private theorem sp16938 : smallValid 16938 33 := by unfold smallValid; decide +kernel

private theorem sp16971 : smallValid 16971 32 := by unfold smallValid; decide +kernel

private theorem sp17003 : smallValid 17003 33 := by unfold smallValid; decide +kernel

private theorem sp17036 : smallValid 17036 32 := by unfold smallValid; decide +kernel

private theorem sp17068 : smallValid 17068 33 := by unfold smallValid; decide +kernel

private theorem sp17101 : smallValid 17101 64 := by unfold smallValid; decide +kernel

private theorem sp17165 : smallValid 17165 32 := by unfold smallValid; decide +kernel

private theorem sp17197 : smallValid 17197 33 := by unfold smallValid; decide +kernel

private theorem sp17230 : smallValid 17230 32 := by unfold smallValid; decide +kernel

private theorem sp17262 : smallValid 17262 33 := by unfold smallValid; decide +kernel

private theorem sp17295 : smallValid 17295 32 := by unfold smallValid; decide +kernel

private theorem sp17327 : smallValid 17327 33 := by unfold smallValid; decide +kernel

private theorem sp17360 : smallValid 17360 64 := by unfold smallValid; decide +kernel

private theorem sp17424 : smallValid 17424 32 := by unfold smallValid; decide +kernel

private theorem sp17456 : smallValid 17456 33 := by unfold smallValid; decide +kernel

private theorem sp17489 : smallValid 17489 32 := by unfold smallValid; decide +kernel

private theorem sp17521 : smallValid 17521 33 := by unfold smallValid; decide +kernel

private theorem sp17554 : smallValid 17554 32 := by unfold smallValid; decide +kernel

private theorem sp17586 : smallValid 17586 33 := by unfold smallValid; decide +kernel

private theorem sp17619 : smallValid 17619 64 := by unfold smallValid; decide +kernel

private theorem sp17683 : smallValid 17683 32 := by unfold smallValid; decide +kernel

private theorem sp17715 : smallValid 17715 33 := by unfold smallValid; decide +kernel

private theorem sp17748 : smallValid 17748 32 := by unfold smallValid; decide +kernel

private theorem sp17780 : smallValid 17780 33 := by unfold smallValid; decide +kernel

private theorem sp17813 : smallValid 17813 32 := by unfold smallValid; decide +kernel

private theorem sp17845 : smallValid 17845 33 := by unfold smallValid; decide +kernel

private theorem sp17878 : smallValid 17878 64 := by unfold smallValid; decide +kernel

private theorem sp17942 : smallValid 17942 32 := by unfold smallValid; decide +kernel

private theorem sp17974 : smallValid 17974 33 := by unfold smallValid; decide +kernel

private theorem sp18007 : smallValid 18007 32 := by unfold smallValid; decide +kernel

private theorem sp18039 : smallValid 18039 33 := by unfold smallValid; decide +kernel

private theorem sp18072 : smallValid 18072 32 := by unfold smallValid; decide +kernel

private theorem sp18104 : smallValid 18104 33 := by unfold smallValid; decide +kernel

private theorem sp18137 : smallValid 18137 64 := by unfold smallValid; decide +kernel

private theorem sp18201 : smallValid 18201 32 := by unfold smallValid; decide +kernel

private theorem sp18233 : smallValid 18233 33 := by unfold smallValid; decide +kernel

private theorem sp18266 : smallValid 18266 32 := by unfold smallValid; decide +kernel

private theorem sp18298 : smallValid 18298 33 := by unfold smallValid; decide +kernel

private theorem sp18331 : smallValid 18331 32 := by unfold smallValid; decide +kernel

private theorem sp18363 : smallValid 18363 33 := by unfold smallValid; decide +kernel

private theorem sp18396 : smallValid 18396 32 := by unfold smallValid; decide +kernel

private theorem sp18428 : smallValid 18428 33 := by unfold smallValid; decide +kernel

private theorem sp18461 : smallValid 18461 32 := by unfold smallValid; decide +kernel

private theorem sp18493 : smallValid 18493 33 := by unfold smallValid; decide +kernel

private theorem sp18526 : smallValid 18526 32 := by unfold smallValid; decide +kernel

private theorem sp18558 : smallValid 18558 33 := by unfold smallValid; decide +kernel

private theorem sp18591 : smallValid 18591 32 := by unfold smallValid; decide +kernel

private theorem sp18623 : smallValid 18623 33 := by unfold smallValid; decide +kernel

private theorem sp18656 : smallValid 18656 64 := by unfold smallValid; decide +kernel

private theorem sp18720 : smallValid 18720 32 := by unfold smallValid; decide +kernel

private theorem sp18752 : smallValid 18752 33 := by unfold smallValid; decide +kernel

private theorem sp18785 : smallValid 18785 32 := by unfold smallValid; decide +kernel

private theorem sp18817 : smallValid 18817 33 := by unfold smallValid; decide +kernel

private theorem sp18850 : smallValid 18850 32 := by unfold smallValid; decide +kernel

private theorem sp18882 : smallValid 18882 33 := by unfold smallValid; decide +kernel

private theorem sp18915 : smallValid 18915 64 := by unfold smallValid; decide +kernel

private theorem sp18979 : smallValid 18979 32 := by unfold smallValid; decide +kernel

private theorem sp19011 : smallValid 19011 33 := by unfold smallValid; decide +kernel

private theorem sp19044 : smallValid 19044 32 := by unfold smallValid; decide +kernel

private theorem sp19076 : smallValid 19076 33 := by unfold smallValid; decide +kernel

private theorem sp19109 : smallValid 19109 32 := by unfold smallValid; decide +kernel

private theorem sp19141 : smallValid 19141 33 := by unfold smallValid; decide +kernel

private theorem sp19174 : smallValid 19174 64 := by unfold smallValid; decide +kernel

private theorem sp19238 : smallValid 19238 32 := by unfold smallValid; decide +kernel

private theorem sp19270 : smallValid 19270 33 := by unfold smallValid; decide +kernel

private theorem sp19303 : smallValid 19303 32 := by unfold smallValid; decide +kernel

private theorem sp19335 : smallValid 19335 33 := by unfold smallValid; decide +kernel

private theorem sp19368 : smallValid 19368 32 := by unfold smallValid; decide +kernel

private theorem sp19400 : smallValid 19400 33 := by unfold smallValid; decide +kernel

private theorem sp19433 : smallValid 19433 64 := by unfold smallValid; decide +kernel

private theorem sp19497 : smallValid 19497 32 := by unfold smallValid; decide +kernel

private theorem sp19529 : smallValid 19529 33 := by unfold smallValid; decide +kernel

private theorem sp19562 : smallValid 19562 32 := by unfold smallValid; decide +kernel

private theorem sp19594 : smallValid 19594 33 := by unfold smallValid; decide +kernel

private theorem sp19627 : smallValid 19627 32 := by unfold smallValid; decide +kernel

private theorem sp19659 : smallValid 19659 33 := by unfold smallValid; decide +kernel

private theorem sp19692 : smallValid 19692 64 := by unfold smallValid; decide +kernel

private theorem sp19756 : smallValid 19756 32 := by unfold smallValid; decide +kernel

private theorem sp19788 : smallValid 19788 33 := by unfold smallValid; decide +kernel

private theorem sp19821 : smallValid 19821 32 := by unfold smallValid; decide +kernel

private theorem sp19853 : smallValid 19853 33 := by unfold smallValid; decide +kernel

private theorem sp19886 : smallValid 19886 32 := by unfold smallValid; decide +kernel

private theorem sp19918 : smallValid 19918 33 := by unfold smallValid; decide +kernel

private theorem sp19951 : smallValid 19951 64 := by unfold smallValid; decide +kernel

private theorem sp20015 : smallValid 20015 32 := by unfold smallValid; decide +kernel

private theorem sp20047 : smallValid 20047 33 := by unfold smallValid; decide +kernel

private theorem sp20080 : smallValid 20080 32 := by unfold smallValid; decide +kernel

private theorem sp20112 : smallValid 20112 33 := by unfold smallValid; decide +kernel

private theorem sp20145 : smallValid 20145 32 := by unfold smallValid; decide +kernel

private theorem sp20177 : smallValid 20177 33 := by unfold smallValid; decide +kernel

private theorem sp20210 : smallValid 20210 64 := by unfold smallValid; decide +kernel

private theorem sp20274 : smallValid 20274 32 := by unfold smallValid; decide +kernel

private theorem sp20306 : smallValid 20306 33 := by unfold smallValid; decide +kernel

private theorem sp20339 : smallValid 20339 32 := by unfold smallValid; decide +kernel

private theorem sp20371 : smallValid 20371 33 := by unfold smallValid; decide +kernel

private theorem sp20404 : smallValid 20404 32 := by unfold smallValid; decide +kernel

private theorem sp20436 : smallValid 20436 33 := by unfold smallValid; decide +kernel

private theorem sp20469 : smallValid 20469 32 := by unfold smallValid; decide +kernel

private theorem sp20501 : smallValid 20501 33 := by unfold smallValid; decide +kernel

private theorem sp20534 : smallValid 20534 32 := by unfold smallValid; decide +kernel

private theorem sp20566 : smallValid 20566 33 := by unfold smallValid; decide +kernel

private theorem sp20599 : smallValid 20599 32 := by unfold smallValid; decide +kernel

private theorem sp20631 : smallValid 20631 33 := by unfold smallValid; decide +kernel

private theorem sp20664 : smallValid 20664 32 := by unfold smallValid; decide +kernel

private theorem sp20696 : smallValid 20696 33 := by unfold smallValid; decide +kernel

private theorem sp20729 : smallValid 20729 64 := by unfold smallValid; decide +kernel

private theorem sp20793 : smallValid 20793 32 := by unfold smallValid; decide +kernel

private theorem sp20825 : smallValid 20825 33 := by unfold smallValid; decide +kernel

private theorem sp20858 : smallValid 20858 32 := by unfold smallValid; decide +kernel

private theorem sp20890 : smallValid 20890 33 := by unfold smallValid; decide +kernel

private theorem sp20923 : smallValid 20923 32 := by unfold smallValid; decide +kernel

private theorem sp20955 : smallValid 20955 33 := by unfold smallValid; decide +kernel

private theorem sp20988 : smallValid 20988 64 := by unfold smallValid; decide +kernel

private theorem sp21052 : smallValid 21052 32 := by unfold smallValid; decide +kernel

private theorem sp21084 : smallValid 21084 33 := by unfold smallValid; decide +kernel

private theorem sp21117 : smallValid 21117 32 := by unfold smallValid; decide +kernel

private theorem sp21149 : smallValid 21149 33 := by unfold smallValid; decide +kernel

private theorem sp21182 : smallValid 21182 32 := by unfold smallValid; decide +kernel

private theorem sp21214 : smallValid 21214 33 := by unfold smallValid; decide +kernel

private theorem sp21247 : smallValid 21247 64 := by unfold smallValid; decide +kernel

private theorem sp21311 : smallValid 21311 32 := by unfold smallValid; decide +kernel

private theorem sp21343 : smallValid 21343 33 := by unfold smallValid; decide +kernel

private theorem sp21376 : smallValid 21376 32 := by unfold smallValid; decide +kernel

private theorem sp21408 : smallValid 21408 33 := by unfold smallValid; decide +kernel

private theorem sp21441 : smallValid 21441 32 := by unfold smallValid; decide +kernel

private theorem sp21473 : smallValid 21473 33 := by unfold smallValid; decide +kernel

private theorem sp21506 : smallValid 21506 64 := by unfold smallValid; decide +kernel

private theorem sp21570 : smallValid 21570 32 := by unfold smallValid; decide +kernel

private theorem sp21602 : smallValid 21602 33 := by unfold smallValid; decide +kernel

private theorem sp21635 : smallValid 21635 32 := by unfold smallValid; decide +kernel

private theorem sp21667 : smallValid 21667 33 := by unfold smallValid; decide +kernel

private theorem sp21700 : smallValid 21700 32 := by unfold smallValid; decide +kernel

private theorem sp21732 : smallValid 21732 33 := by unfold smallValid; decide +kernel

private theorem sp21765 : smallValid 21765 64 := by unfold smallValid; decide +kernel

private theorem sp21829 : smallValid 21829 32 := by unfold smallValid; decide +kernel

private theorem sp21861 : smallValid 21861 33 := by unfold smallValid; decide +kernel

private theorem sp21894 : smallValid 21894 32 := by unfold smallValid; decide +kernel

private theorem sp21926 : smallValid 21926 33 := by unfold smallValid; decide +kernel

private theorem sp21959 : smallValid 21959 32 := by unfold smallValid; decide +kernel

private theorem sp21991 : smallValid 21991 33 := by unfold smallValid; decide +kernel

private theorem sp22024 : smallValid 22024 64 := by unfold smallValid; decide +kernel

private theorem sp22088 : smallValid 22088 32 := by unfold smallValid; decide +kernel

private theorem sp22120 : smallValid 22120 33 := by unfold smallValid; decide +kernel

private theorem sp22153 : smallValid 22153 32 := by unfold smallValid; decide +kernel

private theorem sp22185 : smallValid 22185 33 := by unfold smallValid; decide +kernel

private theorem sp22218 : smallValid 22218 32 := by unfold smallValid; decide +kernel

private theorem sp22250 : smallValid 22250 33 := by unfold smallValid; decide +kernel

private theorem sp22283 : smallValid 22283 64 := by unfold smallValid; decide +kernel

private theorem sp22347 : smallValid 22347 32 := by unfold smallValid; decide +kernel

private theorem sp22379 : smallValid 22379 33 := by unfold smallValid; decide +kernel

private theorem sp22412 : smallValid 22412 32 := by unfold smallValid; decide +kernel

private theorem sp22444 : smallValid 22444 33 := by unfold smallValid; decide +kernel

private theorem sp22477 : smallValid 22477 32 := by unfold smallValid; decide +kernel

private theorem sp22509 : smallValid 22509 33 := by unfold smallValid; decide +kernel

private theorem sp22542 : smallValid 22542 32 := by unfold smallValid; decide +kernel

private theorem sp22574 : smallValid 22574 33 := by unfold smallValid; decide +kernel

private theorem sp22607 : smallValid 22607 32 := by unfold smallValid; decide +kernel

private theorem sp22639 : smallValid 22639 33 := by unfold smallValid; decide +kernel

private theorem sp22672 : smallValid 22672 32 := by unfold smallValid; decide +kernel

private theorem sp22704 : smallValid 22704 33 := by unfold smallValid; decide +kernel

private theorem sp22737 : smallValid 22737 32 := by unfold smallValid; decide +kernel

private theorem sp22769 : smallValid 22769 33 := by unfold smallValid; decide +kernel

private theorem sp22802 : smallValid 22802 64 := by unfold smallValid; decide +kernel

private theorem sp22866 : smallValid 22866 32 := by unfold smallValid; decide +kernel

private theorem sp22898 : smallValid 22898 33 := by unfold smallValid; decide +kernel

private theorem sp22931 : smallValid 22931 32 := by unfold smallValid; decide +kernel

private theorem sp22963 : smallValid 22963 33 := by unfold smallValid; decide +kernel

private theorem sp22996 : smallValid 22996 32 := by unfold smallValid; decide +kernel

private theorem sp23028 : smallValid 23028 33 := by unfold smallValid; decide +kernel

private theorem sp23061 : smallValid 23061 64 := by unfold smallValid; decide +kernel

private theorem sp23125 : smallValid 23125 32 := by unfold smallValid; decide +kernel

private theorem sp23157 : smallValid 23157 33 := by unfold smallValid; decide +kernel

private theorem sp23190 : smallValid 23190 32 := by unfold smallValid; decide +kernel

private theorem sp23222 : smallValid 23222 33 := by unfold smallValid; decide +kernel

private theorem sp23255 : smallValid 23255 32 := by unfold smallValid; decide +kernel

private theorem sp23287 : smallValid 23287 33 := by unfold smallValid; decide +kernel

private theorem sp23320 : smallValid 23320 64 := by unfold smallValid; decide +kernel

private theorem sp23384 : smallValid 23384 32 := by unfold smallValid; decide +kernel

private theorem sp23416 : smallValid 23416 33 := by unfold smallValid; decide +kernel

private theorem sp23449 : smallValid 23449 32 := by unfold smallValid; decide +kernel

private theorem sp23481 : smallValid 23481 33 := by unfold smallValid; decide +kernel

private theorem sp23514 : smallValid 23514 32 := by unfold smallValid; decide +kernel

private theorem sp23546 : smallValid 23546 33 := by unfold smallValid; decide +kernel

private theorem sp23579 : smallValid 23579 64 := by unfold smallValid; decide +kernel

private theorem sp23643 : smallValid 23643 32 := by unfold smallValid; decide +kernel

private theorem sp23675 : smallValid 23675 33 := by unfold smallValid; decide +kernel

private theorem sp23708 : smallValid 23708 32 := by unfold smallValid; decide +kernel

private theorem sp23740 : smallValid 23740 33 := by unfold smallValid; decide +kernel

private theorem sp23773 : smallValid 23773 32 := by unfold smallValid; decide +kernel

private theorem sp23805 : smallValid 23805 33 := by unfold smallValid; decide +kernel

private theorem sp23838 : smallValid 23838 64 := by unfold smallValid; decide +kernel

private theorem sp23902 : smallValid 23902 32 := by unfold smallValid; decide +kernel

private theorem sp23934 : smallValid 23934 33 := by unfold smallValid; decide +kernel

private theorem sp23967 : smallValid 23967 32 := by unfold smallValid; decide +kernel

private theorem sp23999 : smallValid 23999 33 := by unfold smallValid; decide +kernel

private theorem sp24032 : smallValid 24032 32 := by unfold smallValid; decide +kernel

private theorem sp24064 : smallValid 24064 33 := by unfold smallValid; decide +kernel

private theorem sp24097 : smallValid 24097 64 := by unfold smallValid; decide +kernel

private theorem sp24161 : smallValid 24161 32 := by unfold smallValid; decide +kernel

private theorem sp24193 : smallValid 24193 33 := by unfold smallValid; decide +kernel

private theorem sp24226 : smallValid 24226 32 := by unfold smallValid; decide +kernel

private theorem sp24258 : smallValid 24258 33 := by unfold smallValid; decide +kernel

private theorem sp24291 : smallValid 24291 32 := by unfold smallValid; decide +kernel

private theorem sp24323 : smallValid 24323 33 := by unfold smallValid; decide +kernel

private theorem sp24356 : smallValid 24356 64 := by unfold smallValid; decide +kernel

private theorem sp24420 : smallValid 24420 32 := by unfold smallValid; decide +kernel

private theorem sp24452 : smallValid 24452 33 := by unfold smallValid; decide +kernel

private theorem sp24485 : smallValid 24485 32 := by unfold smallValid; decide +kernel

private theorem sp24517 : smallValid 24517 33 := by unfold smallValid; decide +kernel

private theorem sp24550 : smallValid 24550 32 := by unfold smallValid; decide +kernel

private theorem sp24582 : smallValid 24582 33 := by unfold smallValid; decide +kernel

private theorem sp24615 : smallValid 24615 32 := by unfold smallValid; decide +kernel

private theorem sp24647 : smallValid 24647 33 := by unfold smallValid; decide +kernel

private theorem sp24680 : smallValid 24680 32 := by unfold smallValid; decide +kernel

private theorem sp24712 : smallValid 24712 33 := by unfold smallValid; decide +kernel

private theorem sp24745 : smallValid 24745 32 := by unfold smallValid; decide +kernel

private theorem sp24777 : smallValid 24777 33 := by unfold smallValid; decide +kernel

private theorem sp24810 : smallValid 24810 32 := by unfold smallValid; decide +kernel

private theorem sp24842 : smallValid 24842 33 := by unfold smallValid; decide +kernel

private theorem sp24875 : smallValid 24875 64 := by unfold smallValid; decide +kernel

private theorem sp24939 : smallValid 24939 32 := by unfold smallValid; decide +kernel

private theorem sp24971 : smallValid 24971 33 := by unfold smallValid; decide +kernel

private theorem sp25004 : smallValid 25004 32 := by unfold smallValid; decide +kernel

private theorem sp25036 : smallValid 25036 33 := by unfold smallValid; decide +kernel

private theorem sp25069 : smallValid 25069 32 := by unfold smallValid; decide +kernel

private theorem sp25101 : smallValid 25101 33 := by unfold smallValid; decide +kernel

private theorem sp25134 : smallValid 25134 64 := by unfold smallValid; decide +kernel

private theorem sp25198 : smallValid 25198 32 := by unfold smallValid; decide +kernel

private theorem sp25230 : smallValid 25230 33 := by unfold smallValid; decide +kernel

private theorem sp25263 : smallValid 25263 32 := by unfold smallValid; decide +kernel

private theorem sp25295 : smallValid 25295 33 := by unfold smallValid; decide +kernel

private theorem sp25328 : smallValid 25328 32 := by unfold smallValid; decide +kernel

private theorem sp25360 : smallValid 25360 33 := by unfold smallValid; decide +kernel

private theorem sp25393 : smallValid 25393 64 := by unfold smallValid; decide +kernel

private theorem sp25457 : smallValid 25457 32 := by unfold smallValid; decide +kernel

private theorem sp25489 : smallValid 25489 33 := by unfold smallValid; decide +kernel

private theorem sp25522 : smallValid 25522 32 := by unfold smallValid; decide +kernel

private theorem sp25554 : smallValid 25554 33 := by unfold smallValid; decide +kernel

private theorem sp25587 : smallValid 25587 32 := by unfold smallValid; decide +kernel

private theorem sp25619 : smallValid 25619 33 := by unfold smallValid; decide +kernel

private theorem sp25652 : smallValid 25652 64 := by unfold smallValid; decide +kernel

private theorem sp25716 : smallValid 25716 32 := by unfold smallValid; decide +kernel

private theorem sp25748 : smallValid 25748 33 := by unfold smallValid; decide +kernel

private theorem sp25781 : smallValid 25781 32 := by unfold smallValid; decide +kernel

private theorem sp25813 : smallValid 25813 33 := by unfold smallValid; decide +kernel

private theorem sp25846 : smallValid 25846 32 := by unfold smallValid; decide +kernel

private theorem sp25878 : smallValid 25878 33 := by unfold smallValid; decide +kernel

private theorem sp25911 : smallValid 25911 64 := by unfold smallValid; decide +kernel

private theorem sp25975 : smallValid 25975 32 := by unfold smallValid; decide +kernel

private theorem sp26007 : smallValid 26007 33 := by unfold smallValid; decide +kernel

private theorem sp26040 : smallValid 26040 32 := by unfold smallValid; decide +kernel

private theorem sp26072 : smallValid 26072 33 := by unfold smallValid; decide +kernel

private theorem sp26105 : smallValid 26105 32 := by unfold smallValid; decide +kernel

private theorem sp26137 : smallValid 26137 33 := by unfold smallValid; decide +kernel

private theorem sp26170 : smallValid 26170 64 := by unfold smallValid; decide +kernel

private theorem sp26234 : smallValid 26234 32 := by unfold smallValid; decide +kernel

private theorem sp26266 : smallValid 26266 33 := by unfold smallValid; decide +kernel

private theorem sp26299 : smallValid 26299 32 := by unfold smallValid; decide +kernel

private theorem sp26331 : smallValid 26331 33 := by unfold smallValid; decide +kernel

private theorem sp26364 : smallValid 26364 32 := by unfold smallValid; decide +kernel

private theorem sp26396 : smallValid 26396 33 := by unfold smallValid; decide +kernel

private theorem sp26429 : smallValid 26429 64 := by unfold smallValid; decide +kernel

private theorem sp26493 : smallValid 26493 32 := by unfold smallValid; decide +kernel

private theorem sp26525 : smallValid 26525 33 := by unfold smallValid; decide +kernel

private theorem sp26558 : smallValid 26558 32 := by unfold smallValid; decide +kernel

private theorem sp26590 : smallValid 26590 33 := by unfold smallValid; decide +kernel

private theorem sp26623 : smallValid 26623 32 := by unfold smallValid; decide +kernel

private theorem sp26655 : smallValid 26655 33 := by unfold smallValid; decide +kernel

private theorem sp26688 : smallValid 26688 32 := by unfold smallValid; decide +kernel

private theorem sp26720 : smallValid 26720 33 := by unfold smallValid; decide +kernel

private theorem sp26753 : smallValid 26753 32 := by unfold smallValid; decide +kernel

private theorem sp26785 : smallValid 26785 33 := by unfold smallValid; decide +kernel

private theorem sp26818 : smallValid 26818 32 := by unfold smallValid; decide +kernel

private theorem sp26850 : smallValid 26850 33 := by unfold smallValid; decide +kernel

private theorem sp26883 : smallValid 26883 32 := by unfold smallValid; decide +kernel

private theorem sp26915 : smallValid 26915 33 := by unfold smallValid; decide +kernel

private theorem sp26948 : smallValid 26948 64 := by unfold smallValid; decide +kernel

private theorem sp27012 : smallValid 27012 32 := by unfold smallValid; decide +kernel

private theorem sp27044 : smallValid 27044 33 := by unfold smallValid; decide +kernel

private theorem sp27077 : smallValid 27077 32 := by unfold smallValid; decide +kernel

private theorem sp27109 : smallValid 27109 33 := by unfold smallValid; decide +kernel

private theorem sp27142 : smallValid 27142 32 := by unfold smallValid; decide +kernel

private theorem sp27174 : smallValid 27174 33 := by unfold smallValid; decide +kernel

private theorem sp27207 : smallValid 27207 64 := by unfold smallValid; decide +kernel

private theorem sp27271 : smallValid 27271 32 := by unfold smallValid; decide +kernel

private theorem sp27303 : smallValid 27303 33 := by unfold smallValid; decide +kernel

private theorem sp27336 : smallValid 27336 32 := by unfold smallValid; decide +kernel

private theorem sp27368 : smallValid 27368 33 := by unfold smallValid; decide +kernel

private theorem sp27401 : smallValid 27401 32 := by unfold smallValid; decide +kernel

private theorem sp27433 : smallValid 27433 33 := by unfold smallValid; decide +kernel

private theorem sp27466 : smallValid 27466 64 := by unfold smallValid; decide +kernel

private theorem sp27530 : smallValid 27530 32 := by unfold smallValid; decide +kernel

private theorem sp27562 : smallValid 27562 33 := by unfold smallValid; decide +kernel

private theorem sp27595 : smallValid 27595 32 := by unfold smallValid; decide +kernel

private theorem sp27627 : smallValid 27627 33 := by unfold smallValid; decide +kernel

private theorem sp27660 : smallValid 27660 32 := by unfold smallValid; decide +kernel

private theorem sp27692 : smallValid 27692 33 := by unfold smallValid; decide +kernel

private theorem sp27725 : smallValid 27725 64 := by unfold smallValid; decide +kernel

private theorem sp27789 : smallValid 27789 32 := by unfold smallValid; decide +kernel

private theorem sp27821 : smallValid 27821 33 := by unfold smallValid; decide +kernel

private theorem sp27854 : smallValid 27854 32 := by unfold smallValid; decide +kernel

private theorem sp27886 : smallValid 27886 33 := by unfold smallValid; decide +kernel

private theorem sp27919 : smallValid 27919 32 := by unfold smallValid; decide +kernel

private theorem sp27951 : smallValid 27951 33 := by unfold smallValid; decide +kernel

private theorem sp27984 : smallValid 27984 64 := by unfold smallValid; decide +kernel

private theorem sp28048 : smallValid 28048 32 := by unfold smallValid; decide +kernel

private theorem sp28080 : smallValid 28080 33 := by unfold smallValid; decide +kernel

private theorem sp28113 : smallValid 28113 32 := by unfold smallValid; decide +kernel

private theorem sp28145 : smallValid 28145 33 := by unfold smallValid; decide +kernel

private theorem sp28178 : smallValid 28178 32 := by unfold smallValid; decide +kernel

private theorem sp28210 : smallValid 28210 33 := by unfold smallValid; decide +kernel

private theorem sp28243 : smallValid 28243 64 := by unfold smallValid; decide +kernel

private theorem sp28307 : smallValid 28307 32 := by unfold smallValid; decide +kernel

private theorem sp28339 : smallValid 28339 33 := by unfold smallValid; decide +kernel

private theorem sp28372 : smallValid 28372 32 := by unfold smallValid; decide +kernel

private theorem sp28404 : smallValid 28404 33 := by unfold smallValid; decide +kernel

private theorem sp28437 : smallValid 28437 32 := by unfold smallValid; decide +kernel

private theorem sp28469 : smallValid 28469 33 := by unfold smallValid; decide +kernel

private theorem sp28502 : smallValid 28502 64 := by unfold smallValid; decide +kernel

private theorem sp28566 : smallValid 28566 32 := by unfold smallValid; decide +kernel

private theorem sp28598 : smallValid 28598 33 := by unfold smallValid; decide +kernel

private theorem sp28631 : smallValid 28631 32 := by unfold smallValid; decide +kernel

private theorem sp28663 : smallValid 28663 33 := by unfold smallValid; decide +kernel

private theorem sp28696 : smallValid 28696 32 := by unfold smallValid; decide +kernel

private theorem sp28728 : smallValid 28728 33 := by unfold smallValid; decide +kernel

private theorem sp28761 : smallValid 28761 32 := by unfold smallValid; decide +kernel

private theorem sp28793 : smallValid 28793 33 := by unfold smallValid; decide +kernel

private theorem sp28826 : smallValid 28826 32 := by unfold smallValid; decide +kernel

private theorem sp28858 : smallValid 28858 33 := by unfold smallValid; decide +kernel

private theorem sp28891 : smallValid 28891 32 := by unfold smallValid; decide +kernel

private theorem sp28923 : smallValid 28923 33 := by unfold smallValid; decide +kernel

private theorem sp28956 : smallValid 28956 32 := by unfold smallValid; decide +kernel

private theorem sp28988 : smallValid 28988 33 := by unfold smallValid; decide +kernel

private theorem sp29021 : smallValid 29021 64 := by unfold smallValid; decide +kernel

private theorem sp29085 : smallValid 29085 32 := by unfold smallValid; decide +kernel

private theorem sp29117 : smallValid 29117 33 := by unfold smallValid; decide +kernel

private theorem sp29150 : smallValid 29150 32 := by unfold smallValid; decide +kernel

private theorem sp29182 : smallValid 29182 33 := by unfold smallValid; decide +kernel

private theorem sp29215 : smallValid 29215 32 := by unfold smallValid; decide +kernel

private theorem sp29247 : smallValid 29247 33 := by unfold smallValid; decide +kernel

private theorem sp29280 : smallValid 29280 64 := by unfold smallValid; decide +kernel

private theorem sp29344 : smallValid 29344 32 := by unfold smallValid; decide +kernel

private theorem sp29376 : smallValid 29376 33 := by unfold smallValid; decide +kernel

private theorem sp29409 : smallValid 29409 32 := by unfold smallValid; decide +kernel

private theorem sp29441 : smallValid 29441 33 := by unfold smallValid; decide +kernel

private theorem sp29474 : smallValid 29474 32 := by unfold smallValid; decide +kernel

private theorem sp29506 : smallValid 29506 33 := by unfold smallValid; decide +kernel

private theorem sp29539 : smallValid 29539 64 := by unfold smallValid; decide +kernel

private theorem sp29603 : smallValid 29603 32 := by unfold smallValid; decide +kernel

private theorem sp29635 : smallValid 29635 33 := by unfold smallValid; decide +kernel

private theorem sp29668 : smallValid 29668 32 := by unfold smallValid; decide +kernel

private theorem sp29700 : smallValid 29700 33 := by unfold smallValid; decide +kernel

private theorem sp29733 : smallValid 29733 32 := by unfold smallValid; decide +kernel

private theorem sp29765 : smallValid 29765 33 := by unfold smallValid; decide +kernel

private theorem sp29798 : smallValid 29798 64 := by unfold smallValid; decide +kernel

private theorem sp29862 : smallValid 29862 32 := by unfold smallValid; decide +kernel

private theorem sp29894 : smallValid 29894 33 := by unfold smallValid; decide +kernel

private theorem sp29927 : smallValid 29927 32 := by unfold smallValid; decide +kernel

private theorem sp29959 : smallValid 29959 33 := by unfold smallValid; decide +kernel

private theorem sp29992 : smallValid 29992 32 := by unfold smallValid; decide +kernel

private theorem sp30024 : smallValid 30024 33 := by unfold smallValid; decide +kernel

private theorem sp30057 : smallValid 30057 64 := by unfold smallValid; decide +kernel

private theorem sp30121 : smallValid 30121 32 := by unfold smallValid; decide +kernel

private theorem sp30153 : smallValid 30153 33 := by unfold smallValid; decide +kernel

private theorem sp30186 : smallValid 30186 32 := by unfold smallValid; decide +kernel

private theorem sp30218 : smallValid 30218 33 := by unfold smallValid; decide +kernel

private theorem sp30251 : smallValid 30251 32 := by unfold smallValid; decide +kernel

private theorem sp30283 : smallValid 30283 33 := by unfold smallValid; decide +kernel

private theorem sp30316 : smallValid 30316 64 := by unfold smallValid; decide +kernel

private theorem sp30380 : smallValid 30380 32 := by unfold smallValid; decide +kernel

private theorem sp30412 : smallValid 30412 33 := by unfold smallValid; decide +kernel

private theorem sp30445 : smallValid 30445 32 := by unfold smallValid; decide +kernel

private theorem sp30477 : smallValid 30477 33 := by unfold smallValid; decide +kernel

private theorem sp30510 : smallValid 30510 32 := by unfold smallValid; decide +kernel

private theorem sp30542 : smallValid 30542 33 := by unfold smallValid; decide +kernel

private theorem sp30575 : smallValid 30575 64 := by unfold smallValid; decide +kernel

private theorem sp30639 : smallValid 30639 32 := by unfold smallValid; decide +kernel

private theorem sp30671 : smallValid 30671 33 := by unfold smallValid; decide +kernel

private theorem sp30704 : smallValid 30704 32 := by unfold smallValid; decide +kernel

private theorem sp30736 : smallValid 30736 33 := by unfold smallValid; decide +kernel

private theorem sp30769 : smallValid 30769 32 := by unfold smallValid; decide +kernel

private theorem sp30801 : smallValid 30801 33 := by unfold smallValid; decide +kernel

private theorem sp30834 : smallValid 30834 32 := by unfold smallValid; decide +kernel

private theorem sp30866 : smallValid 30866 33 := by unfold smallValid; decide +kernel

private theorem sp30899 : smallValid 30899 32 := by unfold smallValid; decide +kernel

private theorem sp30931 : smallValid 30931 33 := by unfold smallValid; decide +kernel

private theorem sp30964 : smallValid 30964 32 := by unfold smallValid; decide +kernel

private theorem sp30996 : smallValid 30996 33 := by unfold smallValid; decide +kernel

private theorem sp31029 : smallValid 31029 32 := by unfold smallValid; decide +kernel

private theorem sp31061 : smallValid 31061 33 := by unfold smallValid; decide +kernel

private theorem sp31094 : smallValid 31094 64 := by unfold smallValid; decide +kernel

private theorem sp31158 : smallValid 31158 32 := by unfold smallValid; decide +kernel

private theorem sp31190 : smallValid 31190 33 := by unfold smallValid; decide +kernel

private theorem sp31223 : smallValid 31223 32 := by unfold smallValid; decide +kernel

private theorem sp31255 : smallValid 31255 33 := by unfold smallValid; decide +kernel

private theorem sp31288 : smallValid 31288 32 := by unfold smallValid; decide +kernel

private theorem sp31320 : smallValid 31320 33 := by unfold smallValid; decide +kernel

private theorem sp31353 : smallValid 31353 64 := by unfold smallValid; decide +kernel

private theorem sp31417 : smallValid 31417 32 := by unfold smallValid; decide +kernel

private theorem sp31449 : smallValid 31449 33 := by unfold smallValid; decide +kernel

private theorem sp31482 : smallValid 31482 32 := by unfold smallValid; decide +kernel

private theorem sp31514 : smallValid 31514 33 := by unfold smallValid; decide +kernel

private theorem sp31547 : smallValid 31547 32 := by unfold smallValid; decide +kernel

private theorem sp31579 : smallValid 31579 33 := by unfold smallValid; decide +kernel

private theorem sp31612 : smallValid 31612 64 := by unfold smallValid; decide +kernel

private theorem sp31676 : smallValid 31676 32 := by unfold smallValid; decide +kernel

private theorem sp31708 : smallValid 31708 33 := by unfold smallValid; decide +kernel

private theorem sp31741 : smallValid 31741 32 := by unfold smallValid; decide +kernel

private theorem sp31773 : smallValid 31773 33 := by unfold smallValid; decide +kernel

private theorem sp31806 : smallValid 31806 32 := by unfold smallValid; decide +kernel

private theorem sp31838 : smallValid 31838 33 := by unfold smallValid; decide +kernel

private theorem sp31871 : smallValid 31871 64 := by unfold smallValid; decide +kernel

private theorem sp31935 : smallValid 31935 32 := by unfold smallValid; decide +kernel

private theorem sp31967 : smallValid 31967 33 := by unfold smallValid; decide +kernel

private theorem sp32000 : smallValid 32000 32 := by unfold smallValid; decide +kernel

private theorem sp32032 : smallValid 32032 33 := by unfold smallValid; decide +kernel

private theorem sp32065 : smallValid 32065 32 := by unfold smallValid; decide +kernel

private theorem sp32097 : smallValid 32097 33 := by unfold smallValid; decide +kernel

private theorem sp32130 : smallValid 32130 64 := by unfold smallValid; decide +kernel

private theorem sp32194 : smallValid 32194 32 := by unfold smallValid; decide +kernel

private theorem sp32226 : smallValid 32226 33 := by unfold smallValid; decide +kernel

private theorem sp32259 : smallValid 32259 32 := by unfold smallValid; decide +kernel

private theorem sp32291 : smallValid 32291 33 := by unfold smallValid; decide +kernel

private theorem sp32324 : smallValid 32324 32 := by unfold smallValid; decide +kernel

private theorem sp32356 : smallValid 32356 33 := by unfold smallValid; decide +kernel

private theorem sp32389 : smallValid 32389 64 := by unfold smallValid; decide +kernel

private theorem sp32453 : smallValid 32453 32 := by unfold smallValid; decide +kernel

private theorem sp32485 : smallValid 32485 33 := by unfold smallValid; decide +kernel

private theorem sp32518 : smallValid 32518 32 := by unfold smallValid; decide +kernel

private theorem sp32550 : smallValid 32550 33 := by unfold smallValid; decide +kernel

private theorem sp32583 : smallValid 32583 32 := by unfold smallValid; decide +kernel

private theorem sp32615 : smallValid 32615 33 := by unfold smallValid; decide +kernel

private theorem sp32648 : smallValid 32648 64 := by unfold smallValid; decide +kernel

private theorem sp32712 : smallValid 32712 32 := by unfold smallValid; decide +kernel

private theorem sp32744 : smallValid 32744 33 := by unfold smallValid; decide +kernel

private theorem sp32777 : smallValid 32777 32 := by unfold smallValid; decide +kernel

private theorem sp32809 : smallValid 32809 33 := by unfold smallValid; decide +kernel

private theorem sp32842 : smallValid 32842 32 := by unfold smallValid; decide +kernel

private theorem sp32874 : smallValid 32874 33 := by unfold smallValid; decide +kernel

private theorem sp32907 : smallValid 32907 32 := by unfold smallValid; decide +kernel

private theorem sp32939 : smallValid 32939 33 := by unfold smallValid; decide +kernel

private theorem sp32972 : smallValid 32972 32 := by unfold smallValid; decide +kernel

private theorem sp33004 : smallValid 33004 33 := by unfold smallValid; decide +kernel

private theorem sp33037 : smallValid 33037 32 := by unfold smallValid; decide +kernel

private theorem sp33069 : smallValid 33069 33 := by unfold smallValid; decide +kernel

private theorem sp33102 : smallValid 33102 32 := by unfold smallValid; decide +kernel

private theorem sp33134 : smallValid 33134 33 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤33166) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 33167 := (joinSmall (lo:=0) (a:=16583) (b:=16584) (joinSmall (lo:=0) (a:=8291) (b:=8292) (joinSmall (lo:=0) (a:=4145) (b:=4146) (joinSmall (lo:=0) (a:=2072) (b:=2073) (joinSmall (lo:=0) (a:=1036) (b:=1036) (joinSmall (lo:=0) (a:=518) (b:=518) (joinSmall (lo:=0) (a:=259) (b:=259) (joinSmall (lo:=0) (a:=129) (b:=130) (joinSmall (lo:=0) (a:=64) (b:=65) sp0 (joinSmall (lo:=64) (a:=32) (b:=33) sp64 sp96)) (joinSmall (lo:=129) (a:=65) (b:=65) (joinSmall (lo:=129) (a:=32) (b:=33) sp129 sp161) (joinSmall (lo:=194) (a:=32) (b:=33) sp194 sp226))) (joinSmall (lo:=259) (a:=129) (b:=130) (joinSmall (lo:=259) (a:=64) (b:=65) sp259 (joinSmall (lo:=323) (a:=32) (b:=33) sp323 sp355)) (joinSmall (lo:=388) (a:=65) (b:=65) (joinSmall (lo:=388) (a:=32) (b:=33) sp388 sp420) (joinSmall (lo:=453) (a:=32) (b:=33) sp453 sp485)))) (joinSmall (lo:=518) (a:=259) (b:=259) (joinSmall (lo:=518) (a:=129) (b:=130) (joinSmall (lo:=518) (a:=64) (b:=65) sp518 (joinSmall (lo:=582) (a:=32) (b:=33) sp582 sp614)) (joinSmall (lo:=647) (a:=65) (b:=65) (joinSmall (lo:=647) (a:=32) (b:=33) sp647 sp679) (joinSmall (lo:=712) (a:=32) (b:=33) sp712 sp744))) (joinSmall (lo:=777) (a:=129) (b:=130) (joinSmall (lo:=777) (a:=64) (b:=65) sp777 (joinSmall (lo:=841) (a:=32) (b:=33) sp841 sp873)) (joinSmall (lo:=906) (a:=65) (b:=65) (joinSmall (lo:=906) (a:=32) (b:=33) sp906 sp938) (joinSmall (lo:=971) (a:=32) (b:=33) sp971 sp1003))))) (joinSmall (lo:=1036) (a:=518) (b:=518) (joinSmall (lo:=1036) (a:=259) (b:=259) (joinSmall (lo:=1036) (a:=129) (b:=130) (joinSmall (lo:=1036) (a:=64) (b:=65) sp1036 (joinSmall (lo:=1100) (a:=32) (b:=33) sp1100 sp1132)) (joinSmall (lo:=1165) (a:=65) (b:=65) (joinSmall (lo:=1165) (a:=32) (b:=33) sp1165 sp1197) (joinSmall (lo:=1230) (a:=32) (b:=33) sp1230 sp1262))) (joinSmall (lo:=1295) (a:=129) (b:=130) (joinSmall (lo:=1295) (a:=64) (b:=65) sp1295 (joinSmall (lo:=1359) (a:=32) (b:=33) sp1359 sp1391)) (joinSmall (lo:=1424) (a:=65) (b:=65) (joinSmall (lo:=1424) (a:=32) (b:=33) sp1424 sp1456) (joinSmall (lo:=1489) (a:=32) (b:=33) sp1489 sp1521)))) (joinSmall (lo:=1554) (a:=259) (b:=259) (joinSmall (lo:=1554) (a:=129) (b:=130) (joinSmall (lo:=1554) (a:=64) (b:=65) sp1554 (joinSmall (lo:=1618) (a:=32) (b:=33) sp1618 sp1650)) (joinSmall (lo:=1683) (a:=65) (b:=65) (joinSmall (lo:=1683) (a:=32) (b:=33) sp1683 sp1715) (joinSmall (lo:=1748) (a:=32) (b:=33) sp1748 sp1780))) (joinSmall (lo:=1813) (a:=129) (b:=130) (joinSmall (lo:=1813) (a:=64) (b:=65) sp1813 (joinSmall (lo:=1877) (a:=32) (b:=33) sp1877 sp1909)) (joinSmall (lo:=1942) (a:=65) (b:=65) (joinSmall (lo:=1942) (a:=32) (b:=33) sp1942 sp1974) (joinSmall (lo:=2007) (a:=32) (b:=33) sp2007 sp2039)))))) (joinSmall (lo:=2072) (a:=1036) (b:=1037) (joinSmall (lo:=2072) (a:=518) (b:=518) (joinSmall (lo:=2072) (a:=259) (b:=259) (joinSmall (lo:=2072) (a:=129) (b:=130) (joinSmall (lo:=2072) (a:=64) (b:=65) sp2072 (joinSmall (lo:=2136) (a:=32) (b:=33) sp2136 sp2168)) (joinSmall (lo:=2201) (a:=65) (b:=65) (joinSmall (lo:=2201) (a:=32) (b:=33) sp2201 sp2233) (joinSmall (lo:=2266) (a:=32) (b:=33) sp2266 sp2298))) (joinSmall (lo:=2331) (a:=129) (b:=130) (joinSmall (lo:=2331) (a:=64) (b:=65) sp2331 (joinSmall (lo:=2395) (a:=32) (b:=33) sp2395 sp2427)) (joinSmall (lo:=2460) (a:=65) (b:=65) (joinSmall (lo:=2460) (a:=32) (b:=33) sp2460 sp2492) (joinSmall (lo:=2525) (a:=32) (b:=33) sp2525 sp2557)))) (joinSmall (lo:=2590) (a:=259) (b:=259) (joinSmall (lo:=2590) (a:=129) (b:=130) (joinSmall (lo:=2590) (a:=64) (b:=65) sp2590 (joinSmall (lo:=2654) (a:=32) (b:=33) sp2654 sp2686)) (joinSmall (lo:=2719) (a:=65) (b:=65) (joinSmall (lo:=2719) (a:=32) (b:=33) sp2719 sp2751) (joinSmall (lo:=2784) (a:=32) (b:=33) sp2784 sp2816))) (joinSmall (lo:=2849) (a:=129) (b:=130) (joinSmall (lo:=2849) (a:=64) (b:=65) sp2849 (joinSmall (lo:=2913) (a:=32) (b:=33) sp2913 sp2945)) (joinSmall (lo:=2978) (a:=65) (b:=65) (joinSmall (lo:=2978) (a:=32) (b:=33) sp2978 sp3010) (joinSmall (lo:=3043) (a:=32) (b:=33) sp3043 sp3075))))) (joinSmall (lo:=3108) (a:=518) (b:=519) (joinSmall (lo:=3108) (a:=259) (b:=259) (joinSmall (lo:=3108) (a:=129) (b:=130) (joinSmall (lo:=3108) (a:=64) (b:=65) sp3108 (joinSmall (lo:=3172) (a:=32) (b:=33) sp3172 sp3204)) (joinSmall (lo:=3237) (a:=65) (b:=65) (joinSmall (lo:=3237) (a:=32) (b:=33) sp3237 sp3269) (joinSmall (lo:=3302) (a:=32) (b:=33) sp3302 sp3334))) (joinSmall (lo:=3367) (a:=129) (b:=130) (joinSmall (lo:=3367) (a:=64) (b:=65) sp3367 (joinSmall (lo:=3431) (a:=32) (b:=33) sp3431 sp3463)) (joinSmall (lo:=3496) (a:=65) (b:=65) (joinSmall (lo:=3496) (a:=32) (b:=33) sp3496 sp3528) (joinSmall (lo:=3561) (a:=32) (b:=33) sp3561 sp3593)))) (joinSmall (lo:=3626) (a:=259) (b:=260) (joinSmall (lo:=3626) (a:=129) (b:=130) (joinSmall (lo:=3626) (a:=64) (b:=65) sp3626 (joinSmall (lo:=3690) (a:=32) (b:=33) sp3690 sp3722)) (joinSmall (lo:=3755) (a:=65) (b:=65) (joinSmall (lo:=3755) (a:=32) (b:=33) sp3755 sp3787) (joinSmall (lo:=3820) (a:=32) (b:=33) sp3820 sp3852))) (joinSmall (lo:=3885) (a:=130) (b:=130) (joinSmall (lo:=3885) (a:=65) (b:=65) (joinSmall (lo:=3885) (a:=32) (b:=33) sp3885 sp3917) (joinSmall (lo:=3950) (a:=32) (b:=33) sp3950 sp3982)) (joinSmall (lo:=4015) (a:=65) (b:=65) (joinSmall (lo:=4015) (a:=32) (b:=33) sp4015 sp4047) (joinSmall (lo:=4080) (a:=32) (b:=33) sp4080 sp4112))))))) (joinSmall (lo:=4145) (a:=2073) (b:=2073) (joinSmall (lo:=4145) (a:=1036) (b:=1037) (joinSmall (lo:=4145) (a:=518) (b:=518) (joinSmall (lo:=4145) (a:=259) (b:=259) (joinSmall (lo:=4145) (a:=129) (b:=130) (joinSmall (lo:=4145) (a:=64) (b:=65) sp4145 (joinSmall (lo:=4209) (a:=32) (b:=33) sp4209 sp4241)) (joinSmall (lo:=4274) (a:=65) (b:=65) (joinSmall (lo:=4274) (a:=32) (b:=33) sp4274 sp4306) (joinSmall (lo:=4339) (a:=32) (b:=33) sp4339 sp4371))) (joinSmall (lo:=4404) (a:=129) (b:=130) (joinSmall (lo:=4404) (a:=64) (b:=65) sp4404 (joinSmall (lo:=4468) (a:=32) (b:=33) sp4468 sp4500)) (joinSmall (lo:=4533) (a:=65) (b:=65) (joinSmall (lo:=4533) (a:=32) (b:=33) sp4533 sp4565) (joinSmall (lo:=4598) (a:=32) (b:=33) sp4598 sp4630)))) (joinSmall (lo:=4663) (a:=259) (b:=259) (joinSmall (lo:=4663) (a:=129) (b:=130) (joinSmall (lo:=4663) (a:=64) (b:=65) sp4663 (joinSmall (lo:=4727) (a:=32) (b:=33) sp4727 sp4759)) (joinSmall (lo:=4792) (a:=65) (b:=65) (joinSmall (lo:=4792) (a:=32) (b:=33) sp4792 sp4824) (joinSmall (lo:=4857) (a:=32) (b:=33) sp4857 sp4889))) (joinSmall (lo:=4922) (a:=129) (b:=130) (joinSmall (lo:=4922) (a:=64) (b:=65) sp4922 (joinSmall (lo:=4986) (a:=32) (b:=33) sp4986 sp5018)) (joinSmall (lo:=5051) (a:=65) (b:=65) (joinSmall (lo:=5051) (a:=32) (b:=33) sp5051 sp5083) (joinSmall (lo:=5116) (a:=32) (b:=33) sp5116 sp5148))))) (joinSmall (lo:=5181) (a:=518) (b:=519) (joinSmall (lo:=5181) (a:=259) (b:=259) (joinSmall (lo:=5181) (a:=129) (b:=130) (joinSmall (lo:=5181) (a:=64) (b:=65) sp5181 (joinSmall (lo:=5245) (a:=32) (b:=33) sp5245 sp5277)) (joinSmall (lo:=5310) (a:=65) (b:=65) (joinSmall (lo:=5310) (a:=32) (b:=33) sp5310 sp5342) (joinSmall (lo:=5375) (a:=32) (b:=33) sp5375 sp5407))) (joinSmall (lo:=5440) (a:=129) (b:=130) (joinSmall (lo:=5440) (a:=64) (b:=65) sp5440 (joinSmall (lo:=5504) (a:=32) (b:=33) sp5504 sp5536)) (joinSmall (lo:=5569) (a:=65) (b:=65) (joinSmall (lo:=5569) (a:=32) (b:=33) sp5569 sp5601) (joinSmall (lo:=5634) (a:=32) (b:=33) sp5634 sp5666)))) (joinSmall (lo:=5699) (a:=259) (b:=260) (joinSmall (lo:=5699) (a:=129) (b:=130) (joinSmall (lo:=5699) (a:=64) (b:=65) sp5699 (joinSmall (lo:=5763) (a:=32) (b:=33) sp5763 sp5795)) (joinSmall (lo:=5828) (a:=65) (b:=65) (joinSmall (lo:=5828) (a:=32) (b:=33) sp5828 sp5860) (joinSmall (lo:=5893) (a:=32) (b:=33) sp5893 sp5925))) (joinSmall (lo:=5958) (a:=130) (b:=130) (joinSmall (lo:=5958) (a:=65) (b:=65) (joinSmall (lo:=5958) (a:=32) (b:=33) sp5958 sp5990) (joinSmall (lo:=6023) (a:=32) (b:=33) sp6023 sp6055)) (joinSmall (lo:=6088) (a:=65) (b:=65) (joinSmall (lo:=6088) (a:=32) (b:=33) sp6088 sp6120) (joinSmall (lo:=6153) (a:=32) (b:=33) sp6153 sp6185)))))) (joinSmall (lo:=6218) (a:=1036) (b:=1037) (joinSmall (lo:=6218) (a:=518) (b:=518) (joinSmall (lo:=6218) (a:=259) (b:=259) (joinSmall (lo:=6218) (a:=129) (b:=130) (joinSmall (lo:=6218) (a:=64) (b:=65) sp6218 (joinSmall (lo:=6282) (a:=32) (b:=33) sp6282 sp6314)) (joinSmall (lo:=6347) (a:=65) (b:=65) (joinSmall (lo:=6347) (a:=32) (b:=33) sp6347 sp6379) (joinSmall (lo:=6412) (a:=32) (b:=33) sp6412 sp6444))) (joinSmall (lo:=6477) (a:=129) (b:=130) (joinSmall (lo:=6477) (a:=64) (b:=65) sp6477 (joinSmall (lo:=6541) (a:=32) (b:=33) sp6541 sp6573)) (joinSmall (lo:=6606) (a:=65) (b:=65) (joinSmall (lo:=6606) (a:=32) (b:=33) sp6606 sp6638) (joinSmall (lo:=6671) (a:=32) (b:=33) sp6671 sp6703)))) (joinSmall (lo:=6736) (a:=259) (b:=259) (joinSmall (lo:=6736) (a:=129) (b:=130) (joinSmall (lo:=6736) (a:=64) (b:=65) sp6736 (joinSmall (lo:=6800) (a:=32) (b:=33) sp6800 sp6832)) (joinSmall (lo:=6865) (a:=65) (b:=65) (joinSmall (lo:=6865) (a:=32) (b:=33) sp6865 sp6897) (joinSmall (lo:=6930) (a:=32) (b:=33) sp6930 sp6962))) (joinSmall (lo:=6995) (a:=129) (b:=130) (joinSmall (lo:=6995) (a:=64) (b:=65) sp6995 (joinSmall (lo:=7059) (a:=32) (b:=33) sp7059 sp7091)) (joinSmall (lo:=7124) (a:=65) (b:=65) (joinSmall (lo:=7124) (a:=32) (b:=33) sp7124 sp7156) (joinSmall (lo:=7189) (a:=32) (b:=33) sp7189 sp7221))))) (joinSmall (lo:=7254) (a:=518) (b:=519) (joinSmall (lo:=7254) (a:=259) (b:=259) (joinSmall (lo:=7254) (a:=129) (b:=130) (joinSmall (lo:=7254) (a:=64) (b:=65) sp7254 (joinSmall (lo:=7318) (a:=32) (b:=33) sp7318 sp7350)) (joinSmall (lo:=7383) (a:=65) (b:=65) (joinSmall (lo:=7383) (a:=32) (b:=33) sp7383 sp7415) (joinSmall (lo:=7448) (a:=32) (b:=33) sp7448 sp7480))) (joinSmall (lo:=7513) (a:=129) (b:=130) (joinSmall (lo:=7513) (a:=64) (b:=65) sp7513 (joinSmall (lo:=7577) (a:=32) (b:=33) sp7577 sp7609)) (joinSmall (lo:=7642) (a:=65) (b:=65) (joinSmall (lo:=7642) (a:=32) (b:=33) sp7642 sp7674) (joinSmall (lo:=7707) (a:=32) (b:=33) sp7707 sp7739)))) (joinSmall (lo:=7772) (a:=259) (b:=260) (joinSmall (lo:=7772) (a:=129) (b:=130) (joinSmall (lo:=7772) (a:=64) (b:=65) sp7772 (joinSmall (lo:=7836) (a:=32) (b:=33) sp7836 sp7868)) (joinSmall (lo:=7901) (a:=65) (b:=65) (joinSmall (lo:=7901) (a:=32) (b:=33) sp7901 sp7933) (joinSmall (lo:=7966) (a:=32) (b:=33) sp7966 sp7998))) (joinSmall (lo:=8031) (a:=130) (b:=130) (joinSmall (lo:=8031) (a:=65) (b:=65) (joinSmall (lo:=8031) (a:=32) (b:=33) sp8031 sp8063) (joinSmall (lo:=8096) (a:=32) (b:=33) sp8096 sp8128)) (joinSmall (lo:=8161) (a:=65) (b:=65) (joinSmall (lo:=8161) (a:=32) (b:=33) sp8161 sp8193) (joinSmall (lo:=8226) (a:=32) (b:=33) sp8226 sp8258)))))))) (joinSmall (lo:=8291) (a:=4146) (b:=4146) (joinSmall (lo:=8291) (a:=2073) (b:=2073) (joinSmall (lo:=8291) (a:=1036) (b:=1037) (joinSmall (lo:=8291) (a:=518) (b:=518) (joinSmall (lo:=8291) (a:=259) (b:=259) (joinSmall (lo:=8291) (a:=129) (b:=130) (joinSmall (lo:=8291) (a:=64) (b:=65) sp8291 (joinSmall (lo:=8355) (a:=32) (b:=33) sp8355 sp8387)) (joinSmall (lo:=8420) (a:=65) (b:=65) (joinSmall (lo:=8420) (a:=32) (b:=33) sp8420 sp8452) (joinSmall (lo:=8485) (a:=32) (b:=33) sp8485 sp8517))) (joinSmall (lo:=8550) (a:=129) (b:=130) (joinSmall (lo:=8550) (a:=64) (b:=65) sp8550 (joinSmall (lo:=8614) (a:=32) (b:=33) sp8614 sp8646)) (joinSmall (lo:=8679) (a:=65) (b:=65) (joinSmall (lo:=8679) (a:=32) (b:=33) sp8679 sp8711) (joinSmall (lo:=8744) (a:=32) (b:=33) sp8744 sp8776)))) (joinSmall (lo:=8809) (a:=259) (b:=259) (joinSmall (lo:=8809) (a:=129) (b:=130) (joinSmall (lo:=8809) (a:=64) (b:=65) sp8809 (joinSmall (lo:=8873) (a:=32) (b:=33) sp8873 sp8905)) (joinSmall (lo:=8938) (a:=65) (b:=65) (joinSmall (lo:=8938) (a:=32) (b:=33) sp8938 sp8970) (joinSmall (lo:=9003) (a:=32) (b:=33) sp9003 sp9035))) (joinSmall (lo:=9068) (a:=129) (b:=130) (joinSmall (lo:=9068) (a:=64) (b:=65) sp9068 (joinSmall (lo:=9132) (a:=32) (b:=33) sp9132 sp9164)) (joinSmall (lo:=9197) (a:=65) (b:=65) (joinSmall (lo:=9197) (a:=32) (b:=33) sp9197 sp9229) (joinSmall (lo:=9262) (a:=32) (b:=33) sp9262 sp9294))))) (joinSmall (lo:=9327) (a:=518) (b:=519) (joinSmall (lo:=9327) (a:=259) (b:=259) (joinSmall (lo:=9327) (a:=129) (b:=130) (joinSmall (lo:=9327) (a:=64) (b:=65) sp9327 (joinSmall (lo:=9391) (a:=32) (b:=33) sp9391 sp9423)) (joinSmall (lo:=9456) (a:=65) (b:=65) (joinSmall (lo:=9456) (a:=32) (b:=33) sp9456 sp9488) (joinSmall (lo:=9521) (a:=32) (b:=33) sp9521 sp9553))) (joinSmall (lo:=9586) (a:=129) (b:=130) (joinSmall (lo:=9586) (a:=64) (b:=65) sp9586 (joinSmall (lo:=9650) (a:=32) (b:=33) sp9650 sp9682)) (joinSmall (lo:=9715) (a:=65) (b:=65) (joinSmall (lo:=9715) (a:=32) (b:=33) sp9715 sp9747) (joinSmall (lo:=9780) (a:=32) (b:=33) sp9780 sp9812)))) (joinSmall (lo:=9845) (a:=259) (b:=260) (joinSmall (lo:=9845) (a:=129) (b:=130) (joinSmall (lo:=9845) (a:=64) (b:=65) sp9845 (joinSmall (lo:=9909) (a:=32) (b:=33) sp9909 sp9941)) (joinSmall (lo:=9974) (a:=65) (b:=65) (joinSmall (lo:=9974) (a:=32) (b:=33) sp9974 sp10006) (joinSmall (lo:=10039) (a:=32) (b:=33) sp10039 sp10071))) (joinSmall (lo:=10104) (a:=130) (b:=130) (joinSmall (lo:=10104) (a:=65) (b:=65) (joinSmall (lo:=10104) (a:=32) (b:=33) sp10104 sp10136) (joinSmall (lo:=10169) (a:=32) (b:=33) sp10169 sp10201)) (joinSmall (lo:=10234) (a:=65) (b:=65) (joinSmall (lo:=10234) (a:=32) (b:=33) sp10234 sp10266) (joinSmall (lo:=10299) (a:=32) (b:=33) sp10299 sp10331)))))) (joinSmall (lo:=10364) (a:=1036) (b:=1037) (joinSmall (lo:=10364) (a:=518) (b:=518) (joinSmall (lo:=10364) (a:=259) (b:=259) (joinSmall (lo:=10364) (a:=129) (b:=130) (joinSmall (lo:=10364) (a:=64) (b:=65) sp10364 (joinSmall (lo:=10428) (a:=32) (b:=33) sp10428 sp10460)) (joinSmall (lo:=10493) (a:=65) (b:=65) (joinSmall (lo:=10493) (a:=32) (b:=33) sp10493 sp10525) (joinSmall (lo:=10558) (a:=32) (b:=33) sp10558 sp10590))) (joinSmall (lo:=10623) (a:=129) (b:=130) (joinSmall (lo:=10623) (a:=64) (b:=65) sp10623 (joinSmall (lo:=10687) (a:=32) (b:=33) sp10687 sp10719)) (joinSmall (lo:=10752) (a:=65) (b:=65) (joinSmall (lo:=10752) (a:=32) (b:=33) sp10752 sp10784) (joinSmall (lo:=10817) (a:=32) (b:=33) sp10817 sp10849)))) (joinSmall (lo:=10882) (a:=259) (b:=259) (joinSmall (lo:=10882) (a:=129) (b:=130) (joinSmall (lo:=10882) (a:=64) (b:=65) sp10882 (joinSmall (lo:=10946) (a:=32) (b:=33) sp10946 sp10978)) (joinSmall (lo:=11011) (a:=65) (b:=65) (joinSmall (lo:=11011) (a:=32) (b:=33) sp11011 sp11043) (joinSmall (lo:=11076) (a:=32) (b:=33) sp11076 sp11108))) (joinSmall (lo:=11141) (a:=129) (b:=130) (joinSmall (lo:=11141) (a:=64) (b:=65) sp11141 (joinSmall (lo:=11205) (a:=32) (b:=33) sp11205 sp11237)) (joinSmall (lo:=11270) (a:=65) (b:=65) (joinSmall (lo:=11270) (a:=32) (b:=33) sp11270 sp11302) (joinSmall (lo:=11335) (a:=32) (b:=33) sp11335 sp11367))))) (joinSmall (lo:=11400) (a:=518) (b:=519) (joinSmall (lo:=11400) (a:=259) (b:=259) (joinSmall (lo:=11400) (a:=129) (b:=130) (joinSmall (lo:=11400) (a:=64) (b:=65) sp11400 (joinSmall (lo:=11464) (a:=32) (b:=33) sp11464 sp11496)) (joinSmall (lo:=11529) (a:=65) (b:=65) (joinSmall (lo:=11529) (a:=32) (b:=33) sp11529 sp11561) (joinSmall (lo:=11594) (a:=32) (b:=33) sp11594 sp11626))) (joinSmall (lo:=11659) (a:=129) (b:=130) (joinSmall (lo:=11659) (a:=64) (b:=65) sp11659 (joinSmall (lo:=11723) (a:=32) (b:=33) sp11723 sp11755)) (joinSmall (lo:=11788) (a:=65) (b:=65) (joinSmall (lo:=11788) (a:=32) (b:=33) sp11788 sp11820) (joinSmall (lo:=11853) (a:=32) (b:=33) sp11853 sp11885)))) (joinSmall (lo:=11918) (a:=259) (b:=260) (joinSmall (lo:=11918) (a:=129) (b:=130) (joinSmall (lo:=11918) (a:=64) (b:=65) sp11918 (joinSmall (lo:=11982) (a:=32) (b:=33) sp11982 sp12014)) (joinSmall (lo:=12047) (a:=65) (b:=65) (joinSmall (lo:=12047) (a:=32) (b:=33) sp12047 sp12079) (joinSmall (lo:=12112) (a:=32) (b:=33) sp12112 sp12144))) (joinSmall (lo:=12177) (a:=130) (b:=130) (joinSmall (lo:=12177) (a:=65) (b:=65) (joinSmall (lo:=12177) (a:=32) (b:=33) sp12177 sp12209) (joinSmall (lo:=12242) (a:=32) (b:=33) sp12242 sp12274)) (joinSmall (lo:=12307) (a:=65) (b:=65) (joinSmall (lo:=12307) (a:=32) (b:=33) sp12307 sp12339) (joinSmall (lo:=12372) (a:=32) (b:=33) sp12372 sp12404))))))) (joinSmall (lo:=12437) (a:=2073) (b:=2073) (joinSmall (lo:=12437) (a:=1036) (b:=1037) (joinSmall (lo:=12437) (a:=518) (b:=518) (joinSmall (lo:=12437) (a:=259) (b:=259) (joinSmall (lo:=12437) (a:=129) (b:=130) (joinSmall (lo:=12437) (a:=64) (b:=65) sp12437 (joinSmall (lo:=12501) (a:=32) (b:=33) sp12501 sp12533)) (joinSmall (lo:=12566) (a:=65) (b:=65) (joinSmall (lo:=12566) (a:=32) (b:=33) sp12566 sp12598) (joinSmall (lo:=12631) (a:=32) (b:=33) sp12631 sp12663))) (joinSmall (lo:=12696) (a:=129) (b:=130) (joinSmall (lo:=12696) (a:=64) (b:=65) sp12696 (joinSmall (lo:=12760) (a:=32) (b:=33) sp12760 sp12792)) (joinSmall (lo:=12825) (a:=65) (b:=65) (joinSmall (lo:=12825) (a:=32) (b:=33) sp12825 sp12857) (joinSmall (lo:=12890) (a:=32) (b:=33) sp12890 sp12922)))) (joinSmall (lo:=12955) (a:=259) (b:=259) (joinSmall (lo:=12955) (a:=129) (b:=130) (joinSmall (lo:=12955) (a:=64) (b:=65) sp12955 (joinSmall (lo:=13019) (a:=32) (b:=33) sp13019 sp13051)) (joinSmall (lo:=13084) (a:=65) (b:=65) (joinSmall (lo:=13084) (a:=32) (b:=33) sp13084 sp13116) (joinSmall (lo:=13149) (a:=32) (b:=33) sp13149 sp13181))) (joinSmall (lo:=13214) (a:=129) (b:=130) (joinSmall (lo:=13214) (a:=64) (b:=65) sp13214 (joinSmall (lo:=13278) (a:=32) (b:=33) sp13278 sp13310)) (joinSmall (lo:=13343) (a:=65) (b:=65) (joinSmall (lo:=13343) (a:=32) (b:=33) sp13343 sp13375) (joinSmall (lo:=13408) (a:=32) (b:=33) sp13408 sp13440))))) (joinSmall (lo:=13473) (a:=518) (b:=519) (joinSmall (lo:=13473) (a:=259) (b:=259) (joinSmall (lo:=13473) (a:=129) (b:=130) (joinSmall (lo:=13473) (a:=64) (b:=65) sp13473 (joinSmall (lo:=13537) (a:=32) (b:=33) sp13537 sp13569)) (joinSmall (lo:=13602) (a:=65) (b:=65) (joinSmall (lo:=13602) (a:=32) (b:=33) sp13602 sp13634) (joinSmall (lo:=13667) (a:=32) (b:=33) sp13667 sp13699))) (joinSmall (lo:=13732) (a:=129) (b:=130) (joinSmall (lo:=13732) (a:=64) (b:=65) sp13732 (joinSmall (lo:=13796) (a:=32) (b:=33) sp13796 sp13828)) (joinSmall (lo:=13861) (a:=65) (b:=65) (joinSmall (lo:=13861) (a:=32) (b:=33) sp13861 sp13893) (joinSmall (lo:=13926) (a:=32) (b:=33) sp13926 sp13958)))) (joinSmall (lo:=13991) (a:=259) (b:=260) (joinSmall (lo:=13991) (a:=129) (b:=130) (joinSmall (lo:=13991) (a:=64) (b:=65) sp13991 (joinSmall (lo:=14055) (a:=32) (b:=33) sp14055 sp14087)) (joinSmall (lo:=14120) (a:=65) (b:=65) (joinSmall (lo:=14120) (a:=32) (b:=33) sp14120 sp14152) (joinSmall (lo:=14185) (a:=32) (b:=33) sp14185 sp14217))) (joinSmall (lo:=14250) (a:=130) (b:=130) (joinSmall (lo:=14250) (a:=65) (b:=65) (joinSmall (lo:=14250) (a:=32) (b:=33) sp14250 sp14282) (joinSmall (lo:=14315) (a:=32) (b:=33) sp14315 sp14347)) (joinSmall (lo:=14380) (a:=65) (b:=65) (joinSmall (lo:=14380) (a:=32) (b:=33) sp14380 sp14412) (joinSmall (lo:=14445) (a:=32) (b:=33) sp14445 sp14477)))))) (joinSmall (lo:=14510) (a:=1036) (b:=1037) (joinSmall (lo:=14510) (a:=518) (b:=518) (joinSmall (lo:=14510) (a:=259) (b:=259) (joinSmall (lo:=14510) (a:=129) (b:=130) (joinSmall (lo:=14510) (a:=64) (b:=65) sp14510 (joinSmall (lo:=14574) (a:=32) (b:=33) sp14574 sp14606)) (joinSmall (lo:=14639) (a:=65) (b:=65) (joinSmall (lo:=14639) (a:=32) (b:=33) sp14639 sp14671) (joinSmall (lo:=14704) (a:=32) (b:=33) sp14704 sp14736))) (joinSmall (lo:=14769) (a:=129) (b:=130) (joinSmall (lo:=14769) (a:=64) (b:=65) sp14769 (joinSmall (lo:=14833) (a:=32) (b:=33) sp14833 sp14865)) (joinSmall (lo:=14898) (a:=65) (b:=65) (joinSmall (lo:=14898) (a:=32) (b:=33) sp14898 sp14930) (joinSmall (lo:=14963) (a:=32) (b:=33) sp14963 sp14995)))) (joinSmall (lo:=15028) (a:=259) (b:=259) (joinSmall (lo:=15028) (a:=129) (b:=130) (joinSmall (lo:=15028) (a:=64) (b:=65) sp15028 (joinSmall (lo:=15092) (a:=32) (b:=33) sp15092 sp15124)) (joinSmall (lo:=15157) (a:=65) (b:=65) (joinSmall (lo:=15157) (a:=32) (b:=33) sp15157 sp15189) (joinSmall (lo:=15222) (a:=32) (b:=33) sp15222 sp15254))) (joinSmall (lo:=15287) (a:=129) (b:=130) (joinSmall (lo:=15287) (a:=64) (b:=65) sp15287 (joinSmall (lo:=15351) (a:=32) (b:=33) sp15351 sp15383)) (joinSmall (lo:=15416) (a:=65) (b:=65) (joinSmall (lo:=15416) (a:=32) (b:=33) sp15416 sp15448) (joinSmall (lo:=15481) (a:=32) (b:=33) sp15481 sp15513))))) (joinSmall (lo:=15546) (a:=518) (b:=519) (joinSmall (lo:=15546) (a:=259) (b:=259) (joinSmall (lo:=15546) (a:=129) (b:=130) (joinSmall (lo:=15546) (a:=64) (b:=65) sp15546 (joinSmall (lo:=15610) (a:=32) (b:=33) sp15610 sp15642)) (joinSmall (lo:=15675) (a:=65) (b:=65) (joinSmall (lo:=15675) (a:=32) (b:=33) sp15675 sp15707) (joinSmall (lo:=15740) (a:=32) (b:=33) sp15740 sp15772))) (joinSmall (lo:=15805) (a:=129) (b:=130) (joinSmall (lo:=15805) (a:=64) (b:=65) sp15805 (joinSmall (lo:=15869) (a:=32) (b:=33) sp15869 sp15901)) (joinSmall (lo:=15934) (a:=65) (b:=65) (joinSmall (lo:=15934) (a:=32) (b:=33) sp15934 sp15966) (joinSmall (lo:=15999) (a:=32) (b:=33) sp15999 sp16031)))) (joinSmall (lo:=16064) (a:=259) (b:=260) (joinSmall (lo:=16064) (a:=129) (b:=130) (joinSmall (lo:=16064) (a:=64) (b:=65) sp16064 (joinSmall (lo:=16128) (a:=32) (b:=33) sp16128 sp16160)) (joinSmall (lo:=16193) (a:=65) (b:=65) (joinSmall (lo:=16193) (a:=32) (b:=33) sp16193 sp16225) (joinSmall (lo:=16258) (a:=32) (b:=33) sp16258 sp16290))) (joinSmall (lo:=16323) (a:=130) (b:=130) (joinSmall (lo:=16323) (a:=65) (b:=65) (joinSmall (lo:=16323) (a:=32) (b:=33) sp16323 sp16355) (joinSmall (lo:=16388) (a:=32) (b:=33) sp16388 sp16420)) (joinSmall (lo:=16453) (a:=65) (b:=65) (joinSmall (lo:=16453) (a:=32) (b:=33) sp16453 sp16485) (joinSmall (lo:=16518) (a:=32) (b:=33) sp16518 sp16550))))))))) (joinSmall (lo:=16583) (a:=8292) (b:=8292) (joinSmall (lo:=16583) (a:=4146) (b:=4146) (joinSmall (lo:=16583) (a:=2073) (b:=2073) (joinSmall (lo:=16583) (a:=1036) (b:=1037) (joinSmall (lo:=16583) (a:=518) (b:=518) (joinSmall (lo:=16583) (a:=259) (b:=259) (joinSmall (lo:=16583) (a:=129) (b:=130) (joinSmall (lo:=16583) (a:=64) (b:=65) sp16583 (joinSmall (lo:=16647) (a:=32) (b:=33) sp16647 sp16679)) (joinSmall (lo:=16712) (a:=65) (b:=65) (joinSmall (lo:=16712) (a:=32) (b:=33) sp16712 sp16744) (joinSmall (lo:=16777) (a:=32) (b:=33) sp16777 sp16809))) (joinSmall (lo:=16842) (a:=129) (b:=130) (joinSmall (lo:=16842) (a:=64) (b:=65) sp16842 (joinSmall (lo:=16906) (a:=32) (b:=33) sp16906 sp16938)) (joinSmall (lo:=16971) (a:=65) (b:=65) (joinSmall (lo:=16971) (a:=32) (b:=33) sp16971 sp17003) (joinSmall (lo:=17036) (a:=32) (b:=33) sp17036 sp17068)))) (joinSmall (lo:=17101) (a:=259) (b:=259) (joinSmall (lo:=17101) (a:=129) (b:=130) (joinSmall (lo:=17101) (a:=64) (b:=65) sp17101 (joinSmall (lo:=17165) (a:=32) (b:=33) sp17165 sp17197)) (joinSmall (lo:=17230) (a:=65) (b:=65) (joinSmall (lo:=17230) (a:=32) (b:=33) sp17230 sp17262) (joinSmall (lo:=17295) (a:=32) (b:=33) sp17295 sp17327))) (joinSmall (lo:=17360) (a:=129) (b:=130) (joinSmall (lo:=17360) (a:=64) (b:=65) sp17360 (joinSmall (lo:=17424) (a:=32) (b:=33) sp17424 sp17456)) (joinSmall (lo:=17489) (a:=65) (b:=65) (joinSmall (lo:=17489) (a:=32) (b:=33) sp17489 sp17521) (joinSmall (lo:=17554) (a:=32) (b:=33) sp17554 sp17586))))) (joinSmall (lo:=17619) (a:=518) (b:=519) (joinSmall (lo:=17619) (a:=259) (b:=259) (joinSmall (lo:=17619) (a:=129) (b:=130) (joinSmall (lo:=17619) (a:=64) (b:=65) sp17619 (joinSmall (lo:=17683) (a:=32) (b:=33) sp17683 sp17715)) (joinSmall (lo:=17748) (a:=65) (b:=65) (joinSmall (lo:=17748) (a:=32) (b:=33) sp17748 sp17780) (joinSmall (lo:=17813) (a:=32) (b:=33) sp17813 sp17845))) (joinSmall (lo:=17878) (a:=129) (b:=130) (joinSmall (lo:=17878) (a:=64) (b:=65) sp17878 (joinSmall (lo:=17942) (a:=32) (b:=33) sp17942 sp17974)) (joinSmall (lo:=18007) (a:=65) (b:=65) (joinSmall (lo:=18007) (a:=32) (b:=33) sp18007 sp18039) (joinSmall (lo:=18072) (a:=32) (b:=33) sp18072 sp18104)))) (joinSmall (lo:=18137) (a:=259) (b:=260) (joinSmall (lo:=18137) (a:=129) (b:=130) (joinSmall (lo:=18137) (a:=64) (b:=65) sp18137 (joinSmall (lo:=18201) (a:=32) (b:=33) sp18201 sp18233)) (joinSmall (lo:=18266) (a:=65) (b:=65) (joinSmall (lo:=18266) (a:=32) (b:=33) sp18266 sp18298) (joinSmall (lo:=18331) (a:=32) (b:=33) sp18331 sp18363))) (joinSmall (lo:=18396) (a:=130) (b:=130) (joinSmall (lo:=18396) (a:=65) (b:=65) (joinSmall (lo:=18396) (a:=32) (b:=33) sp18396 sp18428) (joinSmall (lo:=18461) (a:=32) (b:=33) sp18461 sp18493)) (joinSmall (lo:=18526) (a:=65) (b:=65) (joinSmall (lo:=18526) (a:=32) (b:=33) sp18526 sp18558) (joinSmall (lo:=18591) (a:=32) (b:=33) sp18591 sp18623)))))) (joinSmall (lo:=18656) (a:=1036) (b:=1037) (joinSmall (lo:=18656) (a:=518) (b:=518) (joinSmall (lo:=18656) (a:=259) (b:=259) (joinSmall (lo:=18656) (a:=129) (b:=130) (joinSmall (lo:=18656) (a:=64) (b:=65) sp18656 (joinSmall (lo:=18720) (a:=32) (b:=33) sp18720 sp18752)) (joinSmall (lo:=18785) (a:=65) (b:=65) (joinSmall (lo:=18785) (a:=32) (b:=33) sp18785 sp18817) (joinSmall (lo:=18850) (a:=32) (b:=33) sp18850 sp18882))) (joinSmall (lo:=18915) (a:=129) (b:=130) (joinSmall (lo:=18915) (a:=64) (b:=65) sp18915 (joinSmall (lo:=18979) (a:=32) (b:=33) sp18979 sp19011)) (joinSmall (lo:=19044) (a:=65) (b:=65) (joinSmall (lo:=19044) (a:=32) (b:=33) sp19044 sp19076) (joinSmall (lo:=19109) (a:=32) (b:=33) sp19109 sp19141)))) (joinSmall (lo:=19174) (a:=259) (b:=259) (joinSmall (lo:=19174) (a:=129) (b:=130) (joinSmall (lo:=19174) (a:=64) (b:=65) sp19174 (joinSmall (lo:=19238) (a:=32) (b:=33) sp19238 sp19270)) (joinSmall (lo:=19303) (a:=65) (b:=65) (joinSmall (lo:=19303) (a:=32) (b:=33) sp19303 sp19335) (joinSmall (lo:=19368) (a:=32) (b:=33) sp19368 sp19400))) (joinSmall (lo:=19433) (a:=129) (b:=130) (joinSmall (lo:=19433) (a:=64) (b:=65) sp19433 (joinSmall (lo:=19497) (a:=32) (b:=33) sp19497 sp19529)) (joinSmall (lo:=19562) (a:=65) (b:=65) (joinSmall (lo:=19562) (a:=32) (b:=33) sp19562 sp19594) (joinSmall (lo:=19627) (a:=32) (b:=33) sp19627 sp19659))))) (joinSmall (lo:=19692) (a:=518) (b:=519) (joinSmall (lo:=19692) (a:=259) (b:=259) (joinSmall (lo:=19692) (a:=129) (b:=130) (joinSmall (lo:=19692) (a:=64) (b:=65) sp19692 (joinSmall (lo:=19756) (a:=32) (b:=33) sp19756 sp19788)) (joinSmall (lo:=19821) (a:=65) (b:=65) (joinSmall (lo:=19821) (a:=32) (b:=33) sp19821 sp19853) (joinSmall (lo:=19886) (a:=32) (b:=33) sp19886 sp19918))) (joinSmall (lo:=19951) (a:=129) (b:=130) (joinSmall (lo:=19951) (a:=64) (b:=65) sp19951 (joinSmall (lo:=20015) (a:=32) (b:=33) sp20015 sp20047)) (joinSmall (lo:=20080) (a:=65) (b:=65) (joinSmall (lo:=20080) (a:=32) (b:=33) sp20080 sp20112) (joinSmall (lo:=20145) (a:=32) (b:=33) sp20145 sp20177)))) (joinSmall (lo:=20210) (a:=259) (b:=260) (joinSmall (lo:=20210) (a:=129) (b:=130) (joinSmall (lo:=20210) (a:=64) (b:=65) sp20210 (joinSmall (lo:=20274) (a:=32) (b:=33) sp20274 sp20306)) (joinSmall (lo:=20339) (a:=65) (b:=65) (joinSmall (lo:=20339) (a:=32) (b:=33) sp20339 sp20371) (joinSmall (lo:=20404) (a:=32) (b:=33) sp20404 sp20436))) (joinSmall (lo:=20469) (a:=130) (b:=130) (joinSmall (lo:=20469) (a:=65) (b:=65) (joinSmall (lo:=20469) (a:=32) (b:=33) sp20469 sp20501) (joinSmall (lo:=20534) (a:=32) (b:=33) sp20534 sp20566)) (joinSmall (lo:=20599) (a:=65) (b:=65) (joinSmall (lo:=20599) (a:=32) (b:=33) sp20599 sp20631) (joinSmall (lo:=20664) (a:=32) (b:=33) sp20664 sp20696))))))) (joinSmall (lo:=20729) (a:=2073) (b:=2073) (joinSmall (lo:=20729) (a:=1036) (b:=1037) (joinSmall (lo:=20729) (a:=518) (b:=518) (joinSmall (lo:=20729) (a:=259) (b:=259) (joinSmall (lo:=20729) (a:=129) (b:=130) (joinSmall (lo:=20729) (a:=64) (b:=65) sp20729 (joinSmall (lo:=20793) (a:=32) (b:=33) sp20793 sp20825)) (joinSmall (lo:=20858) (a:=65) (b:=65) (joinSmall (lo:=20858) (a:=32) (b:=33) sp20858 sp20890) (joinSmall (lo:=20923) (a:=32) (b:=33) sp20923 sp20955))) (joinSmall (lo:=20988) (a:=129) (b:=130) (joinSmall (lo:=20988) (a:=64) (b:=65) sp20988 (joinSmall (lo:=21052) (a:=32) (b:=33) sp21052 sp21084)) (joinSmall (lo:=21117) (a:=65) (b:=65) (joinSmall (lo:=21117) (a:=32) (b:=33) sp21117 sp21149) (joinSmall (lo:=21182) (a:=32) (b:=33) sp21182 sp21214)))) (joinSmall (lo:=21247) (a:=259) (b:=259) (joinSmall (lo:=21247) (a:=129) (b:=130) (joinSmall (lo:=21247) (a:=64) (b:=65) sp21247 (joinSmall (lo:=21311) (a:=32) (b:=33) sp21311 sp21343)) (joinSmall (lo:=21376) (a:=65) (b:=65) (joinSmall (lo:=21376) (a:=32) (b:=33) sp21376 sp21408) (joinSmall (lo:=21441) (a:=32) (b:=33) sp21441 sp21473))) (joinSmall (lo:=21506) (a:=129) (b:=130) (joinSmall (lo:=21506) (a:=64) (b:=65) sp21506 (joinSmall (lo:=21570) (a:=32) (b:=33) sp21570 sp21602)) (joinSmall (lo:=21635) (a:=65) (b:=65) (joinSmall (lo:=21635) (a:=32) (b:=33) sp21635 sp21667) (joinSmall (lo:=21700) (a:=32) (b:=33) sp21700 sp21732))))) (joinSmall (lo:=21765) (a:=518) (b:=519) (joinSmall (lo:=21765) (a:=259) (b:=259) (joinSmall (lo:=21765) (a:=129) (b:=130) (joinSmall (lo:=21765) (a:=64) (b:=65) sp21765 (joinSmall (lo:=21829) (a:=32) (b:=33) sp21829 sp21861)) (joinSmall (lo:=21894) (a:=65) (b:=65) (joinSmall (lo:=21894) (a:=32) (b:=33) sp21894 sp21926) (joinSmall (lo:=21959) (a:=32) (b:=33) sp21959 sp21991))) (joinSmall (lo:=22024) (a:=129) (b:=130) (joinSmall (lo:=22024) (a:=64) (b:=65) sp22024 (joinSmall (lo:=22088) (a:=32) (b:=33) sp22088 sp22120)) (joinSmall (lo:=22153) (a:=65) (b:=65) (joinSmall (lo:=22153) (a:=32) (b:=33) sp22153 sp22185) (joinSmall (lo:=22218) (a:=32) (b:=33) sp22218 sp22250)))) (joinSmall (lo:=22283) (a:=259) (b:=260) (joinSmall (lo:=22283) (a:=129) (b:=130) (joinSmall (lo:=22283) (a:=64) (b:=65) sp22283 (joinSmall (lo:=22347) (a:=32) (b:=33) sp22347 sp22379)) (joinSmall (lo:=22412) (a:=65) (b:=65) (joinSmall (lo:=22412) (a:=32) (b:=33) sp22412 sp22444) (joinSmall (lo:=22477) (a:=32) (b:=33) sp22477 sp22509))) (joinSmall (lo:=22542) (a:=130) (b:=130) (joinSmall (lo:=22542) (a:=65) (b:=65) (joinSmall (lo:=22542) (a:=32) (b:=33) sp22542 sp22574) (joinSmall (lo:=22607) (a:=32) (b:=33) sp22607 sp22639)) (joinSmall (lo:=22672) (a:=65) (b:=65) (joinSmall (lo:=22672) (a:=32) (b:=33) sp22672 sp22704) (joinSmall (lo:=22737) (a:=32) (b:=33) sp22737 sp22769)))))) (joinSmall (lo:=22802) (a:=1036) (b:=1037) (joinSmall (lo:=22802) (a:=518) (b:=518) (joinSmall (lo:=22802) (a:=259) (b:=259) (joinSmall (lo:=22802) (a:=129) (b:=130) (joinSmall (lo:=22802) (a:=64) (b:=65) sp22802 (joinSmall (lo:=22866) (a:=32) (b:=33) sp22866 sp22898)) (joinSmall (lo:=22931) (a:=65) (b:=65) (joinSmall (lo:=22931) (a:=32) (b:=33) sp22931 sp22963) (joinSmall (lo:=22996) (a:=32) (b:=33) sp22996 sp23028))) (joinSmall (lo:=23061) (a:=129) (b:=130) (joinSmall (lo:=23061) (a:=64) (b:=65) sp23061 (joinSmall (lo:=23125) (a:=32) (b:=33) sp23125 sp23157)) (joinSmall (lo:=23190) (a:=65) (b:=65) (joinSmall (lo:=23190) (a:=32) (b:=33) sp23190 sp23222) (joinSmall (lo:=23255) (a:=32) (b:=33) sp23255 sp23287)))) (joinSmall (lo:=23320) (a:=259) (b:=259) (joinSmall (lo:=23320) (a:=129) (b:=130) (joinSmall (lo:=23320) (a:=64) (b:=65) sp23320 (joinSmall (lo:=23384) (a:=32) (b:=33) sp23384 sp23416)) (joinSmall (lo:=23449) (a:=65) (b:=65) (joinSmall (lo:=23449) (a:=32) (b:=33) sp23449 sp23481) (joinSmall (lo:=23514) (a:=32) (b:=33) sp23514 sp23546))) (joinSmall (lo:=23579) (a:=129) (b:=130) (joinSmall (lo:=23579) (a:=64) (b:=65) sp23579 (joinSmall (lo:=23643) (a:=32) (b:=33) sp23643 sp23675)) (joinSmall (lo:=23708) (a:=65) (b:=65) (joinSmall (lo:=23708) (a:=32) (b:=33) sp23708 sp23740) (joinSmall (lo:=23773) (a:=32) (b:=33) sp23773 sp23805))))) (joinSmall (lo:=23838) (a:=518) (b:=519) (joinSmall (lo:=23838) (a:=259) (b:=259) (joinSmall (lo:=23838) (a:=129) (b:=130) (joinSmall (lo:=23838) (a:=64) (b:=65) sp23838 (joinSmall (lo:=23902) (a:=32) (b:=33) sp23902 sp23934)) (joinSmall (lo:=23967) (a:=65) (b:=65) (joinSmall (lo:=23967) (a:=32) (b:=33) sp23967 sp23999) (joinSmall (lo:=24032) (a:=32) (b:=33) sp24032 sp24064))) (joinSmall (lo:=24097) (a:=129) (b:=130) (joinSmall (lo:=24097) (a:=64) (b:=65) sp24097 (joinSmall (lo:=24161) (a:=32) (b:=33) sp24161 sp24193)) (joinSmall (lo:=24226) (a:=65) (b:=65) (joinSmall (lo:=24226) (a:=32) (b:=33) sp24226 sp24258) (joinSmall (lo:=24291) (a:=32) (b:=33) sp24291 sp24323)))) (joinSmall (lo:=24356) (a:=259) (b:=260) (joinSmall (lo:=24356) (a:=129) (b:=130) (joinSmall (lo:=24356) (a:=64) (b:=65) sp24356 (joinSmall (lo:=24420) (a:=32) (b:=33) sp24420 sp24452)) (joinSmall (lo:=24485) (a:=65) (b:=65) (joinSmall (lo:=24485) (a:=32) (b:=33) sp24485 sp24517) (joinSmall (lo:=24550) (a:=32) (b:=33) sp24550 sp24582))) (joinSmall (lo:=24615) (a:=130) (b:=130) (joinSmall (lo:=24615) (a:=65) (b:=65) (joinSmall (lo:=24615) (a:=32) (b:=33) sp24615 sp24647) (joinSmall (lo:=24680) (a:=32) (b:=33) sp24680 sp24712)) (joinSmall (lo:=24745) (a:=65) (b:=65) (joinSmall (lo:=24745) (a:=32) (b:=33) sp24745 sp24777) (joinSmall (lo:=24810) (a:=32) (b:=33) sp24810 sp24842)))))))) (joinSmall (lo:=24875) (a:=4146) (b:=4146) (joinSmall (lo:=24875) (a:=2073) (b:=2073) (joinSmall (lo:=24875) (a:=1036) (b:=1037) (joinSmall (lo:=24875) (a:=518) (b:=518) (joinSmall (lo:=24875) (a:=259) (b:=259) (joinSmall (lo:=24875) (a:=129) (b:=130) (joinSmall (lo:=24875) (a:=64) (b:=65) sp24875 (joinSmall (lo:=24939) (a:=32) (b:=33) sp24939 sp24971)) (joinSmall (lo:=25004) (a:=65) (b:=65) (joinSmall (lo:=25004) (a:=32) (b:=33) sp25004 sp25036) (joinSmall (lo:=25069) (a:=32) (b:=33) sp25069 sp25101))) (joinSmall (lo:=25134) (a:=129) (b:=130) (joinSmall (lo:=25134) (a:=64) (b:=65) sp25134 (joinSmall (lo:=25198) (a:=32) (b:=33) sp25198 sp25230)) (joinSmall (lo:=25263) (a:=65) (b:=65) (joinSmall (lo:=25263) (a:=32) (b:=33) sp25263 sp25295) (joinSmall (lo:=25328) (a:=32) (b:=33) sp25328 sp25360)))) (joinSmall (lo:=25393) (a:=259) (b:=259) (joinSmall (lo:=25393) (a:=129) (b:=130) (joinSmall (lo:=25393) (a:=64) (b:=65) sp25393 (joinSmall (lo:=25457) (a:=32) (b:=33) sp25457 sp25489)) (joinSmall (lo:=25522) (a:=65) (b:=65) (joinSmall (lo:=25522) (a:=32) (b:=33) sp25522 sp25554) (joinSmall (lo:=25587) (a:=32) (b:=33) sp25587 sp25619))) (joinSmall (lo:=25652) (a:=129) (b:=130) (joinSmall (lo:=25652) (a:=64) (b:=65) sp25652 (joinSmall (lo:=25716) (a:=32) (b:=33) sp25716 sp25748)) (joinSmall (lo:=25781) (a:=65) (b:=65) (joinSmall (lo:=25781) (a:=32) (b:=33) sp25781 sp25813) (joinSmall (lo:=25846) (a:=32) (b:=33) sp25846 sp25878))))) (joinSmall (lo:=25911) (a:=518) (b:=519) (joinSmall (lo:=25911) (a:=259) (b:=259) (joinSmall (lo:=25911) (a:=129) (b:=130) (joinSmall (lo:=25911) (a:=64) (b:=65) sp25911 (joinSmall (lo:=25975) (a:=32) (b:=33) sp25975 sp26007)) (joinSmall (lo:=26040) (a:=65) (b:=65) (joinSmall (lo:=26040) (a:=32) (b:=33) sp26040 sp26072) (joinSmall (lo:=26105) (a:=32) (b:=33) sp26105 sp26137))) (joinSmall (lo:=26170) (a:=129) (b:=130) (joinSmall (lo:=26170) (a:=64) (b:=65) sp26170 (joinSmall (lo:=26234) (a:=32) (b:=33) sp26234 sp26266)) (joinSmall (lo:=26299) (a:=65) (b:=65) (joinSmall (lo:=26299) (a:=32) (b:=33) sp26299 sp26331) (joinSmall (lo:=26364) (a:=32) (b:=33) sp26364 sp26396)))) (joinSmall (lo:=26429) (a:=259) (b:=260) (joinSmall (lo:=26429) (a:=129) (b:=130) (joinSmall (lo:=26429) (a:=64) (b:=65) sp26429 (joinSmall (lo:=26493) (a:=32) (b:=33) sp26493 sp26525)) (joinSmall (lo:=26558) (a:=65) (b:=65) (joinSmall (lo:=26558) (a:=32) (b:=33) sp26558 sp26590) (joinSmall (lo:=26623) (a:=32) (b:=33) sp26623 sp26655))) (joinSmall (lo:=26688) (a:=130) (b:=130) (joinSmall (lo:=26688) (a:=65) (b:=65) (joinSmall (lo:=26688) (a:=32) (b:=33) sp26688 sp26720) (joinSmall (lo:=26753) (a:=32) (b:=33) sp26753 sp26785)) (joinSmall (lo:=26818) (a:=65) (b:=65) (joinSmall (lo:=26818) (a:=32) (b:=33) sp26818 sp26850) (joinSmall (lo:=26883) (a:=32) (b:=33) sp26883 sp26915)))))) (joinSmall (lo:=26948) (a:=1036) (b:=1037) (joinSmall (lo:=26948) (a:=518) (b:=518) (joinSmall (lo:=26948) (a:=259) (b:=259) (joinSmall (lo:=26948) (a:=129) (b:=130) (joinSmall (lo:=26948) (a:=64) (b:=65) sp26948 (joinSmall (lo:=27012) (a:=32) (b:=33) sp27012 sp27044)) (joinSmall (lo:=27077) (a:=65) (b:=65) (joinSmall (lo:=27077) (a:=32) (b:=33) sp27077 sp27109) (joinSmall (lo:=27142) (a:=32) (b:=33) sp27142 sp27174))) (joinSmall (lo:=27207) (a:=129) (b:=130) (joinSmall (lo:=27207) (a:=64) (b:=65) sp27207 (joinSmall (lo:=27271) (a:=32) (b:=33) sp27271 sp27303)) (joinSmall (lo:=27336) (a:=65) (b:=65) (joinSmall (lo:=27336) (a:=32) (b:=33) sp27336 sp27368) (joinSmall (lo:=27401) (a:=32) (b:=33) sp27401 sp27433)))) (joinSmall (lo:=27466) (a:=259) (b:=259) (joinSmall (lo:=27466) (a:=129) (b:=130) (joinSmall (lo:=27466) (a:=64) (b:=65) sp27466 (joinSmall (lo:=27530) (a:=32) (b:=33) sp27530 sp27562)) (joinSmall (lo:=27595) (a:=65) (b:=65) (joinSmall (lo:=27595) (a:=32) (b:=33) sp27595 sp27627) (joinSmall (lo:=27660) (a:=32) (b:=33) sp27660 sp27692))) (joinSmall (lo:=27725) (a:=129) (b:=130) (joinSmall (lo:=27725) (a:=64) (b:=65) sp27725 (joinSmall (lo:=27789) (a:=32) (b:=33) sp27789 sp27821)) (joinSmall (lo:=27854) (a:=65) (b:=65) (joinSmall (lo:=27854) (a:=32) (b:=33) sp27854 sp27886) (joinSmall (lo:=27919) (a:=32) (b:=33) sp27919 sp27951))))) (joinSmall (lo:=27984) (a:=518) (b:=519) (joinSmall (lo:=27984) (a:=259) (b:=259) (joinSmall (lo:=27984) (a:=129) (b:=130) (joinSmall (lo:=27984) (a:=64) (b:=65) sp27984 (joinSmall (lo:=28048) (a:=32) (b:=33) sp28048 sp28080)) (joinSmall (lo:=28113) (a:=65) (b:=65) (joinSmall (lo:=28113) (a:=32) (b:=33) sp28113 sp28145) (joinSmall (lo:=28178) (a:=32) (b:=33) sp28178 sp28210))) (joinSmall (lo:=28243) (a:=129) (b:=130) (joinSmall (lo:=28243) (a:=64) (b:=65) sp28243 (joinSmall (lo:=28307) (a:=32) (b:=33) sp28307 sp28339)) (joinSmall (lo:=28372) (a:=65) (b:=65) (joinSmall (lo:=28372) (a:=32) (b:=33) sp28372 sp28404) (joinSmall (lo:=28437) (a:=32) (b:=33) sp28437 sp28469)))) (joinSmall (lo:=28502) (a:=259) (b:=260) (joinSmall (lo:=28502) (a:=129) (b:=130) (joinSmall (lo:=28502) (a:=64) (b:=65) sp28502 (joinSmall (lo:=28566) (a:=32) (b:=33) sp28566 sp28598)) (joinSmall (lo:=28631) (a:=65) (b:=65) (joinSmall (lo:=28631) (a:=32) (b:=33) sp28631 sp28663) (joinSmall (lo:=28696) (a:=32) (b:=33) sp28696 sp28728))) (joinSmall (lo:=28761) (a:=130) (b:=130) (joinSmall (lo:=28761) (a:=65) (b:=65) (joinSmall (lo:=28761) (a:=32) (b:=33) sp28761 sp28793) (joinSmall (lo:=28826) (a:=32) (b:=33) sp28826 sp28858)) (joinSmall (lo:=28891) (a:=65) (b:=65) (joinSmall (lo:=28891) (a:=32) (b:=33) sp28891 sp28923) (joinSmall (lo:=28956) (a:=32) (b:=33) sp28956 sp28988))))))) (joinSmall (lo:=29021) (a:=2073) (b:=2073) (joinSmall (lo:=29021) (a:=1036) (b:=1037) (joinSmall (lo:=29021) (a:=518) (b:=518) (joinSmall (lo:=29021) (a:=259) (b:=259) (joinSmall (lo:=29021) (a:=129) (b:=130) (joinSmall (lo:=29021) (a:=64) (b:=65) sp29021 (joinSmall (lo:=29085) (a:=32) (b:=33) sp29085 sp29117)) (joinSmall (lo:=29150) (a:=65) (b:=65) (joinSmall (lo:=29150) (a:=32) (b:=33) sp29150 sp29182) (joinSmall (lo:=29215) (a:=32) (b:=33) sp29215 sp29247))) (joinSmall (lo:=29280) (a:=129) (b:=130) (joinSmall (lo:=29280) (a:=64) (b:=65) sp29280 (joinSmall (lo:=29344) (a:=32) (b:=33) sp29344 sp29376)) (joinSmall (lo:=29409) (a:=65) (b:=65) (joinSmall (lo:=29409) (a:=32) (b:=33) sp29409 sp29441) (joinSmall (lo:=29474) (a:=32) (b:=33) sp29474 sp29506)))) (joinSmall (lo:=29539) (a:=259) (b:=259) (joinSmall (lo:=29539) (a:=129) (b:=130) (joinSmall (lo:=29539) (a:=64) (b:=65) sp29539 (joinSmall (lo:=29603) (a:=32) (b:=33) sp29603 sp29635)) (joinSmall (lo:=29668) (a:=65) (b:=65) (joinSmall (lo:=29668) (a:=32) (b:=33) sp29668 sp29700) (joinSmall (lo:=29733) (a:=32) (b:=33) sp29733 sp29765))) (joinSmall (lo:=29798) (a:=129) (b:=130) (joinSmall (lo:=29798) (a:=64) (b:=65) sp29798 (joinSmall (lo:=29862) (a:=32) (b:=33) sp29862 sp29894)) (joinSmall (lo:=29927) (a:=65) (b:=65) (joinSmall (lo:=29927) (a:=32) (b:=33) sp29927 sp29959) (joinSmall (lo:=29992) (a:=32) (b:=33) sp29992 sp30024))))) (joinSmall (lo:=30057) (a:=518) (b:=519) (joinSmall (lo:=30057) (a:=259) (b:=259) (joinSmall (lo:=30057) (a:=129) (b:=130) (joinSmall (lo:=30057) (a:=64) (b:=65) sp30057 (joinSmall (lo:=30121) (a:=32) (b:=33) sp30121 sp30153)) (joinSmall (lo:=30186) (a:=65) (b:=65) (joinSmall (lo:=30186) (a:=32) (b:=33) sp30186 sp30218) (joinSmall (lo:=30251) (a:=32) (b:=33) sp30251 sp30283))) (joinSmall (lo:=30316) (a:=129) (b:=130) (joinSmall (lo:=30316) (a:=64) (b:=65) sp30316 (joinSmall (lo:=30380) (a:=32) (b:=33) sp30380 sp30412)) (joinSmall (lo:=30445) (a:=65) (b:=65) (joinSmall (lo:=30445) (a:=32) (b:=33) sp30445 sp30477) (joinSmall (lo:=30510) (a:=32) (b:=33) sp30510 sp30542)))) (joinSmall (lo:=30575) (a:=259) (b:=260) (joinSmall (lo:=30575) (a:=129) (b:=130) (joinSmall (lo:=30575) (a:=64) (b:=65) sp30575 (joinSmall (lo:=30639) (a:=32) (b:=33) sp30639 sp30671)) (joinSmall (lo:=30704) (a:=65) (b:=65) (joinSmall (lo:=30704) (a:=32) (b:=33) sp30704 sp30736) (joinSmall (lo:=30769) (a:=32) (b:=33) sp30769 sp30801))) (joinSmall (lo:=30834) (a:=130) (b:=130) (joinSmall (lo:=30834) (a:=65) (b:=65) (joinSmall (lo:=30834) (a:=32) (b:=33) sp30834 sp30866) (joinSmall (lo:=30899) (a:=32) (b:=33) sp30899 sp30931)) (joinSmall (lo:=30964) (a:=65) (b:=65) (joinSmall (lo:=30964) (a:=32) (b:=33) sp30964 sp30996) (joinSmall (lo:=31029) (a:=32) (b:=33) sp31029 sp31061)))))) (joinSmall (lo:=31094) (a:=1036) (b:=1037) (joinSmall (lo:=31094) (a:=518) (b:=518) (joinSmall (lo:=31094) (a:=259) (b:=259) (joinSmall (lo:=31094) (a:=129) (b:=130) (joinSmall (lo:=31094) (a:=64) (b:=65) sp31094 (joinSmall (lo:=31158) (a:=32) (b:=33) sp31158 sp31190)) (joinSmall (lo:=31223) (a:=65) (b:=65) (joinSmall (lo:=31223) (a:=32) (b:=33) sp31223 sp31255) (joinSmall (lo:=31288) (a:=32) (b:=33) sp31288 sp31320))) (joinSmall (lo:=31353) (a:=129) (b:=130) (joinSmall (lo:=31353) (a:=64) (b:=65) sp31353 (joinSmall (lo:=31417) (a:=32) (b:=33) sp31417 sp31449)) (joinSmall (lo:=31482) (a:=65) (b:=65) (joinSmall (lo:=31482) (a:=32) (b:=33) sp31482 sp31514) (joinSmall (lo:=31547) (a:=32) (b:=33) sp31547 sp31579)))) (joinSmall (lo:=31612) (a:=259) (b:=259) (joinSmall (lo:=31612) (a:=129) (b:=130) (joinSmall (lo:=31612) (a:=64) (b:=65) sp31612 (joinSmall (lo:=31676) (a:=32) (b:=33) sp31676 sp31708)) (joinSmall (lo:=31741) (a:=65) (b:=65) (joinSmall (lo:=31741) (a:=32) (b:=33) sp31741 sp31773) (joinSmall (lo:=31806) (a:=32) (b:=33) sp31806 sp31838))) (joinSmall (lo:=31871) (a:=129) (b:=130) (joinSmall (lo:=31871) (a:=64) (b:=65) sp31871 (joinSmall (lo:=31935) (a:=32) (b:=33) sp31935 sp31967)) (joinSmall (lo:=32000) (a:=65) (b:=65) (joinSmall (lo:=32000) (a:=32) (b:=33) sp32000 sp32032) (joinSmall (lo:=32065) (a:=32) (b:=33) sp32065 sp32097))))) (joinSmall (lo:=32130) (a:=518) (b:=519) (joinSmall (lo:=32130) (a:=259) (b:=259) (joinSmall (lo:=32130) (a:=129) (b:=130) (joinSmall (lo:=32130) (a:=64) (b:=65) sp32130 (joinSmall (lo:=32194) (a:=32) (b:=33) sp32194 sp32226)) (joinSmall (lo:=32259) (a:=65) (b:=65) (joinSmall (lo:=32259) (a:=32) (b:=33) sp32259 sp32291) (joinSmall (lo:=32324) (a:=32) (b:=33) sp32324 sp32356))) (joinSmall (lo:=32389) (a:=129) (b:=130) (joinSmall (lo:=32389) (a:=64) (b:=65) sp32389 (joinSmall (lo:=32453) (a:=32) (b:=33) sp32453 sp32485)) (joinSmall (lo:=32518) (a:=65) (b:=65) (joinSmall (lo:=32518) (a:=32) (b:=33) sp32518 sp32550) (joinSmall (lo:=32583) (a:=32) (b:=33) sp32583 sp32615)))) (joinSmall (lo:=32648) (a:=259) (b:=260) (joinSmall (lo:=32648) (a:=129) (b:=130) (joinSmall (lo:=32648) (a:=64) (b:=65) sp32648 (joinSmall (lo:=32712) (a:=32) (b:=33) sp32712 sp32744)) (joinSmall (lo:=32777) (a:=65) (b:=65) (joinSmall (lo:=32777) (a:=32) (b:=33) sp32777 sp32809) (joinSmall (lo:=32842) (a:=32) (b:=33) sp32842 sp32874))) (joinSmall (lo:=32907) (a:=130) (b:=130) (joinSmall (lo:=32907) (a:=65) (b:=65) (joinSmall (lo:=32907) (a:=32) (b:=33) sp32907 sp32939) (joinSmall (lo:=32972) (a:=32) (b:=33) sp32972 sp33004)) (joinSmall (lo:=33037) (a:=65) (b:=65) (joinSmall (lo:=33037) (a:=32) (b:=33) sp33037 sp33069) (joinSmall (lo:=33102) (a:=32) (b:=33) sp33102 sp33134))))))))))
  have good : (List.range 33167).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 1100000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 33166 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 33166 := by
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


private def packet (i : ℕ) : ℕ := (if i < 280 then (if i < 140 then (if i < 70 then (if i < 35 then (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else 0))) else (if i < 12 then (if i < 10 then (if i < 9 then 0 else 0) else (if i < 11 then 0 else 0)) else (if i < 14 then (if i < 13 then 0 else 0) else (if i < 15 then 0 else (if i < 16 then 0 else 0))))) else (if i < 26 then (if i < 21 then (if i < 19 then (if i < 18 then 0 else 0) else (if i < 20 then 0 else 0)) else (if i < 23 then (if i < 22 then 0 else 0) else (if i < 24 then 0 else (if i < 25 then 0 else 0)))) else (if i < 30 then (if i < 28 then (if i < 27 then 0 else 0) else (if i < 29 then 0 else 0)) else (if i < 32 then (if i < 31 then 0 else 0) else (if i < 33 then 0 else (if i < 34 then 0 else 0)))))) else (if i < 52 then (if i < 43 then (if i < 39 then (if i < 37 then (if i < 36 then 0 else 0) else (if i < 38 then 0 else 0)) else (if i < 41 then (if i < 40 then 0 else 0) else (if i < 42 then 0 else 0))) else (if i < 47 then (if i < 45 then (if i < 44 then 0 else 0) else (if i < 46 then 0 else 0)) else (if i < 49 then (if i < 48 then 0 else 0) else (if i < 50 then 0 else (if i < 51 then 0 else 0))))) else (if i < 61 then (if i < 56 then (if i < 54 then (if i < 53 then 0 else 0) else (if i < 55 then 0 else 0)) else (if i < 58 then (if i < 57 then 0 else 0) else (if i < 59 then 0 else (if i < 60 then 0 else 0)))) else (if i < 65 then (if i < 63 then (if i < 62 then 0 else 0) else (if i < 64 then 0 else 0)) else (if i < 67 then (if i < 66 then 0 else 0) else (if i < 68 then 0 else (if i < 69 then 0 else 0))))))) else (if i < 105 then (if i < 87 then (if i < 78 then (if i < 74 then (if i < 72 then (if i < 71 then 0 else 0) else (if i < 73 then 0 else 0)) else (if i < 76 then (if i < 75 then 0 else 0) else (if i < 77 then 0 else 0))) else (if i < 82 then (if i < 80 then (if i < 79 then 0 else 0) else (if i < 81 then 0 else 0)) else (if i < 84 then (if i < 83 then 0 else 0) else (if i < 85 then 0 else (if i < 86 then 0 else 0))))) else (if i < 96 then (if i < 91 then (if i < 89 then (if i < 88 then 0 else 0) else (if i < 90 then 0 else 0)) else (if i < 93 then (if i < 92 then 0 else 0) else (if i < 94 then 0 else (if i < 95 then 0 else 0)))) else (if i < 100 then (if i < 98 then (if i < 97 then 0 else 0) else (if i < 99 then 0 else 0)) else (if i < 102 then (if i < 101 then 0 else 0) else (if i < 103 then 0 else (if i < 104 then 0 else 0)))))) else (if i < 122 then (if i < 113 then (if i < 109 then (if i < 107 then (if i < 106 then 0 else 0) else (if i < 108 then 0 else 0)) else (if i < 111 then (if i < 110 then 0 else 0) else (if i < 112 then 0 else 0))) else (if i < 117 then (if i < 115 then (if i < 114 then 0 else 0) else (if i < 116 then 0 else 0)) else (if i < 119 then (if i < 118 then 0 else 0) else (if i < 120 then 0 else (if i < 121 then 0 else 0))))) else (if i < 131 then (if i < 126 then (if i < 124 then (if i < 123 then 0 else 0) else (if i < 125 then 0 else 0)) else (if i < 128 then (if i < 127 then 0 else 0) else (if i < 129 then 0 else (if i < 130 then 0 else 0)))) else (if i < 135 then (if i < 133 then (if i < 132 then 0 else 0) else (if i < 134 then 0 else 0)) else (if i < 137 then (if i < 136 then 0 else 0) else (if i < 138 then 0 else (if i < 139 then 0 else 0)))))))) else (if i < 210 then (if i < 175 then (if i < 157 then (if i < 148 then (if i < 144 then (if i < 142 then (if i < 141 then 0 else 0) else (if i < 143 then 0 else 0)) else (if i < 146 then (if i < 145 then 0 else 0) else (if i < 147 then 0 else 0))) else (if i < 152 then (if i < 150 then (if i < 149 then 0 else 0) else (if i < 151 then 0 else 0)) else (if i < 154 then (if i < 153 then 0 else 0) else (if i < 155 then 0 else (if i < 156 then 0 else 0))))) else (if i < 166 then (if i < 161 then (if i < 159 then (if i < 158 then 0 else 0) else (if i < 160 then 0 else 0)) else (if i < 163 then (if i < 162 then 0 else 0) else (if i < 164 then 0 else (if i < 165 then 0 else 0)))) else (if i < 170 then (if i < 168 then (if i < 167 then 0 else 0) else (if i < 169 then 0 else 0)) else (if i < 172 then (if i < 171 then 0 else 0) else (if i < 173 then 0 else (if i < 174 then 0 else 0)))))) else (if i < 192 then (if i < 183 then (if i < 179 then (if i < 177 then (if i < 176 then 0 else 0) else (if i < 178 then 0 else 0)) else (if i < 181 then (if i < 180 then 0 else 0) else (if i < 182 then 0 else 0))) else (if i < 187 then (if i < 185 then (if i < 184 then 0 else 0) else (if i < 186 then 0 else 0)) else (if i < 189 then (if i < 188 then 0 else 0) else (if i < 190 then 0 else (if i < 191 then 0 else 0))))) else (if i < 201 then (if i < 196 then (if i < 194 then (if i < 193 then 0 else 0) else (if i < 195 then 0 else 0)) else (if i < 198 then (if i < 197 then 0 else 0) else (if i < 199 then 0 else (if i < 200 then 0 else 0)))) else (if i < 205 then (if i < 203 then (if i < 202 then 0 else 0) else (if i < 204 then 0 else 0)) else (if i < 207 then (if i < 206 then 0 else 0) else (if i < 208 then 0 else (if i < 209 then 0 else 0))))))) else (if i < 245 then (if i < 227 then (if i < 218 then (if i < 214 then (if i < 212 then (if i < 211 then 0 else 0) else (if i < 213 then 0 else 0)) else (if i < 216 then (if i < 215 then 0 else 0) else (if i < 217 then 0 else 0))) else (if i < 222 then (if i < 220 then (if i < 219 then 0 else 0) else (if i < 221 then 0 else 0)) else (if i < 224 then (if i < 223 then 0 else 0) else (if i < 225 then 0 else (if i < 226 then 0 else 0))))) else (if i < 236 then (if i < 231 then (if i < 229 then (if i < 228 then 0 else 0) else (if i < 230 then 0 else 0)) else (if i < 233 then (if i < 232 then 0 else 0) else (if i < 234 then 0 else (if i < 235 then 0 else 0)))) else (if i < 240 then (if i < 238 then (if i < 237 then 0 else 0) else (if i < 239 then 0 else 0)) else (if i < 242 then (if i < 241 then 0 else 0) else (if i < 243 then 0 else (if i < 244 then 0 else 0)))))) else (if i < 262 then (if i < 253 then (if i < 249 then (if i < 247 then (if i < 246 then 0 else 0) else (if i < 248 then 0 else 0)) else (if i < 251 then (if i < 250 then 0 else 0) else (if i < 252 then 0 else 0))) else (if i < 257 then (if i < 255 then (if i < 254 then 0 else 0) else (if i < 256 then 0 else 0)) else (if i < 259 then (if i < 258 then 0 else 0) else (if i < 260 then 0 else (if i < 261 then 0 else 0))))) else (if i < 271 then (if i < 266 then (if i < 264 then (if i < 263 then 0 else 0) else (if i < 265 then 0 else 0)) else (if i < 268 then (if i < 267 then 0 else 0) else (if i < 269 then 0 else (if i < 270 then 0 else 0)))) else (if i < 275 then (if i < 273 then (if i < 272 then 0 else 0) else (if i < 274 then 0 else 0)) else (if i < 277 then (if i < 276 then 0 else 0) else (if i < 278 then 0 else (if i < 279 then 0 else 0))))))))) else (if i < 420 then (if i < 350 then (if i < 315 then (if i < 297 then (if i < 288 then (if i < 284 then (if i < 282 then (if i < 281 then 0 else 0) else (if i < 283 then 0 else 0)) else (if i < 286 then (if i < 285 then 0 else 0) else (if i < 287 then 0 else 0))) else (if i < 292 then (if i < 290 then (if i < 289 then 0 else 0) else (if i < 291 then 0 else 0)) else (if i < 294 then (if i < 293 then 0 else 0) else (if i < 295 then 0 else (if i < 296 then 0 else 0))))) else (if i < 306 then (if i < 301 then (if i < 299 then (if i < 298 then 0 else 0) else (if i < 300 then 0 else 0)) else (if i < 303 then (if i < 302 then 0 else 0) else (if i < 304 then 0 else (if i < 305 then 0 else 0)))) else (if i < 310 then (if i < 308 then (if i < 307 then 0 else 0) else (if i < 309 then 0 else 0)) else (if i < 312 then (if i < 311 then 0 else 0) else (if i < 313 then 0 else (if i < 314 then 0 else 0)))))) else (if i < 332 then (if i < 323 then (if i < 319 then (if i < 317 then (if i < 316 then 0 else 0) else (if i < 318 then 0 else 0)) else (if i < 321 then (if i < 320 then 0 else 0) else (if i < 322 then 0 else 0))) else (if i < 327 then (if i < 325 then (if i < 324 then 0 else 0) else (if i < 326 then 0 else 0)) else (if i < 329 then (if i < 328 then 0 else 0) else (if i < 330 then 0 else (if i < 331 then 0 else 0))))) else (if i < 341 then (if i < 336 then (if i < 334 then (if i < 333 then 0 else 0) else (if i < 335 then 0 else 0)) else (if i < 338 then (if i < 337 then 0 else 0) else (if i < 339 then 0 else (if i < 340 then 0 else 0)))) else (if i < 345 then (if i < 343 then (if i < 342 then 0 else 0) else (if i < 344 then 0 else 0)) else (if i < 347 then (if i < 346 then 0 else 0) else (if i < 348 then 0 else (if i < 349 then 0 else 0))))))) else (if i < 385 then (if i < 367 then (if i < 358 then (if i < 354 then (if i < 352 then (if i < 351 then 0 else 0) else (if i < 353 then 0 else 0)) else (if i < 356 then (if i < 355 then 0 else 0) else (if i < 357 then 0 else 0))) else (if i < 362 then (if i < 360 then (if i < 359 then 0 else 0) else (if i < 361 then 0 else 0)) else (if i < 364 then (if i < 363 then 0 else 0) else (if i < 365 then 0 else (if i < 366 then 0 else 0))))) else (if i < 376 then (if i < 371 then (if i < 369 then (if i < 368 then 0 else 0) else (if i < 370 then 0 else 0)) else (if i < 373 then (if i < 372 then 0 else 0) else (if i < 374 then 0 else (if i < 375 then 0 else 0)))) else (if i < 380 then (if i < 378 then (if i < 377 then 0 else 0) else (if i < 379 then 0 else 0)) else (if i < 382 then (if i < 381 then 0 else 0) else (if i < 383 then 0 else (if i < 384 then 0 else 0)))))) else (if i < 402 then (if i < 393 then (if i < 389 then (if i < 387 then (if i < 386 then 0 else 0) else (if i < 388 then 0 else 0)) else (if i < 391 then (if i < 390 then 0 else 0) else (if i < 392 then 0 else 0))) else (if i < 397 then (if i < 395 then (if i < 394 then 0 else 0) else (if i < 396 then 0 else 0)) else (if i < 399 then (if i < 398 then 0 else 0) else (if i < 400 then 0 else (if i < 401 then 0 else 0))))) else (if i < 411 then (if i < 406 then (if i < 404 then (if i < 403 then 0 else 0) else (if i < 405 then 0 else 0)) else (if i < 408 then (if i < 407 then 0 else 0) else (if i < 409 then 0 else (if i < 410 then 0 else 0)))) else (if i < 415 then (if i < 413 then (if i < 412 then 0 else 0) else (if i < 414 then 0 else 0)) else (if i < 417 then (if i < 416 then 0 else 0) else (if i < 418 then 0 else (if i < 419 then 0 else 0)))))))) else (if i < 490 then (if i < 455 then (if i < 437 then (if i < 428 then (if i < 424 then (if i < 422 then (if i < 421 then 0 else 0) else (if i < 423 then 0 else 0)) else (if i < 426 then (if i < 425 then 0 else 0) else (if i < 427 then 0 else 0))) else (if i < 432 then (if i < 430 then (if i < 429 then 0 else 0) else (if i < 431 then 0 else 0)) else (if i < 434 then (if i < 433 then 0 else 0) else (if i < 435 then 0 else (if i < 436 then 0 else 0))))) else (if i < 446 then (if i < 441 then (if i < 439 then (if i < 438 then 0 else 0) else (if i < 440 then 0 else 0)) else (if i < 443 then (if i < 442 then 0 else 0) else (if i < 444 then 0 else (if i < 445 then 0 else 0)))) else (if i < 450 then (if i < 448 then (if i < 447 then 0 else 0) else (if i < 449 then 0 else 0)) else (if i < 452 then (if i < 451 then 0 else 0) else (if i < 453 then 0 else (if i < 454 then 0 else 0)))))) else (if i < 472 then (if i < 463 then (if i < 459 then (if i < 457 then (if i < 456 then 0 else 0) else (if i < 458 then 0 else 0)) else (if i < 461 then (if i < 460 then 0 else 0) else (if i < 462 then 0 else 0))) else (if i < 467 then (if i < 465 then (if i < 464 then 0 else 0) else (if i < 466 then 0 else 0)) else (if i < 469 then (if i < 468 then 0 else 0) else (if i < 470 then 0 else (if i < 471 then 0 else 0))))) else (if i < 481 then (if i < 476 then (if i < 474 then (if i < 473 then 0 else 0) else (if i < 475 then 0 else 0)) else (if i < 478 then (if i < 477 then 0 else 0) else (if i < 479 then 0 else (if i < 480 then 0 else 0)))) else (if i < 485 then (if i < 483 then (if i < 482 then 0 else 0) else (if i < 484 then 0 else 0)) else (if i < 487 then (if i < 486 then 0 else 0) else (if i < 488 then 0 else (if i < 489 then 0 else 0))))))) else (if i < 525 then (if i < 507 then (if i < 498 then (if i < 494 then (if i < 492 then (if i < 491 then 0 else 0) else (if i < 493 then 0 else 0)) else (if i < 496 then (if i < 495 then 0 else 0) else (if i < 497 then 0 else 0))) else (if i < 502 then (if i < 500 then (if i < 499 then 0 else 0) else (if i < 501 then 0 else 0)) else (if i < 504 then (if i < 503 then 0 else 0) else (if i < 505 then 0 else (if i < 506 then 0 else 0))))) else (if i < 516 then (if i < 511 then (if i < 509 then (if i < 508 then 0 else 0) else (if i < 510 then 0 else 0)) else (if i < 513 then (if i < 512 then 0 else 0) else (if i < 514 then 0 else (if i < 515 then 0 else 0)))) else (if i < 520 then (if i < 518 then (if i < 517 then 0 else 0) else (if i < 519 then 0 else 0)) else (if i < 522 then (if i < 521 then 0 else 0) else (if i < 523 then 0 else (if i < 524 then 0 else 0)))))) else (if i < 542 then (if i < 533 then (if i < 529 then (if i < 527 then (if i < 526 then 0 else 0) else (if i < 528 then 0 else 0)) else (if i < 531 then (if i < 530 then 0 else 0) else (if i < 532 then 0 else 0))) else (if i < 537 then (if i < 535 then (if i < 534 then 0 else 0) else (if i < 536 then 0 else 0)) else (if i < 539 then (if i < 538 then 0 else 0) else (if i < 540 then 0 else (if i < 541 then 0 else 0))))) else (if i < 551 then (if i < 546 then (if i < 544 then (if i < 543 then 0 else 0) else (if i < 545 then 0 else 0)) else (if i < 548 then (if i < 547 then 0x33f4e022b814549784611f98e106602d413f88a439a17509003080bc000033f48572a713bc9224401f00e146602d013e889839017108d82f40ae000033f42922b3143096a4561fa8e7866a2df143089c3a416c08c82b80ac000033f3cbf2b8948897a46a2088eb46ac2f714d88bc3a817a08d02e00c4000033f37022b394049444441f40e286402c1133881436815007c02a80ac000033f31402b6142095a4491fc8e5c67e2e814008b03a817008802cc0c4000033f2b832b4142094a44f1fe0e686782e414a08c43b417a08b82c00ac000033f25d22a413cc9244381f10e306622d513e08943a416d08682c00be000033f20042b093f09424461fd8e9c6902ee14708d039e17708982b40b6000033f1a352bb94a099646a2058ebc69c2f814d88f83b417e08902f80be000033f148f2a393b09224441ee8de86442c513a088437c15908502ac09c000033f0ee12ab140493c4441f60e246522db13c088838c16408202b00b2000033f09082b9947096c4571fc8e6c6802d913d889438616f08d02e80be000033f03412b3942c9604541f98e7468e2ee144089c39217208802d00b6000033efd9a2a693cc9344401f08e1465e2d4134882836816008582b80ac000033ef7d92b513f894e4511f88e4868c2df141889038c16a07e82b80b8000033ef1fc2c2146497c4622078ed069a2f714e08e039416808702dc0be000033eec4b2a793e093e44a1f98e506762df140088839016308282d00b2000033ee6942ae14209684561f90e486622dd14108ac3a617a08f02ec0d2000033ee0ee2a713d892a4381f10e146582cc136084037816408402c40b8000033edb1e2b9144495c44f1fd0e8468a2ea14988e83ca18509083340c8000033ed5562b4142495044e1fa8e6468c2e314388c43a616f08982f00c4000033ecfaa2ac13c49384451f10dec6482d7137886038a16308282900a4000033ec9e82b4142c95a4461fc0e706642ce13c083436815007e82980b6000033ec4162bb94549624581fc8ea06962ef14908cc39a17108982ec0c0000033ebe302c494c49b047c20f0ef06b42fc15589383d618209103180c2000033eb86d2b914449624592008eac6a42fe15109003b417708e02c00ca000033eb2c02ac93f092a43b1f18e0c64c2cd13a886035e15c083029809c000033eace02c514c49904652048e806922f614c88c83b017a08d03040c4000033ea7102bc947498845f1fc0e7c68a2d413a886c38c16a08882d80be000033ea1582ac93c89344431f78e446482cb137885037a15f08602cc0c0000033e9bbd2a413b492e4391f00e1c6522d5137084436e15907d82ac0a2000033e960a2aa140094a44b1fd0e6c6882df143887c376164082029c09c000033e90472b193fc95e44b1f50e4866a2da13f086437016008582d00ac000033e8a742bd144c9644561ff0e7c6882dd140888839617108b829c0aa000033e84d22a393a08fc4211e58db062a2ba131882c37215c08182c40a4000033e7ed92c814989a047020c0efc6ba2fd15489343e418f09803140c0000033e78f72c414b498a4672068ebc6b02f214b89343d218408e02ec0ba000033e73372b1943896245d1fb0e486782d914408cc3a217408c83080d2000033e6d792b7142c94c4531fc0e646722e814608a839a16d08802e80b2000033e67872c894c49ac4792110ee06d230a15689303da18109202fc0c2000033e61972c294cc9c44882108f206dc30d14d88c43b818108902d40ae000033e5bdc2a913e893c4461f40e3c65e2cc137887838c16f08a83000c6000033e562b2af13f094c4441f68e506642d8140887438c17008b03040c2000033e50652b0140896a4561fe8e7c6782e714988e43b017408e02f00be000033e4a8d2bd145c96845e1ff8e9868e2f214c09003c017908c83100d4000033e449a2ca94a49784622060eac6882e414408a839c17708702a00ae000033e3eda2a9140c94a43c1f50e4066e2cc13d086036815207e02b40b4000033e39262b094149424491fa0e606722df142088438016a08782d80b6000033e33702ac93f093e43e1f68e746582d713e087c38616408302d80c0000033e2db92ab13e09384411ef0e2c6642cc137086c36816908602c80b8000033e280d2ae140c9504501fa0e5c67c2ea14688d03ac18408d02f80ca000033e22392be948097a4692058e806942ed14a88c83a016508682e80c4000033e1c892a7938091e4371ef0de86542d4140088c38a16c08782ec0b2000033e16cf2ae13fc94a44c1f70e2c65e2d313b088038817008c02dc0b0000033e10f62c1948098e4652060eb869e2f714a88e03b618209103100c2000033e0b262b6144897245e1fe8ea46922fa14c08c83a416c08982c00b0000033e05562b4943c96e4591fd8e746802ec14308bc3c417e08e82f40b4000033dffaa2a8942096a4602018e846842e714888d83b217208982f00a4000033dfa092a093989124341e78dcc6362c5133884838016908702d80b6000033df4572a313ac9264371ef0e3c65a2d3133882836415f08002c00ac000033dee6d2c6948497a4581fa8e686782e413e08883a016c08902e00a8000033de8b92b0144895e4521fd0e9868a2e113f88783a016e08b82e40c2000033de3102a613d493443c1ef8e146482cd139085837416c08702f40ba000 else 0x340bed32af141094a4441f18e186482cd137885436215407c02c00a80000340b9002ba145496c4581fd8e7068a2ef14c08f439416408282bc09e0000340b3562ab13f09344451ee0e186562d5142889839e17b09103380c40000340ad812bb947c97c45a2028e9c68a2eb14a08b839c16b08902cc0b60000340a7a32bf94789824521f80e2c6582d2138886438216a08482b80b40000340a1cb2b8945c9704531ff0e8068a2e01450894386166093033c0d000003409beb2bf14989a246f20d8f086ca30415509103c418009203280cc000034096302b2141c9504441f78e5467e2e114008983ae18509283040be000034090762b1943896045b1fc0e846982f414f08c03b017e08e02ec0c800003408acc2a613bc92242c1e98de46522cc13d086437c16608582e80b20000340850a2ad93f092c44a1f40e346742dd14508a839016e08482c80bc00003407f502ad93fc95644b1f58e2866e2df13e887c37a16808482cc0a6000034079992b2144097e46b2058eb469c2e914488cc3a417e08d02fc0c8000034073e02b314189404451fd0e6868a2e914a08cc39617808e82f40ca00003406e0c2b794609804632098ed06a22ed14608b03ae17a08a02e80b8000034068712a093709044221df8d906282b712b881c37615e07b027809c000034062b22b0144496445b1fe0e9469c2eb14708b43ae17308e82f00b800003405d122ab13d092443a1f08e246402c3136084837016608502d40be000034057272c514a498a4682040ec46ac2f614e08c43ba17f09402ec0b4000034051652b7942894844e1f48e2c65c2ca13a087039416708882d009a00003404bac2ae13d091c4391f30e246702d513d085837e16107d82880b00000340461029d137490a43a1f20e2065a2ce139085c37015c08882d40a80000340401c2ca94dc9ac47f20d0f0c6ca30615109303e2190094830c0ba00003403a492be945098246e2038ea46aa2f314a88d838816308302fc0c2000034034a62a713a893443f1ef8e206742de14688bc39e16f08f02f40ca00003402eed2af141c95444f2000e4066a2e314288bc38c16e08502dc0c2000034028fd2cd14cc9ac47520e8ed46c62f714d08d83bc18b09402f80cc0000340232f2ba948899446e2020e886782d913d889438416408a02e40ba00003401d472c514b099c47620d8f5c6e030a15c09343bc18b09083280c8000034017962a813ec93c4481f98e6066a2e0140889838616908582c009e000034011d92b2941095a4571fe8ea46882e314788cc3aa17f08f02e40be00003400c162b314209504461f20e206602da14108c039816d08502a80a6000034006732a393949204401f50e2467e2e0142886037c15f08582c80b60000340009a2bb148c9724571fb8e5065a2d9140087837015d08802e00bc000033ffaa62ca94b499247f20e8ef06cc30915209043ca17b09083000b8000033ff50d2a193a491e4421f30e1c6382d413c08ac39816408702d40c8000033fef4f2b8947098c4712048ec06a62eb14788ac3aa17e08d82ec0b2000033fe9852b4142c9764592048e706822db13e08d43a817208a02e00bc000033fe3d02a993e09244411ee8df463a2be134881836214e07f02bc0a4000033fde0a2b6141c9524582008e806a62f514b88cc3b017608882e00b8000033fd8502b093ec9384381f48e146562d013b888037c16d08b82d00c0000033fd2882b2941895e4541fc0e6c66c2d013a887839217009182f80b8000033fccbe2b1143c9744642010e6864a2c4138084436c15b08682cc0b4000033fc6ee2bf946899447720f0ef46ca30114e08fc3d218809703480da000033fc1222c114849864732098ec869c2f614788d03b017f09203340cc000033fbb662b1944497c4642048edc6c4300156893c3da19409a83640c4000033fb5922b6144c96a4662010eac68a2e714588b43a817508a82c80b0000033fafb82bf146498e4652068e7c6922ed14708f03b017808e82f80be000033fa9ed2b594409644541f48e186562d714388a439a16b08c82e80c2000033fa46629113408ea4211e78dc862e2b8134083035614f081029c0a2000033f9e902bf148c97c4641fd8e7868c2e814308bc3ba176092830c0bc000033f98d92b1142895a44d1f40e3c6662ce135882837215b07c8280098000033f93192ad13fc93e44f1fc8e4c6802e214408b43a616b08882e40b2000033f8d512b3142495044c1fc0e4865c2c8138086837e161085829c0a2000033f879d2aa13bc9344311ed8e3065a2d5138884c36a16508782e40c4000033f81be2bc941894a4451f88e5c67a2e7146089437c16908182d40b2000033f7c1b29d937c9144381f40e2864c2d3140088037a16d08882dc0ba000033f767c2a513d093843e1ec8df06382c6133884c38016908e02ec0ba000033f70a12bc944898a4632000ea46862dc13e087038216808902e40b4000033f6abf2bc94609704571fc0e746662d213a886c37e15d08802d80ac000033f64ff2b694689724561fd0e906a02ea14b08dc3a817908702d40c6000033f5f2d2bb94989924712080ee86aa301155891c3d018508e03000b4000033f59a929d13c092a43a1f10e3465e2d213e08903a016808382c4090000033f53c92bc947497e4722020ea069e2ee14788b03a417409383240c8000) else (if i < 549 then 0x3422fd42a013a091442e1ec0df064a2c713c889839a17808c03080b4000034229f02c0147897a4672090eac6982f515108ec3c218308e83040ac0000342242b2b5944895e4552010e786742e013e888c37a16408982bc0aa00003421e9d29b93789004251e08d9860a2b312c881836415408102c00ac000034218b62c1149c9804621fd0e606762e314408b439416c08482b00a2000034212d12c894949924652098ec86922f614308a43a017408d82dc0c000003420d112b2942095e44b1f50e2066a2d513f888839016d08b02d40a80000342077c2a213b092a42c1e90dc86302b8132882036e15e08182ac0a8000034201d62aa13d89344501fb8e7868c2e2141889439c17408982d80b60000341fc102b594449624551f80e786902ee14608a83a217709003040be0000341f65a2b1145098c4661ff8ec46a62ee14508cc3b417f08e83000c00000341f0742c194789844662070ec46a02ea141088c39616608b02c80b80000341ea882c795089b84802138f246de30a15989203da19109803280cc0000341e4b12c0147498e46a2070e9869c2f214b88c839617a09102f00b80000341ded82bc943c9644602068e986862e614688e43c417b08e02dc0b00000341d8f72c894d89964682080ea869c2e714488cc3c218008f82dc0be0000341d3422b114249644521f78e3466c2d813a087836816308602b40ae0000341cd8f2a693c49424441f30e5866e2dc13b08a839e17808d82f40aa0000341c7bb2b4947897e45d2038ea06942e214808c03b4179091830c0c80000341c20a2ab13c49144331eb8e0463c2c813a086837c160082029c0ae0000341bc4b2b394049504591fc0e3866a2d913f88a838416008102b40ac0000341b67d2b193fc9324381e98dc86402c7136086837015407e82a00a20000341b0c02b114309544572038e7c69e2ed14a08bc39016f08f03240be0000341ab062ac93e09384461f80e606742e514708ac3ac16f08582c80b00000341a5532ac13c492e4341e90e086402c2135082036215b08202c40ce00003419fb02a813d09364371f28e3865e2e114288bc39616c08a02b00bc000034199e62b3143094c4511fd0e646842e514788e43b817f09283200c2000034194322ad13e494e44d1f80e8068c2f314908d039216b08482a00ac00003418e892a413a490a4271e80dc86382c012d87ec33815607f02a00b2000034188bd2bc947c98a4611fd8e886942f514a88d439416908a02d00c2000034183062af93e895e4511fc8e606802e414788ec3c218609603500ea00003417d2a2c0146c9844601fe0e346602d814108a43a016b08f030c0c0000034177482c2948c97c4652058ec06b02fd14e89383d018909383100ca0000341715a2c0948898045d2038ea06a02f814908fc3aa16f08982cc0ba00003416b9a2af93fc9544541ff0e906882ea14608dc3a617508b82e00b6000034165ee2a893e491c4311ea0dd864e2cd137885437616108682b40a60000341603b2ad13ec92243e1f78e506542cc137085038216508582bc0a400003415a922a313b89224361ea8e1066c2e8141087837e16107f828009e000034154bc2ba14549744622020eb06a62fd14c08f43bc17b08e82f80c600003414ef72b9142895044d1f38e0465a2db14708b83a817f08f82f40d2000034148ee2da15689f84992170f106d431015709183c617e09303280d00000341434c2a213b49284391f00df463a2cc13a087038616608982c40be00003413d7c2b8148499446b2080ee86bc2f514e09143d218609783180d0000034137be2af941c96c4562010e6c6862e1141089c39616c08702ec0b8000034131db2c394b09ac47120b0eec6ba2f914b88c038a16908a02f80c200003412c372a813ec9304381ed0dd86422d313d889838c16908b02d00b00000341267a2b2940093e4471f80e246522d3138085839017509002f40b4000034120bc2ac13f494e4461f00df46482c9136084836a15a07d82ac0a800003411ae82bc14749644622018ea86962ed14b090c3ba17808c82d80b8000034115032c814e49ae47b20c8f0c6bc2f314808f43bc17608902e40ca00003410f462b6143495c4551f88e606982f314c88b839a17608f03000b8000034109912ab93e094c4401ef8dfc6462cf13b888437e16908502a4096000034103942c914ac9aa4682070e886802e413e08903a618709282f00b80000340fdd72ab13f49424491fa8e446622de14788d438e16c08c82bc0b00000340f84a29813308ee41b1dc0da862c2b8132082835415307b029c0b80000340f2b229d938091a4381e70dd06522d3139888838816408682c00ac0000340eccb2bf94a899846d20a0eb06a62f414b88ec3ca18309202e40b20000340e7072ba947898e4672050ec469e2ec14508dc3c417c096030c0ce0000340e15d2ac93d494043d1f38e346682d513b888039217008682d80ca0000340dbbe2a393c49204381f28e306582d3138084837016a08682cc0c40000340d5d22c694c099a4782088ecc6a02f314708cc3b817c08e02ec0c00000340d00e2b7145496e45b2058e786702e314408ac39c17208f82fc0be0000340ca3b2bc947898046d20a0ed06d0309154892c3d617a08a02e40ba0000340c4802b2141496c4642040ea869c2f214688dc3b817408d82e00ba000 else (if i < 550 then 0x343a0e52ac13fc94e44f1ff0e946a42fe15388dc3a016f08a02c00a600003439b5d29013248fa41f1e58dc86362cf13b88683a017508702e40a00000343959a2b5143896a44f1fa0e6465e2dd140889c38e17108b82bc0a800003438fb12c594a098e4682078ecc6aa2f714d08f03b817909303040c8000034389dc2be145c98246e2060eb869e2e814808b839417109183100c6000034384052b9145495844d1f80e5067a2da13d889839618009102f00c000003437e2b2bb947096c4632020eac69c2e213c085838616208282b80b00000343785c2b594409624561fb8e806762e4142088839616908a02fc0c2000034372b52a613c09384421f40e6068e2f114e09043b218209303200ca00003436cde2c0949098e46c2060ec46aa30314988e83bc17909183140d80000343672c2a793bc93c44e1fb0e4c6722e514788e03aa18008e82e40c8000034361642b714589644621fb8e3c65c2d713a88a038816d08502a00b800003435ba22ae94149504561fa8e686782e114488bc3a817a08782c80b8000034355dd2b014149444491f98e7c6962fa15109083bc17d08d82f40bc000034350362a913e09364461f90e706762d914108983a817e08f02f80c600003434a742ae93ec93c43b1ef8df464c2cc13c886036a15e08082c00b0000034344a42b7145097245c2000e8468a2f214808d439e17a08f83080ba00003433ec52c3146c97e46920a8ec86a82f014e08cc3ac17408b02e40c0000034338f52ba143095e4541fa0e6c6702dc14288a83a817308a02d00c20000343332f2b5943c96c4531fa0e546582d6139085437c16b08702b40a800003432d9d2a0136890842a1ef0e0c6542d013c887837816908902e40b00000343282828b13208c64061d80d445fa2a812687fc35216108903100b80000343225a2b914449704572008eb86b82e614088c83b617708782fc0c600003431cc9298936c8f44151e30dac6262b312e882036615b08402a00a2000034317152b2144496c4541fa8e3065c2ca134084037216708382a80a2000034311782a213a09184321eb8dac62a2bd135083c36015108002ac0aa00003430bab2ba14589724471f58e246622d314008cc3b017909103040c2000034305d22c014d898a4611fe0e806922e914b09003b016f08e03280b40000342ffff2be948c9884602038ea469a2d513e887c39216308202c40a80000342fa212c414b49884702098ee069a2f014e08e43be18309383140bc0000342f4692b294389624561fe0e4c68a2e614608a43a417408a02f40b80000342ee8d2bd14609724622068ed06b42ef14a89103c217809003240c80000342e8c12b7140094844b1f80e386702e314308d43ba18008e832c0b20000342e2de2cc94fc9be47420b0f046d230c153890c3bc17f09282f40c20000342dd2f2a993c492e43c1f00e106622d5141885c36815d07f829009e0000342d7302cf95009c248521b8f586d630314f88d03b418809182fc0ac0000342d1692ba948898446a2038e746ac2f914b88f03aa17708e83300cc0000342cbbb2aa93d89404431f48e4c6682d713c083c37816108802dc0bc0000342c5d72bc947098445a1fa0e846862f114388d839a17608702d00a80000342c0212a993c49164361f18e086462bf135883837617708a03000c60000342ba412bf94989984712090ef46a82f614a88e43b818209783100b60000342b49d2ac13e493a4401f50e446702dd13f08a039816e08602d40b40000342aecf2b194209364321eb8e086622e0142889c38e16908682b80b00000342a9042b8145497244f1f80e406662ce138082435015407b82800980000342a34d2ab93f094e4471f68e7866e2dc14688b039415d07b82c80b200003429d702c094889a046e2088ebc6ba30614f09103c617d09483180ca0000342978e2c2947498246e2038e8c68c2f814e08e43be18009402ec0b6000034291cc2b7147c97a4591f80e1864e2ce13e08903a817a09182f40b600003428c0f2b313f49364461fc0e686662cc138886038217508e02fc0c6000034286422b6145496a4652098f1c6ca30415088d83b818409002ec0bc0000342806a2c494749804632058edc6b42f114c88e03aa17408a02fc0c400003427ac12a693b492c4431f30e4c6642de14508a439c17408e82ec0b8000034274e22c814c49ae47b20f0f0c6e6306156890c3c618209483080c400003426f202ac141c95844c1fe0e806762df145089039217208782c00ac000034269382c594c49a647420b0ee869e2e814488d43d018609002fc0c80000342636b2b894489764672010e8c6ac2fb15009143ca18809483080be00003425da92b514509704632048e7868e2ee14d88ac39017308b02ec0c8000034257f02b314349724591ff8eb86a42f114a08ec3c218809182f80c8000034252322af93c893443d1f30e4c6742d713e883837215e08202d00aa00003424c672b3142895044d1f88e8468e2f014988e03ac17809283080ca000034246a12b094409664621f98e4c6682e014508d03a616408802dc0c0000034240e02af94149384491f50e206582d413f087c37a16708382a80b000003423b412a293a49184311ee8df064a2c4136885039216708a02ec0d6000034235702bd146499446d2088ee06aa2ed14888dc3b817e091031c0c0000 else 0x34513632af13f893c43d1ea8df06362c8136084036616508502d40b000003450d822c314b09a046c2050ec06842dd141089838e16908282b00ac000034507de2a593c093443f1ee8e1065a2d913e88b838c17608c02dc0bc000034501f22ce94cc9b04752070ea46962e6143888039c17208982f40b20000344fc152c894c099c4712040eb86a42f414c09283d418e09a83380d00000344f6462b914689804622030e806a230415009403d818709283040c00000344f0542c994c49a247720d8ee06c630214f08fc3cc18108d82f80bc0000344ea872b594609704571fc8e986a830615208d03ac16e08c02fc0c00000344e4be2b4141895e44e1f68e286642cd135884036216108702c40b00000344deff2b4943c96a4541f88e4068c2e314108f039617608782ec0c60000344d9512a793d09304371ed0df464a2cc135886036a16708a82cc0b20000344d3512d5153c9e048e2138f106a42fd14d89143b417308b83040d20000344cda12a693b492043b1ee8e206522d613a886c38e16d08482940a00000344c7ff2a593ac92a43e1ef0dd86402c5139087437a17208b02d40c00000344c21e2c094989b447b20b8ee86aa2fa14a08a839c16d08702c00a40000344bc8429d137c9124361ea8e0064c2bc130881c35a15507c829c0a60000344b69c2c494dc9ae4792120f346ca2fe14e88d43a817a08f03040ca0000344b0d12b1143c98a46d2090ed46ba2f214d89003bc18809003280d20000344ab022ba14409644582048ec069c2f014f88d83bc17a08902d40bc0000344a5332b4945896e45d2040eac6b22f714f88dc3be18c09283280d200003449f5f2bd948899c46b2030ea86902f014c888c38216c08982c40b6000034499c52a113ac92443a1ef8e346782e6143089c3a417208802f00b00000344942e29d938c91c4301ef0e1465e2ca13a886036c16908702d80be00003448e922a693c49344451fd8e886a02e5146089838616c08602c40b8000034488af2c114709664591fb8e4867e2e214488d83a617209002fc0c0000034482ee2b294649804602048eb46942f514a88f03b617c08f02f80be00003447d482a113b891a4371f08e2465a2d013b087037e16b08b02cc0b00000344776c2c114a09a047020c8edc6d230a15589203ca181092030c0ca000034471972bb948497444f1fb0e6c66e2d814108bc3a216e08882f40b200003446bf72a293cc92c4431f38e606622d513c887437e16508682f40ae000034466192c194bc9b046d2060e9c68e2e014408c439e17808a02e40ba0000344604d2b6148c99046c2098efc6c42f915308f839617508e02e40be00003445a6c2bb14a49a446b2078ed068e2e314788b439417108c82d80b20000344549d2ba14309704431f68e7868a2ec14708d038c17108d82d00a200003444eda2b4941494e4461f18e0c64c2d013f88bc3aa17f08b83180c2000034449082bc945c9644561f88e646862e514988d03a617008882f00c4000034443492b294149484481fa0e246602cb140889c39c17008582d009e00003443d852b5143495e4521f88e8c6922f314788c83ae17508b02e80bc000034437b42be147c9764582008e9c6a42e814608d43b017c09082e00ac000034431de2b9146c97a45f1fd8e946862e414688dc3be17508f02e40a600003442c2f2a7941094a4491f98e5067e2e2140088039817108682c00b0000034426532b9941094e44b1fb8ea06a62f514a08d03ac17708c82dc0a8000034420732ca94cc98c4612010ec06a62f414808c43b017e09683200c800003441abb2af142c95c45b2040e8067c2e914008943a017308e82e00d2000034415022ac93fc9204341ee8e086402cd138084437616008502c40b400003440f2a2c1947c98c45d1fe8ea86742e214008b438e16e08902e00b80000344098c2a213bc93843f1f10e1c6582cf137885835615e08502cc0ac000034403bb2b7940894843e1f28e246582db14708cc3ae17608b82e40b40000343fdfc2b6941897245b2030e906882ed14788c839e17308702e00a40000343f8312b4942c96044e1f68e2065c2d813d888c38417208c82e80b40000343f24c2c494a89984742070eac6b22fb14d88dc3b818108f02f00ae0000343ec8e2b1141893a4411f48e546702db14388a439617508802cc0ae0000343e6b52c6148c9924572030ea86b430415008e83ae17608c830c0d80000343e0f02b0145497445c1ff0e8867e2e214408b039817909002f40ca0000343db112c0147498a4702088eac6ac2f414908dc3aa17a08c82e00b60000343d5582ae941896245c2018eb06882ee14808b039a18209283000cc0000343cf6c2c994f09bc4772100ef46c230915188f43c4186092030c0b60000343c9992bb148899e4692028e886862ef14788c43b617108d03040c40000343c3aa2c894849804602000e8c68e2e514388c83a217508e82f40b40000343bdcb2c294d09b04722038eb06902e114208b03b4181092031c0ca0000343b8062b4940896244c1f68e4466a2d2141888c39a16d08682f40b80000343b2342b6143895c4541fd8e8467c2e114488bc3b618108d82e40ba0000343ac4b2c714b09a646a2070eac6a62ec14988fc3c818308902e00bc0000343a6932ae93f493843e1ef0e346602d413b885c38416708983000b4000)))) else (if i < 555 then (if i < 553 then (if i < 552 then 0x34684fc2bf14809884672028e886802e114408c83a817808782b40b400003467f672a193ac92c4351f00e3c65e2d7139886037416308382b00b2000034679922b9143c95a4511f50e4c6662dd13d889038416408602d00b0000034673cf2b894589824692050ef06aa30014d08f83c418408e83080c400003466e082b2942096c4511fb0e686802e114408c83ae17808f83000c8000034668682a513b493a43e1ef0e1863c2c7138081c35a15208382a40a2000034662a12b5943c97c46620a0ed86a62ec14888d43b217908e82f00c200003465cd12c394a099445a2008e706822e914608c03a016f08882d40a4000034656fe2bb146899046c1ff8ea069c2e3145887c39216b08a02e40b2000034651072cd94fc9c047f2128f106d831816309903f419609403100b600003464b312c0947496644e1f60e2c6542d5138883036e16108702bc0b2000034645572c394ac9ac4712060eb469a2f014788e83c217d08a02d00c200003463f902b394409684601f98e546742da141088038c17008d02f40b8000034639cc2af141495844e1f60e4065a2c5137083436416208d02cc09c000034634232a813e09244311e90da46222bb12e87f834814c08282c40b400003462e522bc147096c4672040ec069c2eb14708cc3b018a09783280ce000034628842b2144897045a2070e806862eb14388bc3b018108f03080d2000034622c82b2142095c4571fc0e706722e814508b83ac17908a82cc0b000003461d182a613a893844e1f40df46242c1131082c37a15208302cc0b4000034617462b5140c94444a1fa8e5c6702e214808bc3b217a09083040ca000034611812b5140c94644b1f28e3c6602d613d889438e17408582c00aa00003460bb32b5143896645a1f70e8067e2dc13e889c38016408482bc0a6000034605c42c994ec9b447920b0ef46c22fa14e88f83b817a08f02f40ba0000345ffff2b8144496645c2068eb069e2e814c08fc3be17908a02f40bc0000345fa492ac940c9624511fe8e646762e114088ac39817508b02ac0b60000345f4582ca14cc9a046e2018e946982fd14e08f43c018509483000cc0000345eead2a593a09164381e78dc06482cc13b885839016c08702b80b20000345e90a2a693dc94644e1f90e6067c2df14608f83aa16f08f02fc0b80000345e34a2b3140093a4491f70e686822d613c886c38016608202c409c0000345ddb12a613a49364471f08de863e2ce13d887037615d08382c40cc0000345d7da2bd94a49944722088eec6ba30114908f83ce17c09082fc0c40000345d2072be94b89a247d20f0f2c6d230415209183ce184096834c0ce0000345cc4c2b294189624581f60e446602d113f886439017408d82d80b80000345c67e2bd94849824672068ec06982f314988c03a0177093831c0ca0000345c0c92a813f094c4551f98e5866a2d713e088838015608182900a40000345bb0e2a693f893a4401ee0dd06302bb134882836c15e07f82940940000345b5292c994d89a646f20d0ed06aa2f214908c43ae17908c82f80ce0000345af482c0147897245d1fe0e9c6b42fa14908d43b818108f02f80c40000345a9902ad93e094244a1f48e506642da13c085c38017208b82f00bc0000345a3b42c4148097c46a2050e8467c2e114208a838616d08903000b000003459dc32c294b499446e2098ec46a82e7140886039216708902cc0c4000034597fd2bb94509704612058ebc6b22eb14408b438416c08882f80b00000345923f2af941495044a1f30df062c2b613187fc35c15908282c00a600003458c912ae941c9584501fa0e4c6662e51438898398161084029c0a0000034586b82bd947898a4591fd8e8468a2dd14308c83ac17708b82dc0c8000034581062a513f893a4421ef8e246622d313e88c43b017a08d02cc0b400003457b412b2941494644b1f80e486902f714b88b83a216d08982d80c20000345756a2bd149899447220c0ee46b82f714988f83ca17908c82f80c600003456fc22a793f493a44c1f80e4065c2d5135881836615207f82980a400003456a012b414309464471f40e546702e114588a839c17f08d82e00c80000345642d2c0944c9744632018e606782e3143089c39a17b09003180c400003455e602ba147097e4652030e986962ea144088c38a16308702e80c8000034558842bc949898245d1fc8e5066e2db14188bc39e17608d02f40c2000034552bd2b8143c95845a2010e7868c2f714a89103ce18e08e02fc0b600003454cfe2b2141093e44a1f40e4466e2de141088c3b216f08782b00b4000034547362b4142895e44c1f60e2c6642d613d888039c16a08702c00a6000034541542c694c099847720b8ed46c630a15489183be18009403240be00003453bd2291931c8f64161e18da06142ac12f07f834c14b07b02980a4000034536132ad942c95c4471f20e1463a2c7137083c37416608d02e00be000034530512b6944497045c1f98e4c66e2d5140089838c16308402b00a600003452a822b4141096844b1f68e6c6822e214708c03a817c09202e00ba000034524d62a893e49344371ef0e086462d113b082c36416408302dc0c200003451f072b8146097645d2018e8467e2df14208903aa17008d02f80d60000345191e2be149097c4662020ea069e2f414708ac3ae17808e83000c8000 else 0x347f6802be946895a4581ff8eb46a62ef14388943b217909003000be0000347f0b32b4945099446d2020e986922e2141088839016d08b82d40bc0000347eaed2b6944495c4561fb8e746722d2138887039a17508d82d00ae0000347e5192bd94689804672068e8869a2ef14a08ac38c16b07e02780ac0000347df322c314bc9ae4882148f206c230a15409203d618e09003040cc0000347d97d2ad940895444e1fd0e5c6782e014308c83ae17f08f02f80be0000347d39d2c214a49944671fe8eb06a22f015089203cc189090830c0b40000347cdc42bf149898e4692058ec06a02f415188f83a217909403180be0000347c7fd2b114349444481f80e7068a2e5143088839217308c82d40bc0000347c24f2a713a891e43c1ed8dd062e2c5133885038216e08902e80b40000347bc992ab93c492c4321ea0dd86402c4132882c36e15c08402cc0ac0000347b6cf2b114349624551fd8e546802e313e888c38217108a02c809e0000347b12e2a693c89304451fa0e406722d713e885c39016908582c00bc0000347ab6f2ae940093e4451f40e406762e214288d03a817508c02c80b40000347a5992bb145c9644581ff0ea46b02f514c08e03a017a09102fc0ba00003479fc72bc14609584481ee8e1464a2d5140086038015e08802d40ba000034799fd2b7945c97e4581ff0e8067c2dd14308a83a417108902b80bc000034794212bc14549744521fb0e7c68a2ea142887c38215f08b02d40ba00003478e372c995009c849021b0f4c6d030615188f83ba17f08e03200b8000034788ad299938c9124351e80dd864a2d113b08a839416f08a82ec0b0000034783062a413cc91e4351ef8e306742e0141089c38a16508702c80b200003477d272bf14ac98446d2070ea867e2e014408903a217108f030c0b00000347774d2b894689824561fc8e6867c2da14108a439417408f83000ca000034771802b8145c9724681fc8eac6922ef14988983a617308302d40b000003476be229f13a09184311e98e006602cf13b085037015f08302980ae000034765f62c894909a246e2090ecc69a2e914388b438a16808402a40bc000034760242b9946496c4521fa8e746702d9140886838a16708302c80b000003475a602b6144897445d2018e946922f114608c03b617b08983000b6000034754932b6946c9824671fe8e7868e2e113c08843a017208982e00b000003474ecc2b014189524511fb0e706742dc13e088438216b08482a40a4000034749062bd146097a4622018e986822e4143087438816408682c40bc0000347434c2ad13d493643f1f10e5866c2d913f88b039617a08b82f80d000003473d9b2ae93e894444f1fe8e606722e614488d03a217a08a83040cc000034737af2c394a099247c20e8f386e030515709403d418309383100ca0000347321129f938c9224381f40e846842d714608ac39617408f02cc0ac00003472c222cb14d49ac47620a0ef06d030a15309203d018f09683040c6000034726602b0943895c44e1fa8e6466e2db13c086c38c17308c82e80ba000034720892bb144897245e2018e9068a2e814808b83a617c08d02b40a000003471adb2a793d89344481f10e2c6482d314588cc3ae17908b02cc0b4000034714e42c814ac99c47720b0ecc6a42f714c08f83b216908782c40b200003470f4b297136c90a4331ec0e086482d313e085838c17108b82d00ae000034709ba29f93c89344411f48e406582cf13d888038016408782cc0b8000034703e62c1149098a47120a0ebc6962eb141089c39e16b08c02f40be0000346fe4e29d938491042c1e60ddc6402c112b882034e15207a02a00a60000346f88a2b7944896c4652070ec86ac2f314388c03a217908f02f40b60000346f2c12b994649844561fe0e6066a2d213c887037216508402e80b40000346ecd62c914bc98647320e0ee06a02f714e89203b618008f83040cc0000346e7132b694549704672070ed46a62f614a08cc3b418109383280ac0000346e1352c1949099e46b2060eb46902df14508a839017008602d40aa0000346db742b3941495e44a1ef8de464a2ce13b086c37416008882cc0b00000346d5812c914b099e4772078ec468a2e513b889838c15d08302d00a80000346cfcd2a813ac92c43e1f28e406722e014708d03b017508b02cc0ae0000346c9e42ca14b899246c20a0ee06b22f714f08e43ca18c09283180c20000346c4262b194309564511f98e846902d814208b03aa17c08f82f80aa0000346be3d2c214cc9964672058eec6d030d15709183c218108a82bc0a60000346b8962a493d091c43a1f40e7467e2d9140884036615b08402a409e0000346b2e12ab140c9404431f80e486722dd14208a439816908682f00c40000346ad292b1141c95e45b2020e9068a2e114208b83a2175092031c0be0000346a7602bc147c9844662000e886882ea14908d43a217208902bc09e0000346a1982b814309724511fd0e746762d614088903a417709002f00ca00003469be22a993c493a44b1f48e4066e2e414788b43a417e09283080b0000034696192b214109544521f68e6066a2e013c087437415e08402c40ae000034690602b414289704531ff8e746802eb14a08c039417408e82f00be00003468ad229a138490642d1e80dec6322b212887e435e15708082b409c000) else (if i < 554 then 0x349678429b137090c4291e80de46402be132081c35415507f02ac0a6000034961de2a813fc9444451f30e2c66a2dd140089839817408c03180ac00003495be32cd14f49c848e2168f1c6e030415189003bc18308f82f40c6000034956002bd148098a4632060eb86722dd13f088c38217708d02e009e0000349506d29c139c8f04211e48d886202b512e082435e15707d82980ac00003494a972bd14849884662008e9c6a22f314a08e43a417608882f40c2000034944ea2a713d09304331ee0e106442cb13d087438216308582c80b400003493f422a413d092843a1ee0e086462cb137085037616d08a03000c6000034939822b5145c9844642028edc6b42fb14d08bc3ae16e08b82d40b8000034933a02bf94c899a47320b0f046be30415188ec3ba18f09582f80c200003492dbd2c294a89a246d2060ebc6ac2e814308983a417c08b82f80ba000034927dd2be144896e4521fc0e7068a2e9140088438a16008482d40be0000349220a2b8943495a4521ff0e986982e514688d03a617308a82c00b000003491c6e29f13648f841d1e70de46382bc12c084c37016608882b40ac0000349168a2c0148c9824682070ee46ac2f014908b43a017508c82e40bc000034910c32b494609624531f98e346522ce140086838216408582c00a600003490afd2b8145896e4591ff8e986862ec14688bc39c16d089830c0ca000034905342b7947c98446e2038e746762e0141088039017208a02e80c40000348ff572bf146897e4612098ec86ac2f714d88ec3a417608c82f80d00000348f9962b494409624531fa8e7c6762ef14a08d83ca17b08e82ec0aa0000348f3d62b2141494a4461f50e5467a2e4141088837a15d07a82940a20000348ee252b394409804572010e9069a2ed14d891c3d018e09583100d20000348e8742a613f494644a1f90e5866a2e114088a839a16d08782bc0a20000348e2d02a493b891242b1ea0de46462cc139888037416208a83040dc0000348dd3b29e93989284441f60e3c6562c9139888839c16e09002e40b20000348d7942a613d89324341ee8df865c2d3139885436e15e08782d00c00000348d1df2b314389664592008e8c66a2de14588f43c818209583200ca0000348cbf52bc949899646d2070eb06a42fe151090c3d618b09203100ac0000348c6452af94049404461f88e8c6862de14388c03a217709403200cc0000348c06f2b9943c9624521fa0e7467a2e014408a438816508502c40c20000348baa62b0143494e4591fd0eb069a2e514208ac3ac17c09102ec0c20000348b4eb2ae14309544541fb8e746802e5140889839c17308982a00ae0000348af3a2ae13f092c4421fd0e806862e514688e83b417608e03080b80000348a9852a993b493c43b1f48e5c6862e414708a83b218209183200be0000348a3e42a3139890a4331ed0e2863a2cc13e886037a16308602d40ae00003489e212b9142894843c1f28e0863c2d113f88b439016d08682d80b8000034898632ad14209684631fc0e806962ed14608e83c4180094030c0b6000034892792cb94b899e46e2068ecc6ac2f814a88d83b817708e82f80d000003488ccf2ae13e093e4471f20e5c68e2de140888c3a217308a02dc0ba000034887162b2141c9584511f78e546742da13b08843a217d09183040c20000348814c2b6140c93a4431f88e646902e714d08e839e18209403140b000003487b962b794209444431f08e0863e2c9138886837616608582dc0b2000034875782dd95409f64a22268fa470c32015c893c3f619709703040ae00003486fe529f93989164411f28e146502d313b089438417608882b809800003486a282b1942c9644591fb0e6467c2dc14008b038816b08f02f40c60000348643d2c614e09b647d20b8edc6c02fb149889838817008802c00aa00003485e9e2a193a49124311e80ddc6302b712f883035e16008902ec0b0000034858d12b5142895644f1fa8e3464c2cc13c085038e16a08902ec0b00000348532e2a193b09324491f68e6067a2e413f08b43b417908682d40a800003484d7f2ad13f89404371ef8e1866c2d714308c03a217a08a82e00b6000034847b02b394609764652008e7068a2e214108a43a617708d02ec0b60000348420d2a413ac91c4331f20e346682e314608b839c17408a82c40a800003483c252c494d098c4712058eac6902e714588a438616b08882e80bc0000348364d2be147c9884682028e906882ef14788cc3aa17108702cc0a40000348308a2b7944096844a1f08e086562c9137085039016f08402ac0ac00003482ae62a6939490c42c1e38dc46322c6136886c38616a08e02f80ca0000348250b2bb945897e46a2068ed86a42f714d08e83b018209002f00c600003481f4a2b5944497645a1ff8ea067c2e714588b038215f08802d80b2000034819b429c13408e841b1e48de46402be130082435814b08382b00a4000034813c32c6148899a46b2060ed069e2fd15289003b418309483280c000003480de62c014789624521f78e5466c2e3143089c3a417908e82d40bc000034807f62c494bc9b848320d0ee46b430114f08e83ba17008802bc0ca000034802232ba946496244b1fa0e3465e2da13d886437816808a02f80c60000347fc4c2bb94689764581fe8e786822d713d886036815707d82a00ba000 else 0x34ad8592b2142897e4632050ec06942f014708a03c218509583180ca000034ad2922b6943096c4581fe0e9c6962f414608b03a417808682d40b2000034acce82aa93e093e4471fc8e6468c2f814b88ec3ca17909103140cc000034ac75a29d93a89244361ea8e0064a2cd143889839617308602d40b4000034ac17e2bc14749864772120ee86bc2fc15108d83b818209202f80c2000034abbc12b2142896a44e1f28e6c68a2e114308cc3a217708d030c0c0000034ab5d72c694dc9ba4792140f246e8315155093c3c818b09603180b8000034ab0172b1942895c44f1fb0ebc69e2f014488d83ae17709082f00ba000034aaa542b6142c9684571ff0e646742e114488a83a617008e82e00bc000034aa48d2ad13f49464451f58e1c6582de14388a439016c08282980a2000034a9ece2b394309464431f80e4465e2c2132081836416508602e40b8000034a98e22c494b498a4702078ec86a02ee14688b839816e08882d00b4000034a93212b6141c9544531fa8e586702df140088839616808882e40b4000034a8d592b314149464491f38e306702d613e089439817108a02c40ac000034a87942ad14209444521f98e386742e214688ac39816a087029009a000034a81ff2a2139890c42f1ee0e006542c813a088037c15e08202a40a8000034a7c212c0947c97a4642038ea86b02fa14c88fc3c818108f82f40b2000034a76622b413fc94e4491f40e3c6622d0139885c38016c08802cc0b8000034a70842c0148499846d2090ee06b030214f08dc3b217e09183080c0000034a6af829313248e241c1e28d986262cb137084837815e08382f00c4000034a65382b5940c95e44c1f58e3c66a2de1460898390166081028809e000034a5f6e2b4144897c45d2010e886762e014388ac3ac17308f02f40c4000034a59b62ab13d092e4351f30e3c6582c5135884c37615f08982c00aa000034a53f92aa94049384421f40e4c6602ce13a088837c16108182b00b4000034a4e292bb94549764612028e9c6962f614f890c3bc17208c82ec0ce000034a48612b4942896245a1fe8ea46922ed14788b43a617408a02f80bc000034a42b82a193a49264341ee8dfc6662d1138885038a16508402d80c4000034a3cf82b293e495443d1e88dd46382d613c887438e16408682dc0c0000034a36fc2ca14ac9a048020e8ef46e631215809103c617f08a02c80b4000034a31402ad94089584561fd0e786842df14688b83a016e08d03000ce000034a2b812b5941096a44c1f80e2864a2cc13287f434015207f029c0b4000034a25d92a293bc92643f1ea8dd86282cb135884837215a08282d40aa000034a202e2aa13d89324391e88dcc62a2b9136084836214f07c02a80a0000034a1a412c7149c9a24722098ee469a2ff14d88bc3a617008f03040be000034a14722b4943496444a1f08e1c66a2d413d886838217008802d40be000034a0ec62ab93f494244a1f38e406742e714688a83ac16c08402cc0c2000034a08dc2c9149c99a47120b0ecc6c630a15609503da19509583340d2000034a03292b0141c9664501f98e4c6682d0138886837015e08082900a00000349fd432c614c09aa47b2048ea86982e714808c83b017e08b82e80b40000349f7742bc94949b046e2078ee06b82fd15089243c618609583140da0000349f1be2b294309624531ff0e9467e2e2144088838616c08882d00bc0000349ebfc2b2945098445e2038e8c6982f114a08e83c018209282f80b20000349e6312b8144497a4692080eb46982ea142087c37e16208a030c0c20000349e05d2c3948c98e4662068ea46a02fb151890c3a017008302f40ba0000349daa22ae13f094a4351ec8e386622db13b088438616808382b80b40000349d4cb2b5144c9804591fa0e4c6662e8141888c39a16a08782d40aa0000349cf4429813788f04251e68e0c6522cb13b889839a16a08402c00ae0000349c93c2d415149c047d2108f2c6d2306153092c3f618c094032c0ca0000349c35d2c914d89b647f20d8ef86ca30915308f83ca18f09a83440ca0000349bd8f2b3145097a45f2020eb86862e314388c03a217408a02e40bc0000349b7d82ae940094c4461f38e1c64e2d313b886037e15b08202900bc0000349b21f2b014009564441fb8e4066a2d5140888c39816e08582a80bc0000349ac632b0140895e4541fb0e7c66e2e113b888837e16208982f80c60000349a6852c1949098245e1f68e246542d013e887437016408782c00c80000349a0d92ae140c9464531f80e4c6722e814688f03ca18209203040bc00003499b172b914609724652048e9468e2f114988d03ae18009703200b6000034995512b2943c97e46a2090ee86d030f15489143e019e09683240c000003498f6b2c814c49b246d2088ecc6ae30215189003d0192091830c0be000034989c32a1939490e4301ec8e0064a2cd13a886037c15e08682c00b80000349842a2a013a090a4271e68dec63e2cf139084437615f08502e40ae00003497e712ab94289644561fd0e6867e2e414488a839e17508a83040c60000349788f2c314e49b44872148f286d431115509383f619d09503200bc000034972c32bd14a498c46e2058e7c69c2ed14d08d03a017408a82e80bc00003496d162a713ac9284471f48e6467e2e714888c83a217c08f03080c6000)) else (if i < 557 then (if i < 556 then 0x34c49eb2c594c09a847f20c8f106aa2f514e89143b617608c82e00ba000034c44262b3943096845a2018e7c68a2e514588d83ac16e08802f00a8000034c3e432c514a49984722050eac6862e914788c039817408a02d80ba000034c387a2b1141c95c44b1fc0e5466e2db13d087c39016108802d00b6000034c32a62ba944c95644f1fb0e686842e4143886c39817408c02e00b8000034c2cf82ab13bc92843b1ef8e3c6602da13d087438c17408c02d40b4000034c27552a614049584471fc0e4865a2d113b087438016808e02ec0d0000034c21702c294949964651ff8e686842e614308a43ac16808d030c0ce000034c1ba82b014109424501f90e306422c9136085839217108802e80bc000034c15b92c914e89b247a20d0efc6ba2f714a88e43a617108c03000c4000034c10112a413d09284411f30e1c6602c713d889838e16908802ac0a8000034c0a602ab13b49204371ef8e086642d513d087037c16208302c00aa000034c047c2bf14709764591fb0e8468e2e5142089038c16a08582d40b4000034bfed62a693d89364461f38e4c66a2d613c088039e17008382e00b2000034bf9102b013f494444e1fb0e586702dd13f88a038e15b085829409e000034bf3322bd146097a4581fb8e806762e413e087036e16608882dc0b8000034bed6c2b2943096645b1fe0e846922ea14788bc3ac17b08b03100c0000034be7d12a5937c8f24251e00db062a2bc131881c37415d08602d00a8000034be2262a793b492843b1ef0e186482cf13e888038816d08582bc0b2000034bdc442c2949498a45b2000e846702d6139889439416b08d82e80ce000034bd6792b7942096c45a1fb8e8067e2e514508d03aa17608682f40be000034bd0cc2a693c893e43d1f10e006502d013b886037a16c08802b40aa000034bcb072b2942094e4451f48e1065e2c6134083c3761600808278098000034bc5312be946497c45f2010e606762e6142887c37216108382a40bc000034bbf852a693b091443c1ef8e306522d713f888438e16408702d00a8000034bb9f129d13789104291e40dd063e2d113b08a039617308b82f40c2000034bb4192c414ac99e4722090ed86b02f814f08ec3aa17a09183140c4000034bae4c2bc944496845c1fb0e486782d714308a039a17808f83180c0000034ba8742c294909984722090eec6ba2fc14e08c43c218509103040c2000034ba2a12c114ac9a047620b0ee869e2f214a08c839a17b09103000bc000034b9cf02aa93d89444421fb8e746822e714888f43c818d09783140c4000034b970b2c314d899c4702088ee46be30214b88e83c418708e02f40d2000034b91272c5949498c4662098ecc6982ee14b88dc3bc17708802e80b8000034b8b4e2c314ec9c646f2098ec46b22f914b08b43ac16908b82f80bc000034b859f2b094409684612018ea46862e414708f83c017708602ec0b6000034b7fa92c494d09a047420f8f186d030914b88ec3b018209103000c2000034b79eb2ac141494c4501f68e5868a2ee14788e83b617c093030c0c4000034b741e2bc94709684622050e946962eb144888039216c08f02d00c8000034b6e702a893b092e43e1f68e406682d1139885837a15c08382c00ba000034b68992b994449564562018eac6a62f714c88d03be18309083100c8000034b62f32a513dc9324401f10e086482d313d086037e16408582ec0d0000034b5d4b2a9138892c4311f28dec6462ca13a888038816708a03000cc000034b57852b193fc94c44f1fa0e8468e2eb14808943a217c08c82f40c2000034b51a22c194a09a44682020e986902dd13f08b438a16908402b40ac000034b4bd02b994709664602078ec86c22fa14b08e43a817508b02d00b8000034b46052b1942496044f1f78e506862e914288a03a617c08b83080ba000034b404d2a713b092643c1ef8e106802e614288983a4175090031c0c0000034b3a682c094a89904612050e9c6962e914888e03ae17709002fc0c2000034b34b72aa93f49424381f00e146582d313b086037c16108882c80ac000034b2edf2c1947496c4602000e686742e7140888c37215507f02980b0000034b291e2b113e494844f1f40e246582e313e88ac3a017708d02ec0c6000034b234a2b894749724602018e6c6722e114608c43b817909283340cc000034b1d772b7146c9784602018e846822f114a88dc3b818208f82ec0b2000034b17ce2ab13fc95845d1fe0e7c6622d7141086438216908702bc0b4000034b11e52c1148099646a2090eb46a82ec14b08cc3ae16508382d40c2000034b0c3d2a313b491242d1eb0e106602d3138886837a17308b82d40c0000034b06792af93d092843d1ed0e146602db13c087036e15708002bc0a6000034b00c72a8940c9504441f68e486702d913a886838416408982e80b2000034afb0a2b5143496a4612038e9067c2e814a88dc39216408882bc0b6000034af5562ae94289624531f88e306622d4140889039016808802e80b4000034aef772c2945897a4511fa8e8c6a02ee14508a439016b08902e00ba000034ae9842c494989984732070eb06902ee14b88fc3c417809403200d4000034ae3c82ad93f096445a1f90e546682d0139888438415908202d80b4000034ade182ac13d49264391ef8e0c6542c613d887c36a16108502c00ae000 else 0x34dbaf52ad142096e45a1fa8e3c6742de13e086039216307f02b00ae000034db5202bc14949904611ff8e846942f014708fc3ac17e08e83100da000034daf702a813c09224371ed0dfc6442d613f888c3a617a08d02f00c2000034da9cb2a513dc9324381eb8dd062e2c4137884837c15808602b40b0000034da4052b814549804622048eb46802ed14788c039e17b08e03200d2000034d9e3e2b714609844541fa8e5c66a2ce14488c839e17108882ec0b0000034d98522be148899a46c2038e8c69e2f414c08d03b017e08d82f80b2000034d92832b1144096845b1fe0e4066c2d4137885437215c07f82b00a2000034d8cea29e937890e42b1ea0dec6422be12f07f835615807f82ac0b8000034d870e2b9144495a44f1f90e6c65a2ca13c084836c16408302c40be000034d814c2b4943096a4541ff8e9868e2e214608ac38616708502dc0bc000034d7b982ab93e89504441f40dec6502c412f082036c16308482bc0b2000034d75ce2b7941094c44a1f90e2066a2d113b086437416207f82a009e000034d6fff2b394149424471f90e5c6742da14608b03b417b09002e40b8000034d6a262c1947099847620d0efc6c630314908d03a617b08f82e80c0000034d64402c0148c97e4662058ec46b02fe15008cc3c017a09002ec0c2000034d5e9f29e139491243a1f10e006422d0138086838e16a08302b80bc000034d58d62b294409724511fb0e946982e914708d83b017c09182f80be000034d53272b014289584481f38e2c6542d213b886837e16608582e80b8000034d4d742b4940093e44a1fa0e5c67c2de14388cc3b617b08b02e00a2000034d47d329e938c90e4351eb8e0063c2d2137087c38a16608002a40ae000034d420c2b2940c9584531f60e4466a2d513b085c38617408b02f80d2000034d3c562a513dc9404431f30e2c65a2c8137086038816608382d00b4000034d369d2b213e49304421f60e3865a2d913a889039416408102bc0b0000034d30d02bd144495e4521fc0e646882ec144888839816908d02e80c8000034d2b292ab93c893643d1ef8e1c6502d713b086037616a08902d40b8000034d256c2b213f894243f1f68e2864e2ce13808943a417708b830c0b6000034d1fb52ac14189664521f30e246642d313d086438016608982e00b4000034d19e22b4146497a4662020eb06ac2ee14908e43c017708782c80a4000034d14382a6939c91e42b1e40dc463c2c813b086839416208802c40a8000034d0e7c2b2945897446b2028e8c67e2e314888e03ca18809282fc0b0000034d08862c914c49a44732088ec86982ed14788f43cc18609282e00ba000034d02d42a793ac91e43b1f48e3865a2d014188ac39816a08802e40c4000034cfd0e2b294009304391ee0e2868c2e714588d03b017208702dc0c4000034cf7622a893e893a4491f78e206602d7137888038a16108882f40c6000034cf1b72aa940c94c4451f40e3c65c2d313d886038216308682b00b0000034cec072ab93e89344411ef8df863c2c4137884c38016e08b03140bc000034ce6462ab93dc93c4451f40e4865e2d3139889439416f08882c40ae000034ce0822b5945498a46c20b0eec6b82fa14d09083ba18009282ec0bc000034cdaf5298136c9004291ea8e1c6562d813f887839617108702c80c4000034cd5252b8145096e45b2030eb86942ee14508b439817909003000c0000034ccf6f2a493c092643c1f58e446642ca134085439417308f82f80b8000034cc9b62ab140c95e4471ef8e146682dc136883836215a082027c0a4000034cc3f42b0141495644b1f58e646842ef15088ec3b617e09302ec0c8000034cbe0d2cc14f09be4762088ec46902e4145087c38e16a08802f80b8000034cb8392bd146c98c45f1fc8e886902e814608b039416408182c80b4000034cb2842aa93f09404521fe0e946ae2f314788e03ba17f09203300c8000034cacb52b9142495c4531fe0e8467e2e514b08bc3a817908c82f40b6000034ca6f82b6146098245c2020e606762e014788a839c17d08d82d00be000034ca1242b3140c95044b1f88e546622d313f88bc3b017208f03140ca000034c9b602b7145897a4662020e9466e2e9142889c39617808c831c0d8000034c958a2c0147c98645c1fc8e7468e2fa14988fc3bc18208902c80ae000034c8f8a2d3952c9d44812100ec86b030715489183c617c095033c0c8000034c89b32c0149498a46a2090efc6ae2f214b88e03ba17b08e02f40c0000034c83e42bc948c98846e2068ecc6ac2f614788a839c18008f02f80ba000034c7e012c614c89b647420b0ef06c42fd15009143ba18809983280c6000034c78442b314049564561f70e6865a2da13b086037816e08c02b40b2000034c72772bb143495e4531fc8e7c6882f314808b43ac17d08d82d40b6000034c6cad2b814549904692070ebc6c02f914d88ec39c17208902c40c2000034c66d12bd948c99445b1fb8e8867e2e3143888838e16a08402b40b0000034c60db2cf95089b647f2120f286c02fb14b09003c218408c02e40b4000034c5afc2c4949098a45c2040eb06902e513c886837e16108382b00b0000034c556f29d13a091e43c1f30e486782db139085837816608482bc0a2000034c4fca2a513c492a43b1f58e2064c2cb13e88983a017508c02cc0be000) else (if i < 558 then 0x34f2c4b2ad93f894a44b1fd8e886822df13a088439416f08702e80b6000034f266b2be947c97a45c1f68e586822da13f089c38416208602a00a8000034f20922b6145497e4632040e906a62f714d08d83a417108a03040c4000034f1ad52b3945c97c45a1fd0e6c6722eb14688d03bc17b08982c00b8000034f15152b3941c9684581fe8e6c6702e714588c83ae17608f02f40ca000034f0f492b914409584441f68e3466c2d3139883436015807e82ac0a4000034f09692c394ac98e46d2108f446d430c15909583f019409883100ba000034f039d2bd14789744632078eac6922e714588b8392170089029c0aa000034efddf2b214389744601fd8e7468c2e714c88e83ba17208982cc0a8000034ef8172b2943095c4511f80e606662d213c08643721670830290096000034ef2522b414289584521fc8e6868e2f114508d839e17508802d80b2000034eec7c2bb945496c4572018eac6aa2f514c08f03b417308782fc0b6000034ee6a92ba144095c4571fa8e4868c2f514a893c3e619a09603400c8000034ee0d92b7945898445e2040ecc6ae2f714e08c43a017608e83180c0000034edb122b614389524502000eb86a02e614308c03b218109082f00c6000034ed5522b3142895a45d2000e7467c2dd14108a43a616b08802dc0c0000034ecf8c2b193e494444a1f40e246702dd14508a839c17408d82d409e000034ec9d82a993dc93a4421f50e3866e2d4140889838e16c08b82ec0c2000034ec42b2a993d893243b1ed0df864a2ce13e888c39016f08a82fc0c8000034ebe6e2b013ec9424351ea8db06162b2129880035a15607c827809c000034eb8b12b3142496044f1f90e346682dc13f888c39217108882e40bc000034eb3062ad93ec9464471f50e2c6782da13b086038016908582b80a2000034ead1b2c414b899a47920c8ee06aa2f414a88e43b017709203140cc000034ea7422c014749884611fe8e6067e2eb14888f83d418109582d40a4000034ea1732ba94509684571fd8e706762de13f087437a16308782ec0b0000034e9b8f2c014b49aa46a20d8eec6be2fe151092c3f219209803340cc000034e95da2ac93dc94c44b1ff8e8468a2df141889038417408b82f00b2000034e8ffd2bb949098e4632020e946842ed14b08e43b418208c02e00b4000034e8a332ba146096a45f2030e906942ee14288d03b017208a02d40ae000034e84782b0942895844a1fd0e7c6902ee14988dc3ae16e08682c00bc000034e7eb72b394209624511fb8e746902ef14908e43c018209202f40b0000034e79042ae13fc94e4501fb8e686682da142888037616908783080b0000034e732e2c0948898e46d1ff8e746782e314608bc39e16b08c02bc0c8000034e6d692ba948c97e46e20c0f086d230b15809403d018109403100ba000034e67982bb94609684612030e986902ef14a09003cc17b08b82d80d0000034e61f32a8940c95044f1f68e3065c2d3136883035e15307f02b40a0000034e5c0f2bf949c99445b2000eb86b62f314c09183ca18609403280c6000034e56472b194149504541fe0e7867a2dd140889439217308c02fc0a8000034e506c2bc146497e4561fd8e946902ed14a88c43a417308902c00c6000034e4ab02b114489644582000e846842e414588d03ac17208902dc0c4000034e44db2ba944c9744521f78e286682da14408ac3b217908f83200c8000034e3f1e2b4143c96444b1f60e446702d414008b83b017308982e80c6000034e39652b7140c9484461fb0e8c6862d813c889038416808902f00b8000034e33c12a193d49384461f10e3c65c2d213c88b03ae17308882c40b6000034e2df72b814309504551fd8e6067e2df13c087438816508882d80ac000034e283e2b0943896e45f2000e906842e714688b839c17308f03200d2000034e229f2a593ac91643b1ec8dec65a2d3139886438616808602ec0ba000034e1cc62bd948898a46f20e8ecc6ac2fb15009103c218009183100b4000034e170e2b5143c96445a1ff8e7c69a2fe15108f43ba17c08e83040c2000034e112c2c1944c95a44a1f48e5c66c2d813b886c38a16c08702b80ae000034e0b762b5144496645b1fb0e5c67a2e214088a039416908802dc09e000034e05b02b8146096445d2070ee86cc305151891c3d818008c83180c8000034dffc22c614d49ac47a2110f2c6c42ff14a88f03b217308902e80c4000034df9ff2b4143c96445b1fb0e8c6762e6143889c38616f08882e00b6000034df48529793708fe42e1ee0e246442c5139888839818109083180aa000034deed52a593dc94644c1fb8e486682d313b88783a217609103240c6000034de90a2bb14509544501fa8e5467c2e214288d439e17808e02f00b0000034de3502aa13e494844b1fa8e206502c6134083437e16408882e40b2000034dddaa2ab13cc93a43e1ef0e086502cb13b889438417308b82d40be000034dd7f92af93fc9364471f48e606662d413d886039c17008f82f40be000034dd2232bb14289564491f40e246662e3142088838a16308682ac0b2000034dcc392c8949097a46a2050ed06aa2ef14b08a439e18209603000ca000034dc65e2c194a49884632060eb869e2f214608cc3a017a08c82ec0a6000034dc0ac2b0941c9584561fc0e606762d313e887038c16908702f40c2000 else (if i < 559 then 0x3509ce12a793f494e4471f98e5867e2d9139884c37e16508482a00aa0000350973e2a693d093443e1f88e446602dd13f08a038817308e82e40c0000035091912a613dc91e4371ec0e146462cb138887c3a617308c02f40b600003508bd32b0940494a43f1f48e5066e2de13a886038a17008a82e00be00003508648297936490642a1eb8df06462c9139884c378162083029c0b8000035080a62a493a89164321e98dfc64e2c6137885437015a08782e40b200003507aa92ce14e09bc4842138ef46ce312151091c3d618b097031c0d6000035074d02c1147896e4571fb8e586762e214508943ae17208802e00c200003506eda2c895149c248220c8ed86ac2f214c08d03b218a092032c0e6000035069242ac13e89324491f60e646762da141089438616808402cc0c8000035063572b5946896e45a1f80e446802e714708a83a217708f02d80b200003505d902b594349704672020ea067a2de13c088437a16608202cc0c0000035057e72a993d895245a2030eac6a82ef14e092c3d418808f02f40c6000035052402a593d892a4361ee8e146502e013e887038216908882c00a800003504c912aa94109384341f50e0c6542c8139085439217008b83040a8000035046cb2b3942094844f1f40e486742dd13e887038616908702e40b6000035040fa2bc14589704571f98e686982e314288a839e17e09002f40aa00003503b6129f138c91842f1eb8dcc62e2be131880c37216508402c00b8000035035a42b4943c96c4551fe8e886822eb14688bc3a018009103140c200003502ffa2ad14089544541fc0e706682d613d08a03b017a08b02e00b000003502a362b5143095e44f1f98e5c67a2de14608cc3b017209102f00bc000035024682c0146496e45e2010eb869a2ed14308c83a416a08b02ac0a000003501ec529e937091a4321ea8de86422ce137886836e16108802c809e0000350190f2ae141896644f1f08e2865a2ce139087037c16508602a40b80000350132b2c494b09a047420a0f0c6c230014c08c03b417b08b02dc0b400003500d252c814b89a046e2060ec86bc2f414a08c03ca18909082f80b8000035007642b094289644571fd8e646962e614408c83a417e08e83040b2000035001872b9145495c44e1f98e5c6902fc14e08ec3c618b09783380d6000034ffbfd29793588e84201e28d886182b6133883435414e08002a0098000034ff6382b4142494444b1f90e586802dd139888035e15a07c82c80b4000034ff0462c914c49a44752088ed86a62fb14d08e03b217408b02e40a0000034fea822b414289564541ff0e986922e113e888038016308882ec0be000034fe49f2c1948897c4691ff8ea86982f214e09003c218209002e80ce000034fdec82c314b098e4662060ed06ac2fb14f09183c2180091030c0bc000034fd91b2af14009464501fd8e6c67a2d813f887838416708782d80b2000034fd3582b8145c9744582030ec86ac2f514a08e83c418509103080ac000034fcd952b1144096c4561ff0e9869c2e9141889439217108a82d00ac000034fc7f92a413788fa41f1e78e1465c2d813a088037a15e08282bc0a8000034fc2252bb14649724552000e946882ea14308ac3bc17708e03080b6000034fbc822a393b491e4461f80e246622d2140088438416608883000b8000034fb6bc2b2142c9504491f38e2465a2dd14188a838816c08802cc0b0000034fb0e82ba146096c4642008e8c69c2f014888e83ba17e08f03240c6000034fab3b2a593d892843a1ed8e086442cd136885438216b08c82e80ae000034fa5732b6940493c4411f08e1c6662e214888d439e16908a02d00b4000034f9fc92a813c89204291e88ddc6442c7136883835615207e02980a6000034f9a172aa94049584461f68e646842ee14588d83a416b08582cc0bc000034f94302c794ac99a4612088ee46cc2fa14f89243d818708f82e00a8000034f8e502be946c9744602070ec06962ea14708d439215f08102d00b8000034f88862b6944c95a44a1f18e1c65a2cf13a087c39416d08602b40aa000034f829a2c294a09944621fe8ea86922e814808e43cc18109303280c8000034f7cf22a593c492243b1ed8e046502c9131080437816d08282b40ae000034f77372b3144496c45d1ff0e6c6782dd141088c37e16908782bc0a4000034f71832ac140095844b1f28e486722d713d088037a16408582d80b4000034f6bc22b5946098c4692098ef46be2fd14f09143c818809283180c8000034f65f32b794189604531f68e786562db144889039217409183240ca000034f60382ad93e495244d1f90e8067a2e714788ec3b417808b02d00ae000034f5a632bb146896c45e2028eac6c030115489103cc19709682f40b4000034f54942b9143c97c4561fe0e846942f314788c83b818309503200d6000034f4ede2b0940494a44e1fb8e6c69c2ec14708983a217508982e80d6000034f48ef2c914b49964712098ef06ca305152891c3c818509503000d8000034f436d29d135090842c1ea8df86422c2137081836215708202b00bc000034f3daf2b1140c9504531fe8e806702db145889c39e17b08c82e40c2000034f37e22bc94509704592008e746862e214608a039a16f08882bc0ac000034f31fe2c1148c97c4621ff8e846882d913a087438816408782cc0b6000 else 0x35155cf0000000000000000000000000000000003a418509002d80b800003514ff72b8142c9564531f68e386862e214288a03b217708b02bc0c000003514a2d2b013fc9504582020e7c6902e914908bc39016b08882cc0c0000035144692b013f89404401ed8df46502cc139084037216108382d409e00003513eaa2b114309664541fe0e5866c2da14588b03a817908b82ec0ca000035138df2b614409724592018e806822e714788c439617208702f40b2000035132f62c314789804621ff8eb06aa2f114b88fc3b217208602d40c200003512d352b194289684622068ea46ae2fa14908d83ac18109202dc0ba0000351277d2b013ec93443c1ee8e386722d2140089039617309182f80be000035121b62b3143096c4531fd0e686902e7144089037a17909202ec0c200003511bff2ae13f89484521fb0e5867e2db14408a438a17008602d00c0000035116552a313849224421eb8df46582c913a887038816708502f80ca000035110552cf95089d64842118ef86cc309155890c3b817e096033c0d600003510a922b3140c95845e1fc8e746822ec14488ac3b418709402ec0be000035104bf2bd945098246f20a0ed86aa2f114a09183dc18509282f80d20000350ff1f2a513d49324391ee8e146642d914288a038016808382a809c0000350f9612ad13fc94c44f1f50e386702dd144088837616508882bc0ae0000350f3ba29f93b492042e1ed0e0c64e2d714408bc3ae17a08e03000cc0000350edfa2b4945897c45e2020ed06b830214d88f43c618709102f40be0000350e8482a693d492e43b1ee0e3c6762da13d888c38216708c82ec0b80000350e2742bf94749704571fc0e646802e214508bc3a416b08902ec0ae0000350dc972c3949898a45b2010e8c6842ea14789003b818a09502f80c00000350d6b02c794b09b047920c8ecc6be30915609183cc18008f02f40c60000350d0ed2b2141493e44c1f88e386662d714288a438c16108182bc0b40000350cb162c2149098846e20a0ef46d230f15408fc3c217f08e832c0d20000350c5682b2941094e4471f98e606722e0141889838416308382bc0a40000350bfde29513448ea4261e80df063e2ce13c088c39416d08802d00b20000350ba122bf146495444f1f88e406722d113f084c38416008602bc0b60000350b42a2c194749a447320c8ecc6ac2ee14a08dc3b017808c02c40bc0000350ae502bf947c98c46f2080e8c6882e214288a037e16808602c80aa0000350a8672c094a098c4592070ec46aa2f314808b43a017a09203240d00000350a2882bb944897a45d2038eb06a42f014b08e83ca18009202ec0b8000))))))))))

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



private theorem b559838 : covered 559838 559908 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559908 : covered 559908 559978 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559978 : covered 559978 560048 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560048 : covered 560048 560118 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560118 : covered 560118 560188 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560188 : covered 560188 560258 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560258 : covered 560258 560328 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560328 : covered 560328 560398 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560398 : covered 560398 560468 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560468 : covered 560468 560538 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560538 : covered 560538 560608 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560608 : covered 560608 560677 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560677 : covered 560677 560747 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560747 : covered 560747 560817 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560817 : covered 560817 560887 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560887 : covered 560887 560957 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b560957 : covered 560957 561027 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561027 : covered 561027 561097 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561097 : covered 561097 561167 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561167 : covered 561167 561237 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561237 : covered 561237 561307 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561307 : covered 561307 561377 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561377 : covered 561377 561447 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561447 : covered 561447 561517 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561517 : covered 561517 561587 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561587 : covered 561587 561657 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561657 : covered 561657 561727 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561727 : covered 561727 561796 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561796 : covered 561796 561866 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561866 : covered 561866 561936 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b561936 : covered 561936 562006 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562006 : covered 562006 562076 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562076 : covered 562076 562146 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562146 : covered 562146 562216 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562216 : covered 562216 562286 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562286 : covered 562286 562356 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562356 : covered 562356 562426 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562426 : covered 562426 562496 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562496 : covered 562496 562566 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562566 : covered 562566 562636 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562636 : covered 562636 562706 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562706 : covered 562706 562776 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562776 : covered 562776 562846 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562846 : covered 562846 562915 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562915 : covered 562915 562985 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b562985 : covered 562985 563055 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563055 : covered 563055 563125 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563125 : covered 563125 563195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563195 : covered 563195 563265 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563265 : covered 563265 563335 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563335 : covered 563335 563405 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563405 : covered 563405 563475 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563475 : covered 563475 563545 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563545 : covered 563545 563615 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563615 : covered 563615 563685 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563685 : covered 563685 563755 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563755 : covered 563755 563825 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563825 : covered 563825 563895 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563895 : covered 563895 563965 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b563965 : covered 563965 564034 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564034 : covered 564034 564104 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564104 : covered 564104 564174 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564174 : covered 564174 564244 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564244 : covered 564244 564314 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564314 : covered 564314 564384 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564384 : covered 564384 564454 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564454 : covered 564454 564524 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564524 : covered 564524 564594 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564594 : covered 564594 564664 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564664 : covered 564664 564734 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564734 : covered 564734 564804 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564804 : covered 564804 564874 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564874 : covered 564874 564944 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b564944 : covered 564944 565014 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565014 : covered 565014 565084 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565084 : covered 565084 565153 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565153 : covered 565153 565223 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565223 : covered 565223 565293 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565293 : covered 565293 565363 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565363 : covered 565363 565433 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565433 : covered 565433 565503 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565503 : covered 565503 565573 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565573 : covered 565573 565643 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565643 : covered 565643 565713 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565713 : covered 565713 565783 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565783 : covered 565783 565853 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565853 : covered 565853 565923 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565923 : covered 565923 565993 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565993 : covered 565993 566063 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566063 : covered 566063 566133 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566133 : covered 566133 566203 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566203 : covered 566203 566272 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566272 : covered 566272 566342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566342 : covered 566342 566412 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566412 : covered 566412 566482 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566482 : covered 566482 566552 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566552 : covered 566552 566622 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566622 : covered 566622 566692 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566692 : covered 566692 566762 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566762 : covered 566762 566832 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566832 : covered 566832 566902 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566902 : covered 566902 566972 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b566972 : covered 566972 567042 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567042 : covered 567042 567112 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567112 : covered 567112 567182 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567182 : covered 567182 567252 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567252 : covered 567252 567322 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567322 : covered 567322 567391 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567391 : covered 567391 567461 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567461 : covered 567461 567531 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567531 : covered 567531 567601 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567601 : covered 567601 567671 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567671 : covered 567671 567741 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567741 : covered 567741 567811 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567811 : covered 567811 567881 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567881 : covered 567881 567951 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b567951 : covered 567951 568021 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568021 : covered 568021 568091 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568091 : covered 568091 568161 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568161 : covered 568161 568231 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568231 : covered 568231 568301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568301 : covered 568301 568371 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568371 : covered 568371 568441 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568441 : covered 568441 568510 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568510 : covered 568510 568580 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568580 : covered 568580 568650 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568650 : covered 568650 568720 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568720 : covered 568720 568790 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568790 : covered 568790 568860 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568860 : covered 568860 568930 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b568930 : covered 568930 569000 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569000 : covered 569000 569070 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569070 : covered 569070 569140 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569140 : covered 569140 569210 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569210 : covered 569210 569280 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569280 : covered 569280 569350 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569350 : covered 569350 569420 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569420 : covered 569420 569490 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569490 : covered 569490 569560 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569560 : covered 569560 569629 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569629 : covered 569629 569699 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569699 : covered 569699 569769 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569769 : covered 569769 569839 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569839 : covered 569839 569909 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569909 : covered 569909 569979 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b569979 : covered 569979 570049 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570049 : covered 570049 570119 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570119 : covered 570119 570189 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570189 : covered 570189 570259 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570259 : covered 570259 570329 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570329 : covered 570329 570399 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570399 : covered 570399 570469 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570469 : covered 570469 570539 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570539 : covered 570539 570609 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570609 : covered 570609 570679 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570679 : covered 570679 570748 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570748 : covered 570748 570818 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570818 : covered 570818 570888 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570888 : covered 570888 570958 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b570958 : covered 570958 571028 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571028 : covered 571028 571098 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571098 : covered 571098 571168 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571168 : covered 571168 571238 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571238 : covered 571238 571308 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571308 : covered 571308 571378 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571378 : covered 571378 571448 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571448 : covered 571448 571518 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571518 : covered 571518 571588 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571588 : covered 571588 571658 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571658 : covered 571658 571728 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571728 : covered 571728 571798 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571798 : covered 571798 571867 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571867 : covered 571867 571937 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b571937 : covered 571937 572007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572007 : covered 572007 572077 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572077 : covered 572077 572147 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572147 : covered 572147 572217 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572217 : covered 572217 572287 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572287 : covered 572287 572357 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572357 : covered 572357 572427 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572427 : covered 572427 572497 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572497 : covered 572497 572567 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572567 : covered 572567 572637 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572637 : covered 572637 572707 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572707 : covered 572707 572777 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572777 : covered 572777 572847 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b572847 : covered 572847 572917 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 559838 572917 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b559838 b559908) (joinCoverage b559978 (joinCoverage b560048 b560118))) (joinCoverage (joinCoverage b560188 (joinCoverage b560258 b560328)) (joinCoverage b560398 (joinCoverage b560468 b560538)))) (joinCoverage (joinCoverage (joinCoverage b560608 (joinCoverage b560677 b560747)) (joinCoverage b560817 (joinCoverage b560887 b560957))) (joinCoverage (joinCoverage b561027 (joinCoverage b561097 b561167)) (joinCoverage b561237 (joinCoverage b561307 b561377))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b561447 b561517) (joinCoverage b561587 (joinCoverage b561657 b561727))) (joinCoverage (joinCoverage b561796 (joinCoverage b561866 b561936)) (joinCoverage b562006 (joinCoverage b562076 b562146)))) (joinCoverage (joinCoverage (joinCoverage b562216 (joinCoverage b562286 b562356)) (joinCoverage b562426 (joinCoverage b562496 b562566))) (joinCoverage (joinCoverage b562636 (joinCoverage b562706 b562776)) (joinCoverage b562846 (joinCoverage b562915 b562985)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b563055 b563125) (joinCoverage b563195 (joinCoverage b563265 b563335))) (joinCoverage (joinCoverage b563405 (joinCoverage b563475 b563545)) (joinCoverage b563615 (joinCoverage b563685 b563755)))) (joinCoverage (joinCoverage (joinCoverage b563825 (joinCoverage b563895 b563965)) (joinCoverage b564034 (joinCoverage b564104 b564174))) (joinCoverage (joinCoverage b564244 (joinCoverage b564314 b564384)) (joinCoverage b564454 (joinCoverage b564524 b564594))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b564664 (joinCoverage b564734 b564804)) (joinCoverage b564874 (joinCoverage b564944 b565014))) (joinCoverage (joinCoverage b565084 (joinCoverage b565153 b565223)) (joinCoverage b565293 (joinCoverage b565363 b565433)))) (joinCoverage (joinCoverage (joinCoverage b565503 (joinCoverage b565573 b565643)) (joinCoverage b565713 (joinCoverage b565783 b565853))) (joinCoverage (joinCoverage b565923 (joinCoverage b565993 b566063)) (joinCoverage b566133 (joinCoverage b566203 b566272))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b566342 b566412) (joinCoverage b566482 (joinCoverage b566552 b566622))) (joinCoverage (joinCoverage b566692 (joinCoverage b566762 b566832)) (joinCoverage b566902 (joinCoverage b566972 b567042)))) (joinCoverage (joinCoverage (joinCoverage b567112 (joinCoverage b567182 b567252)) (joinCoverage b567322 (joinCoverage b567391 b567461))) (joinCoverage (joinCoverage b567531 (joinCoverage b567601 b567671)) (joinCoverage b567741 (joinCoverage b567811 b567881))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b567951 (joinCoverage b568021 b568091)) (joinCoverage b568161 (joinCoverage b568231 b568301))) (joinCoverage (joinCoverage b568371 (joinCoverage b568441 b568510)) (joinCoverage b568580 (joinCoverage b568650 b568720)))) (joinCoverage (joinCoverage (joinCoverage b568790 (joinCoverage b568860 b568930)) (joinCoverage b569000 (joinCoverage b569070 b569140))) (joinCoverage (joinCoverage b569210 (joinCoverage b569280 b569350)) (joinCoverage b569420 (joinCoverage b569490 b569560)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b569629 b569699) (joinCoverage b569769 (joinCoverage b569839 b569909))) (joinCoverage (joinCoverage b569979 (joinCoverage b570049 b570119)) (joinCoverage b570189 (joinCoverage b570259 b570329)))) (joinCoverage (joinCoverage (joinCoverage b570399 (joinCoverage b570469 b570539)) (joinCoverage b570609 (joinCoverage b570679 b570748))) (joinCoverage (joinCoverage b570818 (joinCoverage b570888 b570958)) (joinCoverage b571028 (joinCoverage b571098 b571168))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b571238 (joinCoverage b571308 b571378)) (joinCoverage b571448 (joinCoverage b571518 b571588))) (joinCoverage (joinCoverage b571658 (joinCoverage b571728 b571798)) (joinCoverage b571867 (joinCoverage b571937 b572007)))) (joinCoverage (joinCoverage (joinCoverage b572077 (joinCoverage b572147 b572217)) (joinCoverage b572287 (joinCoverage b572357 b572427))) (joinCoverage (joinCoverage b572497 (joinCoverage b572567 b572637)) (joinCoverage b572707 (joinCoverage b572777 b572847))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 559838 ≤ index 1075000000/512 := by decide +kernel
private theorem starting_value : fast 1075000000=54460514 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 1075000000=54460514) (n : ℕ) (low : 1075000000≤n) (bound : n≤1100000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=1075000000
    · rw [first,anchor]
      exact starting_value
    · have past : 1075000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤1100000000 by omega)
        have within : index n / 512 < 572917 := by omega
        have lower : index 1075000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤1100000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ1075000000To1100000000
