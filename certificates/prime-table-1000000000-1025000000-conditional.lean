import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ1000000000To1025000000

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




private def radical : ℕ := 0x14600c9a8255335978c17bf268a497f4ae43b567c31e7fffd66f3067334fec7a36dd053b63efe96af7c8186bd559ed7bdf3641543573c4657c3d2ab7188ba3d0536248e7d41d55eb1709508a00c2bb3e3ac9c9aebc60caf2504fe9afad49ed2bab93b0f81f6464e60208066f00f42ad183af2f663c6f399feac2ab30fd8e80dc9d1114e6bba0ed2561bd2153ec13ab62d0e75439f277a4f0fd6cf1c6767465dff29e5d2dc020d0761ace6c066cdc14af0e6f966f032c9f095e637112e79c8f253e59a2bf9a792c02b2ca490e38e0523972da67443aeedd670c4d6bf6ff66f05d5049d5c7bb356ad21fdc2d2fc8c2cf952ef5f11ce80a51dad49dac696990fa608627770496b4cfe301fbb3db84798c897d4b6b11bc068993ddfab32b553eeba74b7e5d50524dfcf5b5fd8c22d86d9098084343b036134765504d524e0943676b951b0b6121fa716d938913edcda96799a68cf1cc0b35d603aedce439672ddc7d347cf9ab9384b779c3a9201d582fb0d543c143554550ba4acf06163b9ccf9b13aedbfd1e63ea07b53a33be68dd635c9d27b46d1378eb8a059ffd1d45f4d19e3a6f48258d350f12abed056c2199cb7ae692090a79d53bbf3dd6160aad4166476566764dca005cb593bdc5bdc2c9fa1588a4bb4cf70998d5812718312d7043be4e69d688c2f454b27240eea09604021828c9d8834391ab73f74079c256b028895ca760880fede27ca2da371277710425b56194c29fd697af9adea77ed761fdc1278593735c8e0a50bbeaaa85f16561c9102bc9ab72bd047e403e353e6388fc9a5f4f561daa6ea9925b53b104c4d542fac94a1f62842e9968cc61e9a7346a94d60bb9fd338419b559024169a7e109d1f8da5673d28d8c958de6e004e965197288d6ee1cec81ff1e9ea76d30e6a30ff4942c09698ef1879ce98774539a8c02db735535b6f7017b4da40430666fc546a5834831719ee5458ae9f43ddf8ea93f142de82ebe5116b92521f43bb145f6ffb986cb2b8017121c81c99f9f5b6618cce196adf335a93d08f5d06be7014ff92b9c8a03c9fc87df28d3007a7644dfcff0b41818fe568d3c807e85ea7972c72c8c5fa946aec51c9ad61650668b96e54a1887d9b2e19eef996fea54aa10d8a1241fd296f0f870af651f39437729d5983e723b2654507c89eaf4c89463551c78bf5e53ef4dcaa624a5382b95fc9012920655b9022876b9495a5e3ea33ea017860c6b6728d0e67351e04b4e8b4477afd384673febaa7ccb401a2dc187f18211103de653765c8ac751b790407c1f39a5deeded8471525655f1f194dc7ff9b1163214819f17cfb13babf6a580535935a14429a7aa4a83a2a9020dbdc2cd22bae5b3088d095ef1f1319849f41eb6b64f3156f848bef7abdbbbcbb27a8eea579521af156757ff3ebcb3147f0fff819dafcb2fd53167c7a1b72d4fd0670a8e4cb12f99d382665194d5f7afbf6f0836dc983dbf1df2abc04bc6e7588def728aa8f88d3b3fc773dee82251b7a0f6e041d8013b3c30428aed5a7e26f5b5c70c7ccd8aa4208f1ba53307db29b8523998dc42745199f57139683681dbc5e069069229e8b2bac4e54ff711fd83228c3f0d3c612b1140a866980f0a935b8765d781458a021c587b25d2b708a923cf18ef66619f23ba74c24fdc3d24772cec652cf5cd243beb92be1c200871947d2c98f795e7814d062d2ad05efdb7d631ab739387db9d0a7a16acefd55f22020cae103a475400b493e7566a75330fef7b617c9fb7695a9e3baa1bb18490374581bb2b8d0adb4bfddc811910b51f4b4f5d61c41c8b806aac5fcd112c010b7f95608aa743dbf08b51e09b73ebb06310812814882a5daf58fba5329892571b0303bd3f2f43a378decc428bc7123e852b1c25077221a33261b21f42a5d49f7fee2bcbb5b14b532dcabae2fc67207e493d22ba0c6ec9483cec6e129ec2ce8dc9a14f708832a3bdccf7edd2c650a919f1eb63a1ff370f4c22704d04ca6c5492dbf274e5ef6447d7d78592787e62dba46cdcc11643ca743ad997a43ed242d3cd3359c4f28f9d77a4c341f007d5fa5c2170736bffdf547de324522f27201222878771bd78f565dd9f8a00d525cc7c270ee10d90dd3d77e9b559bcb278f8e71e0826c613d23189fc1bd6a36bd640f42cde8e43697dac2058e71ae6b1ca1a8c1a27743a46602dd049328caf300c53c2407cc303b32d52ef4434cb5c56a10650e3e9333da8a02c89a31bc373675e356d8501a4e3d9e56abd170ac831d361c3e293829e2ef7c138fd35b7d2e4d87f5b0d531da18f2a745f028239eecae60f1923eab195780342e7715424e4fd807734fe65faafeec985a799c29f132596313e1f8c6f7a30b7eaca135318747186e2ca0f7e6625cfdbbde5d8bc4a7db045bfccea049645066ac9161351af15c37199efad8631dac5e449570f036d5cff6099e17df2e064820a7e539ab822e814983b552f90c974955e78d6830176d688033a836c6a784eb756e066fd62726cd1bfffabd5579d32b4799a7a05741150f0be99c4d9f725219d54e3f9f5d984bc6517c7340892119274f0525951cb0b243d02779ab1227308148f08aeedcfba35681fd5023adfb22bf62dfcedb011f4f24252e6302f8a7ea311ac852f045f32bb61b8a4949398f804b9be8e8b602bee378c887db55d39efa62423338019b6c8e5f5989bed8f5aa9d150466f31036b49e3624562b09ea0a206f4dfbd301929d45b581fca373ba9149ecd4efe056dacb0f6926d21d3dd70811da463ec4fc7be785171e1adf31f818cb3e861a1d49874762c8264b080e267ef772dda447e25bbb31d73e5338d784f80ecc6e960415fddf2a2cbc3bb012cfd8e2ff016e89ddd40d798f52c0a54a5564397cb60cb7fbb60eba99acc17f7753cf34d6901bb3328e72593200fd8874c11318b5de01b753a8d6b1b2ff5b8bd287884ee98f6b7b7bd298ce40a1b99782d48d0cff8e5f43062c57450f52801e932876a4eae0c56abb768424b7f6c842d29f1dfa5a32b1648442d352daf566d9386ed158fc7a37ab70484a1590985338b50a1cdf11a5871d365f1682b36de99964a5e4bb8a80328cf71280030dd85fa47c40d5494910c4fa26aa664d82e280c1fb92c448d0197d80ecedc8143da92e23c6912f02aa0000f52f9f26b6265bfab526baeb50ba5b996839f883422f73ff398cd03b49c98cef80adc5e3892d58de783e6327a0b5b752b38314724644b33598655a2c07d9612438067779af33979753ba4c2403408de47c2a30861cc9579342c05bc167e19477dc0029277e8c55717ff6acf2616a10b42450f50e7ea53480f146e4e5b1c2c549c61eb2f8a009fcef1f453a36d461d639605694b9a570f985cfd5f5278f022054955619c0c17e623308bc64ea861715f3e75ede86817681eb0afd3aaa9f0fb4cbdd277d31c697874e70c4198a4803d97a7270380bbc5fbd0c656fcd37e865fbea61cf05a939c90065585d530f5e4ef0d9722f5c7fa39c3594c124f32bae262ab87792124a2c9b067483f07405ab5be7c06c3d39ac215cc7d580eda35b4d653e6ffcbd79af50e6b23269b2eb0f7a3a80dc129d3c3cf3ff9a12447ded3f87e7752e575079e453cae38a6fba00b46cf5dd42d8bd7323f32226d57be4d6fdfa2a38e6ad2cf1d6b7e5c2204aac987e10deb46d45436bb42ee6321922deacd312372d59e30a84682101a14bd5633f9c3d61d311c2d6918b2ad3a73c765672216858e44f4864b4fb75bf285ddd06b65ee07ceb4ef790b798e33ccb1b46bb18993ddaf595298e3495941500a8edcf13f3f05013cf1bbf93001d6dad5a4cac0bac5fda1198435dae1699e5d0912612d25ac666f37d4af635a81fbc57ef4aefb48bf62229aae818e8cc23014bc222d6ac70d6c41830d7ba8e21e42fd2ea00a3ed06d067ef9a9bb30bc717db99939198539f44c9d3ff2ef8cfa53e56d36b8e4f74d201af6c510a51d5f16510d49417f8163c7ee4ed1bb6d2f030477f53f946ee9e62e4950af59e05054784741b887a4d4f8d57d933224ed3bd6ffe332da186f08edb0f83900e7e39395dd8c9eb9c491e85e6507f1961aedb3ff6959de6d63770da1f565b22f55d891c129458049643ddbe1c78bc5b171d5350fb90523de257a0f2ceb35c724013638b41d6f02144733808a0b38005edcdaaf561c45f9ace3b14a0671756f9f83b12d96a65db1ed78ff1b552774a18c9132742d1f037030babc248d95b2e8e9cd4d435c060122a526bfa477c29434e192961822eba40d1c1082b70f67a2c8bf85f1e7a90d42b410a38ad8704bd713f99996504f763250b7ce0e451db45d3ac90bbfffbc09ac8f5d0710a6ed0192a4b0ed872fd094f53fa72fb2bc38bc2d6bf1396fd4485b38838b5758e819d400ebaafb6924a6852a3edb1ff9436b066801e01ed8f465d4cffa96030b34deb54bc412bbd91966c386f2da08380c3b462922b04afae02ce14754d0a4a854387ee7cf63c902285db604d4fd25265d0874434a7626a0031582e416e6d9ce3b1dec40a30157b3ff686d8076704ec64a518307ce2db205de9941aad50db7a7fef230947fa1dbde5806f7a3c2c4c19f8a047a6e35411afda1ea7c27a955019e479652faee58b629c036f5c553faa2e565ca6626a1c7fa92fdea44a855139f5c12cf635bc35d0f6d23c3475cd9368dea3faed8db0bfc16dba3ba150cc1a3f6d80bc09b76694260b2ac568a82b4990d52853f873fbc105ea1ca7724d44344a550547128a4f790967d13f75d970fbeb2fbeb78c91a82d41d22463fcb040bdc14465a6b6757ade418a8363ba2bf6ebe865376bc26f512bcb2a82155e348b3aebb99a91f7055bde034585c20ae3b8cba3a36709469eccf3dab9108d1f51f3d96ef7d256a2eb95388f736a0ccd2c0bd6462449f1d117f7f7b07b30fad2b37afeef12eaaa853c44d27768bfc4348237f599ef535dd9c51f87d2741a8aa981b7cfb231e299fd40970b713141ab30e0e90e021626fc8f650922895fec80a4b2bc517d5d3a5909f28ef5748afb8f4252e8be1fd6ded05bcc8a1318719dd2c3b3360ed5e23239826e6beb1100afb9a2a6f8336672c8e48bd1a2bc43160cf5480cac2b211c657cb88f802d1e397732f4738fcb7e526df8ed0e1092c95597e02b5f02d3a00d4e1c135e6978be630c0f68bb6d7bfd64e5715ff65a3d221634dca3f9fc6eff052590ff25ae2b51fccfe13845b534b94cd5c0c8f3d92c184988bc540edf3ee4d8f8c9f2ce61165247c859c8eb0334608e327620540702dd29822c28d83f5c0c6c1c26f09dc76f46801e60ee198ba4398bf802a3f5d69846eef3472a563c2defa9a4bab0dc48fdfd193e04937edd7e80f39e28adc71f8145efc80a5f056125d1b72957d5bcb8f9bc4e6c83fddaf9ac7d3db82ebdd7c3dc9a5dd38598b467f6450fc428855ea2b08fda4e29428be8e9e73317d4540fc8e68c1bc84a38b89911acf78c8eda0638c6d4a5d8a6a7bb52702f5f001a9b3149cf4ee673337c05b507237bc056593944c6c1f8ac00522a005839c1db4c824ebcf70701be235637fc59d3d064e9ec4b4d4168904b1beeb8eb00e036a4bb83636f1b5cc340b17e729ab3c0b032706440a17e67204fcc5727746a30ef75544f11f9222a8375c9374d02c60c582840fd9ee95e22d3bfbf8d0271d37878f6192eee7cb4fc1e2bd94c93b5f0334e2d54c99d4a6811f54c640d58ce81946fdecec975cc44a97006be6d223cde262ae9e199cef37c141d089c28d1801796c8c4a5bd8addb51e977c66c71e73ad32933f3a1d3e79ba7763630162ea9ed06c91d7b6018837b83a1a52eb1fa66d1a9a1283e602ac5e55dbdb6701a9a66095ac95e08bd21a1b087c62e55194bd6d7527229b749d9a03aa4342223dc7e3334ebc77e090de182b15ba492f85aa15730908a73bb4fa25d75b48de7592e91d6fabf1021db9e9dbcd7d7c446a0fd63426e7b0ee1897c6726156bef3ee0261b8d76f45cb0106a163b97d1fc2907ea62cf77109401c600d148c39b77ba7c9253f7288c6edc72eb478e42cbe5e4f3fe10ac27b7c3a6435bbe0f69ec54fe44e612ed15366e986a6ccced69661c58c27d2e51f10c2f390db1975d62cf3e93869fd5fae3133da6ba472c8fee280cecbf9f52563d21738c61687d921df58c88b0afe80dacbd85bc086572dfd37fed7d8f851636469731122338a1a528ae6e8d67f49f0f9958745fe6857a67587e74c29356af2588ec221c84c26712254929e87cf5af5b8091ef2f570faaea87aa153e317f12f84b7bccb1263a3128b24e40e52ceb45f33f305bfb17c7c88882c253d09f5817846dc112817e5d78c458e334e9532185d35f157361f577e7e8dde75dc1b49b821a7b0dc3d00d6d325ca832a86352d20ffd2e4f0e2947581e5acdefc92c6b7143644a8d32fd5a04e8dcfe87307c1588965846b8981a3c0167aa3c4bfce524c02cc9dc44ba9f139a077a8e565e9f615d926a6cda2222eecde9d57c9825cf7c9d3e70351bf11fc3a40f776e1f42e07904d9ab67f322d4f49df69c2bc264174793e1cf53b3549d7709fec6bf0c02e535c768e7ddb408f52de90907f83525391cfdb3f77d920b2a15fdd5240d62e36344bd2557f676101e7f650fd6ce5276049a61e84258ec1c337fe2fd420119ca0472bc830af241fb8e0142eed3bebf1b03ed8d1b1f3db06385fcfa60eb0a6ac9d604764833f4f76dec00ea113013fce9815b9918cecd3ebe901ff0558a87d84bed22dfa88080a90e330f921bf44e387165bc1f15d7bc5ec7d16f98759c85d3afa7147175623bb23a8552eff29a6068ba3a85952c59faafd21aa1ed721f2ec93e69381e4057243d428085f5f2c9a01c4c31d705479bea417a030eee71efcd6e2b2c22820146e00eb45c3002eb83141a74e4adc9e5a5cc3369e48973db877015bc97bbc6a736679eaed214307abb5073a343132d84ead78350858a11557e272e0e4a8d8180c5d71fd0336736727e854aa54e00e4aa5530afef74996f186c3de4f447a5a04d8cfab18c82de25566d2ef90cea198846d5af81799d0945e4a0fadaa3213c40bb95ac0b0413c0f22ff7bffc073189dc16311cbd3e159311a92e994c8fc645ddb8079817bf21e5873b8b807179c1a100a78d1e745389dbad25f2b441d1cf7554cb6ed85c7ab4c6caaf89a97d0cb33275683c800227df05f928706afa320871dbb8dbb3b4854c654b07a59c3e33b6fae301e122ebcb5e1bbce11a8d6a4ea52b8d148c4e01f6bd522f21781a974c6aa495b9af47c32dc1758b6570c62daff08c6fecef70c5b7d2afd2a4a7403ff57309199e36246e9a62313d9a3b752e1a692b1602b3f67f7950c83068046f4c9b302b4661cc0a11af8dc9809880fef682b15c24081e1d6288144bb038041624506297bf45298c0ef706ae08bb98e1117b9f8ee713a53a9973f0f1168e82feecfa2c36d0916a1d7c6c9a26b141f09fafe01943cdd9c0eb83faf4fcf4dc2d593d7fd0368d10cf59203b60972c41a1d895afe6f4ffdc872f2d7f0b7d55ddcf9ed9121739043692e9c52fff7deb141fd00c47043ad5747ab8bb979f99c2f46230c47857b9ab04381f78ac9edd86abfc3e6430b66f00be59e1c611bce246577651faf67833cd5c691d0b142c683dc02b10f249bf8bd4ab1396cc6c15b3426d84420cba4f6b3931007cd7f6243c7d80e875ff987cbde073549165dd1201fa23e5486c08c23a66e8cea60b4c9afcacba4fe16d00329f9af82bfb0fe0dc29b3ccfc04fb8cf173a0bbc4d763cc92fd6c18afb3c017b66aae49b12fb0308d6b42cf6f553d5fbf6ee7c28707b98d43c46e36de44a3d3d73418d578a4cb0ff6764d0db7cf18646a617fa72179a55d2899fa6f4e9fd8f49dff204c49c73cf1e37e6885e9d91d4a65cc5ebb7092ba4e6d63eb7e4983113b2962f8e93b45ca49ba5c85e260a3a5e1748bfe993ebb392b739eaaf3147cc9560e2987eae88a428f660fbdd3d19bacc1499bd8d74e1bf098976370f2c1189fdb18f014ae3bddcabbff23394a07d598754b2bf3ddb0925701ac960b84948b9ba69103323e

private def light (n : ℕ) : Bool :=
  if n≤178 then decide n.Prime else n.gcd 6235135397241908741680674639927586558582878361231153877729215864681715113389074517106770270394081618113953882713761626619212667044889245663364667862568799843977208366195524719896472807475423880975816549024219691598995799655217698833954618998814300242650289839922492033762220111298560000000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤32015) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 178 = 6235135397241908741680674639927586558582878361231153877729215864681715113389074517106770270394081618113953882713761626619212667044889245663364667862568799843977208366195524719896472807475423880975816549024219691598995799655217698833954618998814300242650289839922492033762220111298560000000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 178 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤32015 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 62 := by unfold smallValid; decide +kernel

private theorem sp62 : smallValid 62 63 := by unfold smallValid; decide +kernel

private theorem sp125 : smallValid 125 62 := by unfold smallValid; decide +kernel

private theorem sp187 : smallValid 187 63 := by unfold smallValid; decide +kernel

private theorem sp250 : smallValid 250 62 := by unfold smallValid; decide +kernel

private theorem sp312 : smallValid 312 63 := by unfold smallValid; decide +kernel

private theorem sp375 : smallValid 375 62 := by unfold smallValid; decide +kernel

private theorem sp437 : smallValid 437 63 := by unfold smallValid; decide +kernel

private theorem sp500 : smallValid 500 62 := by unfold smallValid; decide +kernel

private theorem sp562 : smallValid 562 63 := by unfold smallValid; decide +kernel

private theorem sp625 : smallValid 625 62 := by unfold smallValid; decide +kernel

private theorem sp687 : smallValid 687 63 := by unfold smallValid; decide +kernel

private theorem sp750 : smallValid 750 62 := by unfold smallValid; decide +kernel

private theorem sp812 : smallValid 812 63 := by unfold smallValid; decide +kernel

private theorem sp875 : smallValid 875 62 := by unfold smallValid; decide +kernel

private theorem sp937 : smallValid 937 63 := by unfold smallValid; decide +kernel

private theorem sp1000 : smallValid 1000 62 := by unfold smallValid; decide +kernel

private theorem sp1062 : smallValid 1062 63 := by unfold smallValid; decide +kernel

private theorem sp1125 : smallValid 1125 62 := by unfold smallValid; decide +kernel

private theorem sp1187 : smallValid 1187 63 := by unfold smallValid; decide +kernel

private theorem sp1250 : smallValid 1250 62 := by unfold smallValid; decide +kernel

private theorem sp1312 : smallValid 1312 63 := by unfold smallValid; decide +kernel

private theorem sp1375 : smallValid 1375 62 := by unfold smallValid; decide +kernel

private theorem sp1437 : smallValid 1437 63 := by unfold smallValid; decide +kernel

private theorem sp1500 : smallValid 1500 62 := by unfold smallValid; decide +kernel

private theorem sp1562 : smallValid 1562 63 := by unfold smallValid; decide +kernel

private theorem sp1625 : smallValid 1625 62 := by unfold smallValid; decide +kernel

private theorem sp1687 : smallValid 1687 63 := by unfold smallValid; decide +kernel

private theorem sp1750 : smallValid 1750 62 := by unfold smallValid; decide +kernel

private theorem sp1812 : smallValid 1812 63 := by unfold smallValid; decide +kernel

private theorem sp1875 : smallValid 1875 63 := by unfold smallValid; decide +kernel

private theorem sp1938 : smallValid 1938 63 := by unfold smallValid; decide +kernel

private theorem sp2001 : smallValid 2001 62 := by unfold smallValid; decide +kernel

private theorem sp2063 : smallValid 2063 63 := by unfold smallValid; decide +kernel

private theorem sp2126 : smallValid 2126 62 := by unfold smallValid; decide +kernel

private theorem sp2188 : smallValid 2188 63 := by unfold smallValid; decide +kernel

private theorem sp2251 : smallValid 2251 62 := by unfold smallValid; decide +kernel

private theorem sp2313 : smallValid 2313 63 := by unfold smallValid; decide +kernel

private theorem sp2376 : smallValid 2376 62 := by unfold smallValid; decide +kernel

private theorem sp2438 : smallValid 2438 63 := by unfold smallValid; decide +kernel

private theorem sp2501 : smallValid 2501 62 := by unfold smallValid; decide +kernel

private theorem sp2563 : smallValid 2563 63 := by unfold smallValid; decide +kernel

private theorem sp2626 : smallValid 2626 62 := by unfold smallValid; decide +kernel

private theorem sp2688 : smallValid 2688 63 := by unfold smallValid; decide +kernel

private theorem sp2751 : smallValid 2751 62 := by unfold smallValid; decide +kernel

private theorem sp2813 : smallValid 2813 63 := by unfold smallValid; decide +kernel

private theorem sp2876 : smallValid 2876 62 := by unfold smallValid; decide +kernel

private theorem sp2938 : smallValid 2938 63 := by unfold smallValid; decide +kernel

private theorem sp3001 : smallValid 3001 62 := by unfold smallValid; decide +kernel

private theorem sp3063 : smallValid 3063 63 := by unfold smallValid; decide +kernel

private theorem sp3126 : smallValid 3126 62 := by unfold smallValid; decide +kernel

private theorem sp3188 : smallValid 3188 63 := by unfold smallValid; decide +kernel

private theorem sp3251 : smallValid 3251 62 := by unfold smallValid; decide +kernel

private theorem sp3313 : smallValid 3313 63 := by unfold smallValid; decide +kernel

private theorem sp3376 : smallValid 3376 62 := by unfold smallValid; decide +kernel

private theorem sp3438 : smallValid 3438 63 := by unfold smallValid; decide +kernel

private theorem sp3501 : smallValid 3501 62 := by unfold smallValid; decide +kernel

private theorem sp3563 : smallValid 3563 63 := by unfold smallValid; decide +kernel

private theorem sp3626 : smallValid 3626 62 := by unfold smallValid; decide +kernel

private theorem sp3688 : smallValid 3688 63 := by unfold smallValid; decide +kernel

private theorem sp3751 : smallValid 3751 62 := by unfold smallValid; decide +kernel

private theorem sp3813 : smallValid 3813 63 := by unfold smallValid; decide +kernel

private theorem sp3876 : smallValid 3876 63 := by unfold smallValid; decide +kernel

private theorem sp3939 : smallValid 3939 63 := by unfold smallValid; decide +kernel

private theorem sp4002 : smallValid 4002 62 := by unfold smallValid; decide +kernel

private theorem sp4064 : smallValid 4064 63 := by unfold smallValid; decide +kernel

private theorem sp4127 : smallValid 4127 62 := by unfold smallValid; decide +kernel

private theorem sp4189 : smallValid 4189 63 := by unfold smallValid; decide +kernel

private theorem sp4252 : smallValid 4252 62 := by unfold smallValid; decide +kernel

private theorem sp4314 : smallValid 4314 63 := by unfold smallValid; decide +kernel

private theorem sp4377 : smallValid 4377 62 := by unfold smallValid; decide +kernel

private theorem sp4439 : smallValid 4439 63 := by unfold smallValid; decide +kernel

private theorem sp4502 : smallValid 4502 62 := by unfold smallValid; decide +kernel

private theorem sp4564 : smallValid 4564 63 := by unfold smallValid; decide +kernel

private theorem sp4627 : smallValid 4627 62 := by unfold smallValid; decide +kernel

private theorem sp4689 : smallValid 4689 63 := by unfold smallValid; decide +kernel

private theorem sp4752 : smallValid 4752 62 := by unfold smallValid; decide +kernel

private theorem sp4814 : smallValid 4814 63 := by unfold smallValid; decide +kernel

private theorem sp4877 : smallValid 4877 62 := by unfold smallValid; decide +kernel

private theorem sp4939 : smallValid 4939 63 := by unfold smallValid; decide +kernel

private theorem sp5002 : smallValid 5002 62 := by unfold smallValid; decide +kernel

private theorem sp5064 : smallValid 5064 63 := by unfold smallValid; decide +kernel

private theorem sp5127 : smallValid 5127 62 := by unfold smallValid; decide +kernel

private theorem sp5189 : smallValid 5189 63 := by unfold smallValid; decide +kernel

private theorem sp5252 : smallValid 5252 62 := by unfold smallValid; decide +kernel

private theorem sp5314 : smallValid 5314 63 := by unfold smallValid; decide +kernel

private theorem sp5377 : smallValid 5377 62 := by unfold smallValid; decide +kernel

private theorem sp5439 : smallValid 5439 63 := by unfold smallValid; decide +kernel

private theorem sp5502 : smallValid 5502 62 := by unfold smallValid; decide +kernel

private theorem sp5564 : smallValid 5564 63 := by unfold smallValid; decide +kernel

private theorem sp5627 : smallValid 5627 62 := by unfold smallValid; decide +kernel

private theorem sp5689 : smallValid 5689 63 := by unfold smallValid; decide +kernel

private theorem sp5752 : smallValid 5752 62 := by unfold smallValid; decide +kernel

private theorem sp5814 : smallValid 5814 63 := by unfold smallValid; decide +kernel

private theorem sp5877 : smallValid 5877 63 := by unfold smallValid; decide +kernel

private theorem sp5940 : smallValid 5940 63 := by unfold smallValid; decide +kernel

private theorem sp6003 : smallValid 6003 62 := by unfold smallValid; decide +kernel

private theorem sp6065 : smallValid 6065 63 := by unfold smallValid; decide +kernel

private theorem sp6128 : smallValid 6128 62 := by unfold smallValid; decide +kernel

private theorem sp6190 : smallValid 6190 63 := by unfold smallValid; decide +kernel

private theorem sp6253 : smallValid 6253 62 := by unfold smallValid; decide +kernel

private theorem sp6315 : smallValid 6315 63 := by unfold smallValid; decide +kernel

private theorem sp6378 : smallValid 6378 62 := by unfold smallValid; decide +kernel

private theorem sp6440 : smallValid 6440 63 := by unfold smallValid; decide +kernel

private theorem sp6503 : smallValid 6503 62 := by unfold smallValid; decide +kernel

private theorem sp6565 : smallValid 6565 63 := by unfold smallValid; decide +kernel

private theorem sp6628 : smallValid 6628 62 := by unfold smallValid; decide +kernel

private theorem sp6690 : smallValid 6690 63 := by unfold smallValid; decide +kernel

private theorem sp6753 : smallValid 6753 62 := by unfold smallValid; decide +kernel

private theorem sp6815 : smallValid 6815 63 := by unfold smallValid; decide +kernel

private theorem sp6878 : smallValid 6878 62 := by unfold smallValid; decide +kernel

private theorem sp6940 : smallValid 6940 63 := by unfold smallValid; decide +kernel

private theorem sp7003 : smallValid 7003 62 := by unfold smallValid; decide +kernel

private theorem sp7065 : smallValid 7065 63 := by unfold smallValid; decide +kernel

private theorem sp7128 : smallValid 7128 62 := by unfold smallValid; decide +kernel

private theorem sp7190 : smallValid 7190 63 := by unfold smallValid; decide +kernel

private theorem sp7253 : smallValid 7253 62 := by unfold smallValid; decide +kernel

private theorem sp7315 : smallValid 7315 63 := by unfold smallValid; decide +kernel

private theorem sp7378 : smallValid 7378 62 := by unfold smallValid; decide +kernel

private theorem sp7440 : smallValid 7440 63 := by unfold smallValid; decide +kernel

private theorem sp7503 : smallValid 7503 62 := by unfold smallValid; decide +kernel

private theorem sp7565 : smallValid 7565 63 := by unfold smallValid; decide +kernel

private theorem sp7628 : smallValid 7628 62 := by unfold smallValid; decide +kernel

private theorem sp7690 : smallValid 7690 63 := by unfold smallValid; decide +kernel

private theorem sp7753 : smallValid 7753 62 := by unfold smallValid; decide +kernel

private theorem sp7815 : smallValid 7815 63 := by unfold smallValid; decide +kernel

private theorem sp7878 : smallValid 7878 63 := by unfold smallValid; decide +kernel

private theorem sp7941 : smallValid 7941 63 := by unfold smallValid; decide +kernel

private theorem sp8004 : smallValid 8004 62 := by unfold smallValid; decide +kernel

private theorem sp8066 : smallValid 8066 63 := by unfold smallValid; decide +kernel

private theorem sp8129 : smallValid 8129 62 := by unfold smallValid; decide +kernel

private theorem sp8191 : smallValid 8191 63 := by unfold smallValid; decide +kernel

private theorem sp8254 : smallValid 8254 62 := by unfold smallValid; decide +kernel

private theorem sp8316 : smallValid 8316 63 := by unfold smallValid; decide +kernel

private theorem sp8379 : smallValid 8379 62 := by unfold smallValid; decide +kernel

private theorem sp8441 : smallValid 8441 63 := by unfold smallValid; decide +kernel

private theorem sp8504 : smallValid 8504 62 := by unfold smallValid; decide +kernel

private theorem sp8566 : smallValid 8566 63 := by unfold smallValid; decide +kernel

private theorem sp8629 : smallValid 8629 62 := by unfold smallValid; decide +kernel

private theorem sp8691 : smallValid 8691 63 := by unfold smallValid; decide +kernel

private theorem sp8754 : smallValid 8754 62 := by unfold smallValid; decide +kernel

private theorem sp8816 : smallValid 8816 63 := by unfold smallValid; decide +kernel

private theorem sp8879 : smallValid 8879 62 := by unfold smallValid; decide +kernel

private theorem sp8941 : smallValid 8941 63 := by unfold smallValid; decide +kernel

private theorem sp9004 : smallValid 9004 62 := by unfold smallValid; decide +kernel

private theorem sp9066 : smallValid 9066 63 := by unfold smallValid; decide +kernel

private theorem sp9129 : smallValid 9129 62 := by unfold smallValid; decide +kernel

private theorem sp9191 : smallValid 9191 63 := by unfold smallValid; decide +kernel

private theorem sp9254 : smallValid 9254 62 := by unfold smallValid; decide +kernel

private theorem sp9316 : smallValid 9316 63 := by unfold smallValid; decide +kernel

private theorem sp9379 : smallValid 9379 62 := by unfold smallValid; decide +kernel

private theorem sp9441 : smallValid 9441 63 := by unfold smallValid; decide +kernel

private theorem sp9504 : smallValid 9504 62 := by unfold smallValid; decide +kernel

private theorem sp9566 : smallValid 9566 63 := by unfold smallValid; decide +kernel

private theorem sp9629 : smallValid 9629 62 := by unfold smallValid; decide +kernel

private theorem sp9691 : smallValid 9691 63 := by unfold smallValid; decide +kernel

private theorem sp9754 : smallValid 9754 62 := by unfold smallValid; decide +kernel

private theorem sp9816 : smallValid 9816 63 := by unfold smallValid; decide +kernel

private theorem sp9879 : smallValid 9879 63 := by unfold smallValid; decide +kernel

private theorem sp9942 : smallValid 9942 63 := by unfold smallValid; decide +kernel

private theorem sp10005 : smallValid 10005 62 := by unfold smallValid; decide +kernel

private theorem sp10067 : smallValid 10067 63 := by unfold smallValid; decide +kernel

private theorem sp10130 : smallValid 10130 62 := by unfold smallValid; decide +kernel

private theorem sp10192 : smallValid 10192 63 := by unfold smallValid; decide +kernel

private theorem sp10255 : smallValid 10255 62 := by unfold smallValid; decide +kernel

private theorem sp10317 : smallValid 10317 63 := by unfold smallValid; decide +kernel

private theorem sp10380 : smallValid 10380 62 := by unfold smallValid; decide +kernel

private theorem sp10442 : smallValid 10442 63 := by unfold smallValid; decide +kernel

private theorem sp10505 : smallValid 10505 62 := by unfold smallValid; decide +kernel

private theorem sp10567 : smallValid 10567 63 := by unfold smallValid; decide +kernel

private theorem sp10630 : smallValid 10630 62 := by unfold smallValid; decide +kernel

private theorem sp10692 : smallValid 10692 63 := by unfold smallValid; decide +kernel

private theorem sp10755 : smallValid 10755 62 := by unfold smallValid; decide +kernel

private theorem sp10817 : smallValid 10817 63 := by unfold smallValid; decide +kernel

private theorem sp10880 : smallValid 10880 62 := by unfold smallValid; decide +kernel

private theorem sp10942 : smallValid 10942 63 := by unfold smallValid; decide +kernel

private theorem sp11005 : smallValid 11005 62 := by unfold smallValid; decide +kernel

private theorem sp11067 : smallValid 11067 63 := by unfold smallValid; decide +kernel

private theorem sp11130 : smallValid 11130 62 := by unfold smallValid; decide +kernel

private theorem sp11192 : smallValid 11192 63 := by unfold smallValid; decide +kernel

private theorem sp11255 : smallValid 11255 62 := by unfold smallValid; decide +kernel

private theorem sp11317 : smallValid 11317 63 := by unfold smallValid; decide +kernel

private theorem sp11380 : smallValid 11380 62 := by unfold smallValid; decide +kernel

private theorem sp11442 : smallValid 11442 63 := by unfold smallValid; decide +kernel

private theorem sp11505 : smallValid 11505 62 := by unfold smallValid; decide +kernel

private theorem sp11567 : smallValid 11567 63 := by unfold smallValid; decide +kernel

private theorem sp11630 : smallValid 11630 62 := by unfold smallValid; decide +kernel

private theorem sp11692 : smallValid 11692 63 := by unfold smallValid; decide +kernel

private theorem sp11755 : smallValid 11755 62 := by unfold smallValid; decide +kernel

private theorem sp11817 : smallValid 11817 63 := by unfold smallValid; decide +kernel

private theorem sp11880 : smallValid 11880 63 := by unfold smallValid; decide +kernel

private theorem sp11943 : smallValid 11943 63 := by unfold smallValid; decide +kernel

private theorem sp12006 : smallValid 12006 62 := by unfold smallValid; decide +kernel

private theorem sp12068 : smallValid 12068 63 := by unfold smallValid; decide +kernel

private theorem sp12131 : smallValid 12131 62 := by unfold smallValid; decide +kernel

private theorem sp12193 : smallValid 12193 63 := by unfold smallValid; decide +kernel

private theorem sp12256 : smallValid 12256 62 := by unfold smallValid; decide +kernel

private theorem sp12318 : smallValid 12318 63 := by unfold smallValid; decide +kernel

private theorem sp12381 : smallValid 12381 62 := by unfold smallValid; decide +kernel

private theorem sp12443 : smallValid 12443 63 := by unfold smallValid; decide +kernel

private theorem sp12506 : smallValid 12506 62 := by unfold smallValid; decide +kernel

private theorem sp12568 : smallValid 12568 63 := by unfold smallValid; decide +kernel

private theorem sp12631 : smallValid 12631 62 := by unfold smallValid; decide +kernel

private theorem sp12693 : smallValid 12693 63 := by unfold smallValid; decide +kernel

private theorem sp12756 : smallValid 12756 62 := by unfold smallValid; decide +kernel

private theorem sp12818 : smallValid 12818 63 := by unfold smallValid; decide +kernel

private theorem sp12881 : smallValid 12881 62 := by unfold smallValid; decide +kernel

private theorem sp12943 : smallValid 12943 63 := by unfold smallValid; decide +kernel

private theorem sp13006 : smallValid 13006 62 := by unfold smallValid; decide +kernel

private theorem sp13068 : smallValid 13068 63 := by unfold smallValid; decide +kernel

private theorem sp13131 : smallValid 13131 62 := by unfold smallValid; decide +kernel

private theorem sp13193 : smallValid 13193 63 := by unfold smallValid; decide +kernel

private theorem sp13256 : smallValid 13256 62 := by unfold smallValid; decide +kernel

private theorem sp13318 : smallValid 13318 63 := by unfold smallValid; decide +kernel

private theorem sp13381 : smallValid 13381 62 := by unfold smallValid; decide +kernel

private theorem sp13443 : smallValid 13443 63 := by unfold smallValid; decide +kernel

private theorem sp13506 : smallValid 13506 62 := by unfold smallValid; decide +kernel

private theorem sp13568 : smallValid 13568 63 := by unfold smallValid; decide +kernel

private theorem sp13631 : smallValid 13631 62 := by unfold smallValid; decide +kernel

private theorem sp13693 : smallValid 13693 63 := by unfold smallValid; decide +kernel

private theorem sp13756 : smallValid 13756 62 := by unfold smallValid; decide +kernel

private theorem sp13818 : smallValid 13818 63 := by unfold smallValid; decide +kernel

private theorem sp13881 : smallValid 13881 63 := by unfold smallValid; decide +kernel

private theorem sp13944 : smallValid 13944 63 := by unfold smallValid; decide +kernel

private theorem sp14007 : smallValid 14007 62 := by unfold smallValid; decide +kernel

private theorem sp14069 : smallValid 14069 63 := by unfold smallValid; decide +kernel

private theorem sp14132 : smallValid 14132 62 := by unfold smallValid; decide +kernel

private theorem sp14194 : smallValid 14194 63 := by unfold smallValid; decide +kernel

private theorem sp14257 : smallValid 14257 62 := by unfold smallValid; decide +kernel

private theorem sp14319 : smallValid 14319 63 := by unfold smallValid; decide +kernel

private theorem sp14382 : smallValid 14382 62 := by unfold smallValid; decide +kernel

private theorem sp14444 : smallValid 14444 63 := by unfold smallValid; decide +kernel

private theorem sp14507 : smallValid 14507 62 := by unfold smallValid; decide +kernel

private theorem sp14569 : smallValid 14569 63 := by unfold smallValid; decide +kernel

private theorem sp14632 : smallValid 14632 62 := by unfold smallValid; decide +kernel

private theorem sp14694 : smallValid 14694 63 := by unfold smallValid; decide +kernel

private theorem sp14757 : smallValid 14757 62 := by unfold smallValid; decide +kernel

private theorem sp14819 : smallValid 14819 63 := by unfold smallValid; decide +kernel

private theorem sp14882 : smallValid 14882 62 := by unfold smallValid; decide +kernel

private theorem sp14944 : smallValid 14944 63 := by unfold smallValid; decide +kernel

private theorem sp15007 : smallValid 15007 62 := by unfold smallValid; decide +kernel

private theorem sp15069 : smallValid 15069 63 := by unfold smallValid; decide +kernel

private theorem sp15132 : smallValid 15132 62 := by unfold smallValid; decide +kernel

private theorem sp15194 : smallValid 15194 63 := by unfold smallValid; decide +kernel

private theorem sp15257 : smallValid 15257 62 := by unfold smallValid; decide +kernel

private theorem sp15319 : smallValid 15319 63 := by unfold smallValid; decide +kernel

private theorem sp15382 : smallValid 15382 62 := by unfold smallValid; decide +kernel

private theorem sp15444 : smallValid 15444 63 := by unfold smallValid; decide +kernel

private theorem sp15507 : smallValid 15507 62 := by unfold smallValid; decide +kernel

private theorem sp15569 : smallValid 15569 63 := by unfold smallValid; decide +kernel

private theorem sp15632 : smallValid 15632 62 := by unfold smallValid; decide +kernel

private theorem sp15694 : smallValid 15694 63 := by unfold smallValid; decide +kernel

private theorem sp15757 : smallValid 15757 62 := by unfold smallValid; decide +kernel

private theorem sp15819 : smallValid 15819 63 := by unfold smallValid; decide +kernel

private theorem sp15882 : smallValid 15882 63 := by unfold smallValid; decide +kernel

private theorem sp15945 : smallValid 15945 63 := by unfold smallValid; decide +kernel

private theorem sp16008 : smallValid 16008 62 := by unfold smallValid; decide +kernel

private theorem sp16070 : smallValid 16070 63 := by unfold smallValid; decide +kernel

private theorem sp16133 : smallValid 16133 62 := by unfold smallValid; decide +kernel

private theorem sp16195 : smallValid 16195 63 := by unfold smallValid; decide +kernel

private theorem sp16258 : smallValid 16258 62 := by unfold smallValid; decide +kernel

private theorem sp16320 : smallValid 16320 63 := by unfold smallValid; decide +kernel

private theorem sp16383 : smallValid 16383 62 := by unfold smallValid; decide +kernel

private theorem sp16445 : smallValid 16445 63 := by unfold smallValid; decide +kernel

private theorem sp16508 : smallValid 16508 62 := by unfold smallValid; decide +kernel

private theorem sp16570 : smallValid 16570 63 := by unfold smallValid; decide +kernel

private theorem sp16633 : smallValid 16633 62 := by unfold smallValid; decide +kernel

private theorem sp16695 : smallValid 16695 63 := by unfold smallValid; decide +kernel

private theorem sp16758 : smallValid 16758 62 := by unfold smallValid; decide +kernel

private theorem sp16820 : smallValid 16820 63 := by unfold smallValid; decide +kernel

private theorem sp16883 : smallValid 16883 62 := by unfold smallValid; decide +kernel

private theorem sp16945 : smallValid 16945 63 := by unfold smallValid; decide +kernel

private theorem sp17008 : smallValid 17008 62 := by unfold smallValid; decide +kernel

private theorem sp17070 : smallValid 17070 63 := by unfold smallValid; decide +kernel

private theorem sp17133 : smallValid 17133 62 := by unfold smallValid; decide +kernel

private theorem sp17195 : smallValid 17195 63 := by unfold smallValid; decide +kernel

private theorem sp17258 : smallValid 17258 62 := by unfold smallValid; decide +kernel

private theorem sp17320 : smallValid 17320 63 := by unfold smallValid; decide +kernel

private theorem sp17383 : smallValid 17383 62 := by unfold smallValid; decide +kernel

private theorem sp17445 : smallValid 17445 63 := by unfold smallValid; decide +kernel

private theorem sp17508 : smallValid 17508 62 := by unfold smallValid; decide +kernel

private theorem sp17570 : smallValid 17570 63 := by unfold smallValid; decide +kernel

private theorem sp17633 : smallValid 17633 62 := by unfold smallValid; decide +kernel

private theorem sp17695 : smallValid 17695 63 := by unfold smallValid; decide +kernel

private theorem sp17758 : smallValid 17758 62 := by unfold smallValid; decide +kernel

private theorem sp17820 : smallValid 17820 63 := by unfold smallValid; decide +kernel

private theorem sp17883 : smallValid 17883 63 := by unfold smallValid; decide +kernel

private theorem sp17946 : smallValid 17946 63 := by unfold smallValid; decide +kernel

private theorem sp18009 : smallValid 18009 62 := by unfold smallValid; decide +kernel

private theorem sp18071 : smallValid 18071 63 := by unfold smallValid; decide +kernel

private theorem sp18134 : smallValid 18134 62 := by unfold smallValid; decide +kernel

private theorem sp18196 : smallValid 18196 63 := by unfold smallValid; decide +kernel

private theorem sp18259 : smallValid 18259 62 := by unfold smallValid; decide +kernel

private theorem sp18321 : smallValid 18321 63 := by unfold smallValid; decide +kernel

private theorem sp18384 : smallValid 18384 62 := by unfold smallValid; decide +kernel

private theorem sp18446 : smallValid 18446 63 := by unfold smallValid; decide +kernel

private theorem sp18509 : smallValid 18509 62 := by unfold smallValid; decide +kernel

private theorem sp18571 : smallValid 18571 63 := by unfold smallValid; decide +kernel

private theorem sp18634 : smallValid 18634 62 := by unfold smallValid; decide +kernel

private theorem sp18696 : smallValid 18696 63 := by unfold smallValid; decide +kernel

private theorem sp18759 : smallValid 18759 62 := by unfold smallValid; decide +kernel

private theorem sp18821 : smallValid 18821 63 := by unfold smallValid; decide +kernel

private theorem sp18884 : smallValid 18884 62 := by unfold smallValid; decide +kernel

private theorem sp18946 : smallValid 18946 63 := by unfold smallValid; decide +kernel

private theorem sp19009 : smallValid 19009 62 := by unfold smallValid; decide +kernel

private theorem sp19071 : smallValid 19071 63 := by unfold smallValid; decide +kernel

private theorem sp19134 : smallValid 19134 62 := by unfold smallValid; decide +kernel

private theorem sp19196 : smallValid 19196 63 := by unfold smallValid; decide +kernel

private theorem sp19259 : smallValid 19259 62 := by unfold smallValid; decide +kernel

private theorem sp19321 : smallValid 19321 63 := by unfold smallValid; decide +kernel

private theorem sp19384 : smallValid 19384 62 := by unfold smallValid; decide +kernel

private theorem sp19446 : smallValid 19446 63 := by unfold smallValid; decide +kernel

private theorem sp19509 : smallValid 19509 62 := by unfold smallValid; decide +kernel

private theorem sp19571 : smallValid 19571 63 := by unfold smallValid; decide +kernel

private theorem sp19634 : smallValid 19634 62 := by unfold smallValid; decide +kernel

private theorem sp19696 : smallValid 19696 63 := by unfold smallValid; decide +kernel

private theorem sp19759 : smallValid 19759 62 := by unfold smallValid; decide +kernel

private theorem sp19821 : smallValid 19821 63 := by unfold smallValid; decide +kernel

private theorem sp19884 : smallValid 19884 63 := by unfold smallValid; decide +kernel

private theorem sp19947 : smallValid 19947 63 := by unfold smallValid; decide +kernel

private theorem sp20010 : smallValid 20010 62 := by unfold smallValid; decide +kernel

private theorem sp20072 : smallValid 20072 63 := by unfold smallValid; decide +kernel

private theorem sp20135 : smallValid 20135 62 := by unfold smallValid; decide +kernel

private theorem sp20197 : smallValid 20197 63 := by unfold smallValid; decide +kernel

private theorem sp20260 : smallValid 20260 62 := by unfold smallValid; decide +kernel

private theorem sp20322 : smallValid 20322 63 := by unfold smallValid; decide +kernel

private theorem sp20385 : smallValid 20385 62 := by unfold smallValid; decide +kernel

private theorem sp20447 : smallValid 20447 63 := by unfold smallValid; decide +kernel

private theorem sp20510 : smallValid 20510 62 := by unfold smallValid; decide +kernel

private theorem sp20572 : smallValid 20572 63 := by unfold smallValid; decide +kernel

private theorem sp20635 : smallValid 20635 62 := by unfold smallValid; decide +kernel

private theorem sp20697 : smallValid 20697 63 := by unfold smallValid; decide +kernel

private theorem sp20760 : smallValid 20760 62 := by unfold smallValid; decide +kernel

private theorem sp20822 : smallValid 20822 63 := by unfold smallValid; decide +kernel

private theorem sp20885 : smallValid 20885 62 := by unfold smallValid; decide +kernel

private theorem sp20947 : smallValid 20947 63 := by unfold smallValid; decide +kernel

private theorem sp21010 : smallValid 21010 62 := by unfold smallValid; decide +kernel

private theorem sp21072 : smallValid 21072 63 := by unfold smallValid; decide +kernel

private theorem sp21135 : smallValid 21135 62 := by unfold smallValid; decide +kernel

private theorem sp21197 : smallValid 21197 63 := by unfold smallValid; decide +kernel

private theorem sp21260 : smallValid 21260 62 := by unfold smallValid; decide +kernel

private theorem sp21322 : smallValid 21322 63 := by unfold smallValid; decide +kernel

private theorem sp21385 : smallValid 21385 62 := by unfold smallValid; decide +kernel

private theorem sp21447 : smallValid 21447 63 := by unfold smallValid; decide +kernel

private theorem sp21510 : smallValid 21510 62 := by unfold smallValid; decide +kernel

private theorem sp21572 : smallValid 21572 63 := by unfold smallValid; decide +kernel

private theorem sp21635 : smallValid 21635 62 := by unfold smallValid; decide +kernel

private theorem sp21697 : smallValid 21697 63 := by unfold smallValid; decide +kernel

private theorem sp21760 : smallValid 21760 62 := by unfold smallValid; decide +kernel

private theorem sp21822 : smallValid 21822 63 := by unfold smallValid; decide +kernel

private theorem sp21885 : smallValid 21885 63 := by unfold smallValid; decide +kernel

private theorem sp21948 : smallValid 21948 63 := by unfold smallValid; decide +kernel

private theorem sp22011 : smallValid 22011 62 := by unfold smallValid; decide +kernel

private theorem sp22073 : smallValid 22073 63 := by unfold smallValid; decide +kernel

private theorem sp22136 : smallValid 22136 62 := by unfold smallValid; decide +kernel

private theorem sp22198 : smallValid 22198 63 := by unfold smallValid; decide +kernel

private theorem sp22261 : smallValid 22261 62 := by unfold smallValid; decide +kernel

private theorem sp22323 : smallValid 22323 63 := by unfold smallValid; decide +kernel

private theorem sp22386 : smallValid 22386 62 := by unfold smallValid; decide +kernel

private theorem sp22448 : smallValid 22448 63 := by unfold smallValid; decide +kernel

private theorem sp22511 : smallValid 22511 62 := by unfold smallValid; decide +kernel

private theorem sp22573 : smallValid 22573 63 := by unfold smallValid; decide +kernel

private theorem sp22636 : smallValid 22636 62 := by unfold smallValid; decide +kernel

private theorem sp22698 : smallValid 22698 63 := by unfold smallValid; decide +kernel

private theorem sp22761 : smallValid 22761 62 := by unfold smallValid; decide +kernel

private theorem sp22823 : smallValid 22823 63 := by unfold smallValid; decide +kernel

private theorem sp22886 : smallValid 22886 62 := by unfold smallValid; decide +kernel

private theorem sp22948 : smallValid 22948 63 := by unfold smallValid; decide +kernel

private theorem sp23011 : smallValid 23011 62 := by unfold smallValid; decide +kernel

private theorem sp23073 : smallValid 23073 63 := by unfold smallValid; decide +kernel

private theorem sp23136 : smallValid 23136 62 := by unfold smallValid; decide +kernel

private theorem sp23198 : smallValid 23198 63 := by unfold smallValid; decide +kernel

private theorem sp23261 : smallValid 23261 62 := by unfold smallValid; decide +kernel

private theorem sp23323 : smallValid 23323 63 := by unfold smallValid; decide +kernel

private theorem sp23386 : smallValid 23386 62 := by unfold smallValid; decide +kernel

private theorem sp23448 : smallValid 23448 63 := by unfold smallValid; decide +kernel

private theorem sp23511 : smallValid 23511 62 := by unfold smallValid; decide +kernel

private theorem sp23573 : smallValid 23573 63 := by unfold smallValid; decide +kernel

private theorem sp23636 : smallValid 23636 62 := by unfold smallValid; decide +kernel

private theorem sp23698 : smallValid 23698 63 := by unfold smallValid; decide +kernel

private theorem sp23761 : smallValid 23761 62 := by unfold smallValid; decide +kernel

private theorem sp23823 : smallValid 23823 63 := by unfold smallValid; decide +kernel

private theorem sp23886 : smallValid 23886 63 := by unfold smallValid; decide +kernel

private theorem sp23949 : smallValid 23949 63 := by unfold smallValid; decide +kernel

private theorem sp24012 : smallValid 24012 62 := by unfold smallValid; decide +kernel

private theorem sp24074 : smallValid 24074 63 := by unfold smallValid; decide +kernel

private theorem sp24137 : smallValid 24137 62 := by unfold smallValid; decide +kernel

private theorem sp24199 : smallValid 24199 63 := by unfold smallValid; decide +kernel

private theorem sp24262 : smallValid 24262 62 := by unfold smallValid; decide +kernel

private theorem sp24324 : smallValid 24324 63 := by unfold smallValid; decide +kernel

private theorem sp24387 : smallValid 24387 62 := by unfold smallValid; decide +kernel

private theorem sp24449 : smallValid 24449 63 := by unfold smallValid; decide +kernel

private theorem sp24512 : smallValid 24512 62 := by unfold smallValid; decide +kernel

private theorem sp24574 : smallValid 24574 63 := by unfold smallValid; decide +kernel

private theorem sp24637 : smallValid 24637 62 := by unfold smallValid; decide +kernel

private theorem sp24699 : smallValid 24699 63 := by unfold smallValid; decide +kernel

private theorem sp24762 : smallValid 24762 62 := by unfold smallValid; decide +kernel

private theorem sp24824 : smallValid 24824 63 := by unfold smallValid; decide +kernel

private theorem sp24887 : smallValid 24887 62 := by unfold smallValid; decide +kernel

private theorem sp24949 : smallValid 24949 63 := by unfold smallValid; decide +kernel

private theorem sp25012 : smallValid 25012 62 := by unfold smallValid; decide +kernel

private theorem sp25074 : smallValid 25074 63 := by unfold smallValid; decide +kernel

private theorem sp25137 : smallValid 25137 62 := by unfold smallValid; decide +kernel

private theorem sp25199 : smallValid 25199 63 := by unfold smallValid; decide +kernel

private theorem sp25262 : smallValid 25262 62 := by unfold smallValid; decide +kernel

private theorem sp25324 : smallValid 25324 63 := by unfold smallValid; decide +kernel

private theorem sp25387 : smallValid 25387 62 := by unfold smallValid; decide +kernel

private theorem sp25449 : smallValid 25449 63 := by unfold smallValid; decide +kernel

private theorem sp25512 : smallValid 25512 62 := by unfold smallValid; decide +kernel

private theorem sp25574 : smallValid 25574 63 := by unfold smallValid; decide +kernel

private theorem sp25637 : smallValid 25637 62 := by unfold smallValid; decide +kernel

private theorem sp25699 : smallValid 25699 63 := by unfold smallValid; decide +kernel

private theorem sp25762 : smallValid 25762 62 := by unfold smallValid; decide +kernel

private theorem sp25824 : smallValid 25824 63 := by unfold smallValid; decide +kernel

private theorem sp25887 : smallValid 25887 63 := by unfold smallValid; decide +kernel

private theorem sp25950 : smallValid 25950 63 := by unfold smallValid; decide +kernel

private theorem sp26013 : smallValid 26013 62 := by unfold smallValid; decide +kernel

private theorem sp26075 : smallValid 26075 63 := by unfold smallValid; decide +kernel

private theorem sp26138 : smallValid 26138 62 := by unfold smallValid; decide +kernel

private theorem sp26200 : smallValid 26200 63 := by unfold smallValid; decide +kernel

private theorem sp26263 : smallValid 26263 62 := by unfold smallValid; decide +kernel

private theorem sp26325 : smallValid 26325 63 := by unfold smallValid; decide +kernel

private theorem sp26388 : smallValid 26388 62 := by unfold smallValid; decide +kernel

private theorem sp26450 : smallValid 26450 63 := by unfold smallValid; decide +kernel

private theorem sp26513 : smallValid 26513 62 := by unfold smallValid; decide +kernel

private theorem sp26575 : smallValid 26575 63 := by unfold smallValid; decide +kernel

private theorem sp26638 : smallValid 26638 62 := by unfold smallValid; decide +kernel

private theorem sp26700 : smallValid 26700 63 := by unfold smallValid; decide +kernel

private theorem sp26763 : smallValid 26763 62 := by unfold smallValid; decide +kernel

private theorem sp26825 : smallValid 26825 63 := by unfold smallValid; decide +kernel

private theorem sp26888 : smallValid 26888 62 := by unfold smallValid; decide +kernel

private theorem sp26950 : smallValid 26950 63 := by unfold smallValid; decide +kernel

private theorem sp27013 : smallValid 27013 62 := by unfold smallValid; decide +kernel

private theorem sp27075 : smallValid 27075 63 := by unfold smallValid; decide +kernel

private theorem sp27138 : smallValid 27138 62 := by unfold smallValid; decide +kernel

private theorem sp27200 : smallValid 27200 63 := by unfold smallValid; decide +kernel

private theorem sp27263 : smallValid 27263 62 := by unfold smallValid; decide +kernel

private theorem sp27325 : smallValid 27325 63 := by unfold smallValid; decide +kernel

private theorem sp27388 : smallValid 27388 62 := by unfold smallValid; decide +kernel

private theorem sp27450 : smallValid 27450 63 := by unfold smallValid; decide +kernel

private theorem sp27513 : smallValid 27513 62 := by unfold smallValid; decide +kernel

private theorem sp27575 : smallValid 27575 63 := by unfold smallValid; decide +kernel

private theorem sp27638 : smallValid 27638 62 := by unfold smallValid; decide +kernel

private theorem sp27700 : smallValid 27700 63 := by unfold smallValid; decide +kernel

private theorem sp27763 : smallValid 27763 62 := by unfold smallValid; decide +kernel

private theorem sp27825 : smallValid 27825 63 := by unfold smallValid; decide +kernel

private theorem sp27888 : smallValid 27888 63 := by unfold smallValid; decide +kernel

private theorem sp27951 : smallValid 27951 63 := by unfold smallValid; decide +kernel

private theorem sp28014 : smallValid 28014 62 := by unfold smallValid; decide +kernel

private theorem sp28076 : smallValid 28076 63 := by unfold smallValid; decide +kernel

private theorem sp28139 : smallValid 28139 62 := by unfold smallValid; decide +kernel

private theorem sp28201 : smallValid 28201 63 := by unfold smallValid; decide +kernel

private theorem sp28264 : smallValid 28264 62 := by unfold smallValid; decide +kernel

private theorem sp28326 : smallValid 28326 63 := by unfold smallValid; decide +kernel

private theorem sp28389 : smallValid 28389 62 := by unfold smallValid; decide +kernel

private theorem sp28451 : smallValid 28451 63 := by unfold smallValid; decide +kernel

private theorem sp28514 : smallValid 28514 62 := by unfold smallValid; decide +kernel

private theorem sp28576 : smallValid 28576 63 := by unfold smallValid; decide +kernel

private theorem sp28639 : smallValid 28639 62 := by unfold smallValid; decide +kernel

private theorem sp28701 : smallValid 28701 63 := by unfold smallValid; decide +kernel

private theorem sp28764 : smallValid 28764 62 := by unfold smallValid; decide +kernel

private theorem sp28826 : smallValid 28826 63 := by unfold smallValid; decide +kernel

private theorem sp28889 : smallValid 28889 62 := by unfold smallValid; decide +kernel

private theorem sp28951 : smallValid 28951 63 := by unfold smallValid; decide +kernel

private theorem sp29014 : smallValid 29014 62 := by unfold smallValid; decide +kernel

private theorem sp29076 : smallValid 29076 63 := by unfold smallValid; decide +kernel

private theorem sp29139 : smallValid 29139 62 := by unfold smallValid; decide +kernel

private theorem sp29201 : smallValid 29201 63 := by unfold smallValid; decide +kernel

private theorem sp29264 : smallValid 29264 62 := by unfold smallValid; decide +kernel

private theorem sp29326 : smallValid 29326 63 := by unfold smallValid; decide +kernel

private theorem sp29389 : smallValid 29389 62 := by unfold smallValid; decide +kernel

private theorem sp29451 : smallValid 29451 63 := by unfold smallValid; decide +kernel

private theorem sp29514 : smallValid 29514 62 := by unfold smallValid; decide +kernel

private theorem sp29576 : smallValid 29576 63 := by unfold smallValid; decide +kernel

private theorem sp29639 : smallValid 29639 62 := by unfold smallValid; decide +kernel

private theorem sp29701 : smallValid 29701 63 := by unfold smallValid; decide +kernel

private theorem sp29764 : smallValid 29764 62 := by unfold smallValid; decide +kernel

private theorem sp29826 : smallValid 29826 63 := by unfold smallValid; decide +kernel

private theorem sp29889 : smallValid 29889 63 := by unfold smallValid; decide +kernel

private theorem sp29952 : smallValid 29952 63 := by unfold smallValid; decide +kernel

private theorem sp30015 : smallValid 30015 62 := by unfold smallValid; decide +kernel

private theorem sp30077 : smallValid 30077 63 := by unfold smallValid; decide +kernel

private theorem sp30140 : smallValid 30140 62 := by unfold smallValid; decide +kernel

private theorem sp30202 : smallValid 30202 63 := by unfold smallValid; decide +kernel

private theorem sp30265 : smallValid 30265 62 := by unfold smallValid; decide +kernel

private theorem sp30327 : smallValid 30327 63 := by unfold smallValid; decide +kernel

private theorem sp30390 : smallValid 30390 62 := by unfold smallValid; decide +kernel

private theorem sp30452 : smallValid 30452 63 := by unfold smallValid; decide +kernel

private theorem sp30515 : smallValid 30515 62 := by unfold smallValid; decide +kernel

private theorem sp30577 : smallValid 30577 63 := by unfold smallValid; decide +kernel

private theorem sp30640 : smallValid 30640 62 := by unfold smallValid; decide +kernel

private theorem sp30702 : smallValid 30702 63 := by unfold smallValid; decide +kernel

private theorem sp30765 : smallValid 30765 62 := by unfold smallValid; decide +kernel

private theorem sp30827 : smallValid 30827 63 := by unfold smallValid; decide +kernel

private theorem sp30890 : smallValid 30890 62 := by unfold smallValid; decide +kernel

private theorem sp30952 : smallValid 30952 63 := by unfold smallValid; decide +kernel

private theorem sp31015 : smallValid 31015 62 := by unfold smallValid; decide +kernel

private theorem sp31077 : smallValid 31077 63 := by unfold smallValid; decide +kernel

private theorem sp31140 : smallValid 31140 62 := by unfold smallValid; decide +kernel

private theorem sp31202 : smallValid 31202 63 := by unfold smallValid; decide +kernel

private theorem sp31265 : smallValid 31265 62 := by unfold smallValid; decide +kernel

private theorem sp31327 : smallValid 31327 63 := by unfold smallValid; decide +kernel

private theorem sp31390 : smallValid 31390 62 := by unfold smallValid; decide +kernel

private theorem sp31452 : smallValid 31452 63 := by unfold smallValid; decide +kernel

private theorem sp31515 : smallValid 31515 62 := by unfold smallValid; decide +kernel

private theorem sp31577 : smallValid 31577 63 := by unfold smallValid; decide +kernel

private theorem sp31640 : smallValid 31640 62 := by unfold smallValid; decide +kernel

private theorem sp31702 : smallValid 31702 63 := by unfold smallValid; decide +kernel

private theorem sp31765 : smallValid 31765 62 := by unfold smallValid; decide +kernel

private theorem sp31827 : smallValid 31827 63 := by unfold smallValid; decide +kernel

private theorem sp31890 : smallValid 31890 63 := by unfold smallValid; decide +kernel

private theorem sp31953 : smallValid 31953 63 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤32015) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 32016 := (joinSmall (lo:=0) (a:=16008) (b:=16008) (joinSmall (lo:=0) (a:=8004) (b:=8004) (joinSmall (lo:=0) (a:=4002) (b:=4002) (joinSmall (lo:=0) (a:=2001) (b:=2001) (joinSmall (lo:=0) (a:=1000) (b:=1001) (joinSmall (lo:=0) (a:=500) (b:=500) (joinSmall (lo:=0) (a:=250) (b:=250) (joinSmall (lo:=0) (a:=125) (b:=125) (joinSmall (lo:=0) (a:=62) (b:=63) sp0 sp62) (joinSmall (lo:=125) (a:=62) (b:=63) sp125 sp187)) (joinSmall (lo:=250) (a:=125) (b:=125) (joinSmall (lo:=250) (a:=62) (b:=63) sp250 sp312) (joinSmall (lo:=375) (a:=62) (b:=63) sp375 sp437))) (joinSmall (lo:=500) (a:=250) (b:=250) (joinSmall (lo:=500) (a:=125) (b:=125) (joinSmall (lo:=500) (a:=62) (b:=63) sp500 sp562) (joinSmall (lo:=625) (a:=62) (b:=63) sp625 sp687)) (joinSmall (lo:=750) (a:=125) (b:=125) (joinSmall (lo:=750) (a:=62) (b:=63) sp750 sp812) (joinSmall (lo:=875) (a:=62) (b:=63) sp875 sp937)))) (joinSmall (lo:=1000) (a:=500) (b:=501) (joinSmall (lo:=1000) (a:=250) (b:=250) (joinSmall (lo:=1000) (a:=125) (b:=125) (joinSmall (lo:=1000) (a:=62) (b:=63) sp1000 sp1062) (joinSmall (lo:=1125) (a:=62) (b:=63) sp1125 sp1187)) (joinSmall (lo:=1250) (a:=125) (b:=125) (joinSmall (lo:=1250) (a:=62) (b:=63) sp1250 sp1312) (joinSmall (lo:=1375) (a:=62) (b:=63) sp1375 sp1437))) (joinSmall (lo:=1500) (a:=250) (b:=251) (joinSmall (lo:=1500) (a:=125) (b:=125) (joinSmall (lo:=1500) (a:=62) (b:=63) sp1500 sp1562) (joinSmall (lo:=1625) (a:=62) (b:=63) sp1625 sp1687)) (joinSmall (lo:=1750) (a:=125) (b:=126) (joinSmall (lo:=1750) (a:=62) (b:=63) sp1750 sp1812) (joinSmall (lo:=1875) (a:=63) (b:=63) sp1875 sp1938))))) (joinSmall (lo:=2001) (a:=1000) (b:=1001) (joinSmall (lo:=2001) (a:=500) (b:=500) (joinSmall (lo:=2001) (a:=250) (b:=250) (joinSmall (lo:=2001) (a:=125) (b:=125) (joinSmall (lo:=2001) (a:=62) (b:=63) sp2001 sp2063) (joinSmall (lo:=2126) (a:=62) (b:=63) sp2126 sp2188)) (joinSmall (lo:=2251) (a:=125) (b:=125) (joinSmall (lo:=2251) (a:=62) (b:=63) sp2251 sp2313) (joinSmall (lo:=2376) (a:=62) (b:=63) sp2376 sp2438))) (joinSmall (lo:=2501) (a:=250) (b:=250) (joinSmall (lo:=2501) (a:=125) (b:=125) (joinSmall (lo:=2501) (a:=62) (b:=63) sp2501 sp2563) (joinSmall (lo:=2626) (a:=62) (b:=63) sp2626 sp2688)) (joinSmall (lo:=2751) (a:=125) (b:=125) (joinSmall (lo:=2751) (a:=62) (b:=63) sp2751 sp2813) (joinSmall (lo:=2876) (a:=62) (b:=63) sp2876 sp2938)))) (joinSmall (lo:=3001) (a:=500) (b:=501) (joinSmall (lo:=3001) (a:=250) (b:=250) (joinSmall (lo:=3001) (a:=125) (b:=125) (joinSmall (lo:=3001) (a:=62) (b:=63) sp3001 sp3063) (joinSmall (lo:=3126) (a:=62) (b:=63) sp3126 sp3188)) (joinSmall (lo:=3251) (a:=125) (b:=125) (joinSmall (lo:=3251) (a:=62) (b:=63) sp3251 sp3313) (joinSmall (lo:=3376) (a:=62) (b:=63) sp3376 sp3438))) (joinSmall (lo:=3501) (a:=250) (b:=251) (joinSmall (lo:=3501) (a:=125) (b:=125) (joinSmall (lo:=3501) (a:=62) (b:=63) sp3501 sp3563) (joinSmall (lo:=3626) (a:=62) (b:=63) sp3626 sp3688)) (joinSmall (lo:=3751) (a:=125) (b:=126) (joinSmall (lo:=3751) (a:=62) (b:=63) sp3751 sp3813) (joinSmall (lo:=3876) (a:=63) (b:=63) sp3876 sp3939)))))) (joinSmall (lo:=4002) (a:=2001) (b:=2001) (joinSmall (lo:=4002) (a:=1000) (b:=1001) (joinSmall (lo:=4002) (a:=500) (b:=500) (joinSmall (lo:=4002) (a:=250) (b:=250) (joinSmall (lo:=4002) (a:=125) (b:=125) (joinSmall (lo:=4002) (a:=62) (b:=63) sp4002 sp4064) (joinSmall (lo:=4127) (a:=62) (b:=63) sp4127 sp4189)) (joinSmall (lo:=4252) (a:=125) (b:=125) (joinSmall (lo:=4252) (a:=62) (b:=63) sp4252 sp4314) (joinSmall (lo:=4377) (a:=62) (b:=63) sp4377 sp4439))) (joinSmall (lo:=4502) (a:=250) (b:=250) (joinSmall (lo:=4502) (a:=125) (b:=125) (joinSmall (lo:=4502) (a:=62) (b:=63) sp4502 sp4564) (joinSmall (lo:=4627) (a:=62) (b:=63) sp4627 sp4689)) (joinSmall (lo:=4752) (a:=125) (b:=125) (joinSmall (lo:=4752) (a:=62) (b:=63) sp4752 sp4814) (joinSmall (lo:=4877) (a:=62) (b:=63) sp4877 sp4939)))) (joinSmall (lo:=5002) (a:=500) (b:=501) (joinSmall (lo:=5002) (a:=250) (b:=250) (joinSmall (lo:=5002) (a:=125) (b:=125) (joinSmall (lo:=5002) (a:=62) (b:=63) sp5002 sp5064) (joinSmall (lo:=5127) (a:=62) (b:=63) sp5127 sp5189)) (joinSmall (lo:=5252) (a:=125) (b:=125) (joinSmall (lo:=5252) (a:=62) (b:=63) sp5252 sp5314) (joinSmall (lo:=5377) (a:=62) (b:=63) sp5377 sp5439))) (joinSmall (lo:=5502) (a:=250) (b:=251) (joinSmall (lo:=5502) (a:=125) (b:=125) (joinSmall (lo:=5502) (a:=62) (b:=63) sp5502 sp5564) (joinSmall (lo:=5627) (a:=62) (b:=63) sp5627 sp5689)) (joinSmall (lo:=5752) (a:=125) (b:=126) (joinSmall (lo:=5752) (a:=62) (b:=63) sp5752 sp5814) (joinSmall (lo:=5877) (a:=63) (b:=63) sp5877 sp5940))))) (joinSmall (lo:=6003) (a:=1000) (b:=1001) (joinSmall (lo:=6003) (a:=500) (b:=500) (joinSmall (lo:=6003) (a:=250) (b:=250) (joinSmall (lo:=6003) (a:=125) (b:=125) (joinSmall (lo:=6003) (a:=62) (b:=63) sp6003 sp6065) (joinSmall (lo:=6128) (a:=62) (b:=63) sp6128 sp6190)) (joinSmall (lo:=6253) (a:=125) (b:=125) (joinSmall (lo:=6253) (a:=62) (b:=63) sp6253 sp6315) (joinSmall (lo:=6378) (a:=62) (b:=63) sp6378 sp6440))) (joinSmall (lo:=6503) (a:=250) (b:=250) (joinSmall (lo:=6503) (a:=125) (b:=125) (joinSmall (lo:=6503) (a:=62) (b:=63) sp6503 sp6565) (joinSmall (lo:=6628) (a:=62) (b:=63) sp6628 sp6690)) (joinSmall (lo:=6753) (a:=125) (b:=125) (joinSmall (lo:=6753) (a:=62) (b:=63) sp6753 sp6815) (joinSmall (lo:=6878) (a:=62) (b:=63) sp6878 sp6940)))) (joinSmall (lo:=7003) (a:=500) (b:=501) (joinSmall (lo:=7003) (a:=250) (b:=250) (joinSmall (lo:=7003) (a:=125) (b:=125) (joinSmall (lo:=7003) (a:=62) (b:=63) sp7003 sp7065) (joinSmall (lo:=7128) (a:=62) (b:=63) sp7128 sp7190)) (joinSmall (lo:=7253) (a:=125) (b:=125) (joinSmall (lo:=7253) (a:=62) (b:=63) sp7253 sp7315) (joinSmall (lo:=7378) (a:=62) (b:=63) sp7378 sp7440))) (joinSmall (lo:=7503) (a:=250) (b:=251) (joinSmall (lo:=7503) (a:=125) (b:=125) (joinSmall (lo:=7503) (a:=62) (b:=63) sp7503 sp7565) (joinSmall (lo:=7628) (a:=62) (b:=63) sp7628 sp7690)) (joinSmall (lo:=7753) (a:=125) (b:=126) (joinSmall (lo:=7753) (a:=62) (b:=63) sp7753 sp7815) (joinSmall (lo:=7878) (a:=63) (b:=63) sp7878 sp7941))))))) (joinSmall (lo:=8004) (a:=4002) (b:=4002) (joinSmall (lo:=8004) (a:=2001) (b:=2001) (joinSmall (lo:=8004) (a:=1000) (b:=1001) (joinSmall (lo:=8004) (a:=500) (b:=500) (joinSmall (lo:=8004) (a:=250) (b:=250) (joinSmall (lo:=8004) (a:=125) (b:=125) (joinSmall (lo:=8004) (a:=62) (b:=63) sp8004 sp8066) (joinSmall (lo:=8129) (a:=62) (b:=63) sp8129 sp8191)) (joinSmall (lo:=8254) (a:=125) (b:=125) (joinSmall (lo:=8254) (a:=62) (b:=63) sp8254 sp8316) (joinSmall (lo:=8379) (a:=62) (b:=63) sp8379 sp8441))) (joinSmall (lo:=8504) (a:=250) (b:=250) (joinSmall (lo:=8504) (a:=125) (b:=125) (joinSmall (lo:=8504) (a:=62) (b:=63) sp8504 sp8566) (joinSmall (lo:=8629) (a:=62) (b:=63) sp8629 sp8691)) (joinSmall (lo:=8754) (a:=125) (b:=125) (joinSmall (lo:=8754) (a:=62) (b:=63) sp8754 sp8816) (joinSmall (lo:=8879) (a:=62) (b:=63) sp8879 sp8941)))) (joinSmall (lo:=9004) (a:=500) (b:=501) (joinSmall (lo:=9004) (a:=250) (b:=250) (joinSmall (lo:=9004) (a:=125) (b:=125) (joinSmall (lo:=9004) (a:=62) (b:=63) sp9004 sp9066) (joinSmall (lo:=9129) (a:=62) (b:=63) sp9129 sp9191)) (joinSmall (lo:=9254) (a:=125) (b:=125) (joinSmall (lo:=9254) (a:=62) (b:=63) sp9254 sp9316) (joinSmall (lo:=9379) (a:=62) (b:=63) sp9379 sp9441))) (joinSmall (lo:=9504) (a:=250) (b:=251) (joinSmall (lo:=9504) (a:=125) (b:=125) (joinSmall (lo:=9504) (a:=62) (b:=63) sp9504 sp9566) (joinSmall (lo:=9629) (a:=62) (b:=63) sp9629 sp9691)) (joinSmall (lo:=9754) (a:=125) (b:=126) (joinSmall (lo:=9754) (a:=62) (b:=63) sp9754 sp9816) (joinSmall (lo:=9879) (a:=63) (b:=63) sp9879 sp9942))))) (joinSmall (lo:=10005) (a:=1000) (b:=1001) (joinSmall (lo:=10005) (a:=500) (b:=500) (joinSmall (lo:=10005) (a:=250) (b:=250) (joinSmall (lo:=10005) (a:=125) (b:=125) (joinSmall (lo:=10005) (a:=62) (b:=63) sp10005 sp10067) (joinSmall (lo:=10130) (a:=62) (b:=63) sp10130 sp10192)) (joinSmall (lo:=10255) (a:=125) (b:=125) (joinSmall (lo:=10255) (a:=62) (b:=63) sp10255 sp10317) (joinSmall (lo:=10380) (a:=62) (b:=63) sp10380 sp10442))) (joinSmall (lo:=10505) (a:=250) (b:=250) (joinSmall (lo:=10505) (a:=125) (b:=125) (joinSmall (lo:=10505) (a:=62) (b:=63) sp10505 sp10567) (joinSmall (lo:=10630) (a:=62) (b:=63) sp10630 sp10692)) (joinSmall (lo:=10755) (a:=125) (b:=125) (joinSmall (lo:=10755) (a:=62) (b:=63) sp10755 sp10817) (joinSmall (lo:=10880) (a:=62) (b:=63) sp10880 sp10942)))) (joinSmall (lo:=11005) (a:=500) (b:=501) (joinSmall (lo:=11005) (a:=250) (b:=250) (joinSmall (lo:=11005) (a:=125) (b:=125) (joinSmall (lo:=11005) (a:=62) (b:=63) sp11005 sp11067) (joinSmall (lo:=11130) (a:=62) (b:=63) sp11130 sp11192)) (joinSmall (lo:=11255) (a:=125) (b:=125) (joinSmall (lo:=11255) (a:=62) (b:=63) sp11255 sp11317) (joinSmall (lo:=11380) (a:=62) (b:=63) sp11380 sp11442))) (joinSmall (lo:=11505) (a:=250) (b:=251) (joinSmall (lo:=11505) (a:=125) (b:=125) (joinSmall (lo:=11505) (a:=62) (b:=63) sp11505 sp11567) (joinSmall (lo:=11630) (a:=62) (b:=63) sp11630 sp11692)) (joinSmall (lo:=11755) (a:=125) (b:=126) (joinSmall (lo:=11755) (a:=62) (b:=63) sp11755 sp11817) (joinSmall (lo:=11880) (a:=63) (b:=63) sp11880 sp11943)))))) (joinSmall (lo:=12006) (a:=2001) (b:=2001) (joinSmall (lo:=12006) (a:=1000) (b:=1001) (joinSmall (lo:=12006) (a:=500) (b:=500) (joinSmall (lo:=12006) (a:=250) (b:=250) (joinSmall (lo:=12006) (a:=125) (b:=125) (joinSmall (lo:=12006) (a:=62) (b:=63) sp12006 sp12068) (joinSmall (lo:=12131) (a:=62) (b:=63) sp12131 sp12193)) (joinSmall (lo:=12256) (a:=125) (b:=125) (joinSmall (lo:=12256) (a:=62) (b:=63) sp12256 sp12318) (joinSmall (lo:=12381) (a:=62) (b:=63) sp12381 sp12443))) (joinSmall (lo:=12506) (a:=250) (b:=250) (joinSmall (lo:=12506) (a:=125) (b:=125) (joinSmall (lo:=12506) (a:=62) (b:=63) sp12506 sp12568) (joinSmall (lo:=12631) (a:=62) (b:=63) sp12631 sp12693)) (joinSmall (lo:=12756) (a:=125) (b:=125) (joinSmall (lo:=12756) (a:=62) (b:=63) sp12756 sp12818) (joinSmall (lo:=12881) (a:=62) (b:=63) sp12881 sp12943)))) (joinSmall (lo:=13006) (a:=500) (b:=501) (joinSmall (lo:=13006) (a:=250) (b:=250) (joinSmall (lo:=13006) (a:=125) (b:=125) (joinSmall (lo:=13006) (a:=62) (b:=63) sp13006 sp13068) (joinSmall (lo:=13131) (a:=62) (b:=63) sp13131 sp13193)) (joinSmall (lo:=13256) (a:=125) (b:=125) (joinSmall (lo:=13256) (a:=62) (b:=63) sp13256 sp13318) (joinSmall (lo:=13381) (a:=62) (b:=63) sp13381 sp13443))) (joinSmall (lo:=13506) (a:=250) (b:=251) (joinSmall (lo:=13506) (a:=125) (b:=125) (joinSmall (lo:=13506) (a:=62) (b:=63) sp13506 sp13568) (joinSmall (lo:=13631) (a:=62) (b:=63) sp13631 sp13693)) (joinSmall (lo:=13756) (a:=125) (b:=126) (joinSmall (lo:=13756) (a:=62) (b:=63) sp13756 sp13818) (joinSmall (lo:=13881) (a:=63) (b:=63) sp13881 sp13944))))) (joinSmall (lo:=14007) (a:=1000) (b:=1001) (joinSmall (lo:=14007) (a:=500) (b:=500) (joinSmall (lo:=14007) (a:=250) (b:=250) (joinSmall (lo:=14007) (a:=125) (b:=125) (joinSmall (lo:=14007) (a:=62) (b:=63) sp14007 sp14069) (joinSmall (lo:=14132) (a:=62) (b:=63) sp14132 sp14194)) (joinSmall (lo:=14257) (a:=125) (b:=125) (joinSmall (lo:=14257) (a:=62) (b:=63) sp14257 sp14319) (joinSmall (lo:=14382) (a:=62) (b:=63) sp14382 sp14444))) (joinSmall (lo:=14507) (a:=250) (b:=250) (joinSmall (lo:=14507) (a:=125) (b:=125) (joinSmall (lo:=14507) (a:=62) (b:=63) sp14507 sp14569) (joinSmall (lo:=14632) (a:=62) (b:=63) sp14632 sp14694)) (joinSmall (lo:=14757) (a:=125) (b:=125) (joinSmall (lo:=14757) (a:=62) (b:=63) sp14757 sp14819) (joinSmall (lo:=14882) (a:=62) (b:=63) sp14882 sp14944)))) (joinSmall (lo:=15007) (a:=500) (b:=501) (joinSmall (lo:=15007) (a:=250) (b:=250) (joinSmall (lo:=15007) (a:=125) (b:=125) (joinSmall (lo:=15007) (a:=62) (b:=63) sp15007 sp15069) (joinSmall (lo:=15132) (a:=62) (b:=63) sp15132 sp15194)) (joinSmall (lo:=15257) (a:=125) (b:=125) (joinSmall (lo:=15257) (a:=62) (b:=63) sp15257 sp15319) (joinSmall (lo:=15382) (a:=62) (b:=63) sp15382 sp15444))) (joinSmall (lo:=15507) (a:=250) (b:=251) (joinSmall (lo:=15507) (a:=125) (b:=125) (joinSmall (lo:=15507) (a:=62) (b:=63) sp15507 sp15569) (joinSmall (lo:=15632) (a:=62) (b:=63) sp15632 sp15694)) (joinSmall (lo:=15757) (a:=125) (b:=126) (joinSmall (lo:=15757) (a:=62) (b:=63) sp15757 sp15819) (joinSmall (lo:=15882) (a:=63) (b:=63) sp15882 sp15945)))))))) (joinSmall (lo:=16008) (a:=8004) (b:=8004) (joinSmall (lo:=16008) (a:=4002) (b:=4002) (joinSmall (lo:=16008) (a:=2001) (b:=2001) (joinSmall (lo:=16008) (a:=1000) (b:=1001) (joinSmall (lo:=16008) (a:=500) (b:=500) (joinSmall (lo:=16008) (a:=250) (b:=250) (joinSmall (lo:=16008) (a:=125) (b:=125) (joinSmall (lo:=16008) (a:=62) (b:=63) sp16008 sp16070) (joinSmall (lo:=16133) (a:=62) (b:=63) sp16133 sp16195)) (joinSmall (lo:=16258) (a:=125) (b:=125) (joinSmall (lo:=16258) (a:=62) (b:=63) sp16258 sp16320) (joinSmall (lo:=16383) (a:=62) (b:=63) sp16383 sp16445))) (joinSmall (lo:=16508) (a:=250) (b:=250) (joinSmall (lo:=16508) (a:=125) (b:=125) (joinSmall (lo:=16508) (a:=62) (b:=63) sp16508 sp16570) (joinSmall (lo:=16633) (a:=62) (b:=63) sp16633 sp16695)) (joinSmall (lo:=16758) (a:=125) (b:=125) (joinSmall (lo:=16758) (a:=62) (b:=63) sp16758 sp16820) (joinSmall (lo:=16883) (a:=62) (b:=63) sp16883 sp16945)))) (joinSmall (lo:=17008) (a:=500) (b:=501) (joinSmall (lo:=17008) (a:=250) (b:=250) (joinSmall (lo:=17008) (a:=125) (b:=125) (joinSmall (lo:=17008) (a:=62) (b:=63) sp17008 sp17070) (joinSmall (lo:=17133) (a:=62) (b:=63) sp17133 sp17195)) (joinSmall (lo:=17258) (a:=125) (b:=125) (joinSmall (lo:=17258) (a:=62) (b:=63) sp17258 sp17320) (joinSmall (lo:=17383) (a:=62) (b:=63) sp17383 sp17445))) (joinSmall (lo:=17508) (a:=250) (b:=251) (joinSmall (lo:=17508) (a:=125) (b:=125) (joinSmall (lo:=17508) (a:=62) (b:=63) sp17508 sp17570) (joinSmall (lo:=17633) (a:=62) (b:=63) sp17633 sp17695)) (joinSmall (lo:=17758) (a:=125) (b:=126) (joinSmall (lo:=17758) (a:=62) (b:=63) sp17758 sp17820) (joinSmall (lo:=17883) (a:=63) (b:=63) sp17883 sp17946))))) (joinSmall (lo:=18009) (a:=1000) (b:=1001) (joinSmall (lo:=18009) (a:=500) (b:=500) (joinSmall (lo:=18009) (a:=250) (b:=250) (joinSmall (lo:=18009) (a:=125) (b:=125) (joinSmall (lo:=18009) (a:=62) (b:=63) sp18009 sp18071) (joinSmall (lo:=18134) (a:=62) (b:=63) sp18134 sp18196)) (joinSmall (lo:=18259) (a:=125) (b:=125) (joinSmall (lo:=18259) (a:=62) (b:=63) sp18259 sp18321) (joinSmall (lo:=18384) (a:=62) (b:=63) sp18384 sp18446))) (joinSmall (lo:=18509) (a:=250) (b:=250) (joinSmall (lo:=18509) (a:=125) (b:=125) (joinSmall (lo:=18509) (a:=62) (b:=63) sp18509 sp18571) (joinSmall (lo:=18634) (a:=62) (b:=63) sp18634 sp18696)) (joinSmall (lo:=18759) (a:=125) (b:=125) (joinSmall (lo:=18759) (a:=62) (b:=63) sp18759 sp18821) (joinSmall (lo:=18884) (a:=62) (b:=63) sp18884 sp18946)))) (joinSmall (lo:=19009) (a:=500) (b:=501) (joinSmall (lo:=19009) (a:=250) (b:=250) (joinSmall (lo:=19009) (a:=125) (b:=125) (joinSmall (lo:=19009) (a:=62) (b:=63) sp19009 sp19071) (joinSmall (lo:=19134) (a:=62) (b:=63) sp19134 sp19196)) (joinSmall (lo:=19259) (a:=125) (b:=125) (joinSmall (lo:=19259) (a:=62) (b:=63) sp19259 sp19321) (joinSmall (lo:=19384) (a:=62) (b:=63) sp19384 sp19446))) (joinSmall (lo:=19509) (a:=250) (b:=251) (joinSmall (lo:=19509) (a:=125) (b:=125) (joinSmall (lo:=19509) (a:=62) (b:=63) sp19509 sp19571) (joinSmall (lo:=19634) (a:=62) (b:=63) sp19634 sp19696)) (joinSmall (lo:=19759) (a:=125) (b:=126) (joinSmall (lo:=19759) (a:=62) (b:=63) sp19759 sp19821) (joinSmall (lo:=19884) (a:=63) (b:=63) sp19884 sp19947)))))) (joinSmall (lo:=20010) (a:=2001) (b:=2001) (joinSmall (lo:=20010) (a:=1000) (b:=1001) (joinSmall (lo:=20010) (a:=500) (b:=500) (joinSmall (lo:=20010) (a:=250) (b:=250) (joinSmall (lo:=20010) (a:=125) (b:=125) (joinSmall (lo:=20010) (a:=62) (b:=63) sp20010 sp20072) (joinSmall (lo:=20135) (a:=62) (b:=63) sp20135 sp20197)) (joinSmall (lo:=20260) (a:=125) (b:=125) (joinSmall (lo:=20260) (a:=62) (b:=63) sp20260 sp20322) (joinSmall (lo:=20385) (a:=62) (b:=63) sp20385 sp20447))) (joinSmall (lo:=20510) (a:=250) (b:=250) (joinSmall (lo:=20510) (a:=125) (b:=125) (joinSmall (lo:=20510) (a:=62) (b:=63) sp20510 sp20572) (joinSmall (lo:=20635) (a:=62) (b:=63) sp20635 sp20697)) (joinSmall (lo:=20760) (a:=125) (b:=125) (joinSmall (lo:=20760) (a:=62) (b:=63) sp20760 sp20822) (joinSmall (lo:=20885) (a:=62) (b:=63) sp20885 sp20947)))) (joinSmall (lo:=21010) (a:=500) (b:=501) (joinSmall (lo:=21010) (a:=250) (b:=250) (joinSmall (lo:=21010) (a:=125) (b:=125) (joinSmall (lo:=21010) (a:=62) (b:=63) sp21010 sp21072) (joinSmall (lo:=21135) (a:=62) (b:=63) sp21135 sp21197)) (joinSmall (lo:=21260) (a:=125) (b:=125) (joinSmall (lo:=21260) (a:=62) (b:=63) sp21260 sp21322) (joinSmall (lo:=21385) (a:=62) (b:=63) sp21385 sp21447))) (joinSmall (lo:=21510) (a:=250) (b:=251) (joinSmall (lo:=21510) (a:=125) (b:=125) (joinSmall (lo:=21510) (a:=62) (b:=63) sp21510 sp21572) (joinSmall (lo:=21635) (a:=62) (b:=63) sp21635 sp21697)) (joinSmall (lo:=21760) (a:=125) (b:=126) (joinSmall (lo:=21760) (a:=62) (b:=63) sp21760 sp21822) (joinSmall (lo:=21885) (a:=63) (b:=63) sp21885 sp21948))))) (joinSmall (lo:=22011) (a:=1000) (b:=1001) (joinSmall (lo:=22011) (a:=500) (b:=500) (joinSmall (lo:=22011) (a:=250) (b:=250) (joinSmall (lo:=22011) (a:=125) (b:=125) (joinSmall (lo:=22011) (a:=62) (b:=63) sp22011 sp22073) (joinSmall (lo:=22136) (a:=62) (b:=63) sp22136 sp22198)) (joinSmall (lo:=22261) (a:=125) (b:=125) (joinSmall (lo:=22261) (a:=62) (b:=63) sp22261 sp22323) (joinSmall (lo:=22386) (a:=62) (b:=63) sp22386 sp22448))) (joinSmall (lo:=22511) (a:=250) (b:=250) (joinSmall (lo:=22511) (a:=125) (b:=125) (joinSmall (lo:=22511) (a:=62) (b:=63) sp22511 sp22573) (joinSmall (lo:=22636) (a:=62) (b:=63) sp22636 sp22698)) (joinSmall (lo:=22761) (a:=125) (b:=125) (joinSmall (lo:=22761) (a:=62) (b:=63) sp22761 sp22823) (joinSmall (lo:=22886) (a:=62) (b:=63) sp22886 sp22948)))) (joinSmall (lo:=23011) (a:=500) (b:=501) (joinSmall (lo:=23011) (a:=250) (b:=250) (joinSmall (lo:=23011) (a:=125) (b:=125) (joinSmall (lo:=23011) (a:=62) (b:=63) sp23011 sp23073) (joinSmall (lo:=23136) (a:=62) (b:=63) sp23136 sp23198)) (joinSmall (lo:=23261) (a:=125) (b:=125) (joinSmall (lo:=23261) (a:=62) (b:=63) sp23261 sp23323) (joinSmall (lo:=23386) (a:=62) (b:=63) sp23386 sp23448))) (joinSmall (lo:=23511) (a:=250) (b:=251) (joinSmall (lo:=23511) (a:=125) (b:=125) (joinSmall (lo:=23511) (a:=62) (b:=63) sp23511 sp23573) (joinSmall (lo:=23636) (a:=62) (b:=63) sp23636 sp23698)) (joinSmall (lo:=23761) (a:=125) (b:=126) (joinSmall (lo:=23761) (a:=62) (b:=63) sp23761 sp23823) (joinSmall (lo:=23886) (a:=63) (b:=63) sp23886 sp23949))))))) (joinSmall (lo:=24012) (a:=4002) (b:=4002) (joinSmall (lo:=24012) (a:=2001) (b:=2001) (joinSmall (lo:=24012) (a:=1000) (b:=1001) (joinSmall (lo:=24012) (a:=500) (b:=500) (joinSmall (lo:=24012) (a:=250) (b:=250) (joinSmall (lo:=24012) (a:=125) (b:=125) (joinSmall (lo:=24012) (a:=62) (b:=63) sp24012 sp24074) (joinSmall (lo:=24137) (a:=62) (b:=63) sp24137 sp24199)) (joinSmall (lo:=24262) (a:=125) (b:=125) (joinSmall (lo:=24262) (a:=62) (b:=63) sp24262 sp24324) (joinSmall (lo:=24387) (a:=62) (b:=63) sp24387 sp24449))) (joinSmall (lo:=24512) (a:=250) (b:=250) (joinSmall (lo:=24512) (a:=125) (b:=125) (joinSmall (lo:=24512) (a:=62) (b:=63) sp24512 sp24574) (joinSmall (lo:=24637) (a:=62) (b:=63) sp24637 sp24699)) (joinSmall (lo:=24762) (a:=125) (b:=125) (joinSmall (lo:=24762) (a:=62) (b:=63) sp24762 sp24824) (joinSmall (lo:=24887) (a:=62) (b:=63) sp24887 sp24949)))) (joinSmall (lo:=25012) (a:=500) (b:=501) (joinSmall (lo:=25012) (a:=250) (b:=250) (joinSmall (lo:=25012) (a:=125) (b:=125) (joinSmall (lo:=25012) (a:=62) (b:=63) sp25012 sp25074) (joinSmall (lo:=25137) (a:=62) (b:=63) sp25137 sp25199)) (joinSmall (lo:=25262) (a:=125) (b:=125) (joinSmall (lo:=25262) (a:=62) (b:=63) sp25262 sp25324) (joinSmall (lo:=25387) (a:=62) (b:=63) sp25387 sp25449))) (joinSmall (lo:=25512) (a:=250) (b:=251) (joinSmall (lo:=25512) (a:=125) (b:=125) (joinSmall (lo:=25512) (a:=62) (b:=63) sp25512 sp25574) (joinSmall (lo:=25637) (a:=62) (b:=63) sp25637 sp25699)) (joinSmall (lo:=25762) (a:=125) (b:=126) (joinSmall (lo:=25762) (a:=62) (b:=63) sp25762 sp25824) (joinSmall (lo:=25887) (a:=63) (b:=63) sp25887 sp25950))))) (joinSmall (lo:=26013) (a:=1000) (b:=1001) (joinSmall (lo:=26013) (a:=500) (b:=500) (joinSmall (lo:=26013) (a:=250) (b:=250) (joinSmall (lo:=26013) (a:=125) (b:=125) (joinSmall (lo:=26013) (a:=62) (b:=63) sp26013 sp26075) (joinSmall (lo:=26138) (a:=62) (b:=63) sp26138 sp26200)) (joinSmall (lo:=26263) (a:=125) (b:=125) (joinSmall (lo:=26263) (a:=62) (b:=63) sp26263 sp26325) (joinSmall (lo:=26388) (a:=62) (b:=63) sp26388 sp26450))) (joinSmall (lo:=26513) (a:=250) (b:=250) (joinSmall (lo:=26513) (a:=125) (b:=125) (joinSmall (lo:=26513) (a:=62) (b:=63) sp26513 sp26575) (joinSmall (lo:=26638) (a:=62) (b:=63) sp26638 sp26700)) (joinSmall (lo:=26763) (a:=125) (b:=125) (joinSmall (lo:=26763) (a:=62) (b:=63) sp26763 sp26825) (joinSmall (lo:=26888) (a:=62) (b:=63) sp26888 sp26950)))) (joinSmall (lo:=27013) (a:=500) (b:=501) (joinSmall (lo:=27013) (a:=250) (b:=250) (joinSmall (lo:=27013) (a:=125) (b:=125) (joinSmall (lo:=27013) (a:=62) (b:=63) sp27013 sp27075) (joinSmall (lo:=27138) (a:=62) (b:=63) sp27138 sp27200)) (joinSmall (lo:=27263) (a:=125) (b:=125) (joinSmall (lo:=27263) (a:=62) (b:=63) sp27263 sp27325) (joinSmall (lo:=27388) (a:=62) (b:=63) sp27388 sp27450))) (joinSmall (lo:=27513) (a:=250) (b:=251) (joinSmall (lo:=27513) (a:=125) (b:=125) (joinSmall (lo:=27513) (a:=62) (b:=63) sp27513 sp27575) (joinSmall (lo:=27638) (a:=62) (b:=63) sp27638 sp27700)) (joinSmall (lo:=27763) (a:=125) (b:=126) (joinSmall (lo:=27763) (a:=62) (b:=63) sp27763 sp27825) (joinSmall (lo:=27888) (a:=63) (b:=63) sp27888 sp27951)))))) (joinSmall (lo:=28014) (a:=2001) (b:=2001) (joinSmall (lo:=28014) (a:=1000) (b:=1001) (joinSmall (lo:=28014) (a:=500) (b:=500) (joinSmall (lo:=28014) (a:=250) (b:=250) (joinSmall (lo:=28014) (a:=125) (b:=125) (joinSmall (lo:=28014) (a:=62) (b:=63) sp28014 sp28076) (joinSmall (lo:=28139) (a:=62) (b:=63) sp28139 sp28201)) (joinSmall (lo:=28264) (a:=125) (b:=125) (joinSmall (lo:=28264) (a:=62) (b:=63) sp28264 sp28326) (joinSmall (lo:=28389) (a:=62) (b:=63) sp28389 sp28451))) (joinSmall (lo:=28514) (a:=250) (b:=250) (joinSmall (lo:=28514) (a:=125) (b:=125) (joinSmall (lo:=28514) (a:=62) (b:=63) sp28514 sp28576) (joinSmall (lo:=28639) (a:=62) (b:=63) sp28639 sp28701)) (joinSmall (lo:=28764) (a:=125) (b:=125) (joinSmall (lo:=28764) (a:=62) (b:=63) sp28764 sp28826) (joinSmall (lo:=28889) (a:=62) (b:=63) sp28889 sp28951)))) (joinSmall (lo:=29014) (a:=500) (b:=501) (joinSmall (lo:=29014) (a:=250) (b:=250) (joinSmall (lo:=29014) (a:=125) (b:=125) (joinSmall (lo:=29014) (a:=62) (b:=63) sp29014 sp29076) (joinSmall (lo:=29139) (a:=62) (b:=63) sp29139 sp29201)) (joinSmall (lo:=29264) (a:=125) (b:=125) (joinSmall (lo:=29264) (a:=62) (b:=63) sp29264 sp29326) (joinSmall (lo:=29389) (a:=62) (b:=63) sp29389 sp29451))) (joinSmall (lo:=29514) (a:=250) (b:=251) (joinSmall (lo:=29514) (a:=125) (b:=125) (joinSmall (lo:=29514) (a:=62) (b:=63) sp29514 sp29576) (joinSmall (lo:=29639) (a:=62) (b:=63) sp29639 sp29701)) (joinSmall (lo:=29764) (a:=125) (b:=126) (joinSmall (lo:=29764) (a:=62) (b:=63) sp29764 sp29826) (joinSmall (lo:=29889) (a:=63) (b:=63) sp29889 sp29952))))) (joinSmall (lo:=30015) (a:=1000) (b:=1001) (joinSmall (lo:=30015) (a:=500) (b:=500) (joinSmall (lo:=30015) (a:=250) (b:=250) (joinSmall (lo:=30015) (a:=125) (b:=125) (joinSmall (lo:=30015) (a:=62) (b:=63) sp30015 sp30077) (joinSmall (lo:=30140) (a:=62) (b:=63) sp30140 sp30202)) (joinSmall (lo:=30265) (a:=125) (b:=125) (joinSmall (lo:=30265) (a:=62) (b:=63) sp30265 sp30327) (joinSmall (lo:=30390) (a:=62) (b:=63) sp30390 sp30452))) (joinSmall (lo:=30515) (a:=250) (b:=250) (joinSmall (lo:=30515) (a:=125) (b:=125) (joinSmall (lo:=30515) (a:=62) (b:=63) sp30515 sp30577) (joinSmall (lo:=30640) (a:=62) (b:=63) sp30640 sp30702)) (joinSmall (lo:=30765) (a:=125) (b:=125) (joinSmall (lo:=30765) (a:=62) (b:=63) sp30765 sp30827) (joinSmall (lo:=30890) (a:=62) (b:=63) sp30890 sp30952)))) (joinSmall (lo:=31015) (a:=500) (b:=501) (joinSmall (lo:=31015) (a:=250) (b:=250) (joinSmall (lo:=31015) (a:=125) (b:=125) (joinSmall (lo:=31015) (a:=62) (b:=63) sp31015 sp31077) (joinSmall (lo:=31140) (a:=62) (b:=63) sp31140 sp31202)) (joinSmall (lo:=31265) (a:=125) (b:=125) (joinSmall (lo:=31265) (a:=62) (b:=63) sp31265 sp31327) (joinSmall (lo:=31390) (a:=62) (b:=63) sp31390 sp31452))) (joinSmall (lo:=31515) (a:=250) (b:=251) (joinSmall (lo:=31515) (a:=125) (b:=125) (joinSmall (lo:=31515) (a:=62) (b:=63) sp31515 sp31577) (joinSmall (lo:=31640) (a:=62) (b:=63) sp31640 sp31702)) (joinSmall (lo:=31765) (a:=125) (b:=126) (joinSmall (lo:=31765) (a:=62) (b:=63) sp31765 sp31827) (joinSmall (lo:=31890) (a:=63) (b:=63) sp31890 sp31953)))))))))
  have good : (List.range 32016).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 1025000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 32015 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 32015 := by
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


private def packet (i : ℕ) : ℕ := (if i < 261 then (if i < 130 then (if i < 65 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else 0))) else (if i < 12 then (if i < 10 then (if i < 9 then 0 else 0) else (if i < 11 then 0 else 0)) else (if i < 14 then (if i < 13 then 0 else 0) else (if i < 15 then 0 else 0)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0 else 0) else (if i < 19 then 0 else 0)) else (if i < 22 then (if i < 21 then 0 else 0) else (if i < 23 then 0 else 0))) else (if i < 28 then (if i < 26 then (if i < 25 then 0 else 0) else (if i < 27 then 0 else 0)) else (if i < 30 then (if i < 29 then 0 else 0) else (if i < 31 then 0 else 0))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0 else 0) else (if i < 35 then 0 else 0)) else (if i < 38 then (if i < 37 then 0 else 0) else (if i < 39 then 0 else 0))) else (if i < 44 then (if i < 42 then (if i < 41 then 0 else 0) else (if i < 43 then 0 else 0)) else (if i < 46 then (if i < 45 then 0 else 0) else (if i < 47 then 0 else 0)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0 else 0) else (if i < 51 then 0 else 0)) else (if i < 54 then (if i < 53 then 0 else 0) else (if i < 55 then 0 else 0))) else (if i < 60 then (if i < 58 then (if i < 57 then 0 else 0) else (if i < 59 then 0 else 0)) else (if i < 62 then (if i < 61 then 0 else 0) else (if i < 63 then 0 else (if i < 64 then 0 else 0))))))) else (if i < 97 then (if i < 81 then (if i < 73 then (if i < 69 then (if i < 67 then (if i < 66 then 0 else 0) else (if i < 68 then 0 else 0)) else (if i < 71 then (if i < 70 then 0 else 0) else (if i < 72 then 0 else 0))) else (if i < 77 then (if i < 75 then (if i < 74 then 0 else 0) else (if i < 76 then 0 else 0)) else (if i < 79 then (if i < 78 then 0 else 0) else (if i < 80 then 0 else 0)))) else (if i < 89 then (if i < 85 then (if i < 83 then (if i < 82 then 0 else 0) else (if i < 84 then 0 else 0)) else (if i < 87 then (if i < 86 then 0 else 0) else (if i < 88 then 0 else 0))) else (if i < 93 then (if i < 91 then (if i < 90 then 0 else 0) else (if i < 92 then 0 else 0)) else (if i < 95 then (if i < 94 then 0 else 0) else (if i < 96 then 0 else 0))))) else (if i < 113 then (if i < 105 then (if i < 101 then (if i < 99 then (if i < 98 then 0 else 0) else (if i < 100 then 0 else 0)) else (if i < 103 then (if i < 102 then 0 else 0) else (if i < 104 then 0 else 0))) else (if i < 109 then (if i < 107 then (if i < 106 then 0 else 0) else (if i < 108 then 0 else 0)) else (if i < 111 then (if i < 110 then 0 else 0) else (if i < 112 then 0 else 0)))) else (if i < 121 then (if i < 117 then (if i < 115 then (if i < 114 then 0 else 0) else (if i < 116 then 0 else 0)) else (if i < 119 then (if i < 118 then 0 else 0) else (if i < 120 then 0 else 0))) else (if i < 125 then (if i < 123 then (if i < 122 then 0 else 0) else (if i < 124 then 0 else 0)) else (if i < 127 then (if i < 126 then 0 else 0) else (if i < 128 then 0 else (if i < 129 then 0 else 0)))))))) else (if i < 195 then (if i < 162 then (if i < 146 then (if i < 138 then (if i < 134 then (if i < 132 then (if i < 131 then 0 else 0) else (if i < 133 then 0 else 0)) else (if i < 136 then (if i < 135 then 0 else 0) else (if i < 137 then 0 else 0))) else (if i < 142 then (if i < 140 then (if i < 139 then 0 else 0) else (if i < 141 then 0 else 0)) else (if i < 144 then (if i < 143 then 0 else 0) else (if i < 145 then 0 else 0)))) else (if i < 154 then (if i < 150 then (if i < 148 then (if i < 147 then 0 else 0) else (if i < 149 then 0 else 0)) else (if i < 152 then (if i < 151 then 0 else 0) else (if i < 153 then 0 else 0))) else (if i < 158 then (if i < 156 then (if i < 155 then 0 else 0) else (if i < 157 then 0 else 0)) else (if i < 160 then (if i < 159 then 0 else 0) else (if i < 161 then 0 else 0))))) else (if i < 178 then (if i < 170 then (if i < 166 then (if i < 164 then (if i < 163 then 0 else 0) else (if i < 165 then 0 else 0)) else (if i < 168 then (if i < 167 then 0 else 0) else (if i < 169 then 0 else 0))) else (if i < 174 then (if i < 172 then (if i < 171 then 0 else 0) else (if i < 173 then 0 else 0)) else (if i < 176 then (if i < 175 then 0 else 0) else (if i < 177 then 0 else 0)))) else (if i < 186 then (if i < 182 then (if i < 180 then (if i < 179 then 0 else 0) else (if i < 181 then 0 else 0)) else (if i < 184 then (if i < 183 then 0 else 0) else (if i < 185 then 0 else 0))) else (if i < 190 then (if i < 188 then (if i < 187 then 0 else 0) else (if i < 189 then 0 else 0)) else (if i < 192 then (if i < 191 then 0 else 0) else (if i < 193 then 0 else (if i < 194 then 0 else 0))))))) else (if i < 228 then (if i < 211 then (if i < 203 then (if i < 199 then (if i < 197 then (if i < 196 then 0 else 0) else (if i < 198 then 0 else 0)) else (if i < 201 then (if i < 200 then 0 else 0) else (if i < 202 then 0 else 0))) else (if i < 207 then (if i < 205 then (if i < 204 then 0 else 0) else (if i < 206 then 0 else 0)) else (if i < 209 then (if i < 208 then 0 else 0) else (if i < 210 then 0 else 0)))) else (if i < 219 then (if i < 215 then (if i < 213 then (if i < 212 then 0 else 0) else (if i < 214 then 0 else 0)) else (if i < 217 then (if i < 216 then 0 else 0) else (if i < 218 then 0 else 0))) else (if i < 223 then (if i < 221 then (if i < 220 then 0 else 0) else (if i < 222 then 0 else 0)) else (if i < 225 then (if i < 224 then 0 else 0) else (if i < 226 then 0 else (if i < 227 then 0 else 0)))))) else (if i < 244 then (if i < 236 then (if i < 232 then (if i < 230 then (if i < 229 then 0 else 0) else (if i < 231 then 0 else 0)) else (if i < 234 then (if i < 233 then 0 else 0) else (if i < 235 then 0 else 0))) else (if i < 240 then (if i < 238 then (if i < 237 then 0 else 0) else (if i < 239 then 0 else 0)) else (if i < 242 then (if i < 241 then 0 else 0) else (if i < 243 then 0 else 0)))) else (if i < 252 then (if i < 248 then (if i < 246 then (if i < 245 then 0 else 0) else (if i < 247 then 0 else 0)) else (if i < 250 then (if i < 249 then 0 else 0) else (if i < 251 then 0 else 0))) else (if i < 256 then (if i < 254 then (if i < 253 then 0 else 0) else (if i < 255 then 0 else 0)) else (if i < 258 then (if i < 257 then 0 else 0) else (if i < 259 then 0 else (if i < 260 then 0 else 0))))))))) else (if i < 391 then (if i < 326 then (if i < 293 then (if i < 277 then (if i < 269 then (if i < 265 then (if i < 263 then (if i < 262 then 0 else 0) else (if i < 264 then 0 else 0)) else (if i < 267 then (if i < 266 then 0 else 0) else (if i < 268 then 0 else 0))) else (if i < 273 then (if i < 271 then (if i < 270 then 0 else 0) else (if i < 272 then 0 else 0)) else (if i < 275 then (if i < 274 then 0 else 0) else (if i < 276 then 0 else 0)))) else (if i < 285 then (if i < 281 then (if i < 279 then (if i < 278 then 0 else 0) else (if i < 280 then 0 else 0)) else (if i < 283 then (if i < 282 then 0 else 0) else (if i < 284 then 0 else 0))) else (if i < 289 then (if i < 287 then (if i < 286 then 0 else 0) else (if i < 288 then 0 else 0)) else (if i < 291 then (if i < 290 then 0 else 0) else (if i < 292 then 0 else 0))))) else (if i < 309 then (if i < 301 then (if i < 297 then (if i < 295 then (if i < 294 then 0 else 0) else (if i < 296 then 0 else 0)) else (if i < 299 then (if i < 298 then 0 else 0) else (if i < 300 then 0 else 0))) else (if i < 305 then (if i < 303 then (if i < 302 then 0 else 0) else (if i < 304 then 0 else 0)) else (if i < 307 then (if i < 306 then 0 else 0) else (if i < 308 then 0 else 0)))) else (if i < 317 then (if i < 313 then (if i < 311 then (if i < 310 then 0 else 0) else (if i < 312 then 0 else 0)) else (if i < 315 then (if i < 314 then 0 else 0) else (if i < 316 then 0 else 0))) else (if i < 321 then (if i < 319 then (if i < 318 then 0 else 0) else (if i < 320 then 0 else 0)) else (if i < 323 then (if i < 322 then 0 else 0) else (if i < 324 then 0 else (if i < 325 then 0 else 0))))))) else (if i < 358 then (if i < 342 then (if i < 334 then (if i < 330 then (if i < 328 then (if i < 327 then 0 else 0) else (if i < 329 then 0 else 0)) else (if i < 332 then (if i < 331 then 0 else 0) else (if i < 333 then 0 else 0))) else (if i < 338 then (if i < 336 then (if i < 335 then 0 else 0) else (if i < 337 then 0 else 0)) else (if i < 340 then (if i < 339 then 0 else 0) else (if i < 341 then 0 else 0)))) else (if i < 350 then (if i < 346 then (if i < 344 then (if i < 343 then 0 else 0) else (if i < 345 then 0 else 0)) else (if i < 348 then (if i < 347 then 0 else 0) else (if i < 349 then 0 else 0))) else (if i < 354 then (if i < 352 then (if i < 351 then 0 else 0) else (if i < 353 then 0 else 0)) else (if i < 356 then (if i < 355 then 0 else 0) else (if i < 357 then 0 else 0))))) else (if i < 374 then (if i < 366 then (if i < 362 then (if i < 360 then (if i < 359 then 0 else 0) else (if i < 361 then 0 else 0)) else (if i < 364 then (if i < 363 then 0 else 0) else (if i < 365 then 0 else 0))) else (if i < 370 then (if i < 368 then (if i < 367 then 0 else 0) else (if i < 369 then 0 else 0)) else (if i < 372 then (if i < 371 then 0 else 0) else (if i < 373 then 0 else 0)))) else (if i < 382 then (if i < 378 then (if i < 376 then (if i < 375 then 0 else 0) else (if i < 377 then 0 else 0)) else (if i < 380 then (if i < 379 then 0 else 0) else (if i < 381 then 0 else 0))) else (if i < 386 then (if i < 384 then (if i < 383 then 0 else 0) else (if i < 385 then 0 else 0)) else (if i < 388 then (if i < 387 then 0 else 0) else (if i < 389 then 0 else (if i < 390 then 0 else 0)))))))) else (if i < 456 then (if i < 423 then (if i < 407 then (if i < 399 then (if i < 395 then (if i < 393 then (if i < 392 then 0 else 0) else (if i < 394 then 0 else 0)) else (if i < 397 then (if i < 396 then 0 else 0) else (if i < 398 then 0 else 0))) else (if i < 403 then (if i < 401 then (if i < 400 then 0 else 0) else (if i < 402 then 0 else 0)) else (if i < 405 then (if i < 404 then 0 else 0) else (if i < 406 then 0 else 0)))) else (if i < 415 then (if i < 411 then (if i < 409 then (if i < 408 then 0 else 0) else (if i < 410 then 0 else 0)) else (if i < 413 then (if i < 412 then 0 else 0) else (if i < 414 then 0 else 0))) else (if i < 419 then (if i < 417 then (if i < 416 then 0 else 0) else (if i < 418 then 0 else 0)) else (if i < 421 then (if i < 420 then 0 else 0) else (if i < 422 then 0 else 0))))) else (if i < 439 then (if i < 431 then (if i < 427 then (if i < 425 then (if i < 424 then 0 else 0) else (if i < 426 then 0 else 0)) else (if i < 429 then (if i < 428 then 0 else 0) else (if i < 430 then 0 else 0))) else (if i < 435 then (if i < 433 then (if i < 432 then 0 else 0) else (if i < 434 then 0 else 0)) else (if i < 437 then (if i < 436 then 0 else 0) else (if i < 438 then 0 else 0)))) else (if i < 447 then (if i < 443 then (if i < 441 then (if i < 440 then 0 else 0) else (if i < 442 then 0 else 0)) else (if i < 445 then (if i < 444 then 0 else 0) else (if i < 446 then 0 else 0))) else (if i < 451 then (if i < 449 then (if i < 448 then 0 else 0) else (if i < 450 then 0 else 0)) else (if i < 453 then (if i < 452 then 0 else 0) else (if i < 454 then 0 else (if i < 455 then 0 else 0))))))) else (if i < 489 then (if i < 472 then (if i < 464 then (if i < 460 then (if i < 458 then (if i < 457 then 0 else 0) else (if i < 459 then 0 else 0)) else (if i < 462 then (if i < 461 then 0 else 0) else (if i < 463 then 0 else 0))) else (if i < 468 then (if i < 466 then (if i < 465 then 0 else 0) else (if i < 467 then 0 else 0)) else (if i < 470 then (if i < 469 then 0 else 0) else (if i < 471 then 0 else 0)))) else (if i < 480 then (if i < 476 then (if i < 474 then (if i < 473 then 0 else 0) else (if i < 475 then 0 else 0)) else (if i < 478 then (if i < 477 then 0 else 0) else (if i < 479 then 0 else 0))) else (if i < 484 then (if i < 482 then (if i < 481 then 0 else 0) else (if i < 483 then 0 else 0)) else (if i < 486 then (if i < 485 then 0 else 0) else (if i < 487 then 0 else (if i < 488 then 0 else 0)))))) else (if i < 505 then (if i < 497 then (if i < 493 then (if i < 491 then (if i < 490 then 0 else 0) else (if i < 492 then 0 else 0)) else (if i < 495 then (if i < 494 then 0 else 0) else (if i < 496 then 0 else 0))) else (if i < 501 then (if i < 499 then (if i < 498 then 0 else 0) else (if i < 500 then 0 else 0)) else (if i < 503 then (if i < 502 then 0 else 0) else (if i < 504 then 0 else 0)))) else (if i < 513 then (if i < 509 then (if i < 507 then (if i < 506 then 0 else 0) else (if i < 508 then 0 else 0x308635f2a493b09064241e48dc063c2c9137087438a17008d02e00c600003085dac2b114109304361f00e406702dc141087038e16a08502b80ae000030857d02ba14689824612060ec46c82f915089343d217d08d83140c2000030851d42c814c89ae47520b8ee86c430314c08d839c17308b02f40ac00003084c1c2b4140c9724581fd0eb86a22f314588e83b8185096031c0c6000030846632ac93ec9364441f58e4464c2d213c889838015d08502c00a0000030840c12a613b49284311ec8dd46322c3138884c37415b08282b80a800003083aee2bf145c9724541fb8e6c67e2e113e089838a16b08882ec0c00000308353a2ae940495a4521f58e4866e2e214588f03ae17d08f82fc0bc00003082f952a413b49244351f20e246602ce13b087838c16808882c80a2000030829c92b814489604601fe8e706782e4141887839a17008e02fc0b8000030823f02bd94609744652070ec46b2309155094c3e219409183040ae00003081e492ab93cc92e4381eb8dac6282b912f080c35c14f07c82700a00000308189c2ab940895644e1f60e3c6602d7140087039e17b08e830c0da000030812c22bf94889924602000e9868e2f214708a438a15f08682f00c000003080cd42c594809784592048ea86a42e114308a838e17408d83000c20000308071c2aa942495445a1fc0e3c6662d8140889039a17809002f80b4000030801472b0943496645f1ff0e5c6842e214608bc39617808f82d80c40000307fba72a793a090c42b1ea8e0c64e2bf134082036c16008482c00be0000307f5d72b8146c9824682060e9c67e2dd141087437e16908c02a80b80000307f00d2b3946097e4621ff0e7467a2e314308cc3a018408c03040ca0000307ea422bc146c9884632058ec46b22f714d88c43aa16a08882f40c00000307e46e2bb144896a4581fb8e586862e814488c03b017508b02d00b40000307deb12ab93e095444d1f58e586762ec14488ac39e17108502e40c60000307d8eb2b6141c97445d2008e8467e2e714588ac3b418309003000be0000307d3222bc143c95e44d1fa0e3c6602d914408c83b417a08e02ec0bc0000307cd402cb94c89a447a20d8ec06922f214909003c018509a03240cc0000307c7802b3145895c4542018ea46a62f014a890c3c818509303180cc0000307c1b42b3144c94a4451f40e2c6502d113a884c38617209082d80c00000307bbdd2bc94649864632040e886842df14488cc3b217409003100b80000307b6392a193a49224361ef8de86402c7139888838816608782c00a80000307b0902a2139490c42f1ea0e106582d0138885c37215e08602a00a40000307aae02aa93ec93c4421f88e6067e2e314008883a017608b82f80ca0000307a5272aa13f093e44b1f30e146682d513b087c38a17308a02e80c200003079f6d2af13f89484481f38dec6442c0131882035015108102a40aa000030799bf2a513d092443b1f28e3c6822e613f088837e16508302c40b0000030793ee2bd947096844f1f88e5866c2d2136888038a16c08902dc0ac00003078e0f2ba945495644b1fb8e9c6922e514688d839e17508a02e80ba0000307889a28d13088e84151db8d9061c2bf132083836015207d02a00a8000030782d12b7943095844d1f90e1c66c2d613f08a438a16c08982f00b800003077d312a3139c9324431ef0e286762d613d085036a16308402c40a40000307774c2c5948c9864662030eb86982e314988cc3b417e09103180be000030771862b4941c94e44b1f58e406562d013f089c38c17208a02f80c600003076bb72b794509784642040ed46d430e15b891c3cc18c098832c0da000030765d72be147897645b2000e9469a2f014808a439a17208b82d80b8000030760122b8145c98646f20a8ec86ba2f814708c83bc180096835c0cc00003075a462b7944c96c4622018ea869c2ec14888fc3b217e08e03000c2000030754812bd94789964652038ed46ac2ef14c89243c018108a82f40c600003074ebb2b514149644581fe0e7069e2e914288803ae17408f83000b6000030748eb2b794709704672080ec86982f414188a839616f08602e40b60000307432a2b2142096045c2000e786862e514088a039016f08682bc09e00003073d6c2b113e89504421ef8e106562c8138088437c17008a02cc0bc000030737b12ae943096a45c2000e5c66c2d813c886438a16708602c00b0000030731df2bb145c96a4531fd8e706822e914788d03a817c090031c0c600003072c242b614149484521fa0e5c67e2e514508bc39817508d02e00b00000307267b2a213889044211ea8dec63c2cd13b087c36c161084829c0ac000030720c42ab93f494c44b1f98e386742e714608b83ae17508d03000d800003071ac92c814d89ac47020c0f1c6b62fd15188fc3be17c08d03340da000030714f12bd948c98e46c20d8eec6a42e114708cc39e16d08a02d40cc00003070f482a293b49344391f20e006642d514088c43be18608f02f40c4000030709762bb947897646a2040ea46822e0145888037e162084029c09c0000307039d2ba948097a4591ff0e586762e314408ac3aa17708d02d40c60000306fde02b1142c9524481f98e606742d913b0880396167084829809c0000306f81d2b5940c94e4441f30e486682d714188d439e17208702c00a6000)) else (if i < 511 then (if i < 510 then 0x309d55e2d3952c9c848e2190f386ec30914f890c3c817c094830c0be0000309cfce29893588fa4231e28da86342c213a087839017308e82e40ae0000309ca332a613a492644a1fb8e6468c2e514508c83b418509203040ba0000309c46c2b6944098c45b2038eb06922ea14208a839e16808a82dc0bc0000309be972bc146098846f2050ea46aa2ee145089c38416408502c00aa0000309b8e32ab13dc93643c1f60e6466e2e214388b43a416e08982e40c00000309b3072bf147c9704612050eb06aa2eb14888e43ce17c08f82fc0ba0000309ad182c794f09ba48220f8ef06b82f414988c83a2184093030c0b40000309a7602b1940c9544481fb8e4c67c2dd13c088038c16908802b40960000309a1ab2ab93e09304301ed0e206482cc138086c37e16508702900a400003099c1429e939092643c1ed8e2c65c2d313a085c38416108802e80b40000309964d2b8149496a4561fd8e746a22f014a08c83b017409003140d20000309903b2dc153c9d84872118f006b830415809103bc17f08e03180b600003098ab129693548fc4281e48dc06322c1130086036c16508682bc0a4000030984e42b814549784642040ea46a82f114d08d039a16c08982cc0b200003097f102bc14589684581ff8e9468c2f114c88e03a617308a82e80cc000030979462c094949924702050efc6ae2f314a88b439016b08402d40cc000030973a12a993c49184351ef0e346542cb13b088438c17008702c80aa00003096dca2b8946098a4591fb8e8467c2e414a08c83ac17208d82cc0b6000030967ea2bc94749844632048e9869830215409183b017308902b00b40000309620c2c014b89a647520d8ed46a22f214388a03a617308a03200c400003095c7129d93588fa4311ed0df46402c613a085436816308a02f40ce000030956b92aa940c9564411f48e306622d613f88a439016508982f40d0000030950cc2ca94c099a47d20b8ec86a82f214d08d43c018809403180c400003094b192a793a491c42c1e78dd06342cc136885436616508282a809a0000309456d2aa13cc93243d1f40e0866a2d9142089838e17208782cc0b000003093fb22af942094e4481f28e5867a2e814a88d039016708582cc0b6000030939e02b413ec9384401f58e186562d8138883836c16008602c40b0000030934202b194249764571fd8e806702e214288f03aa17508903080ba00003092e5a2b194289644521fe8e6c6762d713e089c38a16e08a82c00b40000309289b2b0142494e4481f28e606902e8145089c38215c08602e40c8000030922d12b8144896c4642040e9868c2e814b88d03a017208b82e40ca00003091d122bb149099e4672088ec06c430c15809383c218209082ec0c40000309174f2b1941494e4461f50e306662d413e088838e16308282a00ac0000309116d2bf948497645d1fb0e646862ef14788d43c018909202f00c400003090ba22b3143c96a45c2030e9c6942e114008b03a616b08b82d00b8000030905d22b9946897e4682088f1c6da30e15088f83c616c08902f40b6000030900072b8942c9604592030ecc6ba2fd14e08e83bc17d09003200c40000308fa232c6149c9a046d2000e986982f014e88d43c817e09203000d40000308f4492c014549864622068ec06ae2f715409103d018909083140c80000308ee882b794649844591fe0e9868e2e613e88a83a617308b02e40b40000308e8b22bf14889884642028e7466e2e013f889c37816007e02b40aa0000308e30a2a793e093243e1ef8e106502c413a089839017108982d80bc0000308dd252c0946c9824662090eb86a62fd14b89043ae17608d83100aa0000308d7632b6143496e4571f60e6067e2e214a08bc39e17708502b00980000308d1a22b5145896e45a1fd0e5c67c2e414b09243e619809102f80c20000308cc1029c13388f441c1e50dcc64c2d813e887c39217108d03000b20000308c6302c094a09844622080ea46902f714408b83b017e09303000bc0000308c0802a893d89364461f60e2865c2d7143086438815d07a02a80a80000308bab32b814489804631fe0e886842e014288a83ac16808782e80c20000308b4942e095509f04982170f446ca30e153891c3c018609183140c40000308aeef2a393cc9284301ee8df864a2cc13b084838216308602d80ac0000308a9142c214b499c47120e8ed46be30415409243d418009283000d20000308a3372c0149c9a04772088ec46c02ff14c88e83b617508e03000c000003089d4a2c694e89b047a20f8ef06ba30515889083b017508e02d80b4000030897802b594609804642080ee06b62fd14e88dc3bc18208b02f00bc0000308919e2bd947898e45f2070ecc6b62f814b88d03a217608d82e40b200003088bca2bb14a09a04712078e9868e2f614808bc3b018509003200cc0000308861e2ae14189424391ec8e006382ba134086438e16c08702c00ae000030880632af94289504421f58e446702db13b088439017508982c40ac00003087aa52ae93f094444a1f58e406702db14288bc38e16208502c00b4000030874d82b8143096c4581ff8e7067a2db141888838e16908882d40ba00003086edc2d1152c9dc48d2180f046b2300151891c3d819209783440c6000030868ff2c514b89a247b20a0ee06b02fb15109043ce18309283080b6000 else 0x30b48ae2ac93e89584421f18e2c64c2c4135081837016508402c40b8000030b42ba2d015009c24892170f146e2319159895c3ec19409f83440d2000030b3cee2bc947097c4652080ecc6b42f714988c03b018109082f40b0000030b37132c0947898e45f2020ea468a2e613e88b03a417908a82d40a4000030b31572ac94149484521f98e7c67a2dc14008ac3a217208a83080ca000030b2b872c014b09aa47c2098ec06a62f914e88ec3c017808f82f40be000030b25ae2bb946c97645d2040e9c6942ea143889439016808702a40ae000030b1fb52ce14fc9b447620b0edc6ae2fa14f09203d618208d02dc0ac000030b1a172a493a49224341f20e006402bf138085c37e16b087830c0c0000030b14452b7144896846c20a8ebc69c2ef14889003a817108902c00ae000030b0ec4298937c90242a1e58d9c6202bf136082836816008402c00ae000030b08d22cc14ec9b847f20d0f286da30d15189183d218f09603300ba000030b02ee2c294bc99e46d2038eb468a2ee14588c83aa17808c82fc0b4000030afcf52ca94e09bc48120d8ed46a42e914888e43b018008f03080cc000030af7232bd945496c45d2010eb069a2f014888b03b818209103040b4000030af17d2a913e493a43e1ec8dfc6582c713f087439c17108e82f80d0000030aebb32ba147498845f2040e686802e914908e03a617908c82ec0be000030ae5ba2cf95089c447e20b8ef86b22f014988bc3c018109303180dc000030adff62b6140c9444491f78e7c6822ec14588983b0188090830c0ba000030ada6629c93708d841b1e38d986162b912e881836a15c08402f40c2000030ad4ba2a213b492e43c1f10e2c66c2db140887037c16708402bc0ae000030acee62ba94709884611ff0e906962fc14c88b839e17608e82e40d8000030ac91a2b514449584431f78e0c64e2d313a087037615608402bc0b2000030ac3602ae93ec9444531f68e2c6642d714388c439c17b08f03180c0000030abda22b6142497645e2010e486762d3138884c37416107f82e00b6000030ab7cc2bf948099e46b2028e986982f014e89003b217a08d02fc0b4000030ab2182aa942094644f1f78e146582d414008a839617708e02e40c4000030aac642ae93cc9244341ec0e086562d1141089039017c08d82f00ca000030aa66c2cb14e09b847b2108ef06c62fd14d08e83ac17809202e80d4000030aa0a92aa941894e44a1f38e3c66a2e314b08c03a416a08982fc0c8000030a9abf2c994c09a64722098ec46ac2f414708c439c17608802ec0b8000030a94b32d2951c9de4872100f186bc2fc15309383d818a09802f80c4000030a8ed22c0147098645b2030ed06ae2f414b08d43c017e092030c0c8000030a89132b1140c9424451f48e4c6742e614408b83aa16f08582c80a0000030a83452ac13e493443d1f38e1c65a2c912f881836c15f08182bc0a4000030a7d662be14a09b84752080ecc6b82f715008f03c218109303100c4000030a778b2c114809844691fc8ea46922eb143889438c16d08302900aa000030a7207290933c8fc4261e28da461c2b712d080c36015107e02b80a2000030a6c4b2ac13ec93243a1f00e186642e213e089038e16e08a82e00b0000030a66942b013f893443b1f30e3866c2d814008803a417208b02dc0bc000030a60b92c194bc99e47a2128f2c6da30b15688e83be18108d83000c2000030a5ae92b7143096e44b1f90e486682db13c881835e15607d82840b4000030a55062c294ac99e46c2088ec069e2f914c08f83b417e08d02f80be000030a4f3d2ba146897c45c1fa8e7068a2df14508d43b217d09003280c4000030a496f2b7144497845b1fa0e706842e9143888038c16508282d40ba000030a43c42a6139c91242e1e80db862a2cc139085438416308482d40ba000030a3dfd2b494109524451f78e286642dd14708c43a216d08702f40c0000030a386e299939091042f1ef8df064a2cb137884837616f08a82d80c8000030a32812c294a49924672058ea869a2ee14788a439e17408e83080c4000030a2cd52a893f09504371ef8dfc64c2d513a085037a16c08b82e80aa000030a26f12ca94d89ac4802150f0c6e231315a09283ce18308b82e80b6000030a21352a993c492043e1e88e006522d413c886838416b08582bc0b0000030a1b6c2b5142895445a2030e986a830114c88e43aa16b08582c80ae000030a15a62b4144c9804642080eb06822e214288a03a217508802e00ba000030a0fce2bb14689684561fd8e7065c2d814408c43aa17a08f830c0c0000030a09f22c614b49a64662028e9c6782ea14688a437c167088830c0c8000030a04142c314809864672008ea467e2df14508c439e17208f03140ba0000309fe3c2b8945497845f1ff8e946a42fb14e88f43c218108e83140be0000309f8542c2148898846a2048ec069e2fa14d09083c217c08b02ec0d20000309f2962b193f89344451f60e4c6522d314108983a416b09002ec0a60000309ece12b2942096e4541f88e3466c2d213d88b03a2165082829c09c0000309e7242b2941c94c44b2020ec86b02f214a08e83cc18a09603040c80000309e1542b714509604571fd0e786982e314788e43a417408882d00b20000309db5f2cd14e89be4882160f246b22f914a88c038616b08982dc0be000) else (if i < 512 then 0x30cbb012aa93ec92c43e1f28e3067a2dc140089838416708402c40b0000030cb54d2a413c89484491f68e3c65e2cb140889037e15d08082c80ba000030caf962ae93e89464441f60e786882dd141088839a16f08802cc0a4000030ca9df2b014249744501f98e6c6862eb14908bc39a173090030c0be000030ca42e2ab942496a45d1ff0e9c6822db14308b839216808282a80b2000030c9e572c0147098c46c2040ea06962ed14d890c3c417b09283300c8000030c98a12a693c493e43e1ef0e4c66c2e3143088439a16908982ec0bc000030c92d32b814ac99a47020f0ee46b82f214808c039a17e08c82e00b0000030c8d2d2ab93f89604471f38e386922ef14d08f83c418209203200c4000030c87662b894489664521f90e706762d713f88a039616f08b82c40a6000030c81ac2b113f094e4501f88e8468c2e314708d03b817908c83040d6000030c7be12b7944495c4511fd8e306682dd13f089c39c16d08502d4098000030c75fb2c6949c9944681ff8e846a02f115208ec3aa17109083480d0000030c70302b7944897645e2020e7c68c2e714788fc3cc17a09383240cc000030c6a882ae13c891c4391f10e206582ce13a886436a16b08802f80be000030c649b2c914ec9a04812188f4c6dc30214988fc3de18909083180d0000030c5ee62b4941896e45f1fe8e906902e514508e43b417308382e40be000030c59382a813cc93444a1f28e246582d814388ac38a16308382a00b6000030c53802a793d09364461f60e546842ec14a88d83b016f08602e00b2000030c4dbc2b9146c9764601ff8eb46a02e914888e43bc17f08d02fc0b6000030c483129a939490842a1e70dec6442c4136884036e16508a82b40aa000030c42722b093fc9484461f48e5c6682d514488a438616a08882b80ac000030c3c762cc94f89b64832148ef86d230a15309003be18109182e00b2000030c36aa2b9942c95e4612058ebc6aa2f614c08e03aa17b08e030c0d4000030c31012a413bc9324421f98e306762df140886437816708682d40ae000030c2b1d2c194a09824561fb8e446702e014288943aa17708782c00a6000030c253f2c514b098645b1fe0e786882dd14388a03a217308d02f80b8000030c1f9d2a493ec9584542028eb86a82ea14188ac39417208d830c0c8000030c19b32c3149096c45d2010e746762dd14008983a617108d02ec0a0000030c13e22bd145c96e46a1fe0e7469e2f314c88cc3aa18209203100c6000030c0e082c214d09ae46520a8e806862dc13a08943a017a08b82d00b6000030c084f2af940895244c1fe0e806862ea14388bc3a216d08802f00ac000030c028e2b2941093e44a1f50e306702d0137886437015b08402c40a6000030bfcad2c1946098246e2080eb469a2e514789043b817a08a02e00ae000030bf6ec2b2141496e44d1f90e546742dc139886039617908602f80c4000030bf1032c214949824662028eb86a22f314508a037816608402c00ae000030beb1c2c614889924672038eac6982f014b08ec3aa16d08e02ec0c6000030be58d29b13588f84241e30dcc63a2b912e082035615508082a80b2000030bdfb72bf946897645e2018e706522cd139085c38216708482ac0b2000030bd9e52b9945c9864662068eb46982ec14688fc3ce18c08d82f00c8000030bd3d92da15449d648720e8efc6c630615009143ba18809083080cc000030bce182b1943096044e1fd0e7c6742d514108b03b616a08a02e00a6000030bc82e2cd14fc9b847a20e8ef46b02f514888d839a16e08c82e00a8000030bc2532be947499646d20e0ed46b42fc14c88f83a017608e02f00b2000030bbc6a2c994dc9bc4832138f286dc30a14d88e83ae17408902dc0b4000030bb67c2c694c499c46c2050e946922ec14b88e03b018008e031c0ba000030bb0a52bd147497245c1fa0e686762eb14288c83ac17b08c02f80b6000030baae42b5943c93e4461fa0e546722d713b084c37e16208302d80c0000030ba51c2b5143495c44d1f28e3c6642d513c886037a16508602a40a8000030b9f742a713c892642c1ed0dfc6442d413e088038c16d08d02e40cc000030b99922ba145498a45b2068eec6ae2fd14e08cc3ac16f08482c80b6000030b93ca2af941c9604481f48e7867a2e4140089c3a817008602c00b0000030b8e0e2ad13d892443c1f60e346622d513f087439c16a08702d80ca000030b88602a993cc92c4351f08e1c6622d313b887037016c08c82d80bc000030b828a2b7142c97045c2000e8869e2e914708d83ae17408a02dc0b0000030b7ce02aa13ec95644c1fb0e5c6602cd13b888438c16e08982dc0b6000030b77052c414a09804601fe0e706722e414708a039a17208f02f40b4000030b712d2bd94789724622010e706802dc14108a039216c08983080b4000030b6b9d29a936c8f44261e48dac6302bd133084837015b07a029c0b6000030b65c52b9145495c45a1fe8e9867e2d613f08a439e16c08582dc0a0000030b5fdb2c514c89944722068ee46b82fa15009103a618208c82e00a8000030b59e72ca15049d048a2170f4c6fc31415b89443d017f09183000b6000030b54322ac13fc9464491f28e1c66e2dc14188a439a16e08a02d80aa000030b4e672b6143c97444c1f90e986982ec14a08d43b417708c02ec0b0000 else 0x30e2e382bf949498845f2030e9c6b42fb14b08cc38e16a08582d80ae000030e28622b8943095244e1fc0e606822de13d08a839a16608502f40ba000030e22672cd94cc9aa4792120ef06d830514e08ec3b417b08f82dc0b8000030e1cb22b1142c9624592000e946982f514688e03b217308802e00b6000030e17002aa13dc9484411ed0dfc64a2c6131080436816708702d00bc000030e113e2b7945c96e4612028ec86ac2e814488ac3ae17a09183040b6000030e0b672bb147c97c4622008e9467c2e8141889c39416a08e02bc0ae000030e05972bb943096c4531f80e3c6742e1140086436415608602d00ac000030dffdd2a813a89284391f48e3465c2dd14288c03b818509183040bc000030dfa1b2b2141496a45f1fc8e486782e4143888439417d09283340c4000030df44f2b694409604521f90e6c6702e714788ac3ba17e08d82fc0be000030dee7d2b914449664531ff8ea46982e814908bc3bc18109002d80c6000030de8a52b894989a047c20a8ee46bc2f414d08e43b817808e02ec0c8000030de2d62b414489664551f80e686962f915108ec3a418008d83140bc000030ddcea2c614c89924682040e986942f314a08c03ac17d09303180c8000030dd71a2b9945c99246b20a8f106b42fe15088fc3c418109182f80b8000030dd1722ab13c49284391f10e2465c2c913b885838016008803000c2000030dcb9e2b114249644562008ea068c2e614b08d83a618109203180b4000030dc5ba2c5949899a4682048e786802db140084c36815e08702e80be000030dc00e2ab93d09404431f40e346702e4142089839016008702bc0aa000030dba582a813c093c4491f48e246562d113b086838e17608c82f80cc000030db47c2be148098245e1fe8e746882dd13f08a039a17a09383000c0000030daec32b014489724571f88e5466e2ee14608cc3a017708802f80b8000030da90b2b6944896645b2008e846742e313f887838817408b02d80ae000030da3642a5939c9164341ed8e346602da13f886437617308902e00a4000030d9da82ac941c9584431f70e606942ef14988d83b217809403040b2000030d97f12b014049584551fe0e786802e013d088439417a08d82e80ce000030d920f2c4949c99847520d0eec6b82ff14c88f03b817b09603080cc000030d8c432b9946097a4621ff0eb46a02f314788bc39216b08882c40c6000030d86a729a938090842c1ec0de462e2bc136085837c15f08d02e00b2000030d80fe2ad13e49444441fa8e706762d0134082837216308682c80b8000030d7b122c514ac98e4672088ecc6a82fa14f88e03b217a08b02d40be000030d751f2c894fc9c047a20a8eec6b030715009043b217e08902d80ba000030d6f472bb14589684511fa0e6c6682e2143089439416d08802cc0ba000030d69732b9142895645b2010ea46802e414708b03b217708f031c0c2000030d63b32b4942095e4531fc8e7467a2df13e088c37815407b829c09c000030d5e062a914049404521fe8e8c67c2e614708b439c17108602ec0ba000030d58382b8945c98445e2030ea869a2f314688e83c018709703340ba000030d52542c0948897445c2078eb868a2ea14d88f03a819509d83480da000030d4ca42ad13e894c4551f70e586822e5149088439217408a82dc0b8000030d46cc2c114809704632010ea86782e213e088838c16908702d40b6000030d40fc2bb14589704632078edc69e2fb14f08d039616b08582a40b0000030d3b0d2c414949944702020e9c6a02fa150092c3c217c09102fc0be000030d35102d014f89ae46c2040eb06a830115088dc3ba17c09403100be000030d2f272c914c898e46d2040ec46ae30114f88f83cc18309283040ce000030d295e2b3942c9524431ee8de862c2b9130083836415407c82c80ae000030d23902b714449584501fd0e886802e614508ac38c17008802e00cc000030d1ddf2ac13e492642f1eb8dd86422d2139083437416208682c80bc000030d17ef2cc94f89cc4812160f446c230615188fc3c418308d82d809e000030d120e2c314909804621ff0e846a62f314708c83ae16b08682e00bc000030d0c332ba147497a47020a0f2c6cc30815409343be18709283140be000030d06792b3144c9744632088edc6b42fc14c08dc3a817608e82d80be000030d00a22bd949097a46e2018e806822db13f888037616508a02f80c2000030cfaaf2c914a899a46d2010eac6a02f615209343c017908e83100b8000030cf4bd2cd15009c047820e0f0c6d030615709543e218f09a83480d0000030ceeed2b994589724571fb8e546762df141085c38615f08302cc0b8000030ce9392ab943c96a4581fa0e406662d913f08a83b618008e83000a2000030ce35c2be94889844552010e7c69c2f014988f43ae17708d02e00b4000030cdda12ae14209644581f88e5c6762d713f889039016a08882d80c0000030cd7eb2ab14009344321eb0dd06442d013e888439817308983240d2000030cd20b2bc94b09904672090ee86a82f814c88d83c018008f02f00ae000030ccc552a813d493243a1f20e346482cb138087438616b08882d40c0000030cc69b2ab93dc93c4421f38e5467e2ea14b88fc3d619009a03440e6000030cc0bf2c014a89a24762080ee86b830715189203ca18309202e80b4000))) else (if i < 517 then (if i < 515 then (if i < 514 then 0x30fa05a2b9944c9704571fe8ea869a2fc14f88f43be187097033c0d8000030f9a992b794209664682048ee46be30815289043ec19009a83500e2000030f94cf2bc145496e45c1fc8e546742db13c089838a16708782d00b2000030f8ef32bd948499a4622040eb069c2e614488b439816f08c82d00a4000030f89032c494b09924742098eb068e2fc14908d03aa17108e82fc0ba000030f83422b2942495c44f1f88e5c6802dc13c886c37e16e08982cc0c2000030f7d9f2a713dc92843a1e78dc86402d313b087439416408982e40d4000030f77c52c114949a048020c8ef86b630114d88bc3a417808c82f40b4000030f71df2c3947c98045b2000eb068c2e6144089438816708402cc0ac000030f6c362a913c492442c1e90df465c2c213688303a216a08282c40c2000030f665c2bc14409624501ff0e8468c2ec14588b03a217508d83040d0000030f60a22aa93a49284391f08e1864e2d014308a83ac17a09302e40b4000030f5aee2a613a49164351ec0df864c2d413b887037c16408602d00aa000030f55132b9145c97a4651ff8e806962eb143889838a17208802f80c0000030f4f632a893d093443e1f30e106582d713c889838216908982f00b2000030f49c52a413b492e4361f10e246442c6136883437816008002b40ba000030f44132a893c893a4471f30e386642d113a885c37c16208882d80ba000030f3e082d595389e24922178f346ea30c15309403ce186092030c0cc000030f38522ae13f09364431f60e306502d013b089038416d08982d40aa000030f32872b9144c9624521f88e6c6802db13a086837e16008602cc0b6000030f2c9f2c494bc9a646d2098ee06a42f614a88fc3c018809183100ce000030f26982d495209e04932190f286da315159891c3cc17e08d02e40be000030f20bd2bd948498845d1fc0e846842e214388b83a217008c83080d2000030f1b1b2a293e89324411ed8e1064e2c813107f835215007d02ac0a2000030f15702a913f493c4451f28e086582d5138083837216408902b80b0000030f0faa2b394189504541fd0e246622d313e087c36415c08502bc0a4000030f09e52b6142895c44d1f78e4c65e2da14088983a817a08e03240c2000030f040b2c094ac98046a20a0eb86be30615809303ca18a09703300ce000030efe402b8145096644f1f90e806862dc13f88b038817708c82e00c6000030ef8732b5942096446e2090ec46ac2fc15109103ae17e08d82f40c4000030ef29a2c714ac9964622028eb869c2f614e08dc3a617908c82dc0c4000030eece42ab93d89364451f60e346502d513e089c37215508582c40a4000030ee7112bc949898846e2070ec86a62ec14608ac39c17308782bc0a8000030ee1572ab14089344431f10e7867a2e2142086838e17408c02ec0bc000030edb342dd95489e04952178f506e430f15189103d818c09502f40c8000030ed57a2b5944095445b2000e846782e114588a838e17008b02e80be000030ecf882c794c49b247120b0eb469e2e914408c43aa17208b82fc0bc000030ec9c52b6142896e45b1fe0e6c68e2ec14688c039616408082a00b6000030ec4042b294509744561fa8e546802ef14908943a417a08e02dc0c2000030ebe2f2be144897244f1f98e5c66a2d713e889c38816a08702dc0ba000030eb8862a913ac91442e1ed8e0465c2d4133086038016008602cc0b6000030eb2c22ba14549604622040e8c6822e514508ac39a17308702c80a8000030eacf12bc14449744511fb8e786882ec14a88a83bc18008a02c00b2000030ea73e2a693fc94e4421ee8e506542c613c886c38016a08702e80ba000030ea18f2ac940094644a1f48e4c67e2de140884437e16b08982b00a6000030e9ba32c214749904652020eb86bc30015408f83c217e08f83140d6000030e95ee2aa93f89444451f00e4465e2d214108a438e16808682d00c2000030e90142bf948c9864551f80e586862ed14608d03aa17408f831c0c2000030e8a4e2bb144097c45f2030e9067e2e314108a039c16b08882b40c8000030e84582c994b09984702080ea866c2d713e089839c16d08a82c00a6000030e7eaf2a793c893e44c1fb8e486662da13b086839016208202bc0ba000030e78d52c1148898a46e2088edc6b02f814988f03a216b08a02c80b0000030e72fb2bd94789664481f10e3463c2c5135085838a16d08402f40be000030e6d2b2bb149099847220a0ec46a82ed14b88d039a16608482c00b4000030e67882a693e495444b1f60e806782e2141089038817008882b00ae000030e61db2a513d495444d1f60e386702e314388c839417408d02d40b8000030e5bf82c7948c9884592000eac6a02fc14908cc3b817308a82bc0b6000030e56362b6941896444d1fd8e506642d513f088c3a417b08b82e40c2000030e50502c394b09944662010e7c67e2f114788a43a417208902e40b4000030e4ac929393388f64301e78de06342c5132885439616708182b80bc000030e450c2af13d092043a1f00e3c6642d4139086c37415507e82a80b4000030e3f6c29e136c90a42a1e60dc46422c0133884036c165083029c0a0000030e39ab2b3140c9584561fa8e706682d5139887c39016f08782d00ac000030e340b29c937090041b1e78df06462c2136083837415d08482b40ae000 else 0x31113242b5146096c4521fd8e9868c2f714e88e03cc18809382e80b600003110d3c2c3949898e4692050e8869e2f014b88bc3b417e08e03240d20000311077f2af942c9444411f88df06522c8137086c38e16a08302bc0b6000031101b52b5144496244d1f70e286622cb13c889839216708a02f40c00000310fc2a294134c8ee4151d98d8c5fe2ae13107ec35414f07e02a00a00000310f6492c2949498645c2010e646722e1144089439017408c02d80aa0000310f0562ce14e09aa4772120f186be2fb14888bc3b617008982d40c40000310ea9e2b014249544501f88e8c6a02e914308a839217108782e80b20000310e4d52b414489824602018ea86982fe14b09383dc19309383240c80000310df3029e137891243c1ee8de864a2cf135084c36416008382d00b00000310d9502c294d49c447b20f8f046d230414a08d83be18608f03200c80000310d39b2ad13f494643d1f08e1464e2c7134083035a15208002b00a80000310cdcb2b594049484541fa8e406862e314808bc39617708902f00b00000310c7fd2b5144895e4461f90e306742e514788cc39416408182c80b40000310c2342b794449644481f50e486682db13a087438015c07f82980a20000310bc592c394b499845b2000e9c69e2e914708b039a17008282b80ac0000310b6aa2af13e89404461f50e206622de13c885038817208d03080d20000310b0cc2be14709884632028e946982f114908bc39817508f83200da0000310aaf22bc147c98645f1fc0e7c6822e914708b039a16c08a02d00c20000310a5162b9146497245e2008ea46962f3148889c38616c07e02d00b800003109f1c2ca14ec99a46a1ff0ecc6a82ec14a09103c618009283140c6000031099342be14709804622068ec86982f0146889c38215a08802a80b6000031093632b994a09704572018eb86a42ee14d88f43a617008c83040c400003108db22ae942495e4521fd0e986942f014108a438a16e08903040b4000031087d02c994bc99446c20c0ee46b830115009143d218708d82dc0ce000031081f82b314009704551fa8e6c6642e413c085839017708782dc0a600003107c2c2b0144895e4521fe0e946962de13f08b83a617608882d80ba0000310766e2b7946095e4501f30e546542cd139885c38816508302c00ba000031070982b8947097446b2068e9468a2ee14288b83ac17a09282f80aa00003106aa82c394b499c47e20d0ee86be30415409143ca18a09383200c0000031064ec2b0943096444f1f98e3c6602e214508c83a816d08e82f80c200003105f2b2b714609764672060ec46b22fa14d08d43bc17d08f83000c8000031059602b3942c95044d1fb8e6868a2ec14008b43a617208582c80b8000031053df28f13008cc4081db0d8460c2bc139886436615a08382b40aa00003104e092bc149099246f2048ea46962f014a88c43a017c08e03080cc000031048462b5140495c4521fa8e746942e914a08f03b217c08c02ec0a6000031042702be147c98045d1ff0e9c6aa30315409303da19709b83580d600003103c952c214a49a447120d8edc6aa2f614708a43ba18909083180d2000031036ef2a2937891e4351f20e006322c312f081036015a08302b80a60000310313a2ae13f894c4461f38e2463c2c913a087838c17208d02f00c400003102b592c494a49a047620a8ef46aa2fb15409043c818c09383040ae000031025792bd949499846c2078e986882e113e887838a16608803080bc00003101fa62b994709784511fa8e906842e914888d83a817e09082ec0ba000031019db2bb14509784612040ec469a2f614808f43c017f08d82e00c4000031014182ad93f492c4411f60e386602e2143888838a16f08902d80be00003100e482b9945c9784581fb8e706802e614c08dc3aa18008f03280d00000310088a2b2946c98646c2020e846a22ec13f88a83a016b08d02e00b2000031002e22ab93e893e4471f40e246662db14688e83b017509283240d6000030ffcf52c1948099646b2088ef869e2ec14908c039216a08502c00a2000030ff71d2bf14a89904672028e946742dd142088437a16908d02f40c4000030ff14b2ba145496045a2020e686742e914908c03a417408802b80b6000030feb7f2bb94549804652018ec06982f014508b43a217a08e02f40bc000030fe5b32b9146897245d1ff8e846922e914508c03c618109203080b8000030fe0032ad94189564421f18e146442c51330844372164083829809e000030fda2a2be147897044f1f70e406642dd13e88a838816c08402b40bc000030fd4352cc14b49b047d20e8ed06b630014f08fc3c818009203140ce000030fce772b4944c97a45b1fb0e806882de14288a03ac18409503240d0000030fc8c82a813fc9364411fb8e8c6842ec146089c388165080028c09a000030fc30f2ae140893443b1f08e606842e814688a038c16c08982d80b4000030fbd6c2a793c89204381f00e086442c0130883436e15e08102c40ae000030fb79b2bc14809824632058ec06a02f914e09003ae17608b82dc0c4000030fb1cd2ba145096c45a2058e5c6802e7142089439617c08b82c00ac000030fabf52be148c98a4722078eec6b42f514c88ec3a617b09503240ca000030fa62c2bc146497a4591fd0e946802e113c888838816c08b02c40b8000) else (if i < 516 then 0x31284fe2bd945c96844f1fb8ea06782d513b88a439616f08702bc0b000003127f322bf94849804632010e7c68c2dc13e087837e16908502b00a4000031279632b7940096044f1f88e606722df13d086838216c08a02f00c4000031273b22a793a09284411f50e506682e714208d03ac17f08e02ec0c400003126df02b1141094844d1f80e306702dc141889c39e17408982d00b6000031267fd2c194c499e47820f0ea068c2e614908d03aa18109683280ca0000312622e2bc94609664551fe0ea06902ea14988d03a217208982e40a200003125c7c2ad13e892e43f1f38e2c6702d713b088c38816308782d40be000031256e029d139c9244381f38df06502c813a085438e16e07f82cc0ba000031251092bd14889784622010e8469a2eb14408dc3a817408d02e40ba00003124b5c2ab13cc93c4451f80e546762d6141088038a17308882c00bc000031245762ca14d499a4722098ed46bc2fa15008e43a217908d82dc0ba00003123fbe2ae93e49524461f38e5465e2d9139085837c15f08202d00b6000031239dd2be94909844692050e9069a2f414b89043ce18809703100c4000031234202ac940494c4421f40df06542cc133885839016608a02f80c000003122e212d095049b84842100ee86c830b15809303d617e08e02f00c80000312284d2bd147c9984661ff8e8068c2e814588f03bc17c09003100ba0000312228d2b0140493e4401f10e2065e2d0132883437a15a07f82900a400003121c9c2c994e89be47420a0eac6a62e314508a838a16b08582bc0ba0000312170c299135c8f84191dd8d8c6002a712a080c34a14807b82840a60000312111e2c614ac99a4732088ee06b62f214b08dc3a817d08d02fc0be00003120b452be14989aa47f2048ebc69c2f014d89043e218509483080c0000031205542c814cc9a046f20d8ec86a42ee14988c839a17008502c80a40000311ff962b514289724632008e8c6962ee15009103c218b09882fc0b80000311f9ae2c514d49ae47c20b8ec46982e314988bc39a17508b02e40b80000311f40f2a813e091a4391f38e186602ca13e088438a16308782b80a00000311ee612a713ec9524591fe0e5867c2e414709083da18909503040b20000311e8ad2b113f894844c1fd8e6868e2e1141885c38216f08c83080e00000311e30e2a113788fa4311ea0e0c6582d713b889438c17008f83040ba0000311dd532ac13cc92a4321e90e0464a2d113d887838216608202cc0b40000311d7842b8142895c4501fd0e6c68a2e714508703a017609282ec0ba0000311d1a32c414c89984662008eac68e2e313f089439816908682cc0b40000311cbe42ac94109464421fc8e806942f0143888438c17508883100ba0000311c6052c014809884612050ed06862e214188b03a418509283140d00000311c04d2aa93d492c4381eb8df06462ca134085c36415e08082a809e0000311ba912b1940096045b2010eb46a42f414788a43a817708c82f40bc0000311b50729993348e64211eb0de864a2c51398850362156080026c09c0000311af362b2941495244b1fd0e946842f514d08e43b017108e03140d20000311a9782b314289764591fa0e546722e414108b439c17508d02e40c00000311a3912c794e49b647220c8efc6aa2f014708b839617c08982d00be00003119da62ca94e49ae4732070e7c6802e0145089837e16308702c00ae000031197dd2b414249624591fe0e9c6a62fa14f090c3ba17708b02cc0b2000031192212b0146095e4491f28e3067a2db13f08c83b017608b82e00ba00003118c6b2ac141c9504481f40e2c6782e414808e43b618309082f80c0000031186ae2af93d493443e1f68e506622df142088838616d08402e00a6000031180de2b7946c9764571f88e486782e5143089c39e17008b02dc0b400003117b352a613cc93243f1ea8dec63e2cb136085037016408602c009a0000311759129c13548fe42b1ec8df063e2c8135085c38616c08802e00ae00003116fc72b6946c97c4672028eb06902e014408c83a216408a02cc0b0000031169f72ba144096444c1fe0ec06b630415689303ce18e092830c0be000031164272b894449784612030ec46982ea143889439816f08b02ec0b200003115e672b7143097045e1fb0e446782e114988b83a216f08b02dc0be000031158802c094689724562020ebc6a82f414b88f43be17909103040c4000031152cb2ad14089664571fd0e4c6662db13e087839217508602b40ac00003114cf92ba148c9904702058eb868c2f414908d43b417808b83100ba000031147302b394289624461f88e6867a2e013e88b439617608d82e80b4000031141602b7145c96a45e1fe0e986942ea14508f03b017308e82fc0b000003113bbf29c93548e44141de8d7c6062aa129082836a16108302bc0b6000031135e02c014989984682050ecc69a2f114889003c418509203000c80000311300e2ba945898645c2040ed06c230014d09043bc17508f03040cc00003112a562b0942096a4481f50e3466a2d413a887039816c08782d80b40000311246d2c0148c9864672088eb46a02f114d89183d4186093031c0ba00003111ea92b2143896c4581fc8e706822e313e088037c16108082a40aa000031118e22b7145897245e2058ea46ae2fc15189103c418109503280ce000 else 0x313f81a2ba145c97c45e2040e886862d913f088838a16a08102b00980000313f26b2a613bc9184341eb8e286722d513d089c38616908c82f40ba0000313ec9b2bf94749884641ff8e6c68e2e514508c83c818709602fc0c00000313e6ce2b8145497a4631fd8e946ae2f614f88ec3ac17608c82f40ba0000313e0fc2bc14889b04812118f186ca30514e89003be17a08f02e00c00000313db502a693d493043b1f00e1065c2d3136085436815d08102980980000313d5972ad142c95a4591fa0e6067c2e914688ac3a017008c82d00a60000313cff029a939090842a1ed0dd86442cc13a8858390170084029c0b00000313ca012c794c899646f20c0ee06ae2ff15289083ce18509403180ce0000313c46c298138c9144361e60dcc64e2cf133083836216008782d40a00000313be7c2c194b499646d2090eb06a82f414508c038e16d08b02ec0b80000313b89a2c814a497445d1fd8e746782dc13e08783ae17909282f40ce0000313b2cb2bf145897444e1ff8e6c6782e313d089838816f08d83100c20000313ad002b1941c95c4541fc0e7c6862e614488d03b618009103200c40000313a7262c2148c97e45e2030ed06ac2fa14d88f43c617e08c03140c80000313a1692ae941896444d1f88e5c67e2e5141088439217508782f40be00003139baf2b714589724682088ec46a22ea14408b839a17008882d40c4000031395de2b9947898a45c2008e946a02f814d88ec3ba18708c02b80aa0000313903a2a313bc9264341f28e5868a2dc13d889439c16e08982f40c000003138a692b494289624541fb0e3c65c2db14408b03a417408b83040b6000031384722c914e89ca48a2170f186bc2fe15209103c418208c02e40b400003137ea42b2141496845a2050e946922f614808c43a017208902c40b2000031378d82b6145096a4561fb8e606822e614608b83b017208482a00aa000031373372aa93e49224331e90e086582cb136088838c16a07f82a00a200003136d882a613b892e4471f58e486802e514188a438c17308d830c0d8000031367aa2c3147c97a4551fd8e706642d713e088038416608382b40a8000031361cd2bd945095a4542020e986882ee14a08dc3b617c08702e40ca00003135c092b3140c9484461f50e2064e2cd13c088c39817708e82f00b40000313563d2b694409544501fc0e8867a2e714688b83b418309182e00ae000031350582c914b89aa4702068e9468c2ef14408a039016f08a02dc0b000003134ab02a913e09284401f48e1c6522be131884835e16408b82e00b2000031344c52c5949c96c46020c8edc6aa2f014688a039a16f08802cc0b800003133ef92b5942096a45d2068ed86b02fd154092c3d618d09483300da000031339352b4144096e45d2020e886842e814508b439a15b08102a00ae0000313335e2bb143c9644511f48e3c64e2c6138883435e15307f02a40ac00003132d952b6144895c4562000ea86982ed14508c03a217808f02d40aa000031327c52be146097445e2038ed46942f915188dc3ac17b08d82e40c0000031322052b494249524551ff0e7466a2d614288943a216e08682f40ba00003131c4c2b2942495c44b1f60e5c65a2d714288b83ac17c08882e00b8000031316702bb146496e4632018ea869e2e913d887438617508882f40b4000031310872c494bc9a446a2050ec06b830e15309303da18b09203180c200003130abf2b3942094e44a1f18e1c6482ce13b089439a17308d02dc0ae000031305042af13f89584511fb8e686682d3137883c37015d08402940980000312ff302bd949898a46a2030ea867e2f315089003ac17e09083080c00000312f9612b6141c9604571fe8ea86a22f614789003c618708d82d00b20000312f3732cd14fc9b44802158f386ea31315e898c41219b09c83440ce0000312edcb2ad13ec93842e1ed0e0064e2cb12f886438416408302d00c00000312e7fe2b9143c97045e2028eb86a82f614b89103c017e08e03040bc0000312e23e2b2941096844d1f98e786942f114888e43aa16d08802e00c60000312dc602bc944895644d1f70e2067a2cc13d88c83a616d08802d40c00000312d6aa2a513b091e4301ec8e1c64e2d214008a438c16708502dc0be0000312d0b62c894c89b247620f8ef06b42fd15308f83b017708c82d80b00000312cace2c394c89aa4762050e946902ee14908ec3c218909703280d00000312c5082b0142498045e2008e8869c2f014b08cc3c417d09483180b40000312bf5b2b0941493a4441ee0e0864a2c913d085837a16c08482c00b40000312b9822bc14849724531f98e3c6622cd13b08983a417608602c009e0000312b3932cc14c499e46a2050ea06a62eb14a08e43b417f09182e80b60000312adbe2bc94989884672050eb86982e314288c039616f08982c40b40000312a8012af93f494444b1f18e246462d413e889038216508402c00b80000312a23d2b3945c9724511fa8e3c6722e414788b03ae17308f02dc0c600003129c772ba942c95a4471f20e186542c6137085837215d08382c80bc000031296972c014b89aa47f2118f386ea30315008f43ce18109302f00c4000031290c42b914709564501fe0e7467a2d814188d439617509003140d000003128ad82c7149c9864642040ed46b22f714e08dc3b418008c83100ba000)) else (if i < 519 then (if i < 518 then 0x3156ad62ae141095644b1f98e946942e914388b83aa185097832c0dc0000315650d2b314349504502000e9468a2ef143088438416b08802dc0be00003155f582a693c89204431f38e286662d413c087838616708402cc0a40000315596e2c414b09a247220a0ef86c230515008f83d618609283340c6000031553ca2a4939891843a1f10e5065c2d0134884836014c077027809800003154e1f2a293a892242a1ec8e2465a2da138086c37e15907e82b80ae0000315484f2b6144c95845d1fe0ea469230515a09383e418b08f02ec0b0000031542872b814349544572008eac6a42f315088dc3be17c08e82c00c000003153c8c2d5950c9c44882140f146ba2f815089043c818308c830c0b8000031536a42c214b49ac47620a8eec6c42fd14f88fc3c818d09a83180d4000031530c22c3147c99a47420b8ed86a82f314a08cc3a017508882b40b000003152b072b3944896e4571fb8e9c6902dd14308a03a617308b82e80c00000315255f2a393bc9284351ef0df06342c0133885037215a08502c40ae00003151fb42a593b091442a1df0da461a2b0133084836c15a08482cc0aa000031519cd2c994b09924692068ea46ba30a159092c3e018709283140c00000315140b2b013e093a4401ef8e0c64a2c9136086c38215c07e029c0bc00003150e4b2ad93f893a4421f50e5067e2e1142086436816608b02b40b0000031508742ba94949a046b2040ecc6b42fb14708ac3a817e09003180c4000031502bd2ac940895c4591ff8ea869e2f914c08e43aa16c08402a00b00000314fd132a913d89584532008ea86aa2f914988cc3c417b08982fc0c20000314f7462bd948c99a47b2130f186ca30314c08a838e16f08582c00aa0000314f1592c214bc9a447220e8f006c22f614a88cc3a216908a82ec0b60000314eb852b794389564481f48e4c68c2f414988cc3ae17308d82cc0b80000314e5b32b7147498a45c2010e9468e2e214788ec3b017e09302ec0d40000314dfdf2b7948098c47520b0ed469a2fc15088f039e17208682c40a60000314d9f62c2947c99846b2078e9469e2f814f88e03c619109783500d20000314d41b2c114a89a84782120f146c830f15209103c817209102fc0ca0000314ce5b2b1941894243d1f50e6c6762e013a08a038e16808382b80aa0000314c8802bb94589784672070ebc69e2f514808c43ac17a08682ec0b40000314c2b72b5944894e44b1f80e586542cf13c88983a817f08d02fc0ba0000314bcf22b4943495644f1fe8ec06962e714688bc39217008c83040a80000314b71a2bd947c96c4562008e786602d714188843a017608f03200be0000314b16a2ac13dc9384461f98e6c6802e4144089c38816708a82ec0ba0000314ab7e2c414b89a24662000e806942ed14888ec3a417908a82f00c40000314a5a02bb947498446e2088ed46a82fe14c08e43c218808c82d40c000003149fd32b6946098045e2008ea86ac2f614c88c43ae18608d02f00d600003149a322a513b892a43c1ec0e186482ce136885037c16508482a80a20000314946c2af942496245a2030ea467a2e814688c03aa17508a02d80b600003148e9f2bc145096e4571ff8ea868a2f314d89083c618d09703580dc000031488f82a993e494844b1f08df86582d913d886437c16708202d00b60000314833a2af941495a4551f58e046442cd138087838c16f08b82d00b000003147d4e2be949897e46b2080ed46a62f414b88f03aa17408a82ec0cc0000314775c2c794b49b647a20a8ecc6b8306153892c3e018d09002f40c2000031471b12aa13c092243f1ed8e0063e2ca13d889039016e08b82f40b200003146bec2b814509684502018e5c6842db14288a038a16c08882c80bc0000314662f2b014289564501fd0e8c69c2ef14688a839816a08a82d40b00000314607f2a793f89484451f50e2c66a2d6138086037c16908802c40a400003145a8b2c514ac99a4632000ea86942eb14588b83a617a08d02d40b2000031454e92a613d49344491f78e3866a2d5136886438216808582c80b400003144f132bb94609604562010e886802e714188a039417308b82f00b0000031449592ab93dc94a4481f28e206482d913d886438e17308e82cc0ca0000314437f2b9948098e4662040e946962e914b88d83be17b08f02f80bc00003143d982c894cc99c46c2068ea86b42f514d08e83b818108e03100c4000031437da2b5140c95e4481f40e606742f1143888038416d08382a40ae000031432002c694809944662080e686702e014308a839216c08b02e00ae00003142c542a493d492a4391f38e4c66e2d7143889839a16e08c82c40bc000031426642c894c49a047920e0ef86cc30114e08cc3be18808d02f00c2000031420b22ad940894c45b1fd0ebc6982ef14b08fc3be17b08d02dc0c400003141aff2af13f89444481f98e7868e2ef14b88dc39a16d08782d00b2000031415222be946498e45b2050ed46b22f814d08e83ca181090030c0b000003140f532bd945496044e1f60e7069c2eb15008e83c417d09282f80be000031409aa2a993dc93c4421f08e3066a2d5140087037215a08082840a2000031403bf2c494b498846e2080ea86862ec14a88a039e16b08e02e00da0000313fde92b9146899847a20f8f046b830414d89103d219609a03340cc000 else 0x316dcf62be145096644b1f38e246642d013d88ac39a17409082ec0aa0000316d7352b414789784672028e8069a2ea14888cc3b217208e02e00b00000316d1672bb14649604571f88e6467a2da14408d83c017a08c02e80ae0000316cb8c2c414bc9a846f20b0ef06b430214f092c3b617a08a02f40a80000316c5e82a393c49364351eb0e146562d114008b039e17108d82ec0c80000316c02e2b294389604592008e946922ec14588b439e16c08682b80c20000316ba5b2b714389704531fb8e5c6642e014308c03b217608c82e80b60000316b4772c394b099c4672070ea86842d413a887839216408b02e00b60000316ae852cb94d89bc46e2070eb06a62ef14588d43ba18308d03100be0000316a8bd2c0146c9804682090ecc6a82ef14508a039017008902d40c20000316a2e92bc148096e4602050e846822d2141086c38a17308a02c00b000003169d062be949499446a2050e9c68a2ea14888f43b418209603180c8000031697212c314a89984722128f386c230815309183c017b08c02f40b6000031691582af93f893e4431f70e4c6622cf13e888439415e07f82b40aa00003168b942b6144897c4561fd0e6467e2e314688b43a616e08982e00b6000031685e52aa93e494043b1ee0e4466e2d313e088837416108582ec0b20000316801a2b313f89404401f18e446702d913c086837015f08482ac09e00003167a8029d13889144371ef8ddc6662d113b084036e16308a02fc0ba0000316748a2c614bc9a248520c8f086ca2f814c09003d618508d02cc0c000003166ea72be948098846d2098ee469e2fb15089143bc17608c83100aa000031668eb2af141094a44d1f78e446622e014188a43a017809083100c2000031663182bf94949844602018e986962eb14b08f43b418709402fc0ba00003165d482bc147497e46b2040e846782e214088a838816408682c80b4000031657692bd948897c4501fc8e6c68a2db143089c3b017b08d82f00b6000031651a22b894549704551fe0e706a02f114908b03a417a08b83000a600003164bb62c994b89ac47920a8edc6b82fe14908fc3b017d09503040ca000031645ed2ba14489684501f48e2465e2ce133884036015408282d00b20000316400d2ba947097e45d1f58e0c6482c1134883037615d08882a40a800003163a7529f93c49284371ed0e086462d113d084c37416408782ec0b4000031634b12b6941497044c1f80e5c6762d814288ec3bc18909483240d000003162eec2b9145897c4641fc0e5c6682d514308c439c16f08a02e00b4000031629332ad93f09404421f88e446622e313f887c3a217508b82f40b2000031623942a313c092c43b1f00e186622d3137883837015f08182ac0a800003161dcd2b294189564401f40e446742da141089038616a07e82a00b0000031617ff2bc145896c4612028eac6982eb14808d43b817708b02c00aa000031612352ba947c9844652000e846982e613f089438a16808582c00b200003160c622b8147098a4571fe0e746942ec14a08cc3ae17708b83140c60000316069d2b394309604501fb8e406842da13d885c36c15807e02b00aa000031600e62ac13dc9504461f68e486802d7137084438616808a02c40ba0000315fb0c2c0148498a4572050e8068a2dd141088439016e08b82f40c00000315f5382ba146898246a20b0edc6b430715509043b017d09282d00bc0000315ef7f2ad142095a45d1fc0e646922f414b88d03a617508c02ec0b40000315e9b12b2141495044d1f68e5867a2de14288a839a16f08d02d40b60000315e3f82af94209364341ed8e306722e714989003cc18409603180ca0000315de122c714a099c47a2098ecc6ae2fa14b88d43a217808e82e40b60000315d8622aa140495044d1f90e6067e2dc13f089c39a17508c82d80b80000315d2b72aa13e89544461f68e486702e014588bc39c16908882ec0c80000315ccf82b093e89684571fe8e3c6522d913e888039416b08502bc0a60000315c71a2c494c09a846f20d0f1c6d231215289103b816608a82d40b20000315c13e2c214b498e47d20d0f1c6d6310153892c3ce18a09683400d00000315bb5d2c4948c9704551fc8ebc6ae2f114688bc3a618409383040c00000315b5aa2ae140894844e1f58e286562d014188bc3a817a08902d00b20000315aff82aa13e092a43a1ee8e346702de140887437a16708502c40b60000315aa472af142096445b1fd8eac68e2e514488ac3ae17408682e40b60000315a4732bc94449704501fb8e5c6922f414808ac39616e08b83100cc00003159ebd2b3941095444f1f98e3c65c2c913a085c38016408682d80b6000031598fc2b3140c9644621ff0e986862de141088039016e08702c40ac0000315932b2ba946897c47120a0ec46aa2f414c89103c818509203140c200003158d502c094689864682040eb46962f814b89083be17908c82dc0b40000315877a2c0147c98a4642070ea46a82fa14808d83be17c08d82f40c8000031581c72aa13c093e4441f38e5067a2ea14a889c39617208882d80bc00003157c262a413c89144321ea8df864a2c813c088038015c08482a80aa0000315765b2b7940095c4541ff0e7c6822e014288d03ac17408c02e80c00000315708a2be948499246d2078eec6b62fb15008b439816d08982c80c0000) else (if i < 520 then 0x3184ea22c3148c98c46c2080ed06a42ed14c08d83bc18009303340e6000031848d82b2144c98446a2010eac6ac2f414a88b039c16408302b80b8000031843022ba947096e45a1fd0e546642da13e887c37415e08402d40be00003183d602a013c091c43b1f20de86422d213e089838c168082829c0ac000031837b52a893e494a4481f68e5066a2e2145089839216d08b83000bc000031831fb2ae93f89324481f48e586722d714388b03ac17408c03100be00003182c4e2a613b492e4471ef8e4866a2d313b88943aa17508c82ec0b20000318267e2b814549824632070ef06c62ff14f89103cc18b09183380c2000031820d42ac93c49384491f70e646762d613b887c38416c08a82f00b000003181b142b1943096e4582000e706722d7138888437e17308a82c80b2000031815542a893d493443c1ef0e1c6622da13f885037e16108282c00b800003180f7f2c0149c9a24702080ec469e30114a88a039217909083000b0000031809b22b9943894e44b1f48e486762dd142888038a16808682b80a8000031803f52af13f49364321ea8e0c63e2c9134884437416b08582b809e0000317fe352b6143c9644541fa0e486722d914508983a017709002e40ae0000317f8562c194b099646d2070ec06a82f414988d03a617108f02fc0ca0000317f28b2b914189464391f10df864a2cd13b084c37e16908582a80a80000317ecce2aa943895c4481f00e246742d4134085437c16708782cc0c00000317e7002b314449524541ff0e7c6802ed14888ac3a817609003280d00000317e1332ba146c9844682070e9c6942e714588983aa17e08e82f80b80000317db4c2c1148c97e46e2068ea068c2e114788dc3b617608e02d80a60000317d5ad2a213ec9304381ef8e2066a2e113b886038616c08802f00c20000317cfb12cb14e099e47a2130f186c830315088e83ca18209503240cc0000317c9f22b614309704552000e9c68c2f414408ac39e17508e02e00c40000317c4112c094949a84742088ecc68e2ea14688e43b218a08c02dc0b40000317be562b0941493c4331ed0df46422cb136083836416508702e00b40000317b8a42a814049304371ee8e3c6722e6146889438c16f08202ac0aa0000317b2f02a713f09424341ee8e106602c9136884c36c16008682dc0b00000317ad402a693ec94a44c1fd0e8067a2e6143088437e16508482d00c40000317a7632c394849924672080ef86b22ef14788d43b8184093830c0ca0000317a1972b5141c9604581fe0e7c68a2df147090c3cc17c09703340d600003179bc72bc14649724662080ec46b02fb15009103cc18709383240b6000031795e32b9947c9724571fc0e746782e214608c43b818009182f80c4000031790142b8143096245b1ff0ea06842f314d08a83a417a08302b00b800003178a762a0936c8f04211e48db86202b512d883c37e16908682d00aa000031784d02ab93f49424461f40e346682de14388e03be17b08d82f00a400003177ee02ca94989964632040ec46a62f314b88e43b418109002d40c00000317793a2a593d892e4411f00e1065a2d814108ac39e171084829c0a0000031773552c814dc9b447b20d0eec6ae2f114708c439417008902e009c00003176d782b9145097045f1fe0e7469e2f514e09043b217c09382e80a8000031767a72b7945897e4622088ed86a02ec14988c439e17a09183100cc000031761d62bc144095e44e1fa8e7869a2eb148889838616e08682d40ae00003175c312ab141895e44a1fc0e6c6722e014008bc3aa17408c02e00c0000031756792ad13e89404511f50e206642d5139883c36e15a08702b809c000031750a52bc947899846f20b8ed86b22fe14f09003c017f09203100b400003174ad32bd145c97445c2028eb06a22e114988e83ae17d08e03080c4000031745222af141894c44f1f90e1c6542d013c086438616a08682ec0c400003173f682ad93f093443c1ed0df06482c2136084836015a08302d00b0000031739b22a993e894e4541fa8e5c6782e113f88a039417108b02e40ba000031733df2bf14a89884602018e7c6862f814e88f83ca18709202f40a600003172e2a2aa142092c4331ef8e0863a2c2134886038a16808782cc09e000031728862a913e093c4441f08df06422c1137886037215808202f00bc0000317229e2c3949c9904662040ec86b02f814c08ec3a217308782c40c000003171d0129d93749024271ea0de863e2c9139086c38c16708882e80c6000031717102ce14ec9c047620b8ed46ac2f114988cc3a817008b82f40c00000317113f2be147897645f1ff0e906902e214588e03a017608d03040d200003170b5f2c094809844632020e9467c2e113e888438616407f02bc0ba000031705912b7946c9884782110f0c6ca30115209043ba17a08f83200ba0000316ffeb2a693ac9224431f80e7866a2de14208b03ae17c08e82f40be0000316fa2c2b5940c9484491f70e246602de14188b43ba17608682e80ba0000316f4392c694dc99046920b0f086d631715c09303ce184092030c0be0000316ee792b8146896e4581fd0e4465a2d213b888838216c08982cc0b40000316e8b82b8947c98a45d1fd0e7467e2e814188a039e16c08702940ae0000316e2d22c1948898c46c1ff0e846862dc13a887c38416b08702e80b8000 else (if i < 521 then 0x319c0b129c939090642e1ec8e2066c2e613e08a83a417108d02f40d80000319bb052a993c891642a1e88dd06382c5131885438416808082c00b20000319b5262c394ac9884732098ea06a22f314d08e83c218009002f40b00000319af5c2b7143495a4511fa8e7068a2f1151891c3b417e09383280de0000319a9b62a913e89424491f68e386762d913b085838016a08902c00bc0000319a4052ac13c89164361ee8e006382c413d886837e16508502c40be00003199e292bb146897a45f1fb0e846882ee14c090c3e818d09603300c6000031998652b6144c96c4612020ea46802e114508b839417a08d02cc0b20000319928d2c014b49984652068ee06a62e814588903a817909283080d200003198c9c2c614d09aa47b2148f246b62f714b08d839c17d08b82fc0b6000031986dd2b1943495644e1f98e8868e2ee14588d83bc17d09203380cc000031981372a893c092e43c1f00e006502c9136883c38216108702d00a600003197b732ba147c9864702058ebc6ae2f7149889c38615b07e828c0a6000031975a72b6944c97a4662038e546742dd14288a439016b08a02d00be00003196fe42b6146096c4521f80e646602cf13d888c38416d08582d00a200003196a5f29593448ee4171dc0d6c60e2ad12887fc36215408202940a2000031964792c594b499447720c8efc6c830b15988fc3b417908882d40b800003195eb42b714649744612098eac69a2ef14a08f03c017e08d02d80a2000031958e02b5945c9644551ff8e646782da13d888838e17008902c00c0000031953212b314149704511fb0e7c6822ec14888b839617308e82f40be00003194d552b3942c96e45c2000ec46a42f114788b83a216b08a82f00aa0000319478a2b0141095e4491f88e5066e2d5138886438216a08882bc098000031941ef2a213a491c4341ea0e0c65a2db141089439417008502c80ac00003193c052c894e89c84842128f2c6c630215288fc3b817a09002e80b20000319363b2b1941c97645b1ff8ea06a02f214908e03ba18309103140ae0000319306d2b6944c9604562000e5068a2e4140889438816108302c00b600003192ab22a613ec92844c1fb0e886802f314988e43ba17c08f82fc0b8000031924f02ad13ac92a43c1ef0e1c6562cd13f088838e16908a02ec0a800003191ef52cf14d89ac47220c8ec068e2eb14888e43b618009703400de000031919442aa13b093043c1f08e2865a2dc13f88bc3a617c09183140c60000319136d2bf949099046a2058eb86ae2f214488bc3aa17908b83000a400003190d962bf14809744561fe0e8c6902f214788a439216d08c02f80ba000031907df2ab93d89324441fa8e6c6742dd13e886c37c16e08a02e40b00000319021b2b6144496245a1fb8e8068c2f914e08e43ac18109a83580de0000318fc622b213e09484471fb0e7c65c2de13b884837c16c08982c80aa0000318f6bf2a613888ec4241e90df86522c0133884836216008302e00b60000318f1082ae13f493e43f1f10df86542cd13b089438c16608882e00bc0000318eb3c2b6946097645d1fe0ea06982ed14488a438c16408782e00ae0000318e56a2b714409564501fa0e646702df14088ac3ae17f08e030c0d60000318dfad2b413d892843b1f30dfc6422cc13c889838617408982a80ac0000318d9c72bf949098845b1fc0e946722d814108b83b017408c02ec0b60000318d3fa2b894509644562008e706742dd13f086038016108382b00ac0000318ce532a693e095a4521fc8e8468a2ee14188c43bc18309083140ca0000318c87a2c894c09ae47a2150f246d630d15789543e219309783240b80000318c2862cb94b09b647920b0ee06a02f215289483e419809703380ec0000318bcb82b9144c96c44d1f70e506742e414608c43a417e08e02e00ae0000318b6f22b5945094c4511fc8e5c68c2e514508c438216e090030c0ac0000318b0f32cf15009cc48a2158f2c6d02ff14a88cc3b617308f03140c00000318ab2a2b6145c99247320c0ed46be2fc14f08fc3c217d08b82c00aa0000318a55f2b794609904682090eb86a82f514488b83a217708e02d40ba00003189fa72b2944095e44c1f30e2465e2d614188b43b217908e82fc0bc000031899e52b394149584551fb0e8469c2f014888f43b818308c82d80d4000031894242b5945897c4682018eac69c2ef15188f43b217208903000d600003188e562b8142896245c1fb0eac69a2f314b09203de18909483280c80000318887d2c294789924662028e8c6862e714e891c3c818308e03100c2000031882ad2b5142c9664561ff0e7866a2ee145089439016608402d00be00003187d1329f93748fa4231e18d706222ba132084036615908202cc0ac0000318774b2b7945095a44e1fa0e686862df14108b439a15f08002a80b60000318718a2b2140894c44d1f68e246722dd14188a43a817408f032c0be00003186bb22c0948c99e46a2090ebc6942e914589043c2186097833c0d0000031865f82b514389724642048edc6b82ff14c08d83bc18709583280ca0000318602a2b8147899446720b0ee86b22f914888c83a417e08e831c0d400003185a592ba142897245b1fb8e686862e414588a038617208b830c0c4000031854852ba144c97c4672018e9c67e2e414088c43ac17f09002e80b8000 else 0x31a407d2a813ec9424451f20e146562cd134884437215908402b40b8000031a3a7b2d495389ce48a2170f486d8306154090c3bc17608b82d40bc000031a34c22b0941894c44b1f70e646782e614808e43bc18209383200ba000031a2f1f2a493f493c43f1ef0df06442d613a885038215e08382d00b2000031a295f2b9947898445e2000e6c66e2da14388a439a16808782bc0aa000031a23962b514489604591ff8e906902ec14a889c3a616a08582dc0b6000031a1da82c2149c9aa47c20b0f006d62f814c09203dc18a09383300d4000031a17da2b8145096e45a1fb8e686982fa14f090c3be18b09483400c0000031a12202b1942496c4641fd8e8466e2d113c086438416708982fc0d0000031a0c462c014bc9a047220c0f006982f114988f03b217c08c83040c8000031a06862b8145895a4581fd0e4066c2df14008b03b217c08f02f80cc000031a00a22c614ac99246f2088ed86b82fb14988e03ba18008f02d40b60000319faa52cf952c9e44902150f246c22f715208d43a618008e83380cc0000319f4f52a593d893e4431f30e546602ce13d086c37215c08282a409a0000319ef292c1149498e47b2150f086d230215889483ea18b09603100d60000319e97e2ae13f092c4351ef8e1c6602da13e085438416f08802d00c40000319e38f2c414a897e4692020e986922ef14608d43b416c08502d40b20000319ddc62b6143495644e1f68e4c6602d613f084437c16308682bc0b80000319d80e2ae942896a44a1f18e0864c2bf133883835e15f08282b00960000319d2342c514749684521fe0e606782e314708bc3a617208b83080c80000319cc672b8142c9604592020eb86842ec14808c43b017b08f03100cc0000319c64a2e015989fc49a21d0f646e22fc14c08e03a016a08902e00bc000))))))))))

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



private theorem b520820 : covered 520820 520885 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b520885 : covered 520885 520950 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b520950 : covered 520950 521015 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521015 : covered 521015 521081 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521081 : covered 521081 521146 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521146 : covered 521146 521211 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521211 : covered 521211 521276 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521276 : covered 521276 521342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521342 : covered 521342 521407 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521407 : covered 521407 521472 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521472 : covered 521472 521537 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521537 : covered 521537 521602 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521602 : covered 521602 521667 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521667 : covered 521667 521732 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521732 : covered 521732 521797 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521797 : covered 521797 521863 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521863 : covered 521863 521928 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521928 : covered 521928 521993 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b521993 : covered 521993 522058 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522058 : covered 522058 522123 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522123 : covered 522123 522188 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522188 : covered 522188 522253 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522253 : covered 522253 522318 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522318 : covered 522318 522384 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522384 : covered 522384 522449 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522449 : covered 522449 522514 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522514 : covered 522514 522579 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522579 : covered 522579 522644 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522644 : covered 522644 522709 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522709 : covered 522709 522774 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522774 : covered 522774 522839 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522839 : covered 522839 522905 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522905 : covered 522905 522970 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b522970 : covered 522970 523035 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523035 : covered 523035 523100 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523100 : covered 523100 523166 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523166 : covered 523166 523231 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523231 : covered 523231 523296 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523296 : covered 523296 523361 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523361 : covered 523361 523427 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523427 : covered 523427 523492 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523492 : covered 523492 523557 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523557 : covered 523557 523622 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523622 : covered 523622 523687 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523687 : covered 523687 523752 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523752 : covered 523752 523817 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523817 : covered 523817 523882 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523882 : covered 523882 523948 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b523948 : covered 523948 524013 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524013 : covered 524013 524078 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524078 : covered 524078 524143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524143 : covered 524143 524209 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524209 : covered 524209 524274 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524274 : covered 524274 524339 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524339 : covered 524339 524404 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524404 : covered 524404 524470 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524470 : covered 524470 524535 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524535 : covered 524535 524600 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524600 : covered 524600 524665 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524665 : covered 524665 524730 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524730 : covered 524730 524795 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524795 : covered 524795 524860 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524860 : covered 524860 524925 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524925 : covered 524925 524991 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b524991 : covered 524991 525056 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525056 : covered 525056 525121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525121 : covered 525121 525186 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525186 : covered 525186 525252 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525252 : covered 525252 525317 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525317 : covered 525317 525382 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525382 : covered 525382 525447 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525447 : covered 525447 525513 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525513 : covered 525513 525578 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525578 : covered 525578 525643 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525643 : covered 525643 525708 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525708 : covered 525708 525773 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525773 : covered 525773 525838 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525838 : covered 525838 525903 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525903 : covered 525903 525968 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b525968 : covered 525968 526034 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526034 : covered 526034 526099 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526099 : covered 526099 526164 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526164 : covered 526164 526229 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526229 : covered 526229 526294 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526294 : covered 526294 526359 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526359 : covered 526359 526424 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526424 : covered 526424 526489 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526489 : covered 526489 526555 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526555 : covered 526555 526620 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526620 : covered 526620 526685 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526685 : covered 526685 526750 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526750 : covered 526750 526815 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526815 : covered 526815 526880 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526880 : covered 526880 526945 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b526945 : covered 526945 527010 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527010 : covered 527010 527076 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527076 : covered 527076 527141 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527141 : covered 527141 527206 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527206 : covered 527206 527271 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527271 : covered 527271 527337 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527337 : covered 527337 527402 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527402 : covered 527402 527467 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527467 : covered 527467 527532 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527532 : covered 527532 527598 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527598 : covered 527598 527663 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527663 : covered 527663 527728 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527728 : covered 527728 527793 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527793 : covered 527793 527858 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527858 : covered 527858 527923 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527923 : covered 527923 527988 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b527988 : covered 527988 528053 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528053 : covered 528053 528119 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528119 : covered 528119 528184 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528184 : covered 528184 528249 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528249 : covered 528249 528314 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528314 : covered 528314 528380 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528380 : covered 528380 528445 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528445 : covered 528445 528510 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528510 : covered 528510 528575 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528575 : covered 528575 528641 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528641 : covered 528641 528706 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528706 : covered 528706 528771 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528771 : covered 528771 528836 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528836 : covered 528836 528901 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528901 : covered 528901 528966 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b528966 : covered 528966 529031 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529031 : covered 529031 529096 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529096 : covered 529096 529162 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529162 : covered 529162 529227 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529227 : covered 529227 529292 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529292 : covered 529292 529357 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529357 : covered 529357 529423 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529423 : covered 529423 529488 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529488 : covered 529488 529553 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529553 : covered 529553 529618 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529618 : covered 529618 529684 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529684 : covered 529684 529749 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529749 : covered 529749 529814 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529814 : covered 529814 529879 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529879 : covered 529879 529944 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b529944 : covered 529944 530009 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530009 : covered 530009 530074 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530074 : covered 530074 530139 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530139 : covered 530139 530205 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530205 : covered 530205 530270 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530270 : covered 530270 530335 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530335 : covered 530335 530400 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530400 : covered 530400 530465 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530465 : covered 530465 530530 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530530 : covered 530530 530595 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530595 : covered 530595 530660 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530660 : covered 530660 530726 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530726 : covered 530726 530791 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530791 : covered 530791 530856 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530856 : covered 530856 530921 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530921 : covered 530921 530986 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b530986 : covered 530986 531051 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531051 : covered 531051 531116 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531116 : covered 531116 531181 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531181 : covered 531181 531247 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531247 : covered 531247 531312 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531312 : covered 531312 531377 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531377 : covered 531377 531442 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531442 : covered 531442 531508 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531508 : covered 531508 531573 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531573 : covered 531573 531638 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531638 : covered 531638 531703 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531703 : covered 531703 531769 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531769 : covered 531769 531834 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531834 : covered 531834 531899 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531899 : covered 531899 531964 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b531964 : covered 531964 532029 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532029 : covered 532029 532094 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532094 : covered 532094 532159 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532159 : covered 532159 532224 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532224 : covered 532224 532290 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532290 : covered 532290 532355 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532355 : covered 532355 532420 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532420 : covered 532420 532485 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532485 : covered 532485 532551 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532551 : covered 532551 532616 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532616 : covered 532616 532681 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532681 : covered 532681 532746 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532746 : covered 532746 532812 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532812 : covered 532812 532877 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532877 : covered 532877 532942 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b532942 : covered 532942 533007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533007 : covered 533007 533072 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533072 : covered 533072 533137 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533137 : covered 533137 533202 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533202 : covered 533202 533267 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533267 : covered 533267 533333 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533333 : covered 533333 533398 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533398 : covered 533398 533463 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533463 : covered 533463 533528 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533528 : covered 533528 533594 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533594 : covered 533594 533659 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533659 : covered 533659 533724 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533724 : covered 533724 533789 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533789 : covered 533789 533855 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 520820 533855 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b520820 (joinCoverage b520885 b520950)) (joinCoverage b521015 (joinCoverage b521081 b521146))) (joinCoverage (joinCoverage b521211 (joinCoverage b521276 b521342)) (joinCoverage b521407 (joinCoverage b521472 b521537)))) (joinCoverage (joinCoverage (joinCoverage b521602 (joinCoverage b521667 b521732)) (joinCoverage b521797 (joinCoverage b521863 b521928))) (joinCoverage (joinCoverage b521993 (joinCoverage b522058 b522123)) (joinCoverage (joinCoverage b522188 b522253) (joinCoverage b522318 b522384))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b522449 (joinCoverage b522514 b522579)) (joinCoverage b522644 (joinCoverage b522709 b522774))) (joinCoverage (joinCoverage b522839 (joinCoverage b522905 b522970)) (joinCoverage b523035 (joinCoverage b523100 b523166)))) (joinCoverage (joinCoverage (joinCoverage b523231 (joinCoverage b523296 b523361)) (joinCoverage b523427 (joinCoverage b523492 b523557))) (joinCoverage (joinCoverage b523622 (joinCoverage b523687 b523752)) (joinCoverage (joinCoverage b523817 b523882) (joinCoverage b523948 b524013)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b524078 (joinCoverage b524143 b524209)) (joinCoverage b524274 (joinCoverage b524339 b524404))) (joinCoverage (joinCoverage b524470 (joinCoverage b524535 b524600)) (joinCoverage b524665 (joinCoverage b524730 b524795)))) (joinCoverage (joinCoverage (joinCoverage b524860 (joinCoverage b524925 b524991)) (joinCoverage b525056 (joinCoverage b525121 b525186))) (joinCoverage (joinCoverage b525252 (joinCoverage b525317 b525382)) (joinCoverage (joinCoverage b525447 b525513) (joinCoverage b525578 b525643))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b525708 (joinCoverage b525773 b525838)) (joinCoverage b525903 (joinCoverage b525968 b526034))) (joinCoverage (joinCoverage b526099 (joinCoverage b526164 b526229)) (joinCoverage b526294 (joinCoverage b526359 b526424)))) (joinCoverage (joinCoverage (joinCoverage b526489 (joinCoverage b526555 b526620)) (joinCoverage b526685 (joinCoverage b526750 b526815))) (joinCoverage (joinCoverage b526880 (joinCoverage b526945 b527010)) (joinCoverage (joinCoverage b527076 b527141) (joinCoverage b527206 b527271))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b527337 (joinCoverage b527402 b527467)) (joinCoverage b527532 (joinCoverage b527598 b527663))) (joinCoverage (joinCoverage b527728 (joinCoverage b527793 b527858)) (joinCoverage b527923 (joinCoverage b527988 b528053)))) (joinCoverage (joinCoverage (joinCoverage b528119 (joinCoverage b528184 b528249)) (joinCoverage b528314 (joinCoverage b528380 b528445))) (joinCoverage (joinCoverage b528510 (joinCoverage b528575 b528641)) (joinCoverage (joinCoverage b528706 b528771) (joinCoverage b528836 b528901))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b528966 (joinCoverage b529031 b529096)) (joinCoverage b529162 (joinCoverage b529227 b529292))) (joinCoverage (joinCoverage b529357 (joinCoverage b529423 b529488)) (joinCoverage b529553 (joinCoverage b529618 b529684)))) (joinCoverage (joinCoverage (joinCoverage b529749 (joinCoverage b529814 b529879)) (joinCoverage b529944 (joinCoverage b530009 b530074))) (joinCoverage (joinCoverage b530139 (joinCoverage b530205 b530270)) (joinCoverage (joinCoverage b530335 b530400) (joinCoverage b530465 b530530)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b530595 (joinCoverage b530660 b530726)) (joinCoverage b530791 (joinCoverage b530856 b530921))) (joinCoverage (joinCoverage b530986 (joinCoverage b531051 b531116)) (joinCoverage b531181 (joinCoverage b531247 b531312)))) (joinCoverage (joinCoverage (joinCoverage b531377 (joinCoverage b531442 b531508)) (joinCoverage b531573 (joinCoverage b531638 b531703))) (joinCoverage (joinCoverage b531769 (joinCoverage b531834 b531899)) (joinCoverage (joinCoverage b531964 b532029) (joinCoverage b532094 b532159))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b532224 (joinCoverage b532290 b532355)) (joinCoverage b532420 (joinCoverage b532485 b532551))) (joinCoverage (joinCoverage b532616 (joinCoverage b532681 b532746)) (joinCoverage b532812 (joinCoverage b532877 b532942)))) (joinCoverage (joinCoverage (joinCoverage b533007 (joinCoverage b533072 b533137)) (joinCoverage b533202 (joinCoverage b533267 b533333))) (joinCoverage (joinCoverage b533398 (joinCoverage b533463 b533528)) (joinCoverage (joinCoverage b533594 b533659) (joinCoverage b533724 b533789))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 520820 ≤ index 1000000000/512 := by decide +kernel
private theorem starting_value : fast 1000000000=50847534 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 1000000000=50847534) (n : ℕ) (low : 1000000000≤n) (bound : n≤1025000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=1000000000
    · rw [first,anchor]
      exact starting_value
    · have past : 1000000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤1025000000 by omega)
        have within : index n / 512 < 533855 := by omega
        have lower : index 1000000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤1025000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ1000000000To1025000000
