import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ1025000000To1050000000

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




private def radical : ℕ := 0x139bf43b902e7e6af9b7eb5c4e60f1c7b46849c2e37f268d36a059e60fca29e07c5885801092ed1518b6fc5674fc10a95309d26f5b4909245a1e5bc6e1e8f6b0043a758ade3a7f2ca523ea86b5449f93ca20362e5ef384b7bcb95781ec93fbd54a092527ed27e16a8ddd6bbe198ac5ca0b2c93a25e24ea968fe335b0b1ff5fcfc8f000f0dd828da3c008526d927bd084c73189133dce86a2636aefa747e4ca13db58aeaafafbff66bbdc22acef6db89244103f9b0c4310ccbacab5b8660b2553eb460cf53b7d6e1eaba823c5c4e148b27be137c54f71d1feeceb11aac9d1914a229c4fc8cd1222a40073dda3d5281236e7e68b2fed865062d2b17fcfd650d40b686c55ba4b6a3528971842000554e72ecad28b92635cc26ff312a69c27412f81afd0d440793cdc87a1da2de4b0adf64a8c4d14ca7de3ad7cdf99b3275ce2a465ff99e2070915be9c92cb02bd6020335976d7764b46e8295942c8bbfc3691f682d95ba71f219fb94df32c792e7fa68d2786f60292946a06fa5242d2db18d49174828f9a9be55095430415c630286d9ee7613068dac1b8c832896477d662d5e200f6a762482381e6857e85f4ce03d698d5ffb64e26a33bad6092718a1b9825e20ce2806511eba0215761d4199ed6059767d96f5554cc34183a04df0d1164895c9a4957ba6ecd3fa1eacab80ad5cd3c5380fd380d9d1189bc8472a549d5ed8386eab97599430b2b68e0c0871d1e7345410de708db6a242de5fd46e95badcc732a396cd039e3a9c6b630fad2ab1c4dfc938eccc3479d5255ed4df89e6ea80a9cd9dc233239476fa470b815c1c9055d2bf73236d192805d83bf626aee0b72f474b4d31dec1786ea949392ee4925c9a4c37981817108c38be7384820f2439f00f7f781393fdee80c9edb930947d2b242b270274addaa8c433a215fe42df392dcd7a52b50e7b69e41e47912b76afc3752097c52d624b3e99f5d01be18387cbb867067a473682fe12b86e429d9bd4a0f7365b414e7b0b5c9160c73801dbbfdad5241d0b9b4c2f461f15b05994b1a6b2eefae5ab8170feaa9669d98a89ca49067e94460080d667d345b48b1e5958c289bd89c280fababbb679a33dbb3d245e2c87b1c6ebdcef38133fcfeaec855da415fda9cc54394129f4a5a9ec76d62f5f9614abf3e12d371823f0bd6dc65a3db1338eeb3e96dba191bb5b00270e3a82df99ad063d52cc408da4271c50a94c2a903bd13e396a86f737a706a680debf54f292ed9ab83942ca7c7961223b9b6c310c044b522f79c95b0cbcc115a3e910804da83c297a07cab6ed23f2fe08a1427aa59089c786722a91db8b1c8178cb5a6617b2597e376928ec71b75252302c0b69889ff172daefd4e0fa655c54cc479a56116592b0e4087dcbbfd7b6e7f9c7421a57185edcb948dc022741223cb147b3ad94587c45f36a8c4fe052e4abbd3df099cc9f06d7fb1f6c8e5f67939505865835baa61a8944618751d2f7d2c061badb453ea210f87d518118f410ef9808d93c4d142e8e9745a5f43622229d2825556315948b7a0963ed82c93f23c130510aed01e6b9cec9efcfaf752ebc10778c01c263d50d143a15492537316620bdf80fd18839230eb11eab7e2c9612a9816dd45961bbfe3a388ff25724226d4524bbe05a50d259f69ba341fb0e6855d987c23539cd4b175c24ee7577c0e969013f99b9f97ff2b39d8e33e2036f7384cacb87becdbb012cf475773b044dc6268ef7da807efd57fd2ba3a84de15304d0726934aec94d73cfb6f4db7cf579ae213839d2d14b46576f3a1971e4b7d43dde6d5db7de7d967ea5ba7829360a3eac7d92fe4119396aea22353c596e510165806ac0cfef8dbfb757cbf9f3ac592d176a3d1614f7fd22094e453fd520213b9f883764ba7005f28c9fb17959e297878ee30c2021cab8f432903b697527a755f6b26bc4d936f02fce7f3e626b6129cc70f98a2546939047d5d99a45ee254a44f50037ba244fac90ad646ea57fb2886285cb3e6d299e70db4e9819cefda1fd8aa016547a71195e82dc3217f9ee27c4802f158c962f467a92f3cb243fe7179cedd23559f448f631f719f8631a9941910e1a239bce52ac353cfe479c1a7f8770df5be4953a361486d7fc661149f2b2898e3918cd1df8a8cb19963f4b69d12b8fc24372cadf23f1fe3d67e1de20b2b039c1c660f0f6f848249f2c810776b6b3ba854a7656017310057c986a93c8994d5544b6a2af3a0d8eaeb39665bc0ab1a2d2bfaaa8f9648f15e7dd1cd26d8a31eda56e94a63ce8d0e92aa4bed38da4d38f1f533b2d31e2702d352763a6e359793ad0028587ba1da125997981f2508e140bc9b942dab7085d6dfccf1df2ecd01a0d669b07d9579ace2673f18eefb8f3884f088d5d01a607fb6432b67dc4a6d089d6c7e72da977a17300af5fde3a592b485373227e971a8697568bb56cdfbf9a91d99b96762805d431b41805df89a864bae0e3a1ff98d3404d62edea4821c994131765ed1608d84d0bfa27872e92e2528be52dff25749adbb9473ec068e6da2bdb3a323255f2c089bc28159688ae07cbd731eb1d0383cbf9668cdd4cd839d954595c4e2d55c10978a073780598ad15211d90e3a4d10ace320af6dc6e9223b6c3815a258998cd22383e2b57c01af7c357fcdc63cf6907f79053876896c7f196edfe0c84b6488deacb5b947b7dddd552fe79a2e7dd40b8f4cb2338e5a285d945df6359420b7b3ceb1bfe9712ecf8526799a21c926a9f6e45e440a725327ab96d1bded3894c767dd1c57d9460c3d191d282b45feae30389986e29a9873ba4de4240bb507d4f6b7cb0579cbd67d65d42f379c772459d527c77aa84b7a7c57cc91741cde53e698b00f3ca48e1ae359f10fee49e45b01923bca90136e5e9aaba96925c58d954aae9ec6fbeb9fd72f7428226c5c73d935a65bb777af8eb3a52251f297dee3b012bd3e9f7dc74545fe0b4836729e4c7dadff4f6e1fc475c40327aa41280eb218c6af87d266b2106e06d6fc6fa46193d9e878f8aeb0a7f784155e9dd6abdb0e5acb7151631a6cf6b4652b314d7a93920e9a8137df1a8090d859723484d3bdcbcc83bb64d066afd4b812542f90a45a1d97fb502fa4bfe8b0c3735401738255464d9ab2f1ac5dd6e671e494975083a727859af6c1847d529e59002f9792964d7c05ddaa140916138151ce957a76a412baafb69070afbf533aade113c3d1651d3bc574de1cc87717b3d6e9eeaebe5c671a9d8fbb8bbc5d53b9a6485051c56ccb9f392aac33d941b417712d252dadadfe4726d10f529de232236c2fbe20024e2da8c038edc278dbfa8d2fe7b72ef029124d7fce4e3ea29a692e66256fa8c7ee3c7c27f6b8c3204daeab40345380eb25ea482582ec9158e50d9dcf6bd835378b6940d28f294dae37e317b6e29c80040e25872203472902d57534d1ec9509a4b577188ba52b00b0a5ea05937708f210b75abfdd5673cf09e3d9b084554b670817c27a92296ee3374fba4f26d72e2da4c7ef871ca8a319fe9e33d39b26b2bad4944626533739bc9777e25701781d2c51f1d3799b2b615bf864fcb5df3a5f47b894e585e58cb80e6dacd9f92e2db95ba35ca380623e107ec9a68c515db0fd5e9af03407b77f549c4fc2987fa81933d494ea114241600313cb5bbaf7801e05ff38e34d6aca6f1379b60bd78f07a40461a36e1f05db1ccd8b45c3d59e76e561b945746a76da25763de1ca5d4788beb71348a3c0bf9d5a07dfa7852d1d43b1efcadb0e399dea6d5a0b5a2a76e53b0acff07bfc5f3de8ecec4153ce827afa218f1a047cb8bef3283a0ae1280cbf2dbb2804b5865a13ee482dd18e500b984476ba53b1512764c394f0bcd24a5d898ec46c14300641dde18cd80598e97ddc94e2816ad50e778c4f5bd349f4100b836c0b43fbd2efab8b666f4157a015e9102f2f7b1f7c14dd4522d3a8a33e9bbb1aa50b541151104b5fcb9d63e5321f614b64db32e4940d340c6a623d49f94d2e8c4cc549c08200b429cebb040cde6c5eeb42c8daec9e2da1d34fb16d9d94fc5e29c2ded5c5b39681807cad30b750f7dd6d3600261ebf93aeeb306aaf901ef63bee7787ae36210e8e5e50aa7d70bb4adef1a7030a0d168ea9a6ebde4a8fa09c056fdfc1b58eb8c5aa5f7dafdf9fdc74c697268529a81d681bd2ba15d2ae2c1a4aa41563ca5db0d721e3aae004662c9215fdc9bfdf13ee503084e54cb2b32aec864953539ec4eff2460c98396e90a616c1e367fad2bd285ad9165435d385c7209f6d7a3cecda4d7bd4495bf1745bffe95cc7841f0c4efed10cae0200a69d509b452d216f5565a7b3e82ea325945c7a2465cb0e3d4b1e47d57f22fd24ad17588fdfd7a5ee55a4b3e1ba7c6617f86037f5d2ea7d0fdeda0aea4d57cc8840551f23ae14f13f07213fb3414a4f4e8b70b3acfcdb68db266bc77df8f81ce0ab9d89950f95929306bbf028468311e418507eabac9ef7e81d332243b52ea2e4899da0ebc4534f9569970757f45f78969c4b443d5e2ec94e4c3938a63eb780a7e85da9f3cc936fe68d0ae929db563671b4ea95fd80cce94f1af49b6f5570be25abab26ab792d7452088c71725790bd5d357cc03fe547953798ae301c6d9927441f455853169de96ada57d9e88770c83756e85da8c5d05aaeb93ed537924ea7c6292d4c000809ab84d01c06a9b2552468471146fc3779a4b6fab4f7e959b9bc1e06a05adf19acd8b1499a205db33fa622dc8ca689f65fdb2f708cd06fb0fc4d1deefc1e583a765732e23d95dbd14838b0b50fef67e70c08355f52bd78422006032ce869aa160d6b6826f4e2541bb4270cda478bc4802b62690fbc501088e5b0f799bad5b0338cb312e520e31baadacbe655c083407d3b8d29a41994587a7d7fb6381a93f0fee4167952666c34e0c1b06336dd572f9326b63418cc09778dde9cc0d532ed7bc1effaa263c8a878ae1f25a8f1894ae23216555d2209425a8f3ffdf17c5436cfe71a6c838fb3ae6f5c439fa9cb3be20b1bee4e62210271e07ba83ff210af19a4a8361903511c2feaf9fe6b6bf7509022f675b3e11f8916faf0f1c54d201adbba705c51e8b988a0afd44868d5a2c211a181a1a0170c55db35003787398ddc83ff3410e4169f4f2f91f266105a3a3399576b84aeed89767ff231b60300cd850a61fd142825aa6a70d4b3069cac9b4ba5cda5cce334b96f2723e18c4efa3e9c5d20f1dcccd32f25f717bf0a837782c49a5eb85f76ca5a609e683198ecfa8abca08266db1b30131db8e677cee5425dbf496a77213c9f2d3237a4ec767658fd14fbc1bcd3dfafc4c65d98b864c5928040c69a60babc835b0d19e39a2c5c45f3fa9643be4d9742e5f1061123da7633e73e13572b715c83627fadb4c5beacd246bac9e06fb9f09c6c9adb4add44fd6e311d338d55694d27f331e419e0ba640881e6ecef6eb83c2822f42ab524230751bf98d672aac49737477c44e58dcb11ef629e6a7414ad1fc5d9aafe93d605e31c8f4575f13261952cfac9641b99d57b39f5bc3e0baed75447ffe77c97f7303738e13844fa7b1a36102c7d1d77e4c982ad9d2be71c0b798578031f65aa19ec0b9460eb0292c39298384d7376f5c2f1f16c1adbaa7b96c6810afba5db1e6478fe3772da3fbd7e7ea9b1b96c75150897d5bcdbcbf14a177a6ef83f62da41dceab0a189cb4082a2458c149459fb1926918b14af3c83bf6c3d2cb6f7d9bf5e3197b655b44794a4afbd735d6c4cd6cdb63291dbf782fc3dffdfb69be1e425dcf0fc13c50d8ae2a8df8cd173a92cbcb72decb709ad18bfcd1d36284a6b86ccbe3ac4b980e82d31284beb9c38e1f1adbae3ce0217c263eb2c7b72eaf27db308d377bbdbc04c8a539cfbc6f9b831a39be75ec29c1d8a267b5d8e82cfab3f9ac2f554469003da185a81356637ad0a48b94d0ac5e84e54ff78c466f62fe978195afa0ad08fe8c9e48954d75794e9ff4fedd51d71dcb4cd3709da792afacd7bbb096e5a8fd2e2651e7b75b1875ebc42d22164860026f351fdbf23e87f12b681736c74b011ba2a4028c1619c5b373d671fbc1278621864c8f8981085d90014c395c258fb64e7b99b957b58978e1208054d3a4664e4e4c5eb292f3a0c06aaa44041c70b2d69d3bb0f5614423852c4270d6563f362a40b1535551846c502425a85f19d9a58ecc3704b1f5c35fe6908362e3404f568627b209a8e8c42cf23c5c480b0d954a5f9e489268e0548fcbaf69a170ddf1de3b435a229035ebc2457c8934174cf985459466cb1578837f6a24ec39d5bfb9533c74d374a3e5ce125134c5ab1df7c663d28a024f27253023168d75de4cc778475219a9ea27593ca03bbd57b1a7227ff7910a680158d2852f48f19cc0f6ea613e6dfbed6b37fe85e64ddf8509c766ef3344f89c47615084bb3d47f79333a72bdfeca79e3a08736c8ac904f7b02fca6745fe12ca789d8481ed8986d767f592b7a5a922b623dd112814cdb0e095e0a1a95e2e699d4cbacb3cf2adb29bf9041745efef1b1a77053ed2b89fc6f40a37bae136216aac7ca63cbd539818c4590eea9a831ce965f8b9eb713bd3d10b5611008bd7d2341ee4c17f152f4ecb8a311ceeba18c90d8b8cf893ce882c6b7f14ff3a19089c4532abc868d3b69322ac4554c4f9aa8b58fb9c151c3a0d25cb72dba5b94df7e7934b11b0dc91c3ee3c5c2094d43cfb0d3b1b530c4232f166c289aaed22f5841bb04cfa7e99a25a9cc9243a2c7c50fd17a715d8405cc45e3ba7d0c3b0446c1ecbc40282b9d8791f70a868e653d4495c6a73740e93e9fe6f54f1a5b968d4491e019207cc4fa2cc72922bc4ed64623002e82fa87bd1e62ee9ec43bd3a5b1bb6e0d60bedb83ea744f76bce37faa673200d354827a7b30a6eb188174ee5e1e7a18d6482b9744c45675c129665fc085d612720ddd691c7a2edfd604f2e2f719323d468ef714d49dd59ab8d15064d251e73fd98ad0d43e7f334b68a10ae4ee1ac4fdb37afbb36da4d556260a5ee98c470c66841af383c8df7a779128b9445e4602ee32f5ad33eeb0d00cacde3b38f4d3cd6fcbab9e20ca05ef02b5a153c18f1ca45d4e211df2a62eb3cbdf71af863c5693c91dd48d1bc92ddd29cd49485565ee2faf9156c062d1ba74e13f628bd0c469fa4b1f7b8b2b44083488c5709a153b9736c13787bc4b02a7a2cbab400d4b3d5df74a00bd9b48652f8920110d7d94dc8bf187c563da8e9b5eba14e8b993c69395da2c67d08fe2d22bfdc6e6fdb658e859eb6cc117da5aaa12d6976a066bf9b355766ee351fca9f219b8d0c18e1d0b4dec7ed2b1c642b37b8e039133eba300a44253ff82efc4923b1f8f96f4f41f793857e2cdc6a65a20429da565ef2085e02646a5e2b13111f969b3fb24bc0a6641b7ce9eef01cfe24d41092040031335c7094e71458ed9f14d4a8ba5dcbc1915a74214affc79fc317a0df84f9430961812804141095f81270b743640ef8f679ca8e8e6b2a9c0b0a016dd0cd5c86fa0348db628a3ed291950ca9939fc778ff68a1e2f009b116866e6c5bc14431e57a757e5ccc677380d48ce8c68e78fa971685e4663c5e3466f1199050bc9e55e120b513ba954ca5bd090b28be6e87b4816c0b0c4978a371f17b77f37861735a688c447c71b8352e0daf3657b0c06fb99978c3f211e0e29ec15442f090bbd000880ecf30969379564bb56ca58a6f0660a59c447e6b8e12b45ae748b76d69070821ca9e881a9de1e811ad1d77214d98fae30cc3c0418d14126913b2783f35193c3e5f5def759b407886c7c1033db0de9d82cf707f011d6e7853ee2a389f1ca1986f8989c93f73fc0b8dadc626613726a92e2d42293417cb74649f8b8aa4b17a46dbf31e5863600aa266f9b1a21166a3956b2e519e3edb15bc2c3feb92b799a5982422ba4ee5e4416b2357cf2a479c831d7fd1db68216ed844b3b42b9ec0c531dd11a8c930e4162aa773bccfdf30e0806654818f7a2c156a44ddb14b356a3d4d71bbb9161dad5b573cb11d1462dd64dafaa3f2a06a1dcdafbb3bcb5393100a56c65e7f3f0abab65f01f9c08eb6acff482450c7f4e4e552d3450908879735e5ce6fbea2c7922b35aca2efb50a2469bf2e2b0eb72be825938c52cdc4d176e8e5c875111100666915ac110fa5383964e03c15b71f3660502838cc630f74cadf05f0b914ce

private def light (n : ℕ) : Bool :=
  if n≤180 then decide n.Prime else n.gcd 200896062499134299656951336898466838917540340798867777940435335160044860953395980941180138112097309735631594101037399609671032132186331495273609598531966730972945653558819806475064353856858157445040809209560358463319644664891114256430017824141796753818192338642302693327818731986039603200000000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤32403) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 180 = 200896062499134299656951336898466838917540340798867777940435335160044860953395980941180138112097309735631594101037399609671032132186331495273609598531966730972945653558819806475064353856858157445040809209560358463319644664891114256430017824141796753818192338642302693327818731986039603200000000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 180 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤32403 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 63 := by unfold smallValid; decide +kernel

private theorem sp63 : smallValid 63 63 := by unfold smallValid; decide +kernel

private theorem sp126 : smallValid 126 63 := by unfold smallValid; decide +kernel

private theorem sp189 : smallValid 189 64 := by unfold smallValid; decide +kernel

private theorem sp253 : smallValid 253 63 := by unfold smallValid; decide +kernel

private theorem sp316 : smallValid 316 63 := by unfold smallValid; decide +kernel

private theorem sp379 : smallValid 379 63 := by unfold smallValid; decide +kernel

private theorem sp442 : smallValid 442 64 := by unfold smallValid; decide +kernel

private theorem sp506 : smallValid 506 63 := by unfold smallValid; decide +kernel

private theorem sp569 : smallValid 569 63 := by unfold smallValid; decide +kernel

private theorem sp632 : smallValid 632 63 := by unfold smallValid; decide +kernel

private theorem sp695 : smallValid 695 64 := by unfold smallValid; decide +kernel

private theorem sp759 : smallValid 759 63 := by unfold smallValid; decide +kernel

private theorem sp822 : smallValid 822 63 := by unfold smallValid; decide +kernel

private theorem sp885 : smallValid 885 63 := by unfold smallValid; decide +kernel

private theorem sp948 : smallValid 948 64 := by unfold smallValid; decide +kernel

private theorem sp1012 : smallValid 1012 63 := by unfold smallValid; decide +kernel

private theorem sp1075 : smallValid 1075 63 := by unfold smallValid; decide +kernel

private theorem sp1138 : smallValid 1138 63 := by unfold smallValid; decide +kernel

private theorem sp1201 : smallValid 1201 64 := by unfold smallValid; decide +kernel

private theorem sp1265 : smallValid 1265 63 := by unfold smallValid; decide +kernel

private theorem sp1328 : smallValid 1328 63 := by unfold smallValid; decide +kernel

private theorem sp1391 : smallValid 1391 63 := by unfold smallValid; decide +kernel

private theorem sp1454 : smallValid 1454 64 := by unfold smallValid; decide +kernel

private theorem sp1518 : smallValid 1518 63 := by unfold smallValid; decide +kernel

private theorem sp1581 : smallValid 1581 63 := by unfold smallValid; decide +kernel

private theorem sp1644 : smallValid 1644 63 := by unfold smallValid; decide +kernel

private theorem sp1707 : smallValid 1707 64 := by unfold smallValid; decide +kernel

private theorem sp1771 : smallValid 1771 63 := by unfold smallValid; decide +kernel

private theorem sp1834 : smallValid 1834 64 := by unfold smallValid; decide +kernel

private theorem sp1898 : smallValid 1898 63 := by unfold smallValid; decide +kernel

private theorem sp1961 : smallValid 1961 64 := by unfold smallValid; decide +kernel

private theorem sp2025 : smallValid 2025 63 := by unfold smallValid; decide +kernel

private theorem sp2088 : smallValid 2088 63 := by unfold smallValid; decide +kernel

private theorem sp2151 : smallValid 2151 63 := by unfold smallValid; decide +kernel

private theorem sp2214 : smallValid 2214 64 := by unfold smallValid; decide +kernel

private theorem sp2278 : smallValid 2278 63 := by unfold smallValid; decide +kernel

private theorem sp2341 : smallValid 2341 63 := by unfold smallValid; decide +kernel

private theorem sp2404 : smallValid 2404 63 := by unfold smallValid; decide +kernel

private theorem sp2467 : smallValid 2467 64 := by unfold smallValid; decide +kernel

private theorem sp2531 : smallValid 2531 63 := by unfold smallValid; decide +kernel

private theorem sp2594 : smallValid 2594 63 := by unfold smallValid; decide +kernel

private theorem sp2657 : smallValid 2657 63 := by unfold smallValid; decide +kernel

private theorem sp2720 : smallValid 2720 64 := by unfold smallValid; decide +kernel

private theorem sp2784 : smallValid 2784 63 := by unfold smallValid; decide +kernel

private theorem sp2847 : smallValid 2847 63 := by unfold smallValid; decide +kernel

private theorem sp2910 : smallValid 2910 63 := by unfold smallValid; decide +kernel

private theorem sp2973 : smallValid 2973 64 := by unfold smallValid; decide +kernel

private theorem sp3037 : smallValid 3037 63 := by unfold smallValid; decide +kernel

private theorem sp3100 : smallValid 3100 63 := by unfold smallValid; decide +kernel

private theorem sp3163 : smallValid 3163 63 := by unfold smallValid; decide +kernel

private theorem sp3226 : smallValid 3226 64 := by unfold smallValid; decide +kernel

private theorem sp3290 : smallValid 3290 63 := by unfold smallValid; decide +kernel

private theorem sp3353 : smallValid 3353 63 := by unfold smallValid; decide +kernel

private theorem sp3416 : smallValid 3416 63 := by unfold smallValid; decide +kernel

private theorem sp3479 : smallValid 3479 64 := by unfold smallValid; decide +kernel

private theorem sp3543 : smallValid 3543 63 := by unfold smallValid; decide +kernel

private theorem sp3606 : smallValid 3606 63 := by unfold smallValid; decide +kernel

private theorem sp3669 : smallValid 3669 63 := by unfold smallValid; decide +kernel

private theorem sp3732 : smallValid 3732 64 := by unfold smallValid; decide +kernel

private theorem sp3796 : smallValid 3796 63 := by unfold smallValid; decide +kernel

private theorem sp3859 : smallValid 3859 64 := by unfold smallValid; decide +kernel

private theorem sp3923 : smallValid 3923 63 := by unfold smallValid; decide +kernel

private theorem sp3986 : smallValid 3986 64 := by unfold smallValid; decide +kernel

private theorem sp4050 : smallValid 4050 63 := by unfold smallValid; decide +kernel

private theorem sp4113 : smallValid 4113 63 := by unfold smallValid; decide +kernel

private theorem sp4176 : smallValid 4176 63 := by unfold smallValid; decide +kernel

private theorem sp4239 : smallValid 4239 64 := by unfold smallValid; decide +kernel

private theorem sp4303 : smallValid 4303 63 := by unfold smallValid; decide +kernel

private theorem sp4366 : smallValid 4366 63 := by unfold smallValid; decide +kernel

private theorem sp4429 : smallValid 4429 63 := by unfold smallValid; decide +kernel

private theorem sp4492 : smallValid 4492 64 := by unfold smallValid; decide +kernel

private theorem sp4556 : smallValid 4556 63 := by unfold smallValid; decide +kernel

private theorem sp4619 : smallValid 4619 63 := by unfold smallValid; decide +kernel

private theorem sp4682 : smallValid 4682 63 := by unfold smallValid; decide +kernel

private theorem sp4745 : smallValid 4745 64 := by unfold smallValid; decide +kernel

private theorem sp4809 : smallValid 4809 63 := by unfold smallValid; decide +kernel

private theorem sp4872 : smallValid 4872 63 := by unfold smallValid; decide +kernel

private theorem sp4935 : smallValid 4935 63 := by unfold smallValid; decide +kernel

private theorem sp4998 : smallValid 4998 64 := by unfold smallValid; decide +kernel

private theorem sp5062 : smallValid 5062 63 := by unfold smallValid; decide +kernel

private theorem sp5125 : smallValid 5125 63 := by unfold smallValid; decide +kernel

private theorem sp5188 : smallValid 5188 63 := by unfold smallValid; decide +kernel

private theorem sp5251 : smallValid 5251 64 := by unfold smallValid; decide +kernel

private theorem sp5315 : smallValid 5315 63 := by unfold smallValid; decide +kernel

private theorem sp5378 : smallValid 5378 63 := by unfold smallValid; decide +kernel

private theorem sp5441 : smallValid 5441 63 := by unfold smallValid; decide +kernel

private theorem sp5504 : smallValid 5504 64 := by unfold smallValid; decide +kernel

private theorem sp5568 : smallValid 5568 63 := by unfold smallValid; decide +kernel

private theorem sp5631 : smallValid 5631 63 := by unfold smallValid; decide +kernel

private theorem sp5694 : smallValid 5694 63 := by unfold smallValid; decide +kernel

private theorem sp5757 : smallValid 5757 64 := by unfold smallValid; decide +kernel

private theorem sp5821 : smallValid 5821 63 := by unfold smallValid; decide +kernel

private theorem sp5884 : smallValid 5884 64 := by unfold smallValid; decide +kernel

private theorem sp5948 : smallValid 5948 63 := by unfold smallValid; decide +kernel

private theorem sp6011 : smallValid 6011 64 := by unfold smallValid; decide +kernel

private theorem sp6075 : smallValid 6075 63 := by unfold smallValid; decide +kernel

private theorem sp6138 : smallValid 6138 63 := by unfold smallValid; decide +kernel

private theorem sp6201 : smallValid 6201 63 := by unfold smallValid; decide +kernel

private theorem sp6264 : smallValid 6264 64 := by unfold smallValid; decide +kernel

private theorem sp6328 : smallValid 6328 63 := by unfold smallValid; decide +kernel

private theorem sp6391 : smallValid 6391 63 := by unfold smallValid; decide +kernel

private theorem sp6454 : smallValid 6454 63 := by unfold smallValid; decide +kernel

private theorem sp6517 : smallValid 6517 64 := by unfold smallValid; decide +kernel

private theorem sp6581 : smallValid 6581 63 := by unfold smallValid; decide +kernel

private theorem sp6644 : smallValid 6644 63 := by unfold smallValid; decide +kernel

private theorem sp6707 : smallValid 6707 63 := by unfold smallValid; decide +kernel

private theorem sp6770 : smallValid 6770 64 := by unfold smallValid; decide +kernel

private theorem sp6834 : smallValid 6834 63 := by unfold smallValid; decide +kernel

private theorem sp6897 : smallValid 6897 64 := by unfold smallValid; decide +kernel

private theorem sp6961 : smallValid 6961 63 := by unfold smallValid; decide +kernel

private theorem sp7024 : smallValid 7024 64 := by unfold smallValid; decide +kernel

private theorem sp7088 : smallValid 7088 63 := by unfold smallValid; decide +kernel

private theorem sp7151 : smallValid 7151 63 := by unfold smallValid; decide +kernel

private theorem sp7214 : smallValid 7214 63 := by unfold smallValid; decide +kernel

private theorem sp7277 : smallValid 7277 64 := by unfold smallValid; decide +kernel

private theorem sp7341 : smallValid 7341 63 := by unfold smallValid; decide +kernel

private theorem sp7404 : smallValid 7404 63 := by unfold smallValid; decide +kernel

private theorem sp7467 : smallValid 7467 63 := by unfold smallValid; decide +kernel

private theorem sp7530 : smallValid 7530 64 := by unfold smallValid; decide +kernel

private theorem sp7594 : smallValid 7594 63 := by unfold smallValid; decide +kernel

private theorem sp7657 : smallValid 7657 63 := by unfold smallValid; decide +kernel

private theorem sp7720 : smallValid 7720 63 := by unfold smallValid; decide +kernel

private theorem sp7783 : smallValid 7783 64 := by unfold smallValid; decide +kernel

private theorem sp7847 : smallValid 7847 63 := by unfold smallValid; decide +kernel

private theorem sp7910 : smallValid 7910 64 := by unfold smallValid; decide +kernel

private theorem sp7974 : smallValid 7974 63 := by unfold smallValid; decide +kernel

private theorem sp8037 : smallValid 8037 64 := by unfold smallValid; decide +kernel

private theorem sp8101 : smallValid 8101 63 := by unfold smallValid; decide +kernel

private theorem sp8164 : smallValid 8164 63 := by unfold smallValid; decide +kernel

private theorem sp8227 : smallValid 8227 63 := by unfold smallValid; decide +kernel

private theorem sp8290 : smallValid 8290 64 := by unfold smallValid; decide +kernel

private theorem sp8354 : smallValid 8354 63 := by unfold smallValid; decide +kernel

private theorem sp8417 : smallValid 8417 63 := by unfold smallValid; decide +kernel

private theorem sp8480 : smallValid 8480 63 := by unfold smallValid; decide +kernel

private theorem sp8543 : smallValid 8543 64 := by unfold smallValid; decide +kernel

private theorem sp8607 : smallValid 8607 63 := by unfold smallValid; decide +kernel

private theorem sp8670 : smallValid 8670 63 := by unfold smallValid; decide +kernel

private theorem sp8733 : smallValid 8733 63 := by unfold smallValid; decide +kernel

private theorem sp8796 : smallValid 8796 64 := by unfold smallValid; decide +kernel

private theorem sp8860 : smallValid 8860 63 := by unfold smallValid; decide +kernel

private theorem sp8923 : smallValid 8923 63 := by unfold smallValid; decide +kernel

private theorem sp8986 : smallValid 8986 63 := by unfold smallValid; decide +kernel

private theorem sp9049 : smallValid 9049 64 := by unfold smallValid; decide +kernel

private theorem sp9113 : smallValid 9113 63 := by unfold smallValid; decide +kernel

private theorem sp9176 : smallValid 9176 63 := by unfold smallValid; decide +kernel

private theorem sp9239 : smallValid 9239 63 := by unfold smallValid; decide +kernel

private theorem sp9302 : smallValid 9302 64 := by unfold smallValid; decide +kernel

private theorem sp9366 : smallValid 9366 63 := by unfold smallValid; decide +kernel

private theorem sp9429 : smallValid 9429 63 := by unfold smallValid; decide +kernel

private theorem sp9492 : smallValid 9492 63 := by unfold smallValid; decide +kernel

private theorem sp9555 : smallValid 9555 64 := by unfold smallValid; decide +kernel

private theorem sp9619 : smallValid 9619 63 := by unfold smallValid; decide +kernel

private theorem sp9682 : smallValid 9682 63 := by unfold smallValid; decide +kernel

private theorem sp9745 : smallValid 9745 63 := by unfold smallValid; decide +kernel

private theorem sp9808 : smallValid 9808 64 := by unfold smallValid; decide +kernel

private theorem sp9872 : smallValid 9872 63 := by unfold smallValid; decide +kernel

private theorem sp9935 : smallValid 9935 64 := by unfold smallValid; decide +kernel

private theorem sp9999 : smallValid 9999 63 := by unfold smallValid; decide +kernel

private theorem sp10062 : smallValid 10062 64 := by unfold smallValid; decide +kernel

private theorem sp10126 : smallValid 10126 63 := by unfold smallValid; decide +kernel

private theorem sp10189 : smallValid 10189 63 := by unfold smallValid; decide +kernel

private theorem sp10252 : smallValid 10252 63 := by unfold smallValid; decide +kernel

private theorem sp10315 : smallValid 10315 64 := by unfold smallValid; decide +kernel

private theorem sp10379 : smallValid 10379 63 := by unfold smallValid; decide +kernel

private theorem sp10442 : smallValid 10442 63 := by unfold smallValid; decide +kernel

private theorem sp10505 : smallValid 10505 63 := by unfold smallValid; decide +kernel

private theorem sp10568 : smallValid 10568 64 := by unfold smallValid; decide +kernel

private theorem sp10632 : smallValid 10632 63 := by unfold smallValid; decide +kernel

private theorem sp10695 : smallValid 10695 63 := by unfold smallValid; decide +kernel

private theorem sp10758 : smallValid 10758 63 := by unfold smallValid; decide +kernel

private theorem sp10821 : smallValid 10821 64 := by unfold smallValid; decide +kernel

private theorem sp10885 : smallValid 10885 63 := by unfold smallValid; decide +kernel

private theorem sp10948 : smallValid 10948 63 := by unfold smallValid; decide +kernel

private theorem sp11011 : smallValid 11011 63 := by unfold smallValid; decide +kernel

private theorem sp11074 : smallValid 11074 64 := by unfold smallValid; decide +kernel

private theorem sp11138 : smallValid 11138 63 := by unfold smallValid; decide +kernel

private theorem sp11201 : smallValid 11201 63 := by unfold smallValid; decide +kernel

private theorem sp11264 : smallValid 11264 63 := by unfold smallValid; decide +kernel

private theorem sp11327 : smallValid 11327 64 := by unfold smallValid; decide +kernel

private theorem sp11391 : smallValid 11391 63 := by unfold smallValid; decide +kernel

private theorem sp11454 : smallValid 11454 63 := by unfold smallValid; decide +kernel

private theorem sp11517 : smallValid 11517 63 := by unfold smallValid; decide +kernel

private theorem sp11580 : smallValid 11580 64 := by unfold smallValid; decide +kernel

private theorem sp11644 : smallValid 11644 63 := by unfold smallValid; decide +kernel

private theorem sp11707 : smallValid 11707 63 := by unfold smallValid; decide +kernel

private theorem sp11770 : smallValid 11770 63 := by unfold smallValid; decide +kernel

private theorem sp11833 : smallValid 11833 64 := by unfold smallValid; decide +kernel

private theorem sp11897 : smallValid 11897 63 := by unfold smallValid; decide +kernel

private theorem sp11960 : smallValid 11960 64 := by unfold smallValid; decide +kernel

private theorem sp12024 : smallValid 12024 63 := by unfold smallValid; decide +kernel

private theorem sp12087 : smallValid 12087 64 := by unfold smallValid; decide +kernel

private theorem sp12151 : smallValid 12151 63 := by unfold smallValid; decide +kernel

private theorem sp12214 : smallValid 12214 63 := by unfold smallValid; decide +kernel

private theorem sp12277 : smallValid 12277 63 := by unfold smallValid; decide +kernel

private theorem sp12340 : smallValid 12340 64 := by unfold smallValid; decide +kernel

private theorem sp12404 : smallValid 12404 63 := by unfold smallValid; decide +kernel

private theorem sp12467 : smallValid 12467 63 := by unfold smallValid; decide +kernel

private theorem sp12530 : smallValid 12530 63 := by unfold smallValid; decide +kernel

private theorem sp12593 : smallValid 12593 64 := by unfold smallValid; decide +kernel

private theorem sp12657 : smallValid 12657 63 := by unfold smallValid; decide +kernel

private theorem sp12720 : smallValid 12720 63 := by unfold smallValid; decide +kernel

private theorem sp12783 : smallValid 12783 63 := by unfold smallValid; decide +kernel

private theorem sp12846 : smallValid 12846 64 := by unfold smallValid; decide +kernel

private theorem sp12910 : smallValid 12910 63 := by unfold smallValid; decide +kernel

private theorem sp12973 : smallValid 12973 63 := by unfold smallValid; decide +kernel

private theorem sp13036 : smallValid 13036 63 := by unfold smallValid; decide +kernel

private theorem sp13099 : smallValid 13099 64 := by unfold smallValid; decide +kernel

private theorem sp13163 : smallValid 13163 63 := by unfold smallValid; decide +kernel

private theorem sp13226 : smallValid 13226 63 := by unfold smallValid; decide +kernel

private theorem sp13289 : smallValid 13289 63 := by unfold smallValid; decide +kernel

private theorem sp13352 : smallValid 13352 64 := by unfold smallValid; decide +kernel

private theorem sp13416 : smallValid 13416 63 := by unfold smallValid; decide +kernel

private theorem sp13479 : smallValid 13479 63 := by unfold smallValid; decide +kernel

private theorem sp13542 : smallValid 13542 63 := by unfold smallValid; decide +kernel

private theorem sp13605 : smallValid 13605 64 := by unfold smallValid; decide +kernel

private theorem sp13669 : smallValid 13669 63 := by unfold smallValid; decide +kernel

private theorem sp13732 : smallValid 13732 63 := by unfold smallValid; decide +kernel

private theorem sp13795 : smallValid 13795 63 := by unfold smallValid; decide +kernel

private theorem sp13858 : smallValid 13858 64 := by unfold smallValid; decide +kernel

private theorem sp13922 : smallValid 13922 63 := by unfold smallValid; decide +kernel

private theorem sp13985 : smallValid 13985 64 := by unfold smallValid; decide +kernel

private theorem sp14049 : smallValid 14049 63 := by unfold smallValid; decide +kernel

private theorem sp14112 : smallValid 14112 64 := by unfold smallValid; decide +kernel

private theorem sp14176 : smallValid 14176 63 := by unfold smallValid; decide +kernel

private theorem sp14239 : smallValid 14239 63 := by unfold smallValid; decide +kernel

private theorem sp14302 : smallValid 14302 63 := by unfold smallValid; decide +kernel

private theorem sp14365 : smallValid 14365 64 := by unfold smallValid; decide +kernel

private theorem sp14429 : smallValid 14429 63 := by unfold smallValid; decide +kernel

private theorem sp14492 : smallValid 14492 63 := by unfold smallValid; decide +kernel

private theorem sp14555 : smallValid 14555 63 := by unfold smallValid; decide +kernel

private theorem sp14618 : smallValid 14618 64 := by unfold smallValid; decide +kernel

private theorem sp14682 : smallValid 14682 63 := by unfold smallValid; decide +kernel

private theorem sp14745 : smallValid 14745 63 := by unfold smallValid; decide +kernel

private theorem sp14808 : smallValid 14808 63 := by unfold smallValid; decide +kernel

private theorem sp14871 : smallValid 14871 64 := by unfold smallValid; decide +kernel

private theorem sp14935 : smallValid 14935 63 := by unfold smallValid; decide +kernel

private theorem sp14998 : smallValid 14998 64 := by unfold smallValid; decide +kernel

private theorem sp15062 : smallValid 15062 63 := by unfold smallValid; decide +kernel

private theorem sp15125 : smallValid 15125 64 := by unfold smallValid; decide +kernel

private theorem sp15189 : smallValid 15189 63 := by unfold smallValid; decide +kernel

private theorem sp15252 : smallValid 15252 63 := by unfold smallValid; decide +kernel

private theorem sp15315 : smallValid 15315 63 := by unfold smallValid; decide +kernel

private theorem sp15378 : smallValid 15378 64 := by unfold smallValid; decide +kernel

private theorem sp15442 : smallValid 15442 63 := by unfold smallValid; decide +kernel

private theorem sp15505 : smallValid 15505 63 := by unfold smallValid; decide +kernel

private theorem sp15568 : smallValid 15568 63 := by unfold smallValid; decide +kernel

private theorem sp15631 : smallValid 15631 64 := by unfold smallValid; decide +kernel

private theorem sp15695 : smallValid 15695 63 := by unfold smallValid; decide +kernel

private theorem sp15758 : smallValid 15758 63 := by unfold smallValid; decide +kernel

private theorem sp15821 : smallValid 15821 63 := by unfold smallValid; decide +kernel

private theorem sp15884 : smallValid 15884 64 := by unfold smallValid; decide +kernel

private theorem sp15948 : smallValid 15948 63 := by unfold smallValid; decide +kernel

private theorem sp16011 : smallValid 16011 64 := by unfold smallValid; decide +kernel

private theorem sp16075 : smallValid 16075 63 := by unfold smallValid; decide +kernel

private theorem sp16138 : smallValid 16138 64 := by unfold smallValid; decide +kernel

private theorem sp16202 : smallValid 16202 63 := by unfold smallValid; decide +kernel

private theorem sp16265 : smallValid 16265 63 := by unfold smallValid; decide +kernel

private theorem sp16328 : smallValid 16328 63 := by unfold smallValid; decide +kernel

private theorem sp16391 : smallValid 16391 64 := by unfold smallValid; decide +kernel

private theorem sp16455 : smallValid 16455 63 := by unfold smallValid; decide +kernel

private theorem sp16518 : smallValid 16518 63 := by unfold smallValid; decide +kernel

private theorem sp16581 : smallValid 16581 63 := by unfold smallValid; decide +kernel

private theorem sp16644 : smallValid 16644 64 := by unfold smallValid; decide +kernel

private theorem sp16708 : smallValid 16708 63 := by unfold smallValid; decide +kernel

private theorem sp16771 : smallValid 16771 63 := by unfold smallValid; decide +kernel

private theorem sp16834 : smallValid 16834 63 := by unfold smallValid; decide +kernel

private theorem sp16897 : smallValid 16897 64 := by unfold smallValid; decide +kernel

private theorem sp16961 : smallValid 16961 63 := by unfold smallValid; decide +kernel

private theorem sp17024 : smallValid 17024 63 := by unfold smallValid; decide +kernel

private theorem sp17087 : smallValid 17087 63 := by unfold smallValid; decide +kernel

private theorem sp17150 : smallValid 17150 64 := by unfold smallValid; decide +kernel

private theorem sp17214 : smallValid 17214 63 := by unfold smallValid; decide +kernel

private theorem sp17277 : smallValid 17277 63 := by unfold smallValid; decide +kernel

private theorem sp17340 : smallValid 17340 63 := by unfold smallValid; decide +kernel

private theorem sp17403 : smallValid 17403 64 := by unfold smallValid; decide +kernel

private theorem sp17467 : smallValid 17467 63 := by unfold smallValid; decide +kernel

private theorem sp17530 : smallValid 17530 63 := by unfold smallValid; decide +kernel

private theorem sp17593 : smallValid 17593 63 := by unfold smallValid; decide +kernel

private theorem sp17656 : smallValid 17656 64 := by unfold smallValid; decide +kernel

private theorem sp17720 : smallValid 17720 63 := by unfold smallValid; decide +kernel

private theorem sp17783 : smallValid 17783 63 := by unfold smallValid; decide +kernel

private theorem sp17846 : smallValid 17846 63 := by unfold smallValid; decide +kernel

private theorem sp17909 : smallValid 17909 64 := by unfold smallValid; decide +kernel

private theorem sp17973 : smallValid 17973 63 := by unfold smallValid; decide +kernel

private theorem sp18036 : smallValid 18036 64 := by unfold smallValid; decide +kernel

private theorem sp18100 : smallValid 18100 63 := by unfold smallValid; decide +kernel

private theorem sp18163 : smallValid 18163 64 := by unfold smallValid; decide +kernel

private theorem sp18227 : smallValid 18227 63 := by unfold smallValid; decide +kernel

private theorem sp18290 : smallValid 18290 63 := by unfold smallValid; decide +kernel

private theorem sp18353 : smallValid 18353 63 := by unfold smallValid; decide +kernel

private theorem sp18416 : smallValid 18416 64 := by unfold smallValid; decide +kernel

private theorem sp18480 : smallValid 18480 63 := by unfold smallValid; decide +kernel

private theorem sp18543 : smallValid 18543 63 := by unfold smallValid; decide +kernel

private theorem sp18606 : smallValid 18606 63 := by unfold smallValid; decide +kernel

private theorem sp18669 : smallValid 18669 64 := by unfold smallValid; decide +kernel

private theorem sp18733 : smallValid 18733 63 := by unfold smallValid; decide +kernel

private theorem sp18796 : smallValid 18796 63 := by unfold smallValid; decide +kernel

private theorem sp18859 : smallValid 18859 63 := by unfold smallValid; decide +kernel

private theorem sp18922 : smallValid 18922 64 := by unfold smallValid; decide +kernel

private theorem sp18986 : smallValid 18986 63 := by unfold smallValid; decide +kernel

private theorem sp19049 : smallValid 19049 63 := by unfold smallValid; decide +kernel

private theorem sp19112 : smallValid 19112 63 := by unfold smallValid; decide +kernel

private theorem sp19175 : smallValid 19175 64 := by unfold smallValid; decide +kernel

private theorem sp19239 : smallValid 19239 63 := by unfold smallValid; decide +kernel

private theorem sp19302 : smallValid 19302 63 := by unfold smallValid; decide +kernel

private theorem sp19365 : smallValid 19365 63 := by unfold smallValid; decide +kernel

private theorem sp19428 : smallValid 19428 64 := by unfold smallValid; decide +kernel

private theorem sp19492 : smallValid 19492 63 := by unfold smallValid; decide +kernel

private theorem sp19555 : smallValid 19555 63 := by unfold smallValid; decide +kernel

private theorem sp19618 : smallValid 19618 63 := by unfold smallValid; decide +kernel

private theorem sp19681 : smallValid 19681 64 := by unfold smallValid; decide +kernel

private theorem sp19745 : smallValid 19745 63 := by unfold smallValid; decide +kernel

private theorem sp19808 : smallValid 19808 63 := by unfold smallValid; decide +kernel

private theorem sp19871 : smallValid 19871 63 := by unfold smallValid; decide +kernel

private theorem sp19934 : smallValid 19934 64 := by unfold smallValid; decide +kernel

private theorem sp19998 : smallValid 19998 63 := by unfold smallValid; decide +kernel

private theorem sp20061 : smallValid 20061 64 := by unfold smallValid; decide +kernel

private theorem sp20125 : smallValid 20125 63 := by unfold smallValid; decide +kernel

private theorem sp20188 : smallValid 20188 64 := by unfold smallValid; decide +kernel

private theorem sp20252 : smallValid 20252 63 := by unfold smallValid; decide +kernel

private theorem sp20315 : smallValid 20315 63 := by unfold smallValid; decide +kernel

private theorem sp20378 : smallValid 20378 63 := by unfold smallValid; decide +kernel

private theorem sp20441 : smallValid 20441 64 := by unfold smallValid; decide +kernel

private theorem sp20505 : smallValid 20505 63 := by unfold smallValid; decide +kernel

private theorem sp20568 : smallValid 20568 63 := by unfold smallValid; decide +kernel

private theorem sp20631 : smallValid 20631 63 := by unfold smallValid; decide +kernel

private theorem sp20694 : smallValid 20694 64 := by unfold smallValid; decide +kernel

private theorem sp20758 : smallValid 20758 63 := by unfold smallValid; decide +kernel

private theorem sp20821 : smallValid 20821 63 := by unfold smallValid; decide +kernel

private theorem sp20884 : smallValid 20884 63 := by unfold smallValid; decide +kernel

private theorem sp20947 : smallValid 20947 64 := by unfold smallValid; decide +kernel

private theorem sp21011 : smallValid 21011 63 := by unfold smallValid; decide +kernel

private theorem sp21074 : smallValid 21074 63 := by unfold smallValid; decide +kernel

private theorem sp21137 : smallValid 21137 63 := by unfold smallValid; decide +kernel

private theorem sp21200 : smallValid 21200 64 := by unfold smallValid; decide +kernel

private theorem sp21264 : smallValid 21264 63 := by unfold smallValid; decide +kernel

private theorem sp21327 : smallValid 21327 63 := by unfold smallValid; decide +kernel

private theorem sp21390 : smallValid 21390 63 := by unfold smallValid; decide +kernel

private theorem sp21453 : smallValid 21453 64 := by unfold smallValid; decide +kernel

private theorem sp21517 : smallValid 21517 63 := by unfold smallValid; decide +kernel

private theorem sp21580 : smallValid 21580 63 := by unfold smallValid; decide +kernel

private theorem sp21643 : smallValid 21643 63 := by unfold smallValid; decide +kernel

private theorem sp21706 : smallValid 21706 64 := by unfold smallValid; decide +kernel

private theorem sp21770 : smallValid 21770 63 := by unfold smallValid; decide +kernel

private theorem sp21833 : smallValid 21833 63 := by unfold smallValid; decide +kernel

private theorem sp21896 : smallValid 21896 63 := by unfold smallValid; decide +kernel

private theorem sp21959 : smallValid 21959 64 := by unfold smallValid; decide +kernel

private theorem sp22023 : smallValid 22023 63 := by unfold smallValid; decide +kernel

private theorem sp22086 : smallValid 22086 64 := by unfold smallValid; decide +kernel

private theorem sp22150 : smallValid 22150 63 := by unfold smallValid; decide +kernel

private theorem sp22213 : smallValid 22213 64 := by unfold smallValid; decide +kernel

private theorem sp22277 : smallValid 22277 63 := by unfold smallValid; decide +kernel

private theorem sp22340 : smallValid 22340 63 := by unfold smallValid; decide +kernel

private theorem sp22403 : smallValid 22403 63 := by unfold smallValid; decide +kernel

private theorem sp22466 : smallValid 22466 64 := by unfold smallValid; decide +kernel

private theorem sp22530 : smallValid 22530 63 := by unfold smallValid; decide +kernel

private theorem sp22593 : smallValid 22593 63 := by unfold smallValid; decide +kernel

private theorem sp22656 : smallValid 22656 63 := by unfold smallValid; decide +kernel

private theorem sp22719 : smallValid 22719 64 := by unfold smallValid; decide +kernel

private theorem sp22783 : smallValid 22783 63 := by unfold smallValid; decide +kernel

private theorem sp22846 : smallValid 22846 63 := by unfold smallValid; decide +kernel

private theorem sp22909 : smallValid 22909 63 := by unfold smallValid; decide +kernel

private theorem sp22972 : smallValid 22972 64 := by unfold smallValid; decide +kernel

private theorem sp23036 : smallValid 23036 63 := by unfold smallValid; decide +kernel

private theorem sp23099 : smallValid 23099 64 := by unfold smallValid; decide +kernel

private theorem sp23163 : smallValid 23163 63 := by unfold smallValid; decide +kernel

private theorem sp23226 : smallValid 23226 64 := by unfold smallValid; decide +kernel

private theorem sp23290 : smallValid 23290 63 := by unfold smallValid; decide +kernel

private theorem sp23353 : smallValid 23353 63 := by unfold smallValid; decide +kernel

private theorem sp23416 : smallValid 23416 63 := by unfold smallValid; decide +kernel

private theorem sp23479 : smallValid 23479 64 := by unfold smallValid; decide +kernel

private theorem sp23543 : smallValid 23543 63 := by unfold smallValid; decide +kernel

private theorem sp23606 : smallValid 23606 63 := by unfold smallValid; decide +kernel

private theorem sp23669 : smallValid 23669 63 := by unfold smallValid; decide +kernel

private theorem sp23732 : smallValid 23732 64 := by unfold smallValid; decide +kernel

private theorem sp23796 : smallValid 23796 63 := by unfold smallValid; decide +kernel

private theorem sp23859 : smallValid 23859 63 := by unfold smallValid; decide +kernel

private theorem sp23922 : smallValid 23922 63 := by unfold smallValid; decide +kernel

private theorem sp23985 : smallValid 23985 64 := by unfold smallValid; decide +kernel

private theorem sp24049 : smallValid 24049 63 := by unfold smallValid; decide +kernel

private theorem sp24112 : smallValid 24112 64 := by unfold smallValid; decide +kernel

private theorem sp24176 : smallValid 24176 63 := by unfold smallValid; decide +kernel

private theorem sp24239 : smallValid 24239 64 := by unfold smallValid; decide +kernel

private theorem sp24303 : smallValid 24303 63 := by unfold smallValid; decide +kernel

private theorem sp24366 : smallValid 24366 63 := by unfold smallValid; decide +kernel

private theorem sp24429 : smallValid 24429 63 := by unfold smallValid; decide +kernel

private theorem sp24492 : smallValid 24492 64 := by unfold smallValid; decide +kernel

private theorem sp24556 : smallValid 24556 63 := by unfold smallValid; decide +kernel

private theorem sp24619 : smallValid 24619 63 := by unfold smallValid; decide +kernel

private theorem sp24682 : smallValid 24682 63 := by unfold smallValid; decide +kernel

private theorem sp24745 : smallValid 24745 64 := by unfold smallValid; decide +kernel

private theorem sp24809 : smallValid 24809 63 := by unfold smallValid; decide +kernel

private theorem sp24872 : smallValid 24872 63 := by unfold smallValid; decide +kernel

private theorem sp24935 : smallValid 24935 63 := by unfold smallValid; decide +kernel

private theorem sp24998 : smallValid 24998 64 := by unfold smallValid; decide +kernel

private theorem sp25062 : smallValid 25062 63 := by unfold smallValid; decide +kernel

private theorem sp25125 : smallValid 25125 63 := by unfold smallValid; decide +kernel

private theorem sp25188 : smallValid 25188 63 := by unfold smallValid; decide +kernel

private theorem sp25251 : smallValid 25251 64 := by unfold smallValid; decide +kernel

private theorem sp25315 : smallValid 25315 63 := by unfold smallValid; decide +kernel

private theorem sp25378 : smallValid 25378 63 := by unfold smallValid; decide +kernel

private theorem sp25441 : smallValid 25441 63 := by unfold smallValid; decide +kernel

private theorem sp25504 : smallValid 25504 64 := by unfold smallValid; decide +kernel

private theorem sp25568 : smallValid 25568 63 := by unfold smallValid; decide +kernel

private theorem sp25631 : smallValid 25631 63 := by unfold smallValid; decide +kernel

private theorem sp25694 : smallValid 25694 63 := by unfold smallValid; decide +kernel

private theorem sp25757 : smallValid 25757 64 := by unfold smallValid; decide +kernel

private theorem sp25821 : smallValid 25821 63 := by unfold smallValid; decide +kernel

private theorem sp25884 : smallValid 25884 63 := by unfold smallValid; decide +kernel

private theorem sp25947 : smallValid 25947 63 := by unfold smallValid; decide +kernel

private theorem sp26010 : smallValid 26010 64 := by unfold smallValid; decide +kernel

private theorem sp26074 : smallValid 26074 63 := by unfold smallValid; decide +kernel

private theorem sp26137 : smallValid 26137 64 := by unfold smallValid; decide +kernel

private theorem sp26201 : smallValid 26201 63 := by unfold smallValid; decide +kernel

private theorem sp26264 : smallValid 26264 64 := by unfold smallValid; decide +kernel

private theorem sp26328 : smallValid 26328 63 := by unfold smallValid; decide +kernel

private theorem sp26391 : smallValid 26391 63 := by unfold smallValid; decide +kernel

private theorem sp26454 : smallValid 26454 63 := by unfold smallValid; decide +kernel

private theorem sp26517 : smallValid 26517 64 := by unfold smallValid; decide +kernel

private theorem sp26581 : smallValid 26581 63 := by unfold smallValid; decide +kernel

private theorem sp26644 : smallValid 26644 63 := by unfold smallValid; decide +kernel

private theorem sp26707 : smallValid 26707 63 := by unfold smallValid; decide +kernel

private theorem sp26770 : smallValid 26770 64 := by unfold smallValid; decide +kernel

private theorem sp26834 : smallValid 26834 63 := by unfold smallValid; decide +kernel

private theorem sp26897 : smallValid 26897 63 := by unfold smallValid; decide +kernel

private theorem sp26960 : smallValid 26960 63 := by unfold smallValid; decide +kernel

private theorem sp27023 : smallValid 27023 64 := by unfold smallValid; decide +kernel

private theorem sp27087 : smallValid 27087 63 := by unfold smallValid; decide +kernel

private theorem sp27150 : smallValid 27150 63 := by unfold smallValid; decide +kernel

private theorem sp27213 : smallValid 27213 63 := by unfold smallValid; decide +kernel

private theorem sp27276 : smallValid 27276 64 := by unfold smallValid; decide +kernel

private theorem sp27340 : smallValid 27340 63 := by unfold smallValid; decide +kernel

private theorem sp27403 : smallValid 27403 63 := by unfold smallValid; decide +kernel

private theorem sp27466 : smallValid 27466 63 := by unfold smallValid; decide +kernel

private theorem sp27529 : smallValid 27529 64 := by unfold smallValid; decide +kernel

private theorem sp27593 : smallValid 27593 63 := by unfold smallValid; decide +kernel

private theorem sp27656 : smallValid 27656 63 := by unfold smallValid; decide +kernel

private theorem sp27719 : smallValid 27719 63 := by unfold smallValid; decide +kernel

private theorem sp27782 : smallValid 27782 64 := by unfold smallValid; decide +kernel

private theorem sp27846 : smallValid 27846 63 := by unfold smallValid; decide +kernel

private theorem sp27909 : smallValid 27909 63 := by unfold smallValid; decide +kernel

private theorem sp27972 : smallValid 27972 63 := by unfold smallValid; decide +kernel

private theorem sp28035 : smallValid 28035 64 := by unfold smallValid; decide +kernel

private theorem sp28099 : smallValid 28099 63 := by unfold smallValid; decide +kernel

private theorem sp28162 : smallValid 28162 64 := by unfold smallValid; decide +kernel

private theorem sp28226 : smallValid 28226 63 := by unfold smallValid; decide +kernel

private theorem sp28289 : smallValid 28289 64 := by unfold smallValid; decide +kernel

private theorem sp28353 : smallValid 28353 63 := by unfold smallValid; decide +kernel

private theorem sp28416 : smallValid 28416 63 := by unfold smallValid; decide +kernel

private theorem sp28479 : smallValid 28479 63 := by unfold smallValid; decide +kernel

private theorem sp28542 : smallValid 28542 64 := by unfold smallValid; decide +kernel

private theorem sp28606 : smallValid 28606 63 := by unfold smallValid; decide +kernel

private theorem sp28669 : smallValid 28669 63 := by unfold smallValid; decide +kernel

private theorem sp28732 : smallValid 28732 63 := by unfold smallValid; decide +kernel

private theorem sp28795 : smallValid 28795 64 := by unfold smallValid; decide +kernel

private theorem sp28859 : smallValid 28859 63 := by unfold smallValid; decide +kernel

private theorem sp28922 : smallValid 28922 63 := by unfold smallValid; decide +kernel

private theorem sp28985 : smallValid 28985 63 := by unfold smallValid; decide +kernel

private theorem sp29048 : smallValid 29048 64 := by unfold smallValid; decide +kernel

private theorem sp29112 : smallValid 29112 63 := by unfold smallValid; decide +kernel

private theorem sp29175 : smallValid 29175 63 := by unfold smallValid; decide +kernel

private theorem sp29238 : smallValid 29238 63 := by unfold smallValid; decide +kernel

private theorem sp29301 : smallValid 29301 64 := by unfold smallValid; decide +kernel

private theorem sp29365 : smallValid 29365 63 := by unfold smallValid; decide +kernel

private theorem sp29428 : smallValid 29428 63 := by unfold smallValid; decide +kernel

private theorem sp29491 : smallValid 29491 63 := by unfold smallValid; decide +kernel

private theorem sp29554 : smallValid 29554 64 := by unfold smallValid; decide +kernel

private theorem sp29618 : smallValid 29618 63 := by unfold smallValid; decide +kernel

private theorem sp29681 : smallValid 29681 63 := by unfold smallValid; decide +kernel

private theorem sp29744 : smallValid 29744 63 := by unfold smallValid; decide +kernel

private theorem sp29807 : smallValid 29807 64 := by unfold smallValid; decide +kernel

private theorem sp29871 : smallValid 29871 63 := by unfold smallValid; decide +kernel

private theorem sp29934 : smallValid 29934 63 := by unfold smallValid; decide +kernel

private theorem sp29997 : smallValid 29997 63 := by unfold smallValid; decide +kernel

private theorem sp30060 : smallValid 30060 64 := by unfold smallValid; decide +kernel

private theorem sp30124 : smallValid 30124 63 := by unfold smallValid; decide +kernel

private theorem sp30187 : smallValid 30187 64 := by unfold smallValid; decide +kernel

private theorem sp30251 : smallValid 30251 63 := by unfold smallValid; decide +kernel

private theorem sp30314 : smallValid 30314 64 := by unfold smallValid; decide +kernel

private theorem sp30378 : smallValid 30378 63 := by unfold smallValid; decide +kernel

private theorem sp30441 : smallValid 30441 63 := by unfold smallValid; decide +kernel

private theorem sp30504 : smallValid 30504 63 := by unfold smallValid; decide +kernel

private theorem sp30567 : smallValid 30567 64 := by unfold smallValid; decide +kernel

private theorem sp30631 : smallValid 30631 63 := by unfold smallValid; decide +kernel

private theorem sp30694 : smallValid 30694 63 := by unfold smallValid; decide +kernel

private theorem sp30757 : smallValid 30757 63 := by unfold smallValid; decide +kernel

private theorem sp30820 : smallValid 30820 64 := by unfold smallValid; decide +kernel

private theorem sp30884 : smallValid 30884 63 := by unfold smallValid; decide +kernel

private theorem sp30947 : smallValid 30947 63 := by unfold smallValid; decide +kernel

private theorem sp31010 : smallValid 31010 63 := by unfold smallValid; decide +kernel

private theorem sp31073 : smallValid 31073 64 := by unfold smallValid; decide +kernel

private theorem sp31137 : smallValid 31137 63 := by unfold smallValid; decide +kernel

private theorem sp31200 : smallValid 31200 64 := by unfold smallValid; decide +kernel

private theorem sp31264 : smallValid 31264 63 := by unfold smallValid; decide +kernel

private theorem sp31327 : smallValid 31327 64 := by unfold smallValid; decide +kernel

private theorem sp31391 : smallValid 31391 63 := by unfold smallValid; decide +kernel

private theorem sp31454 : smallValid 31454 63 := by unfold smallValid; decide +kernel

private theorem sp31517 : smallValid 31517 63 := by unfold smallValid; decide +kernel

private theorem sp31580 : smallValid 31580 64 := by unfold smallValid; decide +kernel

private theorem sp31644 : smallValid 31644 63 := by unfold smallValid; decide +kernel

private theorem sp31707 : smallValid 31707 63 := by unfold smallValid; decide +kernel

private theorem sp31770 : smallValid 31770 63 := by unfold smallValid; decide +kernel

private theorem sp31833 : smallValid 31833 64 := by unfold smallValid; decide +kernel

private theorem sp31897 : smallValid 31897 63 := by unfold smallValid; decide +kernel

private theorem sp31960 : smallValid 31960 63 := by unfold smallValid; decide +kernel

private theorem sp32023 : smallValid 32023 63 := by unfold smallValid; decide +kernel

private theorem sp32086 : smallValid 32086 64 := by unfold smallValid; decide +kernel

private theorem sp32150 : smallValid 32150 63 := by unfold smallValid; decide +kernel

private theorem sp32213 : smallValid 32213 64 := by unfold smallValid; decide +kernel

private theorem sp32277 : smallValid 32277 63 := by unfold smallValid; decide +kernel

private theorem sp32340 : smallValid 32340 64 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤32403) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 32404 := (joinSmall (lo:=0) (a:=16202) (b:=16202) (joinSmall (lo:=0) (a:=8101) (b:=8101) (joinSmall (lo:=0) (a:=4050) (b:=4051) (joinSmall (lo:=0) (a:=2025) (b:=2025) (joinSmall (lo:=0) (a:=1012) (b:=1013) (joinSmall (lo:=0) (a:=506) (b:=506) (joinSmall (lo:=0) (a:=253) (b:=253) (joinSmall (lo:=0) (a:=126) (b:=127) (joinSmall (lo:=0) (a:=63) (b:=63) sp0 sp63) (joinSmall (lo:=126) (a:=63) (b:=64) sp126 sp189)) (joinSmall (lo:=253) (a:=126) (b:=127) (joinSmall (lo:=253) (a:=63) (b:=63) sp253 sp316) (joinSmall (lo:=379) (a:=63) (b:=64) sp379 sp442))) (joinSmall (lo:=506) (a:=253) (b:=253) (joinSmall (lo:=506) (a:=126) (b:=127) (joinSmall (lo:=506) (a:=63) (b:=63) sp506 sp569) (joinSmall (lo:=632) (a:=63) (b:=64) sp632 sp695)) (joinSmall (lo:=759) (a:=126) (b:=127) (joinSmall (lo:=759) (a:=63) (b:=63) sp759 sp822) (joinSmall (lo:=885) (a:=63) (b:=64) sp885 sp948)))) (joinSmall (lo:=1012) (a:=506) (b:=507) (joinSmall (lo:=1012) (a:=253) (b:=253) (joinSmall (lo:=1012) (a:=126) (b:=127) (joinSmall (lo:=1012) (a:=63) (b:=63) sp1012 sp1075) (joinSmall (lo:=1138) (a:=63) (b:=64) sp1138 sp1201)) (joinSmall (lo:=1265) (a:=126) (b:=127) (joinSmall (lo:=1265) (a:=63) (b:=63) sp1265 sp1328) (joinSmall (lo:=1391) (a:=63) (b:=64) sp1391 sp1454))) (joinSmall (lo:=1518) (a:=253) (b:=254) (joinSmall (lo:=1518) (a:=126) (b:=127) (joinSmall (lo:=1518) (a:=63) (b:=63) sp1518 sp1581) (joinSmall (lo:=1644) (a:=63) (b:=64) sp1644 sp1707)) (joinSmall (lo:=1771) (a:=127) (b:=127) (joinSmall (lo:=1771) (a:=63) (b:=64) sp1771 sp1834) (joinSmall (lo:=1898) (a:=63) (b:=64) sp1898 sp1961))))) (joinSmall (lo:=2025) (a:=1012) (b:=1013) (joinSmall (lo:=2025) (a:=506) (b:=506) (joinSmall (lo:=2025) (a:=253) (b:=253) (joinSmall (lo:=2025) (a:=126) (b:=127) (joinSmall (lo:=2025) (a:=63) (b:=63) sp2025 sp2088) (joinSmall (lo:=2151) (a:=63) (b:=64) sp2151 sp2214)) (joinSmall (lo:=2278) (a:=126) (b:=127) (joinSmall (lo:=2278) (a:=63) (b:=63) sp2278 sp2341) (joinSmall (lo:=2404) (a:=63) (b:=64) sp2404 sp2467))) (joinSmall (lo:=2531) (a:=253) (b:=253) (joinSmall (lo:=2531) (a:=126) (b:=127) (joinSmall (lo:=2531) (a:=63) (b:=63) sp2531 sp2594) (joinSmall (lo:=2657) (a:=63) (b:=64) sp2657 sp2720)) (joinSmall (lo:=2784) (a:=126) (b:=127) (joinSmall (lo:=2784) (a:=63) (b:=63) sp2784 sp2847) (joinSmall (lo:=2910) (a:=63) (b:=64) sp2910 sp2973)))) (joinSmall (lo:=3037) (a:=506) (b:=507) (joinSmall (lo:=3037) (a:=253) (b:=253) (joinSmall (lo:=3037) (a:=126) (b:=127) (joinSmall (lo:=3037) (a:=63) (b:=63) sp3037 sp3100) (joinSmall (lo:=3163) (a:=63) (b:=64) sp3163 sp3226)) (joinSmall (lo:=3290) (a:=126) (b:=127) (joinSmall (lo:=3290) (a:=63) (b:=63) sp3290 sp3353) (joinSmall (lo:=3416) (a:=63) (b:=64) sp3416 sp3479))) (joinSmall (lo:=3543) (a:=253) (b:=254) (joinSmall (lo:=3543) (a:=126) (b:=127) (joinSmall (lo:=3543) (a:=63) (b:=63) sp3543 sp3606) (joinSmall (lo:=3669) (a:=63) (b:=64) sp3669 sp3732)) (joinSmall (lo:=3796) (a:=127) (b:=127) (joinSmall (lo:=3796) (a:=63) (b:=64) sp3796 sp3859) (joinSmall (lo:=3923) (a:=63) (b:=64) sp3923 sp3986)))))) (joinSmall (lo:=4050) (a:=2025) (b:=2026) (joinSmall (lo:=4050) (a:=1012) (b:=1013) (joinSmall (lo:=4050) (a:=506) (b:=506) (joinSmall (lo:=4050) (a:=253) (b:=253) (joinSmall (lo:=4050) (a:=126) (b:=127) (joinSmall (lo:=4050) (a:=63) (b:=63) sp4050 sp4113) (joinSmall (lo:=4176) (a:=63) (b:=64) sp4176 sp4239)) (joinSmall (lo:=4303) (a:=126) (b:=127) (joinSmall (lo:=4303) (a:=63) (b:=63) sp4303 sp4366) (joinSmall (lo:=4429) (a:=63) (b:=64) sp4429 sp4492))) (joinSmall (lo:=4556) (a:=253) (b:=253) (joinSmall (lo:=4556) (a:=126) (b:=127) (joinSmall (lo:=4556) (a:=63) (b:=63) sp4556 sp4619) (joinSmall (lo:=4682) (a:=63) (b:=64) sp4682 sp4745)) (joinSmall (lo:=4809) (a:=126) (b:=127) (joinSmall (lo:=4809) (a:=63) (b:=63) sp4809 sp4872) (joinSmall (lo:=4935) (a:=63) (b:=64) sp4935 sp4998)))) (joinSmall (lo:=5062) (a:=506) (b:=507) (joinSmall (lo:=5062) (a:=253) (b:=253) (joinSmall (lo:=5062) (a:=126) (b:=127) (joinSmall (lo:=5062) (a:=63) (b:=63) sp5062 sp5125) (joinSmall (lo:=5188) (a:=63) (b:=64) sp5188 sp5251)) (joinSmall (lo:=5315) (a:=126) (b:=127) (joinSmall (lo:=5315) (a:=63) (b:=63) sp5315 sp5378) (joinSmall (lo:=5441) (a:=63) (b:=64) sp5441 sp5504))) (joinSmall (lo:=5568) (a:=253) (b:=254) (joinSmall (lo:=5568) (a:=126) (b:=127) (joinSmall (lo:=5568) (a:=63) (b:=63) sp5568 sp5631) (joinSmall (lo:=5694) (a:=63) (b:=64) sp5694 sp5757)) (joinSmall (lo:=5821) (a:=127) (b:=127) (joinSmall (lo:=5821) (a:=63) (b:=64) sp5821 sp5884) (joinSmall (lo:=5948) (a:=63) (b:=64) sp5948 sp6011))))) (joinSmall (lo:=6075) (a:=1013) (b:=1013) (joinSmall (lo:=6075) (a:=506) (b:=507) (joinSmall (lo:=6075) (a:=253) (b:=253) (joinSmall (lo:=6075) (a:=126) (b:=127) (joinSmall (lo:=6075) (a:=63) (b:=63) sp6075 sp6138) (joinSmall (lo:=6201) (a:=63) (b:=64) sp6201 sp6264)) (joinSmall (lo:=6328) (a:=126) (b:=127) (joinSmall (lo:=6328) (a:=63) (b:=63) sp6328 sp6391) (joinSmall (lo:=6454) (a:=63) (b:=64) sp6454 sp6517))) (joinSmall (lo:=6581) (a:=253) (b:=254) (joinSmall (lo:=6581) (a:=126) (b:=127) (joinSmall (lo:=6581) (a:=63) (b:=63) sp6581 sp6644) (joinSmall (lo:=6707) (a:=63) (b:=64) sp6707 sp6770)) (joinSmall (lo:=6834) (a:=127) (b:=127) (joinSmall (lo:=6834) (a:=63) (b:=64) sp6834 sp6897) (joinSmall (lo:=6961) (a:=63) (b:=64) sp6961 sp7024)))) (joinSmall (lo:=7088) (a:=506) (b:=507) (joinSmall (lo:=7088) (a:=253) (b:=253) (joinSmall (lo:=7088) (a:=126) (b:=127) (joinSmall (lo:=7088) (a:=63) (b:=63) sp7088 sp7151) (joinSmall (lo:=7214) (a:=63) (b:=64) sp7214 sp7277)) (joinSmall (lo:=7341) (a:=126) (b:=127) (joinSmall (lo:=7341) (a:=63) (b:=63) sp7341 sp7404) (joinSmall (lo:=7467) (a:=63) (b:=64) sp7467 sp7530))) (joinSmall (lo:=7594) (a:=253) (b:=254) (joinSmall (lo:=7594) (a:=126) (b:=127) (joinSmall (lo:=7594) (a:=63) (b:=63) sp7594 sp7657) (joinSmall (lo:=7720) (a:=63) (b:=64) sp7720 sp7783)) (joinSmall (lo:=7847) (a:=127) (b:=127) (joinSmall (lo:=7847) (a:=63) (b:=64) sp7847 sp7910) (joinSmall (lo:=7974) (a:=63) (b:=64) sp7974 sp8037))))))) (joinSmall (lo:=8101) (a:=4050) (b:=4051) (joinSmall (lo:=8101) (a:=2025) (b:=2025) (joinSmall (lo:=8101) (a:=1012) (b:=1013) (joinSmall (lo:=8101) (a:=506) (b:=506) (joinSmall (lo:=8101) (a:=253) (b:=253) (joinSmall (lo:=8101) (a:=126) (b:=127) (joinSmall (lo:=8101) (a:=63) (b:=63) sp8101 sp8164) (joinSmall (lo:=8227) (a:=63) (b:=64) sp8227 sp8290)) (joinSmall (lo:=8354) (a:=126) (b:=127) (joinSmall (lo:=8354) (a:=63) (b:=63) sp8354 sp8417) (joinSmall (lo:=8480) (a:=63) (b:=64) sp8480 sp8543))) (joinSmall (lo:=8607) (a:=253) (b:=253) (joinSmall (lo:=8607) (a:=126) (b:=127) (joinSmall (lo:=8607) (a:=63) (b:=63) sp8607 sp8670) (joinSmall (lo:=8733) (a:=63) (b:=64) sp8733 sp8796)) (joinSmall (lo:=8860) (a:=126) (b:=127) (joinSmall (lo:=8860) (a:=63) (b:=63) sp8860 sp8923) (joinSmall (lo:=8986) (a:=63) (b:=64) sp8986 sp9049)))) (joinSmall (lo:=9113) (a:=506) (b:=507) (joinSmall (lo:=9113) (a:=253) (b:=253) (joinSmall (lo:=9113) (a:=126) (b:=127) (joinSmall (lo:=9113) (a:=63) (b:=63) sp9113 sp9176) (joinSmall (lo:=9239) (a:=63) (b:=64) sp9239 sp9302)) (joinSmall (lo:=9366) (a:=126) (b:=127) (joinSmall (lo:=9366) (a:=63) (b:=63) sp9366 sp9429) (joinSmall (lo:=9492) (a:=63) (b:=64) sp9492 sp9555))) (joinSmall (lo:=9619) (a:=253) (b:=254) (joinSmall (lo:=9619) (a:=126) (b:=127) (joinSmall (lo:=9619) (a:=63) (b:=63) sp9619 sp9682) (joinSmall (lo:=9745) (a:=63) (b:=64) sp9745 sp9808)) (joinSmall (lo:=9872) (a:=127) (b:=127) (joinSmall (lo:=9872) (a:=63) (b:=64) sp9872 sp9935) (joinSmall (lo:=9999) (a:=63) (b:=64) sp9999 sp10062))))) (joinSmall (lo:=10126) (a:=1012) (b:=1013) (joinSmall (lo:=10126) (a:=506) (b:=506) (joinSmall (lo:=10126) (a:=253) (b:=253) (joinSmall (lo:=10126) (a:=126) (b:=127) (joinSmall (lo:=10126) (a:=63) (b:=63) sp10126 sp10189) (joinSmall (lo:=10252) (a:=63) (b:=64) sp10252 sp10315)) (joinSmall (lo:=10379) (a:=126) (b:=127) (joinSmall (lo:=10379) (a:=63) (b:=63) sp10379 sp10442) (joinSmall (lo:=10505) (a:=63) (b:=64) sp10505 sp10568))) (joinSmall (lo:=10632) (a:=253) (b:=253) (joinSmall (lo:=10632) (a:=126) (b:=127) (joinSmall (lo:=10632) (a:=63) (b:=63) sp10632 sp10695) (joinSmall (lo:=10758) (a:=63) (b:=64) sp10758 sp10821)) (joinSmall (lo:=10885) (a:=126) (b:=127) (joinSmall (lo:=10885) (a:=63) (b:=63) sp10885 sp10948) (joinSmall (lo:=11011) (a:=63) (b:=64) sp11011 sp11074)))) (joinSmall (lo:=11138) (a:=506) (b:=507) (joinSmall (lo:=11138) (a:=253) (b:=253) (joinSmall (lo:=11138) (a:=126) (b:=127) (joinSmall (lo:=11138) (a:=63) (b:=63) sp11138 sp11201) (joinSmall (lo:=11264) (a:=63) (b:=64) sp11264 sp11327)) (joinSmall (lo:=11391) (a:=126) (b:=127) (joinSmall (lo:=11391) (a:=63) (b:=63) sp11391 sp11454) (joinSmall (lo:=11517) (a:=63) (b:=64) sp11517 sp11580))) (joinSmall (lo:=11644) (a:=253) (b:=254) (joinSmall (lo:=11644) (a:=126) (b:=127) (joinSmall (lo:=11644) (a:=63) (b:=63) sp11644 sp11707) (joinSmall (lo:=11770) (a:=63) (b:=64) sp11770 sp11833)) (joinSmall (lo:=11897) (a:=127) (b:=127) (joinSmall (lo:=11897) (a:=63) (b:=64) sp11897 sp11960) (joinSmall (lo:=12024) (a:=63) (b:=64) sp12024 sp12087)))))) (joinSmall (lo:=12151) (a:=2025) (b:=2026) (joinSmall (lo:=12151) (a:=1012) (b:=1013) (joinSmall (lo:=12151) (a:=506) (b:=506) (joinSmall (lo:=12151) (a:=253) (b:=253) (joinSmall (lo:=12151) (a:=126) (b:=127) (joinSmall (lo:=12151) (a:=63) (b:=63) sp12151 sp12214) (joinSmall (lo:=12277) (a:=63) (b:=64) sp12277 sp12340)) (joinSmall (lo:=12404) (a:=126) (b:=127) (joinSmall (lo:=12404) (a:=63) (b:=63) sp12404 sp12467) (joinSmall (lo:=12530) (a:=63) (b:=64) sp12530 sp12593))) (joinSmall (lo:=12657) (a:=253) (b:=253) (joinSmall (lo:=12657) (a:=126) (b:=127) (joinSmall (lo:=12657) (a:=63) (b:=63) sp12657 sp12720) (joinSmall (lo:=12783) (a:=63) (b:=64) sp12783 sp12846)) (joinSmall (lo:=12910) (a:=126) (b:=127) (joinSmall (lo:=12910) (a:=63) (b:=63) sp12910 sp12973) (joinSmall (lo:=13036) (a:=63) (b:=64) sp13036 sp13099)))) (joinSmall (lo:=13163) (a:=506) (b:=507) (joinSmall (lo:=13163) (a:=253) (b:=253) (joinSmall (lo:=13163) (a:=126) (b:=127) (joinSmall (lo:=13163) (a:=63) (b:=63) sp13163 sp13226) (joinSmall (lo:=13289) (a:=63) (b:=64) sp13289 sp13352)) (joinSmall (lo:=13416) (a:=126) (b:=127) (joinSmall (lo:=13416) (a:=63) (b:=63) sp13416 sp13479) (joinSmall (lo:=13542) (a:=63) (b:=64) sp13542 sp13605))) (joinSmall (lo:=13669) (a:=253) (b:=254) (joinSmall (lo:=13669) (a:=126) (b:=127) (joinSmall (lo:=13669) (a:=63) (b:=63) sp13669 sp13732) (joinSmall (lo:=13795) (a:=63) (b:=64) sp13795 sp13858)) (joinSmall (lo:=13922) (a:=127) (b:=127) (joinSmall (lo:=13922) (a:=63) (b:=64) sp13922 sp13985) (joinSmall (lo:=14049) (a:=63) (b:=64) sp14049 sp14112))))) (joinSmall (lo:=14176) (a:=1013) (b:=1013) (joinSmall (lo:=14176) (a:=506) (b:=507) (joinSmall (lo:=14176) (a:=253) (b:=253) (joinSmall (lo:=14176) (a:=126) (b:=127) (joinSmall (lo:=14176) (a:=63) (b:=63) sp14176 sp14239) (joinSmall (lo:=14302) (a:=63) (b:=64) sp14302 sp14365)) (joinSmall (lo:=14429) (a:=126) (b:=127) (joinSmall (lo:=14429) (a:=63) (b:=63) sp14429 sp14492) (joinSmall (lo:=14555) (a:=63) (b:=64) sp14555 sp14618))) (joinSmall (lo:=14682) (a:=253) (b:=254) (joinSmall (lo:=14682) (a:=126) (b:=127) (joinSmall (lo:=14682) (a:=63) (b:=63) sp14682 sp14745) (joinSmall (lo:=14808) (a:=63) (b:=64) sp14808 sp14871)) (joinSmall (lo:=14935) (a:=127) (b:=127) (joinSmall (lo:=14935) (a:=63) (b:=64) sp14935 sp14998) (joinSmall (lo:=15062) (a:=63) (b:=64) sp15062 sp15125)))) (joinSmall (lo:=15189) (a:=506) (b:=507) (joinSmall (lo:=15189) (a:=253) (b:=253) (joinSmall (lo:=15189) (a:=126) (b:=127) (joinSmall (lo:=15189) (a:=63) (b:=63) sp15189 sp15252) (joinSmall (lo:=15315) (a:=63) (b:=64) sp15315 sp15378)) (joinSmall (lo:=15442) (a:=126) (b:=127) (joinSmall (lo:=15442) (a:=63) (b:=63) sp15442 sp15505) (joinSmall (lo:=15568) (a:=63) (b:=64) sp15568 sp15631))) (joinSmall (lo:=15695) (a:=253) (b:=254) (joinSmall (lo:=15695) (a:=126) (b:=127) (joinSmall (lo:=15695) (a:=63) (b:=63) sp15695 sp15758) (joinSmall (lo:=15821) (a:=63) (b:=64) sp15821 sp15884)) (joinSmall (lo:=15948) (a:=127) (b:=127) (joinSmall (lo:=15948) (a:=63) (b:=64) sp15948 sp16011) (joinSmall (lo:=16075) (a:=63) (b:=64) sp16075 sp16138)))))))) (joinSmall (lo:=16202) (a:=8101) (b:=8101) (joinSmall (lo:=16202) (a:=4050) (b:=4051) (joinSmall (lo:=16202) (a:=2025) (b:=2025) (joinSmall (lo:=16202) (a:=1012) (b:=1013) (joinSmall (lo:=16202) (a:=506) (b:=506) (joinSmall (lo:=16202) (a:=253) (b:=253) (joinSmall (lo:=16202) (a:=126) (b:=127) (joinSmall (lo:=16202) (a:=63) (b:=63) sp16202 sp16265) (joinSmall (lo:=16328) (a:=63) (b:=64) sp16328 sp16391)) (joinSmall (lo:=16455) (a:=126) (b:=127) (joinSmall (lo:=16455) (a:=63) (b:=63) sp16455 sp16518) (joinSmall (lo:=16581) (a:=63) (b:=64) sp16581 sp16644))) (joinSmall (lo:=16708) (a:=253) (b:=253) (joinSmall (lo:=16708) (a:=126) (b:=127) (joinSmall (lo:=16708) (a:=63) (b:=63) sp16708 sp16771) (joinSmall (lo:=16834) (a:=63) (b:=64) sp16834 sp16897)) (joinSmall (lo:=16961) (a:=126) (b:=127) (joinSmall (lo:=16961) (a:=63) (b:=63) sp16961 sp17024) (joinSmall (lo:=17087) (a:=63) (b:=64) sp17087 sp17150)))) (joinSmall (lo:=17214) (a:=506) (b:=507) (joinSmall (lo:=17214) (a:=253) (b:=253) (joinSmall (lo:=17214) (a:=126) (b:=127) (joinSmall (lo:=17214) (a:=63) (b:=63) sp17214 sp17277) (joinSmall (lo:=17340) (a:=63) (b:=64) sp17340 sp17403)) (joinSmall (lo:=17467) (a:=126) (b:=127) (joinSmall (lo:=17467) (a:=63) (b:=63) sp17467 sp17530) (joinSmall (lo:=17593) (a:=63) (b:=64) sp17593 sp17656))) (joinSmall (lo:=17720) (a:=253) (b:=254) (joinSmall (lo:=17720) (a:=126) (b:=127) (joinSmall (lo:=17720) (a:=63) (b:=63) sp17720 sp17783) (joinSmall (lo:=17846) (a:=63) (b:=64) sp17846 sp17909)) (joinSmall (lo:=17973) (a:=127) (b:=127) (joinSmall (lo:=17973) (a:=63) (b:=64) sp17973 sp18036) (joinSmall (lo:=18100) (a:=63) (b:=64) sp18100 sp18163))))) (joinSmall (lo:=18227) (a:=1012) (b:=1013) (joinSmall (lo:=18227) (a:=506) (b:=506) (joinSmall (lo:=18227) (a:=253) (b:=253) (joinSmall (lo:=18227) (a:=126) (b:=127) (joinSmall (lo:=18227) (a:=63) (b:=63) sp18227 sp18290) (joinSmall (lo:=18353) (a:=63) (b:=64) sp18353 sp18416)) (joinSmall (lo:=18480) (a:=126) (b:=127) (joinSmall (lo:=18480) (a:=63) (b:=63) sp18480 sp18543) (joinSmall (lo:=18606) (a:=63) (b:=64) sp18606 sp18669))) (joinSmall (lo:=18733) (a:=253) (b:=253) (joinSmall (lo:=18733) (a:=126) (b:=127) (joinSmall (lo:=18733) (a:=63) (b:=63) sp18733 sp18796) (joinSmall (lo:=18859) (a:=63) (b:=64) sp18859 sp18922)) (joinSmall (lo:=18986) (a:=126) (b:=127) (joinSmall (lo:=18986) (a:=63) (b:=63) sp18986 sp19049) (joinSmall (lo:=19112) (a:=63) (b:=64) sp19112 sp19175)))) (joinSmall (lo:=19239) (a:=506) (b:=507) (joinSmall (lo:=19239) (a:=253) (b:=253) (joinSmall (lo:=19239) (a:=126) (b:=127) (joinSmall (lo:=19239) (a:=63) (b:=63) sp19239 sp19302) (joinSmall (lo:=19365) (a:=63) (b:=64) sp19365 sp19428)) (joinSmall (lo:=19492) (a:=126) (b:=127) (joinSmall (lo:=19492) (a:=63) (b:=63) sp19492 sp19555) (joinSmall (lo:=19618) (a:=63) (b:=64) sp19618 sp19681))) (joinSmall (lo:=19745) (a:=253) (b:=254) (joinSmall (lo:=19745) (a:=126) (b:=127) (joinSmall (lo:=19745) (a:=63) (b:=63) sp19745 sp19808) (joinSmall (lo:=19871) (a:=63) (b:=64) sp19871 sp19934)) (joinSmall (lo:=19998) (a:=127) (b:=127) (joinSmall (lo:=19998) (a:=63) (b:=64) sp19998 sp20061) (joinSmall (lo:=20125) (a:=63) (b:=64) sp20125 sp20188)))))) (joinSmall (lo:=20252) (a:=2025) (b:=2026) (joinSmall (lo:=20252) (a:=1012) (b:=1013) (joinSmall (lo:=20252) (a:=506) (b:=506) (joinSmall (lo:=20252) (a:=253) (b:=253) (joinSmall (lo:=20252) (a:=126) (b:=127) (joinSmall (lo:=20252) (a:=63) (b:=63) sp20252 sp20315) (joinSmall (lo:=20378) (a:=63) (b:=64) sp20378 sp20441)) (joinSmall (lo:=20505) (a:=126) (b:=127) (joinSmall (lo:=20505) (a:=63) (b:=63) sp20505 sp20568) (joinSmall (lo:=20631) (a:=63) (b:=64) sp20631 sp20694))) (joinSmall (lo:=20758) (a:=253) (b:=253) (joinSmall (lo:=20758) (a:=126) (b:=127) (joinSmall (lo:=20758) (a:=63) (b:=63) sp20758 sp20821) (joinSmall (lo:=20884) (a:=63) (b:=64) sp20884 sp20947)) (joinSmall (lo:=21011) (a:=126) (b:=127) (joinSmall (lo:=21011) (a:=63) (b:=63) sp21011 sp21074) (joinSmall (lo:=21137) (a:=63) (b:=64) sp21137 sp21200)))) (joinSmall (lo:=21264) (a:=506) (b:=507) (joinSmall (lo:=21264) (a:=253) (b:=253) (joinSmall (lo:=21264) (a:=126) (b:=127) (joinSmall (lo:=21264) (a:=63) (b:=63) sp21264 sp21327) (joinSmall (lo:=21390) (a:=63) (b:=64) sp21390 sp21453)) (joinSmall (lo:=21517) (a:=126) (b:=127) (joinSmall (lo:=21517) (a:=63) (b:=63) sp21517 sp21580) (joinSmall (lo:=21643) (a:=63) (b:=64) sp21643 sp21706))) (joinSmall (lo:=21770) (a:=253) (b:=254) (joinSmall (lo:=21770) (a:=126) (b:=127) (joinSmall (lo:=21770) (a:=63) (b:=63) sp21770 sp21833) (joinSmall (lo:=21896) (a:=63) (b:=64) sp21896 sp21959)) (joinSmall (lo:=22023) (a:=127) (b:=127) (joinSmall (lo:=22023) (a:=63) (b:=64) sp22023 sp22086) (joinSmall (lo:=22150) (a:=63) (b:=64) sp22150 sp22213))))) (joinSmall (lo:=22277) (a:=1013) (b:=1013) (joinSmall (lo:=22277) (a:=506) (b:=507) (joinSmall (lo:=22277) (a:=253) (b:=253) (joinSmall (lo:=22277) (a:=126) (b:=127) (joinSmall (lo:=22277) (a:=63) (b:=63) sp22277 sp22340) (joinSmall (lo:=22403) (a:=63) (b:=64) sp22403 sp22466)) (joinSmall (lo:=22530) (a:=126) (b:=127) (joinSmall (lo:=22530) (a:=63) (b:=63) sp22530 sp22593) (joinSmall (lo:=22656) (a:=63) (b:=64) sp22656 sp22719))) (joinSmall (lo:=22783) (a:=253) (b:=254) (joinSmall (lo:=22783) (a:=126) (b:=127) (joinSmall (lo:=22783) (a:=63) (b:=63) sp22783 sp22846) (joinSmall (lo:=22909) (a:=63) (b:=64) sp22909 sp22972)) (joinSmall (lo:=23036) (a:=127) (b:=127) (joinSmall (lo:=23036) (a:=63) (b:=64) sp23036 sp23099) (joinSmall (lo:=23163) (a:=63) (b:=64) sp23163 sp23226)))) (joinSmall (lo:=23290) (a:=506) (b:=507) (joinSmall (lo:=23290) (a:=253) (b:=253) (joinSmall (lo:=23290) (a:=126) (b:=127) (joinSmall (lo:=23290) (a:=63) (b:=63) sp23290 sp23353) (joinSmall (lo:=23416) (a:=63) (b:=64) sp23416 sp23479)) (joinSmall (lo:=23543) (a:=126) (b:=127) (joinSmall (lo:=23543) (a:=63) (b:=63) sp23543 sp23606) (joinSmall (lo:=23669) (a:=63) (b:=64) sp23669 sp23732))) (joinSmall (lo:=23796) (a:=253) (b:=254) (joinSmall (lo:=23796) (a:=126) (b:=127) (joinSmall (lo:=23796) (a:=63) (b:=63) sp23796 sp23859) (joinSmall (lo:=23922) (a:=63) (b:=64) sp23922 sp23985)) (joinSmall (lo:=24049) (a:=127) (b:=127) (joinSmall (lo:=24049) (a:=63) (b:=64) sp24049 sp24112) (joinSmall (lo:=24176) (a:=63) (b:=64) sp24176 sp24239))))))) (joinSmall (lo:=24303) (a:=4050) (b:=4051) (joinSmall (lo:=24303) (a:=2025) (b:=2025) (joinSmall (lo:=24303) (a:=1012) (b:=1013) (joinSmall (lo:=24303) (a:=506) (b:=506) (joinSmall (lo:=24303) (a:=253) (b:=253) (joinSmall (lo:=24303) (a:=126) (b:=127) (joinSmall (lo:=24303) (a:=63) (b:=63) sp24303 sp24366) (joinSmall (lo:=24429) (a:=63) (b:=64) sp24429 sp24492)) (joinSmall (lo:=24556) (a:=126) (b:=127) (joinSmall (lo:=24556) (a:=63) (b:=63) sp24556 sp24619) (joinSmall (lo:=24682) (a:=63) (b:=64) sp24682 sp24745))) (joinSmall (lo:=24809) (a:=253) (b:=253) (joinSmall (lo:=24809) (a:=126) (b:=127) (joinSmall (lo:=24809) (a:=63) (b:=63) sp24809 sp24872) (joinSmall (lo:=24935) (a:=63) (b:=64) sp24935 sp24998)) (joinSmall (lo:=25062) (a:=126) (b:=127) (joinSmall (lo:=25062) (a:=63) (b:=63) sp25062 sp25125) (joinSmall (lo:=25188) (a:=63) (b:=64) sp25188 sp25251)))) (joinSmall (lo:=25315) (a:=506) (b:=507) (joinSmall (lo:=25315) (a:=253) (b:=253) (joinSmall (lo:=25315) (a:=126) (b:=127) (joinSmall (lo:=25315) (a:=63) (b:=63) sp25315 sp25378) (joinSmall (lo:=25441) (a:=63) (b:=64) sp25441 sp25504)) (joinSmall (lo:=25568) (a:=126) (b:=127) (joinSmall (lo:=25568) (a:=63) (b:=63) sp25568 sp25631) (joinSmall (lo:=25694) (a:=63) (b:=64) sp25694 sp25757))) (joinSmall (lo:=25821) (a:=253) (b:=254) (joinSmall (lo:=25821) (a:=126) (b:=127) (joinSmall (lo:=25821) (a:=63) (b:=63) sp25821 sp25884) (joinSmall (lo:=25947) (a:=63) (b:=64) sp25947 sp26010)) (joinSmall (lo:=26074) (a:=127) (b:=127) (joinSmall (lo:=26074) (a:=63) (b:=64) sp26074 sp26137) (joinSmall (lo:=26201) (a:=63) (b:=64) sp26201 sp26264))))) (joinSmall (lo:=26328) (a:=1012) (b:=1013) (joinSmall (lo:=26328) (a:=506) (b:=506) (joinSmall (lo:=26328) (a:=253) (b:=253) (joinSmall (lo:=26328) (a:=126) (b:=127) (joinSmall (lo:=26328) (a:=63) (b:=63) sp26328 sp26391) (joinSmall (lo:=26454) (a:=63) (b:=64) sp26454 sp26517)) (joinSmall (lo:=26581) (a:=126) (b:=127) (joinSmall (lo:=26581) (a:=63) (b:=63) sp26581 sp26644) (joinSmall (lo:=26707) (a:=63) (b:=64) sp26707 sp26770))) (joinSmall (lo:=26834) (a:=253) (b:=253) (joinSmall (lo:=26834) (a:=126) (b:=127) (joinSmall (lo:=26834) (a:=63) (b:=63) sp26834 sp26897) (joinSmall (lo:=26960) (a:=63) (b:=64) sp26960 sp27023)) (joinSmall (lo:=27087) (a:=126) (b:=127) (joinSmall (lo:=27087) (a:=63) (b:=63) sp27087 sp27150) (joinSmall (lo:=27213) (a:=63) (b:=64) sp27213 sp27276)))) (joinSmall (lo:=27340) (a:=506) (b:=507) (joinSmall (lo:=27340) (a:=253) (b:=253) (joinSmall (lo:=27340) (a:=126) (b:=127) (joinSmall (lo:=27340) (a:=63) (b:=63) sp27340 sp27403) (joinSmall (lo:=27466) (a:=63) (b:=64) sp27466 sp27529)) (joinSmall (lo:=27593) (a:=126) (b:=127) (joinSmall (lo:=27593) (a:=63) (b:=63) sp27593 sp27656) (joinSmall (lo:=27719) (a:=63) (b:=64) sp27719 sp27782))) (joinSmall (lo:=27846) (a:=253) (b:=254) (joinSmall (lo:=27846) (a:=126) (b:=127) (joinSmall (lo:=27846) (a:=63) (b:=63) sp27846 sp27909) (joinSmall (lo:=27972) (a:=63) (b:=64) sp27972 sp28035)) (joinSmall (lo:=28099) (a:=127) (b:=127) (joinSmall (lo:=28099) (a:=63) (b:=64) sp28099 sp28162) (joinSmall (lo:=28226) (a:=63) (b:=64) sp28226 sp28289)))))) (joinSmall (lo:=28353) (a:=2025) (b:=2026) (joinSmall (lo:=28353) (a:=1012) (b:=1013) (joinSmall (lo:=28353) (a:=506) (b:=506) (joinSmall (lo:=28353) (a:=253) (b:=253) (joinSmall (lo:=28353) (a:=126) (b:=127) (joinSmall (lo:=28353) (a:=63) (b:=63) sp28353 sp28416) (joinSmall (lo:=28479) (a:=63) (b:=64) sp28479 sp28542)) (joinSmall (lo:=28606) (a:=126) (b:=127) (joinSmall (lo:=28606) (a:=63) (b:=63) sp28606 sp28669) (joinSmall (lo:=28732) (a:=63) (b:=64) sp28732 sp28795))) (joinSmall (lo:=28859) (a:=253) (b:=253) (joinSmall (lo:=28859) (a:=126) (b:=127) (joinSmall (lo:=28859) (a:=63) (b:=63) sp28859 sp28922) (joinSmall (lo:=28985) (a:=63) (b:=64) sp28985 sp29048)) (joinSmall (lo:=29112) (a:=126) (b:=127) (joinSmall (lo:=29112) (a:=63) (b:=63) sp29112 sp29175) (joinSmall (lo:=29238) (a:=63) (b:=64) sp29238 sp29301)))) (joinSmall (lo:=29365) (a:=506) (b:=507) (joinSmall (lo:=29365) (a:=253) (b:=253) (joinSmall (lo:=29365) (a:=126) (b:=127) (joinSmall (lo:=29365) (a:=63) (b:=63) sp29365 sp29428) (joinSmall (lo:=29491) (a:=63) (b:=64) sp29491 sp29554)) (joinSmall (lo:=29618) (a:=126) (b:=127) (joinSmall (lo:=29618) (a:=63) (b:=63) sp29618 sp29681) (joinSmall (lo:=29744) (a:=63) (b:=64) sp29744 sp29807))) (joinSmall (lo:=29871) (a:=253) (b:=254) (joinSmall (lo:=29871) (a:=126) (b:=127) (joinSmall (lo:=29871) (a:=63) (b:=63) sp29871 sp29934) (joinSmall (lo:=29997) (a:=63) (b:=64) sp29997 sp30060)) (joinSmall (lo:=30124) (a:=127) (b:=127) (joinSmall (lo:=30124) (a:=63) (b:=64) sp30124 sp30187) (joinSmall (lo:=30251) (a:=63) (b:=64) sp30251 sp30314))))) (joinSmall (lo:=30378) (a:=1013) (b:=1013) (joinSmall (lo:=30378) (a:=506) (b:=507) (joinSmall (lo:=30378) (a:=253) (b:=253) (joinSmall (lo:=30378) (a:=126) (b:=127) (joinSmall (lo:=30378) (a:=63) (b:=63) sp30378 sp30441) (joinSmall (lo:=30504) (a:=63) (b:=64) sp30504 sp30567)) (joinSmall (lo:=30631) (a:=126) (b:=127) (joinSmall (lo:=30631) (a:=63) (b:=63) sp30631 sp30694) (joinSmall (lo:=30757) (a:=63) (b:=64) sp30757 sp30820))) (joinSmall (lo:=30884) (a:=253) (b:=254) (joinSmall (lo:=30884) (a:=126) (b:=127) (joinSmall (lo:=30884) (a:=63) (b:=63) sp30884 sp30947) (joinSmall (lo:=31010) (a:=63) (b:=64) sp31010 sp31073)) (joinSmall (lo:=31137) (a:=127) (b:=127) (joinSmall (lo:=31137) (a:=63) (b:=64) sp31137 sp31200) (joinSmall (lo:=31264) (a:=63) (b:=64) sp31264 sp31327)))) (joinSmall (lo:=31391) (a:=506) (b:=507) (joinSmall (lo:=31391) (a:=253) (b:=253) (joinSmall (lo:=31391) (a:=126) (b:=127) (joinSmall (lo:=31391) (a:=63) (b:=63) sp31391 sp31454) (joinSmall (lo:=31517) (a:=63) (b:=64) sp31517 sp31580)) (joinSmall (lo:=31644) (a:=126) (b:=127) (joinSmall (lo:=31644) (a:=63) (b:=63) sp31644 sp31707) (joinSmall (lo:=31770) (a:=63) (b:=64) sp31770 sp31833))) (joinSmall (lo:=31897) (a:=253) (b:=254) (joinSmall (lo:=31897) (a:=126) (b:=127) (joinSmall (lo:=31897) (a:=63) (b:=63) sp31897 sp31960) (joinSmall (lo:=32023) (a:=63) (b:=64) sp32023 sp32086)) (joinSmall (lo:=32150) (a:=127) (b:=127) (joinSmall (lo:=32150) (a:=63) (b:=64) sp32150 sp32213) (joinSmall (lo:=32277) (a:=63) (b:=64) sp32277 sp32340)))))))))
  have good : (List.range 32404).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 1050000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 32403 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 32403 := by
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


private def packet (i : ℕ) : ℕ := (if i < 267 then (if i < 133 then (if i < 66 then (if i < 33 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else 0))) else (if i < 12 then (if i < 10 then (if i < 9 then 0 else 0) else (if i < 11 then 0 else 0)) else (if i < 14 then (if i < 13 then 0 else 0) else (if i < 15 then 0 else 0)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0 else 0) else (if i < 19 then 0 else 0)) else (if i < 22 then (if i < 21 then 0 else 0) else (if i < 23 then 0 else 0))) else (if i < 28 then (if i < 26 then (if i < 25 then 0 else 0) else (if i < 27 then 0 else 0)) else (if i < 30 then (if i < 29 then 0 else 0) else (if i < 31 then 0 else (if i < 32 then 0 else 0)))))) else (if i < 49 then (if i < 41 then (if i < 37 then (if i < 35 then (if i < 34 then 0 else 0) else (if i < 36 then 0 else 0)) else (if i < 39 then (if i < 38 then 0 else 0) else (if i < 40 then 0 else 0))) else (if i < 45 then (if i < 43 then (if i < 42 then 0 else 0) else (if i < 44 then 0 else 0)) else (if i < 47 then (if i < 46 then 0 else 0) else (if i < 48 then 0 else 0)))) else (if i < 57 then (if i < 53 then (if i < 51 then (if i < 50 then 0 else 0) else (if i < 52 then 0 else 0)) else (if i < 55 then (if i < 54 then 0 else 0) else (if i < 56 then 0 else 0))) else (if i < 61 then (if i < 59 then (if i < 58 then 0 else 0) else (if i < 60 then 0 else 0)) else (if i < 63 then (if i < 62 then 0 else 0) else (if i < 64 then 0 else (if i < 65 then 0 else 0))))))) else (if i < 99 then (if i < 82 then (if i < 74 then (if i < 70 then (if i < 68 then (if i < 67 then 0 else 0) else (if i < 69 then 0 else 0)) else (if i < 72 then (if i < 71 then 0 else 0) else (if i < 73 then 0 else 0))) else (if i < 78 then (if i < 76 then (if i < 75 then 0 else 0) else (if i < 77 then 0 else 0)) else (if i < 80 then (if i < 79 then 0 else 0) else (if i < 81 then 0 else 0)))) else (if i < 90 then (if i < 86 then (if i < 84 then (if i < 83 then 0 else 0) else (if i < 85 then 0 else 0)) else (if i < 88 then (if i < 87 then 0 else 0) else (if i < 89 then 0 else 0))) else (if i < 94 then (if i < 92 then (if i < 91 then 0 else 0) else (if i < 93 then 0 else 0)) else (if i < 96 then (if i < 95 then 0 else 0) else (if i < 97 then 0 else (if i < 98 then 0 else 0)))))) else (if i < 116 then (if i < 107 then (if i < 103 then (if i < 101 then (if i < 100 then 0 else 0) else (if i < 102 then 0 else 0)) else (if i < 105 then (if i < 104 then 0 else 0) else (if i < 106 then 0 else 0))) else (if i < 111 then (if i < 109 then (if i < 108 then 0 else 0) else (if i < 110 then 0 else 0)) else (if i < 113 then (if i < 112 then 0 else 0) else (if i < 114 then 0 else (if i < 115 then 0 else 0))))) else (if i < 124 then (if i < 120 then (if i < 118 then (if i < 117 then 0 else 0) else (if i < 119 then 0 else 0)) else (if i < 122 then (if i < 121 then 0 else 0) else (if i < 123 then 0 else 0))) else (if i < 128 then (if i < 126 then (if i < 125 then 0 else 0) else (if i < 127 then 0 else 0)) else (if i < 130 then (if i < 129 then 0 else 0) else (if i < 131 then 0 else (if i < 132 then 0 else 0)))))))) else (if i < 200 then (if i < 166 then (if i < 149 then (if i < 141 then (if i < 137 then (if i < 135 then (if i < 134 then 0 else 0) else (if i < 136 then 0 else 0)) else (if i < 139 then (if i < 138 then 0 else 0) else (if i < 140 then 0 else 0))) else (if i < 145 then (if i < 143 then (if i < 142 then 0 else 0) else (if i < 144 then 0 else 0)) else (if i < 147 then (if i < 146 then 0 else 0) else (if i < 148 then 0 else 0)))) else (if i < 157 then (if i < 153 then (if i < 151 then (if i < 150 then 0 else 0) else (if i < 152 then 0 else 0)) else (if i < 155 then (if i < 154 then 0 else 0) else (if i < 156 then 0 else 0))) else (if i < 161 then (if i < 159 then (if i < 158 then 0 else 0) else (if i < 160 then 0 else 0)) else (if i < 163 then (if i < 162 then 0 else 0) else (if i < 164 then 0 else (if i < 165 then 0 else 0)))))) else (if i < 183 then (if i < 174 then (if i < 170 then (if i < 168 then (if i < 167 then 0 else 0) else (if i < 169 then 0 else 0)) else (if i < 172 then (if i < 171 then 0 else 0) else (if i < 173 then 0 else 0))) else (if i < 178 then (if i < 176 then (if i < 175 then 0 else 0) else (if i < 177 then 0 else 0)) else (if i < 180 then (if i < 179 then 0 else 0) else (if i < 181 then 0 else (if i < 182 then 0 else 0))))) else (if i < 191 then (if i < 187 then (if i < 185 then (if i < 184 then 0 else 0) else (if i < 186 then 0 else 0)) else (if i < 189 then (if i < 188 then 0 else 0) else (if i < 190 then 0 else 0))) else (if i < 195 then (if i < 193 then (if i < 192 then 0 else 0) else (if i < 194 then 0 else 0)) else (if i < 197 then (if i < 196 then 0 else 0) else (if i < 198 then 0 else (if i < 199 then 0 else 0))))))) else (if i < 233 then (if i < 216 then (if i < 208 then (if i < 204 then (if i < 202 then (if i < 201 then 0 else 0) else (if i < 203 then 0 else 0)) else (if i < 206 then (if i < 205 then 0 else 0) else (if i < 207 then 0 else 0))) else (if i < 212 then (if i < 210 then (if i < 209 then 0 else 0) else (if i < 211 then 0 else 0)) else (if i < 214 then (if i < 213 then 0 else 0) else (if i < 215 then 0 else 0)))) else (if i < 224 then (if i < 220 then (if i < 218 then (if i < 217 then 0 else 0) else (if i < 219 then 0 else 0)) else (if i < 222 then (if i < 221 then 0 else 0) else (if i < 223 then 0 else 0))) else (if i < 228 then (if i < 226 then (if i < 225 then 0 else 0) else (if i < 227 then 0 else 0)) else (if i < 230 then (if i < 229 then 0 else 0) else (if i < 231 then 0 else (if i < 232 then 0 else 0)))))) else (if i < 250 then (if i < 241 then (if i < 237 then (if i < 235 then (if i < 234 then 0 else 0) else (if i < 236 then 0 else 0)) else (if i < 239 then (if i < 238 then 0 else 0) else (if i < 240 then 0 else 0))) else (if i < 245 then (if i < 243 then (if i < 242 then 0 else 0) else (if i < 244 then 0 else 0)) else (if i < 247 then (if i < 246 then 0 else 0) else (if i < 248 then 0 else (if i < 249 then 0 else 0))))) else (if i < 258 then (if i < 254 then (if i < 252 then (if i < 251 then 0 else 0) else (if i < 253 then 0 else 0)) else (if i < 256 then (if i < 255 then 0 else 0) else (if i < 257 then 0 else 0))) else (if i < 262 then (if i < 260 then (if i < 259 then 0 else 0) else (if i < 261 then 0 else 0)) else (if i < 264 then (if i < 263 then 0 else 0) else (if i < 265 then 0 else (if i < 266 then 0 else 0))))))))) else (if i < 401 then (if i < 334 then (if i < 300 then (if i < 283 then (if i < 275 then (if i < 271 then (if i < 269 then (if i < 268 then 0 else 0) else (if i < 270 then 0 else 0)) else (if i < 273 then (if i < 272 then 0 else 0) else (if i < 274 then 0 else 0))) else (if i < 279 then (if i < 277 then (if i < 276 then 0 else 0) else (if i < 278 then 0 else 0)) else (if i < 281 then (if i < 280 then 0 else 0) else (if i < 282 then 0 else 0)))) else (if i < 291 then (if i < 287 then (if i < 285 then (if i < 284 then 0 else 0) else (if i < 286 then 0 else 0)) else (if i < 289 then (if i < 288 then 0 else 0) else (if i < 290 then 0 else 0))) else (if i < 295 then (if i < 293 then (if i < 292 then 0 else 0) else (if i < 294 then 0 else 0)) else (if i < 297 then (if i < 296 then 0 else 0) else (if i < 298 then 0 else (if i < 299 then 0 else 0)))))) else (if i < 317 then (if i < 308 then (if i < 304 then (if i < 302 then (if i < 301 then 0 else 0) else (if i < 303 then 0 else 0)) else (if i < 306 then (if i < 305 then 0 else 0) else (if i < 307 then 0 else 0))) else (if i < 312 then (if i < 310 then (if i < 309 then 0 else 0) else (if i < 311 then 0 else 0)) else (if i < 314 then (if i < 313 then 0 else 0) else (if i < 315 then 0 else (if i < 316 then 0 else 0))))) else (if i < 325 then (if i < 321 then (if i < 319 then (if i < 318 then 0 else 0) else (if i < 320 then 0 else 0)) else (if i < 323 then (if i < 322 then 0 else 0) else (if i < 324 then 0 else 0))) else (if i < 329 then (if i < 327 then (if i < 326 then 0 else 0) else (if i < 328 then 0 else 0)) else (if i < 331 then (if i < 330 then 0 else 0) else (if i < 332 then 0 else (if i < 333 then 0 else 0))))))) else (if i < 367 then (if i < 350 then (if i < 342 then (if i < 338 then (if i < 336 then (if i < 335 then 0 else 0) else (if i < 337 then 0 else 0)) else (if i < 340 then (if i < 339 then 0 else 0) else (if i < 341 then 0 else 0))) else (if i < 346 then (if i < 344 then (if i < 343 then 0 else 0) else (if i < 345 then 0 else 0)) else (if i < 348 then (if i < 347 then 0 else 0) else (if i < 349 then 0 else 0)))) else (if i < 358 then (if i < 354 then (if i < 352 then (if i < 351 then 0 else 0) else (if i < 353 then 0 else 0)) else (if i < 356 then (if i < 355 then 0 else 0) else (if i < 357 then 0 else 0))) else (if i < 362 then (if i < 360 then (if i < 359 then 0 else 0) else (if i < 361 then 0 else 0)) else (if i < 364 then (if i < 363 then 0 else 0) else (if i < 365 then 0 else (if i < 366 then 0 else 0)))))) else (if i < 384 then (if i < 375 then (if i < 371 then (if i < 369 then (if i < 368 then 0 else 0) else (if i < 370 then 0 else 0)) else (if i < 373 then (if i < 372 then 0 else 0) else (if i < 374 then 0 else 0))) else (if i < 379 then (if i < 377 then (if i < 376 then 0 else 0) else (if i < 378 then 0 else 0)) else (if i < 381 then (if i < 380 then 0 else 0) else (if i < 382 then 0 else (if i < 383 then 0 else 0))))) else (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 0 else 0) else (if i < 387 then 0 else 0)) else (if i < 390 then (if i < 389 then 0 else 0) else (if i < 391 then 0 else 0))) else (if i < 396 then (if i < 394 then (if i < 393 then 0 else 0) else (if i < 395 then 0 else 0)) else (if i < 398 then (if i < 397 then 0 else 0) else (if i < 399 then 0 else (if i < 400 then 0 else 0)))))))) else (if i < 468 then (if i < 434 then (if i < 417 then (if i < 409 then (if i < 405 then (if i < 403 then (if i < 402 then 0 else 0) else (if i < 404 then 0 else 0)) else (if i < 407 then (if i < 406 then 0 else 0) else (if i < 408 then 0 else 0))) else (if i < 413 then (if i < 411 then (if i < 410 then 0 else 0) else (if i < 412 then 0 else 0)) else (if i < 415 then (if i < 414 then 0 else 0) else (if i < 416 then 0 else 0)))) else (if i < 425 then (if i < 421 then (if i < 419 then (if i < 418 then 0 else 0) else (if i < 420 then 0 else 0)) else (if i < 423 then (if i < 422 then 0 else 0) else (if i < 424 then 0 else 0))) else (if i < 429 then (if i < 427 then (if i < 426 then 0 else 0) else (if i < 428 then 0 else 0)) else (if i < 431 then (if i < 430 then 0 else 0) else (if i < 432 then 0 else (if i < 433 then 0 else 0)))))) else (if i < 451 then (if i < 442 then (if i < 438 then (if i < 436 then (if i < 435 then 0 else 0) else (if i < 437 then 0 else 0)) else (if i < 440 then (if i < 439 then 0 else 0) else (if i < 441 then 0 else 0))) else (if i < 446 then (if i < 444 then (if i < 443 then 0 else 0) else (if i < 445 then 0 else 0)) else (if i < 448 then (if i < 447 then 0 else 0) else (if i < 449 then 0 else (if i < 450 then 0 else 0))))) else (if i < 459 then (if i < 455 then (if i < 453 then (if i < 452 then 0 else 0) else (if i < 454 then 0 else 0)) else (if i < 457 then (if i < 456 then 0 else 0) else (if i < 458 then 0 else 0))) else (if i < 463 then (if i < 461 then (if i < 460 then 0 else 0) else (if i < 462 then 0 else 0)) else (if i < 465 then (if i < 464 then 0 else 0) else (if i < 466 then 0 else (if i < 467 then 0 else 0))))))) else (if i < 501 then (if i < 484 then (if i < 476 then (if i < 472 then (if i < 470 then (if i < 469 then 0 else 0) else (if i < 471 then 0 else 0)) else (if i < 474 then (if i < 473 then 0 else 0) else (if i < 475 then 0 else 0))) else (if i < 480 then (if i < 478 then (if i < 477 then 0 else 0) else (if i < 479 then 0 else 0)) else (if i < 482 then (if i < 481 then 0 else 0) else (if i < 483 then 0 else 0)))) else (if i < 492 then (if i < 488 then (if i < 486 then (if i < 485 then 0 else 0) else (if i < 487 then 0 else 0)) else (if i < 490 then (if i < 489 then 0 else 0) else (if i < 491 then 0 else 0))) else (if i < 496 then (if i < 494 then (if i < 493 then 0 else 0) else (if i < 495 then 0 else 0)) else (if i < 498 then (if i < 497 then 0 else 0) else (if i < 499 then 0 else (if i < 500 then 0 else 0)))))) else (if i < 518 then (if i < 509 then (if i < 505 then (if i < 503 then (if i < 502 then 0 else 0) else (if i < 504 then 0 else 0)) else (if i < 507 then (if i < 506 then 0 else 0) else (if i < 508 then 0 else 0))) else (if i < 513 then (if i < 511 then (if i < 510 then 0 else 0) else (if i < 512 then 0 else 0)) else (if i < 515 then (if i < 514 then 0 else 0) else (if i < 516 then 0 else (if i < 517 then 0 else 0))))) else (if i < 526 then (if i < 522 then (if i < 520 then (if i < 519 then 0 else 0) else (if i < 521 then 0 else 0x31b33a62b1943c95644a1f98e606642da13c085038a16b08882cc0b6000031b2dc62c094b498846920c0ef86b82fc14f88dc3b216b08a82a80a6000031b27f02bd147095a4521fc8ebc68e2ee14908dc3be17c091030c0be000031b22162bf149c9a246d2100f006b02ed146889437e17108a02c40b4000031b1c4e2b794289524521f88e5466e2d213e888c39416b08a82c80b2000031b16852b3944c9684511f48e4c6702df142888038e16f08882fc0ae000031b10e62a313cc9304391ee0e4064a2c4133884437215508282c80c4000031b0b0b2be944895644f1f58e4466c2cd13808743a216f08902b80c0000031b054d2b1942c9684571fe8ea06962eb14808b039416208582c40b6000031aff8b2ae942c94c4481f10e0864a2ce13a887439a17008282b80aa000031af9a92c414a899247320a8eb86a22f914b09003ba18709503200c2000031af3e92b2142c9484461f58e546762de13d086837816708102cc0b8000031aee082c2949c99846e2098ed86b22ff14f090c3ae17408f03200d0000031ae8532aa141096a4592008e6467e2e113f88943a616f08702c80b8000031ae2972b1942496845a2020e7867a2df14288c439817208d82c00be000031adce72a2937891a43b1ea8dec6582d713b883c34e15308382ac0a4000031ad7502a093b09124341ec0dfc6602d413f08a83a017d09302f80ba000031ad1712c414ac9a847820c8ecc69a2f214c08e43c017908b02bc0b6000031acbb22b413e894a4592008e7869c2ea14c88d43c218208f02f80b8000031ac5b42cb14e89a24772090eac6882e214288a439417a08e831c0d0000031abfe72b6146098046e2038ebc6a02f114c08d83bc18008702c00b2000031aba142ba94789844622040ea46942f414908b839e17509283000c2000031ab4442bc94789844521fb0e886822e214408cc3a217908e83140bc000031aae7f2b8145c99446c2058ed46b02f714d89003be17d08d02e40c0000031aa8ac2b594189544401f20e0865e2e714208c439c17909082fc0b8000031aa2ec2af941c9604512038ec86a82fa15589303e218809783400d0000031a9d162bd948498a45f2058e946802e414688c43ba18808e03140ca000031a97542b794189624591f88e4c6562bf138084836e1630818284092000031a917e2c1147497c45a2018ea06862eb14708a039c17308b03040d4000031a8bae2bc14749784622070edc6ae2fe14c88fc3c618308f83240dc000031a85d92ba94589684511f98e4065e2d2138884838216b08182c40ac000031a7fd72d3150c9d44862128f006c02ff15108f03ae17908f83000b8000031a7a0e2b8946897a4642000ebc6aa2f814808b83a216f08a82e80c2000031a74712a293d494844c1f78e406702e314688d439e16808402bc0a4000031a6e9a2ba94709804672010e846802ed14908e83b2189096033c0c6000031a68f52a613c09384481f58e286622d713d887c38a16b08803080c8000031a63502ac93ec9564501f60e346682cd13b086037e16808382c00ae000031a5d752c094689844602050e886982ee14988d43a017608902b40b6000031a57742d194e49bc47720e8ef46ac2f814908e03b417d08e03080c4000031a51b72b414209564491f88e706822df13f087037c16c08983100bc000031a4bc72cc14c89b047c20e8ef06b82ec14888e03a016f08c82e00b4000031a462e29d938c8fe4321f40e046522d313888803a817808a82c40ac000031a407d2a813ec9424451f20e146562cd134884437215908402b40b8000031a3a7b2d495389ce48a2170f486d8306154090c3bc17608b82d40bc000031a34c22b0941894c44b1f70e646782e614808e43bc18209383200ba000031a2f1f2a493f493c43f1ef0df06442d613a885038215e08382d00b2000031a295f2b9947898445e2000e6c66e2da14388a439a16808782bc0aa000031a23962b514489604591ff8e906902ec14a889c3a616a08582dc0b6000031a1da82c2149c9aa47c20b0f006d62f814c09203dc18a09383300d4000031a17da2b8145096e45a1fb8e686982fa14f090c3be18b09483400c0000031a12202b1942496c4641fd8e8466e2d113c086438416708982fc0d0000031a0c462c014bc9a047220c0f006982f114988f03b217c08c83040c8000031a06862b8145895a4581fd0e4066c2df14008b03b217c08f02f80cc000031a00a22c614ac99246f2088ed86b82fb14988e03ba18008f02d40b60000319faa52cf952c9e44902150f246c22f715208d43a618008e83380cc0000319f4f52a593d893e4431f30e546602ce13d086c37215c08282a409a0000319ef292c1149498e47b2150f086d230215889483ea18b09603100d60000319e97e2ae13f092c4351ef8e1c6602da13e085438416f08802d00c40000319e38f2c414a897e4692020e986922ef14608d43b416c08502d40b20000319ddc62b6143495644e1f68e4c6602d613f084437c16308682bc0b80000319d80e2ae942896a44a1f18e0864c2bf133883835e15f08282b00960000319d2342c514749684521fe0e606782e314708bc3a617208b83080c80000319cc672b8142c9604592020eb86842ec14808c43b017b08f03100cc0000319c64a2e015989fc49a21d0f646e22fc14c08e03a016a08902e00bc000)) else (if i < 524 then (if i < 523 then 0x31ca4c32b7945c98646e20c0f0c6b630415489003c4178090031c0ca000031c9f2729d93949324451f48e306622d313b087037e17308f83080be000031c99582b9145896e44f1fa8e4c67a2ee14b88b83a617f09403100c0000031c937a2be147898e46820b0ef46ba2fb14c08e03a417a08a02e80c2000031c8d8c2ca14cc9b247a2120f106da31215d89543de18108d03040be000031c87e12a493ec93844f1f70e5c66c2df14508e03a217708d82d00bc000031c82082b7143897a4672068eac6ac2e914708a438c16208402c40bc000031c7c5b2a7139c9124311f00e1c6682de142089439017408882e00be000031c76ab2a7141895a4552030e8468a2e614488903a417f08b02f40bc000031c70fc2ab93f093843e1ee0e1c65e2d714108bc3a417208e02f80c6000031c6b6529f138490042b1e38dd462c2bb136882c36215d08082980ac000031c657a2c994a499a4601fd8e906a62eb14a08983a817a08d82fc0b4000031c5fc72ae94189364461f10e246682d613b887839417108c82e80bc000031c5a042b714389564581fd0e746682dd13b085837c15d08282ac0c0000031c54312b8144c96645c1fe8ea46882eb14a88e43a817708982c80be000031c4e692b2945897c4602050ec46bc30014c88ec3d217808f02e40cc000031c48932b694489604491ff8e786682d213b084c36615508382c00b0000031c42a52c494a09804622090ebc6802e314508d03a017308d02d00ac000031c3cc52c214a499c4722080ea469c2f014888cc3a417008b82e80b6000031c37142aa13c493043b1ef8e1c6462c0137883c37a16a08a02c40ac000031c313c2c014a097c4521f50e346582d513e087c39617308803100b2000031c2b8a2ad13d892a43d1ee8e046402c7135887039016b08c03000c2000031c25e02a713e89304421f68e4465a2d613b084838016608782e00be000031c200f2b6943c9784692028e9c69c2e213f887437c16708a832c0c2000031c1a2a2c694b898a4632040ed46a62ec14608ec3a417408702bc0a8000031c14412c914b099a46f2068e8c6962e714788cc3a417809083580e4000031c0e9f2a613a492843f1f18e206742da13c085036a16308602b80b8000031c08d82af942c95c4411f40de464c2d413c087038416108682dc0ca000031c033f2a193b491e43c1f00e206542d4141088438216708982d40c6000031bfd892ad94289664591fb0e6c67c2e114008a438016d08682d80b8000031bf7c02b3944c96445e1fa0e6c6662d713e087c37415b08482bc0b2000031bf2002ba145497e4672098f006e031b15f09483de19409b83380cc000031bec442b014109404441f90ea868e2f114708b43a417e09102c80ac000031be6912ab93f095244f1fa8e6467e2e914508e83ba17308e03100ca000031be10929793708fe41d1e38da46382c9138884c37a15707b828c0ac000031bdb0e2d214fc9ba48f21a8f2c6de308157090c3ca18008e82ec0aa000031bd5532ab93d894643e1f70e3066c2d313e88843a817d08f83280de000031bcfa42ae94509624581fc8e746622d4140087c39216308702c00b8000031bc9d42b494349584491f98e6067e2e814908c03b217708d02ec0c2000031bc3ee2c714dc9b84872130f046bc2fd15008c83a416d08582c80b2000031bbe332ad93e894c4511fd0e6c6742d6138887438815a07e02a00ac000031bb89e29f13d09344431f28e2c64c2cf13a085437016608a02e40be000031bb2c52bc143c96645a1ff0e946802e514008a83a417908782d40ae000031bad032b114309564551f88e586822e314508b039016f08a82f00ba000031ba7202c114909a847a2070eec6ba2f8148089c394177090833c0d6000031ba19129c936890e4251e78e086422bb130083837215f08302b40a4000031b9bb82bb94509784602020e8c6a02f914e08fc3b617208e02f40a4000031b96102a813c892a4381f10e546702e0141087c39a17108a02e00b8000031b90602aa140c94243a1ef0e146582d513e085c37416708a82e00b2000031b8aa32af13fc94c44f1f78e406782df142889c37616608a83000c0000031b84c12c6149c9aa4842160f3c6e031315b09543fe18e09503140dc000031b7f122af941896244d1fc0e486802ea14708c83ae17908d02f00b2000031b79482bb94849984612068eb06a02e914408b03ac17108582e00b4000031b737e2b6942494c4421f50e5467e2e4138086437216908882c00b8000031b6d972c214d89a84802140f006ce31915989283d618b09a03600d6000031b67c52ba14789764602018eb46982eb14688cc3a017008982dc0b8000031b61e22bd147c97845f2050ea06822e113f08a438816408502e40b8000031b5c252b414609804622048eb46a02f314989003c218e08f03140d6000031b56542b494409524522000eb86982ea144089c39c16908902c00a6000031b50642c214909864601ff8e886862eb14908e43b8183096830c0c8000031b4ab62ab13d892a4421f20e1864a2d0133885437e16b08782e40ba000031b44f52ae941c9444481fc0e8c6982e714408cc3ae18209082ec0d0000031b3f342af13f49524411f28e346642cf139885437216108782d00ba000031b396c2b1141c94e4441f68e3c6642d813a086c39216b08802c40bc000 else 0x31e17542c0146c96e4602028e986962e714908b83aa17208782ac0ac000031e11742c214989904682048ec06b630114e88e83b417808a02e40ce000031e0bb22b8145896a45b1ff8ea069c2eb14a88fc3c218908f02f00c2000031e061529d13648f441d1e80dc862e2ba131086436815a08482c40a8000031e00492b7946c9824611fc0e746882e5143888839016908603000c0000031dfa6d2bf148098c45f1fd8e646662d614408a039216d08502d00b6000031df4a32b4942095a44e1ff0e6c68a2e714a08b83a016a08182a80a0000031def0729e93d493443d1f20df86642d5141088438a16f08902e00b2000031de92b2bb947099047820f0f006ce30e156093c3d618509383140da000031de3842a393b49204281e40dd06382be12f083437215d08182b00a4000031dddc72b1941c96c45b2050ec46b230c151891c3c618909703440de000031dd7ff2b814289724601ff8e9c6822e214388e83a217408902c80b4000031dd24f2ac141895a4491f58e0464e2cc137083836216408883000c2000031dcc682c1147c97e4571fb8e7067a2de13f887439217009002f00c2000031dc6a32b8145c97a4611ff0e7c6982e814b09143cc17f08f02f80bc000031dc0bf2c094909884622010e9868c2f114c88c03a416408802a00b0000031dbaed2bb147096a4612040e9068a2e714188b839a16c08a83140bc000031db5542a013989044341ea8e1462c2b412f881036e15107d8278082000031daf9a2b5940c95244f1fc0e646882df14388bc39a17108882d80ba000031da9ec2a613c093443a1ef8e4c65e2d313d085c38016408702ac0a6000031da41b2bb947c9844612080e946842da13f889c38816507f82c40a8000031d9e3f2bc14889884632058ec869a2e414989103be18309382fc0c4000031d98592c1945c9584501fa8e8067a2df144889039416c08802d40b2000031d92932ba14749804581fb8e8c69a2ec14a89083d418909383380de000031d8cbd2ba947c9a847d20b0ea46942ec14888d03a417108d02f40be000031d86f22b6142c96245f1ff8e846882ed14c08dc3aa17508c82d00c6000031d813b2b114209564511fc0e306622d613d885038016e08902e00ba000031d7b5d2c0147c9784541fa0e686722f014f08f83c618008f82fc0c8000031d75b42a213a89164271e48db86242ba133885837a16408582d80b8000031d6ff62ab94009524471f70e6067e2d6139885037a16308482d80b6000031d6a3f2a793e89364461f20e3866c2db13d888c39c16b08702e80d0000031d64722be145497a4602010e486762e114508c83aa17c08d02ec0bc000031d5e802cc14d49b448720e8eec69c2f014d08f43c618309303140c6000031d58972bf14689764561fa0e6c6842e614a09003bc18008c83000d4000031d52c42b8145098a4691fe0e886a02f714488d43b018708e83080b2000031d4ccd2c894c899646f2078eb86c02fe14d88dc3b017709003180be000031d47082b194289604521fa0e5c67a2dd14008803a017008402c80a4000031d41502b1942496e4501f68e6067a2e014588d43ac17c08a82d40bc000031d3b712bc146897446820b8ed46b0302154891c3c818109202f00c6000031d358a2c1148c9824692070eb068c2ee14708b03ac18409703180bc000031d2fd02af141894c4571fa8e746922f014808d43c217d08e82ec0ae000031d2a002ba146097a4491fa0e546842e914908ec3c6180091030c0bc000031d24492ac13f093643f1f10e086522d413f088c38016808903040ca000031d1e792b9144497445a1fe8e7c6982f414988f43d217e09783180b8000031d18972bd946097c4602018e8c6922fb14e09083c018108d03040b4000031d12d92b0941495844f1fb0e646722d513e889838e16b08a82f80c6000031d0d282ab13ec9484401f68e1864a2d213b087038c17008d83240c0000031d073b2bf945c9824672058eb069a2ea14d88f43ac17908882c80b0000031d016c2b4942094844c1fd8e9868a2e4140088039216f08882dc0ba000031cfbcf29c936c8ec4291ed8df46402c313a088038e172080829c0b0000031cf60a2b5941495245e2078ea46a22fc14f88e43b017008982f80b6000031cf04f2b114049444591fe0e5c6782da141889c39217108b02f40c6000031ceaae2a594149504501fd0e8c68a2e314488a439e16e08d03140d0000031ce4dd2b6143494c44e1f38e3c66a2de141888839016609002fc0ae000031cdf162b8147897e4652070ea86962e414188a439017108b02ec09c000031cd9452c194a49aa48320e0f086ce30f15c090c3c218708f83000ba000031cd3632c2948c99047920b0ed06bc2fe148088c39816d08882bc0ae000031ccd4e2dc95549e248c2180f5c6f0312156090c3ca17b08c82cc0c2000031cc7742c494989864581fd0e606822ea14a88c43b617408902dc0be000031cc17d2ce14f49c047c20d8f0c6c830314f08e43a217908e02f00b8000031cbbff29493148cc4151dd8d745fe2a612987f036215408082ac0b4000031cb6202c2947c99646c2050ea06962fd14688bc3a417708e02fc0b6000031cb0592b2143495e44f1fc0e6c69a2e914b08e83aa18008e02e40b8000031caa8f2bd945896a45f2010eb46b030014f08dc3b817c08e82cc0be000) else (if i < 525 then 0x31f89922a894049504531f80e8467e2d513c888438416608982d00c4000031f83f02a013ac91442e1e98de86462c3138884836a15908402e80ae000031f7e402ab94049504531fe8e9c6962e514708bc3b018408f83080d8000031f786d2bc944496a45c1fa0e846702dd13e088439215d08282980a8000031f72a62b0141495e45a1f98e5865e2cf13b086437815f080829c09c000031f6cf52a993f09424501fb0e686802ec14788f03b817708d82e40ca000031f66f92d014f09ce4832110ee86b030f15689143d0195099831c0be000031f613c2b194109524481f90e5c6842e914988dc3a217508d82d00ac000031f5b782b6944895c4581f98e486782de13f885437c16708d03280c8000031f55922c494e09a846e2090eb46a62ee14588b038216008502c00b6000031f4fc52b714649764632050ebc6aa2fc14e090c3c617c08f82f00c6000031f49e52c1148899046d2010ea467c2e214708a83a217508a03000bc000031f44172b694189524512020e806902f714508c83b217d08882980a2000031f3e4b2b9145097a45f2038ecc69a2ec14208a43ae17b08f830c0b8000031f388e2ad140494a44d1f60e446682d4140088c3a217708902cc0a8000031f32bd2bb944c9684591fd8e846842de14208a439416a08a82dc09e000031f2d1b29d93bc9224351ec8e046382cc13b084036615908682b40a8000031f27492bd144c9604491f30e4c65a2df14308a83a817e08b02bc0ac000031f218a2b814489604501ff0eac6b6308152890c3cc194098831c0ba000031f1bc52bb946496645a1fc0e706942e514688a839217808c82ec0b2000031f15f62b5944098245f2030ec869e2ed151090c3ca18108f83100c6000031f10022c914d89a847a2100ee869c2f814988f03aa17008982c00ae000031f0a472aa141c9684531fe8e7867e2e214388c439c17908d82d00ba000031f04702b9147c9824682050eb069c2fc15089043c217908a83240ba000031efec42ac94109424441f18e086462c2133883437016408802b80b0000031ef91e2a5139091e43b1f08e186602d113a887c39c16c08602b80a8000031ef32e2c714d09ae4712100f0c6d030c15489283d218408f82e80b0000031eed7a2ab93dc94c4441f48e5865e2d513b086837c16008a02dc0c6000031ee7c02b3142c96644d1f60e4c6542c813a887c38615e08b83080c4000031ee2202aa13e09404401f10e046742d713e889c38a17208c02e40b8000031edc612b2941093e44a1fb8e4c66e2db14388a839c16f08802e40b0000031ed6b02aa13f49544511f78e4866a2df13f088c3aa17208d02e40ba000031ed0d12c2148098c47120c0eec6ae2e714688c43ba17d09583380dc000031ecafa2bf94b09884602040e7066c2d1137088038e16b08782dc0bc000031ec5332b6942095c4511fa0e5066a2e213d087c38816808782d80b2000031ebf5c2bd146096845a1fe0e9468c2ee14a08f43c418508e82f00ca000031eb97b2c294c09a84722098ecc6bc2f714b08d839e16b08902e40bc000031eb3bd2b294349764622018eb06942ed14788ec3ba17b08c82e00bc000031eae122ab93e893c4431f58e386542d113c085c38216a08602c00ae000031ea8562ae93f09344421ef8e0865c2db13f887838217308602ec0c6000031ea2922b414289604541f88e8068a2e5145889838816508882f80be000031e9cc72b7143c97c4612010ec06c030a157894c3da18409003300dc000031e970f2aa13cc92242c1eb0dc46422ca138089039e16e08c82f00c4000031e911e2c6149897e4642050e9468c2ed14308bc3ac17308a03000c0000031e8b772a513e893443f1ef0e0462e2bf12d881836216008282bc0a8000031e85c12ac13d89404451f60e1c6482d7140887038015c07e82980a8000031e7fd02ca14d09c448e2180f446ea30815209083c618408d82f80aa000031e7a042ba946094844b1f80e5066a2d813e886038016508e83300c4000031e74362b8142c95c4542000e7c6782df14688e43ae17608d82cc0c6000031e6e5b2c214a098246c2040ecc69e2f714c08c439616608682c40aa000031e68732c3948898c4692030e9c6922e614608dc39617908d83080be000031e62822cc94b899646e2088e9869e2f914788c83ae17208982d40c8000031e5c9d2c2149098a4612050eb86a62fd14e08cc39017108482b80a2000031e56da2b614749844692068ec06ae2f614a89043e018d094834c0ce000031e51382a513d49324471f30e286662dd13f88c43a017a094031c0d6000031e4b7a2b194189584591fe0e9c6882e014508bc3a617908e83180c2000031e45d12a493c89284351ef8e0865c2df141885436a15d08602cc0b2000031e3fea2c794bc9a446f20c0f146d430e15709143c217d08b82d00c6000031e3a162bc149496c45f1fe0e8c6842db14288b43ae17508f82f40bc000031e345f2ae14089564501fa0e646642d413c885c35a15708002b00b8000031e2e9e2b4941496c46b20b0ea46862e9141087437a16108202ac0a0000031e28b92c2147497c4622028e906742df13e887c39617709003400cc000031e22ed2b8947c97e4602000eb06982ef14c08c43ba18009102e80b0000031e1d2c2ab93dc94e4421f68e6c66c2d413c888838e17108d02d80ba000 else 0x320fadd2bc147899447120b8e946882e314488c83b016d08b02ec0c80000320f5172b6943095444c1f40e5466e2da14488cc3a817c09603180ca0000320ef302c4146096a44e1f78e6067e2e714908c43b017708d82fc0c20000320e9452c014a09944632088ee469a2e514308e03bc179092031c0c40000320e37d2b514189564491f80e5867e2f514b88ec3be17908d02e40b60000320dde129c938c9164301ed0e186462ca135087037816708702a80980000320d81c2b1941894a44e1fc0eb46a82fb15088fc3aa17908982e80be0000320d26a2aa14149664521f88e746822d713c087c38016f08802c40b40000320cc9d2b694589724581fd0eb46a02f314708c039a16f08482c80b20000320c70329c138c91043a1ed8df863c2d9140888438616208302dc0b00000320c13a2b8142c95c44a1fd8e686842e314208b439217409003100be0000320bb5e2c3948c98846e20e8edc6ae2f614d08fc3b617208882d40b00000320b59c2b9146096c4521ff0e7c6882e1140089839e17208982f40d00000320afa62cf15049ba48220f0ee86aa2fe15188dc3b218209282f00ba0000320a9fb2a913e09184401f48e506562cb13a08943a817508e82d40a60000320a43b2ae141c95044f1f80e6c6802ea14088b039a17508f03100bc00003209e872af14089544471f68e2c6542d714088943a616708682c40b6000032098af2c2148c98445b1fb8e706842e6142089c38016208302cc0ba000032092f52b0143895844c1fd8e686842f114708e43a617308a82f00c200003208d512aa93f89344491f68e3864c2cc13c087838416e08c82d40a8000032087ad2a513b89284341ee8e146522ce14008783a017808d831c0c8000032081ef2b0941096a4551fd0e8c67a2e414608b83a016a08b02f40be00003207c062c2148896c4581fb0e406702e114288c03aa18008f82f80ce0000320762d2be147c98046a2040ec86a62ee14488cc39816d08b83040c6000032070572c194c099e46e2058ebc6962f114708a83a217608d82d40c600003206a6e2ca14ec9b848320e0edc6be30115809243d218409482f80c2000032064ba2aa13b09184361f48e3c6542cc136084835a15807d02900b600003205f182a393bc90e4281ea0db86282ba131882837816208c82b80ba0000320592a2c494d09ae47920d0ee06b02f314d89103b617e08d03040c4000032053722ac93d492c43a1f38e1c6542d0134884435e15208082940a000003204d9e2b8145c9724611ff8e606782e113d088c3a817308e02e80b2000032047d32b894609824702090ed06aa2fa15609103dc18a093030c0c20000320421d2ad14089424471f60e406722eb14c88b83a617008c830c0d000003203c622af13f495a45f2050e906842d913d08ac3a418108a02ec0b0000032036b42a613b09184361ef8dd865a2d4138085837e16b08a82d00bc000032030e02be146896a45e1f98e886802e814688a839817108982d00b400003202b412a293a89304381f10e206502ca13d087437415908182c40b0000032025872a813e493e4451f48e386602cd13b888038216408a02dc0b600003201fa92bb946897a45c1fd8e906882e714688b43ac17208982fc0d8000032019f42a893e092443e1f58e5068a2ea14a08b83a416c08703040b00000320145629e13549064291de0da860a2b012b87f035014e07c02840a600003200ea22ad941497645d1ff8e8068e2ee144888437e16208702e40b2000032008e22ad141095c44f1f60e646742d713b087038616608682c80ba000032003182b3941493e44c1f88e306642d1137887035815f08382b00a2000031ffd4b2bc146c9884742068ed86ae304157890c3bc17c09303080b6000031ff7b22a113b892a4461f78e4467a2e614b08f03b817c08d83200d6000031ff1d92bf948098e4622020e5c6742d6139081c36e16307f82840a0000031fec172ac93e895a44c1f78e5c6782d513f889438617208a82e40ca000031fe62f2c714c49b046b2050ecc68c2eb144089838816c08682e40c0000031fe0762ad13e493a4411f40e686682d413b886838a17908a82e80c2000031fdab22b6940c94444a1f60e5466e2dd14188a439416808102a4098000031fd4ed2af140c94a44d1f90e6c6722da14688a438c16908282ac0c0000031fcf3f2a393a89204351ee0dd463c2cb139086037a16a08402d00c2000031fc9612c2149099446f2060e6c6802e214108bc3ae17008682c40ae000031fc3832c1947c97e4641fd8ea468e2e114388a439c17008d02c809e000031fbd942c914ec9b848220d0ed86b630115208e43c218208e82e40b8000031fb7c52b994889824661fd8e8c6942ec14588d43bc17b08d83140c2000031fb1f62bb144098246b2050ea06942f0142888c3a017908c82dc0be000031fac3f2b5944c95a44b1fa8e586682ea13e888c3a617408882e80bc000031fa6742b2946495c4491f58e8c68e2dc13e08943a217408e82f40be000031fa0c12ab13e094844f1fb0e8469a2e914d091c3c818209082f00a4000031f9adf2c794949a847c2138f0c6d830515689303ce18b09383140be000031f95172b4942495c45d2030ea46a42fb15188ec3be18909003040bc000031f8f3c2c414b098c4682028eac6a22f214688dc3ba17b08b83040bc000))) else (if i < 530 then (if i < 528 then (if i < 527 then 0x3226ccd2aa13a890c41a1e40db862c2bb12d080435415f08502d00a0000032267152a813c893e4491f88e586702dc13f089c39c16d08702f80c40000322614c2bd946496a4591fc0e446722d713d087c39a17208982e00b400003225b7d2bd948897e4592020e946922dd13e889c3a617b08b82e40a2000032255a92bd144498045d2000e986862e914708c438616808b83080bc00003224fe32b194449684521fe0e8067e2d613e08a03a218309002f40be00003224a272ae94109664521f48e5c6762e013f08a83ba17808a02e00ba000032244792a993e49424461f88e3c64e2c9136084035215b08302c00ac00003223eae2b3142496044b1f98e4c66a2df14088ac39616b08782d00b8000032238bb2cb95089b64742070e7c6962f114888d83ba18309183240ca0000322331a2a113a492a43b1f38e446802df14708b83b617808f03000c800003222d362c414f89b247e2138f406d630e15709403e018b09203200c4000032227702b594489704612058e9869a2ee14988e03ac17808902dc0ae0000322219b2bc14a098c4662038ed46a22f914b09043c818509583180c800003221bd42b6942c95e4501f60e306642d013a886c38017008702d80ba000032216212af940493a4411f08e446582ca138883c36e15607e02980ac0000322108629e137c9104331ec0e006562cf139887037616408202e40b600003220aea29f13688e84181dd0db061c2b4136083036a15908602bc0c0000032205252b8144896c4622078eb06962ee14488b83ac17808e82f00b20000321ff832a1939c92e4381f40e5867e2df14408a839216e08902dc0c00000321f9af2b9944496a44f1f38e2464a2d814008a038a16c08f031c0ce0000321f3d12c214a49864612018e486622cf136886836e15807f02a00a60000321edeb2bf94649784511f88e646742d614308b839416708102a00a00000321e83c2ad93d492a43d1f70e3465e2d914008943a017208782ac0a00000321e2612c2146c9684581fc0e2c6442cc137887c39017108782f00cc0000321dcb32ab13a090a42a1ed8e1863a2c4131884437c16908803080ae0000321d6d02c614a89964712080eb46b82fc14e89083c018409403280d40000321d10c2ba945c96a45b1fc0e806802de13f087c39e17308c030c0b00000321cb162cf95289c048f2180f586de30c156092c3ce18909503140d60000321c5722a4939891242f1ed8dc863a2bf12b080c35c15708382d00ac0000321bfb72b1941895a44e2030e946822e414808743a617208b82e00b20000321b9d62bf14b09b04852140f206c8304152090c3be17108802b40ae0000321b40f2b3145097045b1ff0e9c6862f514808bc3a417509202fc0b40000321ae2f2c094749864702090eec6b42f214b08d43a416e08a83180d80000321a8632b5147096a45b1fd8e4465c2d013a886838416d08f83140b80000321a2882c094b49a046c2058ec069c2e914408a439a17208902cc0be00003219ccc2aa13f89504451fc0e646682cc138885036a15b082829809c000032196fa2bf94689984642050ee06b62f815308f83c217e08a82bc0b0000032191422a493f09404431ee0de46402c6137888038616b08a02a00ba00003218b7d2b5945c9764581fa0e906842e013f889439c17908e02dc0b6000032185ae2ba948098c47220f0ef06ca30114f09203d218c09003140c600003217ffc2b0140c9464511fb8e586882da14188b43a016c08782c80b600003217a292bf149c98a47320a8eac69c2f014a08bc39c17008682d40aa000032174512c1146096a4611fe8e486642cb138884c37416c08782d80c600003216ea22a0139091a4301ed0dcc63c2c2135081c36a14c07b82980b0000032169012a293cc93242e1ee0de463e2bb135884836615b08602dc0b2000032163162c214d09904672058ec46942e514408c83d017d093031c0c800003215d212ca14d49a44642078ec46a22ec14588d039a17708882fc0be000032157652b0943096e45f2020ea06902e4140889039c17108b03000b4000032151832c094789784692010e9c68c2f114608b039416b08e03180de00003214bf029f13488ea4101e08db06302c2134085037c15f08302d409e000032146342ae94009404541f60e586802e313d88b43ae17608a82e00aa0000321408d2a713cc94244b1f30e4c6722d513b085037015d08783000ac00003213abc2bd14809804572000ea868c2e114908b839416c08702d00ba000032134fc2b4145094a4441f78e4c6742dc13d089838215907f82980c200003212efd2cf95189d249b2200f546f231615e09503f619309a83340d80000321296929913708fa4251de8dc06382c4136084837a15b08502cc0b6000032123a32b514649664652058ea868e2ea143888838816307f829c09c00003211dd72ba141c94e4471f60e3c6622d6134881434c15607d82c00940000321180c2b7146898445f2000e886842df13e086039216f08882c80aa000032112332c114909844581fd8e6467e2d914288a43a016d08b032c0d400003210c632be149c98646b20d0ed86a02e814608f839417008c02c40b0000032106a12ae940094c4421ee0e0864e2d3141086c36415e07f827c0a0000032100ab2c794a89ba47820c8ef86ba2f914d08a839a16b08582c00ae000 else 0x323df0a2cc94d09b847820a8ec46982f114a88dc3b018209b03500c20000323d9232c614909944692070ebc6a62f214188a039a16308682c80ac0000323d35e2ae940494044f1fd0e886942e713f888439616b08802f40b80000323cd882be946498246c2058ec06aa2f514188b038c17108802fc0ca0000323c7e52a313d893044b1f48e4066e2db13d089039a162081029c0920000323c2092bd14649724531f80e3065c2d513f889038a16d08982c00b00000323bc4c2b3945c97a45d2050eac69c2f114e08f43b017d08c82f80b20000323b68e2ab13e493643d1ee8e0864a2c7133884436815f08402f00b60000323b0cd2b3943895c4491f90e3c6682da13e888838416908782e40b60000323ab212a714149584501f80e506822e313e088837c16808782c80b20000323a53c2c294a098c4702098ed46b62ff15088fc3b617408c02d00a800003239f5c2c514a89804622020e886922e714188a839416808602c40a4000032399c229a93889204331eb8e1c66e2ce135083837015808182840a2000032393f82b7940493e44e1f90e6467c2e714888d039e16708d02e00c800003238e432ad140c93c44b1fe0e7c6762e2141088839a16808702c80bc000032388422d214f09bc4812118ee46c630b15389243dc18909403080c2000032382852b1140c94a44e1f68e706842e514308943b017a08e03080c200003237ca02c614a09864652078ee869e2ec14688dc3a017908d83140ce000032376cc2c0147c97645c1fd8e6467e2ef14908d839617808a02f00ba000032370f32bd94689844672040eac69c2e614a88d03b217d08d02e40b000003236b522ab13e49424411ef0e246582da14208a438616e08e02f40b0000032365792b9146c98c4682058eb46982ee14488b83a616d08882c80b200003235fa72bb94609844632010eac6aa2ec14488a03a617a08d02f00ae000032359ec2b314389524441f28e286642d113d086037816d08b82f40c40000323543f2aa93cc93a44d1f40e5066c2d413c089439c16c08202e40c200003234e7f2aa13cc9424401f38e2464e2d013e08a03ac18008f02f00b4000032348fa29613548ec41b1de0d9461e2ba12907cc34a15407d828009e0000323431f2bf14849904642048eb86a22e214688e83ba18008e82e00a800003233d2f2c0947899247b20a0ec46b62fd14d09043be18708f030c0bc000032337702a913bc93243a1f30e206582d214288ac3a617d08e830c0d2000032331bb2a893d892e4361ed8df86522cd13a085c38216208382cc09c00003232c012ad141c9624542050ec869c2e414408c839a17308d03000b2000032326432b1143c96e4571fc8e5865a2d813b085438016508802b80b4000032320952a613949124271e48df06462c513a089039617508d82e40ac00003231aab2c594c89bc47c20d0ef06b230214e88ec3b217c08d82e80b0000032314e32b8947897e4622050e8c68a2eb14108ac39417708b82c40b400003230f4e29f137c9204361ec8dd862e2b3132883435c15e08902c80b0000032309642c994d899c46c2050e986902e714388a038816d08602c00b60000323038e2bb945c9864672000e9068e2e9143889038016a08782d40a00000322fd9a2cb94c49c248b20d8f046c830215509183c018308b82f00bc0000322f7ec2af943c96a4571fc0e8c67a2e014908e03c017708c82e00a80000322f1fb2cc94bc9a846f2040e986882e3142087c38a16608782f40ca0000322ec2d2bb943494e4421f88e9867e2df13d886837216308182b009a0000322e6802aa93c094444f1fb8e6068a2e214a08b83a617f09103080cc0000322e0b82b6945c9704632020e7868c2f814908fc3d418008d83180ac0000322dad82bc947098c4662028ed46ac30b15709403c417908c830c0cc0000322d5332a513d093e4431f18e0063c2be139087c37816008382b80ae0000322cf822a793e49244301e78dc063c2c1136888838817008382b80aa0000322c9bc2b2141495444d1fa8e5066c2d513c886437616408882f00ae0000322c3c12cb94d89b448720f8f006ba2fa15189003b217c092034c0d80000322be002ba147098c4571fc8e6c6762dd140889439216d08802b80ba0000322b82c2b9945896c4511f78e4465a2d613d088838c16608902f80c40000322b2102d214f49ba4812120f186b42f114588d83ae18509083140c20000322ac202c5149c99846b2018eb069e2fb14488a039416d08a02f80c80000322a6552b8142c95e44e1f88e6066a2db13a888839816a08a02dc0b20000322a0a12a313a091e4481f68e446702de143089839a16b08382ac0a200003229b0b29f93d09364351ee0e106522c2131081c36815d08882f40c2000032295582ab140c95a4481f68e4065e2d814008b43aa17708b82d80ae00003228f7d2b8946897e4612028ea46a62ee14288a03a417308d02b00b2000032289bd2b094289584552018e8c6902ec13e889038c16c08782cc0b6000032283e52bc14789884642010e806842ea14508b038c16f08c02f00b800003227e122be14989a24772068ea867e2e814408b839617808e03000b8000032278612af93f49324371f00e086302be131082035c15a08082c40ae000032272852bd94749744511f78e4c6822eb14608b039a17508b02f40c2000) else (if i < 529 then 0x32551dc2be148096e4521f90e446762ea14b88e43cc18609182f40c000003254c142b9145c97a45d1fe8e8469c2e914a08d43c818708f02e40ca000032546252cc14e099847220c8f106d430a15309103ba18d09003280c8000032540522bf947c97a46c20b8ed86b42fc15309103c618709603300c600003253aa32a813f094e4401f70e5c67e2e5140089c3a217c08f83000b8000032534b92c794e49ca4852110f2c6d030e158892c3d418d095031c0b400003252f0c2a113a09344371ed0dfc65c2d1139883835c15f08682ec0b4000032529072cd94b49ae47f20d8ed46a82f914d08f43b217909282ec0b0000032523152cd95309d448920e8efc6be301152090c3ce18709803400da00003251d502b214449684571fe8e806a02eb14688b438a16c08a02d00a6000032517b72a2139c90c4301ec8df86422c8139886438616b08c82d80ae000032511bb2d215149d24892108f306c030315608e839817b09002e00b600003250bef2b3143095c4451f50e4467a2e414708943a416b08c02e80ce0000325062a2b7943496244e1fe0e7868c2ea140886c37a16c08482dc0bc000032500762ac93e493643a1ef8e0463a2bb133884438416808902c40a80000324fabb2b5143095845a1fd8e6067c2e614588d43b018509303280ce0000324f4d92c3948c99046c2058ea068e2dc13b888c39816c08802c80b20000324eef02cb14d49aa46d20b0ee86b82fc15008f03ac18009702f80b40000324e9412ac142c94a4551ff8eac6962e7141086c37a16d08a82cc0aa0000324e3a62a213a49124341ef0e3466c2d9138887039616f08b02dc0bc0000324de032a493cc94244a1f50e3c6742d813e08c43be18009003380d60000324d8152ca14c89b64792098eb46962f014608d03b017808b83140d40000324d2452bb947c9764501fe8e8069c2f1145888838416708682c80bc0000324cc7b2b4942896044b1f48e0c64a2d914188c83b217109002f40c60000324c6be2ae93dc9504531fc8e606742e314188943a416e08b02f80c40000324c0ee2be147c9764672080ed469e2f614988f83b416c08502c00b40000324bb172c094809724632000e9c6942eb14d890c3ac18009183040d00000324b53a2c294a498645c2030eb46922ea142889c3a216c08482bc0be0000324af772b1141c94244c1fa8e886822ee14c88fc3c818b090031c0ce0000324a9c02b1141893a4391ee8df46582c2131081c35a15b07d02b80ae0000324a40f2aa93cc92843b1f08e486662db13c886437215d07e02c80ba00003249e2e2be949098e4622008e846902e714588bc3aa17709002f40cc0000324987f2aa940c9524561f80e8067c2d413b886837016608082cc0b8000032492a92be145c9764581fd0e706662e314788e83b018109083080cc00003248cca2c114c098a45a1ff0e786842db14588ac38a16608982fc0be000032486fd2ba145c98045b1fe8e886962ef14608bc39617008202a40b6000032481432ac13f49424551fc8e7c6702d9140887837015b08382e40aa00003247b8c2b3145c97a46e2048e7c6962e814508e03a0174091830c0c6000032475b42ba947896445e2020eb069a2e813d086c39e17909003180c000003246fe72bc144494c45a2030ebc6a02ee14d093c3d618508f82ec0ba00003246a332b113fc9584491fa0e5c66e2db13b887c37615d08482bc0a4000032464732b4940894244a1f30e3466c2d513d085c38016108602c80bc00003245e972bb14609664591f98e406662dc13e08743a217608d02e80a2000032458be2be14b498a45a1fc8e946902e914788b839e17508f83200ba000032452df2c0148099046f2068ed06a82fa14b89183ac17608e82fc0ce00003244d182b7144096044d1fa8e8466c2d814008a438a17508a02d80a2000032447732a793dc9484431f28e2067a2e914788a438816c08782b80ba000032441b02ae13f895644b1fc0e8866e2d313c88883a217108882e80bc00003243be82b5146097245b1fd8e6466a2d8142887c39c17008602dc0be000032436262b2942495e45c2010e9c6962e714288a43b618408e82fc0b2000032430662b8143495644d1f78e6868a2eb14608d03bc18209483340cc00003242a7f2c894e099847220b0ee469e2e914b08e03b417a08e02f00be000032424c02b293fc9384431f38e346602d813f089c39c16e08802c40ae00003241efe2b6944495a4501f70e2466e2d3136084438216608382d80a6000032419552a013b490e43e1f40e306662d3137888838616308382b80a2000032413672c314c09a24752080eb46ae2fc14c08d43c418309002f00c400003240dc82a393e09344471f68e506722d5138086437c17208b830c0ca000032407f32b7944097a4531fc8e7c6682c4135086837e15d07e82900a60000324022b2b6144896845e2058e9468a2dc14088a438416508702c40b20000323fc672b4144097c4582018ebc6a22f114888c039c16b08502e00be0000323f6742ca94cc9a047120b0f046c830a15188f83a818d09082f40b80000323f0c32ae14109604441f10e3065c2d314208b839816e08b02c80b40000323eae32c1949099c46f2090ed46aa2fd14d88fc3b818009182f80bc0000323e5032bf148097e4682028ea06982e5144089838a16c08a02c00b6000 else 0x326c41a2a714049504511f78e7c6922ea143089c39e16808782d40b60000326be592b5945496c4591fd8e7c68c2ea14988dc3b017308c02e40ba0000326b8a42ac93e89384381f38dfc6562cd13b085c38216a08682dc0be0000326b2f22ad141093e4481f68e406522d6139085838617508e82e40be0000326ad122bf94789a446b20c0ed06982f814c08e43a217608782ac0b80000326a7442b193fc9484491f20df46522c9135886038416208982f00b20000326a1732ba944c95e4471fa0e686762e114188a039417708b02ec0c200003269bb52ac13cc9324411f50e3866e2df13d088c37a16708802c80b2000032695db2bd147c9804582008e806782e214208a838416f08902d00c400003268ffe2bf148c9724662088e846a22f714f88fc3d218809783480ca00003268a1b2bd146c9884652020e9068e2e5140887837c16408682d00a6000032684462bd146496245b1ff0ea86b22fd152891c3d418209182f80ba00003267e612bc147096e4641fd0e886922eb14588c43ac17708e83000b0000032678852ba947499847320b8ee86ac2f714a89043b618f093032c0ca000032672d32a993e49484451f38e1064c2d413a085c38a16808e02c40ac00003266cf72bc94649964712090ecc6aa2f914888d03a017808f82fc0be000032667372b4144897a4561fc8e6c68c2f114888b838616d08882c00a8000032661692b5942895a4551f90e4067a2e114808c03ae17e09083200c200003265b9b2ba94509864642010e746762e2140088839417708c03140d00000326559f2cc14ec9be47620d0f006d030515b896440419909583280d400003264fd52b3942c9584521fd8e8067e2eb14688b837c16608582bc0b400003264a272a593cc92a4421f58e1c6582dd13e889839417608b02fc0ba000032644622ad141893c4431f68e406622d4140888838215708002b00ac00003263e962b3941895244a1f40e1464e2d213f088837816008282d00c2000032638b52be147098a46b20c0f106c42f0142887c38016508682e00ba000032632e42ba148497e4541fa8e986982f014888f43b618708d82c409e00003262d382a313b492e4431f50e2464a2ca138085c37216908502b00b6000032627aa298937490442b1e88d986202b9134883037215908182a80b6000032621c72bf946499646c2098ea069c2ea14708b43a217508b02f00c000003261bfb2ba149097645d2018e6c66e2e0141889c38616308502b80b4000032616372b6945897646e2050ebc6a22f314888d03ac17908d83100c20000326107f2ad93f49304441f28e206682db13f888437c16108782c00b200003260ace2a913bc93244e1f48e306582cf13d089c3ae17a08f03200ce0000326052c2a1139891c4301eb8dd86522cd143088838c16a08d031c0e40000325ff532ba94709724561fe8eb46b02e914808e43ac17b090030c0c20000325f9992af13f09324431f80e5c6722e013f889839a17108982e00c00000325f3d22b6944097645a2008e6066c2db14508e43b817808e02f80c00000325edd32d4150c9ba47920f8f046ba2f514708d83b017608882c40a80000325e8122af141c96245b2050e7c6742e7142889838016208b02ec0ca0000325e2582b0941c95a4451f38e546642d5138086437a16408582f40ca0000325dc892bb147098245c1fe8e606862f014888e43b216708982d00a60000325d6ca2ad93fc94c44b1f80e186702d5137885838616108602b809a0000325d0c12d095149c648220b8f046ca30115589083c217608c83180cc0000325cb2929813749144371e98e086562cf13c886037415b08182b00a00000325c5882a913b89264391ec8df46602dd14208ac39e17308682c00ba0000325bfb12bb94709844682090ef86c430115008d03a216b08902bc0b20000325ba0d2a413c09364481f60e3c66a2df14308c839a17008902e40c20000325b4642ad143495c4481f80e546702d914008a039817309003080c00000325ae8d2c114c098646a1ff8ec869e2f614a88d03b817408e82e00bc0000325a89f2c994ec9c647d20e8efc6ae2fa14c09043b218909302e80bc0000325a2dc2b594309564501fd0e6867c2e613e889038e16b08482b40aa00003259d0f2b314189504541ff8e986902eb14e88f03c818408c02e40c20000325975a2ac14049564471f80e546782d5138887838816908e82f00b0000032591d529693688fa4281e38ddc6362c0135883036415f08002a008800003258bfd2c614b099446f20f8f106b82f315008e43b418b09202e40be000032586202c1147499e4722068eb06962ec14588e03a817308b02f00d60000325804b2bb947c97a4551fb0e706702db14a88c039e17608d82cc0ae00003257a752c114709764562018e606782e314388ac3ba17d09102ec0a8000032574992bb147c9784652038e986842e714808d03b4178093033c0c600003256eaa2c514ac98645d2030eac6922e914b08e83cc18b09302ec0b2000032568e62b2142096445c2048eac69c2f714a08c83ac17c08c02e00ae000032563282ab93d892c43a1f10e2866a2ce13d888438416208582c80b000003255d5b2b7946c98e4672000e9c6ae2fc15188f43b417e09303040cc000032557ac2aa941094e4481f90e4867c2e914588ac3a417b08d83040c0000)) else (if i < 532 then (if i < 531 then 0x3283631296137891e4331e90dd46482c312e881c37015b08402c00b0000032830752ac93e894c43e1ee0e106462c7132883436a16308102b40ac00003282ab62b0143895e4421f40e506762e114288d83b017e09403040c6000032824e92b894609724561ff8e9869a2f014b88f03b618308f02f80c200003281f232bc145495a44c1fc0e5c6582cf135084835a14c07902980a6000032819672ae93e892843e1f60e386442c0137884437416208382e40b40000328138d2ba145096a4572030e946a82f414a08dc3a417e09083080b200003280d932ca14dc9ae4782110ecc6a42f314a08b43b417e08f82c80ac000032807d02b694409704521fc8e946922f614e08f83ca17e08f03080d0000032801e92cb94ac99647420b8ee46b82fd14f09003b617708b02c00b80000327fc452a613a891a4441f28e306622d8142089039417008b83140bc0000327f6992ac94189464541f98e486762de13a084437c16708202d80ce0000327f0cb2b7942c95a44f1f98e5c66e2d2139086438416d08882e00a80000327eafe2b5946096e4591ff8e7067c2ed14688b03a617908b82d00b60000327e51c2c694d09bc47720a0f146d42f514f89003d018108c83100bc0000327df2d2ca14f09d849521d0f8470e32515c895c3f6190095033c0d20000327d96a2b7942495a44a1f38e0064a2cc139087437615d07f02d00be0000327d3a02b5144896845b1ff0e8468a2e614608f43c017b09083100c40000327cdcd2bf14809824631fe8e8466e2dd141089838816808782e00bc0000327c7e62c794ac9964682020ec06aa2f914a88b439c16908682c80a20000327c2472a293889104341e98de06422c31390864372161080828c0a00000327bc7b2b6147498a46c20a0ecc6a02f814c08d83b417f08e02cc0aa0000327b6cf2a1939c91a4351ec8e0864c2d813e088438016d08702e40c60000327b1302a2939890e42c1eb0dec6482c2132083037616208482a40a80000327ab622b7947897444f1f30e386602d213d889039816d08602c40b80000327a59d2b194389784632058e986a630014e09083c017308a02c80b800003279fc02bd94849904682068ec46ae2fd14d88d43c018209382f80be00003279a102a813c09284391ec0df865e2ca135882836215e08402b00ac000032794312c3149099c4672000ea46862f214c08f03c818909383080b400003278e6e2b414509764652060ebc6962ed14a88c43ae17a09383080cc000032788b82ae940897045f1fe8e886762e013f88a039017608982dc0cc000032782d82c494b89b047b2140f506fc31815109203dc18109303200be00003277d3a2a413a091a43e1f60e6066c2e214208a83aa17508e83200ca000032777872ac13ec9284311ee0de86342bf1318834374161084029c0a6000032771f929613348f841e1e20da06242b7136883c37015f08482c80aa00003276c2f2b3943897645f2058e9868a2e714408b43b217608b83080c0000032766452c1149c99046c20b0ef86b22f614a08f03b217608c02c00ac000032760852af145097645c2058ecc69c2e114308ac3a416f08882cc0c200003275ab72b9145895a44a1f98e6c67a2e314088a83b017508a82c00b6000032754da2c0945c97a4632028ea86962f114988dc3b617908f030c0bc00003274f142b9145097045a1fd0e7866c2d913e088439416908f03100ba000032749692a813c89544541fd0e8067a2e514908b037a16a08b82e80c6000032743962b3945098446a2030e7c6902e5144087838816908a82c00aa00003273dae2c914c099246e2100ee46b62ed14b08c839616f08902d00a0000032737ed2ae93f093c4401f30e0c6602d413d887c37e16308782b00b40000327320c2c614c499647320b8ee06aa2f514e08d43b617608902bc0a800003272c642ab93d09344351ec0de061a2bf12f880c36015208282b80ae000032726782c794cc9bc48120d8ef46c82fa14908e83a617708d83100bc000032720802ca94cc9ba47820a8ef86be2fa15188d83ca18a09583240d600003271aae2bc948098a4602040e8c68c2e614808d03b618609303100d0000032714d82bc14749a047320a0ec06a82f614d09283e818a093830c0c600003270f1f2b314409664541fd8e946662da13f089439617608b02e00b4000032709402c214a098a45e2018ecc6ba30714788d03a4174093831c0be000032703552c394cc9a64712098eac6922de14608a438e16808682cc0c00000326fd902b614389484561f90e306882e0142089437e16308682ac0a00000326f7e02a7941094844d1fb8e646762ea14688bc3b017608c02e40c00000326f2302ae13f89364441f38e246442c2138087039217008282a80b20000326ec682b2140093e44e1f90e606702e213e887038416a08a02e00aa0000326e68d2b6945896845e1ff0e786782e213e088839e17808882fc0c80000326e0d12ad13e49424511ff8e746862e414708b03a418209483180c60000326dafc2bd947897445f1fe8e6c6622d513f888838216208702c80b20000326d53e2b093ec94e4531fe8e886922e3142089c39417808602d00ae0000326cf842ae141496e4592000e8868e2e314388a839017409102f40c40000326c9cf2b4942c95a45c1fd8e606682dd144889c39616908782d40ac000 else 0x329a7102c714849724591fe8e5c6842ef14e09143cc18608f83180d00000329a1482b9945c96c4601fb0e3865c2cd139082c37016008902ec0b400003299b742bb143096444f1fa0e4865c2e414908c03a617008802dc0b8000032995b82ac93f495044a1f70e6c6742d513f888038c16d08702cc0ba0000329901a2a393b891a4341ee0df064c2c713c086c39416f08182900a400003298a452b994549724621fa0e4c6662de13e088438416908082900a8000032984742b3943096e4612028ea86b02ec14708b43b017608b02e40b000003297e8d2c4946c98646b2090ec46a42f314b88f83ba17508b82ec0b4000032978e42a413b092e43e1ec8e1863a2c2131082035a16208802c40ac0000329730f2c2949899046c2028eac6962e713d886c37a16c08a82f00bc00003296d4a2b1141895c45d2010e946882ea14b08ac3a417408f02dc0b4000032967902b0140c9444581f80e346822da13e088039a16f08582f00bc000032961ce2b3142495244a1f90e586662db138887839817108b82c80b200003295c092b0941495043e1f90e6866e2d8140889c37c16a08982e00ce0000329563c2ba14349644511fe0ea46922e714608b83bc17709102ec0b6000032950932a813a490c4271e20db86342be135085838816608982e00b200003294ac22ba94649804591ff8e7c6942f014708e43a217908802dc0b4000032944fe2b5143095244b1f70e346542dc13e88a03a017709102cc0be00003293f292bf148499646a20a8ed06b22f615009083b417f08c83040da000032939322c614ac9964682020eac6962f014708d83b817408702d00aa0000329337f2b2942895044a1f90e686602df14208903a417108c82e80a800003292dae2bb145496a4551fc0e8467a2eb14788b439216d08782bc0b2000032928002b0940894a44e1f20e306562d1141086c38e16a08202a40b400003292278299134c8f64231e10db86242bb12d080034e15008182b40aa00003291ca72b994889884601fe0e8c6842dd13e889838e16808382dc0b4000032916d22be146896a4612058ec86922f914d88dc3ba18209303000b8000032911122b5941c94643e1f40e3866e2d8141889839417208a82d80b400003290b5a2ae940895044e1f90e8868e2ea14588a438e16608802c80a0000032905822bc949c9aa4742048ea46b030014e88f03c418309082fc0c20000328ffcf2ab13f493e43f1f28e2c66c2da13c088c38e16e08e02c80a20000328fa0b2b594149624461f38e306622d7136885c37216408302d00b40000328f4572a693a491842d1ea0dec6462d3138886439e16c08802d00a20000328eeb12a913ac91242a1e78dcc6222be137083c39017608f02f80ba0000328e8da2bf947c9804611fd0e986702d914288a83ac17a09182fc0b80000328e31a2b514149584501f68e6c6822e714608c839c17308c82d80ce0000328dd782a113b09244311f58e346682d9141889038416808382c40a60000328d7a32bc945497245b1fc8e986942f714c88cc39a17508a031c0ce0000328d1d52bc147498046a2080ec06a22fb14988cc3ae17008a82e80b20000328cc2d2a613b893843d1f10e406662d1140889838e17008782d00ae0000328c65f2bf149497e4692058ec06922f6146889837416508902fc0b00000328c0a32aa93e09464461ee8ddc64a2cf135888438015c07b82800960000328bad92b1140893e44e1fa8e3465a2d213e086437c16908602c00960000328b50a2b1142095e45a1f70e2865a2c913d08a038a16a08982d00b60000328af3a2b5943c9664531f90e9468c2ef14889043bc18009582fc0a60000328a9562c294bc9964651ff0e706882ea140088c38a17109383340d80000328a3932b5141c95e4561ff0e8068c2df13b8840388179090030c0d000003289de82a393d092642a1e80da46222b412f081034215108282a40aa000032898232b6142094844f1fb0e786922ed14308f03b818609403100c8000032892462bc94689784602030e906942e714708bc3a817408f02e80a400003288c912a714189544411fa8e6867c2e114788dc3a817f09083040cc000032886b92c1149c98a4692040e946a02ed14a88fc3b818409103140c60000328810c2a713d893643f1f08e106662d313b087838416008702d80be00003287b382bc948497845a1fd0e9c69c2f614888b039a16a08782e80ae0000328756c2b894589744622028e8c6702e8140889c39016f08a02c80ac00003286fc92aa942095a4471f90e606782e013d089c3a016f08c83040d2000032869f72b794549764692048e986a22ed14488bc3aa17c091830c0ce0000328642c2b8147899c4662020e9c6a02f814d08ec3aa18609103140be00003285e852ab13dc92a4431f40e486622ea14708cc3b817e09102e80cc000032858c52ab941c9544491f08df06502d113a887838816208002bc0a6000032853162a813b492a43d1f88e306602cd134084836c15a08702880bc00003284d572ae93f094643f1f48e3865a2d413e887038616808802e80b0000032847902b8944c96c4521f78e606602e4147089439e16c08a02f40bc000032841d72af940c9424461fa8e306462c913e889c3ac17308f03000bc00003283bbd2df95589f84932188f486de30d15109203be17a08e83200da000) else (if i < 533 then 0x32b18602ab93e892c4371ee0e106502d413d888c39616f08b82e00ba000032b12a72a993e493e4401f60e506722dd14108a03a816608602d80c2000032b0ce02b7946c97645e2020e9c69a2f114a88f43c618e095831c0d2000032b075229893809124331f10e1c6642cd137887c37216608302e80bc000032b01622c894a499645e1f78e6c6842e214008b03b417a08c82f80c6000032afb8f2be148c9784642058ec46a82eb14989043bc17308802e40d0000032af59f2c814d899c46a2098ebc6bc30514f89043d018b09c03400ca000032aefdd2b3144095244f1f90e686902f414708b039417708e83540ce000032aea2d2aa93c895645c1ff0e7c6722e1141088c38816a08a82cc0b0000032ae4a229893608f441d1df0d8c61a2b6131081835c16108782d00ae000032aded52b9945898045d1fe0e8c6862db141888037416208402c80ba000032ad8fe2be94b89b847e20e8f0c6c831015609143d218309403200d2000032ad3332bb94549644561fd8e746762e314308a839817408d02f40c6000032acda229f93708e84141db0d9c6142ad12b081c35814b079028409e000032ac7e62a693bc92a43a1f28e106542d713c087437416507f02c80b4000032ac21e2b294089424431f48e146482bf130883c37816b08c03000ce000032abc1e2cf14f09ba47720d8ee06b62ee14508b839616b08682d00b2000032ab65f2af93e093844a1fb0e7c6742d413e887437216408502cc0b0000032ab0a12ab940c9584571fa8e3c6602d1134081c36215408082bc0a2000032aaab02c814b099e46a2068ecc6942f214a88b038c16608502e00b6000032aa5032a813d09404461f40e546702cc13a887c39017208902dc0c4000032a9f512aa93fc96a45d2028ec868e2f114e88c43a017c08e82f80c4000032a99962ab13cc9324371ec0dd86482d414188ac38c16808e03140c8000032a93e82a213e493e43b1ef8e1863c2ce134882036415b08102b009c000032a8e562a313b490e4271e98de06402c8137885c37a16408582e00d2000032a88742bc14b09804561fe8e8467e2e7144888c3a217108a02c00aa000032a82b22b1941893c43b1f38e546642df14808fc3be17e09002f80d2000032a7cf22b1142095e4541fe0e746882eb145889438e16508902f40c4000032a772b2b394209684582038e8468c2ee14f08f83a217408d82f80bc000032a71492c314a499c47320c0ed06a22f514c08c43a817908d02ec0c4000032a6b702be94509704531f48e586822e214288bc39a17608a82e00ac000032a65b92ae940c95c4501fb0e4c66c2e514488983a416d08a03080be000032a601d2a593e894644c1fa8e5065c2d713e089439416908a83000ba000032a5a692ac13e093c43a1f08e246422c212f881836416208102ac0b6000032a54af2b7147899847620b8ee06b030115709403d419909b03680de000032a4eca2c0948898445d1fd8e9869a2f414d08f03b618509303340da000032a49032b994549704471ef8e4467e2e314288bc3a418009283100c0000032a433f2b494489644672080ecc6b82f714c88d83ac17408702ac0b2000032a3d762b794509664581fb0e786822ed14e08f43c218309282e40b8000032a37b72b113d893243f1f90e4c67e2e114288e03ac17208882dc0b8000032a31fa2b0942c95c4551f40e2c65a2d813c886836e16308182a409c000032a2c4a2a713d49304341ef8e3067a2e714308bc3a817708903040dc000032a268a2ad940c96e45d2000e986882d713a085835815b07e02b40ae000032a20ce2ae140494a4511f30e406602d813f08803a816f08582dc0bc000032a1afb2ba144c97a4612018e8468c2e2146089c39217608e82f00c6000032a15192c094a099c46620a0ec86b02fc14a08f03a616e08882a80a6000032a0f652a893ec9384461fb0e4c68e2ec14308a03a216f08802fc0b6000032a098e2b9943095c4592008e906922e814008ac3ac17308782d00ce000032a03c32b6943894c43e1f68e346602d2140888c38216b08d830c0c60000329fe0f2af942c96445b1ff0e706802e214988c839e16f08602d80bc0000329f8382c1149899046d2050ed86c02ff15009403d017d09383240c60000329f27d2ab93dc9244311ea0de86562d413b889039817008882c80b40000329ecab2b4942496e45c2000e786782ed14808a439017008b03080c40000329e6da2b8949097845f2010e506842e8145887436c15007c82880a60000329e0f82c3149099c46f2050e986b02f114808d43b017f08d02d80c60000329db382b4141c94c4451ee8df86402ca13b086c38416e086830c0c60000329d5812b4145896045a2060e8c69c2ed14a88b83a617809383240c40000329cfb42b1943c9604561fd0e8c6982e214388c83ac17708c830c0c80000329ca002a893d89344451f70e7868c2f614c88ec3aa17a08d02dc0a60000329c4162cb94c09a44842118f086b22f314888d03a216f08c83280c40000329be722a713f493243b1ee0e1064e2d2138887c37e15808302a00a40000329b8802c994c49944712040ea06962f014b08e83de18508f82ec0cc0000329b2bd2b193f09364441f50e046562d3139086c39216c08582b80b40000329ad012b3944896a45a1fd8e686662d3135887037816208602cc0a6000 else (if i < 534 then 0x32c89ac2af141c9524421f48e1065c2d113d085837616008702d00b4000032c83ab2cf14cc9c047a2120f046c830615489383d2185094032c0d2000032c7df42ac940c94e4511f80e746802de138885437415a08702c40ba000032c78422b3141c9684591ff8ea86782e114408f83b417508f02e40ba000032c727d2b2945496a44d1fc0e546762dd14288bc3a816e08d03040d0000032c6cac2bb947498a4622000e806922e614708ac3a616c08482a40b8000032c66ca2c314b89aa47a20b8f006ae2ff151890c3b618008d03100ca000032c610f2b6141c95e4551fd8e5c6602d913f88ac3a417c08982f80ca000032c5b5e2ac140094e44b1f48e3864c2ce13a085c36e16608982e00b6000032c55c629c137890a4261ea8dc463a2c5137084437015f080829c0a8000032c4ff82bc945096c4532000e6c6842ef14508c83b817708d02d409e000032c4a1a2bb146097a4591fc0e786802df13e08a43a817208f03040be000032c447a2a013ac91042e1e88e006402c6136085038c16108202ac0b4000032c3e8f2cb14a89924732088e9469e2f914c09043c217c08a82ec0b4000032c38b22c0948c98c4632028ea46822e414808d03a817608882c00b0000032c32d62bd946496444f1f50e4c6662d5141889038e16008902c00b6000032c2d2f2a393d493443b1f40e3468a2e514588b03a817308e82fc0c2000032c27882a393a890a4271e50dac60a2ad12c881036a15908182d40a8000032c21ae2bd148c9904712080ef06bc30715408f43c217e094832c0ce000032c1bbe2cb94ec9bc47a20f8f186ca30d15188e83cc18a09282f00b2000032c15de2b894409744632030ea86922e414508d439417908e02e00c0000032c0fee2c914ec9b04832130f246c62fc14888c83ba18509082fc0c8000032c0a3c2ae140094a4451f80e086542d013c888039e17b08c830c0c8000032c04872ac141095644a1f88e6c6902ea14688ac3b217c09503040c4000032bfedc2aa13dc9424401f28e246602d814708c839e17609103140d4000032bf9252a913f09464441f28e1c66e2de13f88b838a17208b82e80be000032bf3402c6149098645b1ff0e646742da13f089c38816508782c40cc000032bed972a213ac92443a1f58e2c6622d6139885c37015c08502a80a6000032be7ed2aa13f09484501fa8e506602c713a088c39216608b02f00ce000032be2412a9140494043d1f48e406502c012f080836815607f02c80c4000032bdc672be146897a45d1fd8e6c6642d814288c03b418609003080b4000032bd6b32a7940093e4461f30e406702df14a09083cc17909202f40d4000032bd0ef2b1942496044f1f20e306542c613e086438416808482bc0b2000032bcb282b114509644491f20e3466a2d813c085437016a08982f00c4000032bc5532c0946096a4552020e6c6822ed14388a438015b08282ac0bc000032bbfb82a493c49464481f70e746962ed14988b43a817a08b02e80ba000032bb9f02b214009364431f30e606762de141089839a16908702f40aa000032bb4412a693e894444d1f90e406682ce141887c38416808482d00c0000032bae842a893f49484471f90e546682d113c088438e15c07e828c0b2000032ba8dc2a313a49244371ea8e106522d013a086839216508802cc0ca000032ba30a2b5940493c4441f48e1c6722e1142088839217908d82e40ba000032b9d262c4948897645b1ff8e646782ec14688a03a218509483080c6000032b97592bc147897245e2038e9c6a82f414a89003b018008802c80b2000032b91902b7944895c4562010ea869e2f2149889c39616d08482a009c000032b8baf2ba145097245c2028ecc6a62fb14e08c43a017008c030c0ca000032b85f52a793d893643d1f40e3867e2e7143089c3b417e08e03080b4000032b805f2a0939490e4291e28dd86462cb135881435815407c82a00a4000032b7a952b9142495e44c1f90e7067c2dc140088839216408a82b80bc000032b74db2b6143496e45d2040edc6982ed14608d83b018008882d40c4000032b6f3b29f93709044201e68dd461c2b612e082436216208302b0098000032b69752b3943496e4642058eac68c2e1140889039817508f02e00a8000032b63b32b6945496244e1fb8e606822dc14388c039c17308f82e40ae000032b5de52b8944c9684591fe8e706922f214708a438c16808682c4096000032b58012c4949099046b2028e7468e2e5143887837e16408902e80b4000032b52272bf145898846620c8ee46b030014e09003d618c09803000cc000032b4c532bb948497e45c1f78e2c6562d913c087439416f08802cc0b2000032b46892b8144897a4612008e8c6982e414308c839c17208b83180c2000032b40de2a513d892843f1f98e446682d6140889838e17208902d409a000032b3af52c3147c98847020b0ef06b22f114908b439617408802e80ba000032b351e2b994949884682048eb869c2f214c08f83b417a08e83200bc000032b2f772ad13e491e4311eb0dd06302c5132883037616308302a808a000032b29ad2ba94689764632060ec068e2ed14988e83b617508b82f80b0000032b23de2b6943094443f1ed8e146622d013a887c39416708082980b6000032b1e142bb147c97445e1fb8e9469a2f114888c43a217208d02b80a0000 else 0x32ca072000000000047b2088eec6b02fc15209143ce18509183140be000032c9ad42a413f49424491f28e286562d113f088438c16908582900b0000032c952f2a213d493643c1f28e406622d514208bc3a217a08c82e00b8000032c8f652b9146498c4752058ea46962e0145889c39216b08702f40c8000))))))))))

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



private theorem b533791 : covered 533791 533857 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533857 : covered 533857 533924 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533924 : covered 533924 533991 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b533991 : covered 533991 534058 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534058 : covered 534058 534124 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534124 : covered 534124 534191 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534191 : covered 534191 534258 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534258 : covered 534258 534325 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534325 : covered 534325 534391 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534391 : covered 534391 534458 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534458 : covered 534458 534525 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534525 : covered 534525 534592 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534592 : covered 534592 534658 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534658 : covered 534658 534725 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534725 : covered 534725 534792 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534792 : covered 534792 534859 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534859 : covered 534859 534925 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534925 : covered 534925 534992 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b534992 : covered 534992 535059 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535059 : covered 535059 535126 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535126 : covered 535126 535192 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535192 : covered 535192 535259 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535259 : covered 535259 535326 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535326 : covered 535326 535393 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535393 : covered 535393 535459 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535459 : covered 535459 535526 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535526 : covered 535526 535593 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535593 : covered 535593 535660 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535660 : covered 535660 535726 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535726 : covered 535726 535793 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535793 : covered 535793 535860 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535860 : covered 535860 535927 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535927 : covered 535927 535993 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b535993 : covered 535993 536060 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536060 : covered 536060 536127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536127 : covered 536127 536194 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536194 : covered 536194 536260 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536260 : covered 536260 536327 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536327 : covered 536327 536394 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536394 : covered 536394 536461 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536461 : covered 536461 536527 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536527 : covered 536527 536594 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536594 : covered 536594 536661 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536661 : covered 536661 536728 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536728 : covered 536728 536794 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536794 : covered 536794 536861 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536861 : covered 536861 536928 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536928 : covered 536928 536995 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b536995 : covered 536995 537061 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537061 : covered 537061 537128 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537128 : covered 537128 537195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537195 : covered 537195 537262 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537262 : covered 537262 537328 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537328 : covered 537328 537395 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537395 : covered 537395 537462 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537462 : covered 537462 537529 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537529 : covered 537529 537595 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537595 : covered 537595 537662 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537662 : covered 537662 537729 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537729 : covered 537729 537796 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537796 : covered 537796 537862 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537862 : covered 537862 537929 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537929 : covered 537929 537996 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b537996 : covered 537996 538063 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538063 : covered 538063 538130 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538130 : covered 538130 538197 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538197 : covered 538197 538264 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538264 : covered 538264 538331 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538331 : covered 538331 538397 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538397 : covered 538397 538464 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538464 : covered 538464 538531 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538531 : covered 538531 538598 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538598 : covered 538598 538664 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538664 : covered 538664 538731 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538731 : covered 538731 538798 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538798 : covered 538798 538865 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538865 : covered 538865 538931 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538931 : covered 538931 538998 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b538998 : covered 538998 539065 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539065 : covered 539065 539132 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539132 : covered 539132 539198 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539198 : covered 539198 539265 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539265 : covered 539265 539332 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539332 : covered 539332 539399 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539399 : covered 539399 539465 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539465 : covered 539465 539532 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539532 : covered 539532 539599 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539599 : covered 539599 539666 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539666 : covered 539666 539732 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539732 : covered 539732 539799 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539799 : covered 539799 539866 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539866 : covered 539866 539933 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539933 : covered 539933 539999 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b539999 : covered 539999 540066 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540066 : covered 540066 540133 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540133 : covered 540133 540200 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540200 : covered 540200 540266 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540266 : covered 540266 540333 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540333 : covered 540333 540400 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540400 : covered 540400 540467 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540467 : covered 540467 540533 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540533 : covered 540533 540600 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540600 : covered 540600 540667 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540667 : covered 540667 540734 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540734 : covered 540734 540800 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540800 : covered 540800 540867 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540867 : covered 540867 540934 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b540934 : covered 540934 541001 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541001 : covered 541001 541067 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541067 : covered 541067 541134 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541134 : covered 541134 541201 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541201 : covered 541201 541268 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541268 : covered 541268 541334 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541334 : covered 541334 541401 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541401 : covered 541401 541468 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541468 : covered 541468 541535 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541535 : covered 541535 541601 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541601 : covered 541601 541668 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541668 : covered 541668 541735 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541735 : covered 541735 541802 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541802 : covered 541802 541868 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541868 : covered 541868 541935 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b541935 : covered 541935 542002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542002 : covered 542002 542069 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542069 : covered 542069 542135 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542135 : covered 542135 542202 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542202 : covered 542202 542269 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542269 : covered 542269 542336 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542336 : covered 542336 542402 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542402 : covered 542402 542469 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542469 : covered 542469 542536 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542536 : covered 542536 542603 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542603 : covered 542603 542669 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542669 : covered 542669 542736 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542736 : covered 542736 542803 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542803 : covered 542803 542870 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542870 : covered 542870 542936 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b542936 : covered 542936 543003 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543003 : covered 543003 543070 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543070 : covered 543070 543137 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543137 : covered 543137 543203 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543203 : covered 543203 543270 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543270 : covered 543270 543337 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543337 : covered 543337 543404 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543404 : covered 543404 543470 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543470 : covered 543470 543537 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543537 : covered 543537 543604 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543604 : covered 543604 543671 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543671 : covered 543671 543737 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543737 : covered 543737 543804 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543804 : covered 543804 543871 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543871 : covered 543871 543938 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b543938 : covered 543938 544004 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544004 : covered 544004 544071 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544071 : covered 544071 544138 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544138 : covered 544138 544205 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544205 : covered 544205 544271 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544271 : covered 544271 544338 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544338 : covered 544338 544405 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544405 : covered 544405 544472 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544472 : covered 544472 544538 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544538 : covered 544538 544605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544605 : covered 544605 544672 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544672 : covered 544672 544739 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544739 : covered 544739 544805 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544805 : covered 544805 544872 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544872 : covered 544872 544939 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b544939 : covered 544939 545006 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545006 : covered 545006 545072 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545072 : covered 545072 545139 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545139 : covered 545139 545206 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545206 : covered 545206 545273 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545273 : covered 545273 545339 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545339 : covered 545339 545406 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545406 : covered 545406 545473 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545473 : covered 545473 545540 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545540 : covered 545540 545606 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545606 : covered 545606 545673 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545673 : covered 545673 545740 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545740 : covered 545740 545807 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545807 : covered 545807 545873 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545873 : covered 545873 545940 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b545940 : covered 545940 546007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546007 : covered 546007 546074 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546074 : covered 546074 546140 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546140 : covered 546140 546207 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546207 : covered 546207 546274 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546274 : covered 546274 546341 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546341 : covered 546341 546407 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546407 : covered 546407 546474 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546474 : covered 546474 546541 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546541 : covered 546541 546608 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546608 : covered 546608 546675 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546675 : covered 546675 546742 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546742 : covered 546742 546809 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546809 : covered 546809 546876 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 533791 546876 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b533791 (joinCoverage b533857 b533924)) (joinCoverage b533991 (joinCoverage b534058 b534124))) (joinCoverage (joinCoverage b534191 (joinCoverage b534258 b534325)) (joinCoverage b534391 (joinCoverage b534458 b534525)))) (joinCoverage (joinCoverage (joinCoverage b534592 (joinCoverage b534658 b534725)) (joinCoverage b534792 (joinCoverage b534859 b534925))) (joinCoverage (joinCoverage b534992 (joinCoverage b535059 b535126)) (joinCoverage b535192 (joinCoverage b535259 b535326))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b535393 (joinCoverage b535459 b535526)) (joinCoverage b535593 (joinCoverage b535660 b535726))) (joinCoverage (joinCoverage b535793 (joinCoverage b535860 b535927)) (joinCoverage b535993 (joinCoverage b536060 b536127)))) (joinCoverage (joinCoverage (joinCoverage b536194 (joinCoverage b536260 b536327)) (joinCoverage b536394 (joinCoverage b536461 b536527))) (joinCoverage (joinCoverage b536594 (joinCoverage b536661 b536728)) (joinCoverage (joinCoverage b536794 b536861) (joinCoverage b536928 b536995)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b537061 (joinCoverage b537128 b537195)) (joinCoverage b537262 (joinCoverage b537328 b537395))) (joinCoverage (joinCoverage b537462 (joinCoverage b537529 b537595)) (joinCoverage b537662 (joinCoverage b537729 b537796)))) (joinCoverage (joinCoverage (joinCoverage b537862 (joinCoverage b537929 b537996)) (joinCoverage b538063 (joinCoverage b538130 b538197))) (joinCoverage (joinCoverage b538264 (joinCoverage b538331 b538397)) (joinCoverage b538464 (joinCoverage b538531 b538598))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b538664 (joinCoverage b538731 b538798)) (joinCoverage b538865 (joinCoverage b538931 b538998))) (joinCoverage (joinCoverage b539065 (joinCoverage b539132 b539198)) (joinCoverage b539265 (joinCoverage b539332 b539399)))) (joinCoverage (joinCoverage (joinCoverage b539465 (joinCoverage b539532 b539599)) (joinCoverage b539666 (joinCoverage b539732 b539799))) (joinCoverage (joinCoverage b539866 (joinCoverage b539933 b539999)) (joinCoverage (joinCoverage b540066 b540133) (joinCoverage b540200 b540266))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b540333 (joinCoverage b540400 b540467)) (joinCoverage b540533 (joinCoverage b540600 b540667))) (joinCoverage (joinCoverage b540734 (joinCoverage b540800 b540867)) (joinCoverage b540934 (joinCoverage b541001 b541067)))) (joinCoverage (joinCoverage (joinCoverage b541134 (joinCoverage b541201 b541268)) (joinCoverage b541334 (joinCoverage b541401 b541468))) (joinCoverage (joinCoverage b541535 (joinCoverage b541601 b541668)) (joinCoverage b541735 (joinCoverage b541802 b541868))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b541935 (joinCoverage b542002 b542069)) (joinCoverage b542135 (joinCoverage b542202 b542269))) (joinCoverage (joinCoverage b542336 (joinCoverage b542402 b542469)) (joinCoverage b542536 (joinCoverage b542603 b542669)))) (joinCoverage (joinCoverage (joinCoverage b542736 (joinCoverage b542803 b542870)) (joinCoverage b542936 (joinCoverage b543003 b543070))) (joinCoverage (joinCoverage b543137 (joinCoverage b543203 b543270)) (joinCoverage (joinCoverage b543337 b543404) (joinCoverage b543470 b543537)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b543604 (joinCoverage b543671 b543737)) (joinCoverage b543804 (joinCoverage b543871 b543938))) (joinCoverage (joinCoverage b544004 (joinCoverage b544071 b544138)) (joinCoverage b544205 (joinCoverage b544271 b544338)))) (joinCoverage (joinCoverage (joinCoverage b544405 (joinCoverage b544472 b544538)) (joinCoverage b544605 (joinCoverage b544672 b544739))) (joinCoverage (joinCoverage b544805 (joinCoverage b544872 b544939)) (joinCoverage b545006 (joinCoverage b545072 b545139))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b545206 (joinCoverage b545273 b545339)) (joinCoverage b545406 (joinCoverage b545473 b545540))) (joinCoverage (joinCoverage b545606 (joinCoverage b545673 b545740)) (joinCoverage b545807 (joinCoverage b545873 b545940)))) (joinCoverage (joinCoverage (joinCoverage b546007 (joinCoverage b546074 b546140)) (joinCoverage b546207 (joinCoverage b546274 b546341))) (joinCoverage (joinCoverage b546407 (joinCoverage b546474 b546541)) (joinCoverage (joinCoverage b546608 b546675) (joinCoverage b546742 b546809))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 533791 ≤ index 1025000000/512 := by decide +kernel
private theorem starting_value : fast 1025000000=52053384 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 1025000000=52053384) (n : ℕ) (low : 1025000000≤n) (bound : n≤1050000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=1025000000
    · rw [first,anchor]
      exact starting_value
    · have past : 1025000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤1050000000 by omega)
        have within : index n / 512 < 546876 := by omega
        have lower : index 1025000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤1050000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ1025000000To1050000000
